#!/usr/bin/env python3
"""Generate the unrolled round bodies of std.sha256 and std.sha1.

Both are fully unrolled, with no loop: straight-line code is the fastest form.
The rounds are written in the classic unrolled form: each round updates two
working variables in place and the next round uses the variables in rotated
roles, and the 16-word message schedule is a ring updated in place. No
assignment copies one local into another, so the prover's facts stay small
(the loop counter proofs are not drowned in equalities), and every shift is
by a constant, so SHIFT-ELIDE proves it. Rotations are inline shifts, so the
Cranelift backend, which does not inline calls, runs no call per round.

Usage: scripts/gen-sha-rounds.py  (rewrites the marked regions in place)
"""
import pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
STD = ROOT / "crates/kush/std"

def add(*terms):
    """Nested modular additions."""
    expr = terms[0]
    for t in terms[1:]:
        expr = f"Int.wrapping_add::<u32>({expr}, {t})"
    return expr

def rotr(x, n):
    return f"(({x} >> {n}) | ({x} << {32 - n}))"

def rotl(x, n):
    return f"(({x} << {n}) | ({x} >> {32 - n}))"

K256 = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

def sha256_rounds(indent="    "):
    # Fully unrolled, with the round constants as literals: no loop, no table.
    out = []
    names = list("abcdefgh")
    for t in range(64):
        a, b, c, d, e, f, g, h = (names[(i - t) % 8] for i in range(8))
        j = t % 16
        if t >= 16:
            x, y = f"w{(j + 1) % 16}", f"w{(j + 14) % 16}"
            s0 = f"{rotr(x, 7)} ^ {rotr(x, 18)} ^ ({x} >> 3)"
            s1 = f"{rotr(y, 17)} ^ {rotr(y, 19)} ^ ({y} >> 10)"
            out.append(f"{indent}w{j} = {add(f'w{j}', f'({s0})', f'w{(j + 9) % 16}', f'({s1})')};")
        big1 = f"{rotr(e, 6)} ^ {rotr(e, 11)} ^ {rotr(e, 25)}"
        ch = f"({e} & {f}) ^ (!{e} & {g})"
        big0 = f"{rotr(a, 2)} ^ {rotr(a, 13)} ^ {rotr(a, 22)}"
        maj = f"({a} & {b}) ^ ({a} & {c}) ^ ({b} & {c})"
        out.append(f"{indent}let t{t}: u32 = {add(h, f'({big1})', f'({ch})', f'0x{K256[t]:08x}', f'w{j}')};")
        out.append(f"{indent}{d} = {add(d, f't{t}')};")
        out.append(f"{indent}{h} = {add(f't{t}', f'({big0})', f'({maj})')};")
    return "\n".join(out)

def sha1_rounds(indent="    "):
    out = []
    names = list("abcde")
    for t in range(80):
        a, b, c, d, e = (names[(i - t) % 5] for i in range(5))
        j = t % 16
        if t >= 16:
            mix = f"w{(j + 13) % 16} ^ w{(j + 8) % 16} ^ w{(j + 2) % 16} ^ w{j}"
            out.append(f"{indent}let m{t}: u32 = {mix};")
            out.append(f"{indent}w{j} = {rotl(f'm{t}', 1)};")
        if t < 20:
            f, k = f"({b} & {c}) | (!{b} & {d})", "0x5a827999"
        elif t < 40:
            f, k = f"{b} ^ {c} ^ {d}", "0x6ed9eba1"
        elif t < 60:
            f, k = f"({b} & {c}) | ({b} & {d}) | ({c} & {d})", "0x8f1bbcdc"
        else:
            f, k = f"{b} ^ {c} ^ {d}", "0xca62c1d6"
        out.append(f"{indent}{e} = {add(e, rotl(a, 5), f'({f})', k, f'w{j}')};")
        out.append(f"{indent}{b} = {rotl(b, 30)};")
    return "\n".join(out)

def vec(words):
    return "u32x4.new(" + ", ".join(f"0x{w:08x}" for w in words) + ")"

def u8(v):
    return f"u8x16.from_bits(u32x4.to_bits({v}))"

def sha256_ni(indent="    "):
    """Intel's SHA-NI sequence: 16 groups of four rounds on ABEF/CDGH."""
    out = []
    for k in range(4):
        out.append(f"{indent}let mut m{k} = u32x4.load_be(data, n, at + {16 * k}, _);")
    out.append(f"{indent}let mut s0 = abef;")
    out.append(f"{indent}let mut s1 = cdgh;")
    for g in range(16):
        cur, prev, nxt = g % 4, (g - 1) % 4, (g + 1) % 4
        out.append(f"{indent}let wk{g} = u32x4.wrapping_add(m{cur}, {vec(K256[4 * g:4 * g + 4])});")
        out.append(f"{indent}s1 = x86.sha256rnds2(sha, s1, s0, wk{g});")
        out.append(f"{indent}s0 = x86.sha256rnds2(sha, s0, s1, swap_halves(wk{g}));")
        if 3 <= g <= 14:
            out.append(f"{indent}let t{g} = align4(m{cur}, m{prev});")
            out.append(f"{indent}m{nxt} = x86.sha256msg2(sha, u32x4.wrapping_add(m{nxt}, t{g}), m{cur});")
        if 1 <= g <= 12:
            out.append(f"{indent}m{prev} = x86.sha256msg1(sha, m{prev}, m{cur});")
    return "\n".join(out)

def sha1_ni(indent="    "):
    """Intel's SHA-NI sequence: 20 groups of four rounds."""
    out = []
    for k in range(4):
        out.append(f"{indent}let mut m{k} = reverse(u32x4.load_be(data, n, at + {16 * k}, _));")
    for g in range(20):
        cur, nxt = g % 4, (g + 1) % 4
        func = g // 5
        if g == 0:
            out.append(f"{indent}e0 = u32x4.wrapping_add(e0, m0);")
            out.append(f"{indent}e1 = abcd;")
            out.append(f"{indent}abcd = x86.sha1rnds4(sha, abcd, e0, 0, _);")
        else:
            (use, keep) = ("e1", "e0") if g % 2 == 1 else ("e0", "e1")
            out.append(f"{indent}{use} = x86.sha1nexte(sha, {use}, m{cur});")
            out.append(f"{indent}{keep} = abcd;")
            if 3 <= g <= 18:
                out.append(f"{indent}m{nxt} = x86.sha1msg2(sha, m{nxt}, m{cur});")
            out.append(f"{indent}abcd = x86.sha1rnds4(sha, abcd, {use}, {func}, _);")
        if 1 <= g <= 16:
            out.append(f"{indent}m{(g - 1) % 4} = x86.sha1msg1(sha, m{(g - 1) % 4}, m{cur});")
        if 2 <= g <= 17:
            out.append(f"{indent}m{(g - 2) % 4} = u32x4.xor(m{(g - 2) % 4}, m{cur});")
    return "\n".join(out)

def replace(path, marker, body):
    text = path.read_text()
    start, end = f"// BEGIN GENERATED {marker}", f"// END GENERATED {marker}"
    pattern = re.compile(r"(\n[ ]*" + re.escape(start) + r"[^\n]*\n).*?([ ]*" + re.escape(end) + ")", re.S)
    if not pattern.search(text):
        raise SystemExit(f"{path}: markers {marker} not found")
    text = pattern.sub(lambda m: m.group(1) + body + "\n" + m.group(2), text, count=1)
    path.write_text(text)

replace(STD / "sha256.kush", "rounds", sha256_rounds())
replace(STD / "sha256.kush", "ni-rounds", sha256_ni())
replace(STD / "sha1.kush", "ni-rounds", sha1_ni())
replace(STD / "sha1.kush", "rounds", sha1_rounds())
print("generated")
