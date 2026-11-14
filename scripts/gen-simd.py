#!/usr/bin/env python3
"""Generate crates/kush/std/simd.kush: the 128-bit vector types (SIMD-TYPES).

Each type is a struct of two private u64 words in x86 lane order (lane 0 is
the low bits of the first word), so a vector is exactly two words, like the
XMM register it stands for. Every function is ordinary checked Kush: lane
indices are erased preconditions, shift amounts are constants or proved
(SHIFT-ELIDE), and the functions have empty effect rows. The native
backends may later replace recognised operations with vector instructions
(SIMD-OPS); this code stays their specification and the reference
evaluator's implementation.

Usage: scripts/gen-simd.py   (rewrites crates/kush/std/simd.kush)
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "crates/kush/std/simd.kush"

# (name, lane type, lane bits, signed)
TYPES = [
    ("u8x16", "u8", 8, False),
    ("u16x8", "u16", 16, False),
    ("u32x4", "u32", 32, False),
    ("u64x2", "u64", 64, False),
    ("i8x16", "i8", 8, True),
    ("i16x8", "i16", 16, True),
    ("i32x4", "i32", 32, True),
    ("i64x2", "i64", 64, True),
]

def unsigned(bits):
    return f"u{bits}"

def lane_bits(lane, bits, signed):
    """A lane value as its zero-extended bit pattern in a u64."""
    if bits == 64:
        return f"Int.truncate::<u64>({lane})" if signed else lane
    if signed:
        return f"Int.convert::<u64>(Int.truncate::<{unsigned(bits)}>({lane}))"
    return f"Int.convert::<u64>({lane})"

def from_bits(expr, lane, bits, signed):
    """The lane value of the low `bits` bits of a u64 expression."""
    if bits == 64:
        return f"Int.truncate::<i64>({expr})" if signed else expr
    return f"Int.truncate::<{lane}>({expr})"

def gen_type(name, lane, bits, signed):
    count = 128 // bits
    per_word = 64 // bits
    mask = (1 << bits) - 1
    out = []
    out.append(f"/// {count} lanes of `{lane}` in 128 bits.")
    out.append(f"pub struct {name} {{")
    out.append("    w0: u64,")
    out.append("    w1: u64,")
    out.append("}")
    out.append("")
    out.append(f"impl {name} {{")
    # new
    params = ", ".join(f"l{i}: {lane}" for i in range(count))
    out.append(f"    /// The vector with lanes `l0` (lowest) to `l{count - 1}`.")
    out.append(f"    pub fn new({params}) -> {name} ! {{}} {{")
    for w in range(2):
        terms = []
        for k in range(per_word):
            i = w * per_word + k
            value = lane_bits(f"l{i}", bits, signed)
            shift = k * bits
            terms.append(value if shift == 0 else f"({value} << {shift})")
        out.append(f"        let w{w}: u64 = {' | '.join(terms)};")
    out.append("        Self { w0: w0, w1: w1 }")
    out.append("    }")
    out.append("")
    # splat
    out.append(f"    /// Every lane `x`.")
    out.append(f"    pub fn splat(x: {lane}) -> {name} ! {{}} {{")
    out.append(f"        let b: u64 = {lane_bits('x', bits, signed)};")
    if bits == 64:
        out.append("        Self { w0: b, w1: b }")
    else:
        terms = ["b"] + [f"(b << {k * bits})" for k in range(1, per_word)]
        out.append(f"        let w: u64 = {' | '.join(terms)};")
        out.append("        Self { w0: w, w1: w }")
    out.append("    }")
    out.append("")
    # zero
    out.append("    /// Every lane zero.")
    out.append(f"    pub fn zero() -> {name} ! {{}} {{")
    out.append("        Self { w0: 0, w1: 0 }")
    out.append("    }")
    out.append("")
    # lane
    out.append(f"    /// Lane `i` (0 is the lowest).")
    out.append(f"    pub fn lane(v: {name}, i: i64, erased q: {{ 0 <= i && i <= {count - 1} }}) -> {lane} ! {{}} {{")
    if per_word == 1:
        out.append(f"        if i == 0 {{ {from_bits('v.w0', lane, bits, signed)} }} else {{ {from_bits('v.w1', lane, bits, signed)} }}")
    else:
        out.append(f"        if i < {per_word} {{")
        out.append(f"            {from_bits(f'v.w0 >> ({bits} * i)', lane, bits, signed)}")
        out.append("        } else {")
        out.append(f"            {from_bits(f'v.w1 >> ({bits} * (i - {per_word}))', lane, bits, signed)}")
        out.append("        }")
    out.append("    }")
    out.append("")
    # with_lane
    out.append(f"    /// `v` with lane `i` replaced by `x`.")
    out.append(f"    pub fn with_lane(v: {name}, i: i64, x: {lane}, erased q: {{ 0 <= i && i <= {count - 1} }}) -> {name} ! {{}} {{")
    if per_word == 1:
        out.append(f"        let b: u64 = {lane_bits('x', bits, signed)};")
        out.append("        if i == 0 { Self { w0: b, w1: v.w1 } } else { Self { w0: v.w0, w1: b } }")
    else:
        out.append(f"        let b: u64 = {lane_bits('x', bits, signed)};")
        out.append(f"        let mask: u64 = {mask};")
        out.append(f"        if i < {per_word} {{")
        out.append(f"            let s = {bits} * i;")
        out.append("            Self { w0: (v.w0 & !(mask << s)) | (b << s), w1: v.w1 }")
        out.append("        } else {")
        out.append(f"            let s = {bits} * (i - {per_word});")
        out.append("            Self { w0: v.w0, w1: (v.w1 & !(mask << s)) | (b << s) }")
        out.append("        }")
    out.append("    }")
    out.append("")
    # eq
    out.append("    /// Whether every lane is equal.")
    out.append(f"    pub fn eq(a: {name}, b: {name}) -> Bool ! {{}} {{")
    out.append("        a.w0 == b.w0 && a.w1 == b.w1")
    out.append("    }")
    out.append("")
    # bits
    out.append("    /// The 128 bits as two words, low word first (for reinterpreting).")
    out.append(f"    pub fn to_bits(v: {name}) -> (u64, u64) ! {{}} {{")
    out.append("        (v.w0, v.w1)")
    out.append("    }")
    out.append("")
    out.append("    /// The vector with these 128 bits, low word first.")
    out.append(f"    pub fn from_bits(bits: (u64, u64)) -> {name} ! {{}} {{")
    out.append("        let (w0, w1) = bits;")
    out.append("        Self { w0: w0, w1: w1 }")
    out.append("    }")
    out.extend(gen_ops(name, lane, bits, signed))
    out.append("}")
    return "\n".join(out)

def splat_const(value, bits):
    """`value` (one lane) repeated in every lane of a 64-bit word."""
    word = 0
    for k in range(64 // bits):
        word |= value << (k * bits)
    return word

def gen_ops(name, lane, bits, signed):
    """SIMD-OPS: lane-wise operations as SWAR on the two words."""
    count = 128 // bits
    lanemax = (1 << bits) - 1
    high = splat_const(1 << (bits - 1), bits)       # the top bit of every lane
    not_high = (~high) & ((1 << 64) - 1)
    ones = splat_const(1, bits)                     # 1 in every lane
    out = [""]
    def word_fn(fn, doc, params, body_w0, body_w1, extra=None, pre=None):
        out.append(f"    /// {doc}")
        sig = f"    pub fn {fn}({params}"
        if pre:
            sig += f", erased q: {{ {pre} }}"
        sig += f") -> {name} ! {{}} {{"
        out.append(sig)
        for line in extra or []:
            out.append(f"        {line}")
        out.append(f"        Self {{ w0: {body_w0}, w1: {body_w1} }}")
        out.append("    }")
        out.append("")
    two = f"a: {name}, b: {name}"
    # bitwise
    word_fn("and", "Lane-wise `&`.", two, "a.w0 & b.w0", "a.w1 & b.w1")
    word_fn("or", "Lane-wise `|`.", two, "a.w0 | b.w0", "a.w1 | b.w1")
    word_fn("xor", "Lane-wise `^`.", two, "a.w0 ^ b.w0", "a.w1 ^ b.w1")
    word_fn("not", "Lane-wise `!`.", f"v: {name}", "!v.w0", "!v.w1")
    # add / sub
    if bits == 64:
        word_fn("wrapping_add", "Lane-wise addition modulo 2^64.", two,
                "Int.wrapping_add::<u64>(a.w0, b.w0)", "Int.wrapping_add::<u64>(a.w1, b.w1)")
        word_fn("wrapping_sub", "Lane-wise subtraction modulo 2^64.", two,
                "Int.wrapping_sub::<u64>(a.w0, b.w0)", "Int.wrapping_sub::<u64>(a.w1, b.w1)")
    else:
        # The low bits of every lane add without crossing into the next lane;
        # the top bit is the xor of the operands' top bits and the carry.
        add = lambda x, y: f"Int.wrapping_add::<u64>({x} & {not_high}, {y} & {not_high}) ^ (({x} ^ {y}) & {high})"
        sub = lambda x, y: f"Int.wrapping_sub::<u64>({x} | {high}, {y} & {not_high}) ^ (({x} ^ !{y}) & {high})"
        word_fn("wrapping_add", f"Lane-wise addition modulo 2^{bits}.", two, add("a.w0", "b.w0"), add("a.w1", "b.w1"))
        word_fn("wrapping_sub", f"Lane-wise subtraction modulo 2^{bits}.", two, sub("a.w0", "b.w0"), sub("a.w1", "b.w1"))
    # shifts
    pre = f"0 <= n && n <= {bits - 1}"
    if bits == 64:
        word_fn("shl", "Every lane shifted left by `n` (high bits dropped).", f"v: {name}, n: i64",
                "v.w0 << n", "v.w1 << n", pre=pre)
        if signed:
            word_fn("shr", "Every lane shifted right by `n`, keeping its sign.", f"v: {name}, n: i64",
                    "Int.truncate::<u64>(Int.truncate::<i64>(v.w0) >> n)",
                    "Int.truncate::<u64>(Int.truncate::<i64>(v.w1) >> n)", pre=pre)
        else:
            word_fn("shr", "Every lane shifted right by `n`.", f"v: {name}, n: i64",
                    "v.w0 >> n", "v.w1 >> n", pre=pre)
    else:
        word_fn("shl", "Every lane shifted left by `n` (high bits dropped).", f"v: {name}, n: i64",
                "(v.w0 << n) & keep", "(v.w1 << n) & keep",
                extra=[f"let lanemax: u64 = {lanemax};",
                       f"let keep: u64 = Int.wrapping_mul::<u64>((lanemax << n) & lanemax, {ones});"], pre=pre)
        if signed:
            # Logical shift, then the top `n` bits of each negative lane set.
            word_fn("shr", "Every lane shifted right by `n`, keeping its sign.", f"v: {name}, n: i64",
                    f"((v.w0 >> n) & keep) | (Int.wrapping_mul::<u64>((v.w0 & {high}) >> {bits - 1}, lanemax) & fill)",
                    f"((v.w1 >> n) & keep) | (Int.wrapping_mul::<u64>((v.w1 & {high}) >> {bits - 1}, lanemax) & fill)",
                    extra=[f"let lanemax: u64 = {lanemax};",
                           f"let keep: u64 = Int.wrapping_mul::<u64>(lanemax >> n, {ones});",
                           f"let fill: u64 = Int.wrapping_mul::<u64>(lanemax ^ (lanemax >> n), {ones});"], pre=pre)
        else:
            word_fn("shr", "Every lane shifted right by `n`.", f"v: {name}, n: i64",
                    "(v.w0 >> n) & keep", "(v.w1 >> n) & keep",
                    extra=[f"let lanemax: u64 = {lanemax};",
                           f"let keep: u64 = Int.wrapping_mul::<u64>(lanemax >> n, {ones});"], pre=pre)
    # lane equality mask
    if bits == 64:
        out.append("    /// All ones in every lane where `a` and `b` are equal, zero elsewhere.")
        out.append(f"    pub fn eq_lanes({two}) -> {name} ! {{}} {{")
        out.append("        let m0: u64 = if a.w0 == b.w0 { 18446744073709551615 } else { 0 };")
        out.append("        let m1: u64 = if a.w1 == b.w1 { 18446744073709551615 } else { 0 };")
        out.append("        Self { w0: m0, w1: m1 }")
        out.append("    }")
        out.append("")
    else:
        # A lane of x = a ^ b is nonzero iff adding all-ones to its low bits
        # carries into its top bit, or its top bit is set.
        nz = lambda x: f"(Int.wrapping_add::<u64>({x} & {not_high}, {not_high}) | {x}) & {high}"
        word_fn("eq_lanes", "All ones in every lane where `a` and `b` are equal, zero elsewhere.", two,
                f"Int.wrapping_mul::<u64>((!({nz('x0')}) & {high}) >> {bits - 1}, lanemax)",
                f"Int.wrapping_mul::<u64>((!({nz('x1')}) & {high}) >> {bits - 1}, lanemax)",
                extra=[f"let lanemax: u64 = {lanemax};", "let x0 = a.w0 ^ b.w0;", "let x1 = a.w1 ^ b.w1;"])
    # shuffles
    idx = [f"i{k}" for k in range(count)]
    pre_one = " && ".join(f"0 <= i{k} && i{k} <= {count - 1}" for k in range(count))
    out.append(f"    /// Lane `k` of the result is lane `i<k>` of `v`.")
    out.append(f"    pub fn shuffle(v: {name}, {', '.join(f'i{k}: i64' for k in range(count))}, erased q: {{ {pre_one} }}) -> {name} ! {{}} {{")
    out.append(f"        {name}.new({', '.join(f'{name}.lane(v, i{k}, _)' for k in range(count))})")
    out.append("    }")
    out.append("")
    out.append(f"    /// Lane `i` of `a` for `i < {count}`, else lane `i - {count}` of `b`.")
    out.append(f"    fn pick(a: {name}, b: {name}, i: i64, erased q: {{ 0 <= i && i <= {2 * count - 1} }}) -> {lane} ! {{}} {{")
    out.append(f"        if i < {count} {{ {name}.lane(a, i, _) }} else {{ {name}.lane(b, i - {count}, _) }}")
    out.append("    }")
    out.append("")
    pre_two = " && ".join(f"0 <= i{k} && i{k} <= {2 * count - 1}" for k in range(count))
    out.append(f"    /// Lane `k` of the result is lane `i<k>` of `a` then `b` side by side")
    out.append(f"    /// (indices {count} and up name lanes of `b`).")
    out.append(f"    pub fn shuffle2({two}, {', '.join(f'i{k}: i64' for k in range(count))}, erased q: {{ {pre_two} }}) -> {name} ! {{}} {{")
    out.append(f"        {name}.new({', '.join(f'{name}.pick(a, b, i{k}, _)' for k in range(count))})")
    out.append("    }")
    out.append("")
    if bits == 8:
        out.append("    /// Bytes `k` to `k + 15` of `lo` then `hi` side by side (x86 `palignr hi, lo, k`).")
        out.append(f"    pub fn align_right(hi: {name}, lo: {name}, k: i64, erased q: {{ 0 <= k && k <= 16 }}) -> {name} ! {{}} {{")
        out.append(f"        {name}.shuffle2(lo, hi, {', '.join(f'k + {j}' for j in range(16))}, _)")
        out.append("    }")
        out.append("")
    else:
        size = bits // 8
        perm = [l * size + (size - 1 - j) for l in range(16 // size) for j in range(size)]
        out.append("    /// Every lane with its bytes reversed (big-endian <-> little-endian).")
        out.append(f"    pub fn swap_bytes(v: {name}) -> {name} ! {{}} {{")
        out.append(f"        let b = u8x16.from_bits({name}.to_bits(v));")
        out.append(f"        {name}.from_bits(u8x16.to_bits(u8x16.shuffle(b, {', '.join(map(str, perm))}, _)))")
        out.append("    }")
        out.append("")
    # loads and pushes
    pre_load = "0 <= at && at + 16 <= n && n == Bytes.len(data)"
    out.append("    /// The 16 bytes at data[at..at + 16], each lane little-endian. `n` is")
    out.append("    /// `Bytes.len(data)`, an `i64` local of the caller.")
    out.append(f"    pub fn load_le(data: &Bytes, n: i64, at: i64, erased q: {{ {pre_load} }}) -> {name} ! {{}} {{")
    for w in range(2):
        for j in range(8):
            out.append(f"        let b{w}{j}: u64 = Int.truncate(Bytes.at(data, at + {8 * w + j}, _));")
        terms = " | ".join(f"b{w}0" if j == 0 else f"(b{w}{j} << {8 * j})" for j in range(8))
        out.append(f"        let w{w}: u64 = {terms};")
    out.append("        Self { w0: w0, w1: w1 }")
    out.append("    }")
    out.append("")
    out.append("    /// The 16 bytes at data[at..at + 16], each lane big-endian.")
    out.append(f"    pub fn load_be(data: &Bytes, n: i64, at: i64, erased q: {{ {pre_load} }}) -> {name} ! {{}} {{")
    out.append(f"        {name}.load_le(data, n, at, _)" if bits == 8 else f"        {name}.swap_bytes({name}.load_le(data, n, at, _))")
    out.append("    }")
    out.append("")
    out.append("    /// `out` with the 16 bytes of `v` appended, each lane little-endian.")
    out.append(f"    pub fn push_le(out: Bytes, v: {name}) -> Bytes ! {{alloc, panic}} {{")
    out.append("        let mut out = out;")
    for w in range(2):
        for j in range(8):
            out.append(f"        out = Bytes.push(out, Int.truncate::<i64>((v.w{w} >> {8 * j}) & 255));")
    out.append("        out")
    out.append("    }")
    out.append("")
    out.append("    /// `out` with the 16 bytes of `v` appended, each lane big-endian.")
    out.append(f"    pub fn push_be(out: Bytes, v: {name}) -> Bytes ! {{alloc, panic}} {{")
    out.append(f"        {name}.push_le(out, v)" if bits == 8 else f"        {name}.push_le(out, {name}.swap_bytes(v))")
    out.append("    }")
    return out

HEADER = """module std.simd;

// @generated by scripts/gen-simd.py. Do not edit by hand.
//
// 128-bit vector value types (SIMD-TYPES, docs/simd.md):
//
//     use std.simd.u32x4;
//     let v = u32x4.new(1, 2, 3, 4);
//     let x = u32x4.lane(v, 2, _);              // 3; the index is proved
//     let w = u32x4.with_lane(v, 0, 9, _);
//     let bytes = u8x16.from_bits(u32x4.to_bits(v));
//     let s = u32x4.wrapping_add(v, u32x4.splat(1));   // lane-wise (SIMD-OPS)
//     let m = u32x4.load_be(&data, n, at, _);          // bounds proved
//
// Each type is two private u64 words in x86 lane order (lane 0 is the low
// bits of the first word): a vector is exactly the two words of the XMM
// register it stands for. Every function has an empty effect row: lane
// indices are erased preconditions and every shift amount is proved.
"""

def main():
    parts = [HEADER]
    for t in TYPES:
        parts.append(gen_type(*t))
    OUT.write_text("\n\n".join(parts) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)}")

main()
