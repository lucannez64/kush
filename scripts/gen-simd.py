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
    out.append("}")
    return "\n".join(out)

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
