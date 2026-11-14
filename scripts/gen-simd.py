#!/usr/bin/env python3
"""Generate crates/kush/std/simd.kush: the vector types of std.simd.

128-bit types (SIMD-TYPES, SIMD-OPS) are structs of two private u64 words,
256-bit types (SIMD-256) of four, in x86 lane order (lane 0 is the low bits
of the first word): a vector is exactly the words of the register it stands
for. Every function is ordinary checked Kush: lane indices are erased
preconditions, shift amounts are constants or proved (SHIFT-ELIDE), and the
functions have empty effect rows (except the pushes). The native backends
replace recognised operations with vector instructions (SIMD-NATIVE); this
code stays their specification and the reference evaluator's implementation.

256-bit types have no lane permutations of their own (AVX2 shuffles work
within 128-bit halves too): use `low`, `high` and `from_halves` with the
128-bit shuffles.

Usage: scripts/gen-simd.py   (rewrites crates/kush/std/simd.kush)
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "crates/kush/std/simd.kush"

# (lane type, lane bits, signed)
LANES = [("u8", 8, False), ("u16", 16, False), ("u32", 32, False), ("u64", 64, False),
         ("i8", 8, True), ("i16", 16, True), ("i32", 32, True), ("i64", 64, True)]


def type_name(lane, width):
    return f"{lane}x{width // int(lane[1:])}"


def lane_bits(lane, bits, signed):
    """A lane value as its zero-extended bit pattern in a u64."""
    if bits == 64:
        return f"Int.truncate::<u64>({lane})" if signed else lane
    if signed:
        return f"Int.convert::<u64>(Int.truncate::<u{bits}>({lane}))"
    return f"Int.convert::<u64>({lane})"


def from_word(expr, lane, bits, signed):
    """The lane value of the low `bits` bits of a u64 expression."""
    if bits == 64:
        return f"Int.truncate::<i64>({expr})" if signed else expr
    return f"Int.truncate::<{lane}>({expr})"


def splat_const(value, bits):
    word = 0
    for k in range(64 // bits):
        word |= value << (k * bits)
    return word


def record(words, values):
    return "Self { " + ", ".join(f"w{k}: {v}" for k, v in zip(range(words), values)) + " }"


def branches(words, per_word, body_of):
    """An if/else chain over the word holding lane `i`."""
    if words == 1:
        return body_of(0, "i")
    lines = []
    for w in range(words):
        base = w * per_word
        index = "i" if base == 0 else f"(i - {base})"
        if w == 0:
            lines.append(f"if i < {base + per_word} {{")
        elif w < words - 1:
            lines.append(f"}} else if i < {base + per_word} {{")
        else:
            lines.append("} else {")
        lines += ["    " + line for line in body_of(w, index)]
    lines.append("}")
    return lines


def gen_type(lane, bits, signed, width):
    name = type_name(lane, width)
    words = width // 64
    count = width // bits
    per_word = 64 // bits
    lanemax = (1 << bits) - 1
    high = splat_const(1 << (bits - 1), bits)
    not_high = (~high) & ((1 << 64) - 1)
    ones = splat_const(1, bits)
    ws = [f"w{k}" for k in range(words)]
    out = [f"/// {count} lanes of `{lane}` in {width} bits.", f"pub struct {name} {{"]
    out += [f"    w{k}: u64," for k in range(words)]
    out += ["}", "", f"impl {name} {{"]

    def fn(doc, signature, body, effects="{}", public=True):
        out.append(f"    /// {doc}")
        out.append(f"    {'pub ' if public else ''}fn {signature} ! {effects} {{")
        out.extend(f"        {line}" for line in body)
        out.append("    }")
        out.append("")

    # construction
    body = []
    for w in range(words):
        terms = []
        for k in range(per_word):
            value = lane_bits(f"l{w * per_word + k}", bits, signed)
            terms.append(value if k == 0 else f"({value} << {k * bits})")
        body.append(f"let w{w}: u64 = {' | '.join(terms)};")
    body.append(record(words, ws))
    fn(f"The vector with lanes `l0` (lowest) to `l{count - 1}`.",
       f"new({', '.join(f'l{i}: {lane}' for i in range(count))}) -> {name}", body)
    body = [f"let b: u64 = {lane_bits('x', bits, signed)};"]
    if bits == 64:
        body.append(record(words, ["b"] * words))
    else:
        terms = ["b"] + [f"(b << {k * bits})" for k in range(1, per_word)]
        body += [f"let w: u64 = {' | '.join(terms)};", record(words, ["w"] * words)]
    fn("Every lane `x`.", f"splat(x: {lane}) -> {name}", body)
    fn("Every lane zero.", f"zero() -> {name}", [record(words, ["0"] * words)])
    # lane access
    pre = f"0 <= i && i <= {count - 1}"

    def read(w, index):
        value = f"v.w{w}" if per_word == 1 else f"v.w{w} >> ({bits} * {index})"
        return [from_word(value, lane, bits, signed)]
    fn("Lane `i` (0 is the lowest).", f"lane(v: {name}, i: i64, erased q: {{ {pre} }}) -> {lane}",
       branches(words, per_word, read))

    def write(w, index):
        lines = []
        if per_word == 1:
            new_word = "b"
        else:
            lines.append(f"let s = {bits} * {index};")
            new_word = f"(v.w{w} & !(mask << s)) | (b << s)"
        lines.append(record(words, [new_word if k == w else f"v.w{k}" for k in range(words)]))
        return lines
    fn("`v` with lane `i` replaced by `x`.",
       f"with_lane(v: {name}, i: i64, x: {lane}, erased q: {{ {pre} }}) -> {name}",
       [f"let b: u64 = {lane_bits('x', bits, signed)};", f"let mask: u64 = {lanemax};"]
       + branches(words, per_word, write))
    fn("Whether every lane is equal.", f"eq(a: {name}, b: {name}) -> Bool",
       [" && ".join(f"a.w{k} == b.w{k}" for k in range(words))])
    tuple_ty = "(" + ", ".join(["u64"] * words) + ")"
    fn("The bits as words, low word first (for reinterpreting).",
       f"to_bits(v: {name}) -> {tuple_ty}", ["(" + ", ".join(f"v.w{k}" for k in range(words)) + ")"])
    fn("The vector with these bits, low word first.", f"from_bits(bits: {tuple_ty}) -> {name}",
       [f"let ({', '.join(ws)}) = bits;", record(words, ws)])
    if words == 4:
        half = type_name(lane, 128)
        fn("The low half of the lanes, as a 128-bit vector.", f"low(v: {name}) -> {half}",
           [f"{half}.from_bits((v.w0, v.w1))"])
        fn("The high half of the lanes, as a 128-bit vector.", f"high(v: {name}) -> {half}",
           [f"{half}.from_bits((v.w2, v.w3))"])
        fn("The vector with `lo` in its low lanes and `hi` in its high lanes.",
           f"from_halves(lo: {half}, hi: {half}) -> {name}",
           [f"let (w0, w1) = {half}.to_bits(lo);", f"let (w2, w3) = {half}.to_bits(hi);", record(words, ws)])
    # lane-wise operations
    two = f"a: {name}, b: {name}"

    def each(f):
        return record(words, [f(k) for k in range(words)])
    fn("Lane-wise `&`.", f"and({two}) -> {name}", [each(lambda k: f"a.w{k} & b.w{k}")])
    fn("Lane-wise `|`.", f"or({two}) -> {name}", [each(lambda k: f"a.w{k} | b.w{k}")])
    fn("Lane-wise `^`.", f"xor({two}) -> {name}", [each(lambda k: f"a.w{k} ^ b.w{k}")])
    fn("Lane-wise `!`.", f"not(v: {name}) -> {name}", [each(lambda k: f"!v.w{k}")])
    if bits == 64:
        fn("Lane-wise addition modulo 2^64.", f"wrapping_add({two}) -> {name}",
           [each(lambda k: f"Int.wrapping_add::<u64>(a.w{k}, b.w{k})")])
        fn("Lane-wise subtraction modulo 2^64.", f"wrapping_sub({two}) -> {name}",
           [each(lambda k: f"Int.wrapping_sub::<u64>(a.w{k}, b.w{k})")])
    else:
        # The low bits of every lane add without crossing into the next
        # lane; the top bit is the xor of the operands' top bits and carry.
        fn(f"Lane-wise addition modulo 2^{bits}.", f"wrapping_add({two}) -> {name}",
           [each(lambda k: f"Int.wrapping_add::<u64>(a.w{k} & {not_high}, b.w{k} & {not_high}) ^ ((a.w{k} ^ b.w{k}) & {high})")])
        fn(f"Lane-wise subtraction modulo 2^{bits}.", f"wrapping_sub({two}) -> {name}",
           [each(lambda k: f"Int.wrapping_sub::<u64>(a.w{k} | {high}, b.w{k} & {not_high}) ^ ((a.w{k} ^ !b.w{k}) & {high})")])
    shift_pre = f"0 <= n && n <= {bits - 1}"
    shift_sig = lambda op: f"{op}(v: {name}, n: i64, erased q: {{ {shift_pre} }}) -> {name}"
    if bits == 64:
        fn("Every lane shifted left by `n` (high bits dropped).", shift_sig("shl"), [each(lambda k: f"v.w{k} << n")])
        if signed:
            fn("Every lane shifted right by `n`, keeping its sign.", shift_sig("shr"),
               [each(lambda k: f"Int.truncate::<u64>(Int.truncate::<i64>(v.w{k}) >> n)")])
        else:
            fn("Every lane shifted right by `n`.", shift_sig("shr"), [each(lambda k: f"v.w{k} >> n")])
    else:
        fn("Every lane shifted left by `n` (high bits dropped).", shift_sig("shl"),
           [f"let lanemax: u64 = {lanemax};",
            f"let keep: u64 = Int.wrapping_mul::<u64>((lanemax << n) & lanemax, {ones});",
            each(lambda k: f"(v.w{k} << n) & keep")])
        if signed:
            # Logical shift, then the top `n` bits of each negative lane set.
            fn("Every lane shifted right by `n`, keeping its sign.", shift_sig("shr"),
               [f"let lanemax: u64 = {lanemax};",
                f"let keep: u64 = Int.wrapping_mul::<u64>(lanemax >> n, {ones});",
                f"let fill: u64 = Int.wrapping_mul::<u64>(lanemax ^ (lanemax >> n), {ones});",
                each(lambda k: f"((v.w{k} >> n) & keep) | (Int.wrapping_mul::<u64>((v.w{k} & {high}) >> {bits - 1}, lanemax) & fill)")])
        else:
            fn("Every lane shifted right by `n`.", shift_sig("shr"),
               [f"let lanemax: u64 = {lanemax};",
                f"let keep: u64 = Int.wrapping_mul::<u64>(lanemax >> n, {ones});",
                each(lambda k: f"(v.w{k} >> n) & keep")])
    if bits == 64:
        fn("All ones in every lane where `a` and `b` are equal, zero elsewhere.", f"eq_lanes({two}) -> {name}",
           [f"let m{k}: u64 = if a.w{k} == b.w{k} {{ 18446744073709551615 }} else {{ 0 }};" for k in range(words)]
           + [record(words, [f"m{k}" for k in range(words)])])
    else:
        # A lane of x = a ^ b is nonzero iff adding all-ones to its low bits
        # carries into its top bit, or its top bit is set.
        nz = lambda x: f"(Int.wrapping_add::<u64>({x} & {not_high}, {not_high}) | {x}) & {high}"
        fn("All ones in every lane where `a` and `b` are equal, zero elsewhere.", f"eq_lanes({two}) -> {name}",
           [f"let lanemax: u64 = {lanemax};"] + [f"let x{k} = a.w{k} ^ b.w{k};" for k in range(words)]
           + [each(lambda k: f"Int.wrapping_mul::<u64>((!({nz(f'x{k}')}) & {high}) >> {bits - 1}, lanemax)")])
    # permutations (128-bit types)
    if words == 2:
        params = ", ".join(f"i{k}: i64" for k in range(count))
        pre_one = " && ".join(f"0 <= i{k} && i{k} <= {count - 1}" for k in range(count))
        fn("Lane `k` of the result is lane `i<k>` of `v`.",
           f"shuffle(v: {name}, {params}, erased q: {{ {pre_one} }}) -> {name}",
           [f"{name}.new({', '.join(f'{name}.lane(v, i{k}, _)' for k in range(count))})"])
        fn(f"Lane `i` of `a` for `i < {count}`, else lane `i - {count}` of `b`.",
           f"pick(a: {name}, b: {name}, i: i64, erased q: {{ 0 <= i && i <= {2 * count - 1} }}) -> {lane}",
           [f"if i < {count} {{ {name}.lane(a, i, _) }} else {{ {name}.lane(b, i - {count}, _) }}"],
           public=False)
        pre_two = " && ".join(f"0 <= i{k} && i{k} <= {2 * count - 1}" for k in range(count))
        fn(f"Lane `k` of the result is lane `i<k>` of `a` then `b` side by side (indices {count} and up name lanes of `b`).",
           f"shuffle2({two}, {params}, erased q: {{ {pre_two} }}) -> {name}",
           [f"{name}.new({', '.join(f'{name}.pick(a, b, i{k}, _)' for k in range(count))})"])
        if bits == 8:
            fn("Bytes `k` to `k + 15` of `lo` then `hi` side by side (x86 `palignr hi, lo, k`).",
               f"align_right(hi: {name}, lo: {name}, k: i64, erased q: {{ 0 <= k && k <= 16 }}) -> {name}",
               [f"{name}.shuffle2(lo, hi, {', '.join(f'k + {j}' for j in range(16))}, _)"])
    if bits > 8:
        if words == 2:
            size = bits // 8
            perm = [l * size + (size - 1 - j) for l in range(16 // size) for j in range(size)]
            fn("Every lane with its bytes reversed (big-endian <-> little-endian).",
               f"swap_bytes(v: {name}) -> {name}",
               [f"let b = u8x16.from_bits({name}.to_bits(v));",
                f"{name}.from_bits(u8x16.to_bits(u8x16.shuffle(b, {', '.join(map(str, perm))}, _)))"])
        else:
            half = type_name(lane, 128)
            fn("Every lane with its bytes reversed (big-endian <-> little-endian).",
               f"swap_bytes(v: {name}) -> {name}",
               [f"{name}.from_halves({half}.swap_bytes({name}.low(v)), {half}.swap_bytes({name}.high(v)))"])
    # loads and pushes
    nbytes = width // 8
    pre_load = f"0 <= at && at + {nbytes} <= n && n == Bytes.len(data)"
    for big in (False, True):
        body = []
        for w in range(words):
            terms = []
            for j in range(8):
                b = 8 * w + j
                if big and bits > 8:
                    size = bits // 8
                    shift = ((b % 8) // size) * bits + 8 * (size - 1 - b % size)
                else:
                    shift = 8 * j
                body.append(f"let b{w}{j}: u64 = Int.truncate(Bytes.at(data, at + {b}, _));")
                terms.append(f"b{w}{j}" if shift == 0 else f"(b{w}{j} << {shift})")
            body.append(f"let w{w}: u64 = {' | '.join(terms)};")
        body.append(record(words, ws))
        order = "big" if big else "little"
        fn(f"The {nbytes} bytes at data[at..at + {nbytes}], each lane {order}-endian (built with shifts, not a byte shuffle). `n` is `Bytes.len(data)`, an `i64` local of the caller.",
           f"load_{'be' if big else 'le'}(data: &Bytes, n: i64, at: i64, erased q: {{ {pre_load} }}) -> {name}", body)
    body = ["let mut out = out;"]
    for w in range(words):
        for j in range(8):
            body.append(f"out = Bytes.push(out, Int.truncate::<i64>((v.w{w} >> {8 * j}) & 255));")
    body.append("out")
    fn(f"`out` with the {nbytes} bytes of `v` appended, each lane little-endian.",
       f"push_le(out: Bytes, v: {name}) -> Bytes", body, effects="{alloc, panic}")
    fn(f"`out` with the {nbytes} bytes of `v` appended, each lane big-endian.",
       f"push_be(out: Bytes, v: {name}) -> Bytes",
       [f"{name}.push_le(out, v)" if bits == 8 else f"{name}.push_le(out, {name}.swap_bytes(v))"],
       effects="{alloc, panic}")
    out[-1:] = ["}"]
    return "\n".join(out)


HEADER = """module std.simd;

// @generated by scripts/gen-simd.py. Do not edit by hand.
//
// Vector value types (docs/simd.md): 128-bit u8x16, u16x8, u32x4, u64x2 and
// signed forms (two words), 256-bit u8x32, u16x16, u32x8, u64x4 and signed
// forms (four words):
//
//     use std.simd.u32x4;
//     let v = u32x4.new(1, 2, 3, 4);
//     let x = u32x4.lane(v, 2, _);              // 3; the index is proved
//     let w = u32x4.with_lane(v, 0, 9, _);
//     let bytes = u8x16.from_bits(u32x4.to_bits(v));
//     let s = u32x4.wrapping_add(v, u32x4.splat(1));   // lane-wise
//     let m = u32x4.load_be(&data, n, at, _);          // bounds proved
//
// Lane 0 is the low bits of the first word (x86 order). Every function has
// an empty effect row except the pushes: lane indices are erased
// preconditions and every shift amount is proved. 256-bit types split into
// 128-bit halves with low, high and from_halves.
"""


def main():
    parts = [HEADER]
    for width in (128, 256):
        for lane, bits, signed in LANES:
            parts.append(gen_type(lane, bits, signed, width))
    OUT.write_text("\n\n".join(parts) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)}")


main()
