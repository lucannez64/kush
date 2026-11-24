//! SIMD-OPS: the lane-wise operations of `std.simd` against a model of every
//! lane computed here in Rust, on pseudo-random inputs, for all eight 128-bit
//! types. Both backends must agree with the model and the evaluator must free
//! every allocation.
use kush::executable::check;

#[derive(Clone, Copy)]
struct Kind {
    name: &'static str,
    bits: u32,
    signed: bool,
    width: u32,
}

const fn kind(name: &'static str, bits: u32, signed: bool, width: u32) -> Kind {
    Kind {
        name,
        bits,
        signed,
        width,
    }
}

const KINDS: [Kind; 16] = [
    kind("u8x16", 8, false, 128),
    kind("u16x8", 16, false, 128),
    kind("u32x4", 32, false, 128),
    kind("u64x2", 64, false, 128),
    kind("i8x16", 8, true, 128),
    kind("i16x8", 16, true, 128),
    kind("i32x4", 32, true, 128),
    kind("i64x2", 64, true, 128),
    // SIMD-256: four words, lane-wise operations per 128-bit half.
    kind("u8x32", 8, false, 256),
    kind("u16x16", 16, false, 256),
    kind("u32x8", 32, false, 256),
    kind("u64x4", 64, false, 256),
    kind("i8x32", 8, true, 256),
    kind("i16x16", 16, true, 256),
    kind("i32x8", 32, true, 256),
    kind("i64x4", 64, true, 256),
];

impl Kind {
    fn count(self) -> usize {
        (self.width / self.bits) as usize
    }
    fn bytes(self) -> usize {
        (self.width / 8) as usize
    }
    fn mask(self) -> u128 {
        if self.bits == 64 {
            u64::MAX as u128
        } else {
            (1u128 << self.bits) - 1
        }
    }
    /// The lane value of a bit pattern.
    fn value(self, raw: u128) -> i128 {
        let raw = raw & self.mask();
        if self.signed && raw >> (self.bits - 1) & 1 == 1 {
            raw as i128 - (1i128 << self.bits)
        } else {
            raw as i128
        }
    }
    fn raw(self, value: i128) -> u128 {
        (value as u128) & self.mask()
    }
    fn lanes_of_bytes(self, bytes: &[u8], big: bool) -> Vec<i128> {
        let size = (self.bits / 8) as usize;
        bytes
            .chunks(size)
            .map(|chunk| {
                let mut raw = 0u128;
                for (k, byte) in chunk.iter().enumerate() {
                    let shift = if big { 8 * (size - 1 - k) } else { 8 * k };
                    raw |= (*byte as u128) << shift;
                }
                self.value(raw)
            })
            .collect()
    }
    fn bytes_of_lanes(self, lanes: &[i128], big: bool) -> Vec<u8> {
        let size = (self.bits / 8) as usize;
        let mut out = Vec::new();
        for lane in lanes {
            let raw = self.raw(*lane);
            for k in 0..size {
                let shift = if big { 8 * (size - 1 - k) } else { 8 * k };
                out.push((raw >> shift) as u8);
            }
        }
        out
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11 ^ self.0 << 7
    }
    fn lanes(&mut self, kind: Kind) -> Vec<i128> {
        (0..kind.count())
            .map(|_| {
                // Mix extremes in so carries, sign bits and zero lanes appear.
                let raw = match self.next() % 6 {
                    0 => 0,
                    1 => kind.mask(),
                    2 => 1u128 << (kind.bits - 1),
                    _ => (self.next() as u128 | (self.next() as u128) << 64) & kind.mask(),
                };
                kind.value(raw)
            })
            .collect()
    }
}

fn list(lanes: &[i128]) -> String {
    lanes
        .iter()
        .map(i128::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn run(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    let output = String::from_utf8(output).unwrap();
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("simd-ops");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some(0),
            "{}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(
            String::from_utf8(native.stdout).unwrap(),
            output,
            "native and evaluator differ"
        );
        // SIMD-CRANELIFT-FEATURES: the same with the host's CPU features.
        let host = scratch.path().join("simd-ops-host");
        let mut options = kush::native::CodegenOptions::release();
        options.native_cpu = true;
        kush::native::build_with_codegen(
            &program,
            &host,
            false,
            &kush::native::LinkSpec::default(),
            options,
        )
        .unwrap();
        let native = std::process::Command::new(&host).output().unwrap();
        assert_eq!(
            String::from_utf8(native.stdout).unwrap(),
            output,
            "host-feature build differs"
        );
    }
    output
}

fn check_kind(kind: Kind, seed: u64) {
    let t = kind.name;
    let n = kind.count();
    let mut rng = Rng(seed);
    let a = rng.lanes(kind);
    let b = rng.lanes(kind);
    // c equals a in the even lanes and b in the odd ones.
    let c: Vec<i128> = (0..n)
        .map(|i| if i % 2 == 0 { a[i] } else { b[i] })
        .collect();
    let map2 = |f: &dyn Fn(u128, u128) -> u128| -> Vec<i128> {
        (0..n)
            .map(|i| kind.value(f(kind.raw(a[i]), kind.raw(b[i]))))
            .collect()
    };
    let mut body = String::new();
    let mut expected: Vec<Vec<i128>> = Vec::new();
    let mut show = |call: String, lanes: Vec<i128>, body: &mut String| {
        body.push_str(&format!("show({call});\n"));
        expected.push(lanes);
    };
    show(
        format!("{t}.wrapping_add(a, b)"),
        map2(&|x, y| x.wrapping_add(y)),
        &mut body,
    );
    show(
        format!("{t}.wrapping_sub(a, b)"),
        map2(&|x, y| x.wrapping_sub(y)),
        &mut body,
    );
    show(format!("{t}.and(a, b)"), map2(&|x, y| x & y), &mut body);
    show(format!("{t}.or(a, b)"), map2(&|x, y| x | y), &mut body);
    show(format!("{t}.xor(a, b)"), map2(&|x, y| x ^ y), &mut body);
    show(format!("{t}.not(a)"), map2(&|x, _| !x), &mut body);
    for s in [0, 1, kind.bits / 2 + 1, kind.bits - 1] {
        let shl = (0..n).map(|i| kind.value(kind.raw(a[i]) << s)).collect();
        show(format!("{t}.shl(a, {s}, _)"), shl, &mut body);
        let shr = (0..n)
            .map(|i| {
                if kind.signed {
                    kind.value(kind.raw(a[i] >> s))
                } else {
                    a[i] >> s
                }
            })
            .collect();
        show(format!("{t}.shr(a, {s}, _)"), shr, &mut body);
    }
    let all_ones = kind.value(kind.mask());
    let eq = (0..n)
        .map(|i| if a[i] == c[i] { all_ones } else { 0 })
        .collect();
    show(format!("{t}.eq_lanes(a, c)"), eq, &mut body);
    let wide = kind.width == 256;
    let reversed: Vec<usize> = (0..n).rev().collect();
    if !wide {
        show(
            format!(
                "{t}.shuffle(a, {}, _)",
                reversed
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            reversed.iter().map(|&i| a[i]).collect(),
            &mut body,
        );
        let interleave: Vec<usize> = (0..n)
            .map(|k| if k % 2 == 0 { k / 2 } else { n + k / 2 })
            .collect();
        let both: Vec<i128> = a.iter().chain(b.iter()).copied().collect();
        show(
            format!(
                "{t}.shuffle2(a, b, {}, _)",
                interleave
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            interleave.iter().map(|&i| both[i]).collect(),
            &mut body,
        );
    }
    let a_le = kind.bytes_of_lanes(&a, false);
    if kind.bits > 8 {
        show(
            format!("{t}.swap_bytes(a)"),
            kind.lanes_of_bytes(&a_le, true),
            &mut body,
        );
    } else if !wide {
        let b_le = kind.bytes_of_lanes(&b, false);
        for k in [0usize, 5, 16] {
            let joined: Vec<u8> = b_le.iter().chain(a_le.iter()).copied().collect();
            show(
                format!("{t}.align_right(a, b, {k}, _)"),
                kind.lanes_of_bytes(&joined[k..k + 16], false),
                &mut body,
            );
        }
    }
    // Bytes: a little-endian, then three filler bytes and b big-endian.
    let mut bytes = a_le.clone();
    bytes.extend([7, 8, 9]);
    bytes.extend(kind.bytes_of_lanes(&b, true));
    let size = kind.bytes();
    show(
        format!("{t}.load_le(&data, len, 0, _)"),
        a.clone(),
        &mut body,
    );
    show(
        format!("{t}.load_le(&data, len, 3, _)"),
        kind.lanes_of_bytes(&bytes[3..3 + size], false),
        &mut body,
    );
    show(
        format!("{t}.load_be(&data, len, {}, _)", size + 3),
        b.clone(),
        &mut body,
    );
    let source = format!(
        "use std.simd.{t};
         fn show(v: {t}) -> Unit ! {{io}} {{
             {}
         }}
         fn main() -> i64 ! {{io, alloc}} {{
             let a = {t}.new({});
             let b = {t}.new({});
             let c = {t}.new({});
             let mut data = {t}.push_le(Bytes.with_capacity({total}), a);
             data = Bytes.push(data, 7);
             data = Bytes.push(data, 8);
             data = Bytes.push(data, 9);
             data = {t}.push_be(data, b);
             let len = Bytes.len(&data);
             if len < {total} {{ drop(data); return 1; }}
             {body}
             drop(data);
             0
         }}",
        (0..n)
            .map(|i| format!("print_int({t}.lane(v, {i}, _));"))
            .collect::<Vec<_>>()
            .join(" "),
        list(&a),
        list(&b),
        list(&c),
        total = 2 * kind.bytes() + 3,
    );
    let want: String = expected
        .iter()
        .flatten()
        .map(|v| format!("{v}\n"))
        .collect();
    let got = run(&source);
    if got != want {
        let got_lines: Vec<&str> = got.lines().collect();
        let want_lines: Vec<&str> = want.lines().collect();
        let first = got_lines.iter().zip(&want_lines).position(|(g, w)| g != w);
        panic!(
            "{t} (seed {seed}): first difference at output line {first:?} (lane {:?} of operation {:?}); got {} lines, want {}",
            first.map(|line| line % n),
            first.map(|line| line / n),
            got_lines.len(),
            want_lines.len()
        );
    }
}

#[test]
fn unsigned_operations_match_the_lane_model() {
    for kind in KINDS
        .iter()
        .filter(|kind| !kind.signed && kind.width == 128)
    {
        for seed in [1, 2] {
            check_kind(*kind, seed);
        }
    }
}

#[test]
fn signed_operations_match_the_lane_model() {
    for kind in KINDS.iter().filter(|kind| kind.signed && kind.width == 128) {
        for seed in [3, 4] {
            check_kind(*kind, seed);
        }
    }
}

#[test]
fn shift_amounts_and_indices_are_proved() {
    let rejects = |source: &str, fragment: &str| match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(error.message.contains(fragment), "{error:?}"),
    };
    rejects(
        "use std.simd.u32x4;
         fn main() -> i64 ! {} { let v = u32x4.shl(u32x4.zero(), 32, _); Int.convert(u32x4.lane(v, 0, _)) }",
        "cannot prove",
    );
    rejects(
        "use std.simd.u8x16;
         fn main() -> i64 ! {} { let v = u8x16.align_right(u8x16.zero(), u8x16.zero(), 17, _); Int.convert(u8x16.lane(v, 0, _)) }",
        "cannot prove",
    );
    rejects(
        "use std.simd.u32x4;
         fn f(d: &Bytes) -> u32 ! {} { let n = Bytes.len(d); u32x4.lane(u32x4.load_le(d, n, 0, _), 0, _) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove",
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn the_native_backend_emits_vector_instructions() {
    // SIMD-NATIVE: the operations above become Cranelift vector
    // instructions, not calls to their Kush bodies.
    let program = check(
        "use std.simd.u8x16;
         use std.simd.u32x4;
         use std.simd.i16x8;
         fn main() -> i64 ! {} {
             let a = u32x4.new(1, 2, 3, 4);
             let b = u32x4.wrapping_add(a, u32x4.xor(a, u32x4.splat(9)));
             let c = u32x4.shuffle(u32x4.shl(b, 3, _), 3, 2, 1, 0, _);
             let d = u8x16.align_right(u8x16.from_bits(u32x4.to_bits(c)), u8x16.zero(), 4, _);
             let e = i16x8.shr(i16x8.from_bits(u8x16.to_bits(d)), 2, _);
             let f = u32x4.eq_lanes(u32x4.swap_bytes(c), u32x4.from_bits(i16x8.to_bits(e)));
             Int.convert(u32x4.lane(f, 0, _) & 1)
         }",
    )
    .unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let clif = kush::native::build_with_clif(&program, &scratch.path().join("vector")).unwrap();
    // Cranelift prints a value's type on the bitcast that makes it, and the
    // operations on vectors without a suffix.
    for instruction in [
        "bitcast.i32x4",
        "bitcast.i16x8",
        "bitcast.i8x16",
        "= iadd ",
        "= bxor ",
        "= ishl ",
        "= shuffle ",
        "= sshr ",
        "= icmp eq ",
    ] {
        assert!(clif.contains(instruction), "no {instruction:?} in:\n{clif}");
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn the_llvm_backend_emits_vector_operations() {
    // SIMD-LLVM: the translator turns the vector instructions into LLVM
    // vector IR (when `clang` is available, as for the other LLVM tests).
    if std::process::Command::new(std::env::var("KUSH_CLANG").unwrap_or_else(|_| "clang".into()))
        .arg("--version")
        .output()
        .is_err()
    {
        return;
    }
    let program = check(
        "use std.simd.u32x4;
         use std.simd.u8x16;
         fn main() -> i64 ! {} {
             let a = u32x4.new(1, 2, 3, 4);
             let b = u32x4.wrapping_add(a, u32x4.xor(a, u32x4.splat(9)));
             let c = u32x4.shuffle(u32x4.shl(b, 3, _), 3, 2, 1, 0, _);
             let d = u8x16.align_right(u8x16.from_bits(u32x4.to_bits(c)), u8x16.zero(), 4, _);
             let e = u32x4.eq_lanes(u32x4.from_bits(u8x16.to_bits(d)), c);
             Int.convert(u32x4.lane(e, 0, _) & 7)
         }",
    )
    .unwrap();
    let ir =
        kush::native::emit_llvm_ir(&program, kush::native::CodegenOptions::release_llvm()).unwrap();
    for operation in [
        "add <4 x i32>",
        "xor <4 x i32>",
        "shl <4 x i32>",
        "icmp eq <4 x i32>",
        "shufflevector <16 x i8>",
    ] {
        assert!(ir.contains(operation), "no {operation:?} in the LLVM IR");
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn host_features_turn_byte_shuffles_into_instructions() {
    // Without SSSE3 (the x86-64 baseline) Cranelift calls a software
    // pshufb; with `--target-cpu native` on an SSSE3 machine it emits the
    // instruction. Checked with objdump when it is installed.
    let ssse3 = std::fs::read_to_string("/proc/cpuinfo")
        .unwrap()
        .contains(" ssse3");
    let objdump = std::process::Command::new("objdump")
        .arg("--version")
        .output()
        .is_ok();
    // A Cranelift property: KUSH_BACKEND=llvm would build with LLVM instead.
    let cranelift = std::env::var("KUSH_BACKEND").is_err();
    if !ssse3 || !objdump || !cranelift {
        return;
    }
    let program = check(
        "use std.simd.u8x16;
         fn main() -> i64 ! {} {
             let a = u8x16.new(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
             let b = u8x16.shuffle(a, 15, 3, 7, 1, 0, 2, 9, 4, 5, 6, 8, 10, 11, 12, 13, 14, _);
             Int.convert(u8x16.lane(b, 0, _))
         }",
    )
    .unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let count = |native_cpu: bool| -> usize {
        let binary = scratch
            .path()
            .join(if native_cpu { "host" } else { "baseline" });
        let mut options = kush::native::CodegenOptions::release();
        options.native_cpu = native_cpu;
        kush::native::build_with_codegen(
            &program,
            &binary,
            false,
            &kush::native::LinkSpec::default(),
            options,
        )
        .unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(output.status.code(), Some(15));
        let disassembly = std::process::Command::new("objdump")
            .arg("-d")
            .arg(&binary)
            .output()
            .unwrap();
        String::from_utf8_lossy(&disassembly.stdout)
            .lines()
            // The VEX form (vpshufb) when the host also has AVX.
            .filter(|line| line.contains("\tpshufb ") || line.contains("\tvpshufb "))
            .count()
    };
    assert!(
        count(true) > count(false),
        "no pshufb instruction with host features"
    );
}

#[test]
fn wide_operations_match_the_lane_model() {
    for kind in KINDS.iter().filter(|kind| kind.width == 256) {
        check_kind(*kind, 5);
    }
}

#[test]
fn wide_vectors_split_into_halves() {
    let output = run("use std.simd.u32x8;
         use std.simd.u32x4;
         fn main() -> i64 ! {io} {
             let v = u32x8.new(1, 2, 3, 4, 5, 6, 7, 8);
             print_int(u32x4.lane(u32x8.low(v), 3, _));
             print_int(u32x4.lane(u32x8.high(v), 0, _));
             let w = u32x8.from_halves(u32x8.high(v), u32x8.low(v));
             print_int(u32x8.lane(w, 0, _));
             print_int(u32x8.lane(w, 7, _));
             0
         }");
    assert_eq!(output, "4\n5\n5\n4\n");
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn wide_lane_wise_operations_become_two_vector_instructions() {
    let program = check(
        "use std.simd.u32x8;
         fn main() -> i64 ! {} {
             let a = u32x8.splat(3);
             let b = u32x8.wrapping_add(a, u32x8.new(1, 2, 3, 4, 5, 6, 7, 8));
             Int.convert(u32x8.lane(b, 7, _) & 15)
         }",
    )
    .unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let clif = kush::native::build_with_clif(&program, &scratch.path().join("wide")).unwrap();
    assert!(
        clif.matches("= iadd v").filter(|_| true).count() >= 2,
        "{clif}"
    );
    assert!(clif.contains("bitcast.i32x4"), "{clif}");
}
