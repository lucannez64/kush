//! SIMD-TYPES: the 128-bit vector types of `std.simd`, associated functions
//! (`Type.name(..)`) and `Self { .. }` record literals. Both backends must
//! agree and the evaluator must free every allocation.
use kush::executable::check;

fn agrees(source: &str) -> String {
    let output = reference(source);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(native(source), output);
    output
}

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("simd");
    kush::native::build(&program, &binary).unwrap();
    let native = std::process::Command::new(&binary).output().unwrap();
    assert_eq!(
        native.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&native.stderr)
    );
    String::from_utf8(native.stdout).unwrap()
}

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

fn lines(values: &[i128]) -> String {
    values.iter().map(|v| format!("{v}\n")).collect()
}

#[test]
fn lanes_round_trip_in_every_unsigned_type() {
    let output = agrees(
        "use std.simd.u8x16;
         use std.simd.u16x8;
         use std.simd.u32x4;
         use std.simd.u64x2;
         fn main() -> i64 ! {io, panic} {
             let a = u32x4.new(1, 2, 3, 4294967295);
             print_int(u32x4.lane(a, 0, _));
             print_int(u32x4.lane(a, 1, _));
             print_int(u32x4.lane(a, 2, _));
             print_int(u32x4.lane(a, 3, _));
             let b = u8x16.new(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 255);
             print_int(u8x16.lane(b, 0, _));
             print_int(u8x16.lane(b, 7, _));
             print_int(u8x16.lane(b, 8, _));
             print_int(u8x16.lane(b, 15, _));
             let c = u16x8.new(1, 2, 3, 4, 5, 6, 7, 65535);
             print_int(u16x8.lane(c, 3, _));
             print_int(u16x8.lane(c, 4, _));
             print_int(u16x8.lane(c, 7, _));
             let d = u64x2.new(18446744073709551615, 5);
             print_int(u64x2.lane(d, 0, _));
             print_int(u64x2.lane(d, 1, _));
             0
         }",
    );
    assert_eq!(
        output,
        lines(&[
            1,
            2,
            3,
            4294967295,
            0,
            7,
            8,
            255,
            4,
            5,
            65535,
            18446744073709551615,
            5
        ])
    );
}

#[test]
fn signed_lanes_keep_their_sign() {
    let output = agrees(
        "use std.simd.i8x16;
         use std.simd.i16x8;
         use std.simd.i32x4;
         use std.simd.i64x2;
         fn main() -> i64 ! {io, panic} {
             let a = i8x16.new(-1, -128, 127, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, -2);
             print_int(i8x16.lane(a, 0, _));
             print_int(i8x16.lane(a, 1, _));
             print_int(i8x16.lane(a, 2, _));
             print_int(i8x16.lane(a, 15, _));
             let b = i16x8.splat(-300);
             print_int(i16x8.lane(b, 5, _));
             let c = i32x4.new(-2147483648, 2147483647, -1, 0);
             print_int(i32x4.lane(c, 0, _));
             print_int(i32x4.lane(c, 1, _));
             print_int(i32x4.lane(c, 2, _));
             let d = i64x2.new(-9223372036854775808, -7);
             print_int(i64x2.lane(d, 0, _));
             print_int(i64x2.lane(d, 1, _));
             0
         }",
    );
    assert_eq!(
        output,
        lines(&[
            -1,
            -128,
            127,
            -2,
            -300,
            -2147483648,
            2147483647,
            -1,
            -9223372036854775808,
            -7
        ])
    );
}

#[test]
fn splat_zero_with_lane_and_equality() {
    let output = agrees(
        "use std.simd.u32x4;
         use std.simd.u8x16;
         fn flag(b: Bool) -> i64 ! {} { if b { 1 } else { 0 } }
         fn main() -> i64 ! {io, panic} {
             let s = u32x4.splat(7);
             print_int(u32x4.lane(s, 3, _));
             let z = u32x4.zero();
             print_int(u32x4.lane(z, 2, _));
             let w = u32x4.with_lane(s, 2, 99, _);
             print_int(u32x4.lane(w, 1, _));
             print_int(u32x4.lane(w, 2, _));
             print_int(u32x4.lane(w, 3, _));
             print_int(flag(u32x4.eq(s, u32x4.new(7, 7, 7, 7))));
             print_int(flag(u32x4.eq(s, w)));
             let b = u8x16.with_lane(u8x16.splat(1), 9, 200, _);
             print_int(u8x16.lane(b, 8, _));
             print_int(u8x16.lane(b, 9, _));
             print_int(u8x16.lane(b, 10, _));
             0
         }",
    );
    assert_eq!(output, lines(&[7, 0, 7, 99, 7, 1, 0, 1, 200, 1]));
}

#[test]
fn reinterpretation_keeps_x86_lane_order() {
    // Lane 0 is the low bits: u32 0x04030201 is bytes 1, 2, 3, 4.
    let output = agrees(
        "use std.simd.u32x4;
         use std.simd.u8x16;
         use std.simd.u64x2;
         fn main() -> i64 ! {io, panic} {
             let v = u32x4.new(67305985, 0, 0, 4278190080);
             let b = u8x16.from_bits(u32x4.to_bits(v));
             print_int(u8x16.lane(b, 0, _));
             print_int(u8x16.lane(b, 1, _));
             print_int(u8x16.lane(b, 3, _));
             print_int(u8x16.lane(b, 15, _));
             let q = u64x2.from_bits(u32x4.to_bits(v));
             print_int(u64x2.lane(q, 0, _));
             0
         }",
    );
    assert_eq!(output, lines(&[1, 2, 4, 255, 67305985]));
}

#[test]
fn lane_indices_are_proved_and_functions_cannot_panic() {
    // The operations have empty effect rows: a caller without `panic` uses them.
    check(
        "use std.simd.u32x4;
         fn pick(v: u32x4, i: i64) -> u32 ! {} {
             if i >= 0 && i < 4 { u32x4.lane(v, i, _) } else { 0 }
         }
         fn main() -> i64 ! {} { Int.convert(pick(u32x4.splat(3), 2)) }",
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    rejects(
        "use std.simd.u32x4;
         fn main() -> i64 ! {} { Int.convert(u32x4.lane(u32x4.zero(), 4, _)) }",
        "cannot prove",
    );
    rejects(
        "use std.simd.u32x4;
         fn f(v: u32x4, i: i64) -> u32 ! {} { u32x4.lane(v, i, _) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove",
    );
}

#[test]
fn associated_functions_are_called_through_the_type_only() {
    let output = agrees(
        "struct Counter { n: i64 }
         impl Counter {
             pub fn start(n: i64) -> Counter ! {} { Self { n: n } }
             pub fn value(self: Self) -> i64 ! {} { self.n }
         }
         fn main() -> i64 ! {io, panic} {
             let c = Counter.start(41);
             print_int(c.value() + 1);
             0
         }",
    );
    assert_eq!(output, "42\n");
    rejects(
        "struct Counter { n: i64 }
         impl Counter { pub fn start(n: i64) -> Counter ! {} { Self { n: n } } }
         fn main() -> i64 ! {} { Counter.stop(1).n }",
        "unknown qualified name 'Counter.stop'",
    );
    rejects(
        "struct Counter { n: i64 }
         impl Counter { pub fn start(n: i64) -> Counter ! {} { Self { n: n } } }
         fn main() -> i64 ! {} { let c = Counter.start(1); c.start(2).n }",
        "start",
    );
    rejects(
        "struct Counter { n: i64 }
         fn main() -> i64 ! {} { let c = Self { n: 1 }; c.n }",
        "only inside an impl",
    );
    rejects(
        "struct Counter { n: i64 }
         impl Counter {
             pub fn start(n: i64) -> Counter ! {} { Self { n: n } }
             pub fn start(self: Self) -> i64 ! {} { self.n }
         }
         fn main() -> i64 ! {} { 0 }",
        "duplicate",
    );
}
