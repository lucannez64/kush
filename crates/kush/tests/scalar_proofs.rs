//! PROVE-SCALARS: `Bool`, unsigned and fixed-width integer terms in the
//! erased `{ ... }` fragment. A `Bool` is the integer 0 or 1; a fixed-width
//! integer carries its range as an implicit fact; unsigned constants are read
//! by their type (the `u64` word is a raw bit pattern).
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("scalar-proofs");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
    }
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

#[test]
fn bool_terms_follow_branches_and_atoms() {
    agrees(
        "fn need_true(b: Bool, erased p: { b }) -> i64 ! {} { 1 }
         fn need_false(b: Bool, erased p: { !b }) -> i64 ! {} { 2 }
         fn split(b: Bool) -> i64 ! {} { if b { need_true(b, _) } else { need_false(b, _) } }
         fn same(a: Bool, b: Bool, erased p: { a == b }) -> i64 ! {} { 3 }
         fn equal(a: Bool, b: Bool) -> i64 ! {} { if a == b { same(a, b, _) } else { 0 } }
         fn mixed(a: Bool, b: Bool) -> i64 ! {panic} { if a && !b { need_false(b, _) + need_true(a, _) } else { 0 } }
         fn literal() -> i64 ! {panic} { need_true(true, _) + need_false(false, _) }
         fn forward(b: Bool, erased p: { b && b == true }) -> i64 ! {} { need_true(b, _) }
         fn main() -> i64 ! {panic} {
             split(true) + split(false) + equal(true, true) + mixed(true, false) + literal() + forward(true, _)
         }",
        1 + 2 + 3 + 3 + 3 + 1,
    );
    rejects(
        "fn need(b: Bool, erased p: { b }) -> i64 ! {} { 1 }
         fn main() -> i64 ! {} { need(false, _) }",
        "cannot prove 'b'",
    );
    rejects(
        "fn need(b: Bool, erased p: { b }) -> i64 ! {} { 1 }
         fn f(b: Bool) -> i64 ! {} { if !b { need(b, _) } else { 0 } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'b'",
    );
    // A bare name must be a Bool, at the declaration and at the call.
    rejects(
        "fn bad(x: i64, erased p: { x }) -> i64 ! {} { x }
         fn main() -> i64 ! {} { 0 }",
        "a bare name in a proposition must be a Bool parameter",
    );
}

#[test]
fn fixed_width_integers_carry_their_ranges() {
    agrees(
        "fn small(x: u8, erased p: { 0 <= x && x <= 255 }) -> u8 ! {} { x }
         fn forward(x: u8) -> i64 ! {} { let y = small(x, _); 1 }
         fn signed(x: i8, erased p: { 0 - 128 <= x && x <= 127 }) -> i64 ! {} { 2 }
         fn forward_signed(x: i8) -> i64 ! {} { signed(x, _) }
         fn newer(c: u64, p: u64, erased q: { c >= p + 1 }) -> i64 ! {} { 4 }
         fn compare(c: u64, p: u64) -> i64 ! {} { if c > p { newer(c, p, _) } else { 0 } }
         fn positive(x: u64, erased p: { x >= 1 }) -> i64 ! {} { 8 }
         fn main() -> i64 ! {panic} {
             let a: u8 = 200;
             let b: i8 = -5;
             let c: u64 = 18446744073709551615;
             let d: u64 = 18446744073709551614;
             forward(a) + forward_signed(b) + compare(c, d) + positive(18446744073709551615, _)
         }",
        1 + 2 + 4 + 8,
    );
    // u64::MAX is read as 2^64 - 1, never as the word's signed value -1.
    rejects(
        "fn at_most_zero(x: u64, erased p: { x <= 0 }) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { at_most_zero(18446744073709551615, _) }",
        "cannot prove 'x <= 0'",
    );
    // A range alone does not prove more than it says.
    rejects(
        "fn positive(x: u64, erased p: { x >= 1 }) -> i64 ! {} { 1 }
         fn f(x: u64) -> i64 ! {} { positive(x, _) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'x >= 1'",
    );
    rejects(
        "fn below(x: u8, erased p: { x <= 254 }) -> i64 ! {} { 1 }
         fn f(x: u8) -> i64 ! {} { below(x, _) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'x <= 254'",
    );
}
