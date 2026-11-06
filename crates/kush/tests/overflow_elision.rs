//! OVERFLOW-ELIDE: `+`, `-` and `*` (by a constant) whose result the facts
//! keep within the type's range need no runtime overflow check, so they need
//! no `panic` effect. The proof is recorded as a checked certificate; the
//! operation becomes a plain machine add/sub/mul in both backends.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("overflow-elision");
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
fn proved_arithmetic_needs_no_panic_effect() {
    agrees(
        "fn next(c: i64, erased q: { c <= 9223372036854775806 }) -> i64 ! {} { c + 1 }
         fn bump(x: u8) -> u8 ! {} { if x < 255 { x + 1 } else { x } }
         fn literal() -> i64 ! {} { 0 - 1 }
         fn mix(a: i64, b: i64) -> i64 ! {} {
             if a >= 0 && a <= 1000 && b >= 0 && b <= 1000 { a * 3 + b - 7 } else { 0 }
         }
         fn at_most(x: i64, erased q: { x <= 102 }) -> i64 ! {} { x }
         fn chain(c: i64, erased q: { 0 <= c && c <= 100 }) -> i64 ! {} {
             let d = c + 1;
             let e = d + 1;
             at_most(e, _)
         }
         fn top(x: u64, erased q: { x <= 18446744073709551614 }) -> u64 ! {} { x + 1 }
         fn down(x: u64) -> u64 ! {} { if x > 0 { x - 1 } else { 0 } }
         fn main() -> i64 ! {panic} {
             let big: u64 = 18446744073709551614;
             let wrapped: u64 = top(big, _);
             let back: u64 = down(wrapped);
             next(41, _) + literal() + mix(10, 20) + chain(5, _) + Int.convert(bump(254))
                 + if back == big { 1 } else { 0 }
         }",
        42 - 1 + 43 + 7 + 255 + 1,
    );
}

#[test]
fn unproved_arithmetic_still_needs_the_check() {
    for source in [
        "fn f(c: i64) -> i64 ! {} { c + 1 }",
        "fn f(x: u8) -> u8 ! {} { if x <= 255 { x + 1 } else { x } }",
        "fn f(a: i64, b: i64) -> i64 ! {} { if a >= 0 && b >= 0 && a <= 9 && b <= 9 { a * b } else { 0 } }",
        "fn f(x: u64) -> u64 ! {} { x - 1 }",
        "fn f(c: i64, erased q: { c <= 9223372036854775807 }) -> i64 ! {} { c + 1 }",
        "fn f() -> i64 ! {} { 9223372036854775807 + 1 }",
    ] {
        rejects(
            &format!("{source}\nfn main() -> i64 ! {{}} {{ 0 }}"),
            "operation requires effects {panic}",
        );
    }
    // A checked operation still traps at run time.
    let program = check(
        "fn f(c: i64) -> i64 ! {panic} { c + 1 }
         fn main() -> i64 ! {panic} { f(9223372036854775807) }",
    )
    .unwrap();
    assert!(program.evaluate(&mut Vec::new()).is_err());
}
