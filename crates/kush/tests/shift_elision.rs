//! SHIFT-ELIDE: `<<` and `>>` whose amount the facts keep in `0..bits` need
//! no runtime check, so they need no `panic` effect. The proof is a checked
//! certificate; the shift becomes a plain machine shift in both backends,
//! with the language's semantics unchanged (a left shift drops high bits, a
//! right shift of a signed value is arithmetic).
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("shift-elision");
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
fn constant_and_proved_amounts_need_no_panic_effect() {
    agrees(
        "fn rotr(x: u32, n: u64, erased q: { 1 <= n && n <= 31 }) -> u32 ! {} {
             (x >> n) | (x << (32 - n))
         }
         fn spread(b: u32) -> u32 ! {} { (b << 24) | (b << 16) | (b << 8) | b }
         fn top_bit(x: i8) -> i8 ! {} { x >> 7 }
         fn drop_high(x: u8) -> u8 ! {} { x << 1 }
         fn bit(i: i64) -> i64 ! {} { if i >= 0 && i < 63 { 1 << i } else { 0 } }
         fn main() -> i64 ! {panic} {
             let r: u32 = rotr(1, 1, _);                 // 0x80000000
             let a: i64 = if r == 2147483648 { 1 } else { 0 };
             let s: u32 = spread(171);                   // 0xabababab
             let b: i64 = if s == 2880154539 { 2 } else { 0 };
             let c: i64 = if top_bit(-100) == -1 && top_bit(100) == 0 { 4 } else { 0 };
             let d: i64 = if drop_high(200) == 144 { 8 } else { 0 };
             a + b + c + d + bit(5)
         }",
        1 + 2 + 4 + 8 + 32,
    );
}

#[test]
fn unproved_amounts_still_need_the_check() {
    rejects("fn f(x: u32, n: u32) -> u32 ! {} { x << n }", "panic");
    rejects("fn f(x: u32) -> u32 ! {} { x >> 32 }", "panic");
    rejects(
        "fn f(x: i64, n: i64) -> i64 ! {} { if n < 64 { x << n } else { 0 } }",
        "panic",
    );
    // An out-of-range amount still panics at run time in both backends.
    let source = "fn f(x: u32, n: u32) -> u32 ! {panic} { x << n }
                  fn main() -> i64 ! {panic} { let v: u32 = f(1, 40); Int.convert(v) }";
    let program = check(source).unwrap();
    assert!(program.evaluate_with_stats(&mut Vec::new()).is_err());
}

#[test]
fn loop_shifts_are_proved_from_the_loop_condition() {
    agrees(
        "fn mask(n: i64) -> i64 ! {panic} {
             let mut m = 0;
             let mut i = 0;
             while i < n && i < 63 invariant { 0 <= i } {
                 m = m | (1 << i);
                 i = i + 1;
             }
             m
         }
         fn main() -> i64 ! {panic} { mask(6) }",
        63,
    );
}
