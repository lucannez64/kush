//! Arithmetic proof search over the erased `{ ... }` proposition fragment.
//!
//! The fragment admits linear integer expressions (`x`, `x + c`, `c * x`,
//! `len(xs) + c`) and discharges obligations by Fourier–Motzkin elimination
//! over exact rationals. The certificate is a non-negative combination of the
//! hypotheses and the integer negation of the goal, checked independently.
use kush::executable::check;

fn value(source: &str) -> i64 {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    result
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

fn native_agrees(source: &str, expected: i64) {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("arithmetic-proofs-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    let _ = (source, expected);
}

#[test]
fn a_coefficient_bound_discharges_a_scaled_goal() {
    // From 2*x <= 4 derive x <= 2. The old difference-only solver could not
    // scale a term, so this needed an explicit division by hand.
    let source = r#"
        fn take(x: i64, erased p: { x <= 2 }) -> i64 ! {} { x }
        fn forward(x: i64, erased p: { 2 * x <= 4 }) -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(1, _) }
    "#;
    assert_eq!(value(source), 1);
    native_agrees(source, 1);
}

#[test]
fn multi_variable_elimination_uses_every_hypothesis() {
    // From x + y <= 4 and 0 <= x derive y <= 4. Neither hypothesis alone is
    // enough, and eliminating x combines positive and negative bounds.
    let source = r#"
        fn take(y: i64, erased p: { y <= 4 }) -> i64 ! {} { y }
        fn forward(
            x: i64,
            y: i64,
            erased both: { x + y <= 4 },
            erased lower: { 0 <= x },
        ) -> i64 ! {} { take(y, _) }
        fn main() -> i64 ! {panic} { forward(1, 3, _, _) }
    "#;
    assert_eq!(value(source), 3);
    native_agrees(source, 3);
}

#[test]
fn branch_conditions_contribute_scaled_linear_facts() {
    let source = r#"
        fn take(x: i64, erased p: { 2 * x <= 4 }) -> i64 ! {} { x }
        fn main() -> i64 ! {panic} {
            let n = 1;
            if 2 * n <= 4 { take(n, _) } else { 0 }
        }
    "#;
    assert_eq!(value(source), 1);
    native_agrees(source, 1);
}

#[test]
fn integer_strictness_is_respected_by_the_rational_relaxation() {
    // From 2*x <= 1 the integer goal x <= 0 follows. The refutation uses the
    // integer negation x >= 1 and is sound even though the rational relaxation
    // of the hypothesis alone allows x = 1/2.
    let source = r#"
        fn take(x: i64, erased p: { x <= 0 }) -> i64 ! {} { x }
        fn forward(x: i64, erased p: { 2 * x <= 1 }) -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(0, _) }
    "#;
    assert_eq!(value(source), 0);
    native_agrees(source, 0);
}

#[test]
fn false_or_nonlinear_obligations_stay_rejected() {
    // A genuinely false obligation is not proved by search.
    rejects(
        r#"
        fn take(y: i64, erased p: { y <= 4 }) -> i64 ! {} { y }
        fn forward(x: i64, y: i64, erased both: { x + y <= 4 })
            -> i64 ! {} { take(y, _) }
        fn main() -> i64 ! {panic} { forward(1, 3, _) }
        "#,
        "cannot prove",
    );
    // Nonlinear arithmetic is not reinterpreted as a linear fact.
    rejects(
        r#"
        fn bad(x: i64, y: i64, erased p: { x * y <= 4 }) -> i64 ! {} { x + y }
        fn main() -> i64 ! {panic} { bad(1, 2, _) }
        "#,
        "linear integer comparisons",
    );
    // A fact about a mutable local at an older version does not prove the new
    // value's proposition.
    rejects(
        r#"
        fn take(x: i64, erased p: { 2 * x <= 4 }) -> i64 ! {} { x }
        fn main() -> i64 ! {panic} {
            let mut n = 1;
            if 2 * n <= 4 {
                n = 3;
                take(n, _)
            } else {
                0
            }
        }
        "#,
        "cannot prove",
    );
}
