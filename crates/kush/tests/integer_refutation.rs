//! Integer refutation beyond the rational relaxation.
//!
//! These programs are rationally feasible but have no integer solution, or
//! have a goal that the rational relaxation cannot establish. Chvátal–Gomory
//! rounding cuts and integer case splits close the gap; every emitted
//! certificate is re-checked independently by `Certificate::verify`.
use kush::executable::check;

fn value(source: &str) -> i64 {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    result
}

fn checked(source: &str) -> kush::executable::Executable {
    check(source).unwrap()
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
        let binary = scratch.path().join("integer-refutation-test");
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
fn a_tight_scaled_goal_needs_rounding() {
    // The rational relaxation allows x = 1/2, so 2*x <= 1 does not imply
    // 2*x <= 0 over the rationals. For an integer x it does, via the cut
    // 2*x <= 1 -> x <= 0.
    let source = r#"
        fn take(x: i64, erased p: { 2 * x <= 0 }) -> i64 ! {} { x }
        fn forward(x: i64, erased p: { 2 * x <= 1 }) -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(0, _) }
    "#;
    assert_eq!(value(source), 0);
    native_agrees(source, 0);
}

#[test]
fn a_parity_equation_with_no_integer_solution_refutes_the_branch() {
    // 2*n == 1 is satisfiable at n = 1/2 but never by an integer. The branch
    // body is therefore unreachable and every goal follows from its facts.
    let source = r#"
        fn take(n: i64, erased p: { n <= 0 }) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n = 0;
            if 2 * n == 1 { take(n, _) } else { 42 }
        }
    "#;
    assert_eq!(value(source), 42);
    native_agrees(source, 42);
}

#[test]
fn a_double_sided_tight_bound_is_integer_infeasible() {
    // 1 <= 2*n <= 1 is only satisfiable at n = 1/2.
    let source = r#"
        fn take(n: i64, erased p: { n <= 0 }) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n = 0;
            if 1 <= 2 * n && 2 * n <= 1 { take(n, _) } else { 7 }
        }
    "#;
    assert_eq!(value(source), 7);
    native_agrees(source, 7);
}

#[test]
fn a_two_variable_parity_equation_is_refuted() {
    // 2*n == 2*m + 1 has no integer solution for any n, m. Rounding the two
    // inequalities separately gives n - m <= 0 and n - m >= 1.
    let source = r#"
        fn take(n: i64, m: i64, erased p: { n <= m }) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n = 0;
            let m = 0;
            if 2 * n == 2 * m + 1 { take(n, m, _) } else { 9 }
        }
    "#;
    assert_eq!(value(source), 9);
    native_agrees(source, 9);
}

#[test]
fn a_pairwise_combination_cut_closes_the_gap() {
    // Neither hypothesis has a useful gcd on its own, but their sum is
    // 2*x <= 1, whose rounding cut is x <= 0 (and hence 2*x <= 0).
    let source = r#"
        fn take(x: i64, erased p: { 2 * x <= 0 }) -> i64 ! {} { x }
        fn forward(
            x: i64,
            y: i64,
            erased upper: { x + y <= 1 },
            erased difference: { x - y <= 0 },
        ) -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(0, 0, _, _) }
    "#;
    assert_eq!(value(source), 0);
    native_agrees(source, 0);
}

#[test]
fn emitted_integer_certificates_pass_independent_checking() {
    let source = r#"
        fn take(x: i64, erased p: { 2 * x <= 0 }) -> i64 ! {} { x }
        fn forward(x: i64, erased p: { 2 * x <= 1 }) -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(0, _) }
    "#;
    let program = checked(source);
    assert!(!program.certificates().is_empty());
    assert!(
        program.certificates().iter().all(kush::Certificate::verify),
        "every emitted certificate must pass the independent checker"
    );
}

#[test]
fn genuinely_feasible_systems_stay_rejected() {
    // x = 1, y = 0 satisfies x + y <= 1 and violates x <= 0, so no integer
    // rounding or branching may prove this obligation.
    rejects(
        r#"
        fn take(x: i64, erased p: { x <= 0 }) -> i64 ! {} { x }
        fn forward(x: i64, y: i64, erased p: { x + y <= 1 })
            -> i64 ! {} { take(x, _) }
        fn main() -> i64 ! {panic} { forward(0, 0, _) }
        "#,
        "cannot prove",
    );
}

#[test]
fn exceeding_the_integer_term_budget_leaves_the_obligation_unproved() {
    // The obligation is genuinely integer-valid, but the fallback refuses
    // systems wider than its documented term budget. Conservative rejection is
    // the required behaviour; no unverified proof is emitted.
    let mut parameters = String::from("x1: i64");
    let mut facts = String::from("2 * x1 <= 1");
    for index in 2..=24 {
        parameters.push_str(&format!(", x{index}: i64"));
        facts.push_str(&format!(" && x{index} == 0"));
    }
    let source = format!(
        r#"
        fn take(x: i64, erased p: {{ 2 * x <= 0 }}) -> i64 ! {{}} {{ x }}
        fn forward({parameters}, erased p: {{ {facts} }}) -> i64 ! {{}} {{ take(x1, _) }}
        fn main() -> i64 ! {{panic}} {{ 0 }}
        "#
    );
    rejects(&source, "cannot prove");
}

#[test]
fn extreme_coefficients_fail_closed_instead_of_panicking() {
    let source = r#"
fn take(x: i64, erased p: { x >= 0 }) -> i64 ! {} { x }
fn forward(x: i64, erased p: {
    (-170141183460469231731687303715884105727 - 1) * x <= 0
}) -> i64 ! {} { take(x, _) }
fn main() -> i64 ! {panic} { 0 }
"#;
    assert!(check(source).is_err());
}

#[test]
fn an_uncheckable_contradiction_does_not_hide_a_checkable_one() {
    // The facts about `x` are contradictory, but combining them needs
    // multipliers beyond i128, so that certificate cannot be checked. The
    // facts about `y` are plainly contradictory. The search must offer the
    // second, whichever group of facts it looks at first.
    let source = r#"
fn take(z: i64, erased p: { z <= 0 }) -> i64 ! {} { z }
fn forward(y: i64, x: i64, z: i64,
           erased a: { 4611686018427387904 * (4611686018427387904 * x) >= 1 },
           erased b: { 16 * x <= 0 - 1 },
           erased c: { y <= 0 },
           erased d: { y >= 1 }) -> i64 ! {} { take(z, _) }
fn main() -> i64 ! {panic} { 0 }
"#;
    assert!(check(source).is_ok(), "{:?}", check(source).err());
}
