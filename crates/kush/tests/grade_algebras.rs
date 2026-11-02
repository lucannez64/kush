//! User-defined grade algebras.
//!
//! A `grade algebra` declares a finite carrier and total `add`/`mul` tables.
//! The grade pass validates closure, identities, commutativity, associativity,
//! distributivity, and zero annihilation by exhaustive enumeration before any
//! annotation can use the algebra. Elements are written `Algebra.Element`.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let (status, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, stats)
}

fn agrees(source: &str, expected_status: i64) {
    let (status, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("grade-algebra-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// A saturated three-level usage algebra: `None < Once < Twice`.
const SATURATED: &str = r#"
algebra Usage {
    elements { None, Once, Twice }
    zero = None;
    one = Once;
    add {
        None + None = None, None + Once = Once, None + Twice = Twice,
        Once + None = Once, Once + Once = Twice, Once + Twice = Twice,
        Twice + None = Twice, Twice + Once = Twice, Twice + Twice = Twice,
    }
    mul {
        None * None = None, None * Once = None, None * Twice = None,
        Once * None = None, Once * Once = Once, Once * Twice = Twice,
        Twice * None = None, Twice * Once = Twice, Twice * Twice = Twice,
    }
}
"#;

#[test]
fn a_validated_algebra_checks_exact_usage_in_both_backends() {
    agrees(
        &format!(
            "{SATURATED}
            fn main() -> i64 ! {{panic}} {{
                let x: i64 @[Usage.Twice] = 21;
                x + x
            }}"
        ),
        42,
    );
}

#[test]
fn an_algebra_element_can_be_a_parameter_or_result_contract() {
    agrees(
        &format!(
            "{SATURATED}
            fn twice(x: i64 @[Usage.Twice]) -> i64 ! {{panic}} {{ x + x }}
            fn make() -> i64 @[Usage.Once] ! {{}} {{ 41 }}
            fn main() -> i64 ! {{panic}} {{ twice(1) + make() }}"
        ),
        43,
    );
}

#[test]
fn a_saturated_algebra_counts_two_or_more_uses_as_twice() {
    agrees(
        &format!(
            "{SATURATED}
            fn main() -> i64 ! {{panic}} {{
                let x: i64 @[Usage.Twice] = 10;
                x + x + x
            }}"
        ),
        30,
    );
}

#[test]
fn wrong_use_counts_are_rejected_in_the_algebra() {
    rejects(
        &format!(
            "{SATURATED}
            fn main() -> i64 ! {{panic}} {{ let x: i64 @[Usage.Once] = 1; x + x }}"
        ),
        "not used consistently",
    );
}

#[test]
fn a_bare_algebra_name_is_not_a_grade() {
    rejects(
        &format!(
            "{SATURATED}\nfn f(x: i64 @[Usage]) -> i64 ! {{}} {{ x }} fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "requires an element",
    );
    rejects(
        &format!(
            "{SATURATED}\nfn f(x: i64 @[Usage.Missing]) -> i64 ! {{}} {{ x }} fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "has no element",
    );
}

#[test]
fn missing_or_repeated_table_rows_are_rejected() {
    rejects(
        r#"algebra Bad {
            elements { A, B }
            zero = A; one = B;
            add { A + A = A, A + B = B, B + A = B }
            mul { A * A = A, A * B = A, B * A = A, B * B = B }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "missing the pair",
    );
    rejects(
        r#"algebra Bad {
            elements { A, B }
            zero = A; one = B;
            add { A + A = A, A + A = B, A + B = B, B + A = B, B + B = B }
            mul { A * A = A, A * B = A, B * A = A, B * B = B }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "repeats the pair",
    );
}

#[test]
fn identity_and_law_violations_are_rejected() {
    // `B` is not an additive identity, so zero is wrong.
    rejects(
        r#"algebra Bad {
            elements { A, B }
            zero = B; one = B;
            add { A + A = A, A + B = B, B + A = B, B + B = B }
            mul { A * A = A, A * B = A, B * A = A, B * B = B }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "not an additive identity",
    );
    // A non-associative addition table.
    rejects(
        r#"algebra Bad {
            elements { Z, A, B, C }
            zero = Z; one = A;
            add {
                Z + Z = Z, Z + A = A, Z + B = B, Z + C = C,
                A + Z = A, A + A = B, A + B = C, A + C = A,
                B + Z = B, B + A = C, B + B = B, B + C = C,
                C + Z = C, C + A = A, C + B = C, C + C = C,
            }
            mul {
                Z * Z = Z, Z * A = Z, Z * B = Z, Z * C = Z,
                A * Z = Z, A * A = A, A * B = B, A * C = C,
                B * Z = Z, B * A = B, B * B = B, B * C = C,
                C * Z = Z, C * A = C, C * B = C, C * C = C,
            }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "semiring laws",
    );
}

#[test]
fn malformed_declarations_are_rejected() {
    rejects(
        r#"algebra Bad {
            elements { A, A }
            zero = A; one = A;
            add { A + A = A }
            mul { A * A = A }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "duplicate element",
    );
    rejects(
        r#"algebra Bad {
            elements { A }
            zero = A; one = Missing;
            add { A + A = A }
            mul { A * A = A }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "unknown element",
    );
}
