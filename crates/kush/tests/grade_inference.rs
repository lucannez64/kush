//! General usage-grade inference for direct calls and function values.
//!
//! Inference is deliberately restricted to a decidable fragment: a usage-grade
//! binder occurs exactly once in a declared parameter/result grade expression,
//! all other leaves are concrete, and the expected grade comes from an
//! explicitly graded argument or an expected arrow. Such an expression is
//! affine in the binder, so `e(g) = e(0) + (e(1) - e(0)) * g`; a unique natural
//! solution exists when the slope is nonzero and divides the offset. The
//! checker never guesses an unknown grade as one.
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
        let binary = scratch.path().join("grade-inference-test");
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

#[test]
fn a_direct_call_infers_a_bare_parameter_grade_from_an_annotated_argument() {
    agrees(
        r#"fn twice<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x }
        fn main() -> i64 ! {panic} { let x: i64 @[2] = 21; twice(x) }"#,
        42,
    );
}

#[test]
fn a_direct_call_solves_a_composite_parameter_grade() {
    agrees(
        r#"fn twice<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x }
        fn main() -> i64 ! {panic} { let x: i64 @[2] = 21; twice(x) }"#,
        42,
    );
}

#[test]
fn conflicting_argument_grades_are_rejected() {
    rejects(
        r#"fn pair<G: Grade>(a: i64 @[G], b: i64 @[G]) -> i64 ! {panic} { a + b }
        fn main() -> i64 ! {panic} {
            let a: i64 @[2] = 1;
            let b: i64 @[3] = 2;
            pair(a, b)
        }"#,
        "conflicting inferred grades",
    );
}

#[test]
fn ungraded_arguments_do_not_invent_a_grade() {
    rejects(
        r#"fn twice<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x }
        fn main() -> i64 ! {panic} { let x = 21; twice(x) }"#,
        "cannot infer usage grade parameter",
    );
}

#[test]
fn a_function_value_infers_parameter_grades_from_the_expected_arrow() {
    agrees(
        r#"fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x }
        fn apply(f: fn(i64 @[4]) -> i64 ! {panic}) -> i64 ! {panic} { f(10) }
        fn main() -> i64 ! {panic} { apply(four) }"#,
        40,
    );
}

#[test]
fn a_composite_copyable_result_grade_is_inferred() {
    agrees(
        r#"fn make<G: Grade>() -> i64 @[G + 1] ! {} { 41 }
        fn apply(f: fn() -> i64 @[1] ! {}) -> i64 ! {panic} { f() + 1 }
        fn main() -> i64 ! {panic} { apply(make) }"#,
        42,
    );
}

#[test]
fn equations_without_a_unique_natural_solution_stay_explicit() {
    for grade in ["G * 2", "G + G", "G * 0"] {
        rejects(
            &format!(
                r#"fn make<G: Grade>() -> Box<i64> @[{grade}] ! {{alloc, panic}} {{ Box.new(1) }}
                fn apply(f: fn() -> Box<i64> @[1] ! {{alloc, panic}}) -> i64 ! {{alloc, panic}} {{
                    Box.take(f())
                }}
                fn main() -> i64 ! {{alloc, panic}} {{ apply(make) }}"#
            ),
            "cannot infer usage grade parameter",
        );
    }
}

#[test]
fn a_binder_in_an_underlying_type_is_not_inferred() {
    rejects(
        r#"fn make<G: Grade>() -> Box<i64 @[G]> @[1] ! {alloc, panic} { Box.new(1) }
        fn apply(f: fn() -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f())
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        "underlying",
    );
}
