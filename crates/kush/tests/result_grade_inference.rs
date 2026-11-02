//! Inference of an abstract result-transfer grade.
//!
//! A generic function value may leave one grade parameter implicit when it is
//! used only as the entire outer result grade (`-> T @[G]`) and the expected
//! arrow declares the concrete `@[1]` contract. Transparent aliases may carry
//! grade arguments in these result-contract positions, so forwarding and
//! nested aliases preserve the inferred specialization. Every other grade use
//! still requires explicit `::<...>` specialization.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

/// Reference evaluator and native code must agree.
fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("result-grade-inference-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

#[test]
fn a_bare_result_grade_is_inferred_from_the_expected_arrow() {
    agrees(
        r#"fn make<G: Grade>(n: i64) -> Box<i64> @[G] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        42,
        "",
    );
}

#[test]
fn explicit_specialization_remains_available_for_function_values() {
    agrees(
        r#"fn make<G: Grade>(n: i64) -> Box<i64> @[G] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make::<1>) }"#,
        42,
        "",
    );
}

#[test]
fn grade_arguments_forward_through_nested_result_aliases() {
    agrees(
        r#"type Handle<G: Grade, T> = Box<T> @[G];
        type Forward<G: Grade, T> = Handle<G, T>;
        type Nested<G: Grade, T> = Forward<G, T>;
        fn make<G: Grade, T>(n: T) -> Nested<G, T> ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Handle<1, i64> ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        42,
        "",
    );
}

#[test]
fn an_ungraded_expected_arrow_cannot_bind_a_result_grade() {
    rejects(
        r#"fn make<G: Grade>(n: i64) -> Box<i64> @[G] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        "cannot infer usage grade parameter",
    );
}

#[test]
fn a_missing_expected_arrow_cannot_bind_a_result_grade() {
    rejects(
        r#"fn make<G: Grade>(n: i64) -> Box<i64> @[G] ! {alloc, panic} { Box.new(n) }
        fn main() -> i64 ! {alloc, panic} { let f = make; Box.take(f(42)) }"#,
        "needs an expected 'fn(...)' type",
    );
}

#[test]
fn a_grade_reaching_a_parameter_is_solved_and_checked_for_conflicts() {
    // A parameter grade is now a real inference constraint: here the expected
    // arrow parameters are ungraded, so the result contract determines G = 1
    // and the specialization simply has a stricter @[1] parameter.
    agrees(
        r#"fn make<G: Grade>(n: i64, b: Box<i64> @[G]) -> Box<i64> @[G] ! {alloc, panic} {
            Box.take(b); Box.new(n)
        }
        fn apply(f: fn(i64, Box<i64>) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42, Box.new(0)))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        42,
        "",
    );
    // Two positions demand different values for the same binder.
    rejects(
        r#"fn make<G: Grade>(b: i64 @[G]) -> Box<i64> @[G] ! {alloc, panic} { Box.new(b) }
        fn apply(f: fn(i64 @[2]) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        "conflicting inferred grades",
    );
}

#[test]
fn a_grade_used_inside_the_underlying_result_blocks_inference() {
    rejects(
        r#"fn make<G: Grade>(n: i64) -> Box<i64 @[G]> @[1] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        "cannot infer usage grade parameter",
    );
}

#[test]
fn composite_result_grades_use_the_single_occurrence_solver() {
    // `G + 1 = 1` has the unique natural solution G = 0.
    agrees(
        r#"fn make<G: Grade>(n: i64) -> Box<i64> @[G + 1] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        42,
        "",
    );
    // `G * 2 = 1` has no natural solution, and `G + G` has two occurrences,
    // so both stay explicit-specialization errors.
    for grade in ["G * 2", "G + G"] {
        rejects(
            &format!(
                r#"fn make<G: Grade>(n: i64) -> Box<i64> @[{grade}] ! {{alloc, panic}} {{ Box.new(n) }}
                fn apply(f: fn(i64) -> Box<i64> @[1] ! {{alloc, panic}}) -> i64 ! {{alloc, panic}} {{
                    Box.take(f(42))
                }}
                fn main() -> i64 ! {{alloc, panic}} {{ apply(make) }}"#
            ),
            "cannot infer usage grade parameter",
        );
    }
}

#[test]
fn extra_grade_parameters_are_not_silently_dropped() {
    rejects(
        r#"fn make<A: Grade, B: Grade>(n: i64) -> Box<i64> @[A] ! {alloc, panic} { Box.new(n) }
        fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            Box.take(f(42))
        }
        fn main() -> i64 ! {alloc, panic} { apply(make) }"#,
        "cannot infer usage grade parameter",
    );
}

#[test]
fn unsupported_result_grades_through_aliases_are_still_rejected() {
    for grade in ["0", "2", "many"] {
        rejects(
            &format!(
                r#"type Handle<G: Grade, T> = Box<T> @[G];
                fn make() -> Handle<{grade}, i64> ! {{alloc, panic}} {{ Box.new(1) }}
                fn main() -> i64 ! {{alloc, panic}} {{ Box.take(make()) }}"#
            ),
            "result",
        );
    }
}

#[test]
fn copyable_results_through_aliases_carry_a_must_use_contract() {
    agrees(
        r#"type Handle<G: Grade, T> = T @[G];
        fn make() -> Handle<1, i64> ! {} { 42 }
        fn observe(x: i64 @[1]) -> i64 ! {panic} { x + 1 }
        fn main() -> i64 ! {panic} { observe(make()) }"#,
        43,
        "",
    );
    rejects(
        r#"type Handle<G: Grade, T> = T @[G];
        fn make() -> Handle<1, i64> ! {} { 42 }
        fn main() -> i64 ! {} { make(); 0 }"#,
        "must-use `@[1]`",
    );
    // A borrowed view may carry the copyable must-use contract; it is still a
    // view and never becomes an owning value.
    accepts(
        r#"fn view<'a>(s: &'a [i64]) -> &'a [i64] @[1] ! {} { s }
        fn main() -> i64 ! {} { 0 }"#,
    );
}

fn accepts(source: &str) {
    if let Err(error) = check(source) {
        panic!("expected acceptance, got {error:?}: {source}");
    }
}

#[test]
fn grade_arguments_in_parameter_and_stored_alias_positions_are_rejected() {
    rejects(
        r#"type Handle<G: Grade, T> = Box<T> @[G];
        fn consume(b: Handle<1, i64>) -> i64 ! {alloc, panic} { Box.take(b) }
        fn main() -> i64 ! {alloc, panic} { consume(Box.new(1)) }"#,
        "grade parameters are not part of runtime type aliases",
    );
    rejects(
        r#"type Handle<G: Grade, T> = Box<T> @[G];
        struct Holder { b: Handle<1, i64> }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "grade parameters are not part of runtime type aliases",
    );
}
