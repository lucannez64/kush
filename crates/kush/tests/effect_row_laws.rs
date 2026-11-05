//! EFF-ROW-LAWS through the checker (docs/effect-capabilities.md section 4).
//!
//! The unit tests in `src/row_laws_tests.rs` check the row operations over the
//! full 16-bit universe. These tests check that the language rules built on
//! them obey the same laws: every subset of the four builtin effects is tried
//! for each law (composition, monotonicity of calls and arrows, discharge,
//! subtraction and bounded binders), and the expected verdict is computed from
//! set semantics, not from observed behaviour. Accepted programs that run are
//! compared between the reference evaluator and the native backend with
//! balanced allocations.

use kush::executable::{MemoryStats, check};

const BUILTINS: [&str; 4] = ["io", "alloc", "panic", "suspend"];

fn row(bits: u8) -> String {
    BUILTINS
        .iter()
        .enumerate()
        .filter(|(index, _)| bits & (1 << index) != 0)
        .map(|(_, name)| *name)
        .collect::<Vec<_>>()
        .join(", ")
}

fn subset(a: u8, b: u8) -> bool {
    a & !b == 0
}

fn accepted(source: &str) -> bool {
    match check(source) {
        Ok(_) => true,
        Err(error) => {
            // Only effect diagnostics count as a law verdict; any other
            // rejection means the test program itself is wrong.
            assert!(
                error.message.contains("effect")
                    || error.message.contains("row")
                    || error.message.contains("type mismatch: expected fn()")
                    || error.message.contains("excluded"),
                "unexpected rejection: {error:?}\n{source}"
            );
            false
        }
    }
}

fn law(source: &str, expected: bool) {
    assert_eq!(accepted(source), expected, "{source}");
}

fn run(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats)
}

fn agrees(source: &str, expected: i64) -> MemoryStats {
    let (result, stats) = run(source);
    assert_eq!(result, expected, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("effect-row-laws");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
    }
    stats
}

#[test]
fn calls_are_monotone_in_the_caller_row() {
    for callee in 0..16u8 {
        for caller in 0..16u8 {
            law(
                &format!(
                    "fn g() -> i64 ! {{{}}} {{ 1 }}
                     fn h() -> i64 ! {{{}}} {{ g() }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    row(callee),
                    row(caller)
                ),
                subset(callee, caller),
            );
        }
    }
}

#[test]
fn sequential_composition_requires_the_union_of_rows() {
    for first in 0..16u8 {
        for second in 0..16u8 {
            for caller in [
                0u8,
                first,
                second,
                first | second,
                15,
                (first | second) & 0b0111,
            ] {
                law(
                    &format!(
                        "fn g1() -> i64 ! {{{}}} {{ 1 }}
                         fn g2() -> i64 ! {{{}}} {{ 2 }}
                         fn h() -> i64 ! {{{}}} {{ g1(); g2() }}
                         fn main() -> i64 ! {{}} {{ 0 }}",
                        row(first),
                        row(second),
                        row(caller)
                    ),
                    subset(first | second, caller),
                );
            }
        }
    }
}

#[test]
fn arrow_subeffecting_is_inclusion() {
    for source_row in 0..16u8 {
        for target_row in 0..16u8 {
            law(
                &format!(
                    "fn g() -> i64 ! {{{}}} {{ 1 }}
                     fn main() -> i64 ! {{}} {{
                         let f: fn() -> i64 ! {{{}}} = g;
                         0
                     }}",
                    row(source_row),
                    row(target_row)
                ),
                subset(source_row, target_row),
            );
        }
    }
}

#[test]
fn handle_discharges_only_its_operation() {
    // The body performs the declared `Op` and has builtin row `body`; a
    // dynamic perform also needs `panic` (missing handler). The enclosing
    // function must cover `body | panic` but never needs `Op`.
    for body in 0..16u8 {
        for caller in 0..16u8 {
            law(
                &format!(
                    "effect Op: i64 -> i64;
                     fn work() -> i64 ! {{{}}} {{ perform Op(1) }}
                     fn h() -> i64 ! {{{}}} {{
                         handle Op: i64 -> i64 with fn(
                             x: i64,
                             resume: linear once fn(i64) -> i64 ! {{}},
                         ) -> i64 ! {{}} {{ resume(x) }} {{ work() }}
                     }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    [row(body | 0b0100), "Op".to_owned()]
                        .into_iter()
                        .filter(|part| !part.is_empty())
                        .collect::<Vec<_>>()
                        .join(", "),
                    row(caller)
                ),
                subset(body | 0b0100, caller),
            );
        }
    }
    // Without the handle, `Op` is required.
    law(
        "effect Op: i64 -> i64;
         fn work() -> i64 ! {Op, panic} { perform Op(1) }
         fn h() -> i64 ! {panic} { work() }
         fn main() -> i64 ! {} { 0 }",
        false,
    );
}

#[test]
fn the_handler_row_is_never_dropped() {
    // A lexical handler that prints adds `io` and `panic` to the `handle`
    // expression.
    for caller in 0..16u8 {
        law(
            &format!(
                "fn h() -> i64 ! {{{}}} {{
                     handle Ask: i64 -> i64 with fn(
                         x: i64,
                         resume: linear once fn(i64) -> i64 ! {{}},
                     ) -> i64 ! {{io, panic}} {{ print_i64(x); resume(x) }} {{ perform Ask(1) }}
                 }}
                 fn main() -> i64 ! {{}} {{ 0 }}",
                row(caller)
            ),
            subset(0b0101, caller),
        );
    }
}

#[test]
fn row_subtraction_is_checked_per_specialization() {
    // apply's declared row is `e - io`, but its body calls `f`, which needs
    // all of `e`: a specialization is valid only when `io` is not in `e`.
    // The caller then needs `e - io` (= e).
    for callee in 0..16u8 {
        for caller in 0..16u8 {
            law(
                &format!(
                    "fn apply<e: Effects>(f: fn() -> i64 ! {{e}}) -> i64 ! {{e - io}} {{ f() }}
                     fn g() -> i64 ! {{{}}} {{ 1 }}
                     fn h() -> i64 ! {{{}}} {{ apply(g) }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    row(callee),
                    row(caller)
                ),
                callee & 0b0001 == 0 && subset(callee, caller),
            );
        }
    }
}

#[test]
fn bounded_binders_restrict_the_domain() {
    for callee in 0..16u8 {
        for caller in 0..16u8 {
            // Exclusion: alloc (bit 1) is never a valid specialization.
            law(
                &format!(
                    "fn apply<e: Effects - alloc>(f: fn() -> i64 ! {{e}}) -> i64 ! {{e}} {{ f() }}
                     fn g() -> i64 ! {{{}}} {{ 1 }}
                     fn h() -> i64 ! {{{}}} {{ apply(g) }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    row(callee),
                    row(caller)
                ),
                callee & 0b0010 == 0 && subset(callee, caller),
            );
            // Inclusion: the principal row always contains io (bit 0).
            law(
                &format!(
                    "fn apply<e: Effects + io>(f: fn() -> i64 ! {{e}}) -> i64 ! {{e}} {{ f() }}
                     fn g() -> i64 ! {{{}}} {{ 1 }}
                     fn h() -> i64 ! {{{}}} {{ apply(g) }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    row(callee),
                    row(caller)
                ),
                subset(callee | 0b0001, caller),
            );
        }
    }
}

#[test]
fn a_shared_row_variable_receives_the_union_and_split_rows_are_ambiguous() {
    for first in 0..16u8 {
        for second in 0..16u8 {
            let union = first | second;
            law(
                &format!(
                    "fn two<e: Effects>(f: fn() -> i64 ! {{e}}, g: fn() -> i64 ! {{e}}) -> i64 ! {{e}} {{ f(); g() }}
                     fn g1() -> i64 ! {{{}}} {{ 1 }}
                     fn g2() -> i64 ! {{{}}} {{ 2 }}
                     fn h() -> i64 ! {{{}}} {{ two(g1, g2) }}
                     fn main() -> i64 ! {{}} {{ 0 }}",
                    row(first),
                    row(second),
                    row(union)
                ),
                true,
            );
        }
    }
    // One row made of two variables cannot be split uniquely.
    let error = check(
        "fn split<a: Effects, b: Effects>(f: fn() -> i64 ! {a | b}) -> i64 ! {a | b} { f() }
         fn g() -> i64 ! {io} { 1 }
         fn main() -> i64 ! {io} { split(g) }",
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("several incomparable minimal solutions"),
        "{error:?}"
    );
}

#[test]
fn law_programs_run_with_parity_and_balanced_cleanup() {
    // Discharge with an owning value live across the perform, and a generic
    // row specialization that allocates.
    let stats = agrees(
        "effect Op: i64 -> i64;
         fn work() -> i64 ! {Op, alloc, panic} {
             let b = Box.new(40);
             let r = perform Op(1);
             Box.take(b) + r
         }
         fn apply<e: Effects - io>(f: fn() -> i64 ! {e}) -> i64 ! {e} { f() }
         fn boxed() -> i64 ! {alloc, panic} { Box.take(Box.new(1)) }
         fn main() -> i64 ! {alloc, panic} {
             let a = handle Op: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x ^ 2) } { work() };
             a + apply(boxed)
         }",
        44,
    );
    assert_eq!(stats.allocations, 2, "{stats:?}");
}
