//! Copyable exact-use `@[1]` results.
//!
//! A result grade on a copyable type is a *must-use* obligation, not an owning
//! move. The value must be bound with `let` (which transfers the obligation),
//! assigned to a `@[1]` binding, returned through a matching `@[1]` result, or
//! observed exactly once by a call argument, aggregate constructor, read,
//! match scrutinee, or `?`. Discarding the value through an expression
//! statement, a wildcard/destructuring binding, `drop`, an unused `let`, or an
//! ungraded return is rejected. The obligation never changes ownership: a
//! copyable result is still copyable and is never treated as a linear move.
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
    assert_eq!(
        stats.allocations, stats.deallocations,
        "allocation balance: {source}"
    );
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
        let binary = scratch.path().join("copyable-result-transfer-test");
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

const MAKE: &str = "fn make() -> i64 @[1] ! {} { 42 }";

#[test]
fn a_copyable_result_is_observed_by_a_call_argument() {
    agrees(
        &format!(
            "{MAKE}
            fn observe(x: i64 @[1]) -> i64 ! {{panic}} {{ x + 1 }}
            fn main() -> i64 ! {{panic}} {{ observe(make()) }}"
        ),
        43,
        "",
    );
}

#[test]
fn a_let_binding_transfers_the_obligation_and_is_used_exactly_once() {
    agrees(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ let x = make(); x }}"),
        42,
        "",
    );
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ let x = make(); 0 }}"),
        "not used consistently before the end of its lexical scope",
    );
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{panic}} {{ let x = make(); x + x }}"),
        "requires exactly 1",
    );
}

#[test]
fn discard_positions_are_rejected() {
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ make(); 0 }}"),
        "discarded by an expression statement",
    );
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ let _ = make(); 0 }}"),
        "must be bound to a simple name",
    );
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ drop(make()); 0 }}"),
        "cannot be dropped",
    );
    rejects(
        &format!("{MAKE}\nfn main() -> i64 ! {{}} {{ let mut y = 0; y = make(); y }}"),
        "another grade would lose the obligation",
    );
}

#[test]
fn branches_loops_and_aliases_preserve_the_obligation() {
    agrees(
        &format!(
            "{MAKE}
            fn main() -> i64 ! {{}} {{ let x = if true {{ make() }} else {{ make() }}; x }}"
        ),
        42,
        "",
    );
    agrees(
        &format!(
            "{MAKE}
            fn main() -> i64 ! {{}} {{ let x = loop {{ break make(); }}; x }}"
        ),
        42,
        "",
    );
    agrees(
        &format!(
            "{MAKE}
            fn alias(x: i64 @[1]) -> i64 @[1] ! {{}} {{ x }}
            fn main() -> i64 ! {{panic}}
            {{ alias(make()) + 0 }}"
        ),
        42,
        "",
    );
}

#[test]
fn question_mark_observes_the_graded_result_once() {
    agrees(
        r#"use std.result.Result;
        fn make_ok(which: Bool) -> Result<i64, i64> @[1] ! {} {
            if which { Ok(1) } else { Err(0) }
        }
        fn use_it(r: Result<i64, i64> @[1]) -> Result<i64, i64> ! {panic} {
            let x = r?;
            Ok(x + 1)
        }
        fn main() -> i64 ! {panic} {
            match use_it(make_ok(true)) {
                Ok(v) => v,
                Err(e) => e,
            }
        }"#,
        2,
        "",
    );
}

#[test]
fn aggregates_observe_the_value_once() {
    agrees(
        &format!(
            "{MAKE}
            fn main() -> i64 ! {{}} {{ let pair = (make(), 1); pair.0 }}"
        ),
        42,
        "",
    );
    // A must-use tuple result cannot be split across destructured bindings.
    rejects(
        r#"fn pair() -> (i64, i64) @[1] ! {} { (1, 2) }
        fn main() -> i64 ! {panic} { let (a, b) = pair(); a + b }"#,
        "must be bound to a simple name",
    );
}

#[test]
fn a_captured_copyable_result_makes_the_closure_linear_once() {
    agrees(
        &format!(
            "{MAKE}
            fn main() -> i64 ! {{alloc, panic}} {{
                let x = make();
                let f: linear once fn() -> i64 ! {{panic}} = fn() -> i64 ! {{panic}} {{ x + 1 }};
                f()
            }}"
        ),
        43,
        "",
    );
}

#[test]
fn an_ungraded_return_cannot_launder_the_obligation() {
    rejects(
        &format!(
            "{MAKE}\nfn pass() -> i64 ! {{}} {{ make() }}\nfn main() -> i64 ! {{}} {{ pass() }}"
        ),
        "must-use `@[1]` contract through an ungraded result",
    );
}

#[test]
fn a_copyable_result_never_becomes_an_owning_move() {
    // The value is copyable: reading it twice is a grade error, not a
    // use-after-move ownership error, and no allocation is attached to it.
    let (status, output, stats) = run(&format!(
        "{MAKE}\nfn main() -> i64 ! {{}} {{ let x = make(); x }}"
    ));
    assert_eq!(status, 42);
    assert_eq!(output, "");
    assert_eq!(stats.allocations, 0);
}
