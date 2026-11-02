//! Grade-zero runtime erasure and observable-initializer guarantees.
//!
//! `@[0]` still evaluates its initializer because Kush is strict. The binding
//! is not materialized: no store, runtime local, read, or cleanup is emitted,
//! and every runtime observation remains a compile-time error. Initializer
//! effects (I/O, panic, allocation) stay observable and agree across backends.
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

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("grade-zero-test");
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
    stats
}

#[test]
fn the_initializer_is_still_evaluated_for_its_effects() {
    agrees(
        r#"fn main() -> i64 ! {io, panic} {
            let value: i64 @[0] = { print_i64(7); 1 };
            42
        }"#,
        42,
        "7\n",
    );
}

#[test]
fn allocation_effects_are_preserved_and_balanced() {
    let stats = agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let value: i64 @[0] = Box.take(Box.new(9));
            42
        }"#,
        42,
        "",
    );
    assert_eq!(stats.allocations, 1, "{stats:?}");
    assert_eq!(stats.deallocations, 1, "{stats:?}");
}

#[test]
fn a_custom_algebra_zero_is_erased_the_same_way() {
    agrees(
        r#"algebra Usage {
            elements { None, Once }
            zero = None; one = Once;
            add {
                None + None = None, None + Once = Once,
                Once + None = Once, Once + Once = Once,
            }
            mul {
                None * None = None, None * Once = None,
                Once * None = None, Once * Once = Once,
            }
        }
        fn main() -> i64 ! {io, panic} {
            let value: i64 @[Usage.None] = { print_i64(3); 1 };
            5
        }"#,
        5,
        "3\n",
    );
}

#[test]
fn runtime_observation_of_an_erased_binding_is_rejected() {
    rejects(
        "fn main() -> i64 ! {} { let value: i64 @[0] = 1; value }",
        "grade @[0]",
    );
    rejects(
        "fn main() -> i64 ! {} { let value: i64 @[0] = 1; let other = value; 0 }",
        "grade @[0]",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let value: i64 @[0] = 1; value + 1 }",
        "grade @[0]",
    );
    // Zero runtime observations is exactly the contract, so an unused erased
    // binding is accepted and its initializer still runs.
    if let Err(error) = check("fn main() -> i64 ! {} { let value: i64 @[0] = 1; 0 }") {
        panic!("expected an unused grade-zero binding to be accepted: {error:?}");
    }
}

#[test]
fn owning_values_cannot_be_graded_zero() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} { let value: Box<i64> @[0] = Box.new(1); 0 }",
        "would silently discard",
    );
}
