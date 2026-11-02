//! Linear task results and cancellation-preserving cleanup.
//!
//! Cancellation is cooperative. A task body that reaches a normal exit already
//! consumed or transferred every linear resource on that path. When a
//! cancellation request is set and the body still completes with an owning or
//! intrinsically linear payload, the runtime transfers that payload to the
//! joiner as `Completed` instead of silently discarding it. Handles for such
//! tasks are linear: they must be joined explicitly, including on error paths.
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
        let binary = scratch.path().join("linear-task-test");
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

const JOIN: &str = r#"use std.task.TaskExit;
fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
fn main() -> i64 ! {alloc, panic, suspend} {
    Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
        let task: Task<Box<i64>> = Task.spawn(make);
        match Task.join(task) {
            TaskExit.Completed(b) => Box.take(b),
            TaskExit.Cancelled => 0,
        }
    })
}"#;

#[test]
fn an_owning_task_result_transfers_through_join() {
    agrees(JOIN, 42);
}

#[test]
fn cancellation_transfers_a_completed_linear_payload_instead_of_dropping_it() {
    agrees(
        r#"use std.task.TaskExit;
        fn make() -> Box<i64> @[1] ! {alloc, panic, suspend} {
            let cancelled = Task.yield();
            Box.new(if cancelled { 7 } else { 9 })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let task: Task<Box<i64>> = Task.spawn(make);
                Task.cancel(&task);
                match Task.join(task) {
                    TaskExit.Completed(b) => Box.take(b),
                    TaskExit.Cancelled => 0,
                }
            })
        }"#,
        7,
    );
}

#[test]
fn a_linear_capture_is_transferred_to_the_joined_result() {
    agrees(
        r#"use std.task.TaskExit;
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let b = Box.new(11);
                let task: Task<Box<i64>> = Task.spawn(
                    fn() -> Box<i64> @[1] ! {alloc, panic, suspend} {
                        let cancelled = Task.yield();
                        b
                    },
                );
                Task.cancel(&task);
                match Task.join(task) {
                    TaskExit.Completed(x) => Box.take(x),
                    TaskExit.Cancelled => 0,
                }
            })
        }"#,
        11,
    );
}

#[test]
fn a_linear_task_handle_must_be_joined() {
    rejects(
        r#"fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                Task.spawn(make);
            });
            0
        }"#,
        "linear value is discarded",
    );
    rejects(
        r#"fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let task: Task<Box<i64>> = Task.spawn(make);
            });
            0
        }"#,
        "linear",
    );
}

#[test]
fn a_scope_result_may_carry_a_linear_obligation() {
    agrees(
        r#"fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(5) }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Box.take(Task.scope(fn() -> Box<i64> @[1] ! {alloc, panic, suspend} { make() }))
        }"#,
        5,
    );
}

#[test]
fn copyable_task_results_carry_a_must_join_and_must_use_obligation() {
    agrees(
        r#"use std.task.TaskExit;
        fn make() -> i64 @[1] ! {} { 42 }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(make);
                match Task.join(task) {
                    TaskExit.Completed(value) => value,
                    TaskExit.Cancelled => 0,
                }
            })
        }"#,
        42,
    );
    // Cancellation preserves the completed copyable payload the same way it
    // preserves an owning one.
    agrees(
        r#"use std.task.TaskExit;
        fn make() -> i64 @[1] ! {suspend} {
            let cancelled = Task.yield();
            if cancelled { 7 } else { 9 }
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(make);
                Task.cancel(&task);
                match Task.join(task) {
                    TaskExit.Completed(value) => value,
                    TaskExit.Cancelled => 0,
                }
            })
        }"#,
        7,
    );
    // The handle is linear, so it must be joined.
    rejects(
        r#"fn make() -> i64 @[1] ! {} { 42 }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(make);
            });
            0
        }"#,
        "linear",
    );
    // The joined exit is must-use: discarding it drops the observation.
    rejects(
        r#"use std.task.TaskExit;
        fn make() -> i64 @[1] ! {} { 42 }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(make);
                Task.join(task);
            });
            0
        }"#,
        "must-use `@[1]` contract",
    );
}

#[test]
fn a_copyable_scope_result_is_must_use() {
    agrees(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            let value: i64 @[1] = Task.scope(fn() -> i64 @[1] ! {alloc, panic, suspend} { 42 });
            value + 0
        }"#,
        42,
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 @[1] ! {alloc, panic, suspend} { 42 });
            0
        }"#,
        "must-use `@[1]` contract",
    );
}
