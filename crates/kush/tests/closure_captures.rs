//! Scoped by-reference closure captures and live mutable scalar views.
//!
//! A mutable scalar capture stores the caller's location in the closure
//! environment. The ownership pass keeps that location loaned until the
//! closure's checked last use, rejects escapes, and distinguishes shared
//! reader captures from exclusive writing captures. A writing call also
//! invalidates proof facts about the captured location.
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

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("closure-captures-test");
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
fn a_mutable_scalar_capture_writes_the_callers_location() {
    agrees(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 41;
            let bump = fn() -> Unit ! {panic} { n = n + 1; };
            bump();
            n
        }
        "#,
        42,
        "",
    );
}

#[test]
fn a_writer_then_a_fresh_reader_sees_the_updated_value() {
    agrees(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 40;
            let bump = fn(by: i64) -> Unit ! {panic} { n = n + by; };
            bump(1);
            let read = fn() -> i64 ! {panic} { n + 1 };
            read()
        }
        "#,
        42,
        "",
    );
}

#[test]
fn a_shared_reader_allows_outer_reads_and_releases_at_its_last_call() {
    agrees(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 41;
            let read = fn() -> i64 ! {panic} { n };
            let observed = n;
            let value = read();
            n = 0;
            observed + value
        }
        "#,
        82,
        "",
    );
}

#[test]
fn a_reader_loan_blocks_writing_while_the_closure_is_live() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 41;
            let read = fn() -> i64 ! {panic} { n };
            n = 0;
            read()
        }
        "#,
        "while a closure capturing it is live",
    );
}

#[test]
fn an_exclusive_writer_blocks_outer_reads_while_it_is_live() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 41;
            let bump = fn() -> Unit ! {panic} { n = n + 1; };
            let observed = n;
            bump();
            observed
        }
        "#,
        "exclusive",
    );
}

#[test]
fn returning_a_borrowing_closure_is_rejected() {
    rejects(
        r#"
        fn make() -> once fn() -> Unit ! {panic} ! {alloc, panic} {
            let mut n = 0;
            let f = fn() -> Unit ! {panic} { n = n + 1; };
            f
        }
        fn main() -> Unit ! {} {}
        "#,
        "scoped",
    );
}

#[test]
fn storing_a_borrowing_closure_in_an_outliving_record_is_rejected() {
    rejects(
        r#"
        struct Holder { f: once fn() -> Unit ! {alloc, panic} }
        fn main() -> Unit ! {alloc, panic} {
            let mut n = 0;
            let h = Holder { f: fn() -> Unit ! {panic} { n = n + 1; } };
        }
        "#,
        "must be called immediately",
    );
}

#[test]
fn sending_a_borrowing_closure_to_a_task_is_rejected() {
    rejects(
        r#"
        fn main() -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let mut n = 0;
                Task.spawn(fn() -> Unit ! {panic} { n = n + 1; });
            });
        }
        "#,
        "spawned task may borrow only",
    );
}

#[test]
fn a_borrowing_closure_cannot_escape_its_lexical_block() {
    rejects(
        r#"
        fn main() -> Unit ! {alloc, panic} {
            let f = {
                let mut n = 0;
                let inner = fn() -> Unit ! {panic} { n = n + 1; };
                inner
            };
            f();
        }
        "#,
        "scoped",
    );
}

#[test]
fn two_exclusive_captures_of_one_location_are_rejected() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 0;
            let first = fn() -> Unit ! {panic} { n = n + 1; };
            let second = fn() -> Unit ! {panic} { n = n + 2; };
            first();
            second();
            n
        }
        "#,
        "cannot create an exclusive",
    );
}

#[test]
fn moving_a_captured_slice_owner_while_the_closure_is_live_is_rejected() {
    rejects(
        r#"
        fn main() -> Unit ! {alloc, panic} {
            let mut values: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut values[..];
            let bump = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            drop(values);
            bump();
        }
        "#,
        "cannot move or drop",
    );
}

#[test]
fn proof_facts_before_a_writer_call_cannot_be_reused_after_it() {
    rejects(
        r#"
        fn below(i: i64, n: i64, erased p: { i < n }) -> i64 ! {} { i }
        fn main() -> i64 ! {alloc, panic} {
            let mut i = 0;
            let n = 10;
            if i < n {
                let bump = fn() -> Unit ! {panic} { i = i + 1; };
                bump();
                below(i, n, _)
            } else {
                0
            }
        }
        "#,
        "cannot prove",
    );
}

#[test]
fn proof_facts_survive_a_reader_closure_call() {
    agrees(
        r#"
        fn below(i: i64, n: i64, erased p: { i < n }) -> i64 ! {} { i }
        fn main() -> i64 ! {alloc, panic} {
            let mut i = 0;
            let n = 10;
            if i < n {
                let read = fn() -> i64 ! {panic} { i };
                let value = read();
                below(i, n, _) + value
            } else {
                0
            }
        }
        "#,
        0,
        "",
    );
}
