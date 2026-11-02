#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable::{self, MemoryStats},
    native::{self, Scratch},
};
use std::{fs, process::Command};

const RESULT: &str = "enum Result<T,E>{Ok(T),Err(E)}";
const TASK_EXIT: &str = "use std.task.TaskExit;";

fn check(source: &str) -> kush::executable::Executable {
    executable::check(source).unwrap()
}

fn rejects(source: &str, expected: &str) {
    let error = executable::check(source).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected:?}, got {:?}",
        error.message
    );
}

fn stats_line(stderr: &[u8]) -> MemoryStats {
    let text = String::from_utf8_lossy(stderr);
    let line = text
        .lines()
        .find(|line| line.starts_with("allocation-stats: "))
        .unwrap_or_else(|| panic!("missing allocation stats: {text}"));
    let field = |name: &str| -> usize {
        line.split_whitespace()
            .find_map(|part| part.strip_prefix(name))
            .and_then(|value| value.strip_prefix('='))
            .and_then(|value| value.parse().ok())
            .unwrap_or_else(|| panic!("missing {name} in {line}"))
    };
    MemoryStats {
        allocations: field("allocations"),
        deallocations: field("deallocations"),
        peak_live: field("peak-live"),
        buffer_growths: field("buffer-growths"),
        reuses: field("reuses"),
        fusions: field("fusions"),
    }
}

fn compare(source: &str) -> (Vec<u8>, MemoryStats, MemoryStats) {
    let program = check(source);
    let mut expected_output = Vec::new();
    let (expected_exit, reference) = program
        .evaluate_with_io_and_stats(&mut std::io::empty(), &mut expected_output)
        .unwrap();
    assert_eq!(
        reference.allocations, reference.deallocations,
        "reference allocation imbalance: {reference:?}"
    );
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("program");
    native::build_with_stats(&program, &binary, true).unwrap();
    let output = Command::new(&binary)
        .current_dir(scratch.path())
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected_exit as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout,
        expected_output,
        "native/reference output mismatch; stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let native_stats = stats_line(&output.stderr);
    assert_eq!(
        native_stats.allocations, native_stats.deallocations,
        "native allocation imbalance: {native_stats:?}"
    );
    assert_eq!(&fs::read(&binary).unwrap()[..4], b"\x7fELF");
    (expected_output, reference, native_stats)
}

#[test]
fn scheduling_order_is_deterministic_and_agrees_across_backends() {
    let source = format!(
        "{TASK_EXIT}
        fn worker(n: i64) -> i64 ! {{io, panic, suspend}} {{
            print_i64(n * 10 + 1);
            Task.yield();
            print_i64(n * 10 + 2);
            n
        }}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let a: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{ worker(1) }});
                let b: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{ worker(2) }});
                print_i64(0);
                match Task.join(a) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
                match Task.join(b) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-2),
                }}
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(
        String::from_utf8(output).unwrap(),
        "0\n11\n21\n12\n22\n1\n2\n"
    );
}

#[test]
fn independent_tasks_yield_join_and_cancel_before_and_after_start() {
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let before: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{
                    print_i64(1);
                    Task.yield();
                    10
                }});
                Task.cancel(&before);
                match Task.join(before) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
                let after: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{
                    print_i64(2);
                    Task.yield();
                    print_i64(3);
                    if Task.check_cancel() {{ -2 }} else {{ 20 }}
                }});
                print_i64(4);
                Task.yield();
                Task.cancel(&after);
                match Task.join(after) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-3),
                }}
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "1\n-1\n4\n2\n3\n-3\n");
}

#[test]
fn sibling_results_and_scope_epilogue_join_ignored_children() {
    let source = format!(
        "{TASK_EXIT}
        {RESULT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let good: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{
                    print_i64(1);
                    7
                }});
                let ignored: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{
                    print_i64(2);
                    8
                }});
                let bad: Task<Result<i64, i64>> = Task.spawn(fn() -> Result<i64, i64> ! {{io, panic, suspend}} {{
                    print_i64(3);
                    Err(9)
                }});
                match Task.join(good) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
                match Task.join(bad) {{
                    TaskExit.Completed(Err(code)) => print_i64(code),
                    TaskExit.Completed(Ok(v)) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-2),
                }}
                let _ = ignored;
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    // The ignored child still runs and is joined by the scope epilogue.
    assert_eq!(String::from_utf8(output).unwrap(), "1\n2\n3\n7\n9\n");
}

#[test]
fn fallible_scope_cancels_unjoined_siblings_on_err() {
    let source = format!(
        "{TASK_EXIT}
        {RESULT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            match Task.scope(fn() -> Result<Unit, i64> ! {{io, alloc, panic, suspend}} {{
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{io, panic, suspend}} {{
                    print_i64(1);
                    if Task.yield() {{ return -1; }}
                    print_i64(2);
                    0
                }});
                let _ = t;
                Err(7)
            }}) {{
                Ok(_) => print_i64(0),
                Err(code) => print_i64(code),
            }}
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "1\n7\n");
}

#[test]
fn early_return_and_question_mark_still_join_children() {
    for body in [
        "let t: Task<i64> = Task.spawn(fn() -> i64 ! {io, panic, suspend} { print_i64(5); 1 }); if true { return Ok(()); }",
        "let t: Task<i64> = Task.spawn(fn() -> i64 ! {io, panic, suspend} { print_i64(6); 1 }); let r: Result<Unit, i64> = Err(3); r?;",
    ] {
        let source = format!(
            "{TASK_EXIT}
            {RESULT}
            fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
                let _ = Task.scope(fn() -> Result<Unit, i64> ! {{io, alloc, panic, suspend}} {{
                    {body}
                    Ok(())
                }});
                print_i64(9)
            }}"
        );
        let (output, _, _) = compare(&source);
        let text = String::from_utf8(output).unwrap();
        assert!(text.ends_with("9\n"), "{text}");
        assert!(text.starts_with('5') || text.starts_with('6'), "{text}");
    }
}

#[test]
fn owned_capture_and_owned_result_cleanup_is_balanced() {
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let owner = Box.new(40);
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
                    let value = Box.take(owner);
                    Task.yield();
                    value + 2
                }});
                match Task.join(t) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
                let owned: Task<Box<i64>> = Task.spawn(fn() -> Box<i64> ! {{alloc, panic, suspend}} {{
                    Box.new(42)
                }});
                match Task.join(owned) {{
                    TaskExit.Completed(b) => print_i64(Box.take(b)),
                    TaskExit.Cancelled => print_i64(-2),
                }}
            }})
        }}"
    );
    let (output, reference, native_stats) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "42\n42\n");
    assert!(reference.allocations > 0);
    assert!(native_stats.allocations > 0);
}

#[test]
fn cancelled_owned_result_is_dropped_exactly_once() {
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let t: Task<Box<i64>> = Task.spawn(fn() -> Box<i64> ! {{alloc, panic, suspend}} {{
                    if Task.yield() {{ return Box.new(1); }}
                    Box.new(2)
                }});
                Task.cancel(&t);
                match Task.join(t) {{
                    TaskExit.Completed(b) => print_i64(Box.take(b)),
                    TaskExit.Cancelled => print_i64(-1),
                }}
            }})
        }}"
    );
    let (output, reference, native_stats) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "-1\n");
    assert_eq!(reference.allocations, reference.deallocations);
    assert_eq!(native_stats.allocations, native_stats.deallocations);
}

#[test]
fn slice_and_borrow_lifetimes_survive_same_task_suspension() {
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{panic, suspend}} {{
                    let a: [i64; 3] = [10, 20, 30];
                    let view = a[0..2];
                    Task.yield();
                    Slice.get(view, 1)
                }});
                match Task.join(t) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "20\n");
}

#[test]
fn nosuspend_rejects_reachable_suspension_and_unconstrained_rows() {
    rejects(
        "#[nosuspend] fn f() -> Unit ! {suspend} { Task.yield(); } fn main()->i64 ! {} {0}",
        "nosuspend contract forbids the suspend effect",
    );
    rejects(
        "#[nosuspend] fn f<e: Effects>(g: fn() -> Unit ! {e}) -> Unit ! {e} { g() } fn main()->i64 ! {} {0}",
        "nosuspend contracts cannot be effect-polymorphic",
    );
    rejects(
        "#[nosuspend] fn f(g: fn() -> Unit ! {suspend}) -> Unit ! {} { g() } fn main()->i64 ! {} {0}",
        "requires effects {suspend}",
    );
    rejects(
        "#[nosuspend] fn f() -> Unit ! {} { Task.yield(); } fn main()->i64 ! {} {0}",
        "requires effects {suspend}",
    );
    check("#[nosuspend] fn f(x: i64) -> i64 ! {panic} { x + 1 } fn main()->i64 ! {panic} {f(1)}");
}

#[test]
fn noalloc_rejects_spawn_and_effect_polymorphic_suspending_calls_propagate() {
    rejects(
        "#[noalloc] fn f() -> Unit ! {panic, suspend} { Task.scope(fn() -> Unit ! {alloc, panic, suspend} { }) } fn main()->i64 ! {} {0}",
        "requires effects {alloc}",
    );
    let source = format!(
        "{TASK_EXIT}
        fn apply<e: Effects>(f: fn(i64) -> i64 ! {{e}}, x: i64) -> i64 ! {{panic, e}} {{ f(x) }}
        fn susp(x: i64) -> i64 ! {{panic, suspend}} {{ Task.yield(); x + 1 }}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{panic, suspend}} {{ apply(susp, 41) }});
                match Task.join(t) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "42\n");
}

#[test]
fn noalloc_tasks_can_yield_and_join_existing_tasks() {
    let source = format!(
        "{TASK_EXIT}
        #[noalloc]
        fn wait(t: Task<i64>) -> TaskExit<i64> ! {{suspend}} {{
            Task.yield();
            Task.join(t)
        }}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{panic, suspend}} {{
                    Task.yield();
                    42
                }});
                match wait(t) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
            }})
        }}"
    );
    let (output, _, _) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "42\n");
}

#[test]
fn linear_task_results_are_joined_and_consumed_or_rejected() {
    rejects(
        &format!(
            "{TASK_EXIT}
            fn main() -> Unit ! {{alloc, panic, suspend}} {{
                Task.scope(fn() -> Unit ! {{alloc, panic, suspend}} {{
                    let b: Box<i64> @[1] = Box.new(1);
                    let t: Task<Box<i64>> = Task.spawn(fn() -> Box<i64> ! {{alloc, panic, suspend}} {{ b }});
                    let _ = Task.join(t);
                }})
            }}"
        ),
        "ungraded result",
    );
    // A graded task result transfers an owning obligation, so joining it with a
    // wildcard discards a linear value.
    rejects(
        &format!(
            "{TASK_EXIT}
            fn main() -> Unit ! {{alloc, panic, suspend}} {{
                Task.scope(fn() -> Unit ! {{alloc, panic, suspend}} {{
                    let b: Box<i64> @[1] = Box.new(1);
                    let t: Task<Box<i64>> = Task.spawn(
                        fn() -> Box<i64> @[1] ! {{alloc, panic, suspend}} {{ b }}
                    );
                    let _ = Task.join(t);
                }})
            }}"
        ),
        "linear",
    );
    // Consuming the capture inside the task before a cancellation request is
    // observed remains the ordinary cleanup path.
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let b: Box<i64> @[1] = Box.new(1);
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {{alloc, panic, suspend}} {{
                    if Task.yield() {{ return Box.take(b); }}
                    Box.take(b)
                }});
                Task.cancel(&t);
                match Task.join(t) {{
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }}
            }})
        }}"
    );
    let (output, reference, native_stats) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "-1\n");
    assert_eq!(reference.allocations, reference.deallocations);
    assert_eq!(native_stats.allocations, native_stats.deallocations);
}

#[test]
fn task_handles_cannot_escape_through_data_results_or_callbacks() {
    rejects(
        "fn f() -> Task<i64> ! {panic} { panic() } fn main()->i64 ! {} {0}",
        "a function cannot return a task handle",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { let _ = Task.scope(fn() -> Task<i64> ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); t }); }",
        "cannot return a task handle",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let b = Box.new(t); drop(b); }) }",
        "task handles cannot be stored in Box",
    );
    rejects(
        "struct S { t: Task<i64> } fn main()->i64 ! {} {0}",
        "task handles cannot be stored in records",
    );
    rejects(
        "enum E { T(Task<i64>) } fn main()->i64 ! {} {0}",
        "task handles cannot be stored in enum payloads",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let u: Task<i64> | i64 = t; }) }",
        "task handles cannot be union members",
    );
    rejects(
        "fn id<T>(x: T) -> T ! {panic} { x } fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let _ = id(t); }) }",
        "a function cannot return a task handle",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let a: [Task<i64>; 1] = [t]; }) }",
        "task handles cannot be stored in arrays",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { let v: Vec<Task<i64>> = Vec.new(); }",
        "task handles cannot be stored",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let f = fn() -> Task<i64> ! {panic} { t }; }) }",
        "a lambda cannot capture a task handle",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.spawn(fn() -> i64 ! {panic,suspend} {1}); }",
        "Task.spawn requires an enclosing Task.scope",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let f: once fn() -> i64 ! {panic,suspend} = fn() -> i64 ! {panic,suspend} {1}; let t: Task<i64> = Task.spawn(f); let _ = Task.join(t); }) }",
        "Task.spawn requires a statically known function or lambda body",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); Task.cancel(t); }) }",
        "Task.cancel borrows the handle",
    );
}

#[test]
fn task_effects_are_required_and_join_needs_the_conventional_exit_enum() {
    rejects(
        "fn main() -> Unit ! {alloc, panic} { Task.scope(fn() -> Unit ! {alloc, panic, suspend} { }) }",
        "requires effects {suspend}",
    );
    rejects(
        "fn main() -> Unit ! {panic, suspend} { Task.scope(fn() -> Unit ! {alloc, panic, suspend} { }) }",
        "requires effects {alloc}",
    );
    rejects(
        "fn main() -> Unit ! {alloc,panic,suspend} { Task.scope(fn() -> Unit ! {alloc,panic,suspend} { let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic,suspend} {1}); let _ = Task.join(t); }) }",
        "Task.join requires enum TaskExit<T>",
    );
}

#[test]
fn suspending_map_callbacks_are_not_fused_as_pure() {
    let source = format!(
        "{TASK_EXIT}
        fn inc(x: i64) -> i64 ! {{panic, suspend}} {{
            Task.yield();
            x + 1
        }}
        fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                let mut values: Vec<i64> = Vec.new();
                values = Vec.push(values, 1);
                values = Vec.push(values, 2);
                let values = Vec.map_in_place(values, inc);
                print_i64(Vec.get(&values, 0) + Vec.get(&values, 1))
            }})
        }}"
    );
    let (output, reference, native_stats) = compare(&source);
    assert_eq!(String::from_utf8(output).unwrap(), "5\n");
    assert_eq!(reference.fusions, 0);
    assert_eq!(native_stats.fusions, 0);
}

#[test]
fn native_and_reference_agree_on_the_async_example_with_balance() {
    let source = include_str!("../../../examples/async.kush");
    let (output, reference, native_stats) = compare(source);
    assert_eq!(
        String::from_utf8(output).unwrap(),
        "0\n11\n21\n12\n22\n1\n2\n7\n-300\n"
    );
    assert_eq!(reference.allocations, reference.deallocations);
    assert_eq!(native_stats.allocations, native_stats.deallocations);
}

#[test]
fn task_result_widening_inserts_checked_callable_adapters() {
    for spawn in [
        "Task.spawn(fn() -> i64 ! {} { 42 })",
        "Task.spawn::<i64 | Bool>(fn() -> i64 ! {} { 42 })",
    ] {
        let source = format!(
            "{TASK_EXIT}
            fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
                Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                    let task: Task<i64 | Bool> = {spawn};
                    match Task.join(task) {{
                        TaskExit.Completed(value) => match value {{
                            i64 @ n => print_i64(n),
                            Bool @ b => print_i64(if b {{ 1 }} else {{ 0 }}),
                        }},
                        TaskExit.Cancelled => print_i64(-1),
                    }}
                }})
            }}"
        );
        let (output, _, _) = compare(&source);
        assert_eq!(output, b"42\n");
    }
    let source = format!(
        "{TASK_EXIT}
        fn main() -> Unit ! {{alloc, panic, suspend}} {{
            Task.scope(fn() -> Unit ! {{alloc, panic, suspend}} {{
                let task: Task<Box<i64> | Bool> =
                    Task.spawn(fn() -> Box<i64> ! {{alloc, panic}} {{ Box.new(42) }});
                Task.cancel(&task);
                let _ = Task.join(task);
            }})
        }}"
    );
    compare(&source);
}
