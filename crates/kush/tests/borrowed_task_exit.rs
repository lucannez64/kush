//! A child task may return a borrowed `TaskExit<R>`: it joins a grandchild in
//! its own `Task.scope` and returns the exit, whose leaves point at storage
//! the outer scope captured from outside. The parent's join produces
//! `TaskExit<TaskExit<R>>`; matching both levels rebinds the same per-field
//! loans. Cancellation at either level yields `Cancelled` and never exposes a
//! view. Positive cases run in both backends with balanced allocations.
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
        let binary = scratch.path().join("borrowed-task-exit-test");
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

const NESTED: &str = r#"
use std.task.TaskExit;
struct Window<'a> { view: &'a [i64], start: i64 }
fn make<'a>(window: Window<'a>) -> TaskExit<TaskExit<Window<'a>>> ! {alloc, panic, suspend} {
    Task.scope(fn() -> TaskExit<TaskExit<Window<'a>>> ! {alloc, panic, suspend} {
        let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                Task.join(Task.spawn(fn() -> Window<'a> ! {panic, suspend} { Task.yield(); window }))
            })
        });
        Task.join(t)
    })
}
fn read<'a>(e: TaskExit<TaskExit<Window<'a>>>) -> i64 ! {panic} {
    match e {
        TaskExit.Completed(inner) => match inner {
            TaskExit.Completed(w) => Slice.get(w.view, w.start),
            TaskExit.Cancelled => 1,
        },
        TaskExit.Cancelled => 2,
    }
}
"#;

#[test]
fn a_child_returns_a_joined_borrowed_exit() {
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                        Task.join(Task.spawn(fn() -> Window<'a> ! {panic, suspend} { Task.yield(); window }))
                    })
                });
                match Task.join(t) {
                    TaskExit.Completed(inner) => match inner {
                        TaskExit.Completed(w) => Slice.get(w.view, w.start),
                        TaskExit.Cancelled => 1,
                    },
                    TaskExit.Cancelled => 2,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [5, 6, 7];
            run(Window { view: &data[..], start: 1 })
        }"#,
        6,
        "",
    );
    // The nested exit crosses a function boundary and is matched by a helper.
    agrees(
        &format!(
            "{NESTED}
            fn main() -> i64 ! {{alloc, panic, suspend}} {{
                let mut data: [i64; 3] = [5, 6, 7];
                let e = make(Window {{ view: &data[..], start: 2 }});
                let r = read(e);
                data = [0, 0, 0];
                r + data[0]
            }}"
        ),
        7,
        "",
    );
}

#[test]
fn the_nested_exit_keeps_the_outer_storage_borrowed() {
    rejects(
        &format!(
            "{NESTED}
            fn main() -> i64 ! {{alloc, panic, suspend}} {{
                let mut data: [i64; 3] = [5, 6, 7];
                let e = make(Window {{ view: &data[..], start: 2 }});
                data = [0, 0, 0];
                read(e)
            }}"
        ),
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        &format!(
            "{NESTED}
            fn main() -> i64 ! {{alloc, panic, suspend}} {{
                let mut data: [i64; 3] = [5, 6, 7];
                let e = make(Window {{ view: &data[..], start: 2 }});
                match e {{
                    TaskExit.Completed(inner) => match inner {{
                        TaskExit.Completed(w) => {{ data = [0, 0, 0]; Slice.get(w.view, w.start) }},
                        TaskExit.Cancelled => 1,
                    }},
                    TaskExit.Cancelled => 2,
                }}
            }}"
        ),
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // A grandchild cannot return a view of storage owned by the child.
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                    let local: [i64; 2] = [8, 9];
                    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                        Task.join(Task.spawn(fn() -> Window<'a> ! {panic, suspend} { Window { view: &local[..], start: 0 } }))
                    })
                });
                match Task.join(t) {
                    TaskExit.Completed(inner) => 0,
                    TaskExit.Cancelled => 2,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} { 0 }"#,
        "",
    );
    // Only one level: a child cannot return a nested borrowed exit.
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<TaskExit<Window<'a>>>> = Task.spawn(fn() -> TaskExit<TaskExit<Window<'a>>> ! {panic, suspend} { panic() });
                Task.join(t);
                0
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} { 0 }"#,
        "a child task may return TaskExit<R> only for a borrowed record R",
    );
    // A joined exit still cannot be constructed by user code.
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64] }
        fn forge<'a>(view: &'a [i64]) -> i64 ! {} {
            let forged: TaskExit<TaskExit<Window<'a>>> = TaskExit.Completed(TaskExit.Cancelled);
            0
        }
        fn main() -> i64 ! {} { 0 }"#,
        "produced only by Task.join",
    );
}

#[test]
fn cancellation_never_exposes_a_dangling_view() {
    // The grandchild is cancelled (inner Cancelled), and the child is
    // cancelled before its join (outer Cancelled; its completed exit is an
    // affine value dropped in the worker). Owned metadata is released once.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], owner: Vec<i64>, start: i64 }
        fn run<'a>(view: &'a [i64]) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                        let g: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {alloc, panic, suspend} {
                            Task.yield();
                            Window { view: view, owner: [1, 2, 3], start: 1 }
                        });
                        Task.cancel(&g);
                        Task.join(g)
                    })
                });
                let u: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                        Task.join(Task.spawn(fn() -> Window<'a> ! {alloc, panic, suspend} {
                            Task.yield();
                            Window { view: view, owner: [4], start: 0 }
                        }))
                    })
                });
                Task.cancel(&u);
                let a = match Task.join(t) {
                    TaskExit.Completed(inner) => match inner {
                        TaskExit.Completed(w) => Slice.get(w.view, w.start) + Vec.len(&w.owner) * 100,
                        TaskExit.Cancelled => 10,
                    },
                    TaskExit.Cancelled => 20,
                };
                let b = match Task.join(u) {
                    TaskExit.Completed(inner) => match inner {
                        TaskExit.Completed(w) => Slice.get(w.view, w.start) + 1000,
                        TaskExit.Cancelled => 30,
                    },
                    TaskExit.Cancelled => 40,
                };
                a + b
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [5, 6, 7];
            run(&data[..])
        }"#,
        50,
        "",
    );
    // Without cancellation the owned metadata travels through both exits.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], owner: Vec<i64>, start: i64 }
        fn run<'a>(view: &'a [i64]) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                        Task.join(Task.spawn(fn() -> Window<'a> ! {alloc, panic, suspend} {
                            Task.yield();
                            Window { view: view, owner: [1, 2, 3], start: 2 }
                        }))
                    })
                });
                match Task.join(t) {
                    TaskExit.Completed(inner) => match inner {
                        TaskExit.Completed(w) => Slice.get(w.view, w.start) + Vec.len(&w.owner) * 100,
                        TaskExit.Cancelled => 10,
                    },
                    TaskExit.Cancelled => 20,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [5, 6, 7];
            run(&data[..])
        }"#,
        307,
        "",
    );
}
