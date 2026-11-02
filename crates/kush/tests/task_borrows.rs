//! Scoped tasks borrowing slice views. A scope joins every child before it
//! returns, so a child may borrow views the scope body captured from outside;
//! those loans hold for the rest of the scope body.
use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let source = format!("use std.task.TaskExit;\n{source}");
    let error = check(&source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

/// Reference evaluator and native code must agree, with no leaked allocation.
fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = if source.contains("use std.task.TaskExit;") {
        source.to_owned()
    } else {
        format!("use std.task.TaskExit;\n{source}")
    };
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(String::from_utf8(output).unwrap(), expected_output);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("task-borrows-test");
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
fn scope_bodies_and_children_borrow_outside_views() {
    agrees(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 2] = [40, 2];
            let view: &[i64] = &data[..];
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t = Task.spawn(fn() -> i64 ! {panic, suspend} { Task.yield(); Slice.get(view, 0) });
                let own = Slice.get(view, 1);
                match Task.join(t) { TaskExit.Completed(v) => v + own, TaskExit.Cancelled => 0 }
            })
        }",
        42,
        "",
    );
    // Disjoint exclusive halves go to different children; the parent keeps
    // using a half it did not lend.
    agrees(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 4] = [1, 2, 3, 4];
            let view: &mut [i64] = &mut data[..];
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let (left, right) = Slice.split_at_mut(view, 2);
                Task.spawn(fn() -> Unit ! {panic, suspend} { Task.yield(); Slice.set(left, 0, 10); });
                Slice.set(right, 0, 30);
            });
            data[0] + data[2]
        }",
        40,
        "",
    );
    // Shared views may be lent to many children, including from a loop.
    agrees(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 2, 3];
            let view: &[i64] = &data[..];
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let mut i = 0;
                while i < 3 {
                    Task.spawn(fn() -> i64 ! {panic} { Slice.get(view, 0) });
                    i = i + 1;
                }
                Slice.get(view, 2)
            })
        }",
        3,
        "",
    );
    // Once the scope has joined its children, the owner is free again.
    agrees(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let owner: Vec<i64> = [7];
            let view: &[i64] = &owner[..];
            let r = Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                Task.spawn(fn() -> i64 ! {panic} { Slice.get(view, 0) });
                1
            });
            drop(owner);
            r
        }",
        1,
        "",
    );
}

#[test]
fn children_cannot_borrow_storage_that_dies_before_the_final_join() {
    rejects(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let local: [i64; 1] = [5];
                let v: &[i64] = &local[..];
                Task.spawn(fn() -> i64 ! {panic} { Slice.get(v, 0) });
                0
            })
        }",
        "captured from outside the scope",
    );
    // An owner moved into the scope body is owned by it, not by the caller.
    rejects(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let owner: Vec<i64> = [7];
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let v: &[i64] = &owner[..];
                Task.spawn(fn() -> i64 ! {panic} { Slice.get(v, 0) });
                0
            })
        }",
        "captured from outside the scope",
    );
}

#[test]
fn lent_views_stay_borrowed_for_the_rest_of_the_scope() {
    // A child reading through a reborrow keeps the parent from writing.
    rejects(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut data[..];
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let reader: &[i64] = &view[..];
                Task.spawn(fn() -> i64 ! {panic} { Slice.get(reader, 0) });
                Slice.set(view, 0, 9);
            });
            0
        }",
        "lent to a spawned task",
    );
    // Two children cannot get overlapping exclusive views.
    rejects(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut data[..];
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let a: &mut [i64] = &mut view[0..1];
                Task.spawn(fn() -> Unit ! {panic} { Slice.set(a, 0, 3); });
                let b: &mut [i64] = &mut view[0..1];
                Task.spawn(fn() -> Unit ! {panic} { Slice.set(b, 0, 4); });
            });
            0
        }",
        "lent to a spawned task",
    );
    // The parent cannot reuse the split parent while a half is lent.
    rejects(
        "fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 4] = [1, 2, 3, 4];
            let view: &mut [i64] = &mut data[..];
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let (left, right) = Slice.split_at_mut(view, 2);
                Task.spawn(fn() -> Unit ! {panic} { Slice.set(left, 0, 10); });
                Slice.set(view, 0, 99);
            });
            0
        }",
        "lent to a spawned task",
    );
}

#[test]
fn task_borrows_example_agrees_natively() {
    agrees(
        include_str!("../../../examples/task-borrows.kush"),
        21,
        "6\n15\n",
    );
}
