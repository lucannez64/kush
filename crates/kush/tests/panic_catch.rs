//! PANIC-UNWIND-USE: `Task.catch(lambda)` stops a panic and returns
//! `Result<T, std.task.Panic>`; everything the unwound code owned is freed
//! (both backends check that every allocation was released). A spawned
//! task or thread unwinds to its entry and its join raises the panic in the
//! joiner; a panic nothing catches still aborts.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::process::{Command, Stdio};

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program = kush::program::load_source("<panic-catch-test>", source)
        .map_err(|(_, error)| error.message)?;
    executable::check_program(&program).map_err(|error| program.sources.render(&error))
}

/// The reference output, or the error that ended the run.
fn reference(source: &str) -> Result<String, String> {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let mut output = Vec::new();
    match program.evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty()) {
        Ok((status, stats)) => {
            assert_eq!(status, 0);
            assert_eq!(stats.allocations, stats.deallocations, "reference cleanup must be balanced");
            Ok(String::from_utf8(output).unwrap())
        }
        Err(error) => Err(error.message),
    }
}

/// The native output and exit status.
fn native(source: &str) -> (String, Option<i32>, String) {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("catch");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    (
        String::from_utf8(output.stdout).unwrap(),
        output.status.code(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn both(source: &str, expected: &str) {
    assert_eq!(reference(source).as_deref(), Ok(expected), "reference");
    let (stdout, status, stderr) = native(source);
    assert_eq!(status, Some(0), "native stderr: {stderr}");
    assert_eq!(stdout, expected, "native");
}

const PRELUDE: &str = r#"
use std.result.Result;
use std.task.Panic;
use std.task.TaskExit;

fn show(result: Result<i64, Panic>) -> Unit ! {io, panic} {
    match result {
        Result.Ok(value) => print_i64(value),
        Result.Err(_) => print_i64(-1),
    }
}

/// Panics (index out of bounds) while owning a buffer, a box and a vector.
fn boom(depth: i64) -> i64 ! {alloc, panic} {
    let held = Bytes.from("owned on the way down");
    let boxed = Box.new(5);
    let mut list: Vec<i64> = Vec.with_capacity(2);
    list = Vec.push(list, depth);
    if depth == 0 {
        let empty = Bytes.with_capacity(0);
        return Bytes.get(&empty, 3);
    }
    boom(depth - 1) + Bytes.len(&held) + Vec.len(&list) + Box.read(&boxed)
}
"#;

#[test]
fn a_catch_returns_ok_or_err_and_frees_everything() {
    both(
        &format!(
            "{PRELUDE}
fn main() -> i64 ! {{io, alloc, panic, suspend}} {{
    show(Task.catch(fn() -> i64 ! {{alloc, panic}} {{ 40 + 2 }}));
    show(Task.catch(fn() -> i64 ! {{alloc, panic}} {{ boom(5) }}));
    // Nested: the inner catch stops it; the outer one completes.
    show(Task.catch(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
        let inner = Task.catch(fn() -> i64 ! {{alloc, panic}} {{ boom(2) }});
        match inner {{ Result.Ok(v) => v, Result.Err(_) => 7 }}
    }}));
    // Checked arithmetic and an explicit panic().
    show(Task.catch(fn() -> i64 ! {{alloc, panic}} {{ let big = 9223372036854775807; big + 1 }}));
    show(Task.catch(fn() -> i64 ! {{alloc, panic}} {{ panic() }}));
    0
}}"
        ),
        "42\n-1\n7\n-1\n-1\n",
    );
}

#[test]
fn a_task_panic_is_raised_at_its_join() {
    both(
        &format!(
            "{PRELUDE}
fn main() -> i64 ! {{io, alloc, panic, suspend}} {{
    // An explicit join inside the catch raises the child's panic there.
    show(Task.catch(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
        Task.scope(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
            let child = Task.spawn(fn() -> i64 ! {{alloc, panic}} {{ boom(3) }});
            match Task.join(child) {{ TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }}
        }})
    }}));
    // An unjoined child is joined by the scope epilogue, which raises it;
    // the catch is itself a scope here.
    show(Task.catch(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
        Task.spawn(fn() -> i64 ! {{alloc, panic}} {{ boom(1) }});
        5
    }}));
    // A sibling that waits is cancelled while the panic unwinds the scope.
    show(Task.catch(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
        Task.scope(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
            let waiting = Task.spawn(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
                let mut n = 0;
                while !Task.yield() {{ n = n + 1; }}
                n
            }});
            boom(0)
        }})
    }}));
    0
}}"
        ),
        "-1\n-1\n-1\n",
    );
}

#[test]
fn a_thread_panic_is_raised_at_its_join() {
    both(
        &format!(
            "{PRELUDE}
fn main() -> i64 ! {{io, alloc, panic, suspend}} {{
    show(Task.catch(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
        Thread.scope(fn() -> i64 ! {{io, alloc, panic}} {{
            let worker = Thread.spawn(fn() -> i64 ! {{alloc, panic}} {{ boom(4) }});
            let fine = Thread.spawn(fn() -> i64 ! {{alloc, panic}} {{ 9 }});
            Thread.join(fine) + Thread.join(worker)
        }})
    }}));
    0
}}"
        ),
        "-1\n",
    );
}

#[test]
fn an_uncaught_panic_still_ends_the_program() {
    let source = format!(
        "{PRELUDE}
fn main() -> i64 ! {{io, alloc, panic, suspend}} {{
    show(Task.catch(fn() -> i64 ! {{alloc, panic}} {{ 1 }}));
    Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
        let child = Task.spawn(fn() -> i64 ! {{alloc, panic}} {{ boom(2) }});
        let _ = Task.join(child);
    }});
    print_i64(99);
    0
}}"
    );
    let error = reference(&source).unwrap_err();
    assert!(error.starts_with("panic"), "{error}");
    let (stdout, status, stderr) = native(&source);
    assert_eq!(stdout, "1\n");
    assert_ne!(status, Some(0));
    assert!(stderr.contains("panic: a joined task or thread panicked"), "{stderr}");
}

#[test]
fn a_catch_needs_std_task() {
    let error = checked(
        "use std.result.Result;
         fn main() -> i64 ! {alloc, panic, suspend} {
             match Task.catch(fn() -> i64 ! {} { 1 }) { Result.Ok(v) => v, Result.Err(_) => 0 }
         }",
    )
    .err()
    .expect("accepted");
    assert!(error.contains("std.task.Panic"), "{error}");
}
