//! Fibers (FIBER-HANDLERS, docs/tasks-on-handlers.md): `Fiber.new::<Op>`,
//! `Fiber.start` and `Fiber.resume`, through the evaluator and both native
//! backends.
use std::fs;
use std::process::Command;

fn clang_available() -> bool {
    Command::new(std::env::var("KUSH_CLANG").unwrap_or_else(|_| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

struct Run {
    stdout: String,
    stderr: String,
    success: bool,
}

/// Run `source` with the evaluator (`eval`) or built with `flags`.
fn run(source: &str, eval: bool, flags: &[&str]) -> Run {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    fs::write(root.join("main.kush"), source).unwrap();
    let kush = env!("CARGO_BIN_EXE_kush");
    let output = if eval {
        Command::new(kush)
            .current_dir(root)
            .args(["eval", "main.kush"])
            .output()
            .unwrap()
    } else {
        let built = Command::new(kush)
            .current_dir(root)
            .args(["build", "main.kush", "-o", "program"])
            .args(flags)
            .env_remove("KUSH_BACKEND")
            .output()
            .unwrap();
        assert!(
            built.status.success(),
            "{flags:?}: {}\n{source}",
            String::from_utf8_lossy(&built.stderr)
        );
        Command::new(root.join("program")).output().unwrap()
    };
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        success: output.status.success(),
    }
}

fn native_builds() -> Vec<Vec<&'static str>> {
    let mut builds = vec![vec![], vec!["--release"]];
    if clang_available() {
        builds.push(vec!["--release", "--backend", "llvm"]);
    }
    builds
}

/// The evaluator and every native build print `expected` and succeed.
fn agree(source: &str, expected: &str) {
    let evaluated = run(source, true, &[]);
    assert!(evaluated.success, "eval: {}\n{source}", evaluated.stderr);
    assert_eq!(evaluated.stdout, expected, "eval\n{source}");
    for flags in native_builds() {
        let built = run(source, false, &flags);
        assert!(built.success, "{flags:?}: {}\n{source}", built.stderr);
        assert_eq!(built.stdout, expected, "{flags:?}\n{source}");
    }
}

fn rejected(source: &str, message: &str) {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    fs::write(scratch.path().join("main.kush"), source).unwrap();
    let checked = Command::new(env!("CARGO_BIN_EXE_kush"))
        .current_dir(scratch.path())
        .args(["check", "main.kush"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&checked.stderr);
    assert!(!checked.status.success(), "accepted:\n{source}");
    assert!(stderr.contains(message), "{stderr}\n{source}");
}

const PRELUDE: &str = "
use std.fiber.FiberStep;
use std.result.Result;
use std.task.Panic;
use std.task.TaskExit;

effect Emit: i64 -> i64;

fn count(limit: i64) -> i64 ! {Emit} {
    let mut i = 0;
    let mut total = 0;
    while i < limit {
        total = total + perform Emit(i * 10);
        i = i + 1;
    }
    total
}
";

#[test]
fn a_fiber_suspends_in_called_functions_and_finishes() {
    agree(
        &format!(
            "{PRELUDE}
fn main() -> Unit ! {{io, alloc}} {{
    let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ count(4) }});
    let mut step = Fiber.start(&mut f);
    let mut done = false;
    while !done {{
        match step {{
            FiberStep.Performed(request) => {{
                print_i64(request);
                step = Fiber.resume(&mut f, request + 1);
            }},
            FiberStep.Finished(total) => {{
                print_i64(total);
                done = true;
            }},
        }}
    }}
    // A body that never performs finishes at its start.
    let mut quiet = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 7 }});
    match Fiber.start(&mut quiet) {{
        FiberStep.Performed(_) => print_i64(-1),
        FiberStep.Finished(value) => print_i64(value),
    }}
}}"
        ),
        "0\n10\n20\n30\n64\n7\n",
    );
}

#[test]
fn fibers_in_a_vector_run_in_turn() {
    agree(
        &format!(
            "{PRELUDE}
fn main() -> Unit ! {{io, alloc}} {{
    let mut fibers: Vec<Fiber<i64, i64, once fn() -> i64 ! {{}}>> = Vec.with_capacity(3);
    let mut n = 1;
    while n <= 3 {{
        let limit = n;
        fibers = Vec.push(fibers, Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ count(limit) * 100 + limit }}));
        n = n + 1;
    }}
    // Each step resumes one fiber; a finished one is not resumed again.
    let mut started = 0;
    while started < 3 {{
        match Fiber.start(&mut fibers[started]) {{
            FiberStep.Performed(request) => print_i64(request),
            FiberStep.Finished(value) => print_i64(value),
        }}
        started = started + 1;
    }}
    let mut live = 3;
    let mut done: Vec<Bool> = Vec.with_capacity(3);
    done = Vec.push(done, false);
    done = Vec.push(done, false);
    done = Vec.push(done, false);
    while live > 0 {{
        let mut i = 0;
        while i < 3 {{
            if !Vec.get(&done, i) {{
                match Fiber.resume(&mut fibers[i], i) {{
                    FiberStep.Performed(request) => print_i64(request),
                    FiberStep.Finished(value) => {{
                        print_i64(value);
                        done = Vec.set(done, i, true);
                        live = live - 1;
                    }},
                }}
            }}
            i = i + 1;
        }}
    }}
}}"
        ),
        "0\n0\n0\n1\n10\n10\n202\n20\n603\n",
    );
}

#[test]
fn a_panic_in_a_fiber_reaches_its_resumer() {
    let source = format!(
        "{PRELUDE}
fn boom(x: i64) -> i64 ! {{Emit}} {{
    let reply = perform Emit(x);
    reply / (reply - reply)
}}

fn main() -> Unit ! {{io, alloc, suspend}} {{
    let caught = Task.catch(fn() -> i64 ! {{io, alloc, suspend}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ boom(5) }});
        match Fiber.start(&mut f) {{
            FiberStep.Performed(request) => print_i64(request),
            FiberStep.Finished(_) => print_i64(-1),
        }}
        match Fiber.resume(&mut f, 1) {{
            FiberStep.Performed(_) => -2,
            FiberStep.Finished(value) => value,
        }}
    }});
    match caught {{
        Result.Ok(value) => print_i64(value),
        Result.Err(_) => print_i64(99),
    }}
}}"
    );
    agree(&source, "5\n99\n");
}

/// A fiber is started once, then resumed only while it is suspended;
/// anything else is a panic a catch stops.
#[test]
fn a_fiber_is_started_once_and_resumed_while_suspended() {
    let source = format!(
        "{PRELUDE}
fn show(caught: Result<i64, Panic>) -> Unit ! {{io}} {{
    match caught {{
        Result.Ok(value) => print_i64(value),
        Result.Err(_) => print_i64(-1),
    }}
}}

fn main() -> Unit ! {{io, alloc, suspend}} {{
    show(Task.catch(fn() -> i64 ! {{alloc}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 7 }});
        Fiber.start(&mut f);
        Fiber.start(&mut f);
        1
    }}));
    show(Task.catch(fn() -> i64 ! {{alloc}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 7 }});
        Fiber.start(&mut f);
        Fiber.resume(&mut f, 1);
        2
    }}));
    show(Task.catch(fn() -> i64 ! {{alloc}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ count(1) }});
        Fiber.resume(&mut f, 1);
        3
    }}));
    show(Task.catch(fn() -> i64 ! {{alloc}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 7 }});
        match Fiber.start(&mut f) {{
            FiberStep.Performed(_) => -2,
            FiberStep.Finished(value) => value,
        }}
    }}));
}}"
    );
    agree(&source, "-1\n-1\n-1\n7\n");
}

#[test]
fn a_fiber_may_yield_to_other_tasks() {
    agree(
        &format!(
            "{PRELUDE}
fn yielding() -> i64 ! {{Emit, suspend}} {{
    let first = perform Emit(1);
    let _ = Task.yield();
    first + perform Emit(2)
}}

fn main() -> Unit ! {{io, alloc, suspend}} {{
    Task.scope(fn() -> Unit ! {{io, alloc, suspend}} {{
        let other = Task.spawn(fn() -> i64 ! {{io}} {{ print_i64(500); 500 }});
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit, suspend}} {{ yielding() }});
        let mut step = Fiber.start(&mut f);
        let mut done = false;
        while !done {{
            match step {{
                FiberStep.Performed(request) => {{
                    print_i64(request);
                    step = Fiber.resume(&mut f, request * 10);
                }},
                FiberStep.Finished(value) => {{
                    print_i64(value);
                    done = true;
                }},
            }}
        }}
        let _ = Task.join(other);
    }})
}}"
        ),
        "1\n500\n2\n30\n",
    );
}

/// A fiber started in one task may be moved to another task of the same
/// thread and resumed there.
#[test]
fn a_fiber_moves_to_another_task() {
    agree(
        &format!(
            "{PRELUDE}
fn main() -> Unit ! {{io, alloc, suspend}} {{
    Task.scope(fn() -> Unit ! {{io, alloc, suspend}} {{
        let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ count(2) }});
        match Fiber.start(&mut f) {{
            FiberStep.Performed(request) => print_i64(request),
            FiberStep.Finished(_) => print_i64(-1),
        }}
        let child = Task.spawn(fn() -> i64 ! {{io}} {{
            let mut g = f;
            let mut result = -1;
            let mut step = Fiber.resume(&mut g, 5);
            let mut done = false;
            while !done {{
                match step {{
                    FiberStep.Performed(request) => {{
                        print_i64(request);
                        step = Fiber.resume(&mut g, 5);
                    }},
                    FiberStep.Finished(value) => {{
                        result = value;
                        done = true;
                    }},
                }}
            }}
            result + 1
        }});
        match Task.join(child) {{
            TaskExit.Completed(value) => print_i64(value),
            TaskExit.Cancelled => print_i64(-1),
        }}
    }})
}}"
        ),
        "0\n10\n11\n",
    );
}

/// Dropping a fiber that has not finished unwinds it natively: what its
/// frames own is freed. (The evaluator cannot unwind from a drop.)
#[test]
fn dropping_a_suspended_fiber_frees_what_it_holds() {
    let source = format!(
        "{PRELUDE}
fn holding() -> i64 ! {{Emit, alloc}} {{
    let held = Box.new(41);
    let reply = perform Emit(Box.read(&held));
    reply + Box.read(&held)
}}

fn fail(x: i64) -> i64 ! {{}} {{
    x / (x - x)
}}

fn main() -> Unit ! {{io, alloc, suspend}} {{
    let mut f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit, alloc}} {{ holding() }});
    match Fiber.start(&mut f) {{
        FiberStep.Performed(request) => print_i64(request),
        FiberStep.Finished(_) => print_i64(-1),
    }}
    // Never started: its closure is dropped.
    let _unused = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ count(2) }});
    print_i64(1);
    // Dropped while a panic unwinds past it: the panic still reaches the
    // catch.
    let caught = Task.catch(fn() -> i64 ! {{alloc}} {{
        let mut g = Fiber.new::<Emit>(fn() -> i64 ! {{Emit, alloc}} {{ holding() }});
        Fiber.start(&mut g);
        fail(3)
    }});
    match caught {{
        Result.Ok(_) => print_i64(-1),
        Result.Err(_) => print_i64(2),
    }}
}}"
    );
    for flags in native_builds() {
        let mut flags = flags.clone();
        flags.push("--stats");
        let built = run(&source, false, &flags);
        assert!(built.success, "{flags:?}: {}", built.stderr);
        assert_eq!(built.stdout, "41\n1\n2\n", "{flags:?}");
        // Only the division panics: discontinuing prints nothing.
        assert_eq!(
            built.stderr.matches("panic").count(),
            1,
            "{flags:?}: {}",
            built.stderr
        );
        let stats = built
            .stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap();
        let count = |name: &str| {
            stats
                .split_whitespace()
                .find_map(|part| part.strip_prefix(&format!("{name}=")))
                .unwrap()
                .to_string()
        };
        assert_eq!(count("allocations"), count("deallocations"), "{stats}");
    }
}

#[test]
fn fibers_are_checked() {
    rejected(
        &format!(
            "{PRELUDE} fn main() -> Unit ! {{alloc}} {{ let _f = Fiber.new(fn() -> i64 ! {{Emit}} {{ 1 }}); }}"
        ),
        "Fiber.new names the operation",
    );
    rejected(
        &format!(
            "{PRELUDE} effect Other: i64 -> i64;
            fn main() -> Unit ! {{alloc}} {{
                let _f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit, Other}} {{ perform Other(1) }});
            }}"
        ),
        "may perform only 'Emit'",
    );
    rejected(
        &format!(
            "{PRELUDE} fn main() -> Unit ! {{alloc}} {{
                let values: [i64; 2] = [1, 2];
                let view = &values[..];
                let _f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ Slice.len(view) }});
            }}"
        ),
        "cannot capture",
    );
    rejected(
        &format!(
            "{PRELUDE} fn run(f: &mut Fiber<i64, i64, once fn() -> i64 ! {{io}}>) -> Unit ! {{}} {{
                let _ = Fiber.start(f);
            }}
            fn main() -> Unit ! {{}} {{}}"
        ),
        "io",
    );
    rejected(
        &format!(
            "{PRELUDE} fn main() -> Unit ! {{}} {{ let _f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 1 }}); }}"
        ),
        "alloc",
    );
    rejected(
        &format!(
            "{PRELUDE} fn keep(f: Fiber<&[i64], i64, once fn() -> i64 ! {{}}>) -> Unit ! {{}} {{}}
            fn main() -> Unit ! {{}} {{}}"
        ),
        "cannot be Never or hold borrows",
    );
    // A fiber stays on the OS thread that made it.
    rejected(
        &format!(
            "{PRELUDE} fn main() -> Unit ! {{alloc}} {{
                let f = Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 1 }});
                Thread.scope(fn() -> Unit ! {{alloc}} {{
                    Thread.spawn(fn() -> Unit ! {{}} {{ let _g = f; }});
                }});
            }}"
        ),
        "a thread body cannot capture",
    );
    rejected(
        &format!(
            "{PRELUDE} fn main() -> Unit ! {{alloc}} {{
                Thread.scope(fn() -> Unit ! {{alloc}} {{
                    let t = Thread.spawn(fn() -> Fiber<i64, i64, once fn() -> i64 ! {{}}> ! {{alloc}} {{
                        Fiber.new::<Emit>(fn() -> i64 ! {{Emit}} {{ 1 }})
                    }});
                    let _f = Thread.join(t);
                }});
            }}"
        ),
        "a thread body cannot return",
    );
}
