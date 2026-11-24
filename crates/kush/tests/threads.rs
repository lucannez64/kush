//! THREAD-SCOPE (user-approved 2026-11-06): `Thread.scope` / `Thread.spawn`
//! / `Thread.join` run children on real OS threads. Children receive moved
//! values and borrowed views; ownership keeps each loan until the child is
//! joined, so exclusive views reach one thread only (disjoint halves may go to
//! different threads). Thread bodies use only `{io, alloc, panic, suspend}`;
//! each thread runs its own task scheduler (THREAD-TASKS). The
//! reference evaluator runs threads as cooperative tasks (one valid schedule);
//! without shared mutable state both backends agree.
use kush::executable::check;

fn agrees(source: &str, expected: i64, stdout: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (value, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(value, expected, "{source}");
    assert_eq!(String::from_utf8_lossy(&output), stdout, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "cleanup: {source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    for release in [false, true] {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("threads");
        let options = if release {
            kush::native::CodegenOptions::release()
        } else {
            kush::native::CodegenOptions::default()
        };
        kush::native::build_with_codegen(
            &program,
            &binary,
            true,
            &kush::native::LinkSpec::default(),
            options,
        )
        .unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
        let stderr = String::from_utf8_lossy(&native.stderr);
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats:"))
            .expect("stats line");
        let count = |key: &str| -> u64 {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix(key))
                .and_then(|value| value.parse().ok())
                .unwrap()
        };
        assert_eq!(count("allocations="), count("deallocations="), "{line}");
    }
}

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

const HELPERS: &str = "
fn part(v: &[i64], from: i64, to: i64) -> i64 ! {} {
    let mut i = from;
    let mut acc = 0;
    while i < to { acc = acc + Slice.get(v, i); i = i + 1; }
    acc
}
fn fill(v: &mut [i64], base: i64) -> Unit ! {} {
    let mut i = 0;
    while i < Slice.len(v) { Slice.set(v, i, base + i); i = i + 1; }
}
fn label(n: i64) -> Bytes ! {alloc} {
    let mut b = Bytes.with_capacity(8);
    b = Bytes.push(b, 65 + n);
    b
}
";

#[test]
fn threads_share_views_and_return_owned_values() {
    agrees(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{io, alloc}} {{
                let mut v: Vec<i64> = Vec.with_capacity(1000);
                let mut i = 0;
                while i < 1000 {{ v = Vec.push(v, i); i = i + 1; }}
                let view: &[i64] = &v[..];
                let sum = Thread.scope(fn() -> i64 ! {{io, alloc}} {{
                    let a = Thread.spawn(fn() -> i64 ! {{}} {{ part(view, 0, 250) }});
                    let b = Thread.spawn(fn() -> i64 ! {{}} {{ part(view, 250, 500) }});
                    let c = Thread.spawn(fn() -> i64 ! {{}} {{ part(view, 500, 750) }});
                    let d = Thread.spawn(fn() -> i64 ! {{}} {{ part(view, 750, 1000) }});
                    let e = Thread.spawn(fn() -> Bytes ! {{alloc}} {{ label(2) }});
                    let name = Thread.join(e);
                    print_i64(Bytes.get(&name, 0));
                    drop(name);
                    Thread.join(a) + Thread.join(b) + Thread.join(c) + Thread.join(d)
                }});
                print_i64(sum);
                drop(v);
                0
            }}"
        ),
        0,
        "67\n499500\n",
    );
}

#[test]
fn disjoint_exclusive_halves_and_unjoined_threads() {
    agrees(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{io, alloc}} {{
                let mut data: [i64; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
                let whole: &mut [i64] = &mut data[..];
                Thread.scope(fn() -> Unit ! {{alloc}} {{
                    let (left, right) = Slice.split_at_mut(whole, 4);
                    Thread.spawn(fn() -> Unit ! {{}} {{ fill(left, 100); }});
                    Thread.spawn(fn() -> Unit ! {{}} {{ fill(right, 200); }});
                }});
                // Unjoined threads are joined by the scope, and their owned
                // results dropped.
                Thread.scope(fn() -> Unit ! {{alloc}} {{
                    Thread.spawn(fn() -> Bytes ! {{alloc}} {{ label(1) }});
                    Thread.spawn(fn() -> Bytes ! {{alloc}} {{ label(3) }});
                }});
                data[0] + data[3] + data[4] + data[7]
            }}"
        ),
        606,
        "",
    );
}

#[test]
fn nested_scopes_inside_threads_and_handled_effects() {
    agrees(
        "effect Ask: i64 -> i64;
         fn inner(x: i64) -> i64 ! {alloc} {
             Thread.scope(fn() -> i64 ! {alloc} {
                 let a = Thread.spawn(fn() -> i64 ! {} { x * 2 });
                 let b = Thread.spawn(fn() -> i64 ! {} { x * 3 });
                 Thread.join(a) + Thread.join(b)
             })
         }
         fn asks(x: i64) -> i64 ! {Ask} { perform Ask(x) + 1 }
         fn main() -> i64 ! {alloc} {
             Thread.scope(fn() -> i64 ! {alloc} {
                 let a = Thread.spawn(fn() -> i64 ! {alloc} { inner(2) });
                 // A declared operation handled inside the thread body.
                 let b = Thread.spawn(fn() -> i64 ! {} {
                     handle Ask: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y ^ 8) } { asks(1) }
                 });
                 Thread.join(a) + Thread.join(b)
             })
         }",
        10 + 10,
        "",
    );
}

#[test]
fn thread_rules_are_checked() {
    let prelude = "effect Ask: i64 -> i64;";
    for (body, fragment) in [
        // Thread.spawn needs its own scope kind.
        (
            "Thread.spawn(fn() -> i64 ! {} { 1 }); 0",
            "requires an enclosing Task.scope",
        ),
        (
            "Task.scope(fn() -> i64 ! {alloc, suspend} { let t = Thread.spawn(fn() -> i64 ! {} { 1 }); 0 })",
            "Thread.spawn requires an enclosing Thread.scope",
        ),
        // Thread bodies cannot leave declared operations unhandled.
        (
            "Thread.scope(fn() -> i64 ! {alloc} { let t = Thread.spawn(fn() -> i64 ! {Ask} { perform Ask(1) }); Thread.join(t) })",
            "only have the effects",
        ),
        // Handles of the other kind.
        (
            "Thread.scope(fn() -> i64 ! {alloc, suspend} { let t = Thread.spawn(fn() -> i64 ! {} { 1 }); match Task.join(t) { _ => 0 } })",
            "Task.join expects Task<T>",
        ),
        (
            "Task.scope(fn() -> i64 ! {alloc, suspend} { let t = Task.spawn(fn() -> i64 ! {suspend} { 1 }); Thread.join(t) })",
            "Thread.join expects Thread<T>",
        ),
        // A thread handle cannot escape its scope.
        (
            "let t = Thread.scope(fn() -> Thread<i64> ! {alloc} { Thread.spawn(fn() -> i64 ! {} { 1 }) }); 0",
            "must not escape",
        ),
    ] {
        rejects(
            &format!(
                "use std.task.TaskExit; {prelude} fn main() -> i64 ! {{alloc, suspend}} {{ {body} }}"
            ),
            fragment,
        );
    }
    // Data races are ownership errors: the parent cannot write what a running
    // thread borrows, and one exclusive view cannot go to two threads.
    rejects(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{alloc}} {{
                let mut data: [i64; 4] = [1, 2, 3, 4];
                let view: &[i64] = &data[..];
                Thread.scope(fn() -> i64 ! {{alloc}} {{
                    let t = Thread.spawn(fn() -> i64 ! {{}} {{ part(view, 0, 4) }});
                    data[0] = 9;
                    Thread.join(t)
                }})
            }}"
        ),
        // Index assignment writes through an exclusive view, which the
        // captured (immutable) `data` cannot give.
        "exclusive '&mut [T]' view of an immutable binding",
    );
    rejects(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{alloc}} {{
                let mut data: [i64; 4] = [1, 2, 3, 4];
                let whole: &mut [i64] = &mut data[..];
                Thread.scope(fn() -> Unit ! {{alloc}} {{
                    Thread.spawn(fn() -> Unit ! {{}} {{ fill(whole, 1); }});
                    Thread.spawn(fn() -> Unit ! {{}} {{ fill(whole, 2); }});
                }});
                0
            }}"
        ),
        "lent to a spawned task",
    );
    // Values whose allocator or environment another thread could reach.
    rejects(
        "fn main() -> i64 ! {alloc} {
             let n = Box.new(1);
             let f = fn() -> i64 ! {} { Box.take(n) };
             Thread.scope(fn() -> i64 ! {alloc} {
                 let t = Thread.spawn(fn() -> i64 ! {} { f() });
                 Thread.join(t)
             })
         }",
        "cannot capture",
    );
}

/// Each thread has its own abort word: aborts handled inside concurrent
/// threads do not see each other.
#[test]
fn aborts_inside_threads_are_per_thread() {
    agrees(
        "effect Fail: i64 -> Never;
         fn check(x: i64) -> i64 ! {Fail} { if x > 1000 { perform Fail(x) } else { x } }
         fn run(seed: i64) -> i64 ! {alloc} {
             let mut acc = 0;
             let mut i = 0;
             while i < 20000 {
                 let keep = Box.new(i);
                 let r = handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {} { 0 - 1 } {
                     check((i * seed) % 2000)
                 };
                 acc = (acc + r + Box.take(keep)) % 1000003;
                 i = i + 1;
             }
             acc
         }
         fn main() -> i64 ! {io, alloc} {
             let expected = (run(3) + run(7) + run(11)) % 256;
             let got = Thread.scope(fn() -> i64 ! {alloc} {
                 let a = Thread.spawn(fn() -> i64 ! {alloc} { run(3) });
                 let b = Thread.spawn(fn() -> i64 ! {alloc} { run(7) });
                 let c = Thread.spawn(fn() -> i64 ! {alloc} { run(11) });
                 (Thread.join(a) + Thread.join(b) + Thread.join(c)) % 256
             });
             if got == expected { 7 } else { 1 }
         }",
        7,
        "",
    );
}

/// THREAD-ATOMICS (user-approved): `Atomic` cells live in arrays or vectors
/// and are shared through views; `Atomic.load/store/fetch_add/swap/
/// compare_exchange(view, index, ..)` are sequentially consistent. An
/// `Atomic` is never copied, so it is never read with a plain load.
const COUNTER: &str = "
fn bump(c: &[Atomic], n: i64) -> Unit ! {} {
    let mut i = 0;
    while i < n { Atomic.fetch_add(c, 0, 1); Atomic.fetch_add(c, 1, i); i = i + 1; }
}
fn run(n: i64) -> i64 ! {io, alloc} {
    let mut cells: Vec<Atomic> = Vec.with_capacity(2);
    cells = Vec.push(cells, Atomic.new(0));
    cells = Vec.push(cells, Atomic.new(0));
    let c: &[Atomic] = &cells[..];
    Thread.scope(fn() -> Unit ! {alloc} {
        Thread.spawn(fn() -> Unit ! {} { bump(c, n); });
        Thread.spawn(fn() -> Unit ! {} { bump(c, n); });
        Thread.spawn(fn() -> Unit ! {} { bump(c, n); });
        Thread.spawn(fn() -> Unit ! {} { bump(c, n); });
    });
    print_i64(Atomic.load(c, 0));
    print_i64(Atomic.load(c, 1));
    print_i64(Atomic.swap(c, 0, 5));
    print_i64(if Atomic.compare_exchange(c, 0, 5, 9) { 1 } else { 0 });
    print_i64(if Atomic.compare_exchange(c, 0, 5, 11) { 1 } else { 0 });
    Atomic.store(c, 1, 3);
    let both = Atomic.load(c, 0) + Atomic.load(c, 1);
    drop(cells);
    both
}
";

#[test]
fn atomics_count_across_threads() {
    agrees(
        &format!("{COUNTER} fn main() -> i64 ! {{io, alloc}} {{ run(500) }}"),
        12,
        &format!("2000\n{}\n2000\n1\n0\n", 4 * (499 * 500 / 2)),
    );
    // Natively with real contention: no update is lost.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(&format!(
            "{COUNTER} fn main() -> i64 ! {{io, alloc}} {{ run(200000) }}"
        ))
        .unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("atomics");
        kush::native::build_with_codegen(
            &program,
            &binary,
            false,
            &kush::native::LinkSpec::default(),
            kush::native::CodegenOptions::release(),
        )
        .unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            format!("800000\n{}\n800000\n1\n0\n", 4 * (199_999i64 * 200_000 / 2))
        );
    }
}

#[test]
fn atomics_are_never_copied() {
    for (body, fragment) in [
        (
            "let cells: [Atomic; 1] = [Atomic.new(1)]; let c: &[Atomic] = &cells[..]; Slice.get(c, 0); 0",
            "copies the element",
        ),
        (
            "let mut v: Vec<Atomic> = Vec.new(); v = Vec.push(v, Atomic.new(1)); let x = Vec.get(&v, 0); 0",
            "copies the element",
        ),
        (
            "let cells: [Atomic; 1] = [Atomic.new(1)]; let x = cells[0]; 0",
            "cannot copy",
        ),
        (
            "let a = Atomic.new(1); let b = a; Atomic.value(a)",
            "use after move",
        ),
        (
            "let v: [i64; 1] = [1]; let s: &[i64] = &v[..]; Atomic.load(s, 0)",
            "view of atomics",
        ),
    ] {
        rejects(
            &format!("fn main() -> i64 ! {{alloc}} {{ {body} }}"),
            fragment,
        );
    }
    // A record holding an atomic is consumed or dropped normally.
    agrees(
        "struct Stats { hits: Atomic, name: Bytes }
         fn make() -> Stats ! {alloc} { Stats { hits: Atomic.new(3), name: Bytes.from(\"x\") } }
         fn main() -> i64 ! {alloc} {
             let s = make();
             let t = make();
             drop(t);
             let Stats { hits, name } = s;
             drop(name);
             Atomic.value(hits)
         }",
        3,
        "",
    );
}

/// THREAD-CHANNELS (user-approved; plain-data messages in this version):
/// `Channel<T>` lives in a vector or array and is shared through views.
/// `send` waits while full, `recv` waits while empty and gives `None` once
/// the channel is closed and drained.
const PIPELINE: &str = "
use std.option.Option;
struct Item { id: i64, square: i64 }
fn produce(c: &[Channel<Item>], from: i64, to: i64) -> Unit ! {} {
    let mut i = from;
    while i <= to { Channel.send(c, 0, Item { id: i, square: i * i }); i = i + 1; }
}
fn consume(c: &[Channel<Item>]) -> i64 ! {} {
    let mut acc = 0;
    let mut count = 0;
    loop {
        match Channel.recv(c, 0) {
            Option.Some(item) => { acc = acc + item.square - item.id; count = count + 1; },
            Option.None => { break; },
        }
    }
    acc * 1000 + count
}
";

#[test]
fn channels_carry_messages_between_threads() {
    let expected = (1..=120i64).map(|i| i * i - i).sum::<i64>() * 1000 + 120;
    agrees(
        &format!(
            "{PIPELINE}
            fn main() -> i64 ! {{io, alloc}} {{
                let mut chans: Vec<Channel<Item>> = Vec.with_capacity(1);
                chans = Vec.push(chans, Channel.new(4));
                let c: &[Channel<Item>] = &chans[..];
                let got = Thread.scope(fn() -> i64 ! {{alloc}} {{
                    let consumer = Thread.spawn(fn() -> i64 ! {{}} {{ consume(c) }});
                    // Two producers; the channel closes once both are joined.
                    let a = Thread.spawn(fn() -> Unit ! {{}} {{ produce(c, 1, 60); }});
                    let b = Thread.spawn(fn() -> Unit ! {{}} {{ produce(c, 61, 120); }});
                    Thread.join(a);
                    Thread.join(b);
                    Channel.close(c, 0);
                    Thread.join(consumer)
                }});
                print_i64(got);
                drop(chans);
                0
            }}"
        ),
        0,
        &format!("{expected}\n"),
    );
}

#[test]
fn channel_rules() {
    // Sending on a closed channel panics in both backends.
    let source = format!(
        "{PIPELINE}
        fn main() -> i64 ! {{io, alloc}} {{
            let mut chans: Vec<Channel<Item>> = Vec.with_capacity(1);
            chans = Vec.push(chans, Channel.new(2));
            let c: &[Channel<Item>] = &chans[..];
            Channel.close(c, 0);
            produce(c, 1, 1);
            drop(chans);
            0
        }}"
    );
    let program = check(&source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("closed channel"), "{error:?}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("closed");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert!(!native.status.success());
    }
    for (source, fragment) in [
        (
            "fn main() -> i64 ! {alloc} { let v: Vec<Channel<Bytes>> = Vec.new(); 0 }",
            "plain data",
        ),
        (
            "fn main() -> i64 ! {alloc} { let mut v: Vec<Channel<i64>> = Vec.new(); v = Vec.push(v, Channel.new(0)); drop(v); 0 }",
            "",
        ),
        (
            "fn main() -> i64 ! {alloc} { let c = Channel.new(2); 0 }",
            "needs its message type",
        ),
        (
            "fn main() -> i64 ! {alloc} { let mut v: Vec<Channel<i64>> = Vec.new(); v = Vec.push(v, Channel.new(2)); let c: &[Channel<i64>] = &v[..]; let x = Slice.get(c, 0); 0 }",
            "copies the element",
        ),
        (
            "fn main() -> i64 ! {alloc} { let mut v: Vec<Channel<i64>> = Vec.new(); v = Vec.push(v, Channel.new(2)); let c: &[Channel<i64>] = &v[..]; match Channel.recv(c, 0) { _ => 0 } }",
            "Option",
        ),
    ] {
        match check(source) {
            Err(error) => assert!(error.message.contains(fragment), "{fragment}: {error:?}"),
            // A zero capacity is a run-time panic.
            Ok(program) if fragment.is_empty() => {
                let error = program.evaluate(&mut Vec::new()).unwrap_err();
                assert!(error.message.contains("capacity"), "{error:?}");
            }
            Ok(_) => panic!("accepted: {source}"),
        }
    }
}

/// THREAD-TASKS: each OS thread runs its own cooperative scheduler, so a
/// thread body may run `Task.scope`, yield, cancel its own tasks and wait for
/// a timer on its own reactor, while `main` does the same on its scheduler.
const TASKS_IN_THREADS: &str = "
use std.result.Result;
use std.task.TaskExit;
use std.time;

fn steps(seed: i64) -> i64 ! {alloc, suspend} {
    let held = Box.new(seed);
    let mut acc = 0;
    let mut i = 0;
    while i < 50 { acc = (acc + i * seed) % 1000003; let _ = Task.yield(); i = i + 1; }
    acc + Box.take(held)
}

fn worker(seed: i64) -> i64 ! {io, alloc, suspend} {
    Task.scope(fn() -> i64 ! {io, alloc, suspend} {
        let a = Task.spawn(fn() -> i64 ! {alloc, suspend} { steps(seed) });
        let b = Task.spawn(fn() -> i64 ! {alloc, suspend} { steps(seed + 1) });
        let sleeper = Task.spawn(fn() -> i64 ! {io, alloc, suspend} {
            match time.wait_ms(2) { Result.Ok(_) => 5, Result.Err(_) => 0 }
        });
        let spinner = Task.spawn(fn() -> i64 ! {alloc, suspend} {
            let mut n = 0;
            while !Task.yield() { n = n + 1; }
            0
        });
        let mut i = 0;
        while i < 3 { let _ = Task.yield(); i = i + 1; }
        Task.cancel(&spinner);
        let stopped = match Task.join(spinner) { TaskExit.Completed(_) => 0, TaskExit.Cancelled => 1 };
        let x = match Task.join(a) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 };
        let y = match Task.join(b) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 };
        let z = match Task.join(sleeper) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 };
        (x + y + z + stopped) % 1000003
    })
}
";

#[test]
fn threads_run_their_own_task_schedulers() {
    agrees(
        &format!(
            "{TASKS_IN_THREADS}
            fn main() -> i64 ! {{io, alloc, suspend}} {{
                let expected = (worker(3) + worker(7) + worker(11) + worker(13)) % 256;
                let got = Thread.scope(fn() -> i64 ! {{io, alloc, suspend}} {{
                    let a = Thread.spawn(fn() -> i64 ! {{io, alloc, suspend}} {{ worker(3) }});
                    let b = Thread.spawn(fn() -> i64 ! {{io, alloc, suspend}} {{ worker(7) }});
                    let c = Thread.spawn(fn() -> i64 ! {{io, alloc, suspend}} {{
                        // The thread's root yields and waits too.
                        let _ = Task.yield();
                        match time.wait_ms(1) {{ Result.Ok(_) => worker(11), Result.Err(_) => 0 }}
                    }});
                    // Meanwhile main runs tasks on its own scheduler.
                    let d = worker(13);
                    (Thread.join(a) + Thread.join(b) + Thread.join(c) + d) % 256
                }});
                if got == expected {{ 7 }} else {{ 1 }}
            }}"
        ),
        7,
        "",
    );
}

#[test]
fn cancelling_a_task_does_not_reach_its_threads() {
    // A thread is never cancelled: cancelling the task that started it stops
    // at the thread, in the evaluator as natively.
    agrees(
        "use std.task.TaskExit;
         fn main() -> i64 ! {io, alloc, suspend} {
             Task.scope(fn() -> Unit ! {io, alloc, suspend} {
                 let t = Task.spawn(fn() -> i64 ! {io, alloc, suspend} {
                     let seen = Thread.scope(fn() -> i64 ! {alloc} {
                         let w = Thread.spawn(fn() -> i64 ! {alloc, suspend} {
                             let mut i = 0;
                             while i < 100 { let _ = Task.yield(); i = i + 1; }
                             if Task.check_cancel() { 1 } else { 0 }
                         });
                         Thread.join(w)
                     });
                     print_i64(seen);
                     seen
                 });
                 let mut i = 0;
                 while i < 5 { let _ = Task.yield(); i = i + 1; }
                 Task.cancel(&t);
                 let _ = Task.join(t);
             });
             0
         }",
        0,
        "0\n",
    );
}
