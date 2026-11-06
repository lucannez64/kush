//! THREAD-SCOPE (user-approved 2026-11-06): `Thread.scope` / `Thread.spawn`
//! / `Thread.join` run children on real OS threads. Children receive moved
//! values and borrowed views; ownership keeps each loan until the child is
//! joined, so exclusive views reach one thread only (disjoint halves may go to
//! different threads). Thread bodies use only `{io, alloc, panic}`. The
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
fn part(v: &[i64], from: i64, to: i64) -> i64 ! {panic} {
    let mut i = from;
    let mut acc = 0;
    while i < to { acc = acc + Slice.get(v, i); i = i + 1; }
    acc
}
fn fill(v: &mut [i64], base: i64) -> Unit ! {panic} {
    let mut i = 0;
    while i < Slice.len(v) { Slice.set(v, i, base + i); i = i + 1; }
}
fn label(n: i64) -> Bytes ! {alloc, panic} {
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
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut v: Vec<i64> = Vec.with_capacity(1000);
                let mut i = 0;
                while i < 1000 {{ v = Vec.push(v, i); i = i + 1; }}
                let view: &[i64] = &v[..];
                let sum = Thread.scope(fn() -> i64 ! {{io, alloc, panic}} {{
                    let a = Thread.spawn(fn() -> i64 ! {{panic}} {{ part(view, 0, 250) }});
                    let b = Thread.spawn(fn() -> i64 ! {{panic}} {{ part(view, 250, 500) }});
                    let c = Thread.spawn(fn() -> i64 ! {{panic}} {{ part(view, 500, 750) }});
                    let d = Thread.spawn(fn() -> i64 ! {{panic}} {{ part(view, 750, 1000) }});
                    let e = Thread.spawn(fn() -> Bytes ! {{alloc, panic}} {{ label(2) }});
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
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut data: [i64; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
                let whole: &mut [i64] = &mut data[..];
                Thread.scope(fn() -> Unit ! {{alloc, panic}} {{
                    let (left, right) = Slice.split_at_mut(whole, 4);
                    Thread.spawn(fn() -> Unit ! {{panic}} {{ fill(left, 100); }});
                    Thread.spawn(fn() -> Unit ! {{panic}} {{ fill(right, 200); }});
                }});
                // Unjoined threads are joined by the scope, and their owned
                // results dropped.
                Thread.scope(fn() -> Unit ! {{alloc, panic}} {{
                    Thread.spawn(fn() -> Bytes ! {{alloc, panic}} {{ label(1) }});
                    Thread.spawn(fn() -> Bytes ! {{alloc, panic}} {{ label(3) }});
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
         fn inner(x: i64) -> i64 ! {alloc, panic} {
             Thread.scope(fn() -> i64 ! {alloc, panic} {
                 let a = Thread.spawn(fn() -> i64 ! {panic} { x * 2 });
                 let b = Thread.spawn(fn() -> i64 ! {panic} { x * 3 });
                 Thread.join(a) + Thread.join(b)
             })
         }
         fn asks(x: i64) -> i64 ! {Ask, panic} { perform Ask(x) + 1 }
         fn main() -> i64 ! {alloc, panic} {
             Thread.scope(fn() -> i64 ! {alloc, panic} {
                 let a = Thread.spawn(fn() -> i64 ! {alloc, panic} { inner(2) });
                 // A declared operation handled inside the thread body.
                 let b = Thread.spawn(fn() -> i64 ! {panic} {
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
            "Task.scope(fn() -> i64 ! {alloc, panic, suspend} { let t = Thread.spawn(fn() -> i64 ! {} { 1 }); 0 })",
            "Thread.spawn requires an enclosing Thread.scope",
        ),
        // Thread bodies cannot suspend or leave declared operations unhandled.
        (
            "Thread.scope(fn() -> i64 ! {alloc, panic} { let t = Thread.spawn(fn() -> i64 ! {suspend} { 1 }); Thread.join(t) })",
            "only have the effects",
        ),
        (
            "Thread.scope(fn() -> i64 ! {alloc, panic} { let t = Thread.spawn(fn() -> i64 ! {Ask, panic} { perform Ask(1) }); Thread.join(t) })",
            "only have the effects",
        ),
        // Handles of the other kind.
        (
            "Thread.scope(fn() -> i64 ! {alloc, panic, suspend} { let t = Thread.spawn(fn() -> i64 ! {} { 1 }); match Task.join(t) { _ => 0 } })",
            "Task.join expects Task<T>",
        ),
        (
            "Task.scope(fn() -> i64 ! {alloc, panic, suspend} { let t = Task.spawn(fn() -> i64 ! {suspend} { 1 }); Thread.join(t) })",
            "Thread.join expects Thread<T>",
        ),
        // A thread handle cannot escape its scope.
        (
            "let t = Thread.scope(fn() -> Thread<i64> ! {alloc, panic} { Thread.spawn(fn() -> i64 ! {} { 1 }) }); 0",
            "must not escape",
        ),
    ] {
        rejects(
            &format!(
                "use std.task.TaskExit; {prelude} fn main() -> i64 ! {{alloc, panic, suspend}} {{ {body} }}"
            ),
            fragment,
        );
    }
    // Data races are ownership errors: the parent cannot write what a running
    // thread borrows, and one exclusive view cannot go to two threads.
    rejects(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{alloc, panic}} {{
                let mut data: [i64; 4] = [1, 2, 3, 4];
                let view: &[i64] = &data[..];
                Thread.scope(fn() -> i64 ! {{alloc, panic}} {{
                    let t = Thread.spawn(fn() -> i64 ! {{panic}} {{ part(view, 0, 4) }});
                    data[0] = 9;
                    Thread.join(t)
                }})
            }}"
        ),
        "assignment requires",
    );
    rejects(
        &format!(
            "{HELPERS}
            fn main() -> i64 ! {{alloc, panic}} {{
                let mut data: [i64; 4] = [1, 2, 3, 4];
                let whole: &mut [i64] = &mut data[..];
                Thread.scope(fn() -> Unit ! {{alloc, panic}} {{
                    Thread.spawn(fn() -> Unit ! {{panic}} {{ fill(whole, 1); }});
                    Thread.spawn(fn() -> Unit ! {{panic}} {{ fill(whole, 2); }});
                }});
                0
            }}"
        ),
        "lent to a spawned task",
    );
    // Values whose allocator or environment another thread could reach.
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
             let n = Box.new(1);
             let f = fn() -> i64 ! {} { Box.take(n) };
             Thread.scope(fn() -> i64 ! {alloc, panic} {
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
         fn check(x: i64) -> i64 ! {Fail, panic} { if x > 1000 { perform Fail(x) } else { x } }
         fn run(seed: i64) -> i64 ! {alloc, panic} {
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
         fn main() -> i64 ! {io, alloc, panic} {
             let expected = (run(3) + run(7) + run(11)) % 256;
             let got = Thread.scope(fn() -> i64 ! {alloc, panic} {
                 let a = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(3) });
                 let b = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(7) });
                 let c = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(11) });
                 (Thread.join(a) + Thread.join(b) + Thread.join(c)) % 256
             });
             if got == expected { 7 } else { 1 }
         }",
        7,
        "",
    );
}
