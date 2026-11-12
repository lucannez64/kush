//! Effectful, stateful handlers for declared operations: an operation may
//! declare the built-in effects its handlers have (`effect Op: P -> R ! {io}`,
//! required by every perform), and a handler whose captures are all copyable
//! (references, by-reference scalars, plain values) serves every perform,
//! including performs in called functions. Closures may capture references as
//! scoped borrows. Programs run on the evaluator and natively with balanced
//! allocations.

use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("stateful-handlers-test");
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
fn a_declared_operation_names_its_handler_effects() {
    agrees(
        r#"
        effect Show: i64 -> i64 ! {io, panic};
        fn core() -> i64 ! {Show, io, panic} { perform Show(1) + perform Show(2) }
        fn main() -> i64 ! {io, alloc, panic} {
            handle Show: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} { print_i64(x); resume(x * 10) } {
                core()
            }
        }"#,
        30,
        "1\n2\n",
    );
    // A perform requires the declared effects in its own row.
    rejects(
        r#"
        effect Show: i64 -> i64 ! {io};
        fn core() -> i64 ! {Show, panic} { perform Show(1) }
        fn main() -> i64 ! {panic} { 0 }"#,
        "requires effects {io}",
    );
    // A handler may not have more than the declared effects.
    rejects(
        r#"
        effect Show: i64 -> i64 ! {panic};
        fn core() -> i64 ! {Show, panic} { perform Show(1) }
        fn main() -> i64 ! {io, alloc, panic} {
            handle Show: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} { print_i64(x); resume(x) } {
                core()
            }
        }"#,
        "not among the operation's declared effects",
    );
    // Only built-in effects can be declared.
    rejects(
        r#"
        effect Other: i64 -> i64;
        effect Show: i64 -> i64 ! {Other};
        fn main() -> i64 ! {panic} { 0 }"#,
        "built-in effects",
    );
}

#[test]
fn a_capturing_handler_with_copyable_captures_serves_every_perform() {
    agrees(
        r#"
        effect Tick: i64 -> i64 ! {io, panic};
        struct Pad { keys: i64, frames: i64 }
        fn step(x: i64) -> i64 ! {Tick, io, panic} { perform Tick(x) }
        fn core() -> i64 ! {Tick, io, panic} {
            let mut sum = 0;
            let mut i = 1;
            while i <= 3 { sum = sum + step(i); i = i + 1; }
            sum
        }
        fn run(pad: &mut Pad, label: &Bytes) -> i64 ! {io, alloc, panic} {
            let mut seen = 0;
            let r = handle Tick: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} {
                pad.frames = pad.frames + 1;
                seen = seen + x;
                print_i64(Bytes.len(label) * 100 + pad.frames);
                resume(x + pad.keys)
            } { core() };
            r + seen * 1000
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut pad = Pad { keys: 10, frames: 0 };
            let label = Bytes.from("ab");
            let r = run(&mut pad, &label);
            print_i64(pad.frames);
            print_i64(r);
            0
        }"#,
        0,
        "201\n202\n203\n3\n6036\n",
    );
}

#[test]
fn handler_state_stays_borrowed_while_the_body_runs() {
    rejects(
        r#"
        effect Tick: i64 -> i64;
        fn core() -> i64 ! {Tick, panic} { perform Tick(1) }
        fn main() -> i64 ! {alloc, panic} {
            let mut count = 0;
            handle Tick: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { count = count + x; resume(x) } {
                count = 5;
                core()
            }
        }"#,
        "",
    );
    // A handler that owns a box is consumed by its first perform.
    let program = check(
        r#"
        effect Op: i64 -> i64;
        fn a() -> i64 ! {Op, panic} { perform Op(1) }
        fn main() -> i64 ! {alloc, panic} {
            let n = Box.new(10);
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(Box.take(n)) } {
                a() + a()
            }
        }"#,
    )
    .unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("no dynamically active handler"));
}

#[test]
fn captured_references_are_scoped_borrows() {
    rejects(
        r#"
        struct Pad { keys: i64 }
        fn f(pad: &mut Pad) -> i64 ! {alloc, panic} {
            let k = fn(x: i64) -> i64 ! {panic} { pad.keys = pad.keys + x; pad.keys };
            pad.keys = 7;
            k(1)
        }
        fn main() -> i64 ! {} { 0 }"#,
        "cannot write through a reference",
    );
    rejects(
        r#"
        struct Pad { keys: i64 }
        fn f(pad: &Pad) -> once fn(i64) -> i64 ! {panic} ! {alloc, panic} {
            fn(x: i64) -> i64 ! {panic} { pad.keys + x }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "must be called immediately or bound directly to a local",
    );
    rejects(
        r#"
        struct Pad { v: Vec<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let p = Pad { v: Vec.new() };
            let r = &p;
            let k = fn(x: i64) -> i64 ! {panic} { Vec.len(&r.v) + x };
            let q = p;
            k(1)
        }"#,
        "cannot move an owner while it is borrowed",
    );
    agrees(
        r#"
        struct Pad { keys: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Pad { keys: 1 };
            let r = &mut p;
            let k = fn(x: i64) -> i64 ! {} { r.keys = x; x };
            let a = k(5);
            p.keys + a
        }"#,
        10,
        "",
    );
}
