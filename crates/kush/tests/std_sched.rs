//! `std.sched` (STD-SCHEDULER, docs/tasks-on-handlers.md): the task
//! scheduler written in Kush on fibers, through the evaluator and both
//! native backends.
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
    let mut builds = vec![vec!["--release"]];
    if clang_available() {
        builds.push(vec!["--release", "--backend", "llvm"]);
    }
    builds
}

/// The evaluator and every native build print `expected` and succeed;
/// native builds free everything they allocate.
fn agree(source: &str, expected: &str) {
    let evaluated = run(source, true, &[]);
    assert!(evaluated.success, "eval: {}\n{source}", evaluated.stderr);
    assert_eq!(evaluated.stdout, expected, "eval\n{source}");
    for flags in native_builds() {
        let mut flags = flags.clone();
        flags.push("--stats");
        let built = run(source, false, &flags);
        assert!(built.success, "{flags:?}: {}\n{source}", built.stderr);
        assert_eq!(built.stdout, expected, "{flags:?}\n{source}");
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
                .parse::<i64>()
                .unwrap()
        };
        assert_eq!(count("allocations"), count("deallocations"), "{stats}");
        // Joined tasks' slots are reused: what is live stays small.
        assert!(count("peak-live") < 64, "{stats}");
    }
}

const PRELUDE: &str = "
use std.sched;
use std.sched.Sched;
";

/// The example of docs/async.md and reference chapter 8, on `std.sched`:
/// the same interleaving as the built-in tasks.
#[test]
fn the_std_scheduler_interleaves_as_the_builtin_tasks() {
    agree(
        &format!(
            "{PRELUDE}
fn worker(id: i64) -> i64 ! {{io, Sched}} {{
    print_i64(id * 10 + 1);
    sched.yield_now();
    print_i64(id * 10 + 2);
    id
}}

fn main() -> Unit ! {{io, alloc}} {{
    let root = sched.run(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{
        let a = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{ worker(1) }}));
        let b = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{ worker(2) }}));
        print_i64(sched.join(a));
        print_i64(sched.join(b));
        40
    }}));
    print_i64(root);
}}"
        ),
        "11\n21\n12\n22\n1\n2\n40\n",
    );
}

/// Joins wake their waiter at the tail of the queue; a join of a finished
/// task returns at once; a joined task's slot is reused by later spawns.
#[test]
fn joins_wake_waiters_in_order_and_slots_are_reused() {
    agree(
        &format!(
            "{PRELUDE}
fn slow(id: i64, yields: i64) -> i64 ! {{io, Sched}} {{
    let mut i = 0;
    while i < yields {{
        sched.yield_now();
        i = i + 1;
    }}
    print_i64(id);
    id * 100
}}

fn main() -> Unit ! {{io, alloc}} {{
    let root = sched.run(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{
        // The joiner of a task that finishes later waits; the join of one
        // that already finished does not.
        let late = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{ slow(1, 3) }}));
        let early = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{ slow(2, 0) }}));
        let waiter = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{
            let value = sched.join(late);
            print_i64(value + 1);
            0
        }}));
        sched.yield_now();
        print_i64(sched.join(early));
        let _ = sched.join(waiter);
        // A thousand short tasks reuse a few slots.
        let mut sum = 0;
        let mut i = 0;
        while i < 1000 {{
            let task = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{
                sched.yield_now();
                3
            }}));
            sum = sum + sched.join(task);
            i = i + 1;
        }}
        sum
    }}));
    print_i64(root);
}}"
        ),
        "2\n200\n1\n101\n3000\n",
    );
}

/// A handle is joined once, by another task, while its task is current.
#[test]
fn a_bad_join_panics() {
    for join in ["sched.join(5)", "sched.join(0)"] {
        let source = format!(
            "{PRELUDE}
fn main() -> Unit ! {{io, alloc}} {{
    let root = sched.run(Fiber.new::<Sched>(fn() -> i64 ! {{Sched, io, alloc}} {{ {join} }}));
    print_i64(root);
}}"
        );
        let evaluated = run(&source, true, &[]);
        assert!(!evaluated.success, "{join}: {}", evaluated.stdout);
        assert!(evaluated.stdout.is_empty(), "{join}: {}", evaluated.stdout);
        for flags in native_builds() {
            let built = run(&source, false, &flags);
            assert!(!built.success, "{join} {flags:?}: {}", built.stdout);
            assert!(
                built.stderr.contains("panic"),
                "{flags:?}: {}",
                built.stderr
            );
        }
    }
}
