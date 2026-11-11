//! Running out of stack is a panic on every backend and on every stack,
//! never a bare SIGSEGV.
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::process::Command;

const DOWN: &str = "
fn down(n: i64, salt: &[i64]) -> i64 ! {panic} {
    if n == 0 { 0 } else { Slice.get(salt, n & 3) + down(n - 1, salt) }
}
fn salt() -> Vec<i64> ! {alloc, panic} {
    let mut values: Vec<i64> = Vec.with_capacity(4);
    values = Vec.push(values, 1);
    values = Vec.push(values, 2);
    values = Vec.push(values, 3);
    values = Vec.push(values, 4);
    values
}
fn depth() -> i64 ! {io, alloc, panic} {
    let bytes = match ENV.arg(1, Bytes.with_capacity(32)) { Ok(value) => value, Err(_) => { return 0; } };
    let mut n = 0;
    let mut i = 0;
    while i < Bytes.len(&bytes) {
        n = n * 10 + Int.convert::<i64>(Bytes.get(&bytes, i)) - 48;
        i = i + 1;
    }
    n
}
";

fn clang_available() -> bool {
    Command::new(std::env::var("KUSH_CLANG").unwrap_or_else(|_| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

/// Builds `source` in every configuration and runs it at a small and at an
/// absurd depth. The small run must print `shallow`; the deep one must
/// panic in every configuration: no backend turns a recursion into a loop.
fn check(source: &str, shallow: &str) {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    fs::write(root.join("main.kush"), source).unwrap();
    let mut configurations = vec![vec![], vec!["--release"]];
    if clang_available() {
        configurations.push(vec!["--backend", "llvm"]);
        configurations.push(vec!["--release", "--backend", "llvm"]);
    }
    for flags in &configurations {
        let built = Command::new(env!("CARGO_BIN_EXE_kush"))
            .current_dir(root)
            .args(["build", "main.kush", "-o", "program"])
            .args(flags)
            .env_remove("KUSH_BACKEND")
            .output()
            .unwrap();
        assert!(
            built.status.success(),
            "{flags:?}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let small = Command::new(root.join("program"))
            .arg("1000")
            .output()
            .unwrap();
        assert!(small.status.success(), "{flags:?}");
        assert_eq!(String::from_utf8_lossy(&small.stdout), shallow, "{flags:?}");
        let deep = Command::new(root.join("program"))
            .arg("400000000")
            .output()
            .unwrap();
        assert_eq!(
            deep.status.signal(),
            Some(6),
            "{flags:?}: {:?}",
            deep.status
        );
        assert!(
            String::from_utf8_lossy(&deep.stderr).contains("panic: stack exhausted"),
            "{flags:?}: {}",
            String::from_utf8_lossy(&deep.stderr)
        );
    }
}
#[test]
fn unbounded_recursion_on_the_process_stack_panics() {
    check(
        &format!(
            "enum Result<T, E> {{ Ok(T), Err(E) }}
            {DOWN}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let values = salt();
                print_int(down(depth(), &values[..]));
                0
            }}"
        ),
        "2500\n",
    );
}

#[test]
fn unbounded_recursion_on_a_task_stack_panics() {
    check(
        &format!(
            "enum Result<T, E> {{ Ok(T), Err(E) }}
            enum TaskExit<T> {{ Completed(T), Cancelled }}
            {DOWN}
            fn main() -> Unit ! {{io, alloc, panic, suspend}} {{
                let n = depth();
                Task.scope(fn() -> Unit ! {{io, alloc, panic, suspend}} {{
                    let task: Task<i64> = Task.spawn(fn() -> i64 ! {{io, alloc, panic, suspend}} {{
                        let values = salt();
                        down(n, &values[..])
                    }});
                    match Task.join(task) {{
                        TaskExit.Completed(v) => print_int(v),
                        TaskExit.Cancelled => print_int(-1),
                    }}
                }})
            }}"
        ),
        "2500\n",
    );
}

/// A tail call and an accumulating recursion are the shapes an optimizer
/// would run in constant stack.
#[test]
fn tail_recursion_is_not_turned_into_a_loop() {
    check(
        &format!(
            "enum Result<T, E> {{ Ok(T), Err(E) }}
            {DOWN}
            fn count(n: i64, acc: i64) -> i64 ! {{panic}} {{
                if n == 0 {{ acc }} else {{ count(n - 1, acc + 1) }}
            }}
            fn climb(n: i64) -> i64 ! {{panic}} {{
                if n == 0 {{ 0 }} else {{ 1 + climb(n - 1) }}
            }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let n = depth();
                print_int(count(n, 0) + climb(n));
                0
            }}"
        ),
        "2000\n",
    );
}
