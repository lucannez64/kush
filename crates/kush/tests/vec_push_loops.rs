//! A loop that appends to a vector keeps the vector's length and capacity
//! in variables when optimizing. Every shape here must print the same in an
//! unoptimized build (which reloads both at each push) and in the optimized
//! ones.
use std::fs;
use std::process::Command;

fn clang_available() -> bool {
    Command::new(std::env::var("KUSH_CLANG").unwrap_or_else(|_| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

/// `shadowed` is how many loops must report keeping a vector in variables
/// in the LLVM release build (a loop over a slice is lowered twice and
/// reports twice; none of these is).
fn agree(source: &str, shadowed: usize) -> String {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    fs::write(root.join("main.kush"), source).unwrap();
    let mut configurations = vec![vec![], vec!["--release"]];
    if clang_available() {
        configurations.push(vec!["--release", "--backend", "llvm"]);
    }
    let mut reference: Option<String> = None;
    for flags in configurations {
        let built = Command::new(env!("CARGO_BIN_EXE_kush"))
            .current_dir(root)
            .args(["build", "main.kush", "-o", "program"])
            .args(&flags)
            .env_remove("KUSH_BACKEND")
            .env("KUSH_TRACE_SHADOWS", "1")
            .output()
            .unwrap();
        let trace = String::from_utf8_lossy(&built.stderr);
        assert!(built.status.success(), "{flags:?}: {trace}\n{source}");
        let reported = trace.matches("vector shadows:").count();
        let expected = if flags.contains(&"llvm") { shadowed } else { 0 };
        assert_eq!(reported, expected, "{flags:?}: {trace}\n{source}");
        let output = Command::new(root.join("program")).output().unwrap();
        assert!(
            output.status.success(),
            "{flags:?}: {:?}\n{source}",
            output.status
        );
        let printed = String::from_utf8(output.stdout).unwrap();
        match &reference {
            None => reference = Some(printed),
            Some(expected) => assert_eq!(&printed, expected, "{flags:?}\n{source}"),
        }
    }
    reference.unwrap()
}

const SUM: &str = "
fn total_of(values: &Vec<i64>) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < Vec.len(values) {
        acc = acc + Vec.get(values, i) * (i + 1);
        i = i + 1;
    }
    acc
}
";

#[test]
fn growth_from_empty_through_every_capacity() {
    // Starts with no room and grows through the small, pooled and large
    // block representations.
    let printed = agree(
        &format!(
            "{SUM}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut values: Vec<i64> = Vec.with_capacity(0);
            let mut i = 0;
            while i < 70000 {{
                values = Vec.push(values, i & 1023);
                i = i + 1;
            }}
            print_i64(Vec.len(&values));
            print_i64(total_of(&values));
        }}"
        ),
        1,
    );
    assert!(printed.starts_with("70000\n"), "{printed}");
}

#[test]
fn conditional_double_and_interleaved_pushes() {
    agree(
        &format!(
            "{SUM}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut evens: Vec<i64> = Vec.with_capacity(1);
            let mut odds: Vec<i64> = Vec.with_capacity(3);
            let mut i = 0;
            while i < 5000 {{
                if i & 1 == 0 {{
                    evens = Vec.push(evens, i);
                    if i & 7 == 0 {{ evens = Vec.push(evens, 0 - i); }}
                }} else {{
                    odds = Vec.push(odds, i);
                }}
                odds = Vec.push(odds, Vec.len(&evens));
                i = i + 1;
            }}
            print_i64(Vec.len(&evens));
            print_i64(Vec.len(&odds));
            print_i64(total_of(&evens));
            print_i64(total_of(&odds));
        }}"
        ),
        1,
    );
}

#[test]
fn the_length_and_elements_read_in_the_loop_are_current() {
    // The loop reads the vector's own length and elements between pushes.
    agree(
        &format!(
            "{SUM}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut values: Vec<i64> = Vec.with_capacity(2);
            values = Vec.push(values, 1);
            let mut check = 0;
            while Vec.len(&values) < 3000 {{
                let size = Vec.len(&values);
                let last = Vec.get(&values, size - 1);
                values = Vec.push(values, (last * 3 + size) & 4095);
                if Vec.len(&values) & 511 == 0 {{
                    check = check + Vec.get(&values, Vec.len(&values) - 1) + Vec.len(&values);
                }}
            }}
            print_i64(check);
            print_i64(total_of(&values));
        }}"
        ),
        1,
    );
}

#[test]
fn a_vector_lent_to_a_call_in_the_loop_is_left_alone() {
    agree(
        &format!(
            "{SUM}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut values: Vec<i64> = Vec.with_capacity(2);
            let mut check = 0;
            let mut i = 0;
            while i < 3000 {{
                values = Vec.push(values, i & 63);
                if i & 511 == 0 {{ check = check + total_of(&values); }}
                i = i + 1;
            }}
            print_i64(check);
        }}"
        ),
        0,
    );
}

#[test]
fn nested_loops_and_early_exit() {
    agree(
        &format!(
            "{SUM}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut values: Vec<i64> = Vec.with_capacity(0);
            let mut row = 0;
            while row < 200 {{
                let mut column = 0;
                while column < row {{
                    if column == 150 {{ break; }}
                    values = Vec.push(values, row * 1000 + column);
                    column = column + 1;
                }}
                values = Vec.push(values, 0 - row);
                row = row + 1;
            }}
            print_i64(Vec.len(&values));
            print_i64(total_of(&values));
        }}"
        ),
        1,
    );
}

#[test]
fn a_vector_the_loop_also_changes_otherwise_is_left_alone() {
    // Moved through a function, and replaced, inside the loop.
    agree(
        &format!(
            "{SUM}
        fn extend(values: Vec<i64>, x: i64) -> Vec<i64> ! {{alloc, panic}} {{
            let grown = Vec.push(values, x);
            Vec.push(grown, x + 1)
        }}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let mut values: Vec<i64> = Vec.with_capacity(0);
            let mut i = 0;
            while i < 3000 {{
                values = Vec.push(values, i);
                if i & 15 == 0 {{ values = extend(values, 0 - i); }}
                if i == 1500 {{ values = Vec.with_capacity(4); }}
                i = i + 1;
            }}
            print_i64(Vec.len(&values));
            print_i64(total_of(&values));
        }}"
        ),
        0,
    );
}

#[test]
fn wide_elements_and_pushes_inside_the_pushed_value() {
    agree(
        "fn pair(a: i64, b: i64) -> (i64, i64) ! {} { (a, b) }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut pairs: Vec<(i64, i64)> = Vec.with_capacity(0);
            let mut log: Vec<i64> = Vec.with_capacity(0);
            let mut i = 0;
            while i < 4000 {
                pairs = Vec.push(pairs, pair({ log = Vec.push(log, i); i }, Vec.len(&log)));
                i = i + 1;
            }
            let (a, b) = Vec.get(&pairs, 3999);
            print_i64(a);
            print_i64(b);
            print_i64(Vec.len(&pairs) + Vec.len(&log));
        }",
        1,
    );
}
