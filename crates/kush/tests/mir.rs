//! FND-MIR: the control-flow-graph IR (docs/mir-design.md).
//!
//! Every body the builder produces for the example corpus passes the
//! verifier and reads back from its text form; native code lowered from it
//! behaves as the tree path does. `KUSH_MIR=1 scripts/test-all.sh` replays
//! the whole native suite on the MIR path.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable,
    native::{self, CodegenOptions, LinkSpec, Scratch},
};
use std::{fs, path::Path, process::Command};

fn examples() -> Vec<std::path::PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut files = fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|e| e == "kush"))
        .collect::<Vec<_>>();
    files.sort();
    files
}

#[test]
fn every_built_body_verifies_and_reads_back_from_its_text() {
    let (mut built, mut total, mut checked) = (0, 0, 0);
    for path in examples() {
        let Ok(program) = kush::program::load_path(&path) else {
            continue;
        };
        let Ok(program) = executable::check_program(&program) else {
            continue;
        };
        let (covered, functions) = kush::mir::coverage(&program);
        built += covered;
        total += functions;
        checked += kush::mir::self_check(&program)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    }
    assert_eq!(checked, built);
    // The corpus exercises the builder; coverage only grows.
    assert!(built >= 60, "MIR covers {built} of {total} example functions");
}

#[test]
fn the_text_form_is_stable() {
    let program = executable::check(
        "fn count(limit: i64) -> i64 {
            let mut i = 0;
            while i < limit { i = i + 1; }
            i
        }
        fn main() -> Unit ! {io} { print_i64(count(3)); }",
    )
    .unwrap();
    let text = kush::mir::dump(&program);
    let count = text
        .split("\n\n")
        .find(|part| part.contains("fn \"count\""))
        .unwrap();
    assert_eq!(
        count,
        "// function 1
fn \"count\"(_0: i64) -> i64 {
    let mut _1: i64;
    temp _2: bool;
    temp _3: i64;
    bb0: {
        _1 = const 0: i64 @54..55;
        goto bb1 @69..99;
    }
    bb1: {
        _2 = Lt(copy _1, copy _0) @75..84;
        switch move _2 [0 -> bb3] otherwise bb2 @69..99;
    }
    bb2: {
        _3 = int unchecked_add i64 i64(copy _1, const 1: i64) @91..96;
        _1 = move _3 @87..96;
        goto bb1 @69..99;
    }
    bb3: {
        return copy _1 @112..113;
    }
}
"
    );
}

/// Build `source` natively on the tree path and on the MIR path; both must
/// print the same and exit the same way.
fn same_on_both_paths(source: &str) -> String {
    let program = executable::check(source).unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut outputs = Vec::new();
    for mir in [false, true] {
        let binary = scratch.path().join(format!("program-{mir}"));
        let codegen = CodegenOptions {
            mir,
            ..CodegenOptions::default()
        };
        native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), codegen)
            .unwrap();
        let output = Command::new(&binary).output().unwrap();
        outputs.push((output.status.code(), output.stdout, output.stderr));
    }
    assert_eq!(outputs[0], outputs[1]);
    String::from_utf8(outputs.remove(0).1).unwrap()
}

#[test]
fn scalar_control_flow_matches_the_tree_path() {
    let output = same_on_both_paths(
        "fn fib(n: i64) -> i64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
        fn classify(x: i64) -> i64 {
            match x { 0 => 10, 1 | 2 => 20, n if n > 100 => n, _ => 30 }
        }
        fn first_square_over(limit: i64) -> i64 {
            let mut i = 0;
            loop {
                i = i + 1;
                if i * i <= limit { continue; }
                break i;
            }
        }
        fn narrow(x: u8) -> u8 { (x ^ 15) & 255 }
        fn main() -> Unit ! {io} {
            let mut i = 0;
            let mut total = 0;
            while i < 15 { total = total + fib(i); i = i + 1; }
            print_i64(total);
            print_i64(classify(0) + classify(2) + classify(500) + classify(7));
            print_i64(first_square_over(50));
            print_i64(if total > 10 && i == 15 || false { 1 } else { 0 });
            print_i64(if narrow(200) == 199 { 1 } else { 0 });
            let mut x = 0;
            print_i64({ x = 1; x } + { x = 2; x } * 10);
        }",
    );
    assert_eq!(output, "986\n560\n8\n1\n1\n21\n");
}

#[test]
fn checked_arithmetic_panics_on_the_mir_path_as_on_the_tree() {
    same_on_both_paths(
        "fn grow(x: i64) -> i64 { x * 1000000000000 }
        fn main() -> Unit ! {io} { print_i64(1); print_i64(grow(grow(3))); }",
    );
    same_on_both_paths(
        "fn half(x: i64, y: i64) -> i64 { x / y }
        fn main() -> Unit ! {io} { print_i64(half(4, 2)); print_i64(half(1, 0)); }",
    );
}

#[test]
fn functions_outside_the_ir_fall_back_to_the_tree() {
    let output = same_on_both_paths(
        "fn total(values: Vec<i64>) -> i64 {
            let mut sum = 0;
            let mut i = 0;
            while i < values.len() { sum = sum + values.get(i); i = i + 1; }
            sum
        }
        fn square(x: i64) -> i64 { x * x }
        fn main() -> Unit ! {io, alloc} {
            let mut values: Vec<i64> = Vec.with_capacity(3);
            values = values.push(square(2));
            values = values.push(square(3));
            print_i64(total(values));
        }",
    );
    assert_eq!(output, "13\n");
}

#[test]
fn kush_mir_prints_the_ir_and_its_coverage() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let file = scratch.path().join("program.kush");
    fs::write(
        &file,
        "fn twice(x: i64) -> i64 { x + x }
        fn main() -> Unit ! {io} { print_i64(twice(4)); }",
    )
    .unwrap();
    let kush = env!("CARGO_BIN_EXE_kush");
    let output = Command::new(kush).arg("mir").arg(&file).output().unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("fn \"twice\"(_0: i64) -> i64 {"), "{text}");
    assert!(text.contains("call fn "), "{text}");
    let output = Command::new(kush)
        .args([Path::new("mir"), &file, Path::new("--stats")])
        .output()
        .unwrap();
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "MIR covers 2 of 2 functions.\n"
    );
}
