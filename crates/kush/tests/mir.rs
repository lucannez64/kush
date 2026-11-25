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
    assert!(built >= 105, "MIR covers {built} of {total} example functions");
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
    same_program_on_both_paths(&executable::check(source).unwrap(), false)
}

/// As [`same_on_both_paths`]; with `stats`, the programs also report their
/// allocations, which must agree.
fn same_program_on_both_paths(program: &executable::Executable, stats: bool) -> String {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut outputs = Vec::new();
    for mir in [false, true] {
        let binary = scratch.path().join(format!("program-{mir}"));
        let codegen = CodegenOptions {
            mir,
            ..CodegenOptions::default()
        };
        native::build_with_codegen(program, &binary, stats, &LinkSpec::default(), codegen)
            .unwrap();
        let output = Command::new(&binary).output().unwrap();
        outputs.push((output.status.code(), output.stdout, output.stderr));
    }
    assert_eq!(outputs[0], outputs[1]);
    if stats {
        let report = String::from_utf8_lossy(&outputs[0].2).into_owned();
        let count = |key: &str| {
            report
                .split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .and_then(|value| value.parse::<u64>().ok())
                .unwrap_or_else(|| panic!("no {key} in {report}"))
        };
        assert_eq!(count("allocations="), count("deallocations="), "{report}");
    }
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
fn records_and_enums_match_the_tree_path() {
    let source = "
        struct Point { x: i64, y: i64 }
        struct Segment { from: Point, to: Point }
        enum Shape { Dot(Point), Line(Segment), Empty }
        enum Sign { Negative, Zero, Positive }
        enum Maybe { Just(i64), Nothing }
        fn sign(x: i64) -> Sign {
            if x < 0 { Sign.Negative } else if x == 0 { Sign.Zero } else { Sign.Positive }
        }
        fn shift(p: Point, by: i64) -> Point { Point { x: p.x + by, y: p.y - by } }
        fn length(s: Segment) -> i64 { (s.to.x - s.from.x) + (s.to.y - s.from.y) }
        fn weight(shape: Shape) -> i64 {
            match shape {
                Shape.Dot(Point { x: 0, y }) => y,
                Shape.Dot(p) => p.x * 10 + p.y,
                Shape.Line(s) if length(s) > 100 => 100,
                Shape.Line(s) => length(s),
                Shape.Empty => -1,
            }
        }
        fn code(s: Sign) -> i64 {
            match s { Sign.Negative | Sign.Zero => 0, Sign.Positive => 1 }
        }
        fn first(o: Maybe, fallback: i64) -> i64 {
            match o { Maybe.Just(v) => v, Maybe.Nothing => fallback }
        }
        fn main() -> Unit ! {io} {
            let p = shift(Point { x: 1, y: 2 }, 3);
            print_i64(p.x * 100 + p.y);
            let s = Segment { from: p, to: shift(p, 5) };
            print_i64(length(s));
            print_i64(weight(Shape.Dot(Point { x: 0, y: 7 })));
            print_i64(weight(Shape.Dot(p)));
            print_i64(weight(Shape.Line(s)));
            print_i64(weight(Shape.Line(Segment { from: p, to: Point { x: 500, y: 500 } })));
            print_i64(weight(Shape.Empty));
            print_i64(code(sign(-3)) + code(sign(0)) * 10 + code(sign(9)) * 100);
            print_i64(first(Maybe.Just(4), 0) + first(Maybe.Nothing, 30));
        }";
    let program = executable::check(source).unwrap();
    let (built, total) = kush::mir::coverage(&program);
    assert!(built + 1 >= total, "MIR covers {built} of {total} functions");
    let output = same_on_both_paths(source);
    assert_eq!(output, "399\n0\n7\n39\n0\n100\n-1\n100\n34\n");
}

#[test]
fn owned_values_are_dropped_once_on_return_break_and_unwind() {
    let source = "
        use std.result.Result;
        use std.task.Panic;
        struct Pair { left: Box<i64>, right: i64 }
        enum Tree { Leaf(i64), Node(Box<i64>, Box<i64>) }
        fn keep(p: Pair) -> i64 { p.right }
        fn open(b: Box<i64>) -> i64 { b.take() }
        fn sum(t: Tree) -> i64 {
            match t { Tree.Leaf(v) => v, Tree.Node(a, _) => open(a) }
        }
        fn hold(depth: i64, fail: Bool) -> i64 ! {alloc} {
            let a = Box.new(depth);
            let p = Pair { left: Box.new(1), right: depth };
            if depth == 0 {
                if fail { panic(); }
                return 0;
            }
            hold(depth - 1, fail) + keep(p) + a.take()
        }
        fn first_large(limit: i64) -> i64 ! {alloc} {
            let mut i = 0;
            loop {
                let b = Box.new(i * i);
                i = i + 1;
                if i == 2 { continue; }
                if open(b) > limit { break i; }
            }
        }
        fn show(result: Result<i64, Panic>) -> Unit ! {io} {
            match result { Result.Ok(value) => print_i64(value), Result.Err(_) => print_i64(-1) }
        }
        fn main() -> Unit ! {io, alloc, suspend} {
            print_i64(sum(Tree.Node(Box.new(7), Box.new(8))) + sum(Tree.Leaf(3)));
            print_i64(first_large(10));
            show(Task.catch(fn() -> i64 ! {alloc} { hold(3, false) }));
            show(Task.catch(fn() -> i64 ! {alloc} { hold(3, true) }));
        }";
    let program = kush::program::load_source("<mir-owned>", source).unwrap();
    let program = executable::check_program(&program).unwrap();
    let covered = ["keep", "open", "sum", "hold", "first_large"];
    let text = kush::mir::dump(&program);
    for name in covered {
        assert!(text.contains(&format!("fn \"{name}\"(")), "{name} is not covered\n{text}");
    }
    let output = same_program_on_both_paths(&program, true);
    assert_eq!(output, "10\n5\n12\n-1\n");
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
