//! FND-EVAL: the evaluator as a word-level machine over the MIR
//! (docs/mir-design.md section 9), against the tree evaluator it replaces.
//! On every program the machine covers, both print the same, end the same
//! way (with the same panic message), and report the same allocation stats.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{executable, mir::machine};
use std::{collections::BTreeMap, fs, path::Path};

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

/// Run `program` on both evaluators. `Ok(false)` when the machine does not
/// cover it yet (with the reason), `Ok(true)` when both agree.
fn compare(program: &executable::Executable) -> Result<bool, String> {
    let mut tree_output = Vec::new();
    let tree = program.evaluate_with_stats(&mut tree_output);
    let mut machine_output = Vec::new();
    let machine = machine::evaluate_comparing(program, &mut machine_output);
    let machine = match machine {
        Err(machine::Stop::Unsupported(reason)) => return Err(reason),
        Err(machine::Stop::Fault(fault)) => panic!("the machine faulted: {fault}"),
        Err(machine::Stop::Panic(diagnostic)) => Err(diagnostic),
        Ok(done) => Ok(done),
    };
    assert_eq!(
        String::from_utf8_lossy(&machine_output),
        String::from_utf8_lossy(&tree_output),
        "output"
    );
    match (tree, machine) {
        (Ok((tree_result, tree_stats)), Ok((result, stats, comparable))) => {
            assert_eq!(result, tree_result, "result");
            // The tree counts each continuation environment, kush.c (and
            // the machine) the chunks they live in.
            if comparable {
                assert_eq!(stats.report(), tree_stats.report(), "stats");
            }
        }
        (Err(tree_error), Err(error)) => assert_eq!(error.message, tree_error.message),
        (tree, machine) => panic!("tree: {tree:?}\nmachine: {machine:?}"),
    }
    Ok(true)
}

#[test]
fn covered_examples_run_as_on_the_tree_evaluator() {
    let mut compared = Vec::new();
    let mut missing: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for path in examples() {
        let source = fs::read_to_string(&path).unwrap();
        if source.contains("stdin") || !source.contains("fn main(") {
            continue;
        }
        let Ok(program) = kush::program::load_path(&path) else {
            continue;
        };
        let Ok(program) = executable::check_program(&program) else {
            continue;
        };
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        match std::panic::catch_unwind(|| compare(&program)) {
            Ok(Ok(_)) => compared.push(name),
            Ok(Err(reason)) => missing.entry(reason).or_default().push(name),
            Err(failure) => std::panic::resume_unwind(failure),
        }
    }
    // What the next nodes have to cover.
    for (reason, names) in &missing {
        eprintln!("not covered: {reason}: {}", names.join(", "));
    }
    eprintln!("compared {}: {}", compared.len(), compared.join(", "));
    // Coverage only grows.
    assert!(compared.len() >= MACHINE_FLOOR, "{compared:?}");
}

/// The examples the machine runs; raise it as nodes land.
const MACHINE_FLOOR: usize = 42;

#[test]
fn buffers_and_views_run_as_on_the_tree_evaluator() {
    for source in [
        // Vector growth, owned elements, set and clear; byte growth.
        "fn main() -> Unit ! {io, alloc} {
            let mut values: Vec<i64> = Vec.new();
            let mut i = 0;
            while i < 9 { values = Vec.push(values, i * i); i = i + 1; }
            values = Vec.set(values, 2, 100);
            print_i64(Vec.len(&values));
            print_i64(Vec.get(&values, 2) + Vec.get(&values, 8));
            let mut boxes: Vec<Box<i64>> = Vec.with_capacity(1);
            boxes = Vec.push(boxes, Box.new(1));
            boxes = Vec.push(boxes, Box.new(2));
            boxes = Vec.clear(boxes);
            print_i64(Vec.len(&boxes));
            let mut bytes = Bytes.with_capacity(0);
            let mut b = 0;
            while b < 20 { bytes = Bytes.push(bytes, 65 + b); b = b + 1; }
            print_i64(Bytes.len(&bytes));
            print_i64(Bytes.capacity(&bytes));
            print_i64(Bytes.get(&bytes, 19));
        }",
        // Views of arrays, vectors and bytes, and text.
        "fn head(view: &[i64], at: i64) -> i64 ! {} { view[at] }
        fn main() -> Unit ! {io, alloc} {
            let values: [i64; 5] = [10, 20, 30, 40, 50];
            let middle = &values[1..4];
            print_i64(Slice.len(middle));
            print_i64(head(middle[1..], 1));
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 7); v = Vec.push(v, 8);
            let view: &[i64] = &v[1..];
            print_i64(view[0]);
            let bytes = Bytes.from(\"ABCD\");
            let raw: &[i64] = &bytes[1..3];
            print_i64(raw[1]);
            let text = String.from(\"héllo\");
            print_i64(text.len());
            print_i64(text.scalar_len());
            let copy = text.as_bytes();
            print_i64(Bytes.len(&copy));
        }",
        // A widening, then narrowing, in-place map.
        "fn pair(x: i64) -> [i64; 2] ! {} { [x, x + 1] }
        fn sum_pair(pair: [i64; 2]) -> i64 ! {} { let [a, b] = pair; a + b }
        fn main() -> Unit ! {io, alloc} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            let values = Vec.map_chain_in_place(values, pair, sum_pair);
            print_i64(Vec.get(&values, 0) * 10 + Vec.get(&values, 1));
        }",
        // Out-of-bounds accesses panic with the tree's messages.
        "fn main() -> Unit ! {io, alloc} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            print_i64(Vec.get(&v, 3));
        }",
        "fn main() -> Unit ! {io, alloc} {
            let values: [i64; 3] = [1, 2, 3];
            let view = &values[..];
            let mut i = 0;
            while i < 5 { print_i64(view[i]); i = i + 1; }
        }",
    ] {
        let program = executable::check(source).unwrap();
        assert_eq!(compare(&program), Ok(true), "{source}");
    }
}

#[test]
fn closures_and_trait_objects_run_as_on_the_tree_evaluator() {
    for source in [
        // Function values, capturing `once` closures, an environment that
        // owns a box, and a capture by reference.
        "struct Pair { left: i64, right: i64 }
        fn apply(f: fn(i64) -> i64 ! {}, x: i64) -> i64 { f(x) }
        fn twice(f: fn(i64) -> i64 ! {}, x: i64) -> i64 { f(f(x)) }
        fn apply_once(f: once fn(i64) -> i64 ! {}, x: i64) -> i64 { f(x) }
        fn split(f: once fn(i64) -> Pair ! {}, x: i64) -> i64 { let p = f(x); p.left * 10 + p.right }
        fn run_once(f: once fn() -> i64 ! {alloc}) -> i64 ! {alloc} { f() }
        fn inc(x: i64) -> i64 { x + 1 }
        fn main() -> Unit ! {io, alloc} {
            print_i64(apply(inc, 4));
            print_i64(twice(fn(x: i64) -> i64 ! {} { x * 3 }, 2));
            let offset = 10;
            print_i64(apply_once(fn(x: i64) -> i64 ! {} { x + offset }, 5));
            print_i64(split(fn(x: i64) -> Pair ! {} { Pair { left: x, right: x + offset } }, 2));
            let boxed = Box.new(7);
            print_i64(run_once(fn() -> i64 ! {alloc} { boxed.take() + 1 }));
        }",
        // Trait objects: owned and borrowed receivers, payloads that own.
        "trait Describe {
            fn describe(self: Self) -> i64 ! {};
            fn peek(self: &Self) -> i64 ! {};
        }
        struct Point { x: i64 }
        struct Held { value: Box<i64> }
        impl Describe for Point {
            fn describe(self: Self) -> i64 ! {} { self.x }
            fn peek(self: &Self) -> i64 ! {} { self.x + 100 }
        }
        impl Describe for Held {
            fn describe(self: Self) -> i64 ! {} { let Held { value: value } = self; value.take() }
            fn peek(self: &Self) -> i64 ! {} { 200 }
        }
        fn main() -> Unit ! {io, alloc} {
            let point: dyn Describe = Point { x: 9 };
            print_i64(point.peek());
            print_i64(point.describe());
            let held: dyn Describe = Held { value: Box.new(4) };
            print_i64(held.peek());
            print_i64(held.describe());
        }",
    ] {
        let program = executable::check(source).unwrap();
        assert_eq!(compare(&program), Ok(true), "{source}");
    }
}

#[test]
fn panics_unwind_through_cleanup_and_report_the_tree_message() {
    for source in [
        "fn main() -> Unit ! {io} { print_i64(1); print_i64(9223372036854775807 + 1); }",
        "fn deep(n: i64) -> i64 { if n == 0 { panic() } else { deep(n - 1) + 1 } }
        fn main() -> Unit ! {io} { print_i64(deep(3)); }",
        "enum List { Nil, Cons(i64, Box<List>) }
        fn boom(list: List, n: i64) -> i64 { if n > 1 { panic() } else { n } }
        fn main() -> Unit ! {io, alloc} {
            let list = List.Cons(1, Box.new(List.Cons(2, Box.new(List.Nil))));
            print_i64(boom(list, 2));
        }",
    ] {
        let program = executable::check(source).unwrap();
        assert_eq!(compare(&program), Ok(true), "{source}");
    }
}
