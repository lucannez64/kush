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
    let machine = machine::evaluate(program, &mut machine_output);
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
        (Ok((tree_result, tree_stats)), Ok((result, stats))) => {
            assert_eq!(result, tree_result, "result");
            assert_eq!(stats.report(), tree_stats.report(), "stats");
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
const MACHINE_FLOOR: usize = 13;

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
