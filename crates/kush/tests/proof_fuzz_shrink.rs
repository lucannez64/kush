//! PROOF-FUZZ step 5: what a counterexample produces. The input is
//! minimized; the suggestion, applied to the function, lets the prover remove
//! the check; a public function's input becomes a `kush test` case and a
//! private one's a saved input, replayed by the next session. See
//! docs/proof-fuzz.md, section 3.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::executable::check;
use kush::fuzz::engine::{Options, Session};
use kush::fuzz::harness::{Collection, Layout, Passing, Scalar, Slot};
use kush::fuzz::shrink::{self, Value};
use kush::native::{LinkSpec, Scratch};
use kush::program::{self, Memory};
use std::path::{Path, PathBuf};
use std::process::Command;

const I64: Scalar = Scalar::Int {
    name: "i64",
    bytes: 8,
    signed: true,
};

#[test]
fn shrinking_shortens_collections_and_moves_numbers_to_the_boundary() {
    let layout = Layout {
        slots: vec![
            Slot::Scalar {
                name: "x".into(),
                offset: 0,
                scalar: I64,
                passing: Passing::Value,
            },
            Slot::Collection {
                name: "v".into(),
                offset: 8,
                collection: Collection::Vec(I64),
                minimum: 0,
                maximum: 64,
                passing: Passing::Shared,
            },
        ],
        fixed: 10,
        ..Layout::default()
    };
    let start = shrink::encode(
        &layout,
        &[Value::Scalar(123_456), Value::List(vec![-77, 5, 99, 1 << 40])],
    );
    // Fails when x >= 1000 and v has an element of at least 3.
    let fails = |tape: &[u8]| {
        let values = shrink::values(&layout, tape);
        let (Value::Scalar(x), Value::List(v)) = (&values[0], &values[1]) else {
            unreachable!()
        };
        *x >= 1000 && v.iter().any(|e| *e >= 3)
    };
    let (tape, calls) = shrink::shrink(&layout, &start, 500, fails);
    assert_eq!(
        shrink::values(&layout, &tape),
        vec![Value::Scalar(1000), Value::List(vec![3])]
    );
    assert!(calls < 500);
    // A tape whose canonical form does not fail is returned unchanged.
    let (same, _) = shrink::shrink(&layout, &start, 10, |_| false);
    assert_eq!(same, start);
}

const LIB: &str = "module app.lib;
pub fn at(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
pub fn next(x: i64) -> i64 ! {panic} { x + 1 }
pub fn bump(x: u8) -> u8 ! {panic} { x + 1 }
fn byte(b: &Bytes, i: i64) -> i64 ! {panic} { b[i] }
pub fn twice(x: i64, y: i64) -> i64 ! {panic} { x * y }
";

fn fuzzed() -> (Session, Scratch) {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let modules = Memory(vec![("app.lib".into(), LIB.into())]);
    let original = program::load("main.kush", "module app;\nuse app.lib;\nfn main() -> i64 ! {} { 0 }", &modules)
        .unwrap_or_else(|(_, e)| panic!("{e:?}"));
    let mut session = Session::new(&original, &modules, &LinkSpec::default(), &scratch.path().join("f"), None, Vec::new())
        .unwrap_or_else(|e| panic!("{e}"));
    session.fuzz(&Options {
        runs: 400,
        ..Options::default()
    });
    (session, scratch)
}

fn finding<'s>(session: &'s Session, text: &str) -> &'s kush::fuzz::engine::Finding {
    session
        .reports
        .iter()
        .find(|r| r.text == text)
        .and_then(|r| r.finding.as_ref())
        .unwrap_or_else(|| panic!("no finding at {text}: {}", session.render(&Options::default())))
}

fn inputs(finding: &kush::fuzz::engine::Finding) -> String {
    finding
        .inputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The `erased ...` clause between the first pair of backticks.
fn clause(suggestion: &str) -> &str {
    suggestion.split('`').nth(1).unwrap()
}

#[test]
fn findings_are_minimized_classified_and_explained() {
    let (session, _scratch) = fuzzed();
    let at = finding(&session, "v[i]");
    assert_eq!(inputs(at), "v = [], i = 0");
    assert!(at.public);
    assert_eq!(
        at.suggestion,
        "`erased in_bounds: { 0 <= i && i < Vec.len(v) }` on at, and read with `Vec.at(v, i, _)`; callers then prove it"
    );
    let next = finding(&session, "x + 1");
    assert_eq!(inputs(next), "x = 9223372036854775807");
    let byte = finding(&session, "b[i]");
    assert!(!byte.public);
    assert!(byte.reproduction.is_none());
    assert_eq!(inputs(byte), "b = b\"\", i = 0");
    let twice = finding(&session, "x * y");
    assert!(twice.suggestion.contains("product of two values"), "{}", twice.suggestion);
    let report = session.render(&Options::default());
    assert!(report.contains("kind     local: reached through a private function"), "{report}");
    assert!(report.contains("minimized in"), "{report}");
}

#[test]
fn applied_suggestions_remove_the_check() {
    let (session, _scratch) = fuzzed();
    let at = clause(&finding(&session, "v[i]").suggestion).to_owned();
    let next = clause(&finding(&session, "x + 1").suggestion).to_owned();
    // The functions with the suggested precondition (and `Vec.at`), called
    // by a caller whose own facts establish it.
    let source = format!(
        "fn at(v: &Vec<i64>, i: i64, {at}) -> i64 ! {{}} {{ Vec.at(v, i, _) }}
fn next(x: i64, {next}) -> i64 ! {{}} {{ x + 1 }}
fn main() -> i64 ! {{alloc, panic}} {{
    let mut v: Vec<i64> = Vec.new();
    v = v.push(4);
    if v.len() > 0 {{ at(&v, 0, _) + next(5, _) }} else {{ 0 }}
}}"
    );
    let program = check(&source).unwrap_or_else(|e| panic!("{e:?}\n{source}"));
    let left: Vec<_> = program
        .obligations()
        .iter()
        .filter(|o| o.function_name != "main")
        .collect();
    assert!(left.is_empty(), "{left:?}");
}

fn project() -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush fuzz save {}", std::process::id()));
    let _ = std::fs::remove_dir_all(&path);
    std::fs::create_dir_all(path.join("src")).unwrap();
    std::fs::create_dir_all(path.join("tests")).unwrap();
    std::fs::write(
        path.join("Kush.toml"),
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(
        path.join("src/main.kush"),
        "module demo;\nuse demo.lib;\nfn main() -> i64 ! {} { 0 }\n",
    )
    .unwrap();
    std::fs::write(
        path.join("src/lib.kush"),
        "module demo.lib;\npub fn next(x: i64) -> i64 ! {panic} { x + 1 }\nfn byte(b: &Bytes, i: i64) -> i64 ! {panic} { b[i] }\n",
    )
    .unwrap();
    std::fs::write(
        path.join("tests/main.kush"),
        "module demo.tests.main;\n\nuse std.test;\n\n#[test]\nfn passes() -> Unit ! {panic} { test.is_true(true); }\n",
    )
    .unwrap();
    path
}

fn kush(directory: &Path, args: &[&str]) -> (Option<i32>, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(args)
        .current_dir(directory)
        .output()
        .unwrap();
    (
        output.status.code(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
    )
}

#[test]
fn saved_reproductions_fail_under_kush_test_and_inputs_replay() {
    let path = project();
    let (status, output) = kush(&path, &["fuzz", "--runs", "200", "--save"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(output.contains("added 1 tests to"), "{output}");
    assert!(output.contains("saved input"), "{output}");
    let tests = std::fs::read_to_string(path.join("tests/main.kush")).unwrap();
    assert!(tests.contains("use demo.lib;"), "{tests}");
    assert!(tests.contains("fn fuzz_next_line_2()"), "{tests}");
    // The reproduction fails; the existing test still passes.
    let (status, output) = kush(&path, &["test"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(output.contains("test passes ... ok"), "{output}");
    assert!(output.contains("test fuzz_next_line_2 ... FAILED"), "{output}");
    // Saving again adds nothing new.
    let (_, output) = kush(&path, &["fuzz", "--runs", "200", "--save"]);
    assert!(!output.contains("added"), "{output}");
    // With no new inputs at all, the saved one still finds the private bug.
    let (status, output) = kush(&path, &["fuzz", "--runs", "0", "lib.byte"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(output.contains("(calling demo.lib.byte, saved input)"), "{output}");
    let _ = std::fs::remove_dir_all(&path);
}
