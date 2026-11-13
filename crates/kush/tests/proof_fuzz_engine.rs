//! PROOF-FUZZ step 4: the `kush fuzz` driver. Planted bugs are found with the
//! failing check and the decoded input; a true but unproved check survives;
//! a check behind an impossible branch stays unreached; a function whose
//! parameters cannot be generated is reported as such; a session is
//! deterministic for a seed, however many harnesses run at once. See docs/proof-fuzz.md.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::fuzz::engine::{Options, Session, State};
use kush::native::{LinkSpec, Scratch};
use kush::program::{self, Memory};
use std::path::PathBuf;
use std::process::Command;

const LIB: &str = "module app.lib;

pub struct Pair { pub a: i64, pub b: i64 }

// Off by one: `i <= len` lets `i == len` through.
pub fn last(v: &Vec<i64>, i: i64) -> i64 ! {panic} {
    if i < 0 || i > v.len() { return 0; }
    v[i]
}
pub fn next(x: i64) -> i64 ! {panic} { x + 1 }
pub fn bump(x: u8) -> u8 ! {panic} { x + 1 }
// True for every input, but the prover cannot see it (a product).
pub fn square(x: i64) -> i64 ! {panic} {
    if x > 1000 || x < 0 - 1000 { return 0; }
    x * x
}
// `x % 7` is never 13, so the addition is never reached.
pub fn never(x: i64, y: i64) -> i64 ! {panic} {
    if x % 7 == 13 { return y + 1; }
    0
}
pub fn sum(p: Pair) -> i64 ! {panic} { p.a + p.b }
";

// `main` calls nothing: a harness of `main` would reach every function.
const MAIN: &str = "module app;
use app.lib;
fn main() -> i64 ! {} { 0 }";

fn session(scratch: &Scratch) -> Session {
    let modules = Memory(vec![("app.lib".into(), LIB.into())]);
    let original =
        program::load("main.kush", MAIN, &modules).unwrap_or_else(|(_, e)| panic!("{e:?}"));
    Session::new(
        &original,
        &modules,
        &LinkSpec::default(),
        &scratch.path().join("fuzz"),
        None,
        Vec::new(),
    )
    .unwrap_or_else(|e| panic!("{e}"))
}

fn options(filter: Option<&str>) -> Options {
    Options {
        filter: filter.map(str::to_owned),
        runs: 400,
        ..Options::default()
    }
}

/// `(state, goal, decoded inputs)` of the sites in the target `name`.
fn states(session: &Session, name: &str) -> Vec<(State, String, String)> {
    let target = session.targets.iter().position(|t| t.name == name).unwrap();
    session
        .reports
        .iter()
        .filter(|r| r.target == Some(target))
        .map(|r| {
            let inputs = r.finding.as_ref().map_or(String::new(), |f| {
                f.inputs
                    .iter()
                    .map(|(n, v)| format!("{n} = {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            });
            (r.state(&session.targets), r.goal.clone(), inputs)
        })
        .collect()
}

#[test]
fn planted_bugs_are_found() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut session = session(&scratch);
    session.fuzz(&options(None));
    let last = states(&session, "app.lib.last");
    assert!(
        last.iter().any(|(state, goal, inputs)| *state == State::Found
            && goal == "0 <= index && index < len"
            && inputs.ends_with(&format!("i = {}", inputs_length(inputs)))),
        "{last:?}"
    );
    let next = states(&session, "app.lib.next");
    assert!(
        next.contains(&(
            State::Found,
            "the result of + stays in i64".into(),
            "x = 9223372036854775807".into()
        )),
        "{next:?}"
    );
    let bump = states(&session, "app.lib.bump");
    assert!(
        bump.contains(&(
            State::Found,
            "the result of + stays in u8".into(),
            "x = 255".into()
        )),
        "{bump:?}"
    );
    assert!(session.found() >= 3);
}

/// The vector length in a decoded `v = [..], i = n` input.
fn inputs_length(inputs: &str) -> usize {
    let list = &inputs[inputs.find('[').unwrap() + 1..inputs.find(']').unwrap()];
    if list.is_empty() { 0 } else { list.split(", ").count() }
}

#[test]
fn true_unreached_and_ungenerated_checks_are_told_apart() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut session = session(&scratch);
    session.fuzz(&options(None));
    let square = states(&session, "app.lib.square");
    assert!(square.iter().all(|(state, ..)| *state == State::Survived), "{square:?}");
    let never = states(&session, "app.lib.never");
    assert!(
        never.contains(&(State::Unreached, "the result of + stays in i64".into(), String::new())),
        "{never:?}"
    );
    let sum = states(&session, "app.lib.sum");
    assert!(sum.iter().all(|(state, ..)| *state == State::NoGenerator), "{sum:?}");
    let report = session.render(&options(None));
    assert!(report.contains("no generator  app.lib.sum: no generator for `p: Pair`"), "{report}");
}

#[test]
fn a_session_is_deterministic_for_a_seed() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut first = session(&scratch);
    first.fuzz(&options(None));
    let mut second = session(&scratch);
    second.fuzz(&options(None));
    assert_eq!(first.render(&options(None)), second.render(&options(None)));
    assert_eq!(first.reports, second.reports);
}

#[test]
fn parallel_harnesses_give_the_same_session() {
    // Harnesses explore on their own and are folded in order, so how many
    // run at once changes only the wall-clock time.
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut alone = session(&scratch);
    alone.fuzz(&Options { jobs: 1, ..options(None) });
    let mut together = session(&scratch);
    together.fuzz(&Options { jobs: 4, ..options(None) });
    assert_eq!(alone.reports, together.reports);
    assert_eq!(alone.stats, together.stats);
}

#[test]
fn the_filter_selects_functions() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut session = session(&scratch);
    session.fuzz(&options(Some("lib.next")));
    assert_eq!(session.found(), 1);
    let report = session.render(&options(Some("lib.next")));
    assert!(report.contains("FOUND  overflow app.lib.next"), "{report}");
    assert!(!report.contains("app.lib.bump"), "{report}");
    let list = session.render_list(&options(Some("lib.")));
    assert!(list.contains("app.lib.sum  (no generator"), "{list}");
    assert!(list.contains("app.lib.last\n  bounds"), "{list}");
}

fn project(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush fuzz {label} {}", std::process::id()));
    let _ = std::fs::remove_dir_all(&path);
    std::fs::create_dir_all(path.join("src")).unwrap();
    std::fs::write(
        path.join("Kush.toml"),
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    path
}

#[test]
fn the_command_reports_and_exits_by_findings() {
    let buggy = project("buggy");
    std::fs::write(
        buggy.join("src/main.kush"),
        "module demo;\nfn next(x: i64) -> i64 ! {panic} { x + 1 }\nfn main() -> i64 ! {panic} { next(1) }\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--runs", "200"])
        .current_dir(&buggy)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(1), "{stdout}\n{}", String::from_utf8_lossy(&output.stderr));
    assert!(stdout.contains("FOUND  overflow demo.next  src/main.kush:2:36"), "{stdout}");
    assert!(stdout.contains("input    x = 9223372036854775807"), "{stdout}");

    let safe = project("safe");
    std::fs::write(
        safe.join("src/main.kush"),
        "module demo;\nfn small(x: u8) -> i64 ! {panic} { let y: i64 = Int.convert(x); y * y }\nfn main() -> i64 ! {panic} { small(3) }\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--runs", "100"])
        .current_dir(&safe)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("result: 0 found, 1 survived"), "{stdout}");

    let listed = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--list"])
        .current_dir(&safe)
        .output()
        .unwrap();
    assert_eq!(listed.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&listed.stdout).contains("demo.small\n  overflow src/main.kush:2:"));

    let bad = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--runs", "many"])
        .current_dir(&safe)
        .output()
        .unwrap();
    assert_eq!(bad.status.code(), Some(2));
    let _ = std::fs::remove_dir_all(&buggy);
    let _ = std::fs::remove_dir_all(&safe);
}

#[test]
fn coverage_is_reported_per_function_and_as_json() {
    let path = project("coverage");
    std::fs::write(
        path.join("src/main.kush"),
        "module demo;
fn next(x: i64) -> i64 ! {panic} { x + 1 }
fn bounded(x: u8) -> u8 ! {} { if x < 255 { x + 1 } else { x } }
fn mixed(x: u8, y: i64) -> i64 ! {panic} { let a: i64 = Int.convert(x); a + 1 + y }
fn main() -> i64 ! {} { 0 }
",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--runs", "200", "--report"])
        .current_dir(&path)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let row = |name: &str| -> Vec<String> {
        stdout
            .lines()
            .find(|line| line.starts_with(&format!("{name} ")))
            .unwrap_or_else(|| panic!("no row {name}: {stdout}"))
            .split_whitespace()
            .map(str::to_owned)
            .collect()
    };
    assert_eq!(row("function"), ["function", "checks", "proved", "found", "survived", "unreached", "no-gen"]);
    // `next` overflows; `bounded` is fully proved; `mixed` has one proved
    // addition (`a + 1`, a is at most 255) and one found (`+ y`).
    assert_eq!(row("demo.next"), ["demo.next", "1", "0", "1", "0", "0", "0"]);
    assert_eq!(row("demo.bounded"), ["demo.bounded", "1", "1", "0", "0", "0", "0"]);
    assert_eq!(row("demo.mixed"), ["demo.mixed", "2", "1", "1", "0", "0", "0"]);
    assert_eq!(
        row("package").join(" "),
        "package demo 4 2 2 0 0 0 100% proved or attacked"
    );

    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .args(["fuzz", "--runs", "200", "--json"])
        .current_dir(&path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let lines: Vec<serde_json::Value> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(lines.len(), 4, "{lines:?}");
    let states: Vec<&str> = lines.iter().map(|v| v["state"].as_str().unwrap()).collect();
    assert_eq!(states.iter().filter(|s| **s == "proved").count(), 2);
    assert_eq!(states.iter().filter(|s| **s == "found").count(), 2);
    let next = lines.iter().find(|v| v["function"] == "demo.next").unwrap();
    assert_eq!(next["finding"]["input"][0], serde_json::json!(["x", "9223372036854775807"]));
    assert_eq!(next["line"], 2);
    let _ = std::fs::remove_dir_all(&path);
}
