//! GRADE-DEMAND-HINT (docs/grade-effect-demand.md decision 3): an exact-grade
//! violation caused only by statement-position uses inside a block argument
//! passed at demand >= 2 suggests hoisting the block. The hint is diagnostic
//! text only: every accept/reject verdict of section 1 stays as it was.

use kush::executable::check;

const HINT: &str = "hoist it before the call";

fn rejection(source: &str) -> (String, Vec<String>) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => (
            error.message.clone(),
            error.notes.iter().map(|(_, note)| note.clone()).collect(),
        ),
    }
}

fn accepted(source: &str, expected: i64, stdout: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(String::from_utf8(output).unwrap(), stdout, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("grade-demand-hint");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(native.status.code(), Some(expected as i32), "{source}");
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
    }
}

const TWICE: &str = "fn twice(v: i64 @[2]) -> i64 ! {panic} { v + v }\n";

#[test]
fn statement_position_uses_suggest_hoisting() {
    let source = format!(
        "{TWICE} fn main() -> i64 ! {{io, panic}} {{ let x: i64 @[1] = 7; twice({{ print_i64(x); 5 }}) }}"
    );
    let (message, notes) = rejection(&source);
    assert!(message.contains("used 2 time(s)"), "{message}");
    assert!(notes.iter().any(|note| note.contains(HINT)), "{notes:?}");

    // Several statements and a nested call in statement position.
    let source = "fn thrice(v: i64 @[3]) -> i64 ! {panic} { v + v + v }
         fn show(a: i64, b: i64) -> i64 ! {io, panic} { print_i64(a + b); a }
         fn main() -> i64 ! {io, panic} {
             let x: i64 @[2] = 7;
             thrice({ print_i64(x); show(x, 1); 5 })
         }"
    .to_string();
    let (message, notes) = rejection(&source);
    assert!(message.contains("used 6 time(s)"), "{message}");
    assert!(notes.iter().any(|note| note.contains(HINT)), "{notes:?}");
}

#[test]
fn value_uses_and_mixed_counts_get_no_hint() {
    // A genuine value use (the doc's `twice(x + 1)` row).
    for source in [
        format!("{TWICE} fn main() -> i64 ! {{panic}} {{ let x: i64 @[1] = 7; twice(x + 1) }}"),
        // The use is the block's tail value.
        format!("{TWICE} fn main() -> i64 ! {{panic}} {{ let x: i64 @[1] = 7; twice({{ x }}) }}"),
        // A `let` statement may flow to the tail: not counted as statement position.
        format!(
            "{TWICE} fn main() -> i64 ! {{panic}} {{ let x: i64 @[1] = 7; twice({{ let y = x; y }}) }}"
        ),
        // Counting the statement use once would still not reach the grade.
        format!(
            "{TWICE} fn main() -> i64 ! {{io, panic}} {{ let x: i64 @[3] = 7; twice({{ print_i64(x); 5 }}) }}"
        ),
        // Demand 1: no scaling, the error is not about the block.
        "fn one(v: i64) -> i64 ! {} { v } fn main() -> i64 ! {io, panic} { let x: i64 @[2] = 7; one({ print_i64(x); 5 }) }".to_string(),
    ] {
        let (message, notes) = rejection(&source);
        assert!(message.contains("time(s)"), "{message}\n{source}");
        assert!(!notes.iter().any(|note| note.contains(HINT)), "{notes:?}\n{source}");
    }
}

#[test]
fn verdicts_are_unchanged() {
    // Section 1 table, accepted rows.
    accepted(
        &format!(
            "{TWICE} fn main() -> i64 ! {{io, panic}} {{ let x: i64 @[2] = 7; twice({{ print_i64(x); 5 }}) }}"
        ),
        10,
        "7\n",
    );
    accepted(
        &format!(
            "{TWICE} fn main() -> i64 ! {{io, panic}} {{ let x: i64 @[1] = 7; let t = {{ print_i64(x); 5 }}; twice(t) }}"
        ),
        10,
        "7\n",
    );
    accepted(
        &format!(
            "{TWICE} fn id(v: i64) -> i64 ! {{}} {{ v }} fn main() -> i64 ! {{panic}} {{ let x: i64 @[2] = 7; twice(id(x)) }}"
        ),
        14,
        "",
    );
    // A hinted program with an owned allocation in the block is still rejected.
    let (message, _) = rejection(&format!(
        "{TWICE} fn main() -> i64 ! {{io, alloc, panic}} {{ let x: i64 @[1] = 7; twice({{ let b = Box.new(x); print_i64(x); Box.take(b) }}) }}"
    ));
    assert!(message.contains("time(s)"), "{message}");
}
