//! PROOF-FUZZ step 6: `#[fuzz]` entries. A test target declares
//! `#[fuzz] fn name(input: &Bytes) -> Unit` to reach code no generator can
//! call directly (here a function taking a record). Its findings are bugs
//! (the entry is the program's boundary), its reproductions are tests in
//! the test target itself, and `fuzz/corpus/<entry>/` seeds it. See
//! docs/proof-fuzz.md, section 2.3.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::path::{Path, PathBuf};
use std::process::Command;

fn project(label: &str, tests: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush fuzz entries {label} {}", std::process::id()));
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
        "module demo.lib;
pub struct Cursor { pub at: i64 }
// Reads one byte past the cursor: out of bounds at the last byte.
pub fn peek(c: &Cursor, b: &Bytes) -> i64 ! {panic} { b[c.at + 1] }
",
    )
    .unwrap();
    std::fs::write(path.join("tests/main.kush"), tests).unwrap();
    path
}

const TESTS: &str = "module demo.tests.main;

use std.test;
use demo.lib;

#[test]
fn passes() -> Unit ! {panic} { test.is_true(true); }

#[fuzz]
fn last_byte(input: &Bytes) -> Unit ! {panic} {
    if Bytes.len(input) > 2 {
        let c = lib.Cursor { at: Bytes.len(input) - 1 };
        let _ = lib.peek(&c, input);
    }
}

#[fuzz]
fn magic(input: &Bytes) -> Unit ! {panic} {
    if Bytes.len(input) >= 4 && input[0] == 201 && input[1] == 13 && input[2] == 177 && input[3] == 42 {
        let big = 9223372036854775807;
        let _ = big + Bytes.len(input);
    }
}

#[fuzz]
fn wrong(n: i64) -> Unit ! {} {}
";

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
fn an_entry_reaches_code_without_a_generator() {
    let path = project("reach", TESTS);
    let (status, output) = kush(&path, &["fuzz", "--runs", "300", "last_byte"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(
        output.contains("FOUND  bounds   demo.lib.peek  src/lib.kush:4:"),
        "{output}"
    );
    assert!(
        output.contains("(calling demo.tests.main.last_byte, run"),
        "{output}"
    );
    assert!(output.contains("kind     bug"), "{output}");
    // The smallest input that reaches the call: three bytes.
    assert!(output.contains("input    input = b\"\\x00\\x00\\x00\""), "{output}");
    // Its reproduction calls the entry in the test target.
    assert!(output.contains("let _ = last_byte(&input);"), "{output}");
    // A malformed entry is reported, not attacked.
    let (_, listed) = kush(&path, &["fuzz", "--list", "wrong"]);
    assert!(
        listed.contains("demo.tests.main.wrong  (no generator: a #[fuzz] entry takes one `&Bytes` and returns Unit)"),
        "{listed}"
    );
    let (status, output) = kush(&path, &["fuzz", "--runs", "300", "--save", "last_byte"]);
    assert_eq!(status, Some(1), "{output}");
    let (status, output) = kush(&path, &["test"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(output.contains("test fuzz_last_byte_line_4 ... FAILED"), "{output}");
    assert!(output.contains("test passes ... ok"), "{output}");
    let _ = std::fs::remove_dir_all(&path);
}

#[test]
fn corpus_files_seed_an_entry() {
    let path = project("corpus", TESTS);
    // Five runs do not find four magic bytes by mutation.
    let (status, output) = kush(&path, &["fuzz", "--runs", "5", "magic"]);
    assert_eq!(status, Some(0), "{output}");
    let corpus = path.join("fuzz/corpus/demo.tests.main.magic");
    std::fs::create_dir_all(&corpus).unwrap();
    std::fs::write(corpus.join("header"), [201u8, 13, 177, 42, 7]).unwrap();
    let (status, output) = kush(&path, &["fuzz", "--runs", "5", "magic"]);
    assert_eq!(status, Some(1), "{output}");
    assert!(output.contains("FOUND  overflow demo.tests.main.magic"), "{output}");
    let _ = std::fs::remove_dir_all(&path);
}
