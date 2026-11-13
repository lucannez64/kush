//! The prover whose tactics are effect handlers (`examples/tactics`,
//! docs/tactics-handlers.md): its package tests pass, it proves a set of
//! intuitionistic tautologies and finds no proof of non-theorems, and every
//! proof it prints is also accepted by the Rust kernel, so a bug in the Kush
//! kernel cannot let a wrong proof through unnoticed.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn kush() -> Command {
    Command::new(env!("CARGO_BIN_EXE_kush"))
}

fn scratch(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush-tactics-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

fn manifest() -> PathBuf {
    root().join("examples/tactics/Kush.toml")
}

#[test]
fn the_package_tests_pass() {
    let output = kush()
        .arg("test")
        .arg("--manifest-path")
        .arg(manifest())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("0 failed"), "{stdout}");
}

fn build(dir: &Path) -> PathBuf {
    let binary = dir.join("tactics");
    let build = kush()
        .arg("build")
        .arg("--manifest-path")
        .arg(manifest())
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    binary
}

const THEOREMS: &[&str] = &[
    "A -> A",
    "A -> B -> A",
    "(A -> B) -> (B -> C) -> A -> C",
    "(A -> B -> C) -> (A -> B) -> A -> C",
    "A & B -> B & A",
    "A | B -> B | A",
    "A & (B | C) -> A & B | A & C",
    "(A -> C) -> (B -> C) -> A | B -> C",
    "False -> A",
    "A -> ~~A",
    "(A -> B) -> ~B -> ~A",
    "~~(A | ~A)",
    "~(A | B) -> ~A & ~B",
];

const NON_THEOREMS: &[&str] = &["A -> B", "((A -> B) -> A) -> A", "A | ~A", "~~A -> A"];

#[test]
fn tautologies_are_proved_and_both_kernels_accept_the_proofs() {
    let dir = scratch("proofs");
    let binary = build(&dir);
    for formula in THEOREMS {
        let output = Command::new(&binary).arg(formula).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(0), "{formula}\n{stdout}");
        assert!(
            stdout.contains("kernel:  checked by the Kush kernel"),
            "{formula}\n{stdout}"
        );
        // The same proof as an exchange file, answered by the Rust kernel:
        // the three connectives, then the proof.
        let exchange = Command::new(&binary)
            .arg("--kcore")
            .arg(formula)
            .output()
            .unwrap();
        assert_eq!(exchange.status.code(), Some(0), "{formula}");
        let file = dir.join("proof.kcore");
        std::fs::write(&file, &exchange.stdout).unwrap();
        let answer = kush().arg("kernel").arg(&file).output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&answer.stdout),
            "ok And\nok Or\nok False\nok\n",
            "{formula}\n{}",
            String::from_utf8_lossy(&exchange.stdout)
        );
    }
}

#[test]
fn non_theorems_have_no_proof() {
    let dir = scratch("refused");
    let binary = build(&dir);
    for formula in NON_THEOREMS {
        let output = Command::new(&binary).arg(formula).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(1), "{formula}\n{stdout}");
        assert!(
            stdout.contains("proof:   none up to depth 8"),
            "{formula}\n{stdout}"
        );
    }
}

#[test]
fn malformed_formulas_are_reported() {
    let dir = scratch("malformed");
    let binary = build(&dir);
    let output = Command::new(&binary).arg("A -> (B").output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stdout).contains("cannot read the formula at byte 7"));
}
