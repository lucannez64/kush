//! The kernel written in Kush (`examples/kernel`, docs/kernel-in-kush.md):
//! its package tests pass, it reads and prints back every exchange file the
//! Rust side dumps from the example corpus byte for byte, and its normal
//! forms agree with the Rust kernel's.
use std::{path::PathBuf, process::Command};

const CORPUS: &[&str] = &[
    "proofs",
    "induction",
    "logical-data",
    "finite-proofs",
    "large-naturals",
    "universes",
];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn kush() -> Command {
    Command::new(env!("CARGO_BIN_EXE_kush"))
}

fn scratch(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush-kik-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

#[test]
fn the_package_tests_pass() {
    let output = kush()
        .arg("test")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
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

fn build(dir: &std::path::Path) -> PathBuf {
    let binary = dir.join("kernel");
    let build = kush()
        .arg("build")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
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

fn dump(name: &str) -> String {
    let source = std::fs::read_to_string(root().join(format!("examples/{name}.kush"))).unwrap();
    let checked = kush::check(&source)
        .or_else(|_| kush::executable::logical_module(&source))
        .unwrap();
    kush::exchange::dump(&checked)
}

/// Compare the Kush kernel's `normalize` answers with the Rust kernel's.
/// Lines agree exactly, except that a budget exhaustion on either side is
/// inconclusive (the two kernels charge different steps). Returns the number
/// of conclusive normal forms compared.
fn agree_on_normal_forms(binary: &std::path::Path, file: &std::path::Path, text: &str) -> usize {
    std::fs::write(file, text).unwrap();
    let rust = kush::exchange::answer(text).unwrap();
    let output = Command::new(binary)
        .arg("normalize")
        .arg(file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let kush_answer = String::from_utf8(output.stdout).unwrap();
    let rust_lines: Vec<&str> = rust.lines().collect();
    let kush_lines: Vec<&str> = kush_answer.lines().collect();
    assert_eq!(rust_lines.len(), kush_lines.len(), "{kush_answer}");
    let mut compared = 0;
    for (rust_line, kush_line) in rust_lines.iter().zip(&kush_lines) {
        if *rust_line == "budget" || *kush_line == "budget" {
            continue;
        }
        assert_eq!(rust_line, kush_line, "in {}", file.display());
        compared += 1;
    }
    compared
}

#[test]
fn normal_forms_agree_with_the_rust_kernel() {
    let dir = scratch("normal");
    let binary = build(&dir);
    for name in CORPUS {
        let file = dir.join(format!("{name}.kcore"));
        let text = dump(name);
        let compared = agree_on_normal_forms(&binary, &file, &text);
        assert_eq!(
            compared,
            text.lines().count(),
            "{name}: no item may be inconclusive"
        );
    }
    // Targeted reductions, each a normalize query.
    let cases = "
        (def two 0 nat (succ (succ zero)))
        (def id 1 (pi (sort (u 0)) (pi (var 0) (var 1))) (lam (sort (u 0)) (lam (var 0) (var 0))))
        (data Even 0 type () (ctor E0 () () ()) (ctor ES () ((global Even)) ()))
        (normalize (succ (lit 999999999)))
        (normalize (succ (succ (global two))))
        (normalize (lam nat (succ (var 0))))
        (normalize (lam nat (app (lam nat (lam nat (var 1))) (var 0))))
        (normalize (app (app (global id 1) (sort 0)) nat))
        (normalize (natelim (lam nat nat) zero (lam nat (lam nat (var 1))) (lit 100000000000000000000)))
        (normalize (natelim (lam nat nat) (lit 3) (lam nat (lam nat (succ (var 0)))) (lit 40)))
        (normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 1000000)))
        (normalize (lam nat (natelim (lam nat nat) zero (lam nat (lam nat (var 0))) (var 0))))
        (normalize (transport nat zero zero (lam nat nat) (refl nat zero) (lit 5)))
        (normalize (lam (eq nat zero zero) (transport nat zero zero (lam nat nat) (var 0) (lit 5))))
        (normalize (eqelim nat zero zero (lam nat (lam (eq nat zero (var 0)) nat)) (lit 9) (refl nat zero)))
        (normalize (indelim Even (lam (global Even) nat) (zero (lam (global Even) (lam nat (succ (succ (var 0)))))) (app (global ES) (app (global ES) (global E0)))))
        (normalize (lam (global Even) (indelim Even (lam (global Even) nat) (zero (lam (global Even) (lam nat (var 0)))) (var 0))))
    ";
    let file = dir.join("cases.kcore");
    assert!(agree_on_normal_forms(&binary, &file, cases) >= 15);
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn the_kush_kernel_prints_the_corpus_back_unchanged() {
    let dir = scratch("print");
    let binary = build(&dir);
    for name in CORPUS {
        let dump = dump(name);
        let file = dir.join(format!("{name}.kcore"));
        std::fs::write(&file, &dump).unwrap();
        let output = Command::new(&binary)
            .arg("print")
            .arg(&file)
            .output()
            .unwrap();
        assert!(output.status.success(), "{name}");
        assert_eq!(String::from_utf8(output.stdout).unwrap(), dump, "{name}");
    }
    // Malformed input is reported with its byte offset and a nonzero status.
    let bad = dir.join("bad.kcore");
    std::fs::write(&bad, "(def x 0 nat zero)\n(launch)\n").unwrap();
    let output = Command::new(&binary)
        .arg("print")
        .arg(&bad)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("at byte 20"));
    std::fs::remove_dir_all(&dir).ok();
}
