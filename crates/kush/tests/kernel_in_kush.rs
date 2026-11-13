//! The kernel written in Kush (`examples/kernel`, docs/kernel-in-kush.md):
//! its package tests pass, and it reads and prints back every exchange file
//! the Rust side dumps from the example corpus, byte for byte.
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

#[test]
fn the_kush_kernel_prints_the_corpus_back_unchanged() {
    let dir = scratch("print");
    let binary = dir.join("kernel");
    let build = kush()
        .arg("build")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(build.status.success(), "{}", String::from_utf8_lossy(&build.stderr));
    for name in CORPUS {
        let source = std::fs::read_to_string(root().join(format!("examples/{name}.kush"))).unwrap();
        let checked = kush::check(&source)
            .or_else(|_| kush::executable::logical_module(&source))
            .unwrap();
        let dump = kush::exchange::dump(&checked);
        let file = dir.join(format!("{name}.kcore"));
        std::fs::write(&file, &dump).unwrap();
        let output = Command::new(&binary).arg("print").arg(&file).output().unwrap();
        assert!(output.status.success(), "{name}");
        assert_eq!(String::from_utf8(output.stdout).unwrap(), dump, "{name}");
    }
    // Malformed input is reported with its byte offset and a nonzero status.
    let bad = dir.join("bad.kcore");
    std::fs::write(&bad, "(def x 0 nat zero)\n(launch)\n").unwrap();
    let output = Command::new(&binary).arg("print").arg(&bad).output().unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("at byte 20"));
    std::fs::remove_dir_all(&dir).ok();
}
