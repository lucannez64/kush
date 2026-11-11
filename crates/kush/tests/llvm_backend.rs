//! The LLVM backend consumes the same lowered program as Cranelift, so every
//! example must behave identically on both. These tests need `clang`; without
//! it they pass vacuously (the whole suite can also be replayed on LLVM with
//! `KUSH_BACKEND=llvm cargo test`).
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

fn clang_available() -> bool {
    Command::new(std::env::var_os("KUSH_CLANG").unwrap_or_else(|| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}
fn kush() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_kush"));
    command.env_remove("KUSH_BACKEND");
    command
}
fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}
fn run(example: &str, flags: &[&str], stdin: &str) -> Output {
    use std::io::Write;
    let mut child = kush()
        .arg("run")
        .arg(examples().join(example))
        .args(flags)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

/// Programs covering integers, floats, text, closures, traits, ownership,
/// slices, tasks, effects and standard input.
const EXAMPLES: [(&str, &str); 22] = [
    ("first.kush", ""),
    ("floats.kush", ""),
    ("strings.kush", ""),
    ("borrowed-text.kush", ""),
    ("tuples.kush", ""),
    ("functions.kush", ""),
    ("effectful-functions.kush", ""),
    ("borrowed-closures.kush", ""),
    ("traits.kush", ""),
    ("generic_traits.kush", ""),
    ("advanced-traits.kush", ""),
    ("ownership.kush", ""),
    ("reuse.kush", ""),
    ("slices.kush", ""),
    ("mutable-slices.kush", ""),
    ("mutable-borrowed-records.kush", ""),
    ("dependent-arrays.kush", ""),
    ("niches.kush", ""),
    ("async.kush", ""),
    ("linear-tasks.kush", ""),
    ("expression-stdin.kush", "12 + 3 * 10\n"),
    (
        "json.kush",
        "{\"a\": [1, 2.5, \"x\\u00e9\"], \"b\": null}\n",
    ),
];

#[test]
fn examples_agree_between_backends_and_pipelines() {
    if !clang_available() {
        return;
    }
    for (example, stdin) in EXAMPLES {
        let reference = run(example, &[], stdin);
        for flags in [
            &["--backend", "llvm"][..],
            &["--backend", "llvm", "--release"],
            &["--backend", "llvm", "--release", "--no-deferred-overflow"],
            &["--backend", "llvm", "--release", "--target-cpu", "native"],
        ] {
            let output = run(example, flags, stdin);
            assert_eq!(
                (output.status.code(), &output.stdout),
                (reference.status.code(), &reference.stdout),
                "{example} {flags:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

#[test]
fn the_runtime_can_also_be_linked_as_a_separate_object() {
    if !clang_available() {
        return;
    }
    // Without `llvm-link` the program module is compiled alone and linked
    // against the ordinary runtime object.
    for (example, stdin) in [EXAMPLES[0], EXAMPLES[18], EXAMPLES[20]] {
        let reference = run(example, &[], stdin);
        let mut command = kush();
        let output = command
            .arg("run")
            .arg(examples().join(example))
            .args(["--backend", "llvm", "--release"])
            .env("KUSH_LLVM_NO_WHOLE_PROGRAM", "1");
        let output = if stdin.is_empty() {
            output.output().unwrap()
        } else {
            use std::io::Write;
            let mut child = output
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap();
            child
                .stdin
                .take()
                .unwrap()
                .write_all(stdin.as_bytes())
                .unwrap();
            child.wait_with_output().unwrap()
        };
        assert_eq!(
            (output.status.code(), &output.stdout),
            (reference.status.code(), &reference.stdout),
            "{example}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn build_reports_its_backend_and_can_save_the_module() {
    if !clang_available() {
        return;
    }
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("first");
    let module = scratch.path().join("first.ll");
    let output = kush()
        .arg("build")
        .arg(examples().join("first.kush"))
        .arg("-o")
        .arg(&binary)
        .args(["--release", "--backend", "llvm"])
        .env("KUSH_EMIT_LLVM", &module)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("with LLVM."));
    let text = fs::read_to_string(&module).unwrap();
    assert!(text.contains("define internal i64 @kush_entry()"), "{text}");
    assert!(text.contains("define i32 @main(i32 %argc, ptr %argv)"));
    assert!(text.contains("@llvm.smul.with.overflow.i64"));
    let ran = Command::new(&binary).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "42\n720\n42\n");
}

#[test]
fn backend_flags_are_validated_before_building() {
    for (flags, message) in [
        (&["--backend", "gcc"][..], "--backend requires"),
        (&["--target-cpu", "fast"], "--target-cpu requires"),
        (&["--backend"], "option requires a value"),
    ] {
        let output = kush()
            .arg("run")
            .arg(examples().join("first.kush"))
            .args(flags)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{flags:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{flags:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let output = kush()
        .arg("run")
        .arg(examples().join("first.kush"))
        .env("KUSH_BACKEND", "gcc")
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("KUSH_BACKEND must be"));
}

#[test]
fn a_missing_clang_is_reported_and_leaves_no_output() {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("first");
    let output = kush()
        .arg("build")
        .arg(examples().join("first.kush"))
        .arg("-o")
        .arg(&binary)
        .args(["--backend", "llvm"])
        .env("KUSH_CLANG", scratch.path().join("no-such-clang"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("the LLVM backend needs clang"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!binary.exists());
}
