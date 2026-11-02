use std::{path::PathBuf, process::Command};

fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_kush"))
}
fn example() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/parser.kush")
}

#[test]
fn parses_example_and_reports_syntax_only() {
    let output = command().arg("parse").arg(example()).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("syntax only"));
}
#[test]
fn ast_and_token_dumps() {
    let output = command()
        .arg("parse")
        .arg(example())
        .arg("--ast")
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("Function("));
    let output = command().arg("lex").arg(example()).output().unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("Eof"));
}
#[test]
fn usage_errors_and_missing_files_have_nonzero_exit_codes() {
    for args in [
        vec![],
        vec!["check"],
        vec!["parse"],
        vec!["lex", "x", "--ast"],
        vec!["--help", "extra"],
    ] {
        let output = command().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
    }
    let output = command()
        .args(["parse", "/this-path-does-not-exist/kush.kush"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot read"));
}
#[test]
fn help_and_version() {
    for flag in ["--help", "--version"] {
        let output = command().arg(flag).output().unwrap();
        assert!(output.status.success());
        assert!(!output.stdout.is_empty());
    }
}

fn proof_example() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/proofs.kush")
}
fn reuse_example() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/reuse.kush")
}

#[test]
fn stats_flag_writes_stable_diagnostics_to_stderr_without_changing_program_output() {
    for subcommand in ["eval", "run"] {
        let output = command()
            .arg(subcommand)
            .arg(reuse_example())
            .arg("--stats")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"100\n4\n3\n");
        let stderr = String::from_utf8(output.stderr).unwrap();
        let lines = stderr
            .lines()
            .filter(|line| line.starts_with("allocation-stats: "))
            .collect::<Vec<_>>();
        assert_eq!(lines.len(), 1, "{stderr}");
        assert!(
            lines[0].contains("allocations=5 deallocations=5")
                && lines[0].contains("reuses=100")
                && lines[0].contains("fusions=0"),
            "{stderr}"
        );
    }

    let directory = std::env::temp_dir().join(format!("kush-stats-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let binary = directory.join("program");
    let output = command()
        .arg("build")
        .arg(reuse_example())
        .arg("-o")
        .arg(&binary)
        .arg("--stats")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let run = Command::new(&binary).output().unwrap();
    assert!(run.status.success());
    assert_eq!(run.stdout, b"100\n4\n3\n");
    assert!(
        String::from_utf8(run.stderr)
            .unwrap()
            .contains("allocation-stats: allocations=5 deallocations=5")
    );
    let _ = std::fs::remove_dir_all(&directory);
}
fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

#[test]
fn check_and_resolve_commands_report_their_scope() {
    let output = command()
        .arg("resolve")
        .arg(proof_example())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("names only"));
    let output = command()
        .arg("check")
        .arg(proof_example())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .contains("8 logical definitions (restricted kernel")
    );
    let output = command()
        .arg("check")
        .arg(proof_example())
        .arg("--ast")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
}

#[test]
fn false_proofs_and_unknown_names_fail_with_source_diagnostics() {
    for (action, name, message) in [
        ("check", "false-proof.kush", "type mismatch"),
        ("resolve", "unknown-name.kush", "unknown name 'missing'"),
        ("check", "unknown-name.kush", "unknown name 'missing'"),
    ] {
        let output = command().arg(action).arg(fixture(name)).output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(error.contains(message), "{error}");
        assert!(error.contains(name) && error.contains('^'), "{error}");
    }
}

#[test]
fn enum_only_modules_use_runtime_type_checking_without_requiring_main() {
    let output = command()
        .arg("check")
        .arg(fixture("enums-only.kush"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("0 executable functions"));
}

#[test]
fn eval_and_native_run_receive_program_arguments_and_environment() {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let source = scratch.path().join("host inputs.kush");
    std::fs::write(&source, r#"use std.result.Result;
        fn main() -> Unit ! {io, alloc, panic} {
            match ENV.arg_count() { Result.Ok(n) => print_i64(n), Result.Err(_) => print_i64(-1) };
            let arg = match ENV.arg(1, Bytes.with_capacity(64)) { Result.Ok(b) => b, Result.Err(_) => Bytes.from("") };
            print_i64(Bytes.len(&arg));
            let key = Bytes.from("KUSH_CLI_HOST_TEST");
            let value = match ENV.var(&key, Bytes.with_capacity(64)) { Result.Ok(b) => b, Result.Err(_) => Bytes.from("") };
            print_i64(Bytes.len(&value));
        }"#).unwrap();
    for mode in ["eval", "run"] {
        let output = command()
            .arg(mode)
            .arg(&source)
            .args(["--", "hello world", "--flag"])
            .env("KUSH_CLI_HOST_TEST", "present")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"3\n11\n7\n");
    }
}
