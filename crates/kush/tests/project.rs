use kush::project::{self, BuildOptions, TestOptions};
use std::{
    ffi::OsString,
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

struct Scratch {
    path: PathBuf,
}

impl Scratch {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "kush project {label} {} {}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn join(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, contents).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn kush() -> Command {
    Command::new(env!("CARGO_BIN_EXE_kush"))
}

fn run_in(directory: &Path, args: &[&str]) -> Output {
    kush().current_dir(directory).args(args).output().unwrap()
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_failure(output: &Output) {
    assert!(
        !output.status.success(),
        "unexpected success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn new_scaffolds_a_project_that_builds_runs_tests_and_formats() {
    let scratch = Scratch::new("new");
    let project = scratch.join("hello world");
    let output = kush()
        .args(["new", project.to_str().unwrap(), "--name", "hello_world"])
        .output()
        .unwrap();
    assert_success(&output);
    for file in [
        "Kush.toml",
        "src/main.kush",
        "tests/main.kush",
        ".gitignore",
        "README.md",
    ] {
        assert!(project.join(file).is_file(), "missing {file}");
    }
    let manifest = fs::read_to_string(project.join("Kush.toml")).unwrap();
    assert!(manifest.contains("name = \"hello_world\""));
    assert!(manifest.contains("entry = \"src/main.kush\""));
    assert!(manifest.contains("test = \"tests/main.kush\""));

    let checked = run_in(&project, &["check"]);
    assert_success(&checked);
    assert!(String::from_utf8_lossy(&checked.stdout).contains("Checked "));

    let tested = run_in(&project, &["test"]);
    assert_success(&tested);
    let tested = String::from_utf8_lossy(&tested.stdout);
    assert!(tested.contains("test arithmetic_works ... ok"), "{tested}");
    assert!(tested.contains("2 passed; 0 failed"), "{tested}");

    let run = run_in(&project, &["run"]);
    assert_success(&run);
    assert_eq!(run.stdout, b"42\n");

    let built = run_in(&project, &["build"]);
    assert_success(&built);
    let binary = project.join("target/kush/hello_world");
    assert!(binary.is_file());
    let executed = Command::new(&binary).output().unwrap();
    assert_eq!(executed.stdout, b"42\n");

    let formatted = run_in(&project, &["fmt", "--check"]);
    assert_success(&formatted);
}

#[test]
fn local_path_dependencies_resolve_and_the_lockfile_is_deterministic() {
    let scratch = Scratch::new("dependencies");
    scratch.write(
        "dep with space/Kush.toml",
        "[package]\nname = \"math_utils\"\nversion = \"0.1.0\"\nentry = \"src/lib.kush\"\n",
    );
    scratch.write(
        "dep with space/src/lib.kush",
        "module math_utils;\n\npub fn answer() -> i64 ! {panic} {\n    6 * 7\n}\n",
    );
    scratch.write(
        "app/Kush.toml",
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.kush\"\n\n[dependencies]\nmath_utils = { path = \"../dep with space\" }\n",
    );
    scratch.write(
        "app/src/main.kush",
        "module app;\n\nuse math_utils;\n\nfn main() -> Unit ! {io, panic} {\n    print_i64(math_utils.answer());\n}\n",
    );
    let app = scratch.join("app");
    let project = project::load(&app).unwrap();
    assert_eq!(project.dependencies.len(), 1);
    assert_eq!(project.dependencies[0].name, "math_utils");
    assert_eq!(project.dependencies[0].version, "0.1.0");

    let first = project::build(&project, &BuildOptions::default()).unwrap();
    let lock_one = fs::read_to_string(app.join("Kush.lock")).unwrap();
    assert!(lock_one.contains("name = \"math_utils\""));
    assert!(lock_one.contains("path = \"../dep with space\""));
    let second = project::build(&project, &BuildOptions::default()).unwrap();
    assert_eq!(first.output, second.output);
    assert_eq!(lock_one, fs::read_to_string(app.join("Kush.lock")).unwrap());
    let executed = Command::new(&first.output).output().unwrap();
    assert_eq!(executed.stdout, b"42\n");

    scratch.write(
        "dep with space/Kush.toml",
        "[package]\nname = \"math_utils\"\nversion = \"0.2.0\"\nentry = \"src/lib.kush\"\n",
    );
    let changed = project::load(&app).unwrap();
    let locked = project::check(&changed, true).unwrap_err();
    assert!(locked.message().contains("Kush.lock is out of date"));
    project::check(&changed, false).unwrap();
    let updated = fs::read_to_string(app.join("Kush.lock")).unwrap();
    assert!(updated.contains("version = \"0.2.0\""));
    project::check(&changed, true).unwrap();
}

#[test]
fn invalid_missing_and_cyclic_dependencies_have_readable_errors() {
    let scratch = Scratch::new("invalid");

    scratch.write(
        "missing/Kush.toml",
        "[package]\nname = \"missing\"\nentry = \"src/main.kush\"\n\n[dependencies]\nnope = { path = \"../does-not-exist\" }\n",
    );
    scratch.write(
        "missing/src/main.kush",
        "module missing;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("missing")).unwrap_err();
    assert!(error.message().contains("cannot be resolved"), "{error}");

    scratch.write(
        "empty-dep/Kush.toml",
        "[package]\nname = \"empty_dep\"\nentry = \"src/main.kush\"\n\n[dependencies]\nother = { path = \"../other\" }\n",
    );
    scratch.write(
        "empty-dep/src/main.kush",
        "module empty_dep;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    fs::create_dir_all(scratch.join("other")).unwrap();
    let error = project::load(&scratch.join("empty-dep")).unwrap_err();
    assert!(error.message().contains("has no Kush.toml"), "{error}");

    scratch.write(
        "renamed/Kush.toml",
        "[package]\nname = \"renamed\"\nentry = \"src/main.kush\"\n\n[dependencies]\nalias = { path = \"../actual\" }\n",
    );
    scratch.write(
        "renamed/src/main.kush",
        "module renamed;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    scratch.write(
        "actual/Kush.toml",
        "[package]\nname = \"actual\"\nentry = \"src/main.kush\"\n",
    );
    scratch.write(
        "actual/src/main.kush",
        "module actual;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("renamed")).unwrap_err();
    assert!(
        error.message().contains("dependency keys must match"),
        "{error}"
    );

    scratch.write(
        "cycle-a/Kush.toml",
        "[package]\nname = \"cycle_a\"\nentry = \"src/main.kush\"\n\n[dependencies]\ncycle_b = { path = \"../cycle-b\" }\n",
    );
    scratch.write(
        "cycle-a/src/main.kush",
        "module cycle_a;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    scratch.write(
        "cycle-b/Kush.toml",
        "[package]\nname = \"cycle_b\"\nentry = \"src/main.kush\"\n\n[dependencies]\ncycle_a = { path = \"../cycle-a\" }\n",
    );
    scratch.write(
        "cycle-b/src/main.kush",
        "module cycle_b;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("cycle-a")).unwrap_err();
    assert!(error.message().contains("dependency cycle"), "{error}");
    assert!(
        error.message().contains("cycle_a -> cycle_b -> cycle_a"),
        "{error}"
    );

    scratch.write(
        "unknown/Kush.toml",
        "[package]\nname = \"unknown\"\nentry = \"src/main.kush\"\nunexpected = 1\n",
    );
    scratch.write(
        "unknown/src/main.kush",
        "module unknown;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("unknown")).unwrap_err();
    assert!(error.message().contains("unknown field"), "{error}");

    scratch.write(
        "escape/Kush.toml",
        "[package]\nname = \"escape\"\nentry = \"../outside.kush\"\n",
    );
    let error = project::load(&scratch.join("escape")).unwrap_err();
    assert!(error.message().contains("must stay inside"), "{error}");

    scratch.write(
        "bad-name/Kush.toml",
        "[package]\nname = \"not a name\"\nentry = \"src/main.kush\"\n",
    );
    let error = project::load(&scratch.join("bad-name")).unwrap_err();
    assert!(error.message().contains("invalid package name"), "{error}");

    scratch.write(
        "no-test/Kush.toml",
        "[package]\nname = \"no_test\"\nentry = \"src/main.kush\"\ntest = \"tests/main.kush\"\n",
    );
    scratch.write(
        "no-test/src/main.kush",
        "module no_test;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("no-test")).unwrap_err();
    assert!(error.message().contains("does not exist"), "{error}");
}

#[test]
fn dependency_name_collisions_are_rejected() {
    let scratch = Scratch::new("collision");
    scratch.write(
        "root/Kush.toml",
        "[package]\nname = \"root\"\nentry = \"src/main.kush\"\n\n[dependencies]\na = { path = \"../a\" }\nb = { path = \"../b\" }\n",
    );
    scratch.write(
        "root/src/main.kush",
        "module root;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    scratch.write(
        "a/Kush.toml",
        "[package]\nname = \"a\"\nentry = \"src/main.kush\"\n\n[dependencies]\nshared = { path = \"../shared-one\" }\n",
    );
    scratch.write(
        "a/src/main.kush",
        "module a;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    scratch.write(
        "b/Kush.toml",
        "[package]\nname = \"b\"\nentry = \"src/main.kush\"\n\n[dependencies]\nshared = { path = \"../shared-two\" }\n",
    );
    scratch.write(
        "b/src/main.kush",
        "module b;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    for directory in ["shared-one", "shared-two"] {
        scratch.write(
            &format!("{directory}/Kush.toml"),
            "[package]\nname = \"shared\"\nentry = \"src/main.kush\"\n",
        );
        scratch.write(
            &format!("{directory}/src/main.kush"),
            "module shared;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
        );
    }
    let error = project::load(&scratch.join("root")).unwrap_err();
    assert!(error.message().contains("provided by both"), "{error}");
}

#[test]
fn test_filtering_listing_failure_values_and_compile_diagnostics() {
    let scratch = Scratch::new("tests");
    scratch.write(
        "Kush.toml",
        "[package]\nname = \"tests\"\nentry = \"src/main.kush\"\ntest = \"tests/main.kush\"\n",
    );
    scratch.write(
        "src/main.kush",
        "module tests;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    scratch.write(
        "tests/main.kush",
        "module tests.tests.main;\n\nuse std.test;\n\n#[test]\nfn passes() -> Unit ! {panic} {\n    test.is_true(true);\n}\n\n#[test]\nfn fails_with_values() -> Unit ! {io, panic} {\n    test.equal_i64(1, 2);\n}\n",
    );
    let passed = run_in(&scratch.path, &["test", "passes"]);
    assert_success(&passed);
    assert!(String::from_utf8_lossy(&passed.stdout).contains("passes ... ok"));

    let failed = run_in(&scratch.path, &["test", "fails_with_values"]);
    assert_failure(&failed);
    let stdout = String::from_utf8_lossy(&failed.stdout);
    assert!(stdout.contains("FAILED"), "{stdout}");
    assert!(stdout.contains("1\n    2"), "{stdout}");
    assert!(stdout.contains("test result: FAILED"), "{stdout}");

    let listed = run_in(&scratch.path, &["test", "--list"]);
    assert_success(&listed);
    let stdout = String::from_utf8_lossy(&listed.stdout);
    assert!(stdout.contains("passes: test"), "{stdout}");
    assert!(stdout.contains("2 tests"), "{stdout}");

    let exact = run_in(&scratch.path, &["test", "passes", "--exact"]);
    assert_success(&exact);
    let none = run_in(&scratch.path, &["test", "does_not_exist", "--exact"]);
    assert_success(&none);
    assert!(String::from_utf8_lossy(&none.stdout).contains("0 passed"));

    scratch.write(
        "tests/main.kush",
        "module tests.tests.main;\n\n#[test]\nfn broken() -> Unit ! {panic} {\n    missing_name();\n}\n",
    );
    let broken = run_in(&scratch.path, &["test", "broken"]);
    assert_failure(&broken);
    let stderr = String::from_utf8_lossy(&broken.stderr);
    assert!(stderr.contains("tests/main.kush"), "{stderr}");
    assert!(stderr.contains('^'), "{stderr}");
    assert!(stderr.contains("missing_name"), "{stderr}");

    let checked = run_in(&scratch.path, &["check"]);
    assert_failure(&checked);
    let stderr = String::from_utf8_lossy(&checked.stderr);
    assert!(stderr.contains("missing_name"), "{stderr}");
}

#[test]
fn formatter_preserves_comments_and_strings_and_supports_check_mode() {
    let scratch = Scratch::new("format");
    let source = "module format;\n\
                  // keep this comment\t \n\
                  fn main() -> Unit ! {io, panic} {\n\
                  \x20   let text = \"spaces inside  \";\t \n\
                  \x20   /* block comment with trailing   \n\
                  \x20      indentation preserved   */\n\
                  \x20   print_i64(1 + 1);   \n\
                  }\n";
    let path = scratch.write("format.kush", source);
    let check = kush().args(["fmt", "--check"]).arg(&path).output().unwrap();
    assert_eq!(check.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&check.stdout).contains("would be reformatted"));

    let formatted = kush().args(["fmt"]).arg(&path).output().unwrap();
    assert_success(&formatted);
    let text = fs::read_to_string(&path).unwrap();
    assert!(text.contains("\"spaces inside  \";"), "{text}");
    assert!(text.contains("// keep this comment\n"), "{text}");
    assert!(text.contains("block comment with trailing   \n"));
    assert!(text.contains("indentation preserved   */"));
    assert!(!text.contains(");   \n"), "{text}");
    assert!(text.ends_with('\n'));

    let recheck = kush().args(["fmt", "--check"]).arg(&path).output().unwrap();
    assert_success(&recheck);

    let broken = scratch.write("broken.kush", "fn main() { \"unterminated\n");
    let before = fs::read_to_string(&broken).unwrap();
    let rejected = kush().args(["fmt"]).arg(&broken).output().unwrap();
    assert_failure(&rejected);
    assert_eq!(fs::read_to_string(&broken).unwrap(), before);
}

#[test]
fn single_file_commands_keep_working_and_program_arguments_are_forwarded() {
    let scratch = Scratch::new("single-file");
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/first.kush");
    let output = kush()
        .args([
            "run",
            source.to_str().unwrap(),
            "--stats",
            "--",
            "ignored",
            "--stats",
        ])
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(output.stdout, b"42\n720\n42\n");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("allocation-stats: "), "{stderr}");

    let quiet = kush()
        .args(["run", source.to_str().unwrap(), "--", "--stats"])
        .output()
        .unwrap();
    assert_success(&quiet);
    assert_eq!(quiet.stdout, b"42\n720\n42\n");
    assert!(!String::from_utf8_lossy(&quiet.stderr).contains("allocation-stats"));

    let invalid = kush()
        .args(["run", source.to_str().unwrap(), "--stats", "extra"])
        .output()
        .unwrap();
    assert_eq!(invalid.status.code(), Some(2));

    let binary = scratch.join("out with spaces");
    let built = kush()
        .args(["build", source.to_str().unwrap(), "-o"])
        .arg(&binary)
        .output()
        .unwrap();
    assert_success(&built);
    let executed = Command::new(&binary).output().unwrap();
    assert_eq!(executed.stdout, b"42\n720\n42\n");

    let script = scratch.join("arg printer");
    scratch.write("arg printer", "#!/bin/sh\nprintf '%s\\n' \"$@\"\n");
    fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).unwrap();
    let invocation = project::runtime::ProgramInvocation::new(
        &script,
        [
            OsString::from("one two"),
            OsString::from("--flag"),
            OsString::from(""),
        ],
    );
    assert_eq!(
        invocation.arguments(),
        [
            OsString::from("one two"),
            OsString::from("--flag"),
            OsString::from("")
        ]
    );
    let forwarded = invocation.command().output().unwrap();
    assert_success(&forwarded);
    assert_eq!(forwarded.stdout, b"one two\n--flag\n\n");
}

#[test]
fn lockfile_orders_packages_and_dependency_edges_deterministically() {
    let scratch = Scratch::new("lock-order");
    for (directory, name) in [("z-dep", "zeta"), ("a-dep", "alpha")] {
        scratch.write(
            &format!("{directory}/Kush.toml"),
            &format!(
                "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nentry = \"src/lib.kush\"\n"
            ),
        );
        scratch.write(
            &format!("{directory}/src/lib.kush"),
            &format!("module {name};\n\npub fn value() -> i64 ! {{panic}} {{ 1 }}\n"),
        );
    }
    scratch.write(
        "app/Kush.toml",
        "[package]\nname = \"app\"\nentry = \"src/main.kush\"\n\n[dependencies]\nzeta = { path = \"../z-dep\" }\nalpha = { path = \"../a-dep\" }\n",
    );
    scratch.write(
        "app/src/main.kush",
        "module app;\n\nuse alpha;\nuse zeta;\n\nfn main() -> Unit ! {io, panic} {\n    print_i64(alpha.value() + zeta.value());\n}\n",
    );
    let app = scratch.join("app");
    let project = project::load(&app).unwrap();
    project::check(&project, false).unwrap();
    let lock = fs::read_to_string(app.join("Kush.lock")).unwrap();
    let alpha = lock.find("name = \"alpha\"").unwrap();
    let zeta = lock.find("name = \"zeta\"").unwrap();
    assert!(alpha < zeta, "{lock}");
    assert!(lock.contains("dependencies = []"));
}

#[test]
fn native_extension_points_build_and_test_rust_adapters() {
    let scratch = Scratch::new("native");
    scratch.write(
        "bad/Kush.toml",
        "[package]\nname = \"bad\"\nentry = \"src/main.kush\"\n\n[native]\nlibrary-paths = [\"missing\"]\n",
    );
    scratch.write(
        "bad/src/main.kush",
        "module bad;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let error = project::load(&scratch.join("bad")).unwrap_err();
    assert!(error.message().contains("cannot be resolved"), "{error}");

    scratch.write("good/native/lib/.keep", "");
    scratch.write(
        "good/adapters/bridge/Cargo.toml",
        "[package]\nname = \"bridge\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[lib]\ncrate-type = [\"staticlib\"]\n",
    );
    scratch.write(
        "good/adapters/bridge/src/lib.rs",
        r#"#[unsafe(no_mangle)] pub extern "C" fn project_add_two(x: i64) -> i64 { x + 2 }"#,
    );
    scratch.write(
        "good/Kush.toml",
        "[package]\nname = \"good\"\nentry = \"src/main.kush\"\n\n[native]\nlibraries = [\"m\"]\nlibrary-paths = [\"native/lib\"]\ncargo-manifests = [\"adapters/bridge/Cargo.toml\"]\n",
    );
    scratch.write(
        "good/src/main.kush",
        "module good;\n\nfn main() -> Unit ! {io, panic} { print_i64(0); }\n",
    );
    let project = project::load(&scratch.join("good")).unwrap();
    assert_eq!(project.package.native.libraries, vec!["m".to_owned()]);
    assert_eq!(project.package.native.library_paths.len(), 1);
    assert_eq!(project.package.native.cargo_manifests.len(), 1);
    let built = project::build(&project, &BuildOptions::default()).unwrap();
    assert!(Command::new(built.output).status().unwrap().success());
    scratch.write(
        "good/tests/main.kush",
        r#"module good.tests.main;
        use std.test;
        foreign "project_add_two" fn add_two(x: i64) -> i64 ! {io};
        #[test] fn rust_adapter_works() -> Unit ! {io, panic} {
            test.equal_i64(add_two(40), 42);
        }"#,
    );
    let project = project::load(&scratch.join("good")).unwrap();
    let summary =
        project::test_project(&project, &TestOptions::default(), &mut Vec::new()).unwrap();
    assert_eq!(summary.passed, 1);
    assert_eq!(summary.failed, 0);
}

#[test]
fn project_commands_run_from_nested_directories_and_paths_with_spaces() {
    let scratch = Scratch::new("nested");
    let output = kush()
        .args(["new", scratch.join("space project").to_str().unwrap()])
        .output()
        .unwrap();
    assert_success(&output);
    let nested = scratch.join("space project/src");
    let checked = run_in(&nested, &["check"]);
    assert_success(&checked);
    let manifest = project::find_manifest(&nested).unwrap();
    let summary = project::test_project(
        &project::load(&manifest).unwrap(),
        &TestOptions {
            filter: None,
            exact: false,
            list: false,
            nocapture: false,
            locked: false,
        },
        &mut Vec::new(),
    )
    .unwrap();
    assert_eq!(summary.passed, 2);
    assert_eq!(summary.failed, 0);
}

#[test]
fn package_named_tests_does_not_collide_with_test_artifacts() {
    let scratch = Scratch::new("tests-package");
    let root = scratch.join("tests");
    project::new::create(&root, Some("tests")).unwrap();
    assert_success(&run_in(&root, &["test"]));
    assert_success(&run_in(&root, &["build"]));
    assert!(root.join("target/kush/tests").is_file());
    assert!(root.join("target/kush/.tests").is_dir());
    assert_success(&run_in(&root, &["test"]));
    assert_success(&run_in(&root, &["run"]));
}

#[test]
fn filtered_or_empty_tests_still_check_the_target() {
    let scratch = Scratch::new("filtered-invalid");
    let root = scratch.join("app");
    project::new::create(&root, Some("app")).unwrap();
    for body in [
        "module app.tests.main; #[test] fn real_test() -> Unit ! {panic} { missing_name(); }",
        "module app.tests.main; fn broken_helper() -> Unit ! {panic} { missing_name(); }",
    ] {
        fs::write(root.join("tests/main.kush"), body).unwrap();
        let output = run_in(&root, &["test", "absent_filter"]);
        assert_failure(&output);
        assert!(String::from_utf8_lossy(&output.stderr).contains("missing_name"));
        assert_success(&run_in(&root, &["test", "--list"]));
    }
}

#[test]
fn entry_headers_keywords_and_custom_test_locations_are_checked() {
    let scratch = Scratch::new("names-and-headers");
    for keyword in ["fn", "if", "struct", "true", "while"] {
        assert!(project::new::create(&scratch.join(keyword), Some(keyword)).is_err());
        assert!(!scratch.join(keyword).exists());
    }
    let root = scratch.join("app");
    project::new::create(&root, Some("app")).unwrap();
    for source in [
        "module app.util; fn main() -> Unit ! {} {}",
        "fn main() -> Unit ! {} {}",
    ] {
        fs::write(root.join("src/main.kush"), source).unwrap();
        assert!(
            project::load(&root)
                .unwrap_err()
                .message()
                .contains("entry module")
        );
    }
    fs::write(
        root.join("src/main.kush"),
        "module app; fn main() -> Unit ! {} {}",
    )
    .unwrap();
    fs::write(
        root.join("Kush.toml"),
        "[package]\nname = \"app\"\ntest = \"check_me.kush\"\n",
    )
    .unwrap();
    fs::write(
        root.join("check_me.kush"),
        "module app.check_me; #[test] fn works() -> Unit ! {} {}",
    )
    .unwrap();
    assert_success(&run_in(&root, &["test"]));
}

#[test]
fn unreadable_lock_and_dash_prefixed_single_file_are_handled() {
    let scratch = Scratch::new("lock-and-dash");
    let root = scratch.join("app");
    project::new::create(&root, Some("app")).unwrap();
    fs::create_dir(root.join("Kush.lock")).unwrap();
    let output = run_in(&root, &["check", "--locked"]);
    assert_failure(&output);
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("cannot read"), "{error}");
    assert!(!error.contains("is missing"));
    scratch.write(
        "-dash.kush",
        "fn main() -> Unit ! {io, panic} { print_i64(1); }",
    );
    assert_success(&run_in(&scratch.path, &["check", "-dash.kush"]));
    assert_success(&run_in(&scratch.path, &["run", "-dash.kush"]));
    assert_success(&run_in(
        &scratch.path,
        &["build", "-dash.kush", "-o", "dash-bin"],
    ));
}

#[test]
fn source_symlinks_do_not_make_build_and_format_disagree() {
    let scratch = Scratch::new("source-symlinks");
    let root = scratch.join("app");
    project::new::create(&root, Some("app")).unwrap();
    scratch.write("external.kush", "module app; fn main() -> Unit ! {} {}");
    fs::remove_file(root.join("src/main.kush")).unwrap();
    std::os::unix::fs::symlink(scratch.join("external.kush"), root.join("src/main.kush")).unwrap();
    assert!(
        project::load(&root)
            .unwrap_err()
            .message()
            .contains("symlinked source")
    );
    fs::remove_file(root.join("src/main.kush")).unwrap();
    fs::remove_dir(root.join("src")).unwrap();
    fs::create_dir(scratch.join("other-src")).unwrap();
    scratch.write(
        "other-src/main.kush",
        "module app; fn main() -> Unit ! {} {}",
    );
    std::os::unix::fs::symlink(scratch.join("other-src"), root.join("src")).unwrap();
    assert!(
        project::load(&root)
            .unwrap_err()
            .message()
            .contains("symlinked source")
    );
}
