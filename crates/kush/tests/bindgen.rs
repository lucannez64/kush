//! Declarative `kush bindgen` workflow: strict configuration, deterministic
//! generation, drift checks, non-destructive file handling, and an end-to-end
//! project that compiles generated Rust shims and a generated Kush module.
use kush::{
    bindgen,
    native::Scratch,
    project::{self, BuildOptions, TestOptions},
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const BRIDGE_IMPLEMENTATION: &str = r#"
mod bridge {
    use std::cell::RefCell;
    use std::sync::atomic::{AtomicI64, Ordering};
    static LIVE: AtomicI64 = AtomicI64::new(0);

    pub struct Counter { value: RefCell<i64> }
    impl Drop for Counter {
        fn drop(&mut self) { LIVE.fetch_sub(1, Ordering::SeqCst); }
    }

    pub fn double(value: i64) -> i64 { value.wrapping_mul(2) }
    pub fn scale(value: f64) -> f64 { value * 2.0 }
    pub fn flip(value: bool) -> bool { !value }
    pub fn checked_div(a: i64, b: i64) -> Result<i64, String> {
        if b == 0 { Err("division by zero".into()) } else { Ok(a / b) }
    }
    pub fn boom() -> Result<i64, String> { panic!("adapter exploded") }
    pub fn upper(text: &str) -> Result<Vec<u8>, String> {
        Ok(text.bytes().map(|byte| byte.to_ascii_uppercase()).collect())
    }
    pub fn counter_new(start: i64) -> Counter {
        LIVE.fetch_add(1, Ordering::SeqCst);
        Counter { value: RefCell::new(start) }
    }
    pub fn counter_add(counter: &Counter, increment: i64) -> Result<i64, String> {
        let mut value = counter.value.borrow_mut();
        *value += increment;
        Ok(*value)
    }
    pub fn live() -> i64 { LIVE.load(Ordering::SeqCst) }
}
"#;

const BRIDGE_CONFIG: &str = r#"
[adapter]
module = "app.generated"
rust-output = "generated output/ffi.rs"
kush-output = "src/generated.kush"

[[resource]]
name = "Counter"
rust-type = "crate::bridge::Counter"
release-symbol = "kush_test_counter_release"

[[function]]
name = "double"
symbol = "kush_test_double"
rust-path = "crate::bridge::double"
parameters = [{ name = "value", type = "i64" }]
result = "i64"

[[function]]
name = "scale"
symbol = "kush_test_scale"
rust-path = "crate::bridge::scale"
parameters = [{ name = "value", type = "f64" }]
result = "f64"

[[function]]
name = "flip"
symbol = "kush_test_flip"
rust-path = "crate::bridge::flip"
parameters = [{ name = "value", type = "bool" }]
result = "bool"

[[function]]
name = "checked_div"
symbol = "kush_test_checked_div"
rust-path = "crate::bridge::checked_div"
parameters = [
  { name = "a", type = "i64" },
  { name = "b", type = "i64" },
]
result = "i64"
fallible = true

[[function]]
name = "boom"
symbol = "kush_test_boom"
rust-path = "crate::bridge::boom"
result = "i64"
fallible = true

[[function]]
name = "upper"
symbol = "kush_test_upper"
rust-path = "crate::bridge::upper"
parameters = [{ name = "text", type = "text" }]
result = "bytes"
fallible = true

[[function]]
name = "counter_new"
symbol = "kush_test_counter_new"
rust-path = "crate::bridge::counter_new"
parameters = [{ name = "start", type = "i64" }]
result = { resource = "Counter" }

[[function]]
name = "counter_add"
symbol = "kush_test_counter_add"
rust-path = "crate::bridge::counter_add"
parameters = [
  { name = "counter", resource = "Counter" },
  { name = "increment", type = "i64" },
]
result = "i64"
fallible = true

[[function]]
name = "live"
symbol = "kush_test_live"
rust-path = "crate::bridge::live"
result = "i64"
"#;

fn write(path: &Path, text: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, text).unwrap();
}

fn scratch() -> (Scratch, PathBuf) {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let project = scratch.path().join("adapter project");
    fs::create_dir_all(&project).unwrap();
    (scratch, project)
}

fn generate_project(project: &Path) -> PathBuf {
    let config = project.join("Bridge.toml");
    write(&config, BRIDGE_CONFIG);
    write(
        &project.join("Kush.toml"),
        "[package]\n\
         name = \"app\"\n\
         version = \"0.1.0\"\n\
         entry = \"main.kush\"\n\
         test = \"tests/main.kush\"\n\n\
         [native]\n\
         libraries = [\"libapp_adapter.a\", \"pthread\", \"dl\"]\n",
    );
    write(
        &project.join("main.kush"),
        r#"module app;

use std.result.Result;
use app.generated;

fn write_line(text: &Bytes) -> Unit ! {io, alloc, panic} {
    match IO.write(IO.stdout(), text) { Ok(_) => (), Err(_) => () };
    match IO.write(IO.stdout(), &Bytes.from("\n")) { Ok(_) => (), Err(_) => () }
}

fn main() -> Unit ! {io, alloc, panic} {
    print_i64(generated.double(21));
    print_i64(if generated.scale(4.5) == 9.0 { 1 } else { 0 });
    print_i64(if generated.flip(true) == false { 1 } else { 0 });
    print_i64(match generated.checked_div(9, 3) { Ok(value) => value, Err(_) => 0 });
    print_i64(match generated.checked_div(1, 0) { Ok(_) => 0, Err(code) => code });
    print_i64(match generated.boom() { Ok(_) => 0, Err(code) => code });
    write_line(&match generated.last_error() {
        Ok(message) => message,
        Err(_) => Bytes.from("last_error unavailable"),
    });

    let text = String.from("rust");
    let view: &str = String.as_str(&text);
    let upper = match generated.upper(view) {
        Ok(value) => value,
        Err(_) => Bytes.from(""),
    };
    print_i64(Bytes.len(&upper));
    print_i64(Bytes.get(&upper, 0));

    let combined = {
        let counter = generated.counter_new(40);
        let first = match generated.counter_add(&counter, 1) { Ok(value) => value, Err(_) => 0 };
        let second = match generated.counter_add(&counter, 2) { Ok(value) => value, Err(_) => 0 };
        first + second
    };
    print_i64(combined);
    print_i64(generated.live());
}
"#,
    );
    write(
        &project.join("tests/main.kush"),
        r#"module app.tests.main;

use std.result.Result;
use std.test;
use app.generated;

#[test]
fn adapter_is_callable_from_tests() -> Unit ! {io, alloc, panic} {
    test.equal_i64(generated.double(21), 42);
    test.equal_i64(match generated.checked_div(1, 0) { Ok(_) => 0, Err(code) => code }, 1);
}

#[test]
fn adapter_exposes_error_text() -> Unit ! {io, alloc, panic} {
    let _ = generated.checked_div(1, 0);
    let message = match generated.last_error() {
        Ok(value) => value,
        Err(_) => Bytes.from(""),
    };
    test.is_true(Bytes.len(&message) > 0);
}
"#,
    );
    let report = bindgen::run(&config, false).unwrap();
    assert!(report.changed());
    assert!(report.rust_path.ends_with("generated output/ffi.rs"));
    assert!(report.kush_path.ends_with("src/generated.kush"));
    project.join("Bridge.toml")
}

fn compile_generated_rust(project: &Path) -> PathBuf {
    let generated = fs::read_to_string(project.join("generated output/ffi.rs")).unwrap();
    assert!(generated.contains("kush_test_counter_release"));
    assert!(generated.contains("kush_app_generated_bridge_last_error_bytes"));
    assert!(generated.contains("catch_unwind"));
    let source = project.join("adapter crate root.rs");
    write(&source, &format!("{generated}\n{BRIDGE_IMPLEMENTATION}"));
    let archive = project.join("libapp_adapter.a");
    let output = Command::new("rustc")
        .arg("--edition=2024")
        .arg("--crate-name")
        .arg("app_adapter_bridge")
        .arg("--crate-type=staticlib")
        .arg("-C")
        .arg("panic=unwind")
        .arg("-o")
        .arg(&archive)
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "rustc failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    archive
}

#[test]
fn bindgen_project_build_run_and_tests_reuse_safe_rust() {
    let (_scratch, project) = scratch();
    generate_project(&project);
    let archive = compile_generated_rust(&project);
    assert!(archive.is_file());

    let kush_manifest = project.join("Kush.toml");
    let project = project::load(&kush_manifest).unwrap();
    let binary = project.root.join("target/app-adapter");
    let built = project::build(
        &project,
        &BuildOptions {
            output: Some(binary.clone()),
            stats: false,
            locked: false,
        },
    )
    .unwrap();
    assert_eq!(built.output, binary);
    let output = Command::new(&binary).output().unwrap();
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "42\n1\n1\n3\n1\n2\nkush_test_boom panicked: adapter exploded\n4\n82\n84\n0\n"
    );

    let mut test_output = Vec::new();
    let summary = project::test_project(
        &project,
        &TestOptions {
            filter: None,
            exact: false,
            list: false,
            nocapture: false,
            locked: false,
        },
        &mut test_output,
    )
    .unwrap();
    assert_eq!(summary.passed, 2, "{summary:?}");
    assert_eq!(summary.failed, 0);
    let test_output = String::from_utf8(test_output).unwrap();
    assert!(test_output.contains("test adapter_is_callable_from_tests ... ok"));
    assert!(test_output.contains("test adapter_exposes_error_text ... ok"));
}

fn smoke_config(dir: &Path, body: &str) -> PathBuf {
    let config = dir.join("Bridge.toml");
    write(&config, body);
    config
}

fn minimal_config(extra: &str) -> String {
    format!(
        "[adapter]\n\
         module = \"app.generated\"\n\
         rust-output = \"src/ffi.rs\"\n\
         kush-output = \"src/generated.kush\"\n\n\
         [[function]]\n\
         name = \"answer\"\n\
         symbol = \"kush_test_answer\"\n\
         rust-path = \"crate::bridge::answer\"\n\
         parameters = [{{ name = \"value\", type = \"i64\" }}]\n\
         result = \"i64\"\n\n\
         {extra}"
    )
}

#[test]
fn check_reports_drift_without_writing_and_generation_is_deterministic() {
    let (_scratch, project) = scratch();
    let config = smoke_config(&project, &minimal_config(""));
    let report = bindgen::run(&config, true).unwrap();
    assert!(report.changed());
    assert!(!project.join("src/ffi.rs").exists());
    assert!(!project.join("src/generated.kush").exists());

    let first = bindgen::run(&config, false).unwrap();
    assert!(first.changed());
    let rust = fs::read(project.join("src/ffi.rs")).unwrap();
    let kush = fs::read(project.join("src/generated.kush")).unwrap();
    let second = bindgen::run(&config, false).unwrap();
    assert!(!second.changed());
    assert_eq!(fs::read(project.join("src/ffi.rs")).unwrap(), rust);
    assert_eq!(fs::read(project.join("src/generated.kush")).unwrap(), kush);
    assert!(!bindgen::run(&config, true).unwrap().changed());

    let mut edited = String::from_utf8(rust.clone()).unwrap();
    edited.push_str("// local edit with the generated marker retained\n");
    fs::write(project.join("src/ffi.rs"), &edited).unwrap();
    let drift = bindgen::run(&config, true).unwrap();
    assert!(drift.rust_changed);
    assert!(!drift.kush_changed);
    assert_eq!(
        fs::read_to_string(project.join("src/ffi.rs")).unwrap(),
        edited
    );
}

#[test]
fn bindgen_refuses_to_overwrite_handwritten_files_or_follow_symlinks() {
    let (_scratch, project) = scratch();
    let config = smoke_config(&project, &minimal_config(""));
    write(
        &project.join("src/ffi.rs"),
        "// handwritten, do not replace\n",
    );
    let error = bindgen::run(&config, false).unwrap_err().to_string();
    assert!(error.contains("refusing to overwrite"), "{error}");
    assert_eq!(
        fs::read_to_string(project.join("src/ffi.rs")).unwrap(),
        "// handwritten, do not replace\n"
    );
    assert!(!project.join("src/generated.kush").exists());

    fs::remove_file(project.join("src/ffi.rs")).unwrap();
    let victim = project.join("victim.rs");
    write(&victim, "// user file\n");
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&victim, project.join("src/ffi.rs")).unwrap();
        let error = bindgen::run(&config, false).unwrap_err().to_string();
        assert!(error.contains("symbolic link"), "{error}");
        assert_eq!(fs::read_to_string(&victim).unwrap(), "// user file\n");
        fs::remove_file(project.join("src/ffi.rs")).unwrap();
    }

    let real = project.join("real");
    fs::create_dir(&real).unwrap();
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&real, project.join("linked")).unwrap();
        let linked_config = smoke_config(
            &project,
            &minimal_config("").replace(
                "rust-output = \"src/ffi.rs\"",
                "rust-output = \"linked/ffi.rs\"",
            ),
        );
        let error = bindgen::run(&linked_config, false).unwrap_err().to_string();
        assert!(error.contains("symbolic link"), "{error}");
    }
    let _ = config;
}

#[test]
fn invalid_configs_report_unknown_keys_collisions_and_reserved_symbols() {
    let (_scratch, project) = scratch();
    let config = smoke_config(&project, &minimal_config(""));
    let prefix = "kush_app_generated_bridge";
    let cases = [
        (
            minimal_config("unknown = true\n"),
            "unknown field 'unknown'",
        ),
        (
            minimal_config("")
                .replace("result = \"i64\"", "result = \"i64\"\nextra-field = \"no\""),
            "unknown field 'extra-field'",
        ),
        (
            minimal_config("").replace("crate::bridge::answer", "crate::bridge::answer()"),
            "Rust function path",
        ),
        (
            minimal_config("").replace("result = \"i64\"", "result = \"text\""),
            "owned text result",
        ),
        (
            minimal_config("").replace("result = \"i64\"", "result = \"widget\""),
            "result must be one of",
        ),
        (
            minimal_config("").replace("kush_test_answer", "kush_bytes_from"),
            "reserved by the generated bridge support",
        ),
        (
            minimal_config("").replace("kush_test_answer", &format!("{prefix}_last_error_bytes")),
            "reserved by the generated bridge support",
        ),
        (
            minimal_config("").replace("name = \"answer\"", "name = \"last_error\""),
            "reserved for the generated error accessor",
        ),
        (
            minimal_config("").replace("result = \"i64\"", "result = { resource = \"Missing\" }"),
            "undeclared resource",
        ),
        (
            minimal_config("")
                .replace("name = \"answer\"", "name = \"answer\"\nfallible = \"yes\""),
            "fallible must be a boolean",
        ),
        (
            minimal_config("").replace(
                "rust-output = \"src/ffi.rs\"",
                "rust-output = \"src/generated.kush\"",
            ),
            "must be different files",
        ),
        (
            minimal_config("").replace(
                "rust-output = \"src/ffi.rs\"",
                "rust-output = \"/tmp/ffi.rs\"",
            ),
            "must be relative",
        ),
        (
            minimal_config("").replace(
                "rust-output = \"src/ffi.rs\"",
                "rust-output = \"../ffi.rs\"",
            ),
            "must stay inside",
        ),
        (
            minimal_config("").replace(
                "rust-output = \"src/ffi.rs\"",
                "rust-output = \"Bridge.toml\"",
            ),
            "would overwrite the configuration file",
        ),
        (
            minimal_config("").replace("name = \"answer\"", "name = \"type\""),
            "identifier and not a keyword",
        ),
        (
            minimal_config("").replace(
                "parameters = [{ name = \"value\", type = \"i64\" }]",
                "parameters = [{ name = \"kush_out\", type = \"i64\" }]",
            ),
            "reserved for the generated result slot",
        ),
        (
            minimal_config("").replace(
                "parameters = [{ name = \"value\", type = \"i64\" }]",
                "parameters = [{ name = \"value\", type = \"bytes\" }, { name = \"value_data\", type = \"i64\" }]",
            ),
            "generated C parameter name",
        ),
        (
            minimal_config("").replace("kush_test_answer", "match"),
            "Rust keyword",
        ),
        (
            minimal_config("").replace(
                "crate::bridge::answer",
                "crate::bridge::match",
            ),
            "Rust keyword",
        ),
    ];
    for (body, expected) in cases {
        write(&config, &body);
        let error = bindgen::run(&config, true).unwrap_err().to_string();
        assert!(
            error.contains(expected),
            "expected {expected:?} in error: {error}"
        );
    }

    let duplicate_resource = minimal_config("").replace(
        "[[function]]",
        "[[resource]]\n\
         name = \"Handle\"\n\
         rust-type = \"crate::bridge::Handle\"\n\
         release-symbol = \"kush_test_handle_release\"\n\n\
         [[resource]]\n\
         name = \"Handle\"\n\
         rust-type = \"crate::bridge::Other\"\n\
         release-symbol = \"kush_test_other_release\"\n\n\
         [[function]]",
    );
    write(&config, &duplicate_resource);
    let error = bindgen::run(&config, true).unwrap_err().to_string();
    assert!(error.contains("duplicate resource name"), "{error}");

    let duplicate_symbol = minimal_config(
        "[[function]]\n\
         name = \"second\"\n\
         symbol = \"kush_test_answer\"\n\
         rust-path = \"crate::bridge::second\"\n\
         result = \"i64\"\n",
    );
    write(&config, &duplicate_symbol);
    let error = bindgen::run(&config, true).unwrap_err().to_string();
    assert!(error.contains("duplicate generated symbol"), "{error}");

    let duplicate_name = minimal_config(
        "[[function]]\n\
         name = \"answer\"\n\
         symbol = \"kush_test_second\"\n\
         rust-path = \"crate::bridge::second\"\n\
         result = \"i64\"\n",
    );
    write(&config, &duplicate_name);
    let error = bindgen::run(&config, true).unwrap_err().to_string();
    assert!(error.contains("duplicate Kush function name"), "{error}");

    write(
        &config,
        "[adapter]\n\
         module = \"std.generated\"\n\
         rust-output = \"src/ffi.rs\"\n\
         kush-output = \"src/generated.kush\"\n\n\
         [[function]]\n\
         name = \"answer\"\n\
         symbol = \"kush_test_answer\"\n\
         rust-path = \"crate::bridge::answer\"\n\
         result = \"i64\"\n",
    );
    let error = bindgen::run(&config, true).unwrap_err().to_string();
    assert!(error.contains("reserved 'std' module prefix"), "{error}");
}

fn compile_staticlib(root: &Path, name: &str, source: &str) -> PathBuf {
    let source_path = root.join(format!("{name}.rs"));
    write(&source_path, source);
    let archive = root.join(format!("lib{name}.a"));
    let output = Command::new("rustc")
        .arg("--edition=2024")
        .arg("--crate-name")
        .arg(name)
        .arg("--crate-type=staticlib")
        .arg("-C")
        .arg("panic=unwind")
        .arg("-o")
        .arg(&archive)
        .arg(&source_path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "rustc failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    archive
}

fn one_function_config(module: &str, symbol: &str) -> String {
    format!(
        "[adapter]\n\
         module = \"{module}\"\n\
         rust-output = \"{module}/ffi.rs\"\n\
         kush-output = \"{module}.kush\"\n\n\
         [[function]]\n\
         name = \"answer\"\n\
         symbol = \"{symbol}\"\n\
         rust-path = \"crate::bridge::answer\"\n\
         result = \"i64\"\n"
    )
}

#[test]
fn two_generated_adapters_link_without_helper_symbol_collisions_and_include_works() {
    let (_scratch, root) = scratch();
    let one_config = root.join("one-Bridge.toml");
    let two_config = root.join("two-Bridge.toml");
    write(&one_config, &one_function_config("one", "kush_one_answer"));
    write(&two_config, &one_function_config("two", "kush_two_answer"));
    bindgen::run(&one_config, false).unwrap();
    bindgen::run(&two_config, false).unwrap();

    let one_generated = fs::read_to_string(root.join("one/ffi.rs")).unwrap();
    let two_generated = fs::read_to_string(root.join("two/ffi.rs")).unwrap();
    assert!(!one_generated.contains("#![allow"));
    assert!(one_generated.contains("kush_one_bridge_last_error_bytes"));
    assert!(two_generated.contains("kush_two_bridge_last_error_bytes"));
    assert!(!one_generated.contains("kush_two_bridge_last_error"));

    let one_source = format!(
        "mod bridge {{ pub fn answer() -> i64 {{ 1 }} }}\nmod adapter {{\ninclude!(r#\"{}\"#);\n}}\n",
        root.join("one/ffi.rs").display()
    );
    let two_source = format!("{two_generated}\nmod bridge {{ pub fn answer() -> i64 {{ 2 }} }}\n");
    let one_archive = compile_staticlib(&root, "one_adapter", &one_source);
    let two_archive = compile_staticlib(&root, "two_adapter", &two_source);

    let main = root.join("main.kush");
    write(
        &main,
        "module app;\n\
         use std.result.Result;\n\
         use one;\n\
         use two;\n\
         fn main() -> i64 ! {io, alloc, panic} {\n\
         \x20   let first = one.answer();\n\
         \x20   let second = two.answer();\n\
         \x20   let first_error = match one.last_error() { Ok(_) => 0, Err(code) => code };\n\
         \x20   let second_error = match two.last_error() { Ok(_) => 0, Err(code) => code };\n\
         \x20   if first == 1 && second == 2 && first_error == 1 && second_error == 1 { 42 } else { 0 }\n\
         }\n",
    );
    let program = kush::program::load_path(&main).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    let binary = root.join("two-adapters");
    kush::native::build_with_options(
        &checked,
        &binary,
        false,
        &kush::native::LinkSpec {
            libraries: vec![one_archive, two_archive],
            system_libraries: vec!["pthread".into(), "dl".into()],
            ..kush::native::LinkSpec::default()
        },
    )
    .unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(42),
        "stdout: {} stderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn generated_adapter_rejects_panic_abort_builds() {
    let (_scratch, root) = scratch();
    let config = smoke_config(&root, &minimal_config(""));
    bindgen::run(&config, false).unwrap();
    let generated = fs::read_to_string(root.join("src/ffi.rs")).unwrap();
    let source = root.join("abort-root.rs");
    write(
        &source,
        &format!("{generated}\nmod bridge {{ pub fn answer() -> i64 {{ 42 }} }}\n"),
    );
    let output = Command::new("rustc")
        .arg("--edition=2024")
        .arg("--crate-name")
        .arg("abort_adapter")
        .arg("--crate-type=staticlib")
        .arg("-C")
        .arg("panic=abort")
        .arg("-o")
        .arg(root.join("libabort.a"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("panic=unwind"), "{stderr}");
}

#[test]
fn bindgen_cli_reports_check_drift_and_usage_errors() {
    let (_scratch, root) = scratch();
    let config = smoke_config(&root, &minimal_config(""));
    let binary = env!("CARGO_BIN_EXE_kush");

    let missing = Command::new(binary).arg("bindgen").output().unwrap();
    assert_eq!(missing.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&missing.stderr).contains("requires a Bridge.toml path"));

    let drift = Command::new(binary)
        .arg("bindgen")
        .arg(&config)
        .arg("--check")
        .output()
        .unwrap();
    assert_eq!(drift.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&drift.stdout).contains("would update"));

    let generated = Command::new(binary)
        .arg("bindgen")
        .arg(&config)
        .output()
        .unwrap();
    assert_eq!(generated.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&generated.stdout).contains("Generated"));

    let clean = Command::new(binary)
        .arg("bindgen")
        .arg(&config)
        .arg("--check")
        .output()
        .unwrap();
    assert_eq!(clean.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&clean.stdout).contains("up to date"));
}

#[test]
fn temporary_symlinks_are_not_followed_and_private_modes_stay_private() {
    use std::os::unix::fs::{PermissionsExt, symlink};
    let (_scratch, project) = scratch();
    let config = smoke_config(&project, &minimal_config(""));
    let victim = project.join("victim.rs");
    write(&victim, "private user data");
    fs::create_dir_all(project.join("src")).unwrap();
    let old_temporary = project.join(format!("src/.ffi.rs.kush-bindgen-{}", std::process::id()));
    symlink(&victim, &old_temporary).unwrap();
    bindgen::run(&config, false).unwrap();
    assert_eq!(fs::read_to_string(&victim).unwrap(), "private user data");
    assert!(
        fs::symlink_metadata(&old_temporary)
            .unwrap()
            .file_type()
            .is_symlink()
    );
    let output = project.join("src/ffi.rs");
    fs::set_permissions(&output, fs::Permissions::from_mode(0o600)).unwrap();
    let text = fs::read_to_string(&config).unwrap();
    let changed = text.replace("kush_test_answer", "kush_changed_answer");
    assert_ne!(changed, text);
    fs::write(&config, changed).unwrap();
    assert!(bindgen::run(&config, false).unwrap().changed());
    assert_eq!(
        fs::metadata(output).unwrap().permissions().mode() & 0o777,
        0o600
    );
}
