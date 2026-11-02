//! Native Rust/C interop: checked foreign declarations, the C bridge ABI,
//! linking supplied static objects, generated Rust adapters, panic containment,
//! opaque resource release, and clear reference-interpreter rejection.
use kush::executable::check;
use kush::interop::{AdapterSpec, Function, Parameter, Resource, ResultType, Scalar};
use kush::native::{LinkSpec, Scratch, build_with_options};
use std::fs;
use std::process::Command;

const RESULT: &str = "enum Result<T, E> { Ok(T), Err(E) }\n";

fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
}

fn cc(args: &[&str]) {
    let output = Command::new("cc").args(args).output().unwrap();
    assert!(
        output.status.success(),
        "cc failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

const C_LIBRARY: &str = r#"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int64_t value; } Counter;
static int64_t live = 0;

int64_t kush_test_add(int64_t a, int64_t b) { return a + b; }

int32_t kush_test_mul32(int32_t a, int32_t b) { return a * b; }
double kush_test_half(double x) { return x / 2.0; }
int8_t kush_test_neg8(int8_t x) { return (int8_t)-x; }
int32_t kush_test_flag(int32_t flag) { return flag ? 7 : 3; }

typedef struct { uint64_t length; uint64_t capacity; unsigned char data[]; } KushBytes;
extern uint64_t kush_bytes_from(const unsigned char *source, int64_t length);

int64_t kush_test_upper(const uint8_t *data, int64_t length, int64_t *out) {
    if (length < 0) return 3;
    if (length > 0 && data == NULL) return 4;
    KushBytes *buffer = (KushBytes *)(uintptr_t)kush_bytes_from(data, length);
    if (buffer == NULL) return 5;
    for (int64_t i = 0; i < length; i++) {
        uint8_t c = buffer->data[i];
        buffer->data[i] = (c >= 'a' && c <= 'z') ? (uint8_t)(c - 32) : c;
    }
    *out = (int64_t)(uintptr_t)buffer;
    return 0;
}

int64_t kush_test_div(int64_t a, int64_t b, int64_t *out) {
    if (b == 0) return 7;
    *out = a / b;
    return 0;
}

int64_t kush_test_counter_new(int64_t start) {
    Counter *counter = (Counter *)malloc(sizeof(Counter));
    if (counter == NULL) return 0;
    counter->value = start;
    live++;
    return (int64_t)(uintptr_t)counter;
}

int64_t kush_test_counter_add(int64_t handle, int64_t n) {
    Counter *counter = (Counter *)(uintptr_t)handle;
    if (counter == NULL) return -1;
    counter->value += n;
    return counter->value;
}

void kush_test_counter_release(int64_t handle) {
    if (handle == 0) return;
    free((void *)(uintptr_t)handle);
    live--;
}

int64_t kush_test_take_plus(int64_t handle, int64_t n) {
    Counter *counter = (Counter *)(uintptr_t)handle;
    int64_t result = counter->value + n;
    kush_test_counter_release(handle);
    return result;
}
int64_t kush_test_counter_try(int64_t start, int64_t *out) {
    *out = kush_test_counter_new(start); return 0;
}
uint64_t kush_test_echo_u64(uint64_t x) { return x; }
int64_t kush_test_live(void) { return live; }
"#;

fn build_c_library(directory: &std::path::Path) -> std::path::PathBuf {
    let source = directory.join("native.c");
    let object = directory.join("native.o");
    let archive = directory.join("libkushffi.a");
    fs::write(&source, C_LIBRARY).unwrap();
    cc(&[
        "-std=c11",
        "-O2",
        "-fPIC",
        "-c",
        source.to_str().unwrap(),
        "-o",
        object.to_str().unwrap(),
    ]);
    let output = Command::new("ar")
        .args(["crs", archive.to_str().unwrap(), object.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "ar failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    archive
}

#[test]
fn foreign_declarations_require_io_and_the_supported_c_abi() {
    rejects(
        "foreign \"f\" fn f(x: i64) -> i64 ! {};\nfn main() -> i64 ! {} { 0 }",
        "requires the 'io' effect",
    );
    rejects(
        "foreign \"f\" fn f(x: String) -> i64 ! {io};\nfn main() -> i64 ! {} { 0 }",
        "not part of the stable C bridge ABI",
    );
    rejects(
        "foreign \"f\" fn f<T: Type>(x: T) -> i64 ! {io};\nfn main() -> i64 ! {} { 0 }",
        "cannot be generic",
    );
    rejects(
        "foreign \"f\" fn f(x: i64) -> i64 ! {io};\nfn take(g: fn(i64) -> i64 ! {io}) -> i64 ! {io} { g(1) }\nfn main() -> i64 ! {io} { take(f) }",
        "can only be called directly",
    );
    rejects(
        "#[foreign(\"1bad\")] struct Handle {}\nfn main() -> i64 ! {} { 0 }",
        "C identifier",
    );
    rejects(
        "#[linear(\"x\")] struct Data {}\nfn main() -> i64 ! {} { 0 }",
        "data declarations support",
    );
    rejects(
        "#[foreign(\"release\")] struct Handle { value: i64 }\nfn main() -> i64 ! {} { 0 }",
        "opaque and has no fields",
    );
    let executable = check(
        "foreign \"f\" fn f(x: u8, flag: Bool, data: &String) -> f32 ! {io};\n\
         fn main() -> i64 ! {} { 0 }",
    )
    .unwrap();
    assert_eq!(executable.foreign_functions().len(), 1);
    assert_eq!(executable.foreign_functions()[0].symbol, "f");
    assert!(!executable.foreign_functions()[0].fallible);
}

#[test]
fn foreign_resources_move_once_and_linear_resources_need_explicit_consumption() {
    let moved = check(
        "#[foreign(\"release\")] struct Handle {}\n\
         foreign \"make\" fn make() -> Handle ! {io};\n\
         foreign \"take\" fn take(value: Handle) -> i64 ! {io};\n\
         fn main() -> i64 ! {io, panic} { let value = make(); let first = take(value); take(value) + first }",
    )
    .unwrap_err();
    assert!(
        moved.message.contains("moved") || moved.message.contains("use"),
        "{moved:?}"
    );
    // A linear foreign resource cannot be dropped implicitly; it must be
    // explicitly consumed exactly once.
    let dropped = check(
        "#[linear] #[foreign(\"release\")] struct Handle {}\n\
         foreign \"make\" fn make() -> Handle ! {io};\n\
         fn main() -> i64 ! {io, panic} { let value = make(); 0 }",
    )
    .unwrap_err();
    assert!(
        dropped.message.contains("not consumed") || dropped.message.contains("linear"),
        "{dropped:?}"
    );
}

#[test]
fn fallible_foreign_results_require_i64_errors() {
    rejects(
        &format!(
            "{RESULT} foreign \"f\" fn f(x: i64) -> Result<i64, Bool> ! {{io}};\nfn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "must use i64 as its error type",
    );
    let executable = check(&format!(
        "{RESULT} foreign \"f\" fn f(x: i64) -> Result<i64, i64> ! {{io}};\nfn main() -> i64 ! {{}} {{ 0 }}"
    ))
    .unwrap();
    assert!(executable.foreign_functions()[0].fallible);
}

#[test]
fn reference_interpreter_rejects_foreign_calls_instead_of_guessing() {
    let program = check(
        "foreign \"f\" fn f(x: i64) -> i64 ! {io};\n\
         fn main() -> i64 ! {io} { f(1) }",
    )
    .unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("native backend"), "{error:?}");
    assert!(error.message.contains("rejects host FFI"), "{error:?}");
}

#[test]
fn c_static_library_round_trips_scalars_bytes_errors_and_resources() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let archive = build_c_library(scratch.path());
    let source = format!(
        "{RESULT}
        #[foreign(\"kush_test_counter_release\")] struct Counter {{}}
        foreign \"kush_test_add\" fn add(a: i64, b: i64) -> i64 ! {{io}};
        foreign \"kush_test_mul32\" fn mul32(a: i32, b: i32) -> i32 ! {{io}};
        foreign \"kush_test_half\" fn half(x: f64) -> f64 ! {{io}};
        foreign \"kush_test_neg8\" fn neg8(x: i8) -> i8 ! {{io}};
        foreign \"kush_test_flag\" fn flag(value: Bool) -> i32 ! {{io}};
        foreign \"kush_test_upper\" fn upper(data: &Bytes) -> Result<Bytes, i64> ! {{io}};
        foreign \"kush_test_div\" fn divide(a: i64, b: i64) -> Result<i64, i64> ! {{io}};
        foreign \"kush_test_counter_new\" fn counter_new(start: i64) -> Counter ! {{io}};
        foreign \"kush_test_counter_add\" fn counter_add(counter: &Counter, n: i64) -> i64 ! {{io}};
        foreign \"kush_test_live\" fn live() -> i64 ! {{io}};
        fn main() -> Unit ! {{io, alloc, panic}} {{
            print_i64(add(20, 22));
            print_i64(if mul32(6, 7) == 42 {{ 1 }} else {{ 0 }});
            print_i64(if half(9.0) == 4.5 {{ 1 }} else {{ 0 }});
            print_i64(if neg8(-5) == 5 {{ 1 }} else {{ 0 }});
            print_i64(if flag(true) == 7 {{ 1 }} else {{ 0 }});
            let text = Bytes.from(\"hello\");
            let uppercase = match upper(&text) {{
                Ok(value) => value,
                Err(code) => Bytes.from(\"\"),
            }};
            print_i64(Bytes.len(&uppercase));
            print_i64(Bytes.get(&uppercase, 0));
            print_i64(Bytes.get(&uppercase, 4));
            let quotient = match divide(84, 2) {{ Ok(n) => n, Err(code) => 0 - code }};
            print_i64(quotient);
            let failure = match divide(1, 0) {{ Ok(_) => 0, Err(code) => code }};
            print_i64(failure);
            let combined = {{
                let counter = counter_new(5);
                let first = counter_add(&counter, 2);
                let second = counter_add(&counter, 3);
                first + second
            }};
            print_i64(combined);
            print_i64(live());
        }}"
    );
    let executable = check(&source).unwrap_or_else(|error| {
        let start = error.span.start.saturating_sub(40);
        let end = (error.span.end + 40).min(source.len());
        panic!("{error:?}\nsource around span: {:?}", &source[start..end]);
    });
    let binary = scratch.path().join("ffi-c");
    build_with_options(
        &executable,
        &binary,
        false,
        &LinkSpec {
            libraries: vec![archive],
            ..LinkSpec::default()
        },
    )
    .unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "42\n1\n1\n1\n1\n5\n72\n79\n42\n7\n17\n0\n"
    );
}

#[test]
fn link_inputs_may_contain_spaces_and_failures_leave_the_output_intact() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let native = scratch.path().join("native libs");
    fs::create_dir(&native).unwrap();
    let archive = build_c_library(&native);
    let executable = check(
        "foreign \"kush_test_add\" fn add(a: i64, b: i64) -> i64 ! {io};\n\
         fn main() -> i64 ! {io} { add(2, 3) }",
    )
    .unwrap();
    let binary = scratch.path().join("spaced-output");
    build_with_options(
        &executable,
        &binary,
        false,
        &LinkSpec {
            libraries: vec![archive],
            ..LinkSpec::default()
        },
    )
    .unwrap();
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(5));

    let before = fs::read(&binary).unwrap();
    let missing = scratch.path().join("missing library.a");
    let error = build_with_options(
        &executable,
        &binary,
        false,
        &LinkSpec {
            libraries: vec![missing],
            ..LinkSpec::default()
        },
    )
    .unwrap_err();
    assert!(error.message.contains("native link failed"), "{error:?}");
    assert_eq!(
        fs::read(&binary).unwrap(),
        before,
        "failed build replaced the executable"
    );
    assert!(
        build_with_options(
            &executable,
            &binary,
            false,
            &LinkSpec {
                system_libraries: vec!["--evil".into()],
                ..LinkSpec::default()
            },
        )
        .is_err()
    );
}

fn rust_adapter_spec() -> AdapterSpec {
    AdapterSpec {
        resources: vec![Resource {
            name: "Counter".into(),
            rust_type: "bridge::Counter".into(),
            release_symbol: "kush_rs_counter_release".into(),
        }],
        functions: vec![
            Function {
                name: "add".into(),
                symbol: "kush_rs_add".into(),
                rust_path: "bridge::add".into(),
                parameters: vec![
                    Parameter::Scalar {
                        name: "a".into(),
                        ty: Scalar::I64,
                    },
                    Parameter::Scalar {
                        name: "b".into(),
                        ty: Scalar::I64,
                    },
                ],
                result: ResultType::Scalar(Scalar::I64),
                fallible: false,
            },
            Function {
                name: "checked_div".into(),
                symbol: "kush_rs_checked_div".into(),
                rust_path: "bridge::checked_div".into(),
                parameters: vec![
                    Parameter::Scalar {
                        name: "a".into(),
                        ty: Scalar::I64,
                    },
                    Parameter::Scalar {
                        name: "b".into(),
                        ty: Scalar::I64,
                    },
                ],
                result: ResultType::Scalar(Scalar::I64),
                fallible: true,
            },
            Function {
                name: "boom".into(),
                symbol: "kush_rs_boom".into(),
                rust_path: "bridge::boom".into(),
                parameters: vec![],
                result: ResultType::Scalar(Scalar::I64),
                fallible: true,
            },
            Function {
                name: "upper".into(),
                symbol: "kush_rs_upper".into(),
                rust_path: "bridge::upper".into(),
                parameters: vec![Parameter::Str {
                    name: "text".into(),
                }],
                result: ResultType::Bytes,
                fallible: true,
            },
            Function {
                name: "counter_new".into(),
                symbol: "kush_rs_counter_new".into(),
                rust_path: "bridge::counter_new".into(),
                parameters: vec![Parameter::Scalar {
                    name: "start".into(),
                    ty: Scalar::I64,
                }],
                result: ResultType::Resource("Counter".into()),
                fallible: false,
            },
            Function {
                name: "counter_add".into(),
                symbol: "kush_rs_counter_add".into(),
                rust_path: "bridge::counter_add".into(),
                parameters: vec![
                    Parameter::Resource {
                        name: "counter".into(),
                        resource: "Counter".into(),
                    },
                    Parameter::Scalar {
                        name: "n".into(),
                        ty: Scalar::I64,
                    },
                ],
                result: ResultType::Scalar(Scalar::I64),
                fallible: true,
            },
            Function {
                name: "live".into(),
                symbol: "kush_rs_live".into(),
                rust_path: "bridge::live".into(),
                parameters: vec![],
                result: ResultType::Scalar(Scalar::I64),
                fallible: false,
            },
        ],
    }
}

const RUST_BRIDGE: &str = r#"
mod bridge {
    use std::sync::atomic::{AtomicI64, Ordering};
    static LIVE: AtomicI64 = AtomicI64::new(0);

    pub struct Counter { value: i64 }
    impl Drop for Counter {
        fn drop(&mut self) { LIVE.fetch_sub(1, Ordering::SeqCst); }
    }

    pub fn add(a: i64, b: i64) -> i64 { a + b }
    pub fn checked_div(a: i64, b: i64) -> Result<i64, String> {
        if b == 0 { Err("division by zero".into()) } else { Ok(a / b) }
    }
    pub fn boom() -> Result<i64, String> { panic!("adapter exploded") }
    pub fn upper(text: &str) -> Result<Vec<u8>, String> {
        Ok(text.bytes().map(|byte| byte.to_ascii_uppercase()).collect())
    }
    pub fn counter_new(start: i64) -> Counter {
        LIVE.fetch_add(1, Ordering::SeqCst);
        Counter { value: start }
    }
    pub fn counter_add(counter: &Counter, n: i64) -> Result<i64, String> {
        Ok(counter.value + n)
    }
    pub fn live() -> i64 { LIVE.load(Ordering::SeqCst) }
}
"#;

#[test]
fn generated_rust_adapter_checks_errors_and_contains_panics() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let generated = rust_adapter_spec().generate().unwrap();
    assert!(generated.contains("kush_bridge_last_error"));
    assert!(generated.contains("catch_unwind"));
    let source = scratch.path().join("bridge.rs");
    fs::write(&source, format!("{generated}\n{RUST_BRIDGE}")).unwrap();
    let archive = scratch.path().join("libbridge.a");
    let compile = Command::new("rustc")
        .arg("--edition=2024")
        .arg("--crate-type=staticlib")
        .arg("-C")
        .arg("panic=unwind")
        .arg("-o")
        .arg(&archive)
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "rustc failed: {}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let kush_source = format!(
        "{RESULT}
        #[foreign(\"kush_rs_counter_release\")] struct Counter {{}}
        foreign \"kush_rs_add\" fn add(a: i64, b: i64) -> i64 ! {{io}};
        foreign \"kush_rs_checked_div\" fn checked_div(a: i64, b: i64) -> Result<i64, i64> ! {{io}};
        foreign \"kush_rs_boom\" fn boom() -> Result<i64, i64> ! {{io}};
        foreign \"kush_rs_upper\" fn upper(text: &str) -> Result<Bytes, i64> ! {{io}};
        foreign \"kush_rs_counter_new\" fn counter_new(start: i64) -> Counter ! {{io}};
        foreign \"kush_rs_counter_add\" fn counter_add(counter: &Counter, n: i64) -> Result<i64, i64> ! {{io}};
        foreign \"kush_rs_live\" fn live() -> i64 ! {{io}};
        fn main() -> Unit ! {{io, alloc, panic}} {{
            print_i64(add(19, 23));
            print_i64(match checked_div(9, 3) {{ Ok(n) => n, Err(_) => 0 }});
            print_i64(match checked_div(1, 0) {{ Ok(_) => 0, Err(code) => code }});
            print_i64(match boom() {{ Ok(_) => 0, Err(code) => code }});
            let text = String.from(\"rust\");
            let view: &str = String.as_str(&text);
            let uppercase = match upper(view) {{ Ok(value) => value, Err(_) => Bytes.from(\"\") }};
            print_i64(Bytes.len(&uppercase));
            print_i64(Bytes.get(&uppercase, 0));
            print_i64({{
                let counter = counter_new(40);
                match counter_add(&counter, 2) {{ Ok(n) => n, Err(_) => 0 }}
            }});
            print_i64(live());
        }}"
    );
    let executable = check(&kush_source).unwrap();
    let binary = scratch.path().join("ffi-rust");
    build_with_options(
        &executable,
        &binary,
        false,
        &LinkSpec {
            libraries: vec![archive],
            system_libraries: vec!["pthread".into(), "dl".into()],
            ..LinkSpec::default()
        },
    )
    .unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "42\n3\n1\n2\n4\n82\n42\n0\n"
    );
}

#[test]
fn adapter_generator_rejects_malformed_names_instead_of_emitting_source() {
    let mut spec = rust_adapter_spec();
    spec.functions[0].symbol = "bad; symbol".into();
    assert!(spec.generate().is_err());
    assert!(spec.validate().is_err());
    let mut spec = rust_adapter_spec();
    spec.functions[0].rust_path = "bridge::add(); (".into();
    assert!(spec.generate().is_err());
}

#[test]
fn project_native_options_map_to_link_inputs() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let native = scratch.path().join("manifest libs");
    fs::create_dir(&native).unwrap();
    let archive = build_c_library(&native);
    let executable = check(
        "foreign \"kush_test_add\" fn add(a: i64, b: i64) -> i64 ! {io};\n\
         fn main() -> i64 ! {io} { add(40, 2) }",
    )
    .unwrap();
    let links = LinkSpec::from_project_native(
        &native,
        &["kushffi".into()],
        std::slice::from_ref(&native),
        &[],
    )
    .unwrap();
    assert_eq!(links.system_libraries, ["kushffi"]);
    assert_eq!(links.library_dirs, std::slice::from_ref(&native));
    let binary = scratch.path().join("manifest-options");
    build_with_options(&executable, &binary, false, &links).unwrap();
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));

    // A path-shaped library entry is linked explicitly, not as `-l<path>`.
    let links = LinkSpec::from_project_native(
        scratch.path(),
        &[archive.to_string_lossy().into_owned()],
        &[],
        &[],
    )
    .unwrap();
    assert_eq!(links.libraries, [archive]);
    assert!(links.system_libraries.is_empty());
    assert!(LinkSpec::from_project_native(scratch.path(), &["--evil".into()], &[], &[],).is_err());
}

#[test]
fn cargo_manifest_option_builds_and_links_a_staticlib() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let crate_root = scratch.path().join("adapter-crate");
    fs::create_dir_all(crate_root.join("src")).unwrap();
    fs::write(
        crate_root.join("Cargo.toml"),
        "[package]\nname = \"kush_manifest_adapter_test\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ncrate-type = [\"staticlib\"]\npath = \"src/lib.rs\"\n\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        crate_root.join("src/lib.rs"),
        "#[unsafe(no_mangle)]\npub extern \"C\" fn kush_manifest_answer() -> i64 { 42 }\n",
    )
    .unwrap();
    let manifest = crate_root.join("Cargo.toml");
    let artifact = kush::native::build_cargo_static_library(&manifest).unwrap();
    assert!(artifact.is_file(), "{artifact:?}");
    assert_eq!(artifact.extension().and_then(|e| e.to_str()), Some("a"));

    let executable = check(
        "foreign \"kush_manifest_answer\" fn answer() -> i64 ! {io};\n\
         fn main() -> i64 ! {io} { answer() }",
    )
    .unwrap();
    let links =
        LinkSpec::from_project_native(scratch.path(), &[], &[], std::slice::from_ref(&manifest))
            .unwrap();
    assert!(links.system_libraries.iter().any(|name| name == "pthread"));
    let binary = scratch.path().join("manifest-cargo");
    build_with_options(&executable, &binary, false, &links).unwrap();
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
}

#[test]
fn cli_build_accepts_localized_link_flags() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let archive = build_c_library(scratch.path());
    let source = scratch.path().join("cli-ffi.kush");
    fs::write(
        &source,
        "foreign \"kush_test_add\" fn add(a: i64, b: i64) -> i64 ! {io};\n\
         fn main() -> i64 ! {io} { add(20, 22) }\n",
    )
    .unwrap();
    let binary = scratch.path().join("cli-ffi");
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .arg("--link")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));

    let rejected = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg(&source)
        .arg("-o")
        .arg(scratch.path().join("nope"))
        .arg("--unknown")
        .output()
        .unwrap();
    assert_eq!(rejected.status.code(), Some(2));
}

#[test]
fn foreign_resource_layout_matches_calls_containers_and_result_slots() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let archive = build_c_library(scratch.path());
    let source = format!(
        r#"{RESULT}
        #[foreign("kush_test_counter_release")] struct H {{}}
        foreign "kush_test_counter_new" fn make(x: i64) -> H ! {{io}};
        foreign "kush_test_take_plus" fn take(h: H, n: i64) -> i64 ! {{io}};
        foreign "kush_test_counter_try" fn try_make(x: i64) -> Result<H, i64> ! {{io}};
        foreign "kush_test_echo_u64" fn echo(x: u64) -> u64 ! {{io}};
        foreign "kush_test_live" fn live() -> i64 ! {{io}};
        struct P {{ a: H, b: i64 }}
        fn pass(h: H, x: i64) -> i64 ! {{io}} {{ x }}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let h = make(100);
            print_i64(take(h, 7));
            print_i64(pass(make(3), 7));
            {{ let p = P {{ a: make(2), b: 5 }}; print_i64(p.b); }};
            {{ let pair = (make(3), 9); print_i64(pair.1); }};
            {{ let array: [H; 2] = [make(4), make(5)]; drop(array); }};
            {{ let v: Vec<H> = Vec.with_capacity(1); let v = Vec.push(v, make(6)); drop(v); }};
            {{ let boxed = Box.new(make(7)); drop(boxed); }};
            let h = match try_make(30) {{ Ok(h) => h, Err(_) => make(0) }};
            print_i64(take(h, 12));
            print_i64(if echo(18446744073709551615) == 18446744073709551615 {{ 1 }} else {{ 0 }});
            print_i64(live());
        }}"#
    );
    let program = check(&source).unwrap();
    let output = scratch.path().join("resource-layout");
    build_with_options(
        &program,
        &output,
        true,
        &LinkSpec {
            libraries: vec![archive],
            ..Default::default()
        },
    )
    .unwrap();
    let result = Command::new(output).output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, b"107\n7\n5\n9\n42\n1\n0\n");
}

#[test]
fn foreign_borrowed_results_and_owned_buffer_inputs_are_rejected() {
    for ty in ["&str", "&Bytes", "&String", "&H"] {
        rejects(
            &format!(
                r#"#[foreign("release")] struct H {{}}
            foreign "f" fn f(x: {ty}) -> {ty} ! {{io}};
            fn main() -> Unit ! {{}} {{}}"#
            ),
            "foreign result type",
        );
        rejects(
            &format!(
                r#"{RESULT} #[foreign("release")] struct H {{}}
            foreign "f" fn f(x: {ty}) -> Result<{ty}, i64> ! {{io}};
            fn main() -> Unit ! {{}} {{}}"#
            ),
            "foreign Result Ok type",
        );
    }
    for ty in ["Bytes", "Unit"] {
        rejects(
            &format!(
                "foreign \"take\" fn take(x: {ty}) -> i64 ! {{io}}; fn main() -> Unit ! {{}} {{}}"
            ),
            "foreign parameter type",
        );
    }
}

#[test]
fn cargo_selects_the_requested_adapter_not_its_staticlib_dependency() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    fs::create_dir_all(scratch.path().join("dep/src")).unwrap();
    fs::create_dir_all(scratch.path().join("adapter/src")).unwrap();
    fs::write(scratch.path().join("dep/Cargo.toml"), "[package]\nname=\"static_dep\"\nversion=\"0.1.0\"\nedition=\"2024\"\n[lib]\ncrate-type=[\"rlib\",\"staticlib\"]\n").unwrap();
    fs::write(
        scratch.path().join("dep/src/lib.rs"),
        "pub fn answer() -> i64 { 42 }",
    )
    .unwrap();
    fs::write(scratch.path().join("adapter/Cargo.toml"), "[package]\nname=\"selected_adapter\"\nversion=\"0.1.0\"\nedition=\"2024\"\n[lib]\ncrate-type=[\"staticlib\"]\n[dependencies]\nstatic_dep={path=\"../dep\"}\n").unwrap();
    fs::write(scratch.path().join("adapter/src/lib.rs"), r#"#[unsafe(no_mangle)] pub extern "C" fn adapter_answer() -> i64 { static_dep::answer() }"#).unwrap();
    let archive =
        kush::native::build_cargo_static_library(&scratch.path().join("adapter/Cargo.toml"))
            .unwrap();
    assert_eq!(archive.file_name().unwrap(), "libselected_adapter.a");
    let program = check(r#"foreign "adapter_answer" fn answer() -> i64 ! {io}; fn main() -> i64 ! {io} { answer() }"#).unwrap();
    let binary = scratch.path().join("selected-adapter");
    build_with_options(
        &program,
        &binary,
        false,
        &LinkSpec {
            libraries: vec![archive],
            system_libraries: vec!["pthread".into(), "dl".into()],
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}

#[test]
fn native_links_reject_response_files_and_package_escape_paths() {
    let links = LinkSpec {
        libraries: vec!["@arguments".into()],
        ..Default::default()
    };
    assert!(
        links
            .validate()
            .unwrap_err()
            .message
            .contains("must not start")
    );
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for path in ["../escape.a", "/tmp/escape.a"] {
        assert!(LinkSpec::from_project_native(scratch.path(), &[path.into()], &[], &[]).is_err());
    }
    let links = LinkSpec::from_project_native(scratch.path(), &["libsample.so.1".into()], &[], &[])
        .unwrap();
    assert_eq!(links.libraries, vec![scratch.path().join("libsample.so.1")]);
}
