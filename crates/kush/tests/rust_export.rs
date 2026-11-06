//! KUSH-RUST-EXPORT (user-approved design, 2026-11-06): `export "symbol" fn`
//! and `kush build --lib lib<name>.a` produce a static library with C ABI
//! entry points (scalars only, effect row `{}` or `{panic}`) and Rust
//! bindings. The exports called from C and from Rust agree with the
//! reference evaluator running the same calls from `main`.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::executable::check;
use std::{path::Path, process::Command};

const LIBRARY: &str = r#"
struct Facts { authenticated: Bool, has_pin: Bool, revision: u64 }
fn bound(f: Facts) -> Bool ! {} { f.authenticated && f.revision >= 1 }
export "lib_decide" fn decide(authenticated: Bool, has_pin: Bool, revision: u64) -> i64 ! {} {
    let f = Facts { authenticated: authenticated, has_pin: has_pin, revision: revision };
    if !f.has_pin && bound(f) { 1 } else { 0 }
}
export "lib_narrow" fn narrow(a: i8, b: u8, c: i16, d: u32) -> i64 ! {panic} {
    let a: i64 = Int.convert(a);
    let b: i64 = Int.convert(b);
    let c: i64 = Int.convert(c);
    let d: i64 = Int.convert(d);
    a * 1000000 + b * 10000 + c + d
}
export "lib_negate" fn negate(x: i8) -> i8 ! {panic} { 0 - x }
export "lib_top" fn top(x: u64) -> u64 ! {} { x }
export "lib_scale" fn scale(x: i32, factor: f64) -> f64 ! {panic} { Float.from_int(x) * factor }
export "lib_half" fn half(x: f32) -> f32 ! {panic} { x / 2.0 }
export "lib_flag" fn flag(n: i64) -> Bool ! {} { n < 0 }
export "lib_divide" fn divide(a: i64, b: i64) -> i64 ! {panic} { a / b }
export "lib_nothing" fn nothing(x: i64) -> Unit ! {} { }
export "lib_keywords" fn yield(ref: i64, move: Bool) -> i64 ! {} { if move { ref } else { 0 } }
"#;

/// The same calls as the C and Rust drivers, printed by the evaluator.
const MAIN: &str = r#"
fn show_bool(b: Bool) -> Unit ! {io, panic} { print_i64(if b { 1 } else { 0 }); }
fn main() -> i64 ! {io, panic} {
    print_i64(decide(true, false, 3));
    print_i64(decide(true, true, 3));
    print_i64(decide(false, false, 3));
    print_i64(narrow(-5, 200, -300, 4000000000));
    let n: i64 = Int.convert(negate(-127));
    print_i64(n);
    print_int(top(18446744073709551615));
    show_bool(flag(-1));
    show_bool(flag(1));
    print_i64(divide(84, 2));
    nothing(1);
    0
}
"#;

const C_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
int64_t lib_decide(int32_t, int32_t, uint64_t);
int64_t lib_narrow(int8_t, uint8_t, int16_t, uint32_t);
int8_t lib_negate(int8_t);
uint64_t lib_top(uint64_t);
double lib_scale(int32_t, double);
float lib_half(float);
int32_t lib_flag(int64_t);
int64_t lib_divide(int64_t, int64_t);
void lib_nothing(int64_t);
int main(int argc, char **argv) {
    if (argc > 1) { printf("%ld\n", (long)lib_divide(1, 0)); return 0; }
    printf("%ld\n%ld\n%ld\n", (long)lib_decide(1, 0, 3), (long)lib_decide(7, 9, 3), (long)lib_decide(0, 0, 3));
    printf("%ld\n", (long)lib_narrow(-5, 200, -300, 4000000000u));
    printf("%ld\n", (long)lib_negate(-127));
    printf("%lu\n", (unsigned long)lib_top(18446744073709551615ull));
    printf("%d\n%d\n", lib_flag(-1), lib_flag(1));
    printf("%ld\n", (long)lib_divide(84, 2));
    lib_nothing(1);
    printf("%.2f %.2f\n", lib_scale(3, 1.5), (double)lib_half(5.0f));
    return 0;
}
"#;

fn build(dir: &Path, source: &str, release: bool) -> std::path::PathBuf {
    let program = check(source).unwrap_or_else(|e| panic!("{e:?}"));
    let library = dir.join("libpolicy.a");
    let options = if release {
        kush::native::CodegenOptions::release()
    } else {
        kush::native::CodegenOptions::default()
    };
    let bindings = kush::native::build_library_and_bindings(&program, &library, options).unwrap();
    assert_eq!(bindings, dir.join("libpolicy.rs"));
    library
}

fn scratch(label: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("kush-export-{label}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn exports_agree_with_the_evaluator_from_c() {
    let program = check(&format!("{LIBRARY}{MAIN}")).unwrap();
    let mut expected = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut expected).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    let expected = String::from_utf8(expected).unwrap() + "4.50 2.50\n";
    for release in [false, true] {
        let dir = scratch(if release { "c-release" } else { "c" });
        build(&dir, LIBRARY, release);
        std::fs::write(dir.join("main.c"), C_DRIVER).unwrap();
        let status = Command::new("cc")
            .current_dir(&dir)
            .args(["main.c", "-L.", "-lpolicy", "-lm", "-o", "main"])
            .status()
            .unwrap();
        assert!(status.success());
        let output = Command::new(dir.join("main")).output().unwrap();
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
        // A panic inside an export aborts the process.
        let output = Command::new(dir.join("main"))
            .arg("panic")
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("panic"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[test]
fn exports_are_callable_from_rust_through_the_bindings() {
    if Command::new("rustc").arg("--version").output().is_err() {
        return;
    }
    let dir = scratch("rust");
    build(&dir, LIBRARY, true);
    let bindings = std::fs::read_to_string(dir.join("libpolicy.rs")).unwrap();
    assert!(
        bindings
            .contains("pub fn lib_decide(authenticated: i32, has_pin: i32, revision: u64) -> i64;")
    );
    std::fs::write(
        dir.join("main.rs"),
        r#"mod libpolicy;
        use libpolicy::Library;
        fn main() {
            let lib = Library::take().unwrap();
            assert!(Library::take().is_none());
            println!("{} {} {}", lib.decide(true, false, 3), lib.decide(true, true, 3), lib.narrow(-5, 200, -300, 4000000000));
            println!("{} {} {} {}", lib.negate(-127), lib.top(u64::MAX), lib.flag(-1), lib.scale(3, 1.5));
            lib.nothing(1);
            assert_eq!(lib.r#yield(5, true), 5);
            // The token may move to another thread (Send), never be shared.
            let n = std::thread::spawn(move || lib.divide(84, 2)).join().unwrap();
            println!("{n}");
        }"#,
    )
    .unwrap();
    let output = Command::new("rustc")
        .current_dir(&dir)
        .args([
            "--edition",
            "2024",
            "-O",
            "main.rs",
            "-L",
            ".",
            "-o",
            "main",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(dir.join("main")).output().unwrap();
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "1 0 3996999700\n127 18446744073709551615 true 4.5\n42\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn export_rejections() {
    for (source, fragment) in [
        ("export \"f\" fn f<T>(x: T) -> T ! {} { x }", "generic"),
        (
            "export \"f\" fn f(x: Bytes) -> i64 ! {} { drop(x); 0 }",
            "integers, floats and Bool",
        ),
        (
            "struct P { a: i64 } export \"f\" fn f(p: P) -> i64 ! {} { p.a }",
            "integers, floats and Bool",
        ),
        (
            "struct P { a: i64 } export \"f\" fn f(a: i64) -> P ! {} { P { a: a } }",
            "returns an integer",
        ),
        (
            "export \"f\" fn f(a: i64) -> i64 ! {io, panic} { print_i64(a); a }",
            "effect row",
        ),
        (
            "export \"f\" fn f(a: i64) -> i64 ! {alloc, panic} { let b = Box.new(a); Box.take(b) }",
            "effect row",
        ),
        (
            "export \"f\" fn f(a: i64, erased p: { a > 0 }) -> i64 ! {} { a }",
            "erased",
        ),
        (
            "export \"bad-name\" fn f(a: i64) -> i64 ! {} { a }",
            "C identifier",
        ),
        (
            "export \"kush_entry\" fn f(a: i64) -> i64 ! {} { a }",
            "reserved",
        ),
        ("export \"main\" fn f(a: i64) -> i64 ! {} { a }", "reserved"),
        (
            "export \"f\" fn f(a: i64) -> i64 ! {} { a } export \"f\" fn g(a: i64) -> i64 ! {} { a }",
            "twice",
        ),
    ] {
        match check(source) {
            Ok(_) => panic!("accepted: {source}"),
            Err(error) => assert!(
                error.message.contains(fragment),
                "expected {fragment:?}, got {}\n{source}",
                error.message
            ),
        }
    }
    assert!(kush::parse("export \"f\" fn f(a: i64) -> i64 ! {};").is_err());
    // `export` stays an ordinary identifier elsewhere.
    let program = check("fn main() -> i64 ! {} { let export = 4; export }").unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 4);
    // A library needs exports and a lib<name>.a name.
    let dir = scratch("names");
    let none = check("fn main() -> i64 ! {} { 0 }").unwrap();
    let error =
        kush::native::build_library_and_bindings(&none, &dir.join("libx.a"), Default::default())
            .unwrap_err();
    assert!(error.message.contains("at least one"), "{}", error.message);
    let some = check(LIBRARY).unwrap();
    for bad in ["policy.a", "libpolicy.so", "lib.a", "libpo-licy.a"] {
        let error =
            kush::native::build_library_and_bindings(&some, &dir.join(bad), Default::default())
                .unwrap_err();
        assert!(
            error.message.contains("lib<name>.a"),
            "{bad}: {}",
            error.message
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_cli_builds_a_library() {
    let dir = scratch("cli");
    std::fs::write(dir.join("policy.kush"), LIBRARY).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .current_dir(&dir)
        .args(["build", "policy.kush", "--lib", "libpolicy.a", "--release"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(dir.join("libpolicy.a").exists() && dir.join("libpolicy.rs").exists());
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .current_dir(&dir)
        .args(["build", "policy.kush", "--lib", "policy.a"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    // Project mode: target/kush/lib<package>.a by default.
    std::fs::create_dir_all(dir.join("proj/src")).unwrap();
    std::fs::write(
        dir.join("proj/Kush.toml"),
        "[package]\nname = \"share_policy\"\nversion = \"0.1.0\"\nentry = \"src/main.kush\"\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("proj/src/main.kush"),
        format!("module share_policy;\n{LIBRARY}"),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kush"))
        .current_dir(dir.join("proj"))
        .args(["build", "--lib", "--release"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(dir.join("proj/target/kush/libshare_policy.a").exists());
    assert!(dir.join("proj/target/kush/libshare_policy.rs").exists());
    let _ = std::fs::remove_dir_all(&dir);
}
