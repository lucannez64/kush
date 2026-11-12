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
    assert!(text.contains("define i64 @kush_entry()"), "{text}");
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

/// Ownership reaches LLVM: owning handles and exclusive borrows are `noalias`
/// pointer parameters, a function whose address is taken is called through a
/// word-signature thunk, and buffer headers are distinguished from elements.
#[test]
fn ownership_facts_are_stated_in_the_module() {
    if !clang_available() {
        return;
    }
    let source = "
        fn fill(view: &mut [i64], value: i64) -> Unit ! {panic} {
            let mut i = 0;
            while i < Slice.len(view) { Slice.set(view, i, value); i = i + 1; }
        }
        fn sum_all(values: Vec<i64>) -> i64 ! {panic} {
            let mut acc = 0;
            let mut i = 0;
            while i < Vec.len(&values) { acc = acc + Vec.get(&values, i); i = i + 1; }
            acc
        }
        fn open(ticket: Box<i64>) -> i64 ! {} { Box.take(ticket) }
        fn apply(f: fn(Box<i64>) -> i64 ! {}, ticket: Box<i64>) -> i64 ! {} { f(ticket) }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut numbers: [i64; 4] = [0, 0, 0, 0];
            fill(&mut numbers[..], 3);
            let mut values: Vec<i64> = Vec.with_capacity(2);
            let mut i = 0;
            while i < 5 { values = Vec.push(values, numbers[i % 4] + i); i = i + 1; }
            print_i64(sum_all(values));
            print_i64(apply(open, Box.new(7)) + open(Box.new(8)));
        }";
    let program = kush::executable::check(source).unwrap();
    let text =
        kush::native::emit_llvm_ir(&program, kush::native::CodegenOptions::release_llvm()).unwrap();
    // fill(&mut [i64], i64): the data pointer of the exclusive view.
    assert!(
        text.contains("(ptr noalias %v0.p, i64 %v1, i64 %v2, i64 %v3, i64 %v4)"),
        "{text}"
    );
    // sum_all(Vec<i64>) and open(Box<i64>): the owning handle.
    assert!(
        text.matches("(ptr noalias %v0.p) #0 {").count() >= 2,
        "{text}"
    );
    // `open` is passed as a value, so it has a thunk and `apply` gets that.
    assert!(text.contains(".words(i64 %a0) #0 {"), "{text}");
    assert!(text.contains(".words to i64"), "{text}");
    assert!(
        text.contains("!tbaa !4") && text.contains("!tbaa !5"),
        "{text}"
    );
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("facts");
    for options in [
        kush::native::CodegenOptions::default(),
        kush::native::CodegenOptions::release_llvm(),
    ] {
        kush::native::build_with_codegen(
            &program,
            &binary,
            false,
            &kush::native::LinkSpec::default(),
            options,
        )
        .unwrap();
        let output = Command::new(&binary).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "25\n15\n");
    }
}

fn emitted(flags: &[&str]) -> String {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let module = scratch.path().join("module.ll");
    let output = kush()
        .arg("build")
        .arg(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../benchmarks/checked-loops/kush/main.kush"),
        )
        .arg("-o")
        .arg(scratch.path().join("program"))
        .args(flags)
        .env("KUSH_EMIT_LLVM", &module)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{flags:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::read_to_string(module).unwrap()
}

#[test]
fn the_overflow_flag_does_not_depend_on_where_the_backend_is_named() {
    if !clang_available() {
        return;
    }
    let deferred = emitted(&["--release", "--backend", "llvm"]);
    let before = emitted(&["--release", "--no-deferred-overflow", "--backend", "llvm"]);
    let after = emitted(&["--release", "--backend", "llvm", "--no-deferred-overflow"]);
    assert_eq!(before, after);
    assert_ne!(before, deferred);
}

/// A C callee may assume that an argument narrower than `int` arrives
/// extended to 32 bits; the caller has to do it.
#[test]
fn narrow_foreign_arguments_are_extended_for_the_callee() {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    fs::write(
        root.join("lib.c"),
        "#include <stdint.h>\n\
         int64_t ext_u8(uint8_t x) { return (int64_t)(int)x * 1000; }\n\
         int64_t ext_i8(int8_t x) { return (int64_t)(int)x * 1000; }\n\
         int64_t ext_u16(uint16_t x) { return (int64_t)(int)x + 1; }\n\
         int64_t ext_i16(int16_t x) { return (int64_t)(int)x + 1; }\n\
         static const int64_t table[4] = {10, 20, 30, 40};\n\
         int64_t ext_idx(uint8_t x) { return x < 4 ? table[x] : -1; }\n",
    )
    .unwrap();
    assert!(
        Command::new("cc")
            .current_dir(root)
            .args(["-std=c11", "-O2", "-fPIC", "-c", "lib.c", "-o", "lib.o"])
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new("ar")
            .current_dir(root)
            .args(["crs", "libnarrow.a", "lib.o"])
            .status()
            .unwrap()
            .success()
    );
    fs::write(
        root.join("main.kush"),
        "enum Result<T, E> { Ok(T), Err(E) }
foreign \"ext_u8\" fn ext_u8(x: u8) -> i64 ! {io};
foreign \"ext_i8\" fn ext_i8(x: i8) -> i64 ! {io};
foreign \"ext_u16\" fn ext_u16(x: u16) -> i64 ! {io};
foreign \"ext_i16\" fn ext_i16(x: i16) -> i64 ! {io};
foreign \"ext_idx\" fn ext_idx(x: u8) -> i64 ! {io};
fn main() -> i64 ! {io, alloc, panic} {
    let line = match IO.read_line(IO.stdin(), Bytes.with_capacity(64)) {
        Ok(b) => b,
        Err(_) => Bytes.with_capacity(1),
    };
    let mut n = 0;
    let mut i = 0;
    while i < Bytes.len(&line) {
        let c = Int.convert::<i64>(Bytes.get(&line, i));
        if c >= 48 && c <= 57 { n = n * 10 + c - 48; }
        i = i + 1;
    }
    let a: u8 = Int.truncate(n);
    let b: i8 = Int.truncate(n);
    let c: u16 = Int.truncate(n);
    let d: i16 = Int.truncate(n);
    print_int(ext_u8(a));
    print_int(ext_i8(b));
    print_int(ext_u16(c));
    print_int(ext_i16(d));
    print_int(ext_idx(Int.truncate(n)));
    0
}
",
    )
    .unwrap();
    let mut configurations = vec![vec![], vec!["--release"]];
    if clang_available() {
        configurations.push(vec!["--backend", "llvm"]);
        configurations.push(vec!["--release", "--backend", "llvm"]);
    }
    for flags in configurations {
        use std::io::Write;
        let built = kush()
            .current_dir(root)
            .args([
                "build",
                "main.kush",
                "-o",
                "program",
                "--link",
                "libnarrow.a",
            ])
            .args(&flags)
            .output()
            .unwrap();
        assert!(
            built.status.success(),
            "{flags:?}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let mut child = Command::new(root.join("program"))
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        // 0x103E8: every narrow view has set bits above it.
        child.stdin.take().unwrap().write_all(b"66536\n").unwrap();
        let output = child.wait_with_output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "232000\n-24000\n1001\n1001\n-1\n",
            "{flags:?}"
        );
    }
}

/// Which loops are deferred, as the planner reports it.
#[test]
fn the_planner_defers_counted_loops_whose_indices_follow_the_counter() {
    if !clang_available() {
        return;
    }
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    fs::write(
        root.join("main.kush"),
        "fn plain(n: i64, k: i64) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < n { acc = acc + i * k; i = i + 1; }
    acc
}
fn down(n: i64, k: i64) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = n;
    while i > 0 { acc = acc + i * k; i = i - 1; }
    acc
}
fn stencil(values: &[i64]) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 1;
    while i < Slice.len(values) { acc = acc + Slice.get(values, i) - Slice.get(values, i - 1); i = i + 1; }
    acc
}
fn gather(values: &[i64]) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < Slice.len(values) { acc = acc + Slice.get(values, i & 7); i = i + 1; }
    acc
}
fn main() -> i64 ! {alloc, panic} {
    let mut values: Vec<i64> = Vec.with_capacity(8);
    let mut i = 0;
    while i < 8 { values = Vec.push(values, i); i = i + 1; }
    plain(9, 2) + down(9, 2) + stencil(&values[..]) + gather(&values[..]) - 197
}
",
    )
    .unwrap();
    let built = kush()
        .current_dir(root)
        .args([
            "build",
            "main.kush",
            "-o",
            "program",
            "--release",
            "--backend",
            "llvm",
        ])
        .env("KUSH_TRACE_DEFERRED", "1")
        .output()
        .unwrap();
    let trace = String::from_utf8_lossy(&built.stderr);
    assert!(built.status.success(), "{trace}");
    for deferred in ["plain", "down", "stencil"] {
        assert!(
            !trace.contains(&format!("loop in {deferred} keeps")),
            "{trace}"
        );
    }
    assert!(
        trace.contains(
            "loop in gather keeps immediate checks: an index that does not follow the counter"
        ),
        "{trace}"
    );
    assert!(
        Command::new(root.join("program"))
            .status()
            .unwrap()
            .success()
    );
}
