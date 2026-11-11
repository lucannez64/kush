#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::native::Scratch;
use std::{fs, os::unix::fs::PermissionsExt, path::Path, process::Command};

fn setup(root: &Path) {
    fs::write(root.join("main.kush"), "fn main()->i64 ! {} {42}\n").unwrap();
    fs::write(
        root.join("cc"),
        r#"#!/bin/sh
for argument do
    if [ "$argument" = '-c' ]; then echo compile >> "$CC_LOG"; fi
done
exec /usr/bin/cc "$@"
"#,
    )
    .unwrap();
    fs::set_permissions(root.join("cc"), fs::Permissions::from_mode(0o700)).unwrap();
}
fn build(root: &Path, output: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_kush"));
    command
        .args(["build"])
        .arg(root.join("main.kush"))
        .arg("-o")
        .arg(root.join(output))
        .env(
            "PATH",
            format!("{}:{}", root.display(), std::env::var("PATH").unwrap()),
        )
        .env("CC_LOG", root.join("compiles"))
        .env("KUSH_RUNTIME_CACHE", root.join("cache"))
        // These tests replace `cc`; they are about the default backend.
        .env_remove("KUSH_BACKEND")
        .env_remove("KUSH_NO_RUNTIME_CACHE");
    command
}
fn success(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn compiles(root: &Path) -> usize {
    fs::read_to_string(root.join("compiles"))
        .unwrap()
        .lines()
        .count()
}

#[test]
fn warm_builds_reuse_runtime_and_corrupt_entries_rebuild() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    setup(root);
    success(&mut build(root, "first"));
    success(&mut build(root, "second"));
    assert_eq!(compiles(root), 1);
    assert_eq!(
        Command::new(root.join("second")).status().unwrap().code(),
        Some(42)
    );
    let entry = fs::read_dir(root.join("cache"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    fs::write(&entry, b"damaged object").unwrap();
    success(&mut build(root, "third"));
    assert_eq!(compiles(root), 2);
    success(build(root, "stats").arg("--stats"));
    let output = Command::new(root.join("stats")).output().unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("fusions=0"));
    assert_eq!(compiles(root), 3);
    // Compiler/environment inputs cannot silently reuse an incompatible object.
    success(build(root, "environment").env("KUSH_CACHE_TEST_INPUT", "changed"));
    assert_eq!(compiles(root), 4);
    success(build(root, "uncached").env("KUSH_NO_RUNTIME_CACHE", "1"));
    assert_eq!(compiles(root), 5);
    fs::write(root.join("main.kush"), "fn f(x:i64)->i64 ! {} {x^1} fn main()->i64 ! {alloc,panic} {let v:Vec<i64> =[1];let v=Vec.map_in_place(Vec.map_in_place(v,f),f);Vec.get(&v,0)}").unwrap();
    success(build(root, "fused").arg("--stats"));
    let output = Command::new(root.join("fused")).output().unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("fusions=1"));
    assert_eq!(compiles(root), 6);
    fs::write(root.join("main.kush"), "fn main()->Unit ! {alloc,panic,suspend} {Task.scope(fn()->Unit ! {alloc,panic,suspend} {})}").unwrap();
    success(&mut build(root, "tasks"));
    assert!(Command::new(root.join("tasks")).status().unwrap().success());
    assert_eq!(compiles(root), 7);
}
#[test]
fn concurrent_builds_publish_complete_entries() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    setup(root);
    let mut first = build(root, "first").spawn().unwrap();
    let mut second = build(root, "second").spawn().unwrap();
    assert!(first.wait().unwrap().success());
    assert!(second.wait().unwrap().success());
    let count = compiles(root);
    assert!((1..=2).contains(&count));
    success(&mut build(root, "third"));
    assert_eq!(compiles(root), count);
}
#[test]
fn unusable_or_symlinked_cache_falls_back_without_touching_target() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    setup(root);
    fs::write(root.join("victim"), "preserve me").unwrap();
    std::os::unix::fs::symlink(root.join("victim"), root.join("cache")).unwrap();
    success(&mut build(root, "first"));
    success(&mut build(root, "second"));
    assert_eq!(compiles(root), 2);
    assert_eq!(
        fs::read_to_string(root.join("victim")).unwrap(),
        "preserve me"
    );
}

#[test]
fn compiler_header_changes_invalidate_a_warm_entry() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let root = scratch.path();
    setup(root);
    let includes = root.join("includes with spaces");
    fs::create_dir(&includes).unwrap();
    let header = includes.join("math.h");
    fs::write(&header, "#include_next <math.h>\n").unwrap();
    success(build(root, "first").env("CPATH", &includes));
    success(build(root, "second").env("CPATH", &includes));
    assert_eq!(compiles(root), 1);
    fs::write(&header, "#include_next <math.h>\n/* header changed */\n").unwrap();
    success(build(root, "third").env("CPATH", &includes));
    assert_eq!(compiles(root), 2);
}
