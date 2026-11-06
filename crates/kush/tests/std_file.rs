//! STD-FILE: `std.file.File`, a linear open file with positioned reads and
//! writes, `fsync`, truncation and size, over the `FS.open`/`FS.read_at`/...
//! host calls. The reference evaluator and native builds must agree on the
//! output, the errno values and the file left on disk; the evaluator must
//! free every buffer.

use kush::{Host, executable};
use std::{
    fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn unique_directory(label: &str) -> PathBuf {
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("kush-std-file-{label}-{}-{id}", std::process::id()));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir(&path).unwrap();
    path
}

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program = kush::program::load_source("<std-file-test>", source).unwrap();
    executable::check_program(&program).map_err(|error| program.sources.render(&error))
}

fn reference(source: &str) -> (i64, String) {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "reference cleanup");
    (status, String::from_utf8(output).unwrap())
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> (i64, String) {
    let program = checked(source).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("file-program");
    kush::native::build(&program, &binary).unwrap();
    let output = std::process::Command::new(&binary).output().unwrap();
    (
        i64::from(output.status.code().unwrap()),
        String::from_utf8(output.stdout).unwrap(),
    )
}

/// Run `source` (with `@DIR@` replaced by a fresh directory) in both backends
/// and return the agreed output and the directory of the last run.
fn agree(source: &str) -> (String, PathBuf) {
    let first = unique_directory("ref");
    let (status, output) = reference(&source.replace("@DIR@", first.to_str().unwrap()));
    assert_eq!(status, 0, "{output}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let second = unique_directory("native");
        let native = native(&source.replace("@DIR@", second.to_str().unwrap()));
        assert_eq!(native, (0, output.clone()));
        assert_eq!(listing(&first), listing(&second));
        return (output, second);
    }
    #[allow(unreachable_code)]
    (output, first)
}

fn listing(dir: &Path) -> Vec<(String, Vec<u8>)> {
    let mut files: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            (
                entry.file_name().into_string().unwrap(),
                fs::read(entry.path()).unwrap(),
            )
        })
        .collect();
    files.sort();
    files
}

const PRELUDE: &str = "
module file_test;
use std.result.Result;
use std.file;
fn code(r: Result<i64, i64>) -> i64 ! {panic} { match r { Result.Ok(n) => n, Result.Err(e) => -e } }
fn unit(r: Result<Unit, i64>) -> i64 ! {panic} { match r { Result.Ok(_) => 0, Result.Err(e) => -e } }
fn show(n: i64) -> Unit ! {io, panic} { print_i64(n); }
";

#[test]
fn positioned_io_sync_truncate_and_size() {
    let (output, dir) = agree(&format!(
        "{PRELUDE}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let path = Bytes.from(\"@DIR@/data\");
            let f = match file.open_write(&path) {{ Result.Ok(f) => f, Result.Err(e) => return e }};
            show(code(file.write_at(&f, 0, &Bytes.from(\"0123456789\"))));
            show(code(file.write_at(&f, 12, &Bytes.from(\"xy\"))));      // leaves a zero hole
            show(unit(file.sync(&f)));
            show(code(file.size(&f)));
            match file.read_at(&f, 8, 6, Bytes.with_capacity(8)) {{
                Result.Ok(b) => {{
                    show(Bytes.len(&b));
                    show(Bytes.get(&b, 0)); show(Bytes.get(&b, 2)); show(Bytes.get(&b, 5));
                    drop(b);
                }},
                Result.Err(e) => show(-e),
            }}
            // Short read at the end of the file, and a read past it.
            match file.read_at(&f, 13, 5, Bytes.with_capacity(5)) {{
                Result.Ok(b) => {{ show(Bytes.len(&b)); drop(b); }},
                Result.Err(e) => show(-e),
            }}
            match file.read_at(&f, 100, 5, Bytes.with_capacity(5)) {{
                Result.Ok(b) => {{ show(Bytes.len(&b)); drop(b); }},
                Result.Err(e) => show(-e),
            }}
            show(unit(file.truncate(&f, 4)));
            show(code(file.size(&f)));
            show(unit(file.close(f)));
            show(unit(file.sync_dir(&Bytes.from(\"@DIR@\"))));
            show(unit(file.sync_dir(&path)));           // a file: ENOTDIR
            0
        }}"
    ));
    assert_eq!(
        output,
        "10\n2\n0\n14\n6\n56\n0\n121\n1\n0\n0\n4\n0\n0\n-20\n"
    );
    assert_eq!(fs::read(dir.join("data")).unwrap(), b"0123");
}

#[test]
fn open_modes_and_errors() {
    let (output, _) = agree(&format!(
        "{PRELUDE}
        fn try_close(r: Result<file.File, i64>) -> i64 ! {{io, panic}} {{
            match r {{ Result.Ok(f) => unit(file.close(f)), Result.Err(e) => -e }}
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let path = Bytes.from(\"@DIR@/new\");
            show(try_close(file.open_read(&path)));       // ENOENT
            show(try_close(file.open_existing(&path)));   // ENOENT
            show(try_close(file.create_new(&path)));      // created
            show(try_close(file.create_new(&path)));      // EEXIST
            show(try_close(file.open_existing(&path)));
            show(try_close(file.open_read(&Bytes.from(\"@DIR@/a\\0b\"))));  // EINVAL
            // A read-only file refuses writes; a short buffer is EFBIG and freed.
            match file.open_read(&path) {{
                Result.Ok(f) => {{
                    show(code(file.write_at(&f, 0, &Bytes.from(\"x\"))));
                    show(match file.read_at(&f, 0, 9, Bytes.with_capacity(4)) {{
                        Result.Ok(b) => {{ drop(b); 0 }},
                        Result.Err(e) => -e,
                    }});
                    show(match file.read_at(&f, -1, 1, Bytes.with_capacity(4)) {{
                        Result.Ok(b) => {{ drop(b); 0 }},
                        Result.Err(e) => -e,
                    }});
                    show(unit(file.close(f)));
                }},
                Result.Err(e) => show(-e),
            }}
            0
        }}"
    ));
    assert_eq!(
        output,
        "-2\n-2\n0\n-17\n0\n-22\n-9\n-27\n-22\n0\n"
    );
}

#[test]
fn a_file_must_be_closed_and_cannot_be_forged() {
    for (body, message) in [
        (
            "let f = match file.open_write(&Bytes.from(\"x\")) { Result.Ok(f) => f, Result.Err(e) => return e }; 0",
            "linear value is not consumed",
        ),
        (
            "let f = match file.open_write(&Bytes.from(\"x\")) { Result.Ok(f) => f, Result.Err(e) => return e };
             drop(f); 0",
            "linear",
        ),
        (
            "let f = match file.open_write(&Bytes.from(\"x\")) { Result.Ok(f) => f, Result.Err(e) => return e };
             let a = file.close(f); let b = file.close(f); 0",
            "moved",
        ),
        ("let f = file.File { fd: 1 }; unit(file.close(f))", "private"),
        // RAW-FS-HANDLES: the descriptor builtins are reserved for std.
        ("code(FS.open(&Bytes.from(\"x\"), 0))", "reserved for std"),
        ("match FS.read_at(3, 0, 1, Bytes.with_capacity(1)) { Result.Ok(b) => { drop(b); 0 }, Result.Err(e) => e }", "reserved for std"),
        ("code(FS.write_at(3, 0, &Bytes.from(\"x\")))", "reserved for std"),
        ("unit(FS.sync(3))", "reserved for std"),
        ("unit(FS.truncate(3, 0))", "reserved for std"),
        ("code(FS.file_size(0))", "reserved for std"),
        ("unit(FS.close(2))", "reserved for std"),
        ("let f = FS.close; 0", ""),
    ] {
        let source = format!("{PRELUDE} fn main() -> i64 ! {{io, alloc, panic}} {{ {body} }}");
        let error = checked(&source).err().unwrap_or_else(|| panic!("accepted: {body}"));
        assert!(error.contains(message), "expected {message:?} in:\n{error}");
    }
}

/// A root file cannot claim the std namespace to reach the raw builtins.
#[test]
fn a_root_module_named_std_cannot_call_raw_handles() {
    let source = "module std.evil;
        use std.result.Result;
        fn main() -> i64 ! {io, alloc, panic} {
            match FS.file_size(0) { Result.Ok(n) => n, Result.Err(e) => e }
        }";
    let error = checked(source).err().expect("accepted a root std module");
    assert!(error.contains("reserved for std"), "{error}");
}

/// A record holding a `File` and ordinary data (kush-kv's store): taking it
/// apart discharges the record's obligation; the `File` part must still be
/// closed, the `Bytes` part is ordinary data that can be dropped or ignored.
#[test]
fn a_record_holding_a_file_can_be_taken_apart() {
    let (output, _) = agree(&format!(
        "{PRELUDE}
        struct Store {{ log: file.File, name: Bytes, size: i64 }}
        fn finish(s: Store) -> i64 ! {{io, panic}} {{
            match s {{ Store {{ log, name, size }} => {{ drop(name); unit(file.close(log)) + size }} }}
        }}
        fn finish_let(s: Store) -> i64 ! {{io, panic}} {{
            let Store {{ log, name, size }} = s;
            drop(name);
            unit(file.close(log)) + size
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let path = Bytes.from(\"@DIR@/f\");
            let a = match file.open_write(&path) {{ Result.Ok(f) => f, Result.Err(e) => return e }};
            show(finish(Store {{ log: a, name: Bytes.from(\"a\"), size: 1 }}));
            let b = match file.open_write(&path) {{ Result.Ok(f) => f, Result.Err(e) => return e }};
            show(finish_let(Store {{ log: b, name: Bytes.from(\"b\"), size: 2 }}));
            0
        }}"
    ));
    assert_eq!(output, "1\n2\n");
    for body in [
        "match s { Store { log, name, size } => { drop(name); size } }",
        "match s { Store { log: _, name, size } => size }",
        "let Store { log, name, size } = s; drop(log); size",
        // Ignoring any part of a linear value is refused, so a `File` cannot
        // be discarded unclosed through a pattern that never names its
        // private field (review finding).
        "match s { Store { log: file.File {}, name, size } => size }",
        "match s { Store { log, name: _, size } => { let _ = file.close(log); size } }",
        "match s { Store { log, name, size } => match log { file.File { .. } => size } }",
        "let struct { log, .. } = s; match log { file.File {} => 0 }",
    ] {
        let source = format!(
            "{PRELUDE}
             struct Store {{ log: file.File, name: Bytes, size: i64 }}
             fn finish(s: Store) -> i64 ! {{io, panic}} {{ {body} }}
             fn main() -> i64 ! {{io, alloc, panic}} {{ 0 }}"
        );
        let error = checked(&source)
            .err()
            .unwrap_or_else(|| panic!("accepted: {body}"));
        assert!(
            error.contains("linear") || error.contains("private"),
            "{error}"
        );
    }
}
