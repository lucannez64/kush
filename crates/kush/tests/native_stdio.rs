#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable,
    native::{self, Scratch},
};
use std::{
    fs::OpenOptions,
    io::Write,
    path::PathBuf,
    process::{Command, Stdio},
};

fn build(source: &str) -> (Scratch, PathBuf) {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("program");
    native::build(&executable::check(source).unwrap(), &binary).unwrap();
    (scratch, binary)
}
fn compare_once(source: &str, input: &[u8]) -> (i64, Vec<u8>) {
    let program = executable::check(source).unwrap();
    let mut expected_output = Vec::new();
    let (expected_status, stats) = program
        .evaluate_with_io_and_stats(&mut &input[..], &mut expected_output)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    let (scratch, binary) = build(source);
    let mut child = Command::new(binary)
        .current_dir(scratch.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // Feed input concurrently while draining output: streaming programs can
    // fill both OS pipes when the test payload exceeds pipe capacity. A program
    // may also stop reading before its input is exhausted (for example a
    // zero-capacity buffer reports an error on the first read), which closes
    // the pipe under the writer. That early-close race is not a result: status
    // and output are still compared with the reference evaluator below.
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let result = child.wait_with_output().unwrap();
    if let Err(error) = writer.join().unwrap() {
        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe, "{error}");
    }
    assert_eq!(
        result.status.code(),
        Some((expected_status as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, expected_output);
    assert!(
        result.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    (expected_status, expected_output)
}

/// STD-IO-IN-KUSH: the same program through `std.io` (Kush loops over
/// `std.sys`) instead of the `IO.*` builtins. `std.io` returns
/// `std.result.Result`, so a local conventional `Result` declaration becomes
/// that import.
fn through_std_io(source: &str) -> String {
    let mut text = source
        .replace("IO.", "io.")
        .replace("Stdin", "io.Input")
        .replace("Stdout", "io.Output");
    for local in [
        "enum Result<T, E> { Ok(T), Err(E) }",
        "enum Result<T,E>{Ok(T),Err(E)}",
        "enum Result<T,E>{Err(E),Ok(T)}",
    ] {
        text = text.replace(local, "use std.result.Result;");
    }
    if !text.contains("use std.result.Result;") {
        text = format!("use std.result.Result;\n{text}");
    }
    // `use` items go after a `module` header when there is one.
    match text.find("module ") {
        Some(0) => {
            let end = text.find(';').unwrap() + 1;
            format!("{}\nuse std.io;\n{}", &text[..end], &text[end..])
        }
        _ => format!("use std.io;\n{text}"),
    }
}

/// Reference and native runs agree, and the `std.io` version of the program
/// prints exactly what the builtin version prints.
fn compare(source: &str, input: &[u8]) {
    let builtin = compare_once(source, input);
    let library = compare_once(&through_std_io(source), input);
    assert_eq!(
        (library.0, String::from_utf8_lossy(&library.1)),
        (builtin.0, String::from_utf8_lossy(&builtin.1)),
        "std.io differs from IO.*"
    );
}

#[test]
fn standard_stream_copy_preserves_raw_bytes_and_rejects_excess_input() {
    let example = include_str!("../../../examples/stdio.kush");
    for input in [b"".as_slice(), b"Hello\n\0\xff\xc3\xa9"] {
        compare(example, input);
    }
    compare(example, &vec![b'x'; 4096]);
    compare(example, &vec![b'x'; 4097]);
}

#[test]
fn line_input_and_todo_sessions_match_reference() {
    let source =
        include_str!("../../../examples/stdio.kush").replace("IO.read_all", "IO.read_line");
    for input in [
        b"".as_slice(),
        b"a\nb\n",
        b"\n",
        b"partial",
        b"\0\xff\nnext",
    ] {
        compare(&source, input);
    }
    compare(&source, &vec![b'x'; 4097]);
    let todo = include_str!("../../../examples/todo.kush");
    compare(
        todo,
        b"a Buy milk\na Write Kush\nt 1\nf done\nf open\nd 2\nt 99\nq\n",
    );
    compare(todo, b"a Last command without newline");
    compare(todo, b"a First\r\nt 1\r\nq\r\n");
}

#[test]
fn parser_consumes_piped_input_in_native_code() {
    let example = include_str!("../../../examples/expression-stdin.kush");
    for input in [
        "12+3*10\n",
        "2*3+4",
        " 42 \t\r\n",
        "1+2*3+",
        "",
        "9223372036854775808",
    ] {
        compare(example, input.as_bytes());
    }
    compare(example, &vec![b'1'; 4097]);
}

#[test]
fn read_success_and_errors_use_declared_tags_even_when_result_variants_are_reversed() {
    let source = r#"
        enum Result<T,E>{Err(E),Ok(T)}
        fn main()->i64 ! {io,alloc,panic} {
            let mut b=Bytes.with_capacity(3);b=Bytes.push_reserved(b,65);
            match IO.read_all(IO.stdin(),b) {
                Ok(bytes)=>match IO.write(IO.stdout(),&bytes){Ok(_)=>0,Err(code)=>code},
                Err(code)=>code,
            }
        }
    "#;
    compare(source, b"BC");
    compare(source, b"BCD");
}

#[test]
fn zero_capacity_checks_eof_and_cleans_buffers_on_error_propagation() {
    let source = r#"
        enum Result<T,E>{Ok(T),Err(E)}
        #[noalloc] fn read(input:Stdin,buffer:Bytes)->Result<Bytes,i64> ! {io} {
            let keep=buffer;IO.read_all(input,keep)
        }
        fn work()->Result<Unit,i64> ! {io,alloc,panic} {
            let unused=Bytes.from("local");
            let input=read(IO.stdin(),Bytes.with_capacity(0))?;
            IO.write(IO.stdout(),&input)
        }
        fn main()->i64 ! {io,alloc,panic} {match work(){Ok(_)=>0,Err(code)=>code}}
    "#;
    compare(source, b"");
    compare(source, b"x");
}

#[test]
fn invalid_standard_descriptors_return_errors_and_release_owned_buffers() {
    let read = r#"
        enum Result<T,E>{Ok(T),Err(E)}
        fn main()->i64 ! {io,alloc,panic} {
            match IO.read_all(IO.stdin(),Bytes.with_capacity(4)) {Ok(_)=>0,Err(code)=>code}
        }
    "#;
    let write = r#"
        enum Result<T,E>{Err(E),Ok(T)}
        fn main()->i64 ! {io,alloc,panic} {
            let bytes=Bytes.from("text");
            match IO.write(IO.stdout(),&bytes) {Ok(_)=>0,Err(code)=>code}
        }
    "#;
    for (read, write) in [
        (read.to_owned(), write.to_owned()),
        (through_std_io(read), through_std_io(write)),
    ] {
        invalid_descriptors(&read, &write);
    }
}

fn invalid_descriptors(read: &str, write: &str) {
    let (_scratch, binary) = build(read);
    let write_only = OpenOptions::new().write(true).open("/dev/null").unwrap();
    let result = Command::new(&binary).stdin(write_only).output().unwrap();
    assert_eq!(result.status.code(), Some(9));
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
    let (_scratch, binary) = build(write);
    let read_only = OpenOptions::new().read(true).open("/dev/null").unwrap();
    let result = Command::new(&binary)
        .stdout(read_only)
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(9));
    assert!(result.stderr.is_empty());
}

#[test]
fn broken_stdout_pipe_returns_epipe_instead_of_terminating_the_process() {
    let source = r#"
        enum Result<T,E>{Ok(T),Err(E)}
        fn main()->i64 ! {io,alloc,panic} {
            // Reading until EOF is a barrier: the parent closes stdout before releasing stdin.
            let empty=IO.read_all(IO.stdin(),Bytes.with_capacity(0));
            let bytes=Bytes.from("text");
            match IO.write(IO.stdout(),&bytes) {Ok(_)=>0,Err(code)=>code}
        }
    "#;
    broken_pipe(source);
    broken_pipe(&through_std_io(source));
}

fn broken_pipe(source: &str) {
    let (_scratch, binary) = build(source);
    let mut child = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    drop(child.stdout.take());
    drop(child.stdin.take());
    let result = child.wait_with_output().unwrap();
    assert_eq!(result.status.code(), Some(32));
    assert!(result.stderr.is_empty());
}

#[test]
fn run_and_eval_cli_forward_stdin_to_the_program() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/expression-stdin.kush");
    for subcommand in ["run", "eval"] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_kush"))
            .arg(subcommand)
            .arg(&path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"12 + 3 * 10\n")
            .unwrap();
        let result = child.wait_with_output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(result.stdout, b"42\n");
        assert!(result.stderr.is_empty());
    }
}

#[test]
fn chunked_streaming_copy_matches_reference_without_a_total_input_cap() {
    let source = include_str!("../../../examples/stream-copy.kush");
    for input in [b"".as_slice(), b"abc\0\xff", &vec![b'x'; 20000]] {
        compare(source, input);
    }
    let chunk =
        include_str!("../../../examples/stdio.kush").replace("IO.read_all", "IO.read_chunk");
    compare(&chunk, b"abc");
    compare(&chunk, b"");
    let full = chunk.replace("Bytes.with_capacity(4096)", "Bytes.with_capacity(0)");
    compare(&full, b"");
    compare(&full, b"abc");
}
