//! Checked host APIs: filesystem, arguments/environment, clocks, subprocesses,
//! and plain TCP. Reference evaluation uses `Host` injection; native builds
//! read the real process. Both must agree on status, output, bounded-buffer
//! ownership, and errno values.

use kush::{Host, executable};
use std::{
    fs, io,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
    time::Duration,
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn unique_directory(label: &str) -> PathBuf {
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("kush-host-api-{label}-{}-{id}", std::process::id()));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir(&path).unwrap();
    path
}

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<host-api-test>", source).unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

struct Observation {
    status: i64,
    output: Vec<u8>,
}

fn reference(source: &str, arguments: &[String], environment: &[(String, String)]) -> Observation {
    let program = checked(source);
    let mut args = vec![b"kush-program".to_vec()];
    args.extend(
        arguments
            .iter()
            .map(|argument| argument.as_bytes().to_vec()),
    );
    let host = Host::new(
        args,
        environment
            .iter()
            .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
            .collect(),
    );
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &host)
        .unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "reference cleanup must be balanced"
    );
    Observation { status, output }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(
    source: &str,
    arguments: &[String],
    environment: &[(String, String)],
    current: &Path,
) -> Observation {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("host-program");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary)
        .args(arguments)
        .env_clear()
        .envs(environment.iter().map(|(name, value)| (name, value)))
        .current_dir(current)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.stderr.is_empty(),
        "native stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Observation {
        status: output.status.code().unwrap() as i64,
        output: output.stdout,
    }
}

/// Both backends receive the same arguments and environment but separate
/// filesystem roots. This keeps writes isolated and lets the reference and
/// native runs be compared without sharing mutable state.
fn compare(
    source: &str,
    arguments: impl Fn(&Path) -> Vec<String>,
    environment: &[(String, String)],
) {
    let reference_root = unique_directory("reference");
    let native_root = unique_directory("native");
    let expected = reference(source, &arguments(&reference_root), environment);
    let actual = native(source, &arguments(&native_root), environment, &native_root);
    let _ = fs::remove_dir_all(&reference_root);
    let _ = fs::remove_dir_all(&native_root);
    assert_eq!(
        actual.status,
        expected.status,
        "status mismatch\n{}",
        String::from_utf8_lossy(&actual.output)
    );
    assert_eq!(
        actual.output,
        expected.output,
        "output mismatch\nreference: {}\nnative: {}",
        String::from_utf8_lossy(&expected.output),
        String::from_utf8_lossy(&actual.output)
    );
}

const FILESYSTEM: &str = r#"
use std.result.Result;
use std.text;
use std.path;

fn show(value: &Bytes) -> Unit ! {io, panic} {
    let mut i = 0;
    while i < Bytes.len(value) {
        print_i64(Bytes.get(value, i));
        i = i + 1;
    }
    print_i64(-1);
}

fn main() -> i64 ! {io, alloc, panic} {
    let root = match ENV.arg(1, Bytes.with_capacity(4096)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    let file_name = Bytes.from("notes.txt");
    let sub_name = Bytes.from("sub");
    let moved_name = Bytes.from("moved.txt");
    let file = path.join(&root, &file_name);
    let sub = path.join(&root, &sub_name);
    let moved = path.join(&root, &moved_name);
    let missing = path.join(&root, &Bytes.from("missing.txt"));
    let hello = Bytes.from("hello");
    let world = Bytes.from(" world");
    print_i64(match FS.write(&file, &hello) { Ok(count) => count, Err(code) => -code });
    print_i64(match FS.append(&file, &world) { Ok(count) => count, Err(code) => -code });
    let read = match FS.read(&file, Bytes.with_capacity(64)) {
        Ok(value) => value,
        Err(code) => { print_i64(-code); return 0; },
    };
    show(&read);
    drop(read);
    print_i64(match FS.size(&file) { Ok(size) => size, Err(code) => -code });
    print_i64(match FS.is_file(&file) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    print_i64(match FS.is_dir(&file) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    print_i64(match FS.exists(&missing) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    print_i64(match FS.read(&missing, Bytes.with_capacity(8)) { Ok(_) => -1, Err(code) => code });
    print_i64(match FS.write(&sub, &hello) { Ok(_) => -1, Err(code) => code });
    print_i64(match FS.read(&file, Bytes.with_capacity(4)) { Ok(_) => -1, Err(code) => code });
    print_i64(match FS.mkdir(&sub) { Ok(_) => 0, Err(code) => -code });
    print_i64(match FS.is_dir(&sub) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    let listing = match FS.list(&root, Bytes.with_capacity(512)) {
        Ok(value) => value,
        Err(code) => { print_i64(-code); return 0; },
    };
    let file_needle = Bytes.from("notes.txt");
    let sub_needle = Bytes.from("sub\n");
    let has_file = text.contains(&listing, &file_needle);
    let has_sub = text.contains(&listing, &sub_needle);
    print_i64(if has_file { 1 } else { 0 });
    print_i64(if has_sub { 1 } else { 0 });
    drop(listing);
    print_i64(match FS.rename(&file, &moved) { Ok(_) => 0, Err(code) => -code });
    print_i64(match FS.exists(&file) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    print_i64(match FS.exists(&moved) { Ok(flag) => if flag { 1 } else { 0 }, Err(code) => -code });
    print_i64(match FS.remove(&moved) { Ok(_) => 0, Err(code) => -code });
    print_i64(match FS.remove_dir(&sub) { Ok(_) => 0, Err(code) => -code });
    print_i64(match FS.remove(&missing) { Ok(_) => 0, Err(code) => code });
    drop(hello);
    drop(world);
    drop(root);
    0
}
"#;

#[test]
fn filesystem_round_trip_metadata_listing_paths_and_errors_agree() {
    compare(FILESYSTEM, |root| vec![root.display().to_string()], &[]);
}

const WRITE_EXCLUSIVE: &str = r#"
use std.result.Result;
use std.text;
use std.path;

fn show(value: &Bytes) -> Unit ! {io, panic} {
    let mut i = 0;
    while i < Bytes.len(value) {
        print_i64(Bytes.get(value, i));
        i = i + 1;
    }
    print_i64(-1);
}

fn main() -> i64 ! {io, alloc, panic} {
    let root = match ENV.arg(1, Bytes.with_capacity(4096)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    let victim = path.join(&root, &Bytes.from("victim.txt"));
    let planted = path.join(&root, &Bytes.from("planted.tmp"));
    let fresh = path.join(&root, &Bytes.from("fresh.tmp"));
    let data = Bytes.from("over\n");
    let initial = match FS.read(&victim, Bytes.with_capacity(16)) {
        Ok(value) => value,
        Err(code) => { print_i64(-code); return 0; },
    };
    show(&initial);
    drop(initial);
    match FS.write_exclusive(&planted, &data) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    print_i64(match FS.write_exclusive(&fresh, &data) {
        Result.Ok(count) => count,
        Result.Err(code) => -code,
    });
    match FS.write_exclusive(&fresh, &data) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    let read = match FS.read(&fresh, Bytes.with_capacity(16)) {        Ok(value) => value,
        Err(code) => { print_i64(-code); return 0; },
    };
    show(&read);
    drop(read);
    drop(data);
    drop(fresh);
    drop(planted);
    drop(victim);
    drop(root);
    0
}
"#;

/// The victim stays untouched through the planted symlink, and both the
/// reference and native runs create the fresh file with 0600 permissions.
fn prepare_exclusive_fixture(root: &Path) {
    fs::write(root.join("victim.txt"), b"keep\n").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(root.join("victim.txt"), root.join("planted.tmp")).unwrap();
    #[cfg(not(unix))]
    fs::write(root.join("planted.tmp"), b"preexisting").unwrap();
}

fn check_exclusive_run(root: &Path, observation: &Observation) {
    assert_eq!(observation.status, 0);
    if !cfg!(unix) {
        return;
    }
    // Byte values stream: victim content shown before and after the planted
    // attempt, the EEXIST refusal, the fresh 5-byte create, a second refusal,
    // and the verification read of the fresh file.
    let expected: &[&str] = &[
        "107\n101\n101\n112\n10\n-1\n",
        "17\n",
        "5\n",
        "17\n",
        "111\n118\n101\n114\n10\n-1\n",
    ];
    assert_eq!(
        observation.output,
        expected
            .iter()
            .flat_map(|line| line.as_bytes())
            .cloned()
            .collect::<Vec<u8>>()
    );
    assert_eq!(fs::read(root.join("victim.txt")).unwrap(), b"keep\n");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = fs::metadata(root.join("fresh.tmp"))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(mode & 0o777, 0o600, "fresh file mode: {mode:o}");
    }
}

#[test]
fn write_exclusive_refuses_planted_paths_and_creates_0600_files() {
    let reference_root = unique_directory("exclusive-reference");
    prepare_exclusive_fixture(&reference_root);
    let expected = reference(
        WRITE_EXCLUSIVE,
        &[reference_root.display().to_string()],
        &[],
    );
    check_exclusive_run(&reference_root, &expected);
    let native_root = unique_directory("exclusive-native");
    prepare_exclusive_fixture(&native_root);
    let actual = native(
        WRITE_EXCLUSIVE,
        &[native_root.display().to_string()],
        &[],
        &native_root,
    );
    check_exclusive_run(&native_root, &actual);
    let _ = fs::remove_dir_all(&reference_root);
    let _ = fs::remove_dir_all(&native_root);
}

const ENVIRONMENT: &str = r#"
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    let argument_count = match ENV.arg_count() {
        Ok(value) => value,
        Err(code) => return code,
    };
    print_i64(argument_count - 1);
    let mut at = 1;
    while at < argument_count {
        match ENV.arg(at, Bytes.with_capacity(32)) {
            Ok(value) => {
                print_i64(Bytes.len(&value));
                let mut i = 0;
                while i < Bytes.len(&value) {
                    print_i64(Bytes.get(&value, i));
                    i = i + 1;
                }
                drop(value);
            },
            Err(code) => print_i64(-code),
        }
        at = at + 1;
    }
    print_i64(match ENV.arg(99, Bytes.with_capacity(8)) {
        Ok(value) => { drop(value); -1 },
        Err(code) => code,
    });
    let name = Bytes.from("KUSH_HOST_TEST");
    match ENV.var(&name, Bytes.with_capacity(32)) {
        Ok(value) => {
            print_i64(Bytes.len(&value));
            print_i64(Bytes.get(&value, 0));
            drop(value);
        },
        Err(code) => print_i64(-code),
    }
    let missing_name = Bytes.from("KUSH_HOST_MISSING");
    match ENV.var(&missing_name, Bytes.with_capacity(8)) {
        Ok(value) => { print_i64(-1); drop(value); },
        Err(code) => print_i64(code),
    }
    print_i64(match ENV.var_count() { Ok(value) => value, Err(code) => -code });
    drop(name);
    drop(missing_name);
    0
}
"#;

#[test]
fn arguments_and_environment_are_explicit_and_bounded() {
    compare(
        ENVIRONMENT,
        |_| {
            vec![
                "alpha".to_owned(),
                "two words".to_owned(),
                "".to_owned(),
                "z".repeat(80),
            ]
        },
        &[("KUSH_HOST_TEST".to_owned(), "value".to_owned())],
    );
}

const HOSTILE_NAMES: &str = r#"
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    let bad = Bytes.from("a\0b");
    let empty = Bytes.with_capacity(0);
    print_i64(match FS.read(&bad, Bytes.with_capacity(8)) {
        Ok(_) => -1,
        Err(code) => code,
    });
    print_i64(match FS.write(&bad, &empty) {
        Ok(_) => -1,
        Err(code) => code,
    });
    print_i64(match ENV.var(&bad, Bytes.with_capacity(8)) {
        Ok(_) => -1,
        Err(code) => code,
    });
    let mut output = Bytes.with_capacity(8);
    print_i64(match PROC.run(&bad, &empty, &mut output, 100) {
        Ok(_) => -1,
        Err(code) => code,
    });
    print_i64(Bytes.len(&output));
    drop(output);
    let mut response = Bytes.with_capacity(8);
    print_i64(match NET.tcp_exchange(&bad, 80, &empty, &mut response, 100) {
        Ok(_) => -1,
        Err(code) => code,
    });
    print_i64(Bytes.len(&response));
    drop(response);
    drop(bad);
    drop(empty);
    0
}
"#;

#[test]
fn embedded_nul_bytes_are_rejected_before_host_calls() {
    compare(HOSTILE_NAMES, |_| Vec::new(), &[]);
}

const TIME_AND_ERRORS: &str = r#"
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    print_i64(match TIME.unix_seconds() { Ok(_) => 1, Err(_) => 0 });
    let first = match TIME.monotonic_ns() { Ok(value) => value, Err(code) => return code };
    print_i64(match TIME.sleep_ms(5) { Ok(_) => 0, Err(code) => code });
    let second = match TIME.monotonic_ns() { Ok(value) => value, Err(code) => return code };
    print_i64(if second >= first { 1 } else { 0 });
    print_i64(match TIME.sleep_ms(-1) { Ok(_) => -1, Err(code) => code });
    let text = match OS.strerror(2, Bytes.with_capacity(64)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    print_i64(Bytes.len(&text));
    print_i64(Bytes.get(&text, 0));
    drop(text);
    print_i64(match OS.strerror(-1, Bytes.with_capacity(8)) { Ok(_) => -1, Err(code) => code });
    0
}
"#;

#[test]
fn clocks_sleep_and_error_messages_are_observable() {
    compare(TIME_AND_ERRORS, |_| Vec::new(), &[]);
}

const SUBPROCESS: &str = r#"
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    let echo = Bytes.from("/bin/echo");
    let arguments = Bytes.from("hello\0world");
    let mut first_output = Bytes.with_capacity(64);
    let first_status = match PROC.run(&echo, &arguments, &mut first_output, 5000) {
        Ok(status) => status,
        Err(code) => { print_i64(-code); return 0; },
    };
    print_i64(first_status);
    print_i64(Bytes.len(&first_output));
    print_i64(Bytes.get(&first_output, 0));
    drop(first_output);
    let child = Bytes.from("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
    let mut captured = Bytes.with_capacity(64);
    let captured_status = match PROC.run(&echo, &child, &mut captured, 5000) {
        Ok(status) => status,
        Err(code) => { print_i64(-code); return 0; },
    };
    print_i64(captured_status);
    print_i64(Bytes.len(&captured));
    drop(captured);
    let mut overflow = Bytes.with_capacity(4);
    match PROC.run(&echo, &child, &mut overflow, 5000) {
        Ok(status) => print_i64(status),
        Err(code) => print_i64(code),
    }
    print_i64(Bytes.len(&overflow));
    drop(overflow);
    drop(echo);
    drop(arguments);
    drop(child);
    0
}
"#;

#[test]
fn subprocess_runs_capture_bounded_output_and_report_failures() {
    compare(SUBPROCESS, |_| Vec::new(), &[]);
}

const SUBPROCESS_ERRORS: &str = r#"
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    let sleep = Bytes.from("/bin/sleep");
    let one = Bytes.from("1");
    let mut first_output = Bytes.with_capacity(8);
    print_i64(match PROC.run(&sleep, &one, &mut first_output, 60) {
        Ok(_) => -1,
        Err(code) => code,
    });
    drop(first_output);
    let missing = Bytes.from("/definitely/not/a/kush-program");
    let empty = Bytes.with_capacity(0);
    let mut second_output = Bytes.with_capacity(8);
    print_i64(match PROC.run(&missing, &empty, &mut second_output, 1000) {
        Ok(_) => -1,
        Err(code) => code,
    });
    drop(second_output);
    drop(sleep);
    drop(one);
    drop(missing);
    drop(empty);
    0
}
"#;

#[test]
fn subprocess_timeout_and_missing_program_report_errno() {
    compare(SUBPROCESS_ERRORS, |_| Vec::new(), &[]);
}

const NETWORK: &str = r#"
use std.result.Result;
use std.http;
use std.text;

fn main() -> i64 ! {io, alloc, panic} {
    let host = Bytes.from("127.0.0.1");
    let port_bytes = match ENV.arg(1, Bytes.with_capacity(16)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    let port = match text.parse_i64(&port_bytes) {
        Result.Ok(value) => value,
        Result.Err(code) => return code,
    };
    let request = Bytes.from("ping\n");
    let mut response = Bytes.with_capacity(1024);
    match NET.tcp_exchange(&host, port, &request, &mut response, 5000) {
        Ok(count) => print_i64(count),
        Err(code) => { print_i64(-code); return 0; },
    }
    print_i64(Bytes.len(&response));
    print_i64(Bytes.get(&response, 0));
    drop(response);
    let path = Bytes.from("/");
    let answer = match http.get(&host, port, &path, 5000) {
        Result.Ok(value) => value,
        Result.Err(code) => { print_i64(-code); return 0; },
    };
    print_i64(http.response_status(&answer));
    print_i64(Bytes.len(&answer.body));
    print_i64(Bytes.get(&answer.body, 0));
    drop(answer);
    drop(request);
    drop(host);
    drop(port_bytes);
    drop(path);
    0
}
"#;

fn start_http_pair_server() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    thread::spawn(move || {
        for _ in 0..2 {
            let Ok((mut stream, _)) = listener.accept() else {
                return;
            };
            let mut buffer = [0u8; 8192];
            let _ = io::Read::read(&mut stream, &mut buffer);
            let reply: &[u8] = if buffer.starts_with(b"ping") {
                b"pong\n"
            } else {
                b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\nConnection: close\r\n\r\nhello"
            };
            let _ = io::Write::write_all(&mut stream, reply);
        }
    });
    port
}

#[test]
fn tcp_exchange_and_http_client_work_on_loopback() {
    let reference_port = start_http_pair_server();
    let native_port = start_http_pair_server();
    let expected = reference(NETWORK, &[reference_port.to_string()], &[]);
    assert_eq!(expected.output, b"5\n5\n112\n200\n5\n104\n");
    let root = unique_directory("net-native");
    let actual = native(NETWORK, &[native_port.to_string()], &[], &root);
    let _ = fs::remove_dir_all(&root);
    assert_eq!(actual.status, expected.status);
    assert_eq!(actual.output, expected.output);
}

const NETWORK_TIMEOUT: &str = r#"
use std.result.Result;
use std.text;

fn main() -> i64 ! {io, alloc, panic} {
    let port_bytes = match ENV.arg(1, Bytes.with_capacity(16)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    let port = match text.parse_i64(&port_bytes) {
        Result.Ok(value) => value,
        Result.Err(code) => return code,
    };
    let host = Bytes.from("127.0.0.1");
    let request = Bytes.from("ping");
    let mut response = Bytes.with_capacity(16);
    print_i64(match NET.tcp_exchange(&host, port, &request, &mut response, 60) {
        Ok(_) => -1,
        Err(code) => code,
    });
    drop(response);
    drop(host);
    drop(request);
    drop(port_bytes);
    0
}
"#;

fn start_silent_server() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    thread::spawn(move || {
        let mut held = Vec::new();
        for _ in 0..2 {
            if let Ok((stream, _)) = listener.accept() {
                held.push(stream);
            }
        }
        thread::sleep(Duration::from_millis(300));
    });
    port
}

#[test]
fn tcp_timeout_is_explicit_in_both_backends() {
    let port = start_silent_server();
    let arguments = vec![port.to_string()];
    let expected = reference(NETWORK_TIMEOUT, &arguments, &[]);
    assert_eq!(expected.status, 0);
    assert_eq!(String::from_utf8_lossy(&expected.output), "110\n");
    let root = unique_directory("timeout-native");
    let actual = native(NETWORK_TIMEOUT, &arguments, &[], &root);
    let _ = fs::remove_dir_all(&root);
    assert_eq!(actual.status, expected.status);
    assert_eq!(actual.output, expected.output);
}

#[test]
fn http_response_boundaries_preserve_zero_one_and_multiple_headers() {
    let source = r#"use std.result.Result; use std.text; use std.http;
        fn main() -> i64 ! {io, alloc, panic} {
            let port_text = match ENV.arg(1, Bytes.with_capacity(16)) { Ok(v) => v, Err(e) => return e };
            let port = match text.parse_i64(&port_text) { Result.Ok(n) => n, Result.Err(e) => return e };
            let host = Bytes.from("127.0.0.1"); let path = Bytes.from("/");
            let response = match http.get(&host, port, &path, 5000) { Result.Ok(v) => v, Result.Err(e) => return e };
            print_i64(http.response_status(&response));
            print_i64(Bytes.len(&response.headers));
            print_i64(Bytes.len(&response.body));
            let mut i = 0;
            while i < Bytes.len(&response.body) { print_i64(Bytes.get(&response.body, i)); i = i + 1; }
            0
        }"#;
    for (status, headers, body) in [
        (200, "", "hello"),
        (200, "Content-Length: 5", "hello"),
        (200, "Content-Length: 5\r\nConnection: close", "hello"),
        (204, "", ""),
    ] {
        let response = format!(
            "HTTP/1.1 {status} OK\r\n{}\r\n{body}",
            if headers.is_empty() {
                String::new()
            } else {
                format!("{headers}\r\n")
            }
        );
        let start = || {
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let port = listener.local_addr().unwrap().port();
            let reply = response.clone();
            thread::spawn(move || {
                let (mut stream, _) = listener.accept().unwrap();
                let mut request = Vec::new();
                io::Read::read_to_end(&mut stream, &mut request).unwrap();
                io::Write::write_all(&mut stream, reply.as_bytes()).unwrap();
            });
            port
        };
        let observed = reference(source, &[start().to_string()], &[]);
        let mut expected = format!("{status}\n{}\n{}\n", headers.len(), body.len());
        for byte in body.bytes() {
            expected.push_str(&format!("{byte}\n"));
        }
        assert_eq!(observed.status, 0);
        assert_eq!(observed.output, expected.as_bytes());
        let root = unique_directory("http-boundary");
        let observed = native(source, &[start().to_string()], &[], &root);
        assert_eq!(observed.status, 0);
        assert_eq!(observed.output, expected.as_bytes());
        fs::remove_dir_all(root).unwrap();
    }
}

// FS-EXISTS-BOOL: the metadata predicates return Result<Bool, i64>.
const FS_PREDICATES_BOOL: &str = r#"
use std.result.Result;
use std.path;

fn flag(r: Result<Bool, i64>) -> i64 ! {panic} {
    match r { Ok(b) => if b { 1 } else { 0 }, Err(code) => -code }
}

fn main() -> i64 ! {io, alloc, panic} {
    let root = match ENV.arg(1, Bytes.with_capacity(4096)) {
        Ok(value) => value,
        Err(code) => return code,
    };
    let file = path.join(&root, &Bytes.from("f.txt"));
    let missing = path.join(&root, &Bytes.from("nope"));
    let data = Bytes.from("x");
    match FS.write(&file, &data) { Ok(_) => {}, Err(code) => return code };
    let both = match (FS.exists(&file), FS.is_dir(&root)) {
        (Ok(a), Ok(b)) => a && b,
        _ => false,
    };
    print_i64(if both { 1 } else { 0 });
    print_i64(flag(FS.is_file(&file)));
    print_i64(flag(FS.is_file(&root)));
    print_i64(flag(FS.is_dir(&file)));
    print_i64(flag(FS.exists(&missing)));
    print_i64(flag(FS.is_file(&missing)));
    let nul = Bytes.push(Bytes.from("a"), 0);
    print_i64(flag(FS.exists(&nul)));
    drop(nul);
    match FS.exists(&missing) {
        Ok(true) => print_i64(7),
        Ok(false) => print_i64(8),
        Err(_) => print_i64(9),
    }
    match FS.remove(&file) { Ok(_) => {}, Err(code) => return code };
    drop(data);
    drop(root);
    0
}
"#;

#[test]
fn filesystem_predicates_return_bool_in_both_backends() {
    let root = unique_directory("bool-check");
    let observed = reference(FS_PREDICATES_BOOL, &[root.display().to_string()], &[]);
    let _ = fs::remove_dir_all(&root);
    let lines: Vec<&str> = std::str::from_utf8(&observed.output)
        .unwrap()
        .lines()
        .collect();
    assert_eq!(lines, ["1", "1", "0", "0", "0", "0", "-22", "8"]);
    assert_eq!(observed.status, 0);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    compare(
        FS_PREDICATES_BOOL,
        |root| vec![root.display().to_string()],
        &[],
    );
}

#[test]
fn filesystem_predicates_are_not_integers() {
    for call in ["FS.exists(&p)", "FS.is_file(&p)", "FS.is_dir(&p)"] {
        let source = format!(
            "use std.result.Result;
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let p = Bytes.from(\"x\");
                let n: i64 = match {call} {{ Ok(v) => v, Err(code) => code }};
                drop(p);
                n
            }}"
        );
        let program = kush::program::load_source("<fs-bool>", &source).unwrap();
        let error = executable::check_program(&program)
            .err()
            .unwrap_or_else(|| panic!("an i64 use of {call} must be rejected"));
        assert!(
            error.message.contains("Bool") || error.message.contains("mismatch"),
            "{}",
            error.message
        );
    }
}
