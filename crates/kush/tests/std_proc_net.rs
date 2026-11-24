//! STD-PROC-NET-IN-KUSH: `std.proc.run` and `std.net.exchange`, written in
//! Kush over one-call `std.sys` stubs, against the `PROC.run` and
//! `NET.tcp_exchange` builtins they replace. Every program runs each scenario
//! through the builtin and then through std, printing the same two numbers
//! for both, in the reference evaluator and natively.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io::{self, Read, Write};
use std::net::TcpListener;
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<std-proc-net-test>", source).unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str, arguments: &[String]) -> String {
    let program = checked(source);
    let mut args = vec![b"kush-program".to_vec()];
    args.extend(
        arguments
            .iter()
            .map(|argument| argument.as_bytes().to_vec()),
    );
    let host = Host::new(args, Vec::new());
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &host)
        .unwrap();
    assert_eq!(status, 0);
    assert_eq!(
        stats.allocations, stats.deallocations,
        "reference cleanup must be balanced"
    );
    String::from_utf8(output).unwrap()
}

fn native(source: &str, arguments: &[String]) -> String {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("proc-net");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary)
        .args(arguments)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// The output's numbers in groups of four: builtin result and length, then
/// std result and length. Each pair must agree; returns the std pairs.
fn same_as_builtin(output: &str) -> Vec<(i64, i64)> {
    let numbers: Vec<i64> = output.lines().map(|line| line.parse().unwrap()).collect();
    assert_eq!(numbers.len() % 4, 0, "{output}");
    numbers
        .chunks(4)
        .enumerate()
        .map(|(index, chunk)| {
            assert_eq!(
                (chunk[0], chunk[1]),
                (chunk[2], chunk[3]),
                "scenario {index}: builtin and std differ\n{output}"
            );
            (chunk[2], chunk[3])
        })
        .collect()
}

const SUBPROCESS: &str = r#"
use std.proc;
use std.proc.Outcome;
use std.result.Result;

fn builtin(program: &Bytes, arguments: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    let mut output = Bytes.with_capacity(capacity);
    match PROC.run(program, arguments, &mut output, timeout) {
        Result.Ok(status) => print_i64(status),
        Result.Err(code) => print_i64(-code),
    }
    print_i64(Bytes.len(&output));
}

fn library(program: &Bytes, arguments: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    match proc.run(program, arguments, Bytes.with_capacity(capacity), timeout) {
        Outcome.Exited(output, status) => { print_i64(status); print_i64(Bytes.len(&output)); },
        Outcome.Stopped(output, code) => { print_i64(-code); print_i64(Bytes.len(&output)); },
        Outcome.Failed(code) => { print_i64(-code); print_i64(0); },
    }
}

fn both(program: &Bytes, arguments: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    builtin(program, arguments, capacity, timeout);
    library(program, arguments, capacity, timeout);
}

fn main() -> i64 ! {io, alloc} {
    let echo = Bytes.from("/bin/echo");
    let words = Bytes.from("hello\0\0world\0");
    both(&echo, &words, 64, 5000);
    both(&echo, &words, 4, 5000);
    let sleep = Bytes.from("/bin/sleep");
    let one = Bytes.from("1");
    both(&sleep, &one, 8, 60);
    let missing = Bytes.from("/definitely/not/a/kush-program");
    both(&missing, &one, 8, 1000);
    let sh = Bytes.from("/bin/sh");
    let killed = Bytes.from("-c\0kill -9 $$");
    both(&sh, &killed, 8, 0);
    let big = Bytes.from("-c\0head -c 100000 /dev/zero; exit 3");
    both(&sh, &big, 200000, 5000);
    both(&sh, &big, 8, -1);
    let partial = Bytes.from("-c\0printf abc; sleep 1");
    both(&sh, &partial, 8, 200);
    let empty = Bytes.with_capacity(0);
    both(&empty, &one, 8, 1000);
    let nul = Bytes.from("/bin/echo\0x");
    both(&nul, &one, 8, 1000);
    0
}
"#;

#[test]
fn subprocesses_match_the_builtin() {
    let expected = vec![
        (0, 12),     // "hello world\n"; empty segments are skipped
        (-27, 4),    // EFBIG keeps the filled prefix
        (-110, 0),   // ETIMEDOUT, child killed
        (-2, 0),     // ENOENT from the exec
        (137, 0),    // 128 + SIGKILL
        (3, 100000), // many reads, then the exit status
        (-22, 0),    // a negative timeout is EINVAL
        (-110, 3),   // the timeout keeps what was read
        (-22, 0),    // empty program
        (-22, 0),    // NUL in the program
    ];
    let reference = reference(SUBPROCESS, &[]);
    assert_eq!(same_as_builtin(&reference), expected, "{reference}");
    assert_eq!(native(SUBPROCESS, &[]), reference);
}

/// One connection per request: "ping" gets "pong\n", "big" 64 bytes,
/// "silent" nothing until the client gives up, anything else an HTTP reply.
fn start_server() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { return };
            thread::spawn(move || {
                let mut request = Vec::new();
                let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
                let _ = stream.read_to_end(&mut request);
                if request.starts_with(b"silent") {
                    thread::sleep(Duration::from_millis(500));
                    return;
                }
                let reply: Vec<u8> = if request.starts_with(b"ping") {
                    b"pong\n".to_vec()
                } else if request.starts_with(b"big") {
                    vec![b'x'; 64]
                } else {
                    b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\nConnection: close\r\n\r\nhello"
                        .to_vec()
                };
                let _ = stream.write_all(&reply);
            });
        }
    });
    port
}

/// A port with nothing listening.
fn closed_port() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    listener.local_addr().unwrap().port()
}

const NETWORK: &str = r#"
use std.http;
use std.net;
use std.net.Outcome;
use std.result.Result;
use std.text;

fn builtin(host: &Bytes, port: i64, request: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    let mut response = Bytes.with_capacity(capacity);
    match NET.tcp_exchange(host, port, request, &mut response, timeout) {
        Result.Ok(count) => print_i64(count),
        Result.Err(code) => print_i64(-code),
    }
    print_i64(Bytes.len(&response));
}

fn library(host: &Bytes, port: i64, request: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    match net.exchange(host, port, request, Bytes.with_capacity(capacity), timeout) {
        Outcome.Received(response, count) => { print_i64(count); print_i64(Bytes.len(&response)); },
        Outcome.Stopped(response, code) => { print_i64(-code); print_i64(Bytes.len(&response)); },
        Outcome.Failed(code) => { print_i64(-code); print_i64(0); },
    }
}

fn both(host: &Bytes, port: i64, request: &Bytes, capacity: i64, timeout: i64) -> Unit ! {io, alloc} {
    builtin(host, port, request, capacity, timeout);
    library(host, port, request, capacity, timeout);
}

fn argument(index: i64) -> i64 ! {io, alloc} {
    let digits = match ENV.arg(index, Bytes.with_capacity(16)) {
        Ok(value) => value,
        Err(code) => { return -code; },
    };
    match text.parse_i64(&digits) {
        Result.Ok(value) => value,
        Result.Err(code) => -code,
    }
}

fn main() -> i64 ! {io, alloc} {
    let port = argument(1);
    let closed = argument(2);
    let host = Bytes.from("127.0.0.1");
    let ping = Bytes.from("ping\n");
    both(&host, port, &ping, 1024, 5000);
    both(&host, port, &ping, 1024, 0);
    let big = Bytes.from("big");
    both(&host, port, &big, 8, 5000);
    both(&host, port, &big, 64, 5000);
    let silent = Bytes.from("silent");
    both(&host, port, &silent, 16, 60);
    both(&host, closed, &ping, 16, 5000);
    both(&host, 0, &ping, 16, 5000);
    both(&host, 65536, &ping, 16, 5000);
    both(&host, port, &ping, 16, -1);
    let nul = Bytes.from("127.0.0.1\0");
    both(&nul, port, &ping, 16, 5000);
    // std.http now goes through std.net.
    let path = Bytes.from("/");
    let answer = match http.get(&host, port, &path, 5000) {
        Result.Ok(value) => value,
        Result.Err(code) => { print_i64(-code); return 0; },
    };
    print_i64(http.response_status(&answer));
    print_i64(Bytes.len(&answer.body));
    print_i64(http.response_status(&answer));
    print_i64(Bytes.len(&answer.body));
    0
}
"#;

#[test]
fn tcp_exchanges_match_the_builtin() {
    let arguments = vec![start_server().to_string(), closed_port().to_string()];
    let reference = reference(NETWORK, &arguments);
    let pairs = same_as_builtin(&reference);
    let codes: Vec<i64> = pairs.iter().map(|pair| pair.0).collect();
    assert_eq!(
        codes,
        vec![5, 5, -27, 64, -110, -111, -22, -22, -22, -22, 200],
        "{reference}"
    );
    assert_eq!(pairs[2].1, 8, "EFBIG keeps the filled prefix");
    assert_eq!(pairs[10].1, 5, "the HTTP body");
    assert_eq!(native(NETWORK, &arguments), reference);
}
