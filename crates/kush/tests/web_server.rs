//! WEB-SERVER: `web.serve`, one task per connection on the task reactor,
//! keep-alive and pipelining, 4xx answers from the server, idle and request
//! deadlines, and a graceful stop on cancellation. Each program runs a
//! server task and a client task in one thread, in the reference evaluator
//! and natively, with the same output.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::process::{Command, Stdio};
use std::time::Duration;

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<web-server-test>", source).unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str) -> String {
    let program = checked(source);
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(stats.allocations, stats.deallocations, "reference cleanup must be balanced");
    String::from_utf8(output).unwrap()
}

fn build(source: &str) -> (kush::native::Scratch, std::path::PathBuf) {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("web-server");
    kush::native::build(&program, &binary).unwrap();
    (scratch, binary)
}

fn native(source: &str) -> String {
    let (_scratch, binary) = build(source);
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stdout));
    String::from_utf8(output.stdout).unwrap()
}

fn both(source: &str, expected: &str) {
    assert_eq!(reference(source), expected, "reference");
    assert_eq!(native(source), expected, "native");
}

const APP: &str = r#"
use std.http1;
use std.http1.Method;
use std.file;
use std.fs;
use std.io;
use std.net;
use std.result.Result;
use std.task.TaskExit;
use std.time;
use std.web;
use std.web.Config;
use std.web.Request;
use std.web.Responder;

fn app(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    if req.path_is(&Bytes.from("/hello")) {
        res.text(200, &Bytes.from("hi"))
    } else if req.path_is(&Bytes.from("/echo")) {
        res.text(200, &req.body)
    } else if req.path_is(&Bytes.from("/slow")) {
        // Cancellation ends this wait early; the answer is still sent.
        let _ = time.wait_ms(150);
        res.text(200, &Bytes.from("slow"))
    } else if req.path_is(&Bytes.from("/boom")) {
        // Panics before answering: the server answers 500.
        let empty = Bytes.with_capacity(0);
        let byte = Bytes.get(&empty, 3);
        res.status(200 + byte)
    } else if req.path_is(&Bytes.from("/owned")) {
        // Panics with owned locals, a vector and a pending temporary.
        let kept = Bytes.from("kept");
        let mut list: Vec<i64> = Vec.with_capacity(4);
        list = Vec.push(list, 1);
        let total = weigh(Bytes.from("temporary"), Bytes.get(&kept, 99), &list);
        res.status(200 + total)
    } else if req.path_is(&Bytes.from("/scoped")) {
        // Panics while a child task waits: the child is cancelled and joined.
        let code = Task.scope(fn() -> i64 ! {io, alloc, panic, suspend} {
            let child = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
                let held = Bytes.from("held by the child");
                match time.wait_ms(60000) { Result.Ok(_) => Bytes.len(&held), Result.Err(code) => code }
            });
            let _ = time.wait_ms(5);
            let empty = Bytes.with_capacity(0);
            Bytes.get(&empty, 1)
        });
        res.status(200 + code)
    } else if req.path_is(&Bytes.from("/file")) {
        // Panics holding an open file inside a Result: its unwind cleanup
        // closes it.
        let opened = file.open_read(&Bytes.from("/dev/null"));
        let empty = Bytes.with_capacity(0);
        let _ = Bytes.get(&empty, 1);
        match opened {
            Result.Ok(f) => {
                let _ = file.close(f);
                res.status(200)
            },
            Result.Err(code) => res.status(500 + code),
        }
    } else if req.path_is(&Bytes.from("/fds")) {
        // How many descriptors the process has open.
        match fs.list(&Bytes.from("/proc/self/fd"), Bytes.with_capacity(65536)) {
            Result.Ok(names) => {
                let mut count = 0;
                let mut i = 0;
                while i < Bytes.len(&names) {
                    if Bytes.get(&names, i) == 10 { count = count + 1; }
                    i = i + 1;
                }
                res.status(200 + count)
            },
            Result.Err(code) => res.status(500 + code),
        }
    } else if req.path_is(&Bytes.from("/late")) {
        // Panics after starting the answer: the connection is closed.
        let mut s = res.stream(200, &Bytes.from("text/plain"));
        s = s.send(&Bytes.from("ab"));
        panic()
    } else if req.path_is(&Bytes.from("/stream")) {
        let mut s = res.stream(200, &Bytes.from("text/plain"));
        s = s.send(&Bytes.from("ab"));
        s = s.send(&Bytes.from("cd"));
        s.finish()
    } else {
        res.status(404)
    }
}

fn weigh(owned: Bytes, extra: i64, list: &Vec<i64>) -> i64 ! {panic} {
    Bytes.len(&owned) + extra + Vec.len(list)
}

fn show(exit: TaskExit<i64>) -> Unit ! {io, panic} {
    match exit {
        TaskExit.Completed(value) => print_i64(value),
        TaskExit.Cancelled => print_i64(-1),
    }
}

fn out(bytes: &Bytes) -> Unit ! {io, alloc, panic} {
    let _ = io.write(io.stdout(), bytes);
    let _ = io.write(io.stdout(), &Bytes.from("|\n"));
}

/// Read until the server closes the connection.
fn read_all(conn: &net.Conn) -> Bytes ! {io, alloc, panic, suspend} {
    let mut buffer = Bytes.with_capacity(4096);
    loop {
        let before = Bytes.len(&buffer);
        buffer = match net.read(conn, buffer, 5000) {
            Result.Ok(next) => next,
            Result.Err(code) => { print_i64(-code); return Bytes.with_capacity(0); },
        };
        if Bytes.len(&buffer) == before { return buffer; }
    }
}

/// Read until at least `count` bytes came.
fn read_some(conn: &net.Conn, count: i64) -> Bytes ! {io, alloc, panic, suspend} {
    let mut buffer = Bytes.with_capacity(4096);
    while Bytes.len(&buffer) < count {
        let before = Bytes.len(&buffer);
        buffer = match net.read(conn, buffer, 5000) {
            Result.Ok(next) => next,
            Result.Err(code) => { print_i64(-code); return Bytes.with_capacity(0); },
        };
        if Bytes.len(&buffer) == before { return buffer; }
    }
    buffer
}

fn open(port: i64) -> net.Conn ! {io, alloc, panic, suspend} {
    match net.connect(&Bytes.from("127.0.0.1"), port, 5000) {
        Result.Ok(conn) => conn,
        Result.Err(code) => { print_i64(-code); panic() },
    }
}

/// Send `request`, close the sending side, print everything that comes back.
fn exchange(port: i64, request: &Bytes) -> Unit ! {io, alloc, panic, suspend} {
    let conn = open(port);
    let _ = net.write(&conn, request, 5000);
    let _ = net.shutdown(&conn, 1);
    let reply = read_all(&conn);
    out(&reply);
    let _ = net.close(conn);
}

fn listener() -> net.Listener ! {io, alloc, panic} {
    match net.listen(&Bytes.from("127.0.0.1"), 0, 64, false) {
        Result.Ok(listener) => listener,
        Result.Err(code) => { print_i64(-code); panic() },
    }
}

fn port_of(listener: &net.Listener) -> i64 ! {io} {
    match net.local_port(listener) { Result.Ok(port) => port, Result.Err(_) => 0 }
}
"#;

const REQUESTS: &str = r#"
fn clients(port: i64) -> i64 ! {io, alloc, panic, suspend} {
    exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\n\r\n"));
    // Pipelined: both answers on one connection, in order.
    exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\n\r\nPOST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello"));
    // Keep-alive: the second request is sent after the first answer.
    let conn = open(port);
    let _ = net.write(&conn, &Bytes.from("HEAD /hello HTTP/1.1\r\nHost: x\r\n\r\n"), 5000);
    let first = read_some(&conn, 79);
    out(&first);
    let _ = net.write(&conn, &Bytes.from("GET /nope HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"), 5000);
    let second = read_all(&conn);
    out(&second);
    let _ = net.close(conn);
    exchange(port, &Bytes.from("POST /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2\r\nde\r\n0\r\n\r\n"));
    exchange(port, &Bytes.from("GET /stream HTTP/1.0\r\n\r\n"));
    // The server answers malformed requests itself and closes.
    exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\n\r\n"));
    exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\nA: 1\r\nB: 2\r\nC: 3\r\n\r\n"));
    exchange(port, &Bytes.from("POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 100\r\n\r\n"));
    // A head that never ends: 408 after the request deadline.
    let slow = open(port);
    let _ = net.write(&slow, &Bytes.from("GET /hello HT"), 5000);
    let late = read_all(&slow);
    out(&late);
    let _ = net.close(slow);
    // An idle connection is closed after the idle deadline, unanswered.
    let idle = open(port);
    let nothing = read_all(&idle);
    print_i64(Bytes.len(&nothing));
    let _ = net.close(idle);
    0
}

fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    let port = port_of(&server_socket);
    let mut config = web.config();
    config.limits.fields = 3;
    config.limits.body = 50;
    config.idle_ms = 50;
    config.request_ms = 100;
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            match web.serve(server_socket, app, config) { Result.Ok(_) => 0, Result.Err(code) => code }
        });
        let client = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { clients(port) });
        show(Task.join(client));
        Task.cancel(&server);
        show(Task.join(server));
    });
    0
}
"#;

#[test]
fn the_server_answers_keeps_alive_and_refuses() {
    let hi = "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 2\r\n\r\nhi";
    let expected = format!(
        "{hi}|\n\
{hi}HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 5\r\n\r\nhello|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 2\r\n\r\n|\n\
HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 5\r\n\r\nabcde|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nConnection: close\r\n\r\nabcd|\n\
HTTP/1.1 400 Bad Request\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
HTTP/1.1 431 Request Header Fields Too Large\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
HTTP/1.1 413 Content Too Large\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
HTTP/1.1 408 Request Timeout\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
0\n0\n-1\n"
    );
    both(&format!("{APP}{REQUESTS}"), &expected);
}

const GRACEFUL: &str = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    let port = port_of(&server_socket);
    let start = time.monotonic_ns();
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            match web.serve(server_socket, app, web.config()) { Result.Ok(_) => 0, Result.Err(code) => code }
        });
        // One request in flight, one idle kept-alive connection.
        let busy = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            let conn = open(port);
            let _ = net.write(&conn, &Bytes.from("GET /slow HTTP/1.1\r\nHost: x\r\n\r\n"), 5000);
            let reply = read_all(&conn);
            let _ = net.close(conn);
            // The whole answer, "slow" included.
            if Bytes.len(&reply) > 0 && Bytes.get(&reply, Bytes.len(&reply) - 1) == 119 { Bytes.len(&reply) } else { -Bytes.len(&reply) }
        });
        let idle = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            let conn = open(port);
            let _ = net.write(&conn, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\n\r\n"), 5000);
            let reply = read_all(&conn);
            let _ = net.close(conn);
            Bytes.len(&reply)
        });
        let _ = time.wait_ms(50);
        Task.cancel(&server);
        show(Task.join(server));
        show(Task.join(busy));
        show(Task.join(idle));
    });
    // The idle connection was closed at once, not after the 5 s idle time.
    let elapsed = match time.monotonic_ns() { Result.Ok(now) => match start { Result.Ok(s) => now - s, Result.Err(_) => 0 }, Result.Err(_) => 0 };
    print_i64(if elapsed < 3000000000 { 1 } else { 0 });
    // The listener is closed.
    match net.connect(&Bytes.from("127.0.0.1"), port, 1000) {
        Result.Ok(conn) => { print_i64(-1); let _ = net.close(conn); },
        Result.Err(code) => print_i64(code),
    }
    0
}
"#;

#[test]
fn cancelling_the_server_finishes_responses_and_closes_idle_connections() {
    both(
        &format!("{APP}{GRACEFUL}"),
        "-1\n83\n81\n1\n111\n",
    );
}

/// A native server under real clients: concurrent keep-alive connections
/// from Rust threads.
#[test]
fn a_native_server_serves_concurrent_rust_clients() {
    let main = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    print_i64(port_of(&server_socket));
    match web.serve(server_socket, app, web.config()) { Result.Ok(_) => 0, Result.Err(code) => code }
}
"#;
    let (_scratch, binary) = build(&format!("{APP}{main}"));
    let mut child = Command::new(&binary).stdout(Stdio::piped()).spawn().unwrap();
    let mut lines = BufReader::new(child.stdout.take().unwrap());
    let mut line = String::new();
    lines.read_line(&mut line).unwrap();
    let port: u16 = line.trim().parse().unwrap();
    let workers: Vec<_> = (0..16)
        .map(|worker| {
            std::thread::spawn(move || {
                let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
                stream.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
                // Five requests on one kept-alive connection, the last
                // closing it.
                let mut request = Vec::new();
                for i in 0..5 {
                    let body = format!("w{worker}r{i}");
                    let close = if i == 4 { "Connection: close\r\n" } else { "" };
                    request.extend_from_slice(
                        format!(
                            "POST /echo HTTP/1.1\r\nHost: x\r\n{close}Content-Length: {}\r\n\r\n{body}",
                            body.len()
                        )
                        .as_bytes(),
                    );
                }
                stream.write_all(&request).unwrap();
                let mut reply = String::new();
                stream.read_to_string(&mut reply).unwrap();
                for i in 0..5 {
                    assert!(reply.contains(&format!("\r\n\r\nw{worker}r{i}")), "{reply}");
                }
                reply.matches("HTTP/1.1 200 OK").count()
            })
        })
        .collect();
    let answered: usize = workers.into_iter().map(|worker| worker.join().unwrap()).sum();
    let _ = child.kill();
    let _ = child.wait();
    assert_eq!(answered, 80);
}

const PANICS: &str = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    let port = port_of(&server_socket);
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            match web.serve(server_socket, app, web.config()) { Result.Ok(_) => 0, Result.Err(code) => code }
        });
        let client = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            // The pipelined /hello is not answered: the connection closes.
            exchange(port, &Bytes.from("GET /boom HTTP/1.1\r\nHost: x\r\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\n\r\n"));
            exchange(port, &Bytes.from("GET /late HTTP/1.1\r\nHost: x\r\n\r\n"));
            exchange(port, &Bytes.from("GET /owned HTTP/1.1\r\nHost: x\r\n\r\n"));
            SCOPED
            // The server still serves.
            exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\n\r\n"));
            0
        });
        show(Task.join(client));
        Task.cancel(&server);
        show(Task.join(server));
    });
    0
}
"#;

/// A panicking handler ends only its own task (WEB-PANIC-500).
#[test]
fn a_handler_panic_is_answered_with_500() {
    let source = format!("{APP}{PANICS}");
    let expected = "HTTP/1.1 500 Internal Server Error\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n|\n\
HTTP/1.1 500 Internal Server Error\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n\
SCOPED\
HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 2\r\n\r\nhi|\n\
0\n-1\n";
    // Both backends unwind the panicking handlers (PANIC-UNWIND-EVAL and
    // -NATIVE): every allocation is freed (the reference run and the native
    // exit check both require it), and a child task of the handler is
    // cancelled and joined.
    let scoped = r#"exchange(port, &Bytes.from("GET /scoped HTTP/1.1\r\nHost: x\r\n\r\n"));"#;
    let five_hundred = "HTTP/1.1 500 Internal Server Error\r\nContent-Length: 0\r\nConnection: close\r\n\r\n|\n";
    let source = source.replace("SCOPED", scoped);
    let expected = expected.replace("SCOPED", five_hundred);
    assert_eq!(reference(&source), expected, "reference");
    let (_scratch, binary) = build(&source);
    let run = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(run.status.code(), Some(0));
    assert_eq!(String::from_utf8(run.stdout).unwrap(), expected, "native");
    let stderr = String::from_utf8(run.stderr).unwrap();
    // Four panics, each reported once; none needed the leaking fallback.
    assert_eq!(stderr.matches("panic: checked arithmetic").count(), 4, "{stderr}");
    assert!(!stderr.contains("recovered in an isolated task"), "{stderr}");
}

/// A panic unwinding past an open file closes it (PANIC-LINEAR-CLEANUP):
/// the process's descriptor count is the same before and after.
#[test]
fn unwinding_closes_linear_resources() {
    let main = r#"
fn status_of(port: i64, request: &Bytes) -> i64 ! {io, alloc, panic, suspend} {
    let conn = open(port);
    let _ = net.write(&conn, request, 5000);
    let _ = net.shutdown(&conn, 1);
    let reply = read_all(&conn);
    let _ = net.close(conn);
    // "HTTP/1.1 NNN": the status digits.
    if Bytes.len(&reply) < 12 { return -1; }
    (Bytes.get(&reply, 9) - 48) * 100 + (Bytes.get(&reply, 10) - 48) * 10 + Bytes.get(&reply, 11) - 48
}

fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    let port = port_of(&server_socket);
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            match web.serve(server_socket, app, web.config()) { Result.Ok(_) => 0, Result.Err(code) => code }
        });
        let client = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            let fds = Bytes.from("GET /fds HTTP/1.1\r\nHost: x\r\n\r\n");
            let before = status_of(port, &fds);
            let mut i = 0;
            while i < 5 {
                print_i64(status_of(port, &Bytes.from("GET /file HTTP/1.1\r\nHost: x\r\n\r\n")));
                i = i + 1;
            }
            let after = status_of(port, &fds);
            if before == after { 1 } else { after - before }
        });
        show(Task.join(client));
        Task.cancel(&server);
        show(Task.join(server));
    });
    0
}
"#;
    let source = format!("{APP}{main}");
    let expected = "500\n500\n500\n500\n500\n1\n-1\n";
    let (scratch, binary) = build(&source);
    let run = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(run.status.code(), Some(0), "{}", String::from_utf8_lossy(&run.stderr));
    assert_eq!(String::from_utf8(run.stdout).unwrap(), expected, "native");
    // The reference evaluator in a process of its own, so the descriptor
    // count is only this program's (the File sits inside a Result there).
    let file = scratch.path().join("fds.kush");
    std::fs::write(&file, &source).unwrap();
    let run = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("eval")
        .arg(&file)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert_eq!(run.status.code(), Some(0), "{}", String::from_utf8_lossy(&run.stderr));
    assert_eq!(String::from_utf8(run.stdout).unwrap(), expected, "reference");
}

#[test]
fn unwind_cleanups_are_checked() {
    for (source, message) in [
        ("#[linear(unwind = missing)] struct R { x: i64 }\nfn main() -> i64 ! {} { 0 }", "names no function"),
        (
            "#[linear(unwind = wrong)] struct R { x: i64 }\nfn wrong(r: &R) -> Unit ! {} { }\nfn main() -> i64 ! {} { 0 }",
            "must take the R by value",
        ),
        (
            "#[linear(unwind = wrong)] struct R { x: i64 }\nfn wrong(r: R) -> i64 ! {} { match r { R { x } => x } }\nfn main() -> i64 ! {} { 0 }",
            "return Unit",
        ),
        ("#[linear(close = f)] struct R { x: i64 }\nfn main() -> i64 ! {} { 0 }", "#[linear(unwind = cleanup)]"),
    ] {
        let program = kush::program::load_source("<unwind-test>", source).unwrap();
        let error = executable::check_program(&program).err().unwrap_or_else(|| panic!("accepted: {source}"));
        assert!(error.message.contains(message), "{source}: {}", error.message);
    }
}

/// Standard input that must never be read.
struct Untouched;
impl Read for Untouched {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        panic!("the program never reads standard input")
    }
}

/// EVAL-SERVE-HANG: a task program buffers standard input up front only when
/// a function reachable from main reads it. This server imports std.io
/// (whose `stdin()` it never calls), so the evaluator must not wait for the
/// end of an input that, run from a terminal, never comes.
#[test]
fn the_evaluator_does_not_wait_for_unread_standard_input() {
    let main = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let server_socket = listener();
    let port = port_of(&server_socket);
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            match web.serve(server_socket, app, web.config()) { Result.Ok(_) => 0, Result.Err(code) => code }
        });
        let client = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            exchange(port, &Bytes.from("GET /hello HTTP/1.1\r\nHost: x\r\n\r\n"));
            0
        });
        show(Task.join(client));
        Task.cancel(&server);
        show(Task.join(server));
    });
    0
}
"#;
    let program = checked(&format!("{APP}{main}"));
    let mut output = Vec::new();
    let (status, _) = program
        .evaluate_with_host_and_stats(&mut Untouched, &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0);
    assert!(String::from_utf8(output).unwrap().ends_with("hi|\n0\n-1\n"));
}
