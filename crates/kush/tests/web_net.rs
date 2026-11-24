//! WEB-NET: server sockets in `std.net`, a linear `Listener` and `Conn`
//! over one-call `std.sys` stubs, in the reference evaluator and natively.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io::{self, Read, Write};
use std::net::TcpStream;
use std::process::{Command, Stdio};
use std::time::Duration;

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program =
        kush::program::load_source("<web-net-test>", source).map_err(|(_, error)| error.message)?;
    executable::check_program(&program).map_err(|error| program.sources.render(&error))
}

fn reference(source: &str) -> String {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(
        stats.allocations, stats.deallocations,
        "reference cleanup must be balanced"
    );
    String::from_utf8(output).unwrap()
}

fn build(source: &str, name: &str) -> (kush::native::Scratch, std::path::PathBuf) {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join(name);
    kush::native::build(&program, &binary).unwrap();
    (scratch, binary)
}

fn native(source: &str) -> String {
    let (_scratch, binary) = build(source, "web-net");
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stdout).unwrap()
}

const PRELUDE: &str = r#"
use std.net;
use std.net.Conn;
use std.net.Listener;
use std.result.Result;

fn listener(host: &Bytes, port: i64, reuse: Bool) -> Listener ! {io} {
    match net.listen(host, port, 16, reuse) {
        Result.Ok(listener) => listener,
        Result.Err(code) => { print_i64(-code); panic() },
    }
}

fn conn(result: Result<Conn, i64>) -> Conn ! {io} {
    match result {
        Result.Ok(conn) => conn,
        Result.Err(code) => { print_i64(-code); panic() },
    }
}

fn code(result: Result<Unit, i64>) -> i64 ! {} {
    match result {
        Result.Ok(_) => 0,
        Result.Err(code) => code,
    }
}

/// Read until the peer closes; the length, or minus the errno.
fn read_all(conn: &Conn, capacity: i64) -> i64 ! {io, alloc, suspend} {
    let mut buffer = Bytes.with_capacity(capacity);
    loop {
        let before = Bytes.len(&buffer);
        match net.read(conn, buffer, 1000) {
            Result.Ok(next) => {
                buffer = next;
                if Bytes.len(&buffer) == before { return before; }
            },
            Result.Err(code) => { return -code; },
        }
    }
}
"#;

const ROUND_TRIP: &str = r#"
fn main() -> i64 ! {io, alloc, suspend} {
    let host = Bytes.from("127.0.0.1");
    let server = listener(&host, 0, false);
    let port = match net.local_port(&server) { Result.Ok(port) => port, Result.Err(code) => -code };
    print_i64(if port > 0 { 1 } else { 0 });
    // Nobody connected yet: ETIMEDOUT.
    match net.accept(&server, 30) {
        Result.Ok(stray) => { print_i64(-1); let _ = net.close(stray); },
        Result.Err(code) => print_i64(code),
    }
    // A client in the same thread: the kernel completes the connection
    // before it is accepted.
    let client = conn(net.connect(&host, port, 1000));
    print_i64(code(net.set_nodelay(&client, true)));
    let ping = Bytes.from("ping");
    print_i64(code(net.write(&client, &ping, 1000)));
    print_i64(code(net.shutdown(&client, 1)));
    let accepted = conn(net.accept(&server, 1000));
    print_i64(read_all(&accepted, 64));
    // The client has not closed its reading side: nothing to read yet.
    let pong = Bytes.from("pong!");
    print_i64(code(net.write(&accepted, &pong, 1000)));
    print_i64(code(net.close(accepted)));
    print_i64(read_all(&client, 64));
    print_i64(code(net.close(client)));
    // A silent peer: the read times out, and a full buffer is EFBIG.
    let quiet = conn(net.connect(&host, port, 1000));
    let held = conn(net.accept(&server, 1000));
    match net.read(&quiet, Bytes.with_capacity(8), 40) {
        Result.Ok(buffer) => print_i64(-Bytes.len(&buffer)),
        Result.Err(code) => print_i64(code),
    }
    match net.read(&quiet, Bytes.with_capacity(0), 40) {
        Result.Ok(buffer) => print_i64(-Bytes.len(&buffer)),
        Result.Err(code) => print_i64(code),
    }
    print_i64(code(net.close(held)));
    print_i64(code(net.close(quiet)));
    // The port is taken without SO_REUSEPORT.
    match net.listen(&host, port, 16, false) {
        Result.Ok(second) => { print_i64(-1); let _ = net.close_listener(second); },
        Result.Err(code) => print_i64(code),
    }
    print_i64(code(net.close_listener(server)));
    // Nothing listens there any more.
    match net.connect(&host, port, 1000) {
        Result.Ok(stray) => { print_i64(-1); let _ = net.close(stray); },
        Result.Err(code) => print_i64(code),
    }
    // Bad arguments.
    match net.listen(&host, 65536, 16, false) {
        Result.Ok(bad) => { print_i64(-1); let _ = net.close_listener(bad); },
        Result.Err(code) => print_i64(code),
    }
    0
}
"#;

#[test]
fn a_server_and_client_round_trip_in_both_backends() {
    let source = format!("{PRELUDE}{ROUND_TRIP}");
    let reference = reference(&source);
    assert_eq!(
        reference,
        "1\n110\n0\n0\n0\n4\n0\n0\n5\n0\n110\n27\n0\n0\n98\n0\n111\n22\n"
    );
    assert_eq!(native(&source), reference);
}

/// A native server answering a real client: it prints its port, then
/// serves one connection.
const ECHO: &str = r#"
fn main() -> i64 ! {io, alloc, suspend} {
    let host = Bytes.from("127.0.0.1");
    let server = listener(&host, 0, false);
    match net.local_port(&server) { Result.Ok(port) => print_i64(port), Result.Err(code) => print_i64(-code) }
    let client = conn(net.accept(&server, 10000));
    let mut request = Bytes.with_capacity(64);
    loop {
        let before = Bytes.len(&request);
        request = match net.read(&client, request, 10000) {
            Result.Ok(next) => next,
            Result.Err(code) => { print_i64(-code); panic() },
        };
        if Bytes.len(&request) == before { break; }
    }
    let _ = net.write(&client, &request, 10000);
    let _ = net.close(client);
    let _ = net.close_listener(server);
    0
}
"#;

#[test]
fn a_native_server_echoes_a_rust_client() {
    let (_scratch, binary) = build(&format!("{PRELUDE}{ECHO}"), "echo");
    let mut child = Command::new(&binary)
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    // The first line is the port (print_i64 writes it at once).
    let mut line = Vec::new();
    let mut byte = [0u8; 1];
    while stdout.read(&mut byte).unwrap() == 1 && byte[0] != b'\n' {
        line.push(byte[0]);
    }
    let port: u16 = String::from_utf8(line).unwrap().parse().unwrap();
    let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    stream.write_all(b"hello kush").unwrap();
    stream.shutdown(std::net::Shutdown::Write).unwrap();
    let mut reply = Vec::new();
    stream.read_to_end(&mut reply).unwrap();
    assert_eq!(reply, b"hello kush");
    assert!(child.wait().unwrap().success());
}

/// With SO_REUSEPORT two listeners share a port (natively; the evaluator
/// cannot set the option).
#[test]
fn reuse_port_lets_two_listeners_share_a_port() {
    let source = format!(
        "{PRELUDE}
        fn main() -> i64 ! {{io, alloc, suspend}} {{
            let host = Bytes.from(\"127.0.0.1\");
            let first = listener(&host, 0, true);
            let port = match net.local_port(&first) {{ Result.Ok(port) => port, Result.Err(code) => -code }};
            let second = listener(&host, port, true);
            print_i64(code(net.close_listener(second)));
            print_i64(code(net.close_listener(first)));
            0
        }}"
    );
    assert_eq!(native(&source), "0\n0\n");
}

#[test]
fn sockets_are_linear_and_cannot_be_forged() {
    for (body, message) in [
        (
            "let s = listener(&Bytes.from(\"127.0.0.1\"), 0, false); 0",
            "linear value is not consumed",
        ),
        (
            "let c = conn(net.connect(&Bytes.from(\"127.0.0.1\"), 80, 10)); let a = net.close(c); let b = net.close(c); 0",
            "moved",
        ),
        ("let c = net.Conn { fd: 1 }; code(net.close(c))", "private"),
        (
            "let l = net.Listener { fd: 3 }; code(net.close_listener(l))",
            "private",
        ),
    ] {
        let source = format!("{PRELUDE}\nfn main() -> i64 ! {{io, alloc, suspend}} {{ {body} }}");
        match checked(&source) {
            Ok(_) => panic!("accepted: {body}"),
            Err(error) => assert!(error.contains(message), "{body}: {error}"),
        }
    }
}
