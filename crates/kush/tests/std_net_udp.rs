//! `std.net.udp_send`: one UDP datagram through the `resolve_udp`, `socket`
//! and `sendto` stubs, in the reference evaluator and natively.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::net::UdpSocket;
use std::process::{Command, Stdio};
use std::time::Duration;

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<std-net-udp-test>", source)
        .unwrap_or_else(|(_, error)| panic!("{}", error.message));
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str) -> String {
    let mut output = Vec::new();
    let (status, stats) = checked(source)
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(
        stats.allocations, stats.deallocations,
        "reference cleanup must be balanced"
    );
    String::from_utf8(output).unwrap()
}

fn native(source: &str) -> String {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("std-net-udp");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// A program that sends a Wake-on-LAN style packet (6 x 0xFF, then a MAC 16
/// times) to `host`:`port` with `net.<function>` and prints the count or
/// minus the errno.
fn sender(function: &str, host: &str, port: u16) -> String {
    format!(
        r#"
use std.net;
use std.result.Result;

fn main() -> i64 ! {{io, alloc, panic}} {{
    let mut packet = Bytes.with_capacity(102);
    let mut i = 0;
    while i < 6 {{ packet = Bytes.push(packet, 255); i = i + 1; }}
    let mut n = 0;
    while n < 16 {{
        packet = Bytes.push(packet, 112);
        packet = Bytes.push(packet, 113);
        packet = Bytes.push(packet, 1);
        packet = Bytes.push(packet, 2);
        packet = Bytes.push(packet, 3);
        packet = Bytes.push(packet, 4);
        n = n + 1;
    }}
    match net.{function}(&Bytes.from("{host}"), {port}, &packet) {{
        Result.Ok(count) => print_i64(count),
        Result.Err(code) => print_i64(-code),
    }}
    0
}}
"#
    )
}

fn expected_packet() -> Vec<u8> {
    let mut packet = vec![0xff; 6];
    for _ in 0..16 {
        packet.extend_from_slice(b"pq\x01\x02\x03\x04");
    }
    packet
}

fn receive(socket: &UdpSocket) -> Vec<u8> {
    let mut buffer = [0u8; 512];
    let (count, _) = socket.recv_from(&mut buffer).expect("no datagram arrived");
    buffer[..count].to_vec()
}

#[test]
fn udp_send_delivers_one_datagram_on_both_backends() {
    for host in ["127.0.0.1", "::1"] {
        let receiver = match UdpSocket::bind((host, 0)) {
            Ok(socket) => socket,
            // A host without IPv6 loopback.
            Err(_) if host == "::1" => continue,
            Err(error) => panic!("{error}"),
        };
        receiver
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        let source = sender("udp_send", host, receiver.local_addr().unwrap().port());
        assert_eq!(reference(&source).trim(), "102", "{host} reference");
        assert_eq!(receive(&receiver), expected_packet(), "{host} reference");
        assert_eq!(native(&source).trim(), "102", "{host} native");
        assert_eq!(receive(&receiver), expected_packet(), "{host} native");
    }
}

#[test]
fn udp_broadcast_sets_so_broadcast_and_sends_on_both_backends() {
    // A real broadcast would leave this host, so the test sends to loopback:
    // what it checks is that setting SO_BROADCAST succeeds on both backends
    // and the datagram still arrives intact.
    let receiver = UdpSocket::bind("127.0.0.1:0").unwrap();
    receiver
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    let source = sender(
        "udp_broadcast",
        "127.0.0.1",
        receiver.local_addr().unwrap().port(),
    );
    assert_eq!(reference(&source).trim(), "102", "reference");
    assert_eq!(receive(&receiver), expected_packet(), "reference");
    assert_eq!(native(&source).trim(), "102", "native");
    assert_eq!(receive(&receiver), expected_packet(), "native");
}

#[test]
fn udp_send_reports_errors_on_both_backends() {
    // Port 0 is EINVAL before resolving; a datagram over 65507 bytes is
    // EMSGSIZE (90) from sendto.
    let source = r#"
use std.net;
use std.result.Result;

fn show(result: Result<i64, i64>) -> Unit ! {io, panic} {
    match result {
        Result.Ok(count) => print_i64(count),
        Result.Err(code) => print_i64(-code),
    }
}

fn main() -> i64 ! {io, alloc, panic} {
    show(net.udp_send(&Bytes.from("127.0.0.1"), 0, &Bytes.from("x")));
    let mut big = Bytes.with_capacity(70000);
    let mut i = 0;
    while i < 70000 { big = Bytes.push(big, 0); i = i + 1; }
    show(net.udp_send(&Bytes.from("127.0.0.1"), 9, &big));
    0
}
"#;
    let expected = "-22\n-90\n";
    assert_eq!(reference(source), expected);
    assert_eq!(native(source), expected);
}

/// A program that sends `xyz` with `net.udp_send6` to each `(host, port)`
/// and prints the address used, or minus the errno.
fn sender6(targets: &[(&str, u16)]) -> String {
    let calls: String = targets
        .iter()
        .map(|(host, port)| format!("    send6(&Bytes.from(\"{host}\"), {port});\n"))
        .collect();
    format!(
        r#"
use std.io;
use std.net;
use std.result.Result;

fn send6(host: &Bytes, port: i64) -> Unit ! {{io, alloc, panic}} {{
    match net.udp_send6(host, port, &Bytes.from("xyz"), Bytes.with_capacity(64)) {{
        Result.Ok(address) => {{
            let line = Bytes.push(address, 10);
            let _ = io.write(io.stdout(), &line);
        }},
        Result.Err(code) => print_i64(-code),
    }}
}}

fn main() -> i64 ! {{io, alloc, panic}} {{
{calls}    0
}}
"#
    )
}

#[test]
fn udp_send6_reports_the_ipv6_address_it_used_on_both_backends() {
    let Ok(receiver) = UdpSocket::bind("[::1]:0") else {
        return; // A host without IPv6 loopback.
    };
    receiver
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    let port = receiver.local_addr().unwrap().port();
    // An IPv4 literal has no IPv6 address: EINVAL, nothing sent.
    let source = sender6(&[("::1", port), ("127.0.0.1", port)]);
    for (backend, output) in [
        ("reference", reference(&source)),
        ("native", native(&source)),
    ] {
        assert_eq!(output, "::1\n-22\n", "{backend}");
        assert_eq!(receive(&receiver), b"xyz", "{backend}");
    }
    receiver.set_nonblocking(true).unwrap();
    assert!(
        receiver.recv(&mut [0u8; 8]).is_err(),
        "the IPv4 literal must not be sent"
    );
}

#[test]
fn udp_route_source_names_the_local_address_without_sending_on_both_backends() {
    // A listener on the probed port: the probe must not send to it.
    let listener = UdpSocket::bind("0.0.0.0:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let ipv6 = UdpSocket::bind("[::1]:0").is_ok();
    let mut targets = vec!["127.0.0.1", "127.255.255.255"];
    if ipv6 {
        targets.push("::1");
    }
    let calls: String = targets
        .iter()
        .map(|host| format!("    route(&Bytes.from(\"{host}\"), {port});\n"))
        .collect();
    let source = format!(
        r#"
use std.io;
use std.net;
use std.result.Result;

fn route(host: &Bytes, port: i64) -> Unit ! {{io, alloc, panic}} {{
    match net.udp_route_source(host, port, Bytes.with_capacity(64)) {{
        Result.Ok(address) => {{
            let line = Bytes.push(address, 10);
            let _ = io.write(io.stdout(), &line);
        }},
        Result.Err(code) => print_i64(-code),
    }}
}}

fn main() -> i64 ! {{io, alloc, panic}} {{
{calls}    route(&Bytes.from("127.0.0.1"), 0);
    0
}}
"#
    );
    // 127.255.255.255 is loopback's broadcast address: connecting to it
    // needs SO_BROADCAST, and its route leaves from 127.0.0.1.
    let expected = if ipv6 {
        "127.0.0.1\n127.0.0.1\n::1\n-22\n"
    } else {
        "127.0.0.1\n127.0.0.1\n-22\n"
    };
    assert_eq!(reference(&source), expected, "reference");
    assert_eq!(native(&source), expected, "native");
    listener.set_nonblocking(true).unwrap();
    assert!(
        listener.recv(&mut [0u8; 8]).is_err(),
        "a route probe must not send"
    );
}
