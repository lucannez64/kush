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
    executable::check_program(&program).unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str) -> String {
    let mut output = Vec::new();
    let (status, stats) = checked(source)
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(stats.allocations, stats.deallocations, "reference cleanup must be balanced");
    String::from_utf8(output).unwrap()
}

fn native(source: &str) -> String {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("std-net-udp");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stdout));
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
        receiver.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
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
    receiver.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let source = sender("udp_broadcast", "127.0.0.1", receiver.local_addr().unwrap().port());
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
