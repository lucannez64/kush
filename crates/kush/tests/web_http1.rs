//! WEB-HTTP-PARSE: the HTTP/1.1 request parser, chunked body reader and
//! response writer in `std.http1`. Every program runs in the reference
//! evaluator and natively with the same output.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::process::{Command, Stdio};

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program = kush::program::load_source("<web-http1-test>", source)
        .map_err(|(_, error)| error.message)?;
    executable::check_program(&program).map_err(|error| program.sources.render(&error))
}

fn reference(source: &str) -> String {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(stats.allocations, stats.deallocations, "reference cleanup must be balanced");
    String::from_utf8(output).unwrap()
}

fn native(source: &str) -> String {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("web-http1");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stdout));
    String::from_utf8(output.stdout).unwrap()
}

fn both(source: &str) -> String {
    let reference = reference(source);
    assert_eq!(native(source), reference, "native and reference differ");
    reference
}

const PARSER: &str = r#"
use std.http1;
use std.http1.Framing;
use std.http1.Limits;
use std.http1.Method;
use std.http1.Parse;
use std.http1.Body;

fn method(m: Method) -> i64 ! {} {
    match m {
        Method.Get => 0, Method.Head => 1, Method.Post => 2, Method.Put => 3,
        Method.Delete => 4, Method.Patch => 5, Method.Options => 6,
        Method.Connect => 7, Method.Trace => 8, Method.Other => 9,
    }
}

/// -1 incomplete, the status of a rejection, or a summary line of numbers.
fn show(request: &Bytes, limits: &Limits) -> Unit ! {io, alloc, panic} {
    match http1.parse_head(request, limits) {
        Parse.Incomplete => print_i64(-1),
        Parse.Reject(status) => print_i64(status),
        Parse.Complete(head) => {
            let framing = match head.framing {
                Framing.Empty => 0,
                Framing.Length(n) => 1000 + n,
                Framing.Chunked => 2,
            };
            let summary = method(head.method) * 1000000000000
                + (head.target_end - head.target) * 10000000000
                + head.minor * 1000000000
                + Vec.len(&head.fields) * 10000000
                + framing * 1000
                + (if head.keep_alive { 100 } else { 0 })
                + head.size;
            print_i64(summary);
        },
    }
}

fn chunked(text: &Bytes, limits: &Limits) -> i64 ! {} {
    match http1.chunked_size(text, 0, limits) {
        Body.Complete(length, _) => length,
        Body.Incomplete => -1,
        Body.Reject(status) => status,
    }
}

fn main() -> i64 ! {io, alloc, panic} {
    let l = http1.limits();
    let small = Limits { line: 16, fields: 2, head: 200, body: 10 };
    let small_body = Limits { line: 8192, fields: 100, head: 65536, body: 10 };
    // 0: GET, target 2, 1.1, 1 field, no body, keep-alive, 27 bytes
    show(&Bytes.from("GET /a HTTP/1.1\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET /a HTTP/1.1\r\nHost: x\r\n"), &l);
    show(&Bytes.from("GET /a HTT"), &l);
    show(&Bytes.from("GET / HTTP/1.1\nHost: x\n\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.0\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.0\r\nConnection: Keep-Alive\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\r\nConnection: foo, close\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: gzip\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\ncontent-length: 5\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5, 5\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 11\r\n\r\n"), &small_body);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\r\n y\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost : x\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/2.0\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.x\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET /aaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\n"), &small);
    show(&Bytes.from("GET /aaaaaaaaaaaaaaaaaaaa"), &small);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\r\nA: 1\r\nB: 2\r\n\r\n"), &small);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\r\nExpect: 100-continue\r\n\r\n"), &l);
    show(&Bytes.from("POST /up HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: Chunked\r\n\r\n"), &l);
    show(&Bytes.from("\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\0y\r\n\r\n"), &l);
    show(&Bytes.from("BREW /pot HTTP/1.1\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET  / HTTP/1.1\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("G(T / HTTP/1.1\r\nHost: x\r\n\r\n"), &l);
    show(&Bytes.from("GET / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n"), &l);
    show(&Bytes.from("POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n"), &l);
    show(&Bytes.from("DELETE /x HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\n\r\n"), &l);
    // Chunked bodies.
    let body = Bytes.from("4\r\nWiki\r\n5;name=v\r\npedia\r\n0\r\nTrailer: t\r\n\r\nNEXT");
    match http1.chunked_size(&body, 0, &l) {
        Body.Complete(length, next) => {
            print_i64(length);
            print_i64(next);
            let decoded = http1.chunked_copy(&body, 0, Bytes.with_capacity(16));
            print_i64(Bytes.len(&decoded));
            print_i64(Bytes.get(&decoded, 0));
            print_i64(Bytes.get(&decoded, 8));
        },
        Body.Incomplete => print_i64(-1),
        Body.Reject(status) => print_i64(status),
    }
    print_i64(chunked(&Bytes.from("4\r\nWi"), &l));
    print_i64(chunked(&Bytes.from("4\r\nWikiX\r\n"), &l));
    print_i64(chunked(&Bytes.from("x\r\n"), &l));
    print_i64(chunked(&Bytes.from("b\r\nhello world\r\n0\r\n\r\n"), &small));
    print_i64(chunked(&Bytes.from("1111111111111111\r\n"), &l));
    print_i64(chunked(&Bytes.from("0\r\n\r\n"), &l));
    print_i64(chunked(&Bytes.from("3\r\nabc\r\n0\r\n"), &l));
    0
}
"#;

#[test]
fn the_parser_accepts_valid_heads_and_rejects_smuggling() {
    let output = both(PARSER);
    let lines: Vec<&str> = output.lines().collect();
    let expected = [
        "21010000128",    // GET, target 2, 1.1, 1 field, no body, keep-alive, 28 bytes
        "-1",             // incomplete head
        "-1",             // incomplete request line
        "400",            // bare LF
        "400",            // HTTP/1.1 without Host
        "400",            // two Host fields
        "10000000018",    // HTTP/1.0 without Host: no keep-alive
        "10010000142",    // HTTP/1.0 keep-alive
        "11020000051",    // Connection: close in a list
        "400",            // Content-Length with Transfer-Encoding
        "501",            // an unsupported transfer coding
        "400",            // two different Content-Lengths
        "2011031005166",  // the same Content-Length twice: Length(5)
        "400",            // a list as Content-Length
        "413",            // over the body limit
        "400",            // obsolete line folding
        "400",            // space before the colon
        "505",            // HTTP/2.0
        "400",            // malformed version
        "414",            // request line over the limit
        "414",            // request line over the limit, unfinished
        "431",            // too many fields
        "417",            // Expect: 100-continue
        "2031020002158",  // chunked (case-insensitive)
        "11010000131",    // leading empty lines skipped (size includes them)
        "400",            // NUL in a value
        "9041010000131",  // unknown method
        "400",            // two spaces
        "400",            // non-token method
        "400",            // two Transfer-Encoding fields
        "400",            // chunked in HTTP/1.0
        "4021020000150",  // Content-Length: 0 is no body
        "9", "43", "9", "87", "97", // Wiki + pedia, ends before NEXT
        "-1", "400", "400", "413", "413", "0", "-1",
    ];
    assert_eq!(lines, expected, "\n{output}");
}

const WRITER: &str = r#"
use std.http1;
use std.io;
use std.result.Result;

fn main() -> i64 ! {io, alloc, panic} {
    let mut out = http1.status_line(Bytes.with_capacity(64), 404);
    out = match http1.field(out, &Bytes.from("X-Id"), &Bytes.from("7\tok")) {
        Result.Ok(next) => next,
        Result.Err(code) => { print_i64(code); return 1; },
    };
    out = http1.content_length(out, 12);
    out = http1.end_head(out);
    out = http1.status_line(out, 299);
    out = http1.status_line(out, 42);
    out = http1.chunk(out, &Bytes.from("0123456789abcdefg"));
    out = http1.chunk(out, &Bytes.from(""));
    out = http1.last_chunk(out);
    let _ = io.write(io.stdout(), &out);
    // A value with CR LF is refused, so it cannot add a header.
    match http1.field(Bytes.with_capacity(8), &Bytes.from("X"), &Bytes.from("a\r\nSet-Cookie: x")) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    match http1.field(Bytes.with_capacity(8), &Bytes.from("Bad Name"), &Bytes.from("v")) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    0
}
"#;

#[test]
fn the_writer_emits_heads_and_chunks() {
    assert_eq!(
        both(WRITER),
        "HTTP/1.1 404 Not Found\r\nX-Id: 7\tok\r\nContent-Length: 12\r\n\r\n\
         HTTP/1.1 299 \r\nHTTP/1.1 500 Internal Server Error\r\n\
         11\r\n0123456789abcdefg\r\n0\r\n\r\n22\n22\n"
    );
}
