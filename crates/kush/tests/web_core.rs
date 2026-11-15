//! WEB-CORE: `std.web`'s Request and linear Responder. Every program runs
//! in the reference evaluator and natively with the same output.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::process::{Command, Stdio};

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program = kush::program::load_source("<web-core-test>", source)
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
    let binary = scratch.path().join("web-core");
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

const RESPONDER: &str = r#"
use std.http1;
use std.http1.Method;
use std.http1.Parse;
use std.io;
use std.option.Option;
use std.result.Result;
use std.web;
use std.web.Request;
use std.web.Responder;
use std.web.Response;

fn hello(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    if req.path_is(&Bytes.from("/hello")) {
        res.text(200, &Bytes.from("hi"))
    } else {
        res.status(404)
    }
}

fn data(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    res.json(201, &Bytes.from("{\"ok\":true}"))
}

fn empty(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    res.status(204)
}

fn streamed(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    let mut stream = res.stream(200, &Bytes.from("text/csv"));
    stream = stream.send(&Bytes.from("a,b\n"));
    stream = stream.send(&Bytes.from(""));
    stream = stream.send(&Bytes.from("1,2\n"));
    stream.finish()
}

fn injected(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    res.reply(Response {
        status: 200,
        content_type: Bytes.from("text/html\r\nSet-Cookie: stolen=1"),
        body: Bytes.from("x"),
    })
}

fn echo(req: &Request) -> Response ! {io, alloc, panic, suspend} {
    let mut body = req.path();
    body = Bytes.push(body, 124);
    let query = req.query();
    let mut i = 0;
    while i < Bytes.len(&query) { body = Bytes.push(body, Bytes.get(&query, i)); i = i + 1; }
    body = Bytes.push(body, 124);
    match req.header(&Bytes.from("x-NAME")) {
        Option.Some(value) => {
            let mut j = 0;
            while j < Bytes.len(&value) { body = Bytes.push(body, Bytes.get(&value, j)); j = j + 1; }
        },
        Option.None => { body = Bytes.push(body, 45); },
    }
    Response { status: 200, content_type: Bytes.from("text/plain"), body: body }
}

fn wrapped(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
    web.answer(req, res, echo)
}

fn run(req: &Request, handler: fn(&Request, Responder) -> Unit ! {io, alloc, panic, suspend}) -> Unit ! {io, alloc, panic, suspend} {
    match web.capture(req, handler) {
        Result.Ok(out) => { let _ = io.write(io.stdout(), &out); },
        Result.Err(code) => print_i64(-code),
    }
    let _ = io.write(io.stdout(), &Bytes.from("|\n"));
}

fn main() -> i64 ! {io, alloc, panic, suspend} {
    let none = Bytes.with_capacity(0);
    run(&web.request_for(Method.Get, &Bytes.from("/hello?x=1"), Bytes.copy(&none)), hello);
    run(&web.request_for(Method.Get, &Bytes.from("/nope"), Bytes.copy(&none)), hello);
    run(&web.request_for(Method.Head, &Bytes.from("/hello"), Bytes.copy(&none)), hello);
    run(&web.request_for(Method.Post, &Bytes.from("/d"), Bytes.copy(&none)), data);
    run(&web.request_for(Method.Get, &Bytes.from("/"), Bytes.copy(&none)), empty);
    run(&web.request_for(Method.Get, &Bytes.from("/"), Bytes.copy(&none)), streamed);
    run(&web.request_for(Method.Head, &Bytes.from("/"), Bytes.copy(&none)), streamed);
    run(&web.request_for(Method.Get, &Bytes.from("/"), Bytes.copy(&none)), injected);
    // A parsed request: header lookup, path and query, Connection: close.
    let raw = Bytes.from("GET /p/q?a=1&b HTTP/1.1\r\nHost: h\r\nX-Name: kush\r\nConnection: close\r\n\r\n");
    match http1.parse_head(&raw, &http1.limits()) {
        Parse.Complete(head) => {
            let request = web.request(&raw, head, Bytes.copy(&none));
            print_i64(request.field_count());
            let target = request.target();
            print_i64(Bytes.len(&target));
            run(&request, wrapped);
        },
        Parse.Incomplete => print_i64(-1),
        Parse.Reject(status) => print_i64(status),
    }
    0
}
"#;

#[test]
fn every_responder_form_writes_one_response() {
    let output = both(RESPONDER);
    let expected = "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 2\r\n\r\nhi|\n\
HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 2\r\n\r\n|\n\
HTTP/1.1 201 Created\r\nContent-Type: application/json\r\nContent-Length: 11\r\n\r\n{\"ok\":true}|\n\
HTTP/1.1 204 No Content\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/csv\r\nTransfer-Encoding: chunked\r\n\r\n4\r\na,b\n\r\n4\r\n1,2\n\r\n0\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: text/csv\r\nTransfer-Encoding: chunked\r\n\r\n|\n\
HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 1\r\n\r\nx|\n\
3\n10\n\
HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 15\r\nConnection: close\r\n\r\n/p/q|a=1&b|kush|\n";
    assert_eq!(output, expected);
}

#[test]
fn a_responder_is_answered_exactly_once() {
    let prelude = "use std.web;\nuse std.web.Request;\nuse std.web.Responder;\n";
    for (body, message) in [
        ("fn h(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} { }", "linear value is not consumed"),
        (
            "fn h(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
                 if req.path_is(&Bytes.from(\"/\")) { res.status(200) }
             }",
            "linear",
        ),
        (
            "fn h(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
                 res.status(200); res.status(500)
             }",
            "moved",
        ),
        (
            "fn h(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
                 let s = res.stream(200, &Bytes.from(\"text/plain\"));
             }",
            "linear value is not consumed",
        ),
        (
            "fn h(req: &Request, res: Responder) -> Unit ! {io, alloc, panic, suspend} {
                 let forged = web.Responder { fd: 1, head_only: false, keep_alive: true, chunked: true, timeout_ms: 0 };
                 forged.status(200); res.status(200)
             }",
            "private",
        ),
    ] {
        let source = format!("{prelude}{body}\nfn main() -> i64 ! {{}} {{ 0 }}");
        match checked(&source) {
            Ok(_) => panic!("accepted: {body}"),
            Err(error) => assert!(error.contains(message), "{body}: {error}"),
        }
    }
}
