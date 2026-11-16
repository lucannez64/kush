//! WEB-URL: bounded URL decoding. Every program runs
//! in the reference evaluator and natively with the same output.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::process::{Command, Stdio};

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program =
        kush::program::load_source("<web-url-test>", source).map_err(|(_, error)| error.message)?;
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

fn native(source: &str) -> String {
    let program = checked(source).unwrap_or_else(|error| panic!("{error}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("web-url");
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

fn both(source: &str) -> String {
    let reference = reference(source);
    assert_eq!(native(source), reference, "native and reference differ");
    reference
}

#[test]
fn decoding() {
    assert_eq!(
        both(
            r#"
use std.url;
use std.result.Result;
use std.io;
use std.text;
use std.test;
use std.web;
use std.http1.Method;
fn run() -> Result<Unit, url.Error> ! {io, alloc, panic} {
    let req = web.request_for(Method.Get, &Bytes.from("/a%2Fb?x=%3F%26"), Bytes.from(""));
    let segments = url.path_segments(&req.path(), 64)?;
    test.is_true(segments.segment_count() == 2);
    test.is_true(text.eq(&segments.segment(1), &Bytes.from("a/b")));
    let fields = url.query(&req.query(), 64)?;
    test.is_true(text.eq(&fields.value(0), &Bytes.from("?&")));
    let decoded = url.percent_decode(&Bytes.from("caf%C3%A9+%252F"), 100)?;
    test.is_true(text.eq(&decoded, &Bytes.from("café+%2F")));
    let path = url.path_segments(&Bytes.from("/a%2fb//c/"), 100)?;
    test.is_true(path.segment_count() == 5);
    test.is_true(text.eq(&path.segment(0), &Bytes.from("")));
    test.is_true(text.eq(&path.segment(1), &Bytes.from("a/b")));
    test.is_true(text.eq(&path.segment(2), &Bytes.from("")));
    test.is_true(text.eq(&path.segment(3), &Bytes.from("c")));
    test.is_true(text.eq(&path.segment(4), &Bytes.from("")));
    let q = url.query(&Bytes.from("x=a+b&x=%26%3D&bare&=v&&z=a=b"), 100)?;
    test.is_true(q.field_count() == 5);
    test.is_true(text.eq(&q.value(0), &Bytes.from("a+b")));
    test.is_true(text.eq(&q.name(1), &Bytes.from("x")));
    test.is_true(text.eq(&q.value(1), &Bytes.from("&=")));
    test.is_true(text.eq(&q.value(2), &Bytes.from("")));
    test.is_true(text.eq(&q.name(3), &Bytes.from("")));
    test.is_true(text.eq(&q.value(4), &Bytes.from("a=b")));
    let f = url.form(&Bytes.from("x=a+b%2Bc"), 100)?;
    test.is_true(text.eq(&f.value(0), &Bytes.from("a b+c")));
    let empty = url.query(&Bytes.from(""), 0)?;
    test.is_true(empty.field_count() == 0);
    test.is_true(Bytes.len(&url.percent_decode(&Bytes.from(""), 0)?) == 0);
    test.is_true(Bytes.len(&url.percent_decode(&Bytes.from("abc"), 3)?) == 3);
    let path = url.path_segments(&Bytes.from(""), 0)?;
    test.is_true(path.segment_count() == 1);
    let form = url.form(&Bytes.from("&&"), 2)?;
    test.is_true(form.field_count() == 0);
    Ok(())
}
fn main() -> Unit ! {io, alloc, panic} {
    match run() { Result.Ok(_) => print_i64(1), Result.Err(_) => panic() }
}
"#
        ),
        "1\n"
    );
}

#[test]
fn malformed_and_limits() {
    let mut source = String::from(
        r#"
use std.url;
use std.url.Error;
use std.result.Result;
use std.test;
use std.io;
fn main() -> Unit ! {io, alloc, panic} {
"#,
    );
    for (input, error) in [
        ("%", "InvalidEscape"),
        ("%0", "InvalidEscape"),
        ("%gg", "InvalidEscape"),
        ("%0/", "InvalidEscape"),
        ("%80", "InvalidUtf8"),
        ("%C0%AF", "InvalidUtf8"),
        ("%C2", "InvalidUtf8"),
        ("%E0%80%80", "InvalidUtf8"),
        ("%ED%A0%80", "InvalidUtf8"),
        ("%F0%80%80%80", "InvalidUtf8"),
        ("%F4%90%80%80", "InvalidUtf8"),
        ("%F5%80%80%80", "InvalidUtf8"),
        ("%E2%28%A1", "InvalidUtf8"),
    ] {
        source.push_str(&format!(
            "match url.percent_decode(&Bytes.from(\"{input}\"), 100) {{ Result.Err(Error.{error}) => (), _ => panic() }};\n"
        ));
    }
    for function in ["percent_decode", "path_segments", "query", "form"] {
        for (input, limit) in [("abc", 2), ("", -1), ("%", 0)] {
            source.push_str(&format!(
                "match url.{function}(&Bytes.from(\"{input}\"), {limit}) {{ Result.Err(Error.TooLong) => (), _ => panic() }};\n"
            ));
        }
    }
    source.push_str(r#"
    match url.path_segments(&Bytes.from("/ok/%GG"), 100) {
        Result.Err(Error.InvalidEscape) => (), _ => panic()
    };
    match url.query(&Bytes.from("ok=1&bad=%FF"), 100) {
        Result.Err(Error.InvalidUtf8) => (), _ => panic()
    };
    match url.form(&Bytes.from("%GG=x"), 100) {
        Result.Err(Error.InvalidEscape) => (), _ => panic()
    };
    let raw = Bytes.push(Bytes.with_capacity(1), 255);
    match url.percent_decode(&raw, 1) {
        Result.Err(Error.InvalidUtf8) => (), _ => panic()
    };
    // Every UTF-8 width, including its boundary scalar values.
    match url.percent_decode(&Bytes.from("%00%7F%C2%80%DF%BF%E0%A0%80%ED%9F%BF%EE%80%80%EF%BF%BF%F0%90%80%80%F4%8F%BF%BF"), 200) {
        Result.Ok(value) => test.is_true(Bytes.len(&value) == 26),
        Result.Err(_) => panic()
    };
    print_i64(1)
}
"#);
    assert_eq!(both(&source), "1\n");
}
