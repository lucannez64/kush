use kush::executable::{Executable, check};

const CLI: &str = include_str!("../../../examples/json.kush");
fn run(program: &Executable, input: &[u8]) -> (i64, Vec<u8>) {
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_io_and_stats(&mut &input[..], &mut output)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{input:?}");
    (status, output)
}

#[test]
fn json_values_numbers_unicode_and_duplicate_keys_round_trip() {
    let p = check(CLI).unwrap();
    for (input, output) in [
        (" null \n", "null"),
        (" [true, false, null] ", "[true,false,null]"),
        ("-0.12300e+9999", "-0.12300e+9999"),
        (
            "123456789012345678901234567890",
            "123456789012345678901234567890",
        ),
        (
            r#"{"a": 1, "a": 2, "nested": [{}, []]}"#,
            r#"{"a":1,"a":2,"nested":[{},[]]}"#,
        ),
        (r#""\u0041\u00e9\uD834\uDD1E""#, "\"Aé𝄞\""),
        (
            r#""\"\\\/\b\f\n\r\t\u0000""#,
            r#""\"\\/\u0008\u000c\u000a\u000d\u0009\u0000""#,
        ),
        ("\"Hello 世界 🌍\"", "\"Hello 世界 🌍\""),
        ("{}", "{}"),
        ("[]", "[]"),
        ("\"\"", "\"\""),
    ] {
        assert_eq!(
            run(&p, input.as_bytes()),
            (0, format!("{output}\n").into_bytes()),
            "{input}"
        );
    }
}

#[test]
fn malformed_json_fails_with_offsets_and_balanced_partial_tree_cleanup() {
    let p = check(CLI).unwrap();
    for input in [
        "",
        " ",
        "01",
        "-",
        "+1",
        "1.",
        "1e",
        "1e+",
        "NaN",
        "Infinity",
        "true false",
        "nullx",
        "[1,]",
        "{\"x\":1,}",
        "{x:1}",
        "{\"x\" 1}",
        "[1 2]",
        "{\"a\":[1,2],\"b\":",
        "\"unterminated",
        "\"line\nfeed\"",
        r#""\x00""#,
        r#""\uD800""#,
        r#""\uDC00""#,
        r#""\uD800\u0041""#,
        r#""\u12xz""#,
        r#""\u123""#,
        "[",
        "{",
        "\u{feff}null",
        "\u{000b}null",
    ] {
        let (status, out) = run(&p, input.as_bytes());
        assert_eq!(status, 1, "{input}");
        assert!(
            String::from_utf8(out).unwrap().contains(" at byte "),
            "{input}"
        );
    }
    for input in [
        b"\"\xc0\xaf\"".as_slice(),
        b"\"\xed\xa0\x80\"",
        b"\"\xf4\x90\x80\x80\"",
        b"\"\x80\"",
        b"\"\xe2\x82\"",
    ] {
        assert_eq!(run(&p, input).0, 1, "{input:?}");
    }
    assert_eq!(
        run(&p, b"[true,]").1,
        b"unexpected byte or end of input at byte 6\n"
    );
    assert_eq!(
        run(&p, b"null x").1,
        b"trailing input after JSON value at byte 5\n"
    );
}

#[test]
fn json_limits_are_recoverable_and_do_not_leak_partial_values() {
    let p = check(CLI).unwrap();
    let boundary = format!("{}0{}", "[".repeat(8), "]".repeat(8));
    assert_eq!(run(&p, boundary.as_bytes()).0, 0);
    let mixed = format!("{}\"\\uD83D\\uDE80\"{}", "{\"k\":".repeat(8), "}".repeat(8));
    assert_eq!(run(&p, mixed.as_bytes()).0, 0);
    let empty_deep = format!("{}{}", "[".repeat(9), "]".repeat(9));
    assert_eq!(run(&p, empty_deep.as_bytes()).0, 1);
    let deep = format!("{}0{}", "[".repeat(18), "]".repeat(18));
    assert_eq!(run(&p, deep.as_bytes()).0, 1);
    let wide = format!("[{}]", vec!["0"; 257].join(","));
    assert_eq!(run(&p, wide.as_bytes()).0, 1);
    assert_eq!(run(&p, &vec![b' '; 65537]).0, 2);
}

#[test]
fn stringify_validates_user_constructed_numbers_and_strings() {
    for value in [
        "json.Value.Number(Bytes.from(\"01\"))",
        "json.Value.Number(Bytes.from(\"\"))",
        "json.Value.String(Bytes.push(Bytes.with_capacity(1), 255))",
    ] {
        let source = format!(
            r#"use std.result.Result; use std.json;
            fn main() -> i64 ! {{alloc, panic}} {{
                match json.stringify({value}) {{ Ok(_) => 9, Err(_) => 0 }}
            }}"#
        );
        let p = check(&source).unwrap();
        assert_eq!(run(&p, b"").0, 0);
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn json_native_and_reference_agree_for_valid_invalid_and_partial_trees() {
    use kush::native::{self, Scratch};
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let program = check(CLI).unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("json");
    native::build(&program, &binary).unwrap();
    let mut corpus = vec![
        b"{\"todo\":[{\"title\":\"Ship Kush\",\"done\":false}],\"n\":1.2300e+42}".to_vec(),
        br#"{"unicode":"\uD83D\uDE80","controls":"\u0000\n"}"#.to_vec(),
        b"[1,true,null,{},[]]".to_vec(),
        b"{\"a\":1,\"a\":2}".to_vec(),
        b"[1,]".to_vec(),
        b"{\"a\":[1,2],\"b\":\"bad\\q\"}".to_vec(),
        b"\"\xed\xa0\x80\"".to_vec(),
        b"-1.2e-99999".to_vec(),
        b"true false".to_vec(),
    ];
    corpus.push(format!("{}0{}", "[".repeat(18), "]".repeat(18)).into_bytes());
    // This valid boundary exceeds the reference evaluator's fuel budget when
    // parsing AND serializing; check the native result directly against input.
    let maximum = format!("[{}]", vec!["0"; 256].join(","));
    let mut child = Command::new(&binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(maximum.as_bytes())
        .unwrap();
    let actual = child.wait_with_output().unwrap();
    assert_eq!(actual.status.code(), Some(0));
    assert_eq!(actual.stdout, format!("{maximum}\n").as_bytes());
    assert!(actual.stderr.is_empty());
    for input in corpus {
        let (status, output) = run(&program, &input);
        let mut child = Command::new(&binary)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(&input).unwrap();
        let actual = child.wait_with_output().unwrap();
        assert_eq!(
            actual.status.code(),
            Some(status as i32),
            "{input:?}: {}",
            String::from_utf8_lossy(&actual.stderr)
        );
        assert_eq!(actual.stdout, output, "{input:?}");
        assert!(
            actual.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&actual.stderr)
        );
    }
}
