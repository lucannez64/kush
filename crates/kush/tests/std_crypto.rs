//! WEB-CRYPTO: std.sha256, std.sha1, std.hmac, std.ct, std.base64 and
//! std.random against known-answer vectors (FIPS 180-4 examples, RFC 4231,
//! RFC 4648, RFC 6455, and values computed with Python's hashlib, hmac and
//! base64). Both backends must agree and the evaluator must free every
//! allocation.
use kush::executable::check;

const PRELUDE: &str = r#"
use std.result.Result;
use std.option.Option;
use std.sha256;
use std.sha1;
use std.hmac;
use std.ct;
use std.base64;
use std.random;

fn hex(b: &Bytes) -> Bytes ! {alloc} {
    let digits = Bytes.from("0123456789abcdef");
    let mut out = Bytes.with_capacity(Bytes.len(b) * 2);
    let mut i = 0;
    while i < Bytes.len(b) {
        let v = Bytes.get(b, i);
        out = Bytes.push(out, Bytes.get(&digits, v >> 4));
        out = Bytes.push(out, Bytes.get(&digits, v & 15));
        i = i + 1;
    }
    drop(digits);
    out
}

fn line(text: Bytes) -> Unit ! {io, alloc} {
    let t = Bytes.push(text, 10);
    match IO.write(IO.stdout(), &t) { Result.Ok(_) => {}, Result.Err(_) => {} };
    drop(t);
}

fn repeat(byte: i64, n: i64) -> Bytes ! {alloc} {
    let mut out = Bytes.with_capacity(n);
    let mut i = 0;
    while i < n {
        out = Bytes.push(out, byte);
        i = i + 1;
    }
    out
}

fn show(decoded: Option<Bytes>) -> Unit ! {io, alloc} {
    match decoded {
        Option.Some(b) => { line(hex(&b)); drop(b); },
        Option.None => line(Bytes.from("none")),
    }
}
"#;

fn agrees(body: &str) -> String {
    let source = format!("{PRELUDE}\n{body}");
    let output = reference(&source);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(native(&source), output);
    output
}

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("crypto");
    kush::native::build(&program, &binary).unwrap();
    let native = std::process::Command::new(&binary).output().unwrap();
    assert_eq!(
        native.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&native.stderr)
    );
    String::from_utf8(native.stdout).unwrap()
}

fn lines(expected: &[&str]) -> String {
    expected.iter().map(|line| format!("{line}\n")).collect()
}

#[test]
fn sha256_and_sha1_match_known_digests() {
    // Empty, FIPS 180-4 examples, and every padding boundary: 55 bytes fits
    // the length in the same block, 56 and 64 need a second one.
    let output = agrees(
        r#"
        fn both(data: Bytes) -> Unit ! {io, alloc} {
            line(hex(&sha256.digest(&data)));
            line(hex(&sha1.digest(&data)));
            drop(data);
        }
        fn main() -> i64 ! {io, alloc} {
            both(Bytes.from(""));
            both(Bytes.from("abc"));
            both(Bytes.from("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"));
            both(repeat(97, 55));
            both(repeat(97, 56));
            both(repeat(97, 64));
            both(repeat(97, 119));
            both(repeat(97, 1000));
            0
        }"#,
    );
    assert_eq!(
        output,
        lines(&[
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            "da39a3ee5e6b4b0d3255bfef95601890afd80709",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            "a9993e364706816aba3e25717850c26c9cd0d89d",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
            "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318",
            "c1c8bbdc22796e28c0e15163d20899b65621d65a",
            "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
            "c2db330f6083854c99d4b5bfb6e8f29f201be699",
            "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb",
            "0098ba824b5c16427bd7a1122a5a442a25ec644d",
            "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb",
            "ee971065aaa017e0632a8ca6c77bb3bf8b1dfc56",
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3",
            "291e9a6c66994949b57ba5e650361e98fc36b1ba",
        ])
    );
}

#[test]
fn incremental_updates_match_one_call() {
    // Pieces of 1, 63, 64, 200 and 672 bytes cross block boundaries in every
    // way: partial block, exact fill, whole blocks straight from the input.
    let output = agrees(
        r#"
        fn main() -> i64 ! {io, alloc} {
            let mut h = sha256.new();
            let mut g = sha1.new();
            let sizes: Vec<i64> = [1, 63, 64, 200, 672];
            let mut i = 0;
            while i < Vec.len(&sizes) {
                let piece = repeat(97, Vec.get(&sizes, i));
                h = sha256.update(h, &piece);
                g = sha1.update(g, &piece);
                drop(piece);
                i = i + 1;
            }
            line(hex(&sha256.finish(h)));
            line(hex(&sha1.finish(g)));
            0
        }"#,
    );
    assert_eq!(
        output,
        lines(&[
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3",
            "291e9a6c66994949b57ba5e650361e98fc36b1ba",
        ])
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn a_million_bytes_hash_natively() {
    // FIPS 180-4's long example; too many steps for the reference budget.
    let source = format!(
        "{PRELUDE}\n{}",
        r#"
        fn main() -> i64 ! {io, alloc} {
            let data = repeat(97, 1000000);
            line(hex(&sha256.digest(&data)));
            line(hex(&sha1.digest(&data)));
            0
        }"#
    );
    assert_eq!(
        native(&source),
        lines(&[
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0",
            "34aa973cd4c4daa4f61eeb2bdbad27316534016f",
        ])
    );
}

#[test]
fn hmac_sha256_matches_rfc_4231_and_verifies_in_constant_time() {
    let output = agrees(
        r#"
        fn main() -> i64 ! {io, alloc} {
            // RFC 4231 test cases 1, 2 and 6 (a 131-byte key is hashed first),
            // and a key of exactly one block.
            line(hex(&hmac.sign(&repeat(11, 20), &Bytes.from("Hi There"))));
            line(hex(&hmac.sign(&Bytes.from("Jefe"), &Bytes.from("what do ya want for nothing?"))));
            let long = repeat(170, 131);
            let message = Bytes.from("Test Using Larger Than Block-Size Key - Hash Key First");
            let tag = hmac.sign(&long, &message);
            line(hex(&tag));
            line(hex(&hmac.sign(&repeat(107, 64), &Bytes.from(""))));
            // verify: the right tag, a tag with one bit flipped, a short tag.
            let ok = hmac.verify(&long, &message, &tag);
            let mut flipped = Bytes.with_capacity(32);
            let mut i = 0;
            while i < 32 {
                let byte = Bytes.get(&tag, i);
                flipped = Bytes.push(flipped, if i == 31 { byte ^ 1 } else { byte });
                i = i + 1;
            }
            let bad = hmac.verify(&long, &message, &flipped);
            let short = hmac.verify(&long, &message, &Bytes.from("abc"));
            print_i64(if ok { 1 } else { 0 });
            print_i64(if bad { 1 } else { 0 });
            print_i64(if short { 1 } else { 0 });
            0
        }"#,
    );
    assert_eq!(
        output,
        lines(&[
            "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
            "83026a325aaee70e36cfe607536aa1054104ad1077c36134810d4ccded1ccd3b",
            "1",
            "0",
            "0",
        ])
    );
}

#[test]
fn constant_time_equal_compares_bytes_and_lengths() {
    let output = agrees(
        r#"
        fn main() -> i64 ! {io, alloc} {
            print_i64(if ct.equal(&Bytes.from(""), &Bytes.from("")) { 1 } else { 0 });
            print_i64(if ct.equal(&Bytes.from("secret"), &Bytes.from("secret")) { 1 } else { 0 });
            print_i64(if ct.equal(&Bytes.from("secret"), &Bytes.from("secreT")) { 1 } else { 0 });
            print_i64(if ct.equal(&Bytes.from("Secret"), &Bytes.from("secret")) { 1 } else { 0 });
            print_i64(if ct.equal(&Bytes.from("secret"), &Bytes.from("secrets")) { 1 } else { 0 });
            0
        }"#,
    );
    assert_eq!(output, lines(&["1", "1", "0", "0", "0"]));
}

#[test]
fn base64_round_trips_rfc_4648_vectors_in_both_alphabets() {
    let output = agrees(
        r#"
        fn row(data: Bytes) -> Unit ! {io, alloc} {
            let standard = base64.encode(&data);
            let url = base64.encode_url(&data);
            line(Bytes.copy(&standard));
            line(Bytes.copy(&url));
            show(base64.decode(&standard));
            show(base64.decode_url(&url));
            drop(standard);
            drop(url);
            drop(data);
        }
        fn main() -> i64 ! {io, alloc} {
            row(Bytes.from(""));
            row(Bytes.from("f"));
            row(Bytes.from("fo"));
            row(Bytes.from("foo"));
            row(Bytes.from("foob"));
            row(Bytes.from("fooba"));
            row(Bytes.from("foobar"));
            let mut odd = Bytes.with_capacity(3);
            odd = Bytes.push(odd, 251);
            odd = Bytes.push(odd, 255);
            odd = Bytes.push(odd, 191);
            row(odd);
            0
        }"#,
    );
    let mut expected = Vec::new();
    for (data, standard, url) in [
        ("", "", ""),
        ("66", "Zg==", "Zg"),
        ("666f", "Zm8=", "Zm8"),
        ("666f6f", "Zm9v", "Zm9v"),
        ("666f6f62", "Zm9vYg==", "Zm9vYg"),
        ("666f6f6261", "Zm9vYmE=", "Zm9vYmE"),
        ("666f6f626172", "Zm9vYmFy", "Zm9vYmFy"),
        ("fbffbf", "+/+/", "-_-_"),
    ] {
        expected.extend([standard, url, data, data]);
    }
    assert_eq!(output, lines(&expected));
}

#[test]
fn base64_decoding_is_strict_and_canonical() {
    let output = agrees(
        r#"
        fn standard(text: Bytes) -> Unit ! {io, alloc} {
            show(base64.decode(&text));
            drop(text);
        }
        fn url(text: Bytes) -> Unit ! {io, alloc} {
            show(base64.decode_url(&text));
            drop(text);
        }
        fn main() -> i64 ! {io, alloc} {
            standard(Bytes.from("Zg=="));      // 66
            standard(Bytes.from("Zg="));       // length not a multiple of 4
            standard(Bytes.from("Zh=="));      // nonzero unused bits
            standard(Bytes.from("Z==="));      // too much padding
            standard(Bytes.from("===="));
            standard(Bytes.from("Zg==Zg=="));  // padding in the middle
            standard(Bytes.from("Zm 9"));      // space
            standard(Bytes.from("-_-_"));      // URL alphabet
            url(Bytes.from("-_-_"));           // fbffbf
            url(Bytes.from("Zg=="));           // no padding in the URL form
            url(Bytes.from("Zm9vY"));          // length 1 mod 4
            url(Bytes.from("+/+/"));           // standard alphabet
            url(Bytes.from("Zh"));             // nonzero unused bits
            0
        }"#,
    );
    assert_eq!(
        output,
        lines(&[
            "66", "none", "none", "none", "none", "none", "none", "none", "fbffbf", "none", "none",
            "none", "none",
        ])
    );
}

#[test]
fn websocket_accept_key_from_rfc_6455() {
    let output = agrees(
        r#"
        fn main() -> i64 ! {io, alloc} {
            let key = Bytes.from("dGhlIHNhbXBsZSBub25jZQ==258EAFA5-E914-47DA-95CA-C5AB0DC85B11");
            line(base64.encode(&sha1.digest(&key)));
            0
        }"#,
    );
    assert_eq!(output, "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\n");
}

#[test]
fn random_bytes_come_from_the_kernel() {
    // Two 32-byte draws are distinct (a collision has probability 2^-256);
    // zero bytes is fine; a negative count is EINVAL.
    let output = agrees(
        r#"
        fn main() -> i64 ! {io, alloc} {
            let a = match random.bytes(32) { Result.Ok(b) => b, Result.Err(_) => Bytes.from("") };
            let b = match random.bytes(32) { Result.Ok(b) => b, Result.Err(_) => Bytes.from("") };
            print_i64(Bytes.len(&a));
            print_i64(Bytes.len(&b));
            print_i64(if ct.equal(&a, &b) { 1 } else { 0 });
            match random.bytes(0) {
                Result.Ok(e) => print_i64(Bytes.len(&e)),
                Result.Err(code) => print_i64(-code),
            }
            match random.bytes(-1) {
                Result.Ok(e) => print_i64(Bytes.len(&e)),
                Result.Err(code) => print_i64(code),
            }
            drop(a);
            drop(b);
            0
        }"#,
    );
    assert_eq!(output, lines(&["32", "32", "0", "0", "22"]));
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn sha_instructions_and_portable_code_give_the_same_digests() {
    // SHA-NI-STD: native builds use the CPU's SHA instructions when it has
    // them; KUSH_CPU_DISABLE=sha forces the proved portable code. Both, and
    // the evaluator, must agree on inputs crossing every padding boundary.
    let source = format!(
        "{PRELUDE}\n{}",
        r#"
        fn main() -> i64 ! {io, alloc} {
            let sizes: Vec<i64> = [0, 1, 55, 56, 63, 64, 65, 119, 128, 1000, 4096];
            let mut i = 0;
            while i < Vec.len(&sizes) {
                let data = repeat(97, Vec.get(&sizes, i));
                line(hex(&sha256.digest(&data)));
                line(hex(&sha1.digest(&data)));
                drop(data);
                i = i + 1;
            }
            0
        }"#
    );
    let program = check(&source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("both");
    kush::native::build(&program, &binary).unwrap();
    let run = |disable: Option<&str>| {
        let mut command = std::process::Command::new(&binary);
        command.env_remove("KUSH_CPU_DISABLE");
        if let Some(disable) = disable {
            command.env("KUSH_CPU_DISABLE", disable);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        String::from_utf8(output.stdout).unwrap()
    };
    let fast = run(None);
    let portable = run(Some("sha"));
    assert_eq!(fast, portable);
    assert_eq!(reference(&source), portable);
    // 1000 'a': known digests.
    assert!(portable.contains("41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"));
    assert!(portable.contains("291e9a6c66994949b57ba5e650361e98fc36b1ba"));
}
