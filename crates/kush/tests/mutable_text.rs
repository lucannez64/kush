//! Exclusive text views: `&mut str`. A view is created from a `&mut String`
//! (or narrowed from another `&mut str`) and holds an exclusive loan on its
//! owner. Its only writes keep the bytes valid UTF-8 and never change the
//! length: ASCII case changes, and `Str.set_scalar`, which replaces one scalar
//! by another of the same encoded width and panics otherwise. Every positive
//! case runs in the reference evaluator and, on Linux x86-64, natively.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("mutable-text-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native_aborts(source: &str) {
    let program = check(source).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("mutable-text-abort");
    kush::native::build(&program, &binary).unwrap();
    let output = std::process::Command::new(&binary).output().unwrap();
    assert!(!output.status.success(), "native code must abort: {source}");
}

fn panics(source: &str, fragment: &str) {
    let program = check(source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains(fragment), "{error:?}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    native_aborts(source);
}

#[test]
fn mutable_text_views_write_valid_utf8_in_place() {
    agrees(
        r#"
        fn shout<'a>(text: &'a mut str) -> Unit ! {} { Str.make_ascii_uppercase(text); }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut s = String.from("héllo wörld");
            {
                let v = s.as_mut_str();
                shout(&mut v[..]);
                print_i64(Str.len(v));
                print_i64(v.scalar_len());
                let tail: &mut str = &mut v[7..];
                Str.make_ascii_lowercase(tail);
                Str.set_scalar(tail, 1, 'ō');
                tail.set_scalar(0, 'W');
            }
            let w = String.as_str(&s);
            let copy = Str.to_string(w);
            print_i64(String.byte_at(&copy, 0));
            print_i64(String.byte_at(&copy, 1));
            print_i64(String.byte_at(&copy, 8));
            print_i64(String.byte_at(&copy, 9));
            String.len(&copy)
        }"#,
        13,
        "13\n11\n72\n195\n197\n141\n",
    );
    // A function may narrow and return an exclusive text view; the owner is
    // usable again after the view's last use.
    agrees(
        r#"
        fn rest<'a>(text: &'a mut str) -> &'a mut str ! {panic} { &mut text[1..] }
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let r = rest(String.as_mut_str(&mut s));
            Str.make_ascii_uppercase(r);
            let first = String.byte_at(&s, 0);
            let second = String.byte_at(&s, 1);
            first * 1000 + second
        }"#,
        97 * 1000 + 66,
        "",
    );
    // A four-byte scalar replaced by another four-byte scalar.
    agrees(
        r#"
        use std.option.Option;
        fn main() -> i64 ! {io, alloc, panic} {
            let mut s = String.from("a😀b");
            {
                let v = String.as_mut_str(&mut s);
                Str.set_scalar(v, 1, '😎');
            }
            match String.scalar_at(&s, 1) {
                Option.Some(c) => print_int(c.code()),
                Option.None => print_i64(0),
            }
            String.len(&s)
        }"#,
        6,
        "128526\n",
    );
}

#[test]
fn documented_mutable_text_example_runs() {
    agrees(
        r#"
        fn shout(text: &mut str) -> Unit ! {} { Str.make_ascii_uppercase(text); }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut s = String.from("héllo wörld");
            let v = s.as_mut_str();
            shout(&mut v[..]);
            let shared: &str = &v[0..1];
            print_i64(Str.byte_at(shared, 0));
            let tail: &mut str = &mut v[7..];
            Str.make_ascii_lowercase(tail);
            Str.set_scalar(tail, 1, 'ō');
            print_i64(s.len());
            print_i64(s.byte_at(7));
            0
        }"#,
        0,
        "72\n13\n119\n",
    );
}

#[test]
fn invalid_utf8_writes_panic_in_both_backends() {
    // A width mismatch, an offset inside a scalar, and an offset past the end.
    panics(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("hé");
            let v = String.as_mut_str(&mut s);
            Str.set_scalar(v, 1, 'x');
            0
        }"#,
        "same UTF-8 width",
    );
    panics(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("hé");
            let v = String.as_mut_str(&mut s);
            Str.set_scalar(v, 2, 'x');
            0
        }"#,
        "not a scalar boundary",
    );
    panics(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("ab");
            let v = String.as_mut_str(&mut s);
            Str.set_scalar(v, 2, 'x');
            0
        }"#,
        "not a scalar boundary",
    );
    // Subview ends are scalar boundaries.
    panics(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("hé");
            let v = String.as_mut_str(&mut s);
            let w: &mut str = &mut v[0..2];
            Str.make_ascii_uppercase(w);
            0
        }"#,
        "",
    );
    // There is no raw byte write: a `&mut str` is not a byte slice.
    rejects(
        r#"fn poke(text: &mut str) -> Unit ! {panic} { Slice.set(text, 0, 255); }
        fn main() -> i64 ! {} { 0 }"#,
        "Slice.set",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("ab");
            let v = String.as_mut_str(&mut s);
            let p = &mut v[0];
            0
        }"#,
        "a &str view is not indexed by a single index",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let s = String.from("ab");
            let v = String.as_str(&s);
            Str.make_ascii_uppercase(v);
            0
        }"#,
        "writes through an exclusive '&mut str' view",
    );
}

#[test]
fn mutable_text_views_hold_an_exclusive_loan() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            let w = String.as_str(&s);
            Str.make_ascii_uppercase(v);
            Str.len(w)
        }"#,
        "while an exclusive",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            Str.make_ascii_uppercase(v);
            let n = String.byte_at(&s, 0);
            Str.make_ascii_lowercase(v);
            n
        }"#,
        "cannot borrow an owner while an exclusive",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            let moved = s;
            Str.make_ascii_uppercase(v);
            0
        }"#,
        "cannot move an owner while it is borrowed",
    );
    // Two exclusive subviews of one view alias.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            let a: &mut str = &mut v[0..1];
            let b: &mut str = &mut v[1..2];
            Str.make_ascii_uppercase(a);
            Str.make_ascii_uppercase(b);
            0
        }"#,
        "cannot create an exclusive",
    );
    // A shared view cannot be upgraded, and an immutable owner cannot lend
    // an exclusive view.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let s = String.from("abc");
            let v = String.as_str(&s);
            let w: &mut str = &mut v[..];
            0
        }"#,
        "cannot create an exclusive '&mut str' view from a shared '&str'",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let s = String.from("abc");
            let v = s.as_mut_str();
            0
        }"#,
        "cannot mutably borrow an immutable binding",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&s);
            0
        }"#,
        "String.as_mut_str needs an exclusive '&mut String'",
    );
}

#[test]
fn mutable_text_views_cannot_outlive_or_escape_their_owner() {
    rejects(
        r#"
        fn leak<'a>() -> &'a mut str ! {alloc} {
            let mut s = String.from("abc");
            String.as_mut_str(&mut s)
        }
        fn main() -> i64 ! {alloc} { 0 }"#,
        "does not appear on any parameter",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let v = {
                let mut s = String.from("abc");
                String.as_mut_str(&mut s)
            };
            0
        }"#,
        "",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            let f = fn() -> Unit ! {} { Str.make_ascii_uppercase(v); };
            f();
            0
        }"#,
        "",
    );
    rejects(
        r#"
        struct Holder<'a> { text: &'a mut str }
        fn take<'a>(holder: Holder<'a>) -> Unit ! {} { }
        fn main() -> Unit ! {} { }"#,
        "a record cannot store an exclusive '&mut str' text view",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            let b = Box.new(v);
            0
        }"#,
        "",
    );
    // A view passed to a helper is moved; reborrow it with `&mut v[..]`.
    rejects(
        r#"
        fn shout(text: &mut str) -> Unit ! {} { Str.make_ascii_uppercase(text); }
        fn main() -> i64 ! {alloc, panic} {
            let mut s = String.from("abc");
            let v = String.as_mut_str(&mut s);
            shout(v);
            Str.len(v)
        }"#,
        "use after move",
    );
}
