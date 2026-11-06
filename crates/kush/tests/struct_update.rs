//! STRUCT-UPDATE (user-approved Rust semantics, 2026-11-06):
//! `S { f: v, ..base }` takes the fields it does not name from `base`, which
//! is consumed. Replaced owned fields are dropped; a linear one cannot be.
//! Outside the struct's module every field must be visible. The checker knows
//! each field: `x.f == v` and `x.g == base.g`, and `let x = S { .. }` records
//! the literal's fields. Every accepted program runs in the reference
//! evaluator and natively with balanced allocations.
use kush::executable::check;

fn agrees(source: &str, expected: i64, stdout: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (value, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(value, expected, "{source}");
    assert_eq!(String::from_utf8_lossy(&output), stdout, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "cleanup: {source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("struct-update");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
    }
}

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

const CONFIG: &str = "
struct Config { retries: i64, verbose: Bool, name: Bytes, limit: i64 }
fn config() -> Config ! {alloc, panic} {
    Config { retries: 1, verbose: false, name: Bytes.from(\"abc\"), limit: 10 }
}
";

#[test]
fn update_takes_the_other_fields_from_the_base() {
    // A field value may read the base before it is consumed.
    agrees(
        &format!(
            "{CONFIG}
            fn main() -> i64 ! {{alloc, panic}} {{
                let c = config();
                let d = Config {{ retries: c.retries + 4, ..c }};
                let n = Bytes.len(&d.name);
                let Config {{ retries, verbose, name, limit }} = d;
                drop(name);
                retries * 100 + limit + n + (if verbose {{ 1000 }} else {{ 0 }})
            }}"
        ),
        513,
        "",
    );
    // A replaced owned field is dropped; the new one is kept. A call base.
    agrees(
        &format!(
            "{CONFIG}
            fn main() -> i64 ! {{alloc, panic}} {{
                let d = Config {{ name: Bytes.from(\"longer name\"), verbose: true, ..config() }};
                let Config {{ retries, verbose, name, limit }} = d;
                let n = Bytes.len(&name);
                drop(name);
                n + retries + limit + (if verbose {{ 100 }} else {{ 0 }})
            }}"
        ),
        122,
        "",
    );
    // No overrides; nested updates; generic records.
    agrees(
        "struct Pair<T> { left: T, right: T }
        struct Outer { inner: Pair<i64>, tag: i64 }
        fn main() -> i64 ! {panic} {
            let p = Pair { left: 1, right: 2 };
            let q = Pair { ..p };
            let o = Outer { inner: q, tag: 5 };
            let r = Outer { inner: Pair { right: 40, ..o.inner }, ..o };
            r.inner.left + r.inner.right + r.tag
        }",
        46,
        "",
    );
    // Field values are evaluated in source order, after the base.
    agrees(
        "struct T { a: i64, b: i64, c: i64 }
        fn say(n: i64) -> i64 ! {io, panic} { print_i64(n); n }
        fn main() -> i64 ! {io, panic} {
            let t = T { c: say(3), a: say(1), ..T { a: say(7), b: say(8), c: say(9) } };
            t.a * 100 + t.b * 10 + t.c
        }",
        183,
        "7\n8\n9\n3\n1\n",
    );
}

#[test]
fn update_rejections() {
    let base = "struct S { a: i64, b: i64 } struct U { a: i64 }";
    for (body, fragment) in [
        // The base has another type.
        (
            "let u = U { a: 1 }; let s = S { a: 2, ..u }; s.a",
            "must have type S",
        ),
        // An unknown field.
        (
            "let s = S { a: 1, b: 2 }; let t = S { c: 1, ..s }; t.a",
            "no field 'c'",
        ),
        // Type arguments come from the base.
        (
            "let s = S { a: 1, b: 2 }; let t = S.<i64> { a: 1, ..s }; t.a",
            "",
        ),
        // A reference is not a base.
        (
            "let s = S { a: 1, b: 2 }; let t = S { a: 1, ..&s }; t.a",
            "must have type S",
        ),
    ] {
        rejects(
            &format!("{base} fn main() -> i64 ! {{panic}} {{ {body} }}"),
            fragment,
        );
    }
    // The base is consumed: an owned base cannot be used afterwards.
    rejects(
        &format!(
            "{CONFIG}
            fn main() -> i64 ! {{alloc, panic}} {{
                let c = config();
                let d = Config {{ retries: 2, ..c }};
                let n = Bytes.len(&c.name);
                drop(d);
                n
            }}"
        ),
        "moved",
    );
    // `..base` must come last.
    assert!(kush::parse("fn f() -> Unit ! {} { let s = S { ..b, a: 1 }; }").is_err());
    assert!(kush::parse("fn f() -> Unit ! {} { let s = S { a: 1, ..b, }; }").is_err());
    // A linear field cannot be replaced: the base's value would be dropped.
    rejects(
        "#[linear] struct Token { id: i64 }
        struct Holder { token: Token, n: i64 }
        fn spend(t: Token) -> i64 ! {} { let Token { id } = t; id }
        fn main() -> i64 ! {panic} {
            let h = Holder { token: Token { id: 1 }, n: 2 };
            let g = Holder { token: Token { id: 3 }, ..h };
            let Holder { token, n } = g;
            spend(token) + n
        }",
        "linear",
    );
    // Moving a linear field through the update is fine.
    agrees(
        "#[linear] struct Token { id: i64 }
        struct Holder { token: Token, n: i64 }
        fn spend(t: Token) -> i64 ! {} { let Token { id } = t; id }
        fn main() -> i64 ! {panic} {
            let h = Holder { token: Token { id: 1 }, n: 2 };
            let g = Holder { n: 40, ..h };
            let Holder { token, n } = g;
            spend(token) + n
        }",
        41,
        "",
    );
}

#[test]
fn update_fields_are_known_to_the_prover() {
    let prelude = "struct S { a: i64, b: i64, flag: Bool }
        fn small(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }";
    // Replaced and kept fields, and a let of a literal.
    agrees(
        &format!(
            "{prelude}
            fn main() -> i64 ! {{panic}} {{
                let s = S {{ a: 3, b: 9, flag: true }};
                let x = small(s.a, _) + small(s.b, _);
                let t = S {{ a: 4, ..s }};
                x + small(t.a, _) + small(t.b, _)
            }}"
        ),
        25,
        "",
    );
    // A postcondition about an update, proved.
    agrees(
        &format!(
            "{prelude}
            fn raise(s: S, by: i64) -> S ! {{panic}}
                ensures {{ result.a == s.a + by && result.b == s.b && result.flag == s.flag }}
            {{
                S {{ a: s.a + by, ..s }}
            }}
            fn main() -> i64 ! {{panic}} {{
                let r = raise(S {{ a: 1, b: 2, flag: false }}, 5);
                small(r.a, _) + small(r.b, _)
            }}"
        ),
        8,
        "",
    );
    // Wrong claims are rejected.
    rejects(
        &format!(
            "{prelude}
            fn main() -> i64 ! {{panic}} {{
                let s = S {{ a: 3, b: 11, flag: true }};
                let t = S {{ a: 4, ..s }};
                small(t.b, _)
            }}"
        ),
        "cannot prove",
    );
    rejects(
        &format!(
            "{prelude}
            fn raise(s: S, by: i64) -> S ! {{panic}}
                ensures {{ result.b == s.b + 1 }}
            {{
                S {{ a: s.a + by, ..s }}
            }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "cannot prove",
    );
    // A loop that rebinds the record forgets the literal's facts, and a
    // `&mut` borrow makes the local opaque.
    rejects(
        &format!(
            "{prelude}
            fn main() -> i64 ! {{panic}} {{
                let mut s = S {{ a: 3, b: 9, flag: true }};
                let mut i = 0;
                while i < 3 {{ s = S {{ a: s.a + 5, ..s }}; i = i + 1; }}
                let t = s;
                small(t.a - 5, _)
            }}"
        ),
        "cannot prove",
    );
    rejects(
        &format!(
            "{prelude}
            fn set(s: &mut S) -> Unit ! {{}} {{ s.a = 20; }}
            fn main() -> i64 ! {{panic}} {{
                let mut s = S {{ a: 3, b: 9, flag: true }};
                set(&mut s);
                let t = S {{ b: 1, ..s }};
                small(t.a, _)
            }}"
        ),
        "",
    );
}
