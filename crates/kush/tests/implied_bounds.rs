//! The Rust implied-bounds soundness hole (rust-lang/rust#25860) translated to
//! Kush. Rust accepts `fn foo<'a, 'b>(_: &'a &'b (), v: &'b T) -> &'a T { v }`
//! because the argument type implies `'b: 'a`, and loses that implied fact
//! when `foo` is coerced to a function pointer, so a dangling reference can be
//! manufactured. Kush never assumes a bound from an argument type: the bound is
//! written into `foo`'s signature, checked at every call, and an arrow type
//! that omits it is a type mismatch.
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
        let binary = scratch.path().join("implied-bounds-test");
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

#[test]
fn an_arrow_that_drops_the_inferred_bound_is_a_type_mismatch() {
    // The exploit: coerce `foo` to an arrow without `'q: 'p`, then pass a
    // long-lived anchor and a short-lived value.
    for program in [
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn bad<'a, 'z>(unit: &'z Anchor<'z>, x: &'a Point) -> &'z Point ! {} {
    let f: fn<'p, 'q>(&'p Anchor<'q>, &'q Point) -> &'p Point ! {} = foo;
    f(unit, x)
}
fn main() -> i64 ! {alloc, panic} {
    let keep = Point { x: 1, y: 1 };
    let unit = Anchor { p: &keep };
    let r = {
        let s = Point { x: 42, y: 0 };
        bad(&unit, &s)
    };
    let junk = Point { x: 9, y: 9 };
    r.x + junk.x * 0
}"#,
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn main() -> i64 ! {alloc, panic} {
    let keep = Point { x: 1, y: 1 };
    let unit = Anchor { p: &keep };
    let f: fn<'p, 'q>(&'p Anchor<'q>, &'q Point) -> &'p Point ! {} = foo;
    let r = {
        let s = Point { x: 42, y: 0 };
        f(&unit, &s)
    };
    let junk = Point { x: 9, y: 9 };
    r.x + junk.x * 0
}"#,
    ] {
        let error = check(program).unwrap_err();
        assert!(error.message.contains("type mismatch"), "{error:?}");
        // Both sides print the arrow's canonical lifetime names.
        assert!(
            error
                .message
                .contains("fn<'a, 'b>(&'a Anchor<'b>, &'b Point)"),
            "{error:?}"
        );
        assert!(!error.message.contains("'q"), "{error:?}");
    }
}

#[test]
fn the_inferred_bound_is_checked_at_every_call() {
    // A direct call and an unannotated function value keep the bound.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn main() -> i64 ! {alloc, panic} {
    let keep = Point { x: 1, y: 1 };
    let unit = Anchor { p: &keep };
    let r = {
        let s = Point { x: 42, y: 0 };
        foo(&unit, &s)
    };
    let junk = Point { x: 9, y: 9 };
    r.x + junk.x * 0
}"#,
        "this call cannot establish the callee's outlives constraint 'b: 'a",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn main() -> i64 ! {alloc, panic} {
    let keep = Point { x: 1, y: 1 };
    let unit = Anchor { p: &keep };
    let f = foo;
    let r = {
        let s = Point { x: 42, y: 0 };
        f(&unit, &s)
    };
    let junk = Point { x: 9, y: 9 };
    r.x + junk.x * 0
}"#,
        "this call cannot establish the callee's outlives constraint 'b: 'a",
    );
    // An arrow that states the bound is checked at its call with a real
    // diagnostic (this used to be an internal error).
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b: 'a>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn bad<'a, 'z>(unit: &'z Anchor<'z>, x: &'a Point) -> &'z Point ! {} {
    let f: fn<'p, 'q: 'p>(&'p Anchor<'q>, &'q Point) -> &'p Point ! {} = foo;
    f(unit, x)
}
fn main() -> i64 ! {} { 0 }"#,
        "this call cannot establish the callee's outlives constraint 'b: 'a",
    );
    // When the bound holds, both the direct and the arrow call run.
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b: 'a>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn relay<'z>(anchor: &'z Anchor<'z>, x: &'z Point) -> &'z Point ! {} { foo(anchor, x) }
fn main() -> i64 ! {} {
    let keep = Point { x: 1, y: 1 };
    let anchor = Anchor { p: &keep };
    relay(&anchor, &keep).x
}"#,
        1,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Anchor<'b> { p: &'b Point }
fn foo<'a, 'b: 'a>(u: &'a Anchor<'b>, v: &'b Point) -> &'a Point ! {} { v }
fn good<'z>(anchor: &'z Anchor<'z>, x: &'z Point) -> &'z Point ! {} {
    let f: fn<'p, 'q: 'p>(&'p Anchor<'q>, &'q Point) -> &'p Point ! {} = foo;
    f(anchor, x)
}
fn main() -> i64 ! {} {
    let keep = Point { x: 7, y: 1 };
    let anchor = Anchor { p: &keep };
    good(&anchor, &keep).x
}"#,
        7,
        "",
    );
}
