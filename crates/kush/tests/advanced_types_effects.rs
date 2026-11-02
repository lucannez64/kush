//! Advanced types and effects: structural records, constrained subtype
//! inference, effect handlers, general row constraints, versioned runtime
//! proofs, and runtime-sized inline arrays.
//!
//! Each feature has positive, rejection, cleanup, and native/reference tests.
//! The tests describe the supported fragment, not a claim that the full v0.1
//! dependent/algebraic/effect calculus is implemented.

use kush::executable::{MemoryStats, check};

fn evaluate(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
    (result, stats)
}

fn value(source: &str) -> i64 {
    evaluate(source).0
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn agrees(source: &str, expected: i64) {
    use std::process::Command;
    let program = check(source).unwrap();
    let (reference, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(reference, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("advanced-types-effects");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
}

// ---------------------------------------------------------------------------
// Structural records
// ---------------------------------------------------------------------------

#[test]
fn structural_width_coercion_reorders_and_drops_affine_fields() {
    // The target row is canonical (sorted), so the source declaration order is
    // irrelevant. `extra: Box<i64>` is absent from the target and must be
    // dropped exactly once by the checked conversion.
    let source = r#"
        struct Wide { b: i64, a: i64, extra: Box<i64> }
        fn sum(v: struct { a: i64, b: i64 }) -> i64 ! {panic} { v.a + v.b }
        fn main() -> i64 ! {alloc, panic} {
            let w = Wide { b: 20, a: 22, extra: Box.new(1) };
            sum(w)
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn structural_alias_and_parameter_share_the_canonical_row() {
    let source = r#"
        struct Point { x: i64, y: i64, tag: Bool }
        type Pair = struct { y: i64, x: i64 };
        fn read(p: Pair) -> i64 ! {panic} { p.x - p.y }
        fn main() -> i64 ! {panic} {
            read(Point { x: 42, y: 0, tag: true })
        }"#;
    assert_eq!(value(source), 42);
}

#[test]
fn structural_missing_field_and_changed_borrowed_leaf_are_rejected() {
    rejects(
        r#"
        struct Point { x: i64 }
        fn read(p: struct { x: i64, y: i64 }) -> i64 ! {panic} { p.x + p.y }
        fn main() -> i64 ! {panic} { read(Point { x: 1 }) }"#,
        "no field 'y'",
    );
    rejects(
        r#"
        struct Window<'a> { view: &'a mut [i64], n: i64 }
        fn keep<'a>(w: struct { view: &'a [i64], n: i64 }) -> i64 ! {} { w.n }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            keep(Window { view: &mut a[..], n: 1 })
        }"#,
        "cannot convert field 'view'",
    );
}

#[test]
fn structural_width_cannot_erase_a_linear_field() {
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        struct Wide { a: i64, token: Token }
        fn read(v: struct { a: i64 }) -> i64 ! {panic} { v.a }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 1 };
            read(Wide { a: 1, token: token })
        }"#,
        "linear obligation",
    );
}

#[test]
fn structural_nested_representation_change_is_explicitly_rejected() {
    rejects(
        r#"
        struct Inner { x: i64 }
        struct Outer { inner: Inner }
        fn read(v: struct { inner: struct { x: i64 } }) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} { read(Outer { inner: Inner { x: 1 } }) }"#,
        "nested representation change",
    );
}

#[test]
fn structural_borrowed_field_transfer_keeps_cleanup_balanced() {
    let source = r#"
        struct View<'a> { view: &'a mut [i64], n: i64, extra: Box<i64> }
        fn keep<'a>(v: struct { n: i64, view: &'a mut [i64] }) -> i64 ! {} { v.n }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            keep(View { view: &mut a[..], n: 42, extra: Box.new(1) })
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}
