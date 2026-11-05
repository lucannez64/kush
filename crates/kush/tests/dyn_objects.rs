//! Trait-object types beyond one plain trait: explicit associated-type
//! bindings (`dyn Trait<Out = T>`) and multi-trait objects (`dyn A + B`).
//! Every accepted program runs in the reference evaluator and the native
//! backend with balanced allocations.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("dyn-objects-test");
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
    stats
}

/// `Conv`'s only impl is generic, so its projection is unknown until a member
/// is registered, unless a `dyn Conv<Out = T>` binding fixes it.
const CONV: &str = r#"
struct Label { text: String }
struct W<T> { value: T }
trait Conv {
    type Out;
    fn conv(self: &Self) -> Self.Out ! {alloc, panic};
    fn size(self: &Self) -> i64 ! {panic};
}
impl<T> Conv for W<T> {
    type Out = Label;
    fn conv(self: &Self) -> Label ! {alloc, panic} { Label { text: "made" } }
    fn size(self: &Self) -> i64 ! {panic} { 7 }
}
"#;

#[test]
fn an_explicit_binding_fixes_the_projection_before_any_member() {
    // `use_it` is checked before `main` registers the first member.
    let stats = agrees(
        &format!(
            "{CONV}
            fn use_it(object: &dyn Conv<Out = Label>) -> i64 ! {{alloc, panic}} {{
                let Label {{ text }} = object.conv();
                String.len(&text) + object.size()
            }}
            fn unused(object: &dyn Conv<Out = Label>) -> i64 ! {{alloc, panic}} {{ object.size() }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let object: dyn Conv = W {{ value: 1 }};
                print_i64(use_it(&object));
                let other: dyn Conv<Out = Label> = W {{ value: true }};
                print_i64(use_it(&other));
                0
            }}"
        ),
        0,
        "11\n11\n",
    );
    // Two payloads and two "made" strings, each released once.
    assert_eq!(stats.allocations, 4);
    rejects(
        &format!(
            "{CONV}
            fn use_it(object: &dyn Conv) -> i64 ! {{alloc, panic}} {{
                let Label {{ text }} = object.conv();
                String.len(&text)
            }}
            fn main() -> i64 ! {{alloc, panic}} {{ 0 }}"
        ),
        "associated type 'Out'",
    );
}

#[test]
fn a_binding_is_checked_against_members_impls_and_other_bindings() {
    // A later member projects a different type.
    rejects(
        &format!(
            "{CONV}
            fn size(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.size() }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Conv = W {{ value: 1 }};
                size(&object)
            }}"
        ),
        "already fixed it as i64",
    );
    // Two bindings disagree.
    rejects(
        &format!(
            "{CONV}
            fn a(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.size() }}
            fn b(object: &dyn Conv<Out = Bool>) -> i64 ! {{panic}} {{ object.size() }}
            fn main() -> i64 ! {{alloc, panic}} {{ 0 }}"
        ),
        "already fixed as",
    );
    // Concrete impls agree on a different type: closed-world object, and a
    // nominal field lowered before the impls are collected.
    let concrete = r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Conv { type Out; fn conv(self: &Self) -> Self.Out ! {panic}; }
        impl Conv for A { type Out = i64; fn conv(self: &Self) -> i64 ! {panic} { self.x } }
        impl Conv for B { type Out = i64; fn conv(self: &Self) -> i64 ! {panic} { self.y } }
    "#;
    rejects(
        &format!(
            "{concrete}
            fn f(object: &dyn Conv<Out = Bool>) -> Bool ! {{panic}} {{ object.conv() }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "fixed as",
    );
    rejects(
        &format!(
            "{concrete}
            struct Holder {{ object: dyn Conv<Out = Bool> }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "fixes it as Bool",
    );
    // An agreeing binding on a closed-world object keeps the union (no
    // payload allocation).
    let stats = agrees(
        &format!(
            "{concrete}
            fn f(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.conv() }}
            fn main() -> i64 ! {{io, panic}} {{
                let object: dyn Conv<Out = i64> = A {{ x: 5 }};
                print_i64(f(&object));
                0
            }}"
        ),
        0,
        "5\n",
    );
    assert_eq!(stats.allocations, 0);
}

#[test]
fn binding_syntax_is_validated() {
    for (binding, expected) in [
        ("dyn Conv<Nope = i64>", "declares no associated type 'Nope'"),
        ("dyn Conv<Out = i64, Out = i64>", "bound twice"),
    ] {
        rejects(
            &format!(
                "{CONV}
                fn f(object: &{binding}) -> i64 ! {{panic}} {{ object.size() }}
                fn main() -> i64 ! {{panic}} {{ 0 }}"
            ),
            expected,
        );
    }
    let generic = r#"
        struct W<T> { value: T }
        trait Into<X> { type Out; fn into(self: &Self, x: X) -> Self.Out ! {panic}; }
        impl<T> Into<i64> for W<T> { type Out = i64; fn into(self: &Self, x: i64) -> i64 ! {panic} { x + 1 } }
    "#;
    rejects(
        &format!(
            "{generic}
            fn f(object: &dyn Into<Out = i64, i64>) -> i64 ! {{panic}} {{ 0 }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "trait arguments must come before",
    );
    agrees(
        &format!(
            "{generic}
            fn f(object: &dyn Into<i64, Out = i64>) -> i64 ! {{panic}} {{ object.into(4) }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Into<i64> = W {{ value: 0 }};
                f(&object)
            }}"
        ),
        5,
        "",
    );
}
