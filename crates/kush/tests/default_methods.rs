//! Default trait method bodies.
//!
//! A trait method written with a block is a default body. An impl that omits
//! that method inherits a fresh specialization of the body with `Self` and the
//! trait's type/`Nat`/`Grade`/effect arguments substituted. An impl that
//! overrides the method must still match the trait signature exactly. There are
//! still no vtables, trait values, trait objects, associated items, blanket
//! impls, or specialization.
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
    if let Some(output) = native(source) {
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

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("default-methods-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

#[test]
fn inherited_defaults_dispatch_to_overrides_and_other_defaults() {
    agrees(
        "trait Scaled {
            fn base(self: Self) -> i64 ! {panic};
            fn scaled(self: Self, factor: i64) -> i64 ! {panic} {
                self.base() * factor
            }
            fn quadrupled(self: Self) -> i64 ! {panic} {
                self.scaled(2) * 2
            }
        }
        struct Point { x: i64 }
        struct Other { x: i64 }
        impl Scaled for Point {
            fn base(self: Self) -> i64 ! {panic} { self.x + 1 }
        }
        impl Scaled for Other {
            fn base(self: Self) -> i64 ! {panic} { self.x + 100 }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 4 };
            let other = Other { x: 4 };
            print_i64(point.scaled(2));
            print_i64(other.scaled(3));
            print_i64(point.quadrupled());
            0
        }",
        0,
        "10\n312\n20\n",
    );
}

#[test]
fn default_bodies_can_call_inherent_methods() {
    agrees(
        "struct Point { x: i64 }
        impl Point {
            fn double(self: Point) -> i64 ! {panic} { self.x * 2 }
        }
        trait Show {
            fn show(self: Self) -> i64 ! {panic} { self.double() }
        }
        impl Show for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 6 };
            print_i64(point.show());
            0
        }",
        0,
        "12\n",
    );
}

#[test]
fn overrides_must_match_the_trait_signature_exactly() {
    agrees(
        "trait Greet { fn greet(self: Self) -> i64 ! {panic} { 1 } }
        struct Point { x: i64 }
        impl Greet for Point {
            fn greet(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 7 };
            print_i64(point.greet());
            0
        }",
        0,
        "7\n",
    );
    rejects(
        "trait Greet { fn greet(self: Self) -> i64 ! {panic} { 1 } }
        struct Point { x: i64 }
        impl Greet for Point {
            fn greet(self: Self) -> i64 ! {} { self.x }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Greet { fn greet(self: Self) -> i64 ! {panic} { 1 } }
        struct Point { x: i64 }
        impl Greet for Point {
            fn greet(self: Self) -> Bool ! {panic} { true }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Greet { fn greet(self: Self) -> i64 ! {panic} { 1 } }
        struct Point { x: i64 }
        impl Greet for Point {
            fn greet(self: Self, extra: i64) -> i64 ! {panic} { extra }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
}

#[test]
fn empty_impls_inherit_every_default_and_still_require_bodyless_methods() {
    agrees(
        "trait Identity { fn identity(self: Self) -> i64 ! {} { 9 } }
        struct Point { x: i64 }
        impl Identity for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            print_i64(point.identity());
            0
        }",
        0,
        "9\n",
    );
    rejects(
        "trait Partial {
            fn value(self: Self) -> i64 ! {};
            fn doubled(self: Self) -> i64 ! {} { 2 }
        }
        struct Point { x: i64 }
        impl Partial for Point { }
        fn main() -> i64 ! {} { 0 }",
        "missing implementation of trait method 'value'",
    );
}

#[test]
fn self_is_substituted_per_impl_target() {
    agrees(
        "trait Choose {
            fn choose(self: Self, other: Self) -> Self ! {panic} {
                if self.x >= other.x { self } else { other }
            }
        }
        struct Point { x: i64 }
        struct Other { x: i64 }
        impl Choose for Point { }
        impl Choose for Other { }
        fn main() -> i64 ! {io, panic} {
            let low = Point { x: 1 };
            let high = Point { x: 5 };
            let chosen = low.choose(high);
            print_i64(chosen.x);
            let low = Other { x: 2 };
            let high = Other { x: 8 };
            let chosen = low.choose(high);
            print_i64(chosen.x);
            0
        }",
        0,
        "5\n8\n",
    );
}

#[test]
fn trait_arguments_are_substituted_into_default_signatures_and_bodies() {
    agrees(
        "trait Wrap<T> {
            fn value(self: Self) -> T ! {panic};
            fn wrapped(self: Self) -> T ! {panic} { self.value() }
        }
        struct Point { x: i64 }
        impl Wrap<i64> for Point {
            fn value(self: Self) -> i64 ! {panic} { self.x }
        }
        impl Wrap<Bool> for Point {
            fn value(self: Self) -> Bool ! {panic} { self.x == 0 }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            print_i64(point.Wrap::<i64>.wrapped());
            if point.Wrap::<Bool>.wrapped() { print_i64(1) } else { print_i64(0) }
            0
        }",
        0,
        "0\n1\n",
    );
    rejects(
        "trait Wrap<T> {
            fn value(self: Self) -> T ! {panic};
            fn wrapped(self: Self) -> T ! {panic} { self.value() }
        }
        struct Point { x: i64 }
        impl Wrap<i64> for Point {
            fn value(self: Self) -> i64 ! {panic} { self.x }
        }
        impl Wrap<Bool> for Point {
            fn value(self: Self) -> Bool ! {panic} { self.x == 0 }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            print_i64(point.wrapped());
            0
        }",
        "is ambiguous",
    );
}

#[test]
fn generic_methods_infer_beside_trait_parameters_in_defaults() {
    agrees(
        "trait Pairing<T> {
            fn head(self: Self) -> T ! {};
            fn echo<U>(self: Self, tag: T, value: U) -> (T, U) ! {} {
                (tag, value)
            }
        }
        struct Point { x: i64 }
        impl Pairing<i64> for Point {
            fn head(self: Self) -> i64 ! {} { self.x }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 9 };
            let pair = point.Pairing::<i64>.echo(4, true);
            if pair.1 { print_i64(pair.0) }
            let explicit = point.echo::<Bool>(7, false);
            if explicit.1 { print_i64(0) } else { print_i64(explicit.0) }
            0
        }",
        0,
        "4\n7\n",
    );
}

#[test]
fn trait_grade_arguments_are_substituted_into_defaults() {
    agrees(
        "trait Graded<gr: Grade> {
            fn consume2(self: Self, value: i64 @[gr]) -> i64 ! {panic} {
                value + value
            }
        }
        struct Point { x: i64 }
        impl Graded<2> for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            let value = 3;
            print_i64(point.Graded::<2>.consume2(value));
            0
        }",
        0,
        "6\n",
    );
    rejects(
        "trait Graded<gr: Grade> {
            fn consume2(self: Self, value: i64 @[gr]) -> i64 ! {panic} {
                value + value
            }
        }
        struct Point { x: i64 }
        impl Graded<1> for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            let value = 3;
            print_i64(point.Graded::<1>.consume2(value));
            0
        }",
        "is not used consistently",
    );
}

#[test]
fn borrowed_receiver_defaults_keep_their_receiver_contract() {
    agrees(
        "trait Offset {
            fn sum_with(self: &Self, other: i64) -> i64 ! {panic} {
                self.x + other
            }
        }
        struct Point { x: i64 }
        impl Offset for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 7 };
            print_i64(point.sum_with(5));
            0
        }",
        0,
        "12\n",
    );
    rejects(
        "enum Choice { Left, Right }
        trait Shift { fn shift(self: &Self) -> i64 ! {} { 1 } }
        impl Shift for Choice { }
        fn main() -> i64 ! {} { 0 }",
        "borrowed receivers are supported only for nominal record targets",
    );
    agrees(
        "trait Bump {
            fn bump(self: &mut Self) -> i64 ! {panic} {
                self.x = self.x + 1;
                self.x
            }
        }
        struct Point { x: i64 }
        impl Bump for Point { }
        fn main() -> i64 ! {io, panic} {
            let mut point = Point { x: 4 };
            print_i64(point.bump());
            print_i64(point.x);
            0
        }",
        0,
        "5\n5\n",
    );
}

#[test]
fn inherited_defaults_join_unqualified_ambiguity_and_qualification() {
    agrees(
        "trait First { fn tag(self: Self) -> i64 ! {} { 1 } }
        trait Second { fn tag(self: Self) -> i64 ! {} { 2 } }
        struct Point { x: i64 }
        impl First for Point { }
        impl Second for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            print_i64(point.First.tag());
            print_i64(point.Second.tag());
            0
        }",
        0,
        "1\n2\n",
    );
    rejects(
        "trait First { fn tag(self: Self) -> i64 ! {} { 1 } }
        trait Second { fn tag(self: Self) -> i64 ! {} { 2 } }
        struct Point { x: i64 }
        impl First for Point { }
        impl Second for Point { }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 0 };
            print_i64(point.tag());
            0
        }",
        "is ambiguous",
    );
}

#[test]
fn default_bodies_are_checked_when_inherited() {
    rejects(
        "trait Bad { fn bad(self: Self) -> i64 ! {} { self.x + 1 } }
        struct Point { x: i64 }
        impl Bad for Point { }
        fn main() -> i64 ! {} { 0 }",
        "operation requires effects {panic}",
    );
    rejects(
        "trait Fieldy { fn x(self: Self) -> i64 ! {} { 1 } }
        struct Point { x: i64 }
        impl Fieldy for Point { }
        fn main() -> i64 ! {} { 0 }",
        "collides with a record field",
    );
}

#[test]
fn cross_module_defaults_inherit_the_trait_visibility() {
    let root = std::env::temp_dir().join(format!(
        "kush-default-methods-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(
        root.join("demo").join("show.kush"),
        r#"module demo.show;
        pub struct Marker { x: i64 }
        fn bias() -> i64 ! {} { 40 }
        pub trait Show {
            fn show(self: Self) -> i64 ! {panic} { bias() + 2 }
        }
        "#,
    )
    .unwrap();
    // The impl lives in a different module from the trait. The default body is
    // still checked in `demo.show`, so its private helper `bias` stays callable.
    std::fs::write(
        root.join("demo").join("impls.kush"),
        r#"module demo.impls;
        use demo.show.Marker;
        use demo.show.Show;
        impl Show for Marker { }
        "#,
    )
    .unwrap();
    std::fs::write(
        root.join("main.kush"),
        r#"use demo.show.Marker;
        use demo.impls;
        fn main() -> i64 ! {io, panic} {
            let marker = Marker { x: 1 };
            print_i64(marker.show());
            0
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "42\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("default-methods-module");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"42\n");
    }
    let _ = std::fs::remove_dir_all(&root);

    // A private trait keeps its inherited defaults private to its module.
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(
        root.join("demo").join("show.kush"),
        r#"module demo.show;
        pub struct Marker { x: i64 }
        trait Show {
            fn show(self: Self) -> i64 ! {} { 42 }
        }
        impl Show for Marker { }
        "#,
    )
    .unwrap();
    std::fs::write(
        root.join("main.kush"),
        r#"use demo.show.Marker;
        fn main() -> i64 ! {io, panic} {
            let marker = Marker { x: 1 };
            print_i64(marker.show());
            0
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let error = kush::executable::check_program(&loaded).unwrap_err();
    assert!(
        error.message.contains("is private to module 'demo.show'"),
        "{error:?}"
    );
    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn default_methods_example_matches_documented_output() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/default-methods.kush");
    let loaded = kush::program::load_path(&root).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "10\n312\n20\n9\n42\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("default-methods-example");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"10\n312\n20\n9\n42\n");
    }
}
