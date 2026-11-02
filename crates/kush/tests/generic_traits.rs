//! Generic static traits and generic methods.
//!
//! A trait's type/Nat/Grade parameters are part of its static identity, so one
//! receiver type may implement several specializations. Generic methods are
//! monomorphized exactly like generic free functions. There are still no
//! vtables, trait values, trait objects, associated types, or blanket impls.
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
        let binary = scratch.path().join("generic-traits-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

const CONVERT: &str = r#"
struct Point { x: i64, y: i64 }
trait Convert<T> { fn render(self: Self) -> T ! {panic}; }
impl Convert<i64> for Point {
    fn render(self: Self) -> i64 ! {panic} { self.x * 10 + self.y }
}
impl Convert<Bool> for Point {
    fn render(self: Self) -> Bool ! {panic} { self.x == 0 }
}
"#;

#[test]
fn concrete_generic_trait_specializations_are_distinct() {
    agrees(
        &format!(
            "{CONVERT}
            fn main() -> i64 ! {{io, panic}} {{
                let point = Point {{ x: 4, y: 2 }};
                print_i64(point.Convert::<i64>.render());
                if point.Convert::<Bool>.render() {{ print_i64(1) }} else {{ print_i64(0) }}
                let zero = Point {{ x: 0, y: 9 }};
                if zero.Convert::<Bool>.render() {{ print_i64(2) }} else {{ print_i64(3) }}
                0
            }}"
        ),
        0,
        "42\n0\n2\n",
    );
}

#[test]
fn generic_trait_duplicates_and_unqualified_ambiguity_are_explicit() {
    rejects(
        &format!(
            "{CONVERT}
            impl Convert<i64> for Point {{
                fn render(self: Self) -> i64 ! {{panic}} {{ 0 }}
            }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "duplicate implementation of trait 'Convert<i64>'",
    );
    rejects(
        &format!(
            "{CONVERT}
            fn main() -> i64 ! {{panic}} {{
                let point = Point {{ x: 1, y: 2 }};
                point.render()
            }}"
        ),
        "is ambiguous",
    );
}

#[test]
fn generic_trait_bounds_are_discharged_at_specialization() {
    agrees(
        &format!(
            "{CONVERT}
            fn convert_point<T: Convert<i64>>(value: T) -> i64 ! {{panic}} {{
                value.Convert::<i64>.render()
            }}
            fn main() -> i64 ! {{io, panic}} {{
                print_i64(convert_point(Point {{ x: 2, y: 3 }}));
                0
            }}"
        ),
        0,
        "23\n",
    );
    rejects(
        &format!(
            "{CONVERT}
            struct Plain {{ n: i64 }}
            fn helper<T: Convert<i64>>(value: T) -> i64 ! {{}} {{ 7 }}
            fn main() -> i64 ! {{panic}} {{ helper(Plain {{ n: 1 }}) }}"
        ),
        "does not implement trait 'Convert<i64>'",
    );
}

#[test]
fn generic_trait_argument_arity_is_checked_at_declarations_and_bounds() {
    rejects(
        "struct P { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        impl Convert for P { fn render(self: Self) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {} { 0 }",
        "expects 1 argument(s), found 0",
    );
    rejects(
        "struct P { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        impl Convert<i64, Bool> for P { fn render(self: Self) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {} { 0 }",
        "expects 1 argument(s), found 2",
    );
    rejects(
        "struct P { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        fn helper<T: Convert>(value: T) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }",
        "expects 1 argument(s), found 0",
    );
    rejects(
        "struct P { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        impl Convert<i64> for P { fn render(self: Self) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {} {
            let p = P { x: 1 };
            p.Convert.render()
        }",
        "trait 'Convert' is generic; qualify the call",
    );
}

#[test]
fn self_and_trait_arguments_substitute_into_impl_contracts() {
    agrees(
        "struct Point { x: i64, y: i64 }
        trait Merge<T> {
            fn merge(self: Self, other: Self, extra: T) -> Self ! {panic};
        }
        impl Merge<i64> for Point {
            fn merge(self: Point, other: Point, extra: i64) -> Point ! {panic} {
                Point { x: self.x + other.x + extra, y: self.y + other.y }
            }
        }
        fn main() -> i64 ! {io, panic} {
            let left = Point { x: 1, y: 2 };
            let right = Point { x: 3, y: 4 };
            let merged = left.Merge::<i64>.merge(right, 10);
            print_i64(merged.x);
            print_i64(merged.y);
            0
        }",
        0,
        "14\n6\n",
    );
}

#[test]
fn trait_methods_may_be_generic_and_alpha_equivalent() {
    agrees(
        "struct Point { x: i64 }
        trait Pairing<T> {
            fn pair<U>(self: Self, value: U) -> (T, U) ! {};
        }
        impl Pairing<i64> for Point {
            fn pair<V>(self: Self, value: V) -> (i64, V) ! {} { (self.x, value) }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 5 };
            let inferred = point.Pairing::<i64>.pair(true);
            if inferred.1 { print_i64(inferred.0); }
            let explicit = point.pair::<i64>(7);
            print_i64(explicit.1);
            0
        }",
        0,
        "5\n7\n",
    );
    agrees(
        "trait Pick {
            fn pick<T>(self: Self, erased positive: { 0 < self }, value: T) -> T ! {};
        }
        impl Pick for i64 {
            fn pick<U>(self: Self, erased positive: { 0 < self }, value: U) -> U ! {} {
                value
            }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64((5).Pick.pick(_, 7));
            0
        }",
        0,
        "7\n",
    );
}

#[test]
fn generic_method_contracts_require_matching_parameters_effects_grades_and_evidence() {
    rejects(
        "trait Wrap { fn map<U>(self: Self, value: U) -> U ! {}; }
        struct P { x: i64 }
        impl Wrap for P { fn map(self: Self, value: i64) -> i64 ! {} { value } }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "struct P { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        impl Convert<i64> for P { fn render(self: Self) -> i64 ! {panic} { self.x } }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "struct P { x: i64 }
        trait Consume<T> { fn apply<U>(self: Self, value: U @[1]) -> U ! {}; }
        impl Consume<i64> for P {
            fn apply<V>(self: Self, value: V @[2]) -> V ! {} { value }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Witness<T> {
            fn fetch(self: Self, erased proof: { 0 < self }) -> T ! {};
        }
        impl Witness<i64> for i64 {
            fn fetch(self: Self, erased other: { 1 < self }) -> i64 ! {} { self }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Convert<T> { fn render(self: Self) -> T ! {}; }
        struct P { x: i64 }
        impl Convert<Bool> for P { fn render(self: Self) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
}

#[test]
fn generic_inherent_method_identity_cleans_up_owning_types() {
    let source = r#"
        struct Token { text: String }
        struct Point { x: i64 }
        impl Token {
            fn unwrap_with<T>(self: Token, note: T) -> String ! {alloc, panic} {
                let Token { text } = self;
                text
            }
        }
        impl Point {
            fn echo<T>(self: Point, value: T) -> T ! {} { value }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let first = Token { text: String.from("abcd") };
            let second = Token { text: String.from("xy") };
            let first_text = first.unwrap_with(1);
            let second_text = second.unwrap_with(true);
            print_i64(first_text.len());
            print_i64(second_text.len());
            print_i64(Point { x: 9 }.echo(4));
            0
        }
    "#;
    let (status, output, stats) = run(source);
    assert_eq!(status, 0);
    assert_eq!(output, "4\n2\n4\n");
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stats.allocations > 0);
    if let Some(output) = native(source) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"4\n2\n4\n");
    }
}

#[test]
fn generic_methods_infer_or_accept_explicit_arguments_and_keep_static_dispatch() {
    let program = check(
        "struct Point { x: i64 }
        impl Point {
            fn echo<T>(self: Point, value: T) -> T ! {} { value }
        }
        fn main() -> i64 ! {} { Point { x: 9 }.echo(4) }",
    )
    .unwrap();
    let (status, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(status, 4);
    assert_eq!(stats.allocations, 0, "static dispatch adds no allocation");
    assert_eq!(stats.allocations, stats.deallocations);

    agrees(
        "struct Point { x: i64 }
        impl Point {
            fn echo<T>(self: Point, value: T) -> T ! {} { value }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(Point { x: 1 }.echo::<i64>(7));
            0
        }",
        0,
        "7\n",
    );
    rejects(
        "struct Point { x: i64 }
        impl Point {
            fn echo<T>(self: Point, value: T) -> T ! {} { value }
        }
        fn main() -> i64 ! {} { Point { x: 1 }.echo::<i64, Bool>(7) }",
        "expects 1 type/grade/const/effect arguments, found 2",
    );
    rejects(
        "struct Point { x: i64 }
        impl Point {
            fn echo<T>(self: Point, value: T) -> T ! {} { value }
        }
        fn main() -> i64 ! {panic} {
            let point = Point { x: 1 };
            Point { x: 0 }.echo::<&Point>(&point)
        }",
        "borrowed record cannot be passed through an ordinary generic type parameter",
    );
}

#[test]
fn generic_method_receivers_are_evaluated_once_before_later_arguments() {
    agrees(
        "struct Point { x: i64 }
        impl Point {
            fn mix<T>(self: Point, value: T) -> T ! {io, panic} {
                print_i64(self.x);
                value
            }
        }
        fn make(value: i64) -> Point ! {io, panic} {
            print_i64(value);
            Point { x: value }
        }
        fn argument(value: i64) -> i64 ! {io, panic} {
            print_i64(value);
            value
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(make(1).mix(argument(3)));
            0
        }",
        0,
        "1\n3\n1\n3\n",
    );
}

#[test]
fn generic_method_bounds_are_not_dropped_when_the_body_ignores_them() {
    rejects(
        "struct Plain { n: i64 }
        struct Point { x: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {}; }
        impl Convert<i64> for Point { fn render(self: Self) -> i64 ! {} { self.x } }
        impl Point {
            fn ignore_bound<U: Convert<i64>>(self: Point, value: U) -> i64 ! {} { 7 }
        }
        fn main() -> i64 ! {panic} {
            let point = Point { x: 1 };
            point.ignore_bound(Plain { n: 2 })
        }",
        "does not implement trait 'Convert<i64>'",
    );
}

#[test]
fn borrowed_record_receivers_compose_with_generic_methods() {
    agrees(
        "struct Counter { value: i64 }
        impl Counter {
            fn pick<T>(self: &Self, fallback: T) -> T ! {} { fallback }
            fn value_plus<T>(&self, extra: T) -> i64 ! {panic} { self.value + 1 }
        }
        fn main() -> i64 ! {io, panic} {
            let counter = Counter { value: 41 };
            print_i64(counter.pick(7));
            print_i64(counter.value_plus::<i64>(9));
            print_i64(counter.value);
            0
        }",
        0,
        "7\n42\n41\n",
    );
}

#[test]
fn exclusive_loans_survive_into_later_generic_method_arguments() {
    rejects(
        "struct P { x: i64 }
        impl P {
            fn consume<T>(self: &mut Self, value: T) -> Unit ! {panic} {
                self.x = self.x + 1;
            }
            fn peek(&self) -> i64 ! {panic} { self.x }
        }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            p.consume(p.peek());
        }",
        "exclusive",
    );
    rejects(
        "struct P { x: i64 }
        impl P {
            fn consume<T>(self: &mut Self, value: T) -> Unit ! {panic} {
                self.x = self.x + 1;
            }
        }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            p.consume(p.x)
        }",
        "while an exclusive",
    );
}

#[test]
fn generic_nat_and_grade_trait_parameters_are_compile_time_identity() {
    agrees(
        "struct Chunk { bytes: i64 }
        trait Chunked<N: Nat> { fn width(self: Self) -> i64 ! {}; }
        impl Chunked<3> for Chunk {
            fn width(self: Self) -> i64 ! {} { 3 }
        }
        fn use_chunk<T: Chunked<3>>(value: T) -> i64 ! {} {
            value.Chunked::<3>.width()
        }
        fn main() -> i64 ! {io, panic} {
            let chunk = Chunk { bytes: 9 };
            print_i64(chunk.Chunked::<3>.width());
            print_i64(use_chunk(Chunk { bytes: 1 }));
            0
        }",
        0,
        "3\n3\n",
    );
    rejects(
        "struct Chunk { bytes: i64 }
        trait Chunked<N: Nat> { fn width(self: Self) -> i64 ! {}; }
        impl Chunked<3> for Chunk { fn width(self: Self) -> i64 ! {} { 3 } }
        fn helper<T: Chunked<4>>(value: T) -> i64 ! {} { 0 }
        fn main() -> i64 ! {panic} { helper(Chunk { bytes: 1 }) }",
        "does not implement trait 'Chunked<4>'",
    );
    agrees(
        "struct Counter { n: i64 }
        trait Cost<g: Grade> {
            fn charge(self: Self, value: i64 @[g]) -> i64 ! {panic};
        }
        impl Cost<1> for Counter {
            fn charge(self: Self, value: i64 @[1]) -> i64 ! {panic} { self.n + value }
        }
        fn main() -> i64 ! {io, panic} {
            let counter = Counter { n: 4 };
            print_i64(counter.Cost::<1>.charge(2));
            0
        }",
        0,
        "6\n",
    );
}

#[test]
fn generic_nominal_impl_targets_and_generic_impl_headers_work() {
    agrees(
        "struct Pair<T> { first: T, second: T }
        trait First<T> { fn first_value(self: Self) -> T ! {}; }
        impl First<i64> for Pair<i64> {
            fn first_value(self: Self) -> i64 ! {} { self.first }
        }
        fn main() -> i64 ! {io, panic} {
            let pair = Pair { first: 3, second: 4 };
            print_i64(pair.First::<i64>.first_value());
            0
        }",
        0,
        "3\n",
    );
    // Generic impl headers are now implemented. The trait argument is
    // specialized per receiver, and the method body sees `Self = Pair<T>`.
    agrees(
        "struct Pair<T> { first: T, second: T }
        trait First<T> { fn first_value(self: Self) -> T ! {}; }
        impl<U> First<U> for Pair<U> {
            fn first_value(self: Self) -> U ! {} { self.first }
        }
        fn main() -> i64 ! {io, panic} {
            let pair = Pair { first: 7, second: 8 };
            print_i64(pair.First::<i64>.first_value());
            0
        }",
        0,
        "7\n",
    );
    rejects(
        "struct Pair<T, U> { first: T, second: U }
        trait First<T> { fn first_value(self: Self) -> T ! {}; }
        impl<T> First<i64> for Pair<T, i64> {
            fn first_value(self: Self) -> i64 ! {} { 0 }
        }
        impl<T> First<i64> for Pair<i64, T> {
            fn first_value(self: Self) -> i64 ! {} { 1 }
        }
        fn main() -> i64 ! {} { 0 }",
        "incomparable",
    );
}

#[test]
fn generic_trait_method_lifetimes_are_alpha_equivalent() {
    agrees(
        "struct Reader { bias: i64 }
        trait FirstView<T> {
            fn first<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        impl FirstView<i64> for Reader {
            fn first<'b>(self: Self, values: &'b [i64]) -> &'b [i64] ! {panic} {
                &values[..1]
            }
        }
        fn main() -> i64 ! {io, panic} {
            let values: [i64; 2] = [10, 20];
            let reader = Reader { bias: 0 };
            let view = reader.FirstView::<i64>.first(&values[..]);
            print_i64(view[0]);
            0
        }",
        0,
        "10\n",
    );
}

#[test]
fn cross_module_generic_traits_and_methods_require_visibility() {
    let root = std::env::temp_dir().join(format!(
        "kush-generic-traits-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(
        root.join("demo").join("generic.kush"),
        r#"module demo.generic;
        pub struct Point { x: i64 }
        pub trait Convert<T> { fn render(self: Self) -> T ! {panic}; }
        impl Convert<i64> for Point {
            pub fn render(self: Self) -> i64 ! {panic} { self.x }
        }
        impl Point {
            pub fn echo<T>(self: Point, value: T) -> T ! {} { value }
            fn hidden<T>(self: Point, value: T) -> T ! {} { value }
        }
        "#,
    )
    .unwrap();
    std::fs::write(
        root.join("main.kush"),
        r#"use demo.generic.Point;
        use demo.generic.Convert;
        fn run<T: Convert<i64>>(value: T) -> i64 ! {panic} {
            value.Convert::<i64>.render()
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 4 };
            print_i64(point.echo(9));
            print_i64(run(Point { x: 3 }));
            0
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "9\n3\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("generic-traits-multi-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"9\n3\n");
    }

    std::fs::write(
        root.join("main.kush"),
        r#"use demo.generic.Point;
        fn main() -> i64 ! {} {
            let point = Point { x: 4 };
            point.hidden(1)
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let error = kush::executable::check_program(&loaded).unwrap_err();
    assert!(
        error
            .message
            .contains("is private to module 'demo.generic'"),
        "{error:?}"
    );
    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn generic_traits_example_matches_documented_output() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/generic_traits.kush");
    let loaded = kush::program::load_path(&root).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "42\n1\n23\n5\n3\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("generic-traits-example");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"42\n1\n23\n5\n3\n");
    }
}
