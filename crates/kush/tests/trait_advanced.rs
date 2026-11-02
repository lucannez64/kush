//! Advanced static traits: associated types/constants, generic and blanket
//! impls with coherence, deterministic specialization, and closed-world trait
//! objects. Every accepted program is compared between the reference evaluator
//! and the Cranelift backend; every rejected contract has a focused test.
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

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("trait-advanced-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
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

const SCALED: &str = r#"
struct Point { x: i64 }

trait Scaled {
    type Out;
    const FACTOR: i64;
    fn scaled(self: Self) -> Self.Out ! {panic};
    fn bumped(self: Self) -> Self.Out ! {panic} {
        self.scaled() + Self.FACTOR
    }
}

impl Scaled for Point {
    type Out = i64;
    const FACTOR: i64 = 3;
    fn scaled(self: Self) -> i64 ! {panic} { self.x * Self.FACTOR }
}
"#;

#[test]
fn associated_types_and_constants_project_through_impls() {
    agrees(
        &format!(
            "{SCALED}
            fn main() -> i64 ! {{io, panic}} {{
                let point = Point {{ x: 4 }};
                print_i64(point.scaled());
                print_i64(point.bumped());
                print_i64(Point.FACTOR);
                0
            }}"
        ),
        0,
        "12\n15\n3\n",
    );
}

#[test]
fn associated_projection_works_in_a_bounded_generic_result() {
    agrees(
        &format!(
            "{SCALED}
            fn reveal<T: Scaled>(value: T) -> T.Out ! {{panic}} {{
                value.scaled()
            }}
            fn main() -> i64 ! {{io, panic}} {{
                print_i64(reveal(Point {{ x: 5 }}));
                0
            }}"
        ),
        0,
        "15\n",
    );
}

#[test]
fn associated_constant_defaults_and_checked_arithmetic() {
    agrees(
        r#"
        struct Marker { tag: i64 }
        trait Limits {
            const BASE: i64;
            const DOUBLE: i64 = Self.BASE * 2;
            fn value(self: Self) -> i64 ! {panic} { Self.DOUBLE }
        }
        impl Limits for Marker { const BASE: i64 = 21; }
        fn main() -> i64 ! {io, panic} {
            let marker = Marker { tag: 0 };
            print_i64(marker.value());
            print_i64(Marker.DOUBLE);
            0
        }"#,
        0,
        "42\n42\n",
    );
    rejects(
        r#"
        struct Marker { }
        trait Limits { const BASE: i64; }
        impl Limits for Marker { const BASE: i64 = 9223372036854775807 + 1; }
        fn main() -> i64 ! {} { 0 }"#,
        "outside the range of i64",
    );
    rejects(
        r#"
        struct Marker { }
        trait Limits { const BASE: i64; }
        impl Limits for Marker { const BASE: i64 = 1 / 0; }
        fn main() -> i64 ! {} { 0 }"#,
        "overflows or divides by zero",
    );
}

#[test]
fn generic_associated_constant_projections_select_the_impl() {
    agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Factor { const F: i64; fn value(self: Self) -> i64 ! {panic}; }
        impl Factor for A { const F: i64 = 3; fn value(self: Self) -> i64 ! {panic} { self.x } }
        impl Factor for B { const F: i64 = 4; fn value(self: Self) -> i64 ! {panic} { self.y } }
        fn scaled<T: Factor>(value: T) -> i64 ! {panic} { value.value() * T.F }
        fn main() -> i64 ! {io, panic} {
            print_i64(scaled(A { x: 2 }));
            print_i64(scaled(B { y: 2 }));
            0
        }"#,
        0,
        "6\n8\n",
    );
}

#[test]
fn associated_items_are_required_and_must_match_declarations() {
    rejects(
        r#"
        struct Point { x: i64 }
        trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }
        impl Show for Point { fn show(self: Self) -> i64 ! {panic} { self.x } }
        fn main() -> i64 ! {} { 0 }"#,
        "missing associated type 'Out'",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }
        impl Show for Point {
            type Out = i64;
            type Extra = Bool;
            fn show(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "not declared by the implemented trait",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Show { type Out; const LIMIT: i64; fn show(self: Self) -> Self.Out ! {panic}; }
        impl Show for Point {
            type Out = i64;
            const LIMIT: Bool = true;
            fn show(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "must have the declared type i64",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Show { const LIMIT: String; }
        impl Show for Point { const LIMIT: String = "x"; }
        fn main() -> i64 ! {} { 0 }"#,
        "compile-time scalar, tuple, or inline-array",
    );
}

#[test]
fn associated_projection_must_agree_with_the_impl_method_result() {
    rejects(
        r#"
        struct Point { x: i64 }
        trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }
        impl Show for Point {
            type Out = Bool;
            fn show(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! { } { 0 }"#,
        "does not match the trait signature exactly",
    );
}

#[test]
fn generic_impl_headers_specialize_methods_per_receiver() {
    agrees(
        r#"
        struct W<T> { value: T }
        trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }
        impl<T> Show for W<T> {
            type Out = T;
            fn show(self: Self) -> T ! {panic} { self.value }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(W { value: 7 }.show());
            print_i64(W { value: 9 }.show());
            0
        }"#,
        0,
        "7\n9\n",
    );
}

#[test]
fn blanket_impls_discharge_their_bounds_per_specialization() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct W<T> { value: T }
        trait Show { fn show(self: Self) -> i64 ! {panic}; }
        trait Loud { fn loud(self: Self) -> i64 ! {panic}; }
        impl Show for Point { fn show(self: Self) -> i64 ! {panic} { self.x } }
        impl<T: Show> Loud for W<T> {
            fn loud(self: Self) -> i64 ! {panic} { self.value.show() * 2 }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(W { value: Point { x: 5 } }.loud());
            0
        }"#,
        0,
        "10\n",
    );
    rejects(
        r#"
        struct Other { x: i64 }
        struct W<T> { value: T }
        trait Show { fn show(self: Self) -> i64 ! {panic}; }
        trait Loud { fn loud(self: Self) -> i64 ! {panic}; }
        impl<T: Show> Loud for W<T> {
            fn loud(self: Self) -> i64 ! {panic} { 1 }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(W { value: Other { x: 5 } }.loud());
            0
        }"#,
        "no method 'loud'",
    );
}

#[test]
fn generic_trait_arguments_are_solved_by_the_impl_header() {
    agrees(
        r#"
        struct W<T> { value: T }
        trait Convert<T> { type Out; fn render(self: Self) -> Self.Out ! {panic}; }
        impl<T> Convert<T> for W<T> {
            type Out = T;
            fn render(self: Self) -> T ! {panic} { self.value }
        }
        fn main() -> i64 ! {io, panic} {
            let value = W { value: 12 };
            print_i64(value.Convert::<i64>.render());
            0
        }"#,
        0,
        "12\n",
    );
}

#[test]
fn generic_impls_respect_borrowed_receivers_and_defaults() {
    agrees(
        r#"
        struct W<T> { value: T }
        trait Doubler {
            fn base(self: &Self) -> i64 ! {panic};
            fn doubled(self: &Self) -> i64 ! {panic} { 5 * 2 }
        }
        impl<T> Doubler for W<T> {
            fn base(self: &Self) -> i64 ! {panic} { 5 }
        }
        fn main() -> i64 ! {io, panic} {
            let value = W { value: true };
            print_i64(value.doubled());
            0
        }"#,
        0,
        "10\n",
    );
    rejects(
        r#"
        struct W<T> { value: T }
        trait Doubler { fn base(self: &Self) -> i64 ! {panic}; }
        impl<T> Doubler for W<T> {
            fn base(self: Self) -> i64 ! {panic} { 5 }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "does not match the trait signature",
    );
}

#[test]
fn generic_methods_and_linear_results_compose_with_generic_impls() {
    agrees(
        r#"
        struct W<T> { value: T }
        trait Pairing<T> { fn pair<U>(self: Self, value: U) -> (T, U) ! {}; }
        impl<T> Pairing<T> for W<T> {
            fn pair<U>(self: Self, value: U) -> (T, U) ! {} { (self.value, value) }
        }
        fn main() -> i64 ! {io, panic} {
            let pair = W { value: 5 }.pair(true);
            print_i64(pair.0);
            0
        }"#,
        0,
        "5\n",
    );
    let stats = agrees(
        r#"
        struct W<T> { value: T }
        trait Make { fn make(self: Self) -> Box<i64> @[1] ! {alloc, panic}; }
        impl<T> Make for W<T> {
            fn make(self: Self) -> Box<i64> @[1] ! {alloc, panic} { Box.new(self.value) }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let owner = W { value: 3 }.make();
            print_i64(Box.take(owner));
            0
        }"#,
        0,
        "3\n",
    );
    assert_eq!(stats.allocations, 1, "{}", stats.allocations);
}

#[test]
fn effect_exclusions_are_enforced_on_generic_impl_methods() {
    agrees(
        r#"
        struct W<T> { value: T }
        trait Apply {
            fn apply<e: Effects - alloc>(self: Self, f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e};
        }
        impl<T> Apply for W<T> {
            fn apply<e: Effects - alloc>(self: Self, f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                f(x)
            }
        }
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn main() -> i64 ! {io, panic} {
            print_i64(W { value: true }.apply(inc, 4));
            0
        }"#,
        0,
        "5\n",
    );
    rejects(
        r#"
        struct W<T> { value: T }
        trait Apply {
            fn apply<e: Effects - alloc>(self: Self, f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e};
        }
        impl<T> Apply for W<T> {
            fn apply<e: Effects - alloc>(self: Self, f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                f(x)
            }
        }
        fn make(name: String) -> i64 ! {alloc, panic} { name.len() }
        fn main() -> i64 ! {io, alloc, panic} {
            print_i64(W { value: true }.apply(make, 4));
            0
        }"#,
        "excluded by '<e: Effects - alloc>'",
    );
}

#[test]
fn specialization_selects_the_unique_most_specific_impl() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct Pair<T, U> { first: T, second: U }
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<T> Tag for T { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        impl Tag for Point { fn tag(self: Self) -> i64 ! {panic} { 2 } }
        impl<T, U> Tag for Pair<T, U> { fn tag(self: Self) -> i64 ! {panic} { 3 } }
        impl<T> Tag for Pair<T, i64> { fn tag(self: Self) -> i64 ! {panic} { 4 } }
        fn main() -> i64 ! {io, panic} {
            print_i64(Point { x: 1 }.tag());
            print_i64(Pair { first: true, second: 2 }.tag());
            print_i64(Pair { first: 1, second: true }.tag());
            0
        }"#,
        0,
        "2\n4\n3\n",
    );
}

#[test]
fn coherence_rejects_duplicate_and_incomparable_overlaps() {
    rejects(
        r#"
        struct W<T> { value: T }
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<T> Tag for W<T> { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        impl<U> Tag for W<U> { fn tag(self: Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {} { 0 }"#,
        "duplicate implementation",
    );
    rejects(
        r#"
        struct Pair<T, U> { first: T, second: U }
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<T> Tag for Pair<T, i64> { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        impl<T> Tag for Pair<i64, T> { fn tag(self: Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {} { 0 }"#,
        "incomparable",
    );
}

#[test]
fn associated_type_defaults_are_inherited_and_can_chain() {
    agrees(
        r#"
        struct Point { x: i64 }
        trait Scaled {
            type Base = i64;
            type Out = Self.Base;
            fn scaled(self: Self) -> Self.Out ! {panic};
        }
        impl Scaled for Point {
            type Base = i64;
            fn scaled(self: Self) -> i64 ! {panic} { self.x * 3 }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 4 };
            print_i64(point.scaled());
            0
        }"#,
        0,
        "12\n",
    );
}

#[test]
fn associated_type_defaults_substitute_trait_arguments_and_may_be_overridden() {
    agrees(
        r#"
        struct Point { x: i64 }
        trait Convert<T> {
            type Out = T;
            fn render(self: Self) -> Self.Out ! {panic};
        }
        impl Convert<i64> for Point {
            fn render(self: Self) -> i64 ! {panic} { self.x }
        }
        trait Flagged {
            type Out = i64;
            fn flagged(self: Self) -> Self.Out ! {panic};
        }
        impl Flagged for Point {
            type Out = Bool;
            fn flagged(self: Self) -> Bool ! {panic} { self.x == 0 }
        }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 9 };
            print_i64(point.Convert::<i64>.render());
            if point.flagged() { print_i64(1); } else { print_i64(0); }
            0
        }"#,
        0,
        "9\n0\n",
    );
}

#[test]
fn associated_type_defaults_agree_across_trait_object_members() {
    agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Show {
            type Out = i64;
            fn show(self: Self) -> Self.Out ! {panic};
        }
        impl Show for A { fn show(self: Self) -> i64 ! {panic} { self.x } }
        impl Show for B { fn show(self: Self) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {io, panic} {
            let object: dyn Show = B { y: 7 };
            print_i64(object.show());
            0
        }"#,
        0,
        "7\n",
    );
}

#[test]
fn associated_type_default_cycles_and_invalid_defaults_are_rejected() {
    rejects(
        r#"
        struct Point { x: i64 }
        trait Bad { type A = Self.B; type B = Self.A; fn value(self: Self) -> Self.A ! {panic}; }
        impl Bad for Point { fn value(self: Self) -> i64 ! {panic} { self.x } }
        fn main() -> i64 ! {} { 0 }"#,
        "associated type default cycle",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Bad { type A = Self.Missing; fn value(self: Self) -> Self.A ! {panic}; }
        impl Bad for Point { fn value(self: Self) -> i64 ! {panic} { self.x } }
        fn main() -> i64 ! {} { 0 }"#,
        "not a declared associated type",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Bad { type A = Self; }
        impl Bad for Point { }
        fn main() -> i64 ! {} { 0 }"#,
        "may not mention bare 'Self'",
    );
}

#[test]
fn impl_headers_may_carry_natural_and_grade_parameters() {
    agrees(
        r#"
        struct Buffer<N: Nat> { data: [i64; N] }
        trait First { fn first(self: Self) -> i64 ! {panic}; }
        impl<N: Nat> First for Buffer<N> {
            fn first(self: Self) -> i64 ! {panic} { self.data[0] }
        }
        struct Point { x: i64 }
        trait Weighted<G: Grade> { fn weighted(self: Self) -> i64 ! {panic}; }
        impl<G: Grade> Weighted<G> for Point {
            fn weighted(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {io, panic} {
            let buffer: Buffer<3> = Buffer { data: [7, 8, 9] };
            print_i64(buffer.first());
            let point = Point { x: 5 };
            print_i64(point.Weighted::<1>.weighted());
            print_i64(point.Weighted::<2>.weighted());
            0
        }"#,
        0,
        "7\n5\n5\n",
    );
}

#[test]
fn impl_headers_solve_natural_trait_arguments_from_the_receiver() {
    agrees(
        r#"
        struct Buffer<N: Nat> { data: [i64; N] }
        trait At<N: Nat> { fn value(self: Self) -> i64 ! {panic}; }
        impl<N: Nat> At<N> for Buffer<N> {
            fn value(self: Self) -> i64 ! {panic} { self.data[0] }
        }
        fn main() -> i64 ! {io, panic} {
            let buffer: Buffer<2> = Buffer { data: [11, 12] };
            print_i64(buffer.At::<2>.value());
            0
        }"#,
        0,
        "11\n",
    );
}

#[test]
fn impl_parameter_categories_are_validated() {
    rejects(
        r#"
        struct Buffer<N: Nat> { data: [i64; N] }
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<N: Nat, M: Nat> Tag for Buffer<N> { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        fn main() -> i64 ! {} { 0 }"#,
        "impl parameter 'M' is unconstrained",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<N> Tag for Point { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        fn main() -> i64 ! {} { 0 }"#,
        "unconstrained",
    );
}

#[test]
fn mutable_dynamic_dispatch_writes_back_to_the_object_local() {
    agrees(
        r#"
        struct Counter { value: i64 }
        struct Offset { value: i64 }
        trait Bump {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
            fn current(self: &Self) -> i64 ! {panic};
        }
        impl Bump for Counter {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        impl Bump for Offset {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by * 10; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        fn make() -> dyn Bump ! {panic} { Counter { value: 10 } }
        fn main() -> i64 ! {io, panic} {
            let mut object: dyn Bump = Counter { value: 1 };
            object.bump(2);
            print_i64(object.current());
            object.bump(3);
            print_i64(object.current());
            let mut other: dyn Bump = Offset { value: 4 };
            other.bump(2);
            print_i64(other.current());
            make().bump(7);
            0
        }"#,
        0,
        "3\n6\n24\n",
    );
}

#[test]
fn stored_shared_borrowed_trait_objects_dispatch_read_only() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct Flag { on: Bool }
        trait Describe { fn describe(self: &Self) -> i64 ! {panic}; }
        impl Describe for Point { fn describe(self: &Self) -> i64 ! {panic} { self.x } }
        impl Describe for Flag { fn describe(self: &Self) -> i64 ! {panic} { if self.on { 1 } else { 0 } } }
        fn read(object: &dyn Describe) -> i64 ! {panic} { object.describe() }
        fn main() -> i64 ! {io, panic} {
            let point: dyn Describe = Point { x: 7 };
            let reference: &dyn Describe = &point;
            print_i64(reference.describe());
            print_i64(read(&point));
            print_i64(point.describe());
            let flag: dyn Describe = Flag { on: true };
            print_i64(read(&flag));
            0
        }"#,
        0,
        "7
7
7
1
",
    );
}

#[test]
fn stored_mutable_borrowed_trait_objects_write_through_the_reference() {
    agrees(
        r#"
        struct Counter { value: i64 }
        struct Offset { value: i64 }
        trait Bump {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
            fn current(self: &Self) -> i64 ! {panic};
        }
        impl Bump for Counter {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        impl Bump for Offset {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by * 10; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        fn bump_twice(object: &mut dyn Bump) -> Unit ! {panic} {
            object.bump(1);
            object.bump(2);
        }
        fn main() -> i64 ! {io, panic} {
            let mut object: dyn Bump = Counter { value: 1 };
            let reference: &mut dyn Bump = &mut object;
            reference.bump(2);
            print_i64(reference.current());
            reference.bump(3);
            print_i64(object.current());
            bump_twice(&mut object);
            print_i64(object.current());
            let mut other: dyn Bump = Offset { value: 4 };
            let borrowed: &mut dyn Bump = &mut other;
            borrowed.bump(2);
            print_i64(other.current());
            0
        }"#,
        0,
        "3
6
9
24
",
    );
}

#[test]
fn borrowed_trait_object_boundaries_are_explicit() {
    rejects(
        r#"
        struct Text { name: String }
        struct Other { name: String }
        trait Consume { fn consume(self: Self) -> i64 ! {panic}; }
        impl Consume for Text { fn consume(self: Self) -> i64 ! {panic} { 1 } }
        impl Consume for Other { fn consume(self: Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Consume = Text { name: "x" };
            let reference: &dyn Consume = &object;
            print_i64(reference.consume());
            0
        }"#,
        "must have copyable members",
    );
    rejects(
        r#"
        struct Counter { value: i64 }
        struct Other { value: i64 }
        trait Bump { fn bump(self: &mut Self) -> Unit ! {panic}; }
        impl Bump for Counter { fn bump(self: &mut Self) -> Unit ! {panic} { self.value = self.value + 1; } }
        impl Bump for Other { fn bump(self: &mut Self) -> Unit ! {panic} { self.value = self.value + 2; } }
        fn main() -> i64 ! {panic} {
            let object: dyn Bump = Counter { value: 1 };
            let reference: &dyn Bump = &object;
            reference.bump();
            0
        }"#,
        "exclusive dynamic method through a shared",
    );
    rejects(
        r#"
        struct Counter { value: i64 }
        struct Other { value: i64 }
        trait Consume { fn consume(self: Self) -> i64 ! {panic}; }
        impl Consume for Counter { fn consume(self: Self) -> i64 ! {panic} { self.value } }
        impl Consume for Other { fn consume(self: Self) -> i64 ! {panic} { self.value } }
        fn main() -> i64 ! {panic} {
            let object: dyn Consume = Counter { value: 1 };
            let reference: &dyn Consume = &object;
            reference.consume()
        }"#,
        "owning dynamic method through a borrowed",
    );
}

#[test]
fn mutable_object_dispatch_preserves_owning_member_cleanup() {
    let stats = agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct Blob { name: String, count: i64 }
        trait Bump {
            fn bump(self: &mut Self) -> i64 ! {panic};
            fn make(self: &mut Self) -> Box<i64> ! {alloc, panic};
        }
        impl Bump for Text {
            fn bump(self: &mut Self) -> i64 ! {panic} { self.count = self.count + 1; self.count }
            fn make(self: &mut Self) -> Box<i64> ! {alloc, panic} { Box.new(self.count) }
        }
        impl Bump for Blob {
            fn bump(self: &mut Self) -> i64 ! {panic} { self.count = self.count + 2; self.count }
            fn make(self: &mut Self) -> Box<i64> ! {alloc, panic} { Box.new(self.count) }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut text: dyn Bump = Text { name: "x", count: 1 };
            print_i64(text.bump());
            print_i64(Box.take(text.make()));
            let mut blob: dyn Bump = Blob { name: "y", count: 3 };
            print_i64(blob.bump());
            0
        }"#,
        0,
        "2
2
5
",
    );
    assert_eq!(stats.allocations, 3, "{}", stats.allocations);
}

#[test]
fn associated_constants_may_be_tuples_and_inline_arrays() {
    agrees(
        r#"
        struct Marker { tag: i64 }
        trait Table {
            const PAIR: (i64, Bool);
            const ROWS: [i64; 3] = [1, 2, 3];
            const ALIAS: [i64; 3] = Self.ROWS;
            fn first(self: Self) -> i64 ! {panic} { let rows = Self.ALIAS; rows[0] }
            fn flag(self: Self) -> Bool ! {panic} { let pair = Self.PAIR; pair.1 }
        }
        impl Table for Marker { const PAIR: (i64, Bool) = (9, true); }
        fn main() -> i64 ! {io, panic} {
            let marker = Marker { tag: 0 };
            print_i64(Marker.ROWS[1]);
            print_i64(marker.first());
            if marker.flag() { print_i64(1); } else { print_i64(0); }
            0
        }"#,
        0,
        "2
1
1
",
    );
    rejects(
        r#"
        struct Marker { }
        trait Bad { const VALUE: (i64, String); }
        impl Bad for Marker { const VALUE: (i64, String) = (1, "x"); }
        fn main() -> i64 ! {} { 0 }"#,
        "compile-time scalar, tuple, or inline-array",
    );
    rejects(
        r#"
        struct Marker { }
        trait Bad { const ROWS: [i64; 2] = [1, 2, 3]; }
        impl Bad for Marker { }
        fn main() -> i64 ! {} { 0 }"#,
        "array associated constant has 3 element(s), but its type needs 2",
    );
}

#[test]
fn closed_world_trait_objects_dispatch_and_clean_up_ownership() {
    let stats = agrees(
        r#"
        struct Text { name: String }
        struct Num { value: i64 }
        trait Size { fn size(self: Self) -> i64 ! {panic}; }
        impl Size for Text { fn size(self: Self) -> i64 ! {panic} { let Text { name } = self; name.len() } }
        impl Size for Num { fn size(self: Self) -> i64 ! {panic} { self.value } }
        fn measure(object: dyn Size) -> i64 ! {panic} { object.size() }
        fn main() -> i64 ! {io, panic, alloc} {
            print_i64(measure(Text { name: "hello" }));
            print_i64(measure(Num { value: 8 }));
            0
        }"#,
        0,
        "5\n8\n",
    );
    // Both accepted backends release the one String allocation exactly once.
    assert_eq!(stats.allocations, 1, "{}", stats.allocations);
}

#[test]
fn shared_receiver_objects_are_copyable_and_reusable() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct Flag { on: Bool }
        trait Describe { fn describe(self: &Self) -> i64 ! {panic}; }
        impl Describe for Point { fn describe(self: &Self) -> i64 ! {panic} { self.x } }
        impl Describe for Flag { fn describe(self: &Self) -> i64 ! {panic} { if self.on { 1 } else { 0 } } }
        fn main() -> i64 ! {io, panic} {
            let object: dyn Describe = Point { x: 4 };
            print_i64(object.describe());
            print_i64(object.describe());
            0
        }"#,
        0,
        "4\n4\n",
    );
}

#[test]
fn trait_objects_with_arguments_and_effects_dispatch_by_alternative() {
    agrees(
        r#"
        struct P { x: i64 }
        struct Q { y: i64 }
        trait Combine { fn combine(self: Self, other: i64) -> i64 ! {panic}; }
        impl Combine for P { fn combine(self: Self, other: i64) -> i64 ! {panic} { self.x + other } }
        impl Combine for Q { fn combine(self: Self, other: i64) -> i64 ! {panic} { self.y * other } }
        fn apply(object: dyn Combine, value: i64) -> i64 ! {panic} { object.combine(value) }
        fn main() -> i64 ! {io, panic} {
            print_i64(apply(P { x: 3 }, 4));
            print_i64(apply(Q { y: 3 }, 4));
            0
        }"#,
        0,
        "7\n12\n",
    );
}

#[test]
fn dynamic_methods_may_return_affine_owning_values() {
    let stats = agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Make { fn make(self: Self) -> Box<i64> ! {alloc, panic}; }
        impl Make for A { fn make(self: Self) -> Box<i64> ! {alloc, panic} { Box.new(self.x) } }
        impl Make for B { fn make(self: Self) -> Box<i64> ! {alloc, panic} { Box.new(self.y) } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Make = A { x: 4 };
            print_i64(Box.take(object.make()));
            0
        }"#,
        0,
        "4\n",
    );
    assert_eq!(stats.allocations, 1, "{}", stats.allocations);
}

#[test]
fn object_methods_may_project_a_shared_associated_type() {
    agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }
        impl Show for A { type Out = i64; fn show(self: Self) -> i64 ! {panic} { self.x } }
        impl Show for B { type Out = i64; fn show(self: Self) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {io, panic} {
            let a: dyn Show = A { x: 5 };
            let b: dyn Show = B { y: 6 };
            print_i64(a.show());
            print_i64(b.show());
            0
        }"#,
        0,
        "5\n6\n",
    );
}

#[test]
fn object_safety_rejections_are_explicit() {
    rejects(
        r#"
        struct Text { name: String }
        struct Point { x: i64 }
        trait Describe { fn describe(self: &Self) -> i64 ! {panic}; }
        impl Describe for Text { fn describe(self: &Self) -> i64 ! {panic} { 1 } }
        impl Describe for Point { fn describe(self: &Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {panic} {
            let object: dyn Describe = Point { x: 1 };
            0
        }"#,
        "owns storage",
    );
    rejects(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Convert { fn make<U>(self: Self, value: U) -> i64 ! {panic}; }
        impl Convert for A { fn make<U>(self: Self, value: U) -> i64 ! {panic} { self.x } }
        impl Convert for B { fn make<U>(self: Self, value: U) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {panic} {
            let object: dyn Convert = A { x: 1 };
            0
        }"#,
        "generic method",
    );
    rejects(
        r#"
        struct A { x: i64 }
        trait Convert { fn make(self: Self) -> i64 ! {panic}; }
        impl<T> Convert for T { fn make(self: Self) -> i64 ! {panic} { 1 } }
        fn main() -> i64 ! {panic} {
            let object: dyn Convert = A { x: 1 };
            0
        }"#,
        "set of concrete members is open",
    );
    rejects(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Convert { type Out; fn make(self: Self) -> i64 ! {panic}; }
        impl Convert for A { type Out = i64; fn make(self: Self) -> i64 ! {panic} { self.x } }
        impl Convert for B { type Out = Bool; fn make(self: Self) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {panic} {
            let object: dyn Convert = A { x: 1 };
            0
        }"#,
        "disagree on associated type",
    );
    rejects(
        r#"
        trait Empty { fn value(self: Self) -> i64 ! {panic}; }
        fn main() -> i64 ! {panic} {
            let object: dyn Empty = 1;
            0
        }"#,
        "has no concrete impls",
    );
}

#[test]
fn object_traits_sharing_members_require_qualification_for_same_names() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct Flag { on: Bool }
        trait A { fn value(self: Self) -> i64 ! {panic}; }
        trait B { fn value(self: Self) -> i64 ! {panic}; }
        impl A for Point { fn value(self: Self) -> i64 ! {panic} { self.x } }
        impl B for Point { fn value(self: Self) -> i64 ! {panic} { self.x + 1 } }
        impl A for Flag { fn value(self: Self) -> i64 ! {panic} { 2 } }
        impl B for Flag { fn value(self: Self) -> i64 ! {panic} { 3 } }
        fn main() -> i64 ! {io, panic} {
            let object: dyn A = Point { x: 5 };
            print_i64(object.A.value());
            print_i64(object.B.value());
            0
        }"#,
        0,
        "5\n6\n",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        struct Flag { on: Bool }
        trait A { fn value(self: Self) -> i64 ! {panic}; }
        trait B { fn value(self: Self) -> i64 ! {panic}; }
        impl A for Point { fn value(self: Self) -> i64 ! {panic} { self.x } }
        impl B for Point { fn value(self: Self) -> i64 ! {panic} { self.x + 1 } }
        impl A for Flag { fn value(self: Self) -> i64 ! {panic} { 2 } }
        impl B for Flag { fn value(self: Self) -> i64 ! {panic} { 3 } }
        fn main() -> i64 ! {panic} {
            let object: dyn A = Point { x: 5 };
            object.value()
        }"#,
        "disambiguate as 'receiver.Trait.method(...)'",
    );
}

#[test]
fn generic_trait_objects_use_one_finite_specialization() {
    agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Convert<T> { fn render(self: Self) -> T ! {panic}; }
        impl Convert<i64> for A { fn render(self: Self) -> i64 ! {panic} { self.x } }
        impl Convert<i64> for B { fn render(self: Self) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {io, panic} {
            let object: dyn Convert<i64> = A { x: 11 };
            print_i64(object.render());
            0
        }"#,
        0,
        "11\n",
    );
}

#[test]
fn trait_object_result_is_an_ordinary_union_value() {
    agrees(
        r#"
        struct Point { x: i64 }
        struct Flag { on: Bool }
        trait Describe { fn describe(self: Self) -> i64 ! {panic}; }
        impl Describe for Point { fn describe(self: Self) -> i64 ! {panic} { self.x } }
        impl Describe for Flag { fn describe(self: Self) -> i64 ! {panic} { if self.on { 1 } else { 0 } } }
        fn make(flag: Bool) -> dyn Describe ! {panic} {
            if flag { Point { x: 6 } } else { Flag { on: true } }
        }
        fn main() -> i64 ! {io, panic} {
            print_i64(make(true).describe());
            print_i64(make(false).describe());
            0
        }"#,
        0,
        "6\n1\n",
    );
}

#[test]
fn advanced_traits_example_matches_documented_output() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/advanced-traits.kush");
    let loaded = kush::program::load_path(&root).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "12\n7\n9\n");
    if let Some(output) = native_program(&program) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"12\n7\n9\n");
    }
}

fn native_program(program: &kush::executable::Executable) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("trait-advanced-example");
        kush::native::build(program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}
