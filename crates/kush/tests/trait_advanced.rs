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
        "owning dynamic method through a borrowed",
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
    // A `Self`-dependent non-receiver parameter would have a different ABI per
    // member and cannot cross a dynamic boundary.
    rejects(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Convert { fn make(self: Self, value: [Self; 2]) -> i64 ! {panic}; }
        impl Convert for A { fn make(self: Self, value: [Self; 2]) -> i64 ! {panic} { self.x } }
        impl Convert for B { fn make(self: Self, value: [Self; 2]) -> i64 ! {panic} { self.y } }
        fn main() -> i64 ! {panic} {
            let object: dyn Convert = A { x: 1 };
            0
        }"#,
        "mentions 'Self' in a non-receiver parameter",
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

#[test]
fn mutable_dynamic_receivers_require_mutable_places_and_exclude_argument_aliases() {
    let definitions = r#"
        struct Counter { value: i64 }
        struct Other { value: i64 }
        trait Bump {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
            fn current(self: &Self) -> i64 ! {panic};
        }
        impl Bump for Counter {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        impl Bump for Other {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
    "#;
    rejects(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{panic}} {{
                let object: dyn Bump = Counter {{value: 1}};
                object.bump(2); object.current()
            }}"
        ),
        "mutable object binding",
    );
    for later in [
        "object.bump(10); 2",
        "object = Other {value: 10}; 2",
        "object.current()",
    ] {
        rejects(
            &format!(
                "{definitions}
                fn main() -> i64 ! {{panic}} {{
                    let mut object: dyn Bump = Counter {{value: 1}};
                    object.bump({{{later}}}); object.current()
                }}"
            ),
            "while",
        );
    }
    rejects(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{panic}} {{
                let mut object: dyn Bump = Counter {{value: 1}};
                let reference: &mut dyn Bump = &mut object;
                reference.bump({{reference.bump(10); 2}});
                object.current()
            }}"
        ),
        "live",
    );
    agrees(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{panic}} {{
                let mut object: dyn Bump = Counter {{value: 1}};
                object.bump({{let amount = 2; amount}});
                let reference: &mut dyn Bump = &mut object;
                reference.bump(3);
                object.current()
            }}"
        ),
        6,
        "",
    );
}

#[test]
fn shared_dynamic_receivers_remain_borrowed_through_later_arguments() {
    let definitions = r#"
        struct Counter { value: i64 }
        struct Other { value: i64 }
        trait Read { fn inspect(self: &Self, extra: i64) -> i64 ! {panic}; }
        impl Read for Counter { fn inspect(self: &Self, extra: i64) -> i64 ! {panic} { self.value + extra } }
        impl Read for Other { fn inspect(self: &Self, extra: i64) -> i64 ! {panic} { self.value + extra } }
    "#;
    for receiver in ["object", "reference"] {
        rejects(
            &format!(
                "{definitions}
                fn main() -> i64 ! {{panic}} {{
                    let mut object: dyn Read = Counter {{value: 1}};
                    let reference: &dyn Read = &object;
                    {receiver}.inspect({{object = Other {{value: 10}}; 0}})
                }}"
            ),
            "borrow",
        );
    }
    agrees(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{panic}} {{
                let object: dyn Read = Counter {{value: 1}};
                object.inspect(object.inspect(0))
            }}"
        ),
        2,
        "",
    );
}

#[test]
fn mutable_dynamic_dispatch_preserves_erased_argument_effects_and_writeback() {
    agrees(
        r#"
        struct Counter { value: i64 }
        struct Other { value: i64 }
        trait Bump {
            fn bump(self: &mut Self, ignored: i64 @[0], by: i64) -> i64 @[0] ! {io, panic};
            fn current(self: &Self) -> i64 ! {panic};
        }
        impl Bump for Counter {
            fn bump(self: &mut Self, ignored: i64 @[0], by: i64) -> i64 @[0] ! {io, panic} {
                self.value = self.value + by; print_i64(3); self.value
            }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        impl Bump for Other {
            fn bump(self: &mut Self, ignored: i64 @[0], by: i64) -> i64 @[0] ! {io, panic} {
                self.value = self.value + by; print_i64(3); self.value
            }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        fn main() -> i64 ! {io, panic} {
            let mut object: dyn Bump = Counter {value: 40};
            object.bump({print_i64(1); 99}, {print_i64(2); 2});
            object.current()
        }"#,
        42,
        "1\n2\n3\n",
    );
}

#[test]
fn projected_method_receivers_cannot_duplicate_owners_and_keep_mutations() {
    let definitions = r#"
        struct Text { name: String, count: i64 }
        struct Other { count: i64 }
        struct Wrap<T> { value: T }
        trait Bump { fn bump(self: &mut Self, by: i64) -> i64 ! {panic}; }
        impl Bump for Text { fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count } }
        impl Bump for Other { fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count } }
        trait Eat { fn eat(self: Self) -> i64 ! {panic}; }
        impl Eat for Text { fn eat(self: Self) -> i64 ! {panic} { self.count } }
        impl Eat for Other { fn eat(self: Self) -> i64 ! {panic} { self.count } }
        impl Text { fn consume(self: Text) -> i64 ! {panic} { self.count } }
    "#;
    // Consuming dispatch on a projected object field consumes the aggregate
    // like a destructuring; the static owned-field case below stays rejected.
    agrees(
        &format!(
            "{definitions} fn main() -> i64 ! {{alloc, panic}} {{
                let pair: (dyn Eat, i64) = (Text {{name: \"x\", count: 6}}, 9); pair.0.eat()
            }}"
        ),
        6,
        "",
    );
    // Mutable dispatch on a projected object field borrows the field in place;
    // the write stays in the aggregate.
    for body in [
        "let mut pair: (dyn Bump, i64) = (Text {name: \"x\", count: 1}, 9); pair.0.bump(5); pair.0.bump(0)",
        "let mut wrap: Wrap<dyn Bump> = Wrap {value: Text {name: \"x\", count: 1}}; wrap.value.bump(5); wrap.value.bump(0)",
    ] {
        agrees(
            &format!("{definitions} fn main() -> i64 ! {{alloc, panic}} {{{body}}}"),
            6,
            "",
        );
    }
    rejects(
        &format!(
            "{definitions} fn main() -> i64 ! {{alloc, panic}} {{
                let pair = (Text {{name: \"x\", count: 1}}, 9); pair.0.consume()
            }}"
        ),
        "owned field",
    );
    rejects(
        &format!(
            "{definitions} fn main() -> i64 ! {{alloc, panic}} {{
        let pair: (dyn Bump, i64) = (Other {{count: 1}}, 9); pair.0.bump(5)
    }}"
        ),
        "needs a mutable owner",
    );
}

#[test]
fn projected_dynamic_mutation_needs_a_mutable_owner_and_destructuring_still_works() {
    rejects(
        r#"struct Counter { count: i64 }
        struct Other { count: i64 }
        trait Bump { fn bump(self: &mut Self) -> Unit ! {panic}; }
        impl Bump for Counter { fn bump(self: &mut Self) -> Unit ! {panic} { self.count = self.count + 1; } }
        impl Bump for Other { fn bump(self: &mut Self) -> Unit ! {panic} { self.count = self.count + 1; } }
        fn main() -> i64 ! {panic} {
            let pair: (dyn Bump, i64) = (Counter {count: 1}, 9);
            pair.0.bump(); 0
        }"#,
        "needs a mutable owner",
    );
    agrees(
        r#"struct Text { name: String, count: i64 }
        struct Other { count: i64 }
        struct Wrap<T> { value: T }
        trait Bump { fn bump(self: &mut Self, by: i64) -> i64 ! {panic}; }
        impl Bump for Text { fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count } }
        impl Bump for Other { fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count } }
        fn main() -> i64 ! {alloc, panic} {
            let wrapper: Wrap<dyn Bump> = Wrap {value: Text {name: "x", count: 37}};
            let Wrap {value} = wrapper;
            let mut object = value;
            object.bump(5)
        }"#,
        42,
        "",
    );
}

#[test]
fn open_generic_member_sets_use_a_checked_runtime_vtable() {
    let stats = agrees(
        r#"
        trait Describe {
            fn describe(self: Self) -> i64 ! {panic};
        }
        struct Point { x: i64 }
        struct Wrapper<T> { value: T }
        impl Describe for Point {
            fn describe(self: Self) -> i64 ! {panic} { self.x }
        }
        impl<T: Describe> Describe for Wrapper<T> {
            fn describe(self: Self) -> i64 ! {panic} { self.value.describe() + 1 }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let once: dyn Describe = Point { x: 4 };
            let nested: dyn Describe = Wrapper { value: Wrapper { value: Point { x: 10 } } };
            print_i64(once.describe());
            print_i64(nested.describe());
            0
        }"#,
        0,
        "4\n12\n",
    );
    assert_eq!(stats.allocations, 2, "{}", stats.allocations);
}

#[test]
fn nominal_fields_may_spell_dyn_directly() {
    let stats = agrees(
        r#"
        trait Describe {
            fn describe(self: Self) -> i64 ! {panic};
        }
        struct Point { x: i64 }
        struct Holder { object: dyn Describe }
        struct Boxed { object: Box<dyn Describe> }
        impl Describe for Point {
            fn describe(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let holder = Holder { object: Point { x: 7 } };
            let Holder { object } = holder;
            print_i64(object.describe());
            let boxed = Boxed { object: Box.new(Point { x: 8 }) };
            let Boxed { object } = boxed;
            print_i64(Box.take(object).describe());
            0
        }"#,
        0,
        "7\n8\n",
    );
    assert_eq!(stats.allocations, 3, "{}", stats.allocations);
}

#[test]
fn borrowed_objects_keep_owning_members_in_place() {
    let stats = agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct Plain { amount: i64 }
        trait Counted {
            fn value(self: &Self) -> i64 ! {panic};
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
        }
        impl Counted for Text {
            fn value(self: &Self) -> i64 ! {panic} { self.count }
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.count = self.count + by }
        }
        impl Counted for Plain {
            fn value(self: &Self) -> i64 ! {panic} { self.amount }
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.amount = self.amount + by }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Counted = Text { name: "x", count: 5 };
            let shared: &dyn Counted = &object;
            print_i64(shared.value());
            print_i64(object.value());
            let mut plain: dyn Counted = Plain { amount: 3 };
            let exclusive: &mut dyn Counted = &mut plain;
            exclusive.bump(4);
            print_i64(plain.value());
            0
        }"#,
        0,
        "5\n5\n7\n",
    );
    assert_eq!(stats.allocations, 1, "{}", stats.allocations);
}

#[test]
fn object_methods_accept_lifetime_parameterized_borrows() {
    agrees(
        r#"
        trait Feed {
            fn feed<'a>(self: &mut Self, input: &'a [i64]) -> i64 ! {panic};
        }
        struct Counter { sum: i64 }
        struct Other { sum: i64 }
        impl Feed for Counter {
            fn feed<'a>(self: &mut Self, input: &'a [i64]) -> i64 ! {panic} {
                self.sum = self.sum + input[0];
                self.sum
            }
        }
        impl Feed for Other {
            fn feed<'a>(self: &mut Self, input: &'a [i64]) -> i64 ! {panic} {
                self.sum = self.sum + input[1];
                self.sum
            }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut counter: dyn Feed = Counter { sum: 1 };
            let values = [10, 20, 30];
            print_i64(counter.feed(&values[..]));
            let mut other: dyn Feed = Other { sum: 5 };
            let reference: &mut dyn Feed = &mut other;
            print_i64(reference.feed(&values[..]));
            0
        }"#,
        0,
        "11\n25\n",
    );
}

#[test]
fn generic_impl_non_type_parameters_substitute_for_object_members() {
    agrees(
        r#"
        trait First {
            fn first(self: Self) -> i64 ! {panic};
        }
        struct Buffer<N: Nat> { data: [i64; N] }
        struct Single { n: i64 }
        impl<N: Nat> First for Buffer<N> {
            fn first(self: Self) -> i64 ! {panic} { self.data[0] }
        }
        impl First for Single {
            fn first(self: Self) -> i64 ! {panic} { self.n }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let buffer: dyn First = Buffer { data: [7, 8, 9] };
            print_i64(buffer.first());
            let single: dyn First = Single { n: 4 };
            print_i64(single.first());
            0
        }"#,
        0,
        "7\n4\n",
    );
}

#[test]
fn open_objects_may_carry_linear_members_and_require_consumption() {
    let stats = agrees(
        r#"
        #[linear]
        enum Ticket { Live }
        struct Wrapper<T> { value: T }
        trait Consume {
            fn consume(self: Self) -> i64 ! {panic};
        }
        impl Consume for Ticket {
            fn consume(self: Self) -> i64 ! {panic} { match self { Ticket.Live => 9 } }
        }
        impl<T: Consume> Consume for Wrapper<T> {
            fn consume(self: Self) -> i64 ! {panic} {
                let Wrapper { value } = self;
                value.consume() + 1
            }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Consume = Ticket.Live;
            print_i64(object.consume());
            let nested: dyn Consume = Wrapper { value: Ticket.Live };
            print_i64(nested.consume());
            0
        }"#,
        0,
        "9\n10\n",
    );
    assert_eq!(stats.allocations, 2, "{}", stats.allocations);

    rejects(
        r#"
        #[linear]
        enum Ticket { Live }
        struct Wrapper<T> { value: T }
        trait Consume { fn consume(self: Self) -> i64 ! {panic}; }
        impl Consume for Ticket { fn consume(self: Self) -> i64 ! {panic} { match self { Ticket.Live => 9 } } }
        impl<T: Consume> Consume for Wrapper<T> {
            fn consume(self: Self) -> i64 ! {panic} {
                let Wrapper { value } = self;
                value.consume() + 1
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            let object: dyn Consume = Ticket.Live;
            0
        }"#,
        "linear value is not consumed",
    );
}

#[test]
fn open_object_membership_requires_a_concrete_impl() {
    rejects(
        r#"
        struct A { x: i64 }
        trait Show {
            fn show(self: Self) -> i64 ! {panic};
        }
        impl Show for A { fn show(self: Self) -> i64 ! {panic} { self.x } }
        impl<T> Show for Box<T> { fn show(self: Self) -> i64 ! {panic} { 0 } }
        fn main() -> i64 ! {alloc, panic} {
            let object: dyn Show = 7;
            0
        }"#,
        "does not implement trait",
    );
}

#[test]
fn open_objects_dispatch_borrowed_owning_members_in_place() {
    agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct Wrap<T> { value: T }
        trait Counted {
            fn value(self: &Self) -> i64 ! {panic};
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
        }
        impl Counted for Text {
            fn value(self: &Self) -> i64 ! {panic} { self.count }
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.count = self.count + by }
        }
        impl<T> Counted for Wrap<T> {
            fn value(self: &Self) -> i64 ! {panic} { 7 }
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} {  }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Counted = Wrap { value: Text { name: "x", count: 1 } };
            let shared: &dyn Counted = &object;
            print_i64(shared.value());
            let mut other: dyn Counted = Text { name: "y", count: 3 };
            let exclusive: &mut dyn Counted = &mut other;
            exclusive.bump(4);
            print_i64(other.value());
            0
        }"#,
        0,
        "7\n7\n",
    );
}

#[test]
fn object_methods_may_return_a_view_of_a_caller_argument() {
    agrees(
        r#"
        trait Pick {
            fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct B { tag: i64 }
        impl Pick for A { fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl Pick for B { fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Pick = A { tag: 1 };
            let values = [5, 6, 7];
            let got = object.pick(&values[..]);
            print_i64(got[1]);
            0
        }"#,
        0,
        "6\n",
    );
}

#[test]
fn open_object_methods_may_return_a_view_of_a_caller_argument() {
    agrees(
        r#"
        trait Pick {
            fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct W<T> { value: T }
        impl Pick for A { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl<T> Pick for W<T> { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Pick = W { value: A { tag: 1 } };
            let values = [5, 6, 7];
            let shared: &dyn Pick = &object;
            print_i64(shared.pick(&values[..])[2]);
            0
        }"#,
        0,
        "7\n",
    );
}

#[test]
fn borrowed_object_results_through_temporary_and_owned_receivers() {
    agrees(
        r#"
        trait Pick {
            fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct B { tag: i64 }
        impl Pick for A { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl Pick for B { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn make() -> dyn Pick ! {panic} { A { tag: 1 } }
        fn main() -> i64 ! {alloc, panic} {
            let values = [1, 2];
            make().pick(&values[..])[1]
        }"#,
        2,
        "",
    );
    agrees(
        r#"
        trait Owned {
            fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct B { tag: i64 }
        impl Owned for A { fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl Owned for B { fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Owned = A { tag: 1 };
            let values = [3, 4];
            print_i64(object.grab(&values[..])[1]);
            print_i64(B { tag: 2 }.grab(&values[..])[0]);
            0
        }"#,
        0,
        "4\n3\n",
    );
}

#[test]
fn open_objects_clean_up_fields_and_affine_owning_results() {
    let stats = agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct W<T> { value: T }
        trait Make {
            fn value(self: &Self) -> i64 ! {panic};
            fn make(self: Self) -> Box<i64> ! {alloc, panic};
        }
        struct Holder { object: dyn Make }
        impl Make for Text {
            fn value(self: &Self) -> i64 ! {panic} { self.count }
            fn make(self: Self) -> Box<i64> ! {alloc, panic} { Box.new(self.count) }
        }
        impl<T> Make for W<T> {
            fn value(self: &Self) -> i64 ! {panic} { 7 }
            fn make(self: Self) -> Box<i64> ! {alloc, panic} { Box.new(9) }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let holder = Holder { object: Text { name: "x", count: 4 } };
            let Holder { object } = holder;
            print_i64(object.value());
            print_i64(Box.take(object.make()));
            let dropped = Holder { object: Text { name: "y", count: 5 } };
            let Holder { object: unused } = dropped;
            print_i64(unused.value());
            0
        }"#,
        0,
        "4\n4\n5\n",
    );
    assert_eq!(stats.allocations, 5, "{}", stats.allocations);
}

const LINEAR_TICKET: &str = r#"
#[linear]
enum Ticket { Live }
trait Consume { fn consume(self: Self) -> i64 ! {panic}; }
impl Consume for Ticket {
    fn consume(self: Self) -> i64 ! {panic} { match self { Ticket.Live => 9 } }
}
"#;

#[test]
fn linear_dynamic_objects_stay_linear_inside_layouts() {
    let unconsumed = "linear value is not consumed";
    rejects(
        &format!(
            "{LINEAR_TICKET}struct Holder {{ object: dyn Consume }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let holder = Holder {{ object: Ticket.Live }};
                0
            }}"
        ),
        unconsumed,
    );
    rejects(
        &format!(
            "{LINEAR_TICKET}fn main() -> i64 ! {{io, alloc, panic}} {{
                let a: [dyn Consume; 1] = [Ticket.Live];
                0
            }}"
        ),
        unconsumed,
    );
    rejects(
        &format!(
            "{LINEAR_TICKET}struct Holder {{ object: dyn Consume }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let holder = Holder {{ object: Ticket.Live }};
                let mut items: Vec<Holder> = Vec.new();
                items = Vec.push(items, holder);
                items = Vec.clear(items);
                0
            }}"
        ),
        "",
    );
    rejects(
        &format!(
            "{LINEAR_TICKET}fn main() -> i64 ! {{io, alloc, panic}} {{
                let a: DynArray<dyn Consume, 1> = DynArray.new::<dyn Consume, 1>();
                let a = DynArray.push(a, Ticket.Live);
                DynArray.len(&a)
            }}"
        ),
        "DynArray elements cannot",
    );
    agrees(
        &format!(
            "{LINEAR_TICKET}struct Holder {{ object: dyn Consume }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let holder = Holder {{ object: Ticket.Live }};
                match holder {{ Holder {{ object }} => object.consume() }}
            }}"
        ),
        9,
        "",
    );
}

const BUMP_TEXT: &str = r#"
struct Text { name: String, count: i64 }
struct Wrap<T> { value: T }
trait Bump {
    fn bump(self: &mut Self) -> Unit ! {panic};
    fn current(self: &Self) -> i64 ! {panic};
}
impl Bump for Text {
    fn bump(self: &mut Self) -> Unit ! {panic} { self.count = self.count + 1; }
    fn current(self: &Self) -> i64 ! {panic} { self.count }
}
impl<T> Bump for Wrap<T> {
    fn bump(self: &mut Self) -> Unit ! {panic} { }
    fn current(self: &Self) -> i64 ! {panic} { 7 }
}
"#;

#[test]
fn a_live_shared_object_reference_blocks_exclusive_access() {
    rejects(
        &format!(
            "{BUMP_TEXT}fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut object: dyn Bump = Text {{ name: \"aaaaaaaa\", count: 1 }};
                let shared: &dyn Bump = &object;
                let exclusive: &mut dyn Bump = &mut object;
                exclusive.bump();
                print_i64(shared.current());
                0
            }}"
        ),
        "cannot create an exclusive",
    );
    rejects(
        &format!(
            "{BUMP_TEXT}fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut object: dyn Bump = Text {{ name: \"aaaaaaaa\", count: 1 }};
                let shared: &dyn Bump = &object;
                object.bump();
                print_i64(shared.current());
                0
            }}"
        ),
        "cannot create an exclusive",
    );
    agrees(
        &format!(
            "{BUMP_TEXT}fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut object: dyn Bump = Text {{ name: \"aaaaaaaa\", count: 1 }};
                let exclusive: &mut dyn Bump = &mut object;
                exclusive.bump();
                let shared: &dyn Bump = &object;
                print_i64(shared.current());
                0
            }}"
        ),
        0,
        "2\n",
    );
}

#[test]
fn single_impl_objects_dispatch_through_stored_references() {
    agrees(
        r#"struct Counter { value: i64 }
        trait Bump {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic};
            fn current(self: &Self) -> i64 ! {panic};
        }
        impl Bump for Counter {
            fn bump(self: &mut Self, by: i64) -> Unit ! {panic} { self.value = self.value + by; }
            fn current(self: &Self) -> i64 ! {panic} { self.value }
        }
        fn main() -> i64 ! {io, panic} {
            let mut object: dyn Bump = Counter { value: 1 };
            let reference: &mut dyn Bump = &mut object;
            reference.bump(2);
            let shared: &dyn Bump = &object;
            print_i64(shared.current());
            object.current()
        }"#,
        3,
        "3\n",
    );
}

#[test]
fn traits_whose_only_impls_are_generic_are_usable_as_dyn() {
    let stats = agrees(
        r#"
        struct W<T> { value: T }
        struct Boxed<T> { value: Box<T> }
        trait Size { fn size(self: &Self) -> i64 ! {panic}; }
        impl<T> Size for W<T> { fn size(self: &Self) -> i64 ! {panic} { 4 } }
        impl<T> Size for Boxed<T> { fn size(self: &Self) -> i64 ! {panic} { 9 } }
        fn read(object: &dyn Size) -> i64 ! {panic} { object.size() }
        fn main() -> i64 ! {io, alloc, panic} {
            let a: dyn Size = W { value: true };
            let b: dyn Size = Boxed { value: Box.new(3) };
            print_i64(read(&a));
            print_i64(read(&b));
            print_i64(a.size());
            0
        }"#,
        0,
        "4\n9\n4\n",
    );
    // One payload allocation per coercion; the boxed payload is released once.
    assert_eq!(stats.allocations, 3, "{}", stats.allocations);

    rejects(
        r#"
        struct W<T> { value: T }
        trait Size { fn size(self: Self) -> i64 ! {panic}; }
        impl<T> Size for W<T> { fn size(self: Self) -> i64 ! {panic} { 4 } }
        fn main() -> i64 ! {alloc, panic} {
            let object: dyn Size = 7;
            object.size()
        }"#,
        "does not implement trait",
    );
}

#[test]
fn parameter_dependent_generic_associated_projection_is_fixed_by_the_member() {
    let stats = agrees(
        r#"
        struct W<T> { value: T }
        trait Show { type Out; fn show(self: &Self) -> Self.Out ! {panic}; }
        impl<T> Show for W<T> { type Out = T; fn show(self: &Self) -> T ! {panic} { self.value } }
        fn read(object: &dyn Show) -> i64 ! {panic} { object.show() }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Show = W { value: 5 };
            print_i64(read(&object));
            print_i64(object.show());
            0
        }"#,
        0,
        "5\n5\n",
    );
    assert_eq!(stats.allocations, 1, "{}", stats.allocations);

    rejects(
        r#"
        struct W<T> { value: T }
        trait Show { type Out; fn show(self: &Self) -> Self.Out ! {panic}; }
        impl<T> Show for W<T> { type Out = T; fn show(self: &Self) -> T ! {panic} { self.value } }
        fn main() -> i64 ! {alloc, panic} {
            let a: dyn Show = W { value: 5 };
            let b: dyn Show = W { value: true };
            print_i64(a.show());
            0
        }"#,
        "already fixed it as i64",
    );
}

#[test]
fn non_type_trait_arguments_dispatch_through_dyn() {
    agrees(
        r#"
        struct Buffer<N: Nat> { data: [i64; N] }
        trait First<N: Nat> { fn first(self: Self) -> i64 ! {panic}; }
        impl<N: Nat> First<N> for Buffer<N> {
            fn first(self: Self) -> i64 ! {panic} { self.data[0] }
        }
        struct Point { x: i64 }
        trait Weighted<G: Grade> { fn weighted(self: Self) -> i64 ! {panic}; }
        impl<G: Grade> Weighted<G> for Point {
            fn weighted(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let buffer: dyn First<3> = Buffer { data: [7, 8, 9] };
            print_i64(buffer.first());
            let point: dyn Weighted<1> = Point { x: 6 };
            print_i64(point.weighted());
            0
        }"#,
        0,
        "7\n6\n",
    );
}

#[test]
fn temporary_shared_receivers_of_open_objects_bind_to_a_hidden_place() {
    let stats = agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct W<T> { value: T }
        trait Counted { fn value(self: &Self) -> i64 ! {panic}; }
        impl Counted for Text { fn value(self: &Self) -> i64 ! {panic} { self.count } }
        impl<T> Counted for W<T> { fn value(self: &Self) -> i64 ! {panic} { 7 } }
        fn make_text() -> dyn Counted ! {alloc, panic} { Text { name: "x", count: 5 } }
        fn make_wrap() -> dyn Counted ! {alloc, panic} {
            W { value: Text { name: "y", count: 9 } }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            print_i64(make_text().value());
            print_i64(make_wrap().value());
            0
        }"#,
        0,
        "5\n7\n",
    );
    // Two object payloads plus the two member Strings, each released once.
    assert_eq!(stats.allocations, 4, "{}", stats.allocations);
}

#[test]
fn temporary_shared_receivers_return_receiver_tied_views() {
    agrees(
        r#"
        trait Pick {
            fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct W<T> { value: T }
        impl Pick for A { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl<T> Pick for W<T> { fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn make() -> dyn Pick ! {alloc, panic} { W { value: A { tag: 1 } } }
        fn main() -> i64 ! {alloc, alloc, panic} {
            let values = [1, 2];
            make().pick(&values[..])[1]
        }"#,
        2,
        "",
    );
}

#[test]
fn owned_receivers_may_return_views_of_caller_arguments_through_open_objects() {
    agrees(
        r#"
        trait Owned {
            fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct W<T> { value: T }
        impl Owned for A { fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl<T> Owned for W<T> { fn grab<'a>(self: Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn Owned = W { value: A { tag: 1 } };
            let values = [3, 4];
            print_i64(object.grab(&values[..])[1]);
            print_i64(A { tag: 2 }.grab(&values[..])[0]);
            0
        }"#,
        0,
        "4\n3\n",
    );
}

#[test]
fn generic_methods_dispatch_through_dyn_with_per_call_monomorphization() {
    let stats = agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Pairing {
            fn pair<U>(self: Self, value: U) -> (i64, U) ! {};
            fn combine<U>(self: &Self, left: U, right: U) -> U ! {panic};
        }
        impl Pairing for A {
            fn pair<U>(self: Self, value: U) -> (i64, U) ! {} { (self.x, value) }
            fn combine<U>(self: &Self, left: U, right: U) -> U ! {panic} { left }
        }
        impl Pairing for B {
            fn pair<U>(self: Self, value: U) -> (i64, U) ! {} { (self.y, value) }
            fn combine<U>(self: &Self, left: U, right: U) -> U ! {panic} { right }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let a: dyn Pairing = A { x: 5 };
            let pair = a.pair(true);
            print_i64(pair.0);
            if pair.1 { print_i64(1); } else { print_i64(0); }
            let b: dyn Pairing = B { y: 9 };
            print_i64(b.pair::<i64>(7).1);
            let c: dyn Pairing = A { x: 1 };
            print_i64(c.combine(3, 4));
            let d: dyn Pairing = B { y: 2 };
            print_i64(d.combine::<i64>(3, 4));
            0
        }"#,
        0,
        "5\n1\n7\n3\n4\n",
    );
    assert_eq!(stats.allocations, 4, "{}", stats.allocations);
}

#[test]
fn generic_methods_may_take_natural_parameters_through_dyn() {
    agrees(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Sizer {
            fn gather<N: Nat>(self: Self, data: [i64; N]) -> i64 ! {panic};
        }
        impl Sizer for A {
            fn gather<N: Nat>(self: Self, data: [i64; N]) -> i64 ! {panic} { self.x + data[0] }
        }
        impl Sizer for B {
            fn gather<N: Nat>(self: Self, data: [i64; N]) -> i64 ! {panic} { self.y + data[N - 1] }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let a: dyn Sizer = A { x: 5 };
            print_i64(a.gather([1, 2]));
            let b: dyn Sizer = B { y: 9 };
            print_i64(b.gather([3, 4, 10]));
            0
        }"#,
        0,
        "6\n19\n",
    );
}

#[test]
fn generic_method_member_abi_disagreement_is_rejected() {
    rejects(
        r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Pairing { fn pair<U>(self: Self, value: U) -> (i64, U) ! {}; }
        impl Pairing for A {
            fn pair<U>(self: Self, value: U) -> (i64, U) ! {} { (self.x, value) }
        }
        impl Pairing for B {
            fn pair<U>(self: Self, value: U) -> (U, U) ! {} { (value, value) }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let b: dyn Pairing = B { y: 9 };
            print_i64(b.pair(7).0);
            0
        }"#,
        "does not match the trait signature",
    );
}

#[test]
fn shared_dispatch_borrows_owning_projected_receivers_in_place() {
    let stats = agrees(
        r#"
        struct Text { name: String, count: i64 }
        struct Plain { amount: i64 }
        struct W<T> { value: T }
        trait Counted { fn value(self: &Self) -> i64 ! {panic}; }
        impl Counted for Text { fn value(self: &Self) -> i64 ! {panic} { self.count } }
        impl Counted for Plain { fn value(self: &Self) -> i64 ! {panic} { self.amount } }
        impl<T> Counted for W<T> { fn value(self: &Self) -> i64 ! {panic} { 7 } }
        struct Holder { inner: dyn Counted }
        fn read_holder(holder: Holder) -> i64 ! {panic} { holder.inner.value() }
        fn main() -> i64 ! {io, alloc, panic} {
            let pair: (dyn Counted, i64) = (Text { name: "x", count: 5 }, 9);
            print_i64(pair.0.value());
            let holder = Holder { inner: Text { name: "y", count: 6 } };
            print_i64(read_holder(holder));
            let wrap = Holder { inner: W { value: true } };
            print_i64(wrap.inner.value());
            let plain: (dyn Counted, i64) = (Plain { amount: 11 }, 2);
            print_i64(plain.0.value());
            0
        }"#,
        0,
        "5\n6\n7\n11\n",
    );
    // Two Text names, four object payloads; each is released exactly once.
    assert_eq!(stats.allocations, 6, "{}", stats.allocations);
}

#[test]
fn projected_shared_receivers_keep_their_owner_borrowed_through_arguments() {
    let definitions = r#"
        struct Text { name: String, count: i64 }
        struct Other { count: i64 }
        trait Read { fn inspect(self: &Self, extra: i64) -> i64 ! {panic}; }
        impl Read for Text { fn inspect(self: &Self, extra: i64) -> i64 ! {panic} { self.count + extra } }
        impl Read for Other { fn inspect(self: &Self, extra: i64) -> i64 ! {panic} { self.count + extra } }
    "#;
    rejects(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{alloc, panic}} {{
                let mut pair: (dyn Read, i64) = (Text {{name: \"x\", count: 1}}, 9);
                pair.0.inspect({{pair = (Other {{count: 10}}, 0); 0}})
            }}"
        ),
        "borrow",
    );
    agrees(
        &format!(
            "{definitions}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let pair: (dyn Read, i64) = (Text {{name: \"x\", count: 1}}, 9);
                print_i64(pair.0.inspect(pair.1));
                0
            }}"
        ),
        0,
        "10\n",
    );
}

#[test]
fn multi_trait_trait_objects_dispatch_both_traits() {
    agrees(
        r#"
        struct Point { x: i64 }
        trait A { fn a(self: Self) -> i64 ! {panic}; }
        trait B { fn b(self: Self) -> i64 ! {panic}; }
        impl A for Point { fn a(self: Self) -> i64 ! {panic} { self.x } }
        impl B for Point { fn b(self: Self) -> i64 ! {panic} { self.x + 1 } }
        fn main() -> i64 ! {io, alloc, panic} {
            let object: dyn A + B = Point { x: 5 };
            print_i64(object.a());
            0
        }"#,
        0,
        "5\n",
    );
}

#[test]
fn temporary_shared_receivers_may_return_views_of_caller_arguments() {
    agrees(
        r#"
        trait Pick {
            fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic};
        }
        struct A { tag: i64 }
        struct W<T> { value: T }
        impl Pick for A { fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        impl<T> Pick for W<T> { fn pick<'a>(self: &Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values } }
        fn make() -> dyn Pick ! {alloc, panic} { W { value: A { tag: 1 } } }
        fn main() -> i64 ! {io, alloc, panic} {
            let values = [5, 6, 7];
            print_i64(make().pick(&values[..])[1]);
            0
        }"#,
        0,
        "6\n",
    );
}
