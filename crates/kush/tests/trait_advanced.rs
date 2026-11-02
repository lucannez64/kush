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
        "compile-time scalar type",
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
        struct Point { x: i64 }
        struct Other { y: i64 }
        trait Update { fn update(self: &mut Self) -> i64 ! {panic}; }
        impl Update for Point { fn update(self: &mut Self) -> i64 ! {panic} { 1 } }
        impl Update for Other { fn update(self: &mut Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {panic} {
            let object: dyn Update = Point { x: 1 };
            0
        }"#,
        "exclusive '&mut self' receiver",
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
