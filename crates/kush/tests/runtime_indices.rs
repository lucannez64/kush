use kush::executable::{Executable, check};

fn checked(source: &str) -> Executable {
    check(source).unwrap()
}
fn evaluate(source: &str) -> i64 {
    checked(source).evaluate(&mut Vec::new()).unwrap()
}
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

const PRELUDE: &str = r#"
    prop ZeroI<n: i64> { Zero: ZeroI<0> }
    prop IsTrue<b: Bool> { Yes: IsTrue<true>, Also: IsTrue<true> }
    prop UnitTag<u: Unit> { Mk: UnitTag<()> }
    total enum Tag<n: i64> { Mk: Tag<n> }

    total fn zero_proof() -> ZeroI<0> ! {} { ZeroI.Zero::<0> }
    total fn true_proof() -> IsTrue<true> ! {} { IsTrue.Yes::<true> }
    total fn unit_proof() -> UnitTag<()> ! {} { UnitTag.Mk::<()> }
    total fn same_i64(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(n) }

    fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
    fn keep_bool(b: Bool, erased same: Eq<Bool, b, b>) -> i64 ! {} { if b { 1 } else { 0 } }
    fn keep_zero(n: i64, erased p: ZeroI<n>) -> i64 ! {} { n }
    fn keep_true(b: Bool, erased p: IsTrue<b>) -> i64 ! {} { 4 }
    fn keep_unit(u: Unit, erased p: UnitTag<u>) -> i64 ! {} { 2 }
    fn keep_tag(n: i64, erased p: Tag<n>) -> i64 ! {} { 11 }
    fn forward(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { keep(n, p) }
"#;

#[test]
fn runtime_scalars_index_equality_and_user_predicates_without_runtime_storage() {
    // The shipped example stays executable and agrees with this test.
    assert_eq!(
        evaluate(include_str!("../../../examples/runtime-indices.kush")),
        42
    );
    let source = format!(
        "{PRELUDE}
        fn main() -> i64 ! {{panic}} {{
            let five: i64 = 5;
            let b: Bool = true;
            let u: Unit = ();
            keep(five, refl::<i64>(five))
                + forward(five, same_i64(five))
                + keep(10, refl::<i64>(10))
                + keep_bool(b, refl::<Bool>(b))
                + keep_zero(0, zero_proof())
                + keep_true(true, true_proof())
                + keep_true(true, IsTrue.Also::<true>)
                + keep_unit(u, unit_proof())
                + keep_tag(0, Tag.Mk::<0>)
        }}"
    );
    let program = checked(&source);
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    // Proofs, proposition indices, and their constructors never allocate or
    // become runtime values.
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);
    let mut logical = program.logical_definitions().to_vec();
    logical.sort();
    assert!(logical.contains(&"ZeroI".to_string()));
    assert!(logical.contains(&"IsTrue".to_string()));
    assert!(logical.contains(&"Tag".to_string()));
    assert!(logical.contains(&"same_i64".to_string()));
    // Only the executable functions are in the runtime IR.
    assert_eq!(program.function_count(), 8);
}

#[test]
fn mixed_erased_and_runtime_binders_substitute_in_source_order() {
    let source = r#"
        total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
        fn mixed(
            erased n: Nat,
            k: i64,
            erased same: Eq<i64, k, k>,
            erased p: Eq<Nat, n, n>,
        ) -> i64 ! {} { k }
        fn main() -> i64 ! {panic} {
            mixed(0, 42, refl::<i64>(42), truth())
        }
    "#;
    assert_eq!(evaluate(source), 42);
    rejects(
        r#"
        total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
        fn mixed(
            erased n: Nat,
            k: i64,
            erased same: Eq<i64, k, k>,
            erased p: Eq<Nat, n, n>,
        ) -> i64 ! {} { k }
        fn main() -> i64 ! {panic} {
            mixed(1, 42, refl::<i64>(42), truth())
        }
        "#,
        "proof does not establish",
    );
}

#[test]
fn recursive_logical_data_can_be_indexed_by_machine_literals() {
    let source = r#"
        total enum Other<n: i64> { Mk: Other<0> }
        total enum Steps<n: i64> {
            End: Steps<0>,
            More(Steps<0>, Other<0>): Steps<1>,
        }
        total fn one_step() -> Steps<1> ! {} {
            Steps.More::<1>(Steps.End::<0>, Other.Mk::<0>)
        }
        fn use_steps(n: i64, erased p: Steps<n>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { use_steps(1, one_step()) }
    "#;
    assert_eq!(evaluate(source), 42);
    rejects(
        r#"
        total enum Other<n: i64> { Mk: Other<0> }
        total enum Steps<n: i64> {
            End: Steps<0>,
            More(Steps<0>, Other<0>): Steps<1>,
        }
        total fn one_step() -> Steps<1> ! {} {
            Steps.More::<1>(Steps.End::<0>, Other.Mk::<0>)
        }
        fn use_steps(n: i64, erased p: Steps<n>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { use_steps(0, one_step()) }
        "#,
        "proof does not establish",
    );
}

#[test]
fn symbolic_indices_are_ordinary_checked_values_not_evidence() {
    // A runtime scalar is a valid index inside a proof's type.
    let positive = r#"
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} { let n = 21; keep(n, refl::<i64>(n)) + 21 }
    "#;
    assert_eq!(evaluate(positive), 42);
    // It is not itself a proof, even for an erased machine-carried value.
    rejects(
        r#"
        fn consume(erased n: i64) -> i64 ! {} { 1 }
        fn main() -> i64 ! {panic} { let n = 3; consume(n) }
        "#,
        "runtime scalar is a symbolic index, not erased evidence",
    );
    // Nor can it inhabit an equality proposition.
    rejects(
        r#"
        fn consume(erased p: Eq<i64, 0, 0>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {panic} { let n = 0; consume(n) }
        "#,
        "runtime scalar is a symbolic index, not erased evidence",
    );
    // A wildcard cannot hide a missing kernel proof.
    rejects(
        r#"
        fn consume(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {panic} { consume(1, _) }
        "#,
        "cannot discharge a logical proposition",
    );
}

#[test]
fn wrong_and_false_proofs_are_rejected_by_the_kernel() {
    rejects(
        &format!("{PRELUDE} fn main() -> i64 ! {{panic}} {{ keep(3, refl::<i64>(4)) }}"),
        "proof does not establish",
    );
    rejects(
        &format!(
            "{PRELUDE} fn main() -> i64 ! {{panic}} {{ keep_bool(false, refl::<Bool>(true)) }}"
        ),
        "proof does not establish",
    );
    rejects(
        &format!("{PRELUDE} fn main() -> i64 ! {{panic}} {{ keep_true(false, true_proof()) }}"),
        "proof does not establish",
    );
    rejects(
        &format!("{PRELUDE} fn main() -> i64 ! {{panic}} {{ keep_zero(1, zero_proof()) }}"),
        "proof does not establish",
    );
    rejects(
        &format!("{PRELUDE} fn main() -> i64 ! {{panic}} {{ keep_tag(1, Tag.Mk::<0>) }}"),
        "proof does not establish",
    );
    // A false theorem is still rejected at its definition.
    rejects(
        "total fn bad() -> Eq<i64, 3, 4> ! {} { refl::<i64>(3) }",
        "type mismatch",
    );
    // The mere syntax of a constructor or `refl` is not a proof shortcut: the
    // result index must be the same symbolic value.
    rejects(
        "prop ZeroI<n: i64> { Zero: ZeroI<0> }
         total fn bad(n: i64) -> ZeroI<n> ! {} { ZeroI.Zero::<0> }",
        "type mismatch",
    );
    // `Eq<Nat, n, n>` is not `Eq<i64, n, n>`: no unchecked cast from machine
    // arithmetic to mathematical unbounded naturals.
    rejects(
        "fn bad(n: i64, erased p: Eq<Nat, n, n>) -> i64 ! {} { n }
         fn main() -> i64 ! {} { 0 }",
        "type mismatch",
    );
    // A runtime function is never a checked logical definition.
    rejects(
        "fn runtime() -> i64 ! {} { 0 }
         fn f(erased p: Eq<i64, 0, 0>) -> i64 ! {} { 1 }
         fn main() -> i64 ! {} { f(runtime) }",
        "not a checked logical definition",
    );
    // A total proof helper may not call runtime code either.
    rejects(
        "fn runtime(n: i64) -> i64 ! {} { n }
         total fn bad(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(runtime(n)) }",
        "depends on executable or effectful function",
    );
}

#[test]
fn mutable_indices_use_the_current_version_at_each_call() {
    assert_eq!(
        evaluate(
            "fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
             fn main() -> i64 ! {panic} { let mut n = 3; keep(n, refl::<i64>(n)) }"
        ),
        3
    );
    assert_eq!(
        evaluate(
            "fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
             fn main() -> i64 ! {panic} {
                 let mut n = 3;
                 if true { n = 4; }
                 keep(n, refl::<i64>(n))
             }"
        ),
        4
    );
    assert_eq!(
        evaluate(
            "fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {panic} { n }
             fn main() -> i64 ! {panic} {
                 let mut n = 0;
                 while n < 3 { n = n + 1; }
                 keep(n, refl::<i64>(n))
             }"
        ),
        3
    );
    // A proof about an older literal is independent evidence for that literal,
    // not for the mutable binding's new value.
    rejects(
        "fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
         fn main() -> i64 ! {panic} {
             let mut n = 4;
             keep(n, refl::<i64>(3))
         }",
        "proof does not establish",
    );
    // A scalar actual is frozen only when a later proof type actually names it.
    // Independent evaluated arguments keep their normal runtime evaluation.
    let independent = r#"
        total fn truth() -> Eq<i64, 0, 0> ! {} { refl::<i64>(0) }
        fn make() -> i64 ! {} { 21 }
        fn keep_indep(n: i64, erased p: Eq<i64, 0, 0>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} { keep_indep(make(), truth()) * 2 }
    "#;
    assert_eq!(evaluate(independent), 42);
    // An argument is frozen where it is written. A proof may not be checked
    // against the result of an arbitrarily evaluated call...
    rejects(
        "fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
         fn make(n: i64) -> i64 ! {} { n }
         fn main() -> i64 ! {panic} { keep(make(3), refl::<i64>(3)) }",
        "evaluate the expression into a named immutable local",
    );
    // ...but binding that evaluated result to an immutable local is exactly the
    // supported freezing point.
    let named = r#"
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn make(n: i64) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let x = make(42);
            keep(x, refl::<i64>(x))
        }
    "#;
    assert_eq!(evaluate(named), 42);
    // A non-scalar runtime value is not a symbolic index at all.
    rejects(
        "fn keep(xs: Vec<i64>, erased p: Eq<i64, xs, xs>) -> i64 ! {} { 1 }
         fn main() -> i64 ! {panic} { 0 }",
        "runtime or generic binding 'xs'",
    );
}

#[test]
fn aliases_wrappers_and_cross_module_proofs_substitute_symbolic_indices() {
    let alias = r#"
        type MyInt = i64;
        type Same<T: Type, x: T> = Eq<T, x, x>;
        total fn same(n: MyInt) -> Same<MyInt, n> ! {} { refl::<MyInt>(n) }
        fn keep(n: MyInt, erased p: Same<MyInt, n>) -> i64 ! {} { n }
        fn forward(n: MyInt, erased p: Same<MyInt, n>) -> i64 ! {} { keep(n, p) }
        fn main() -> i64 ! {panic} {
            let n: MyInt = 42;
            forward(n, same(n))
        }
    "#;
    assert_eq!(evaluate(alias), 42);

    use kush::program::{Memory, load};
    let modules = Memory(vec![(
        "app.logic".into(),
        "module app.logic;
         pub prop ZeroI<n: i64> { Zero: ZeroI<0> }
         pub total enum Tag<n: i64> { Mk: Tag<n> }
         pub total fn zero_proof() -> ZeroI<0> ! {} { ZeroI.Zero::<0> }
         pub total fn same(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(n) }"
            .into(),
    )]);
    let source = "module app.main;
        use app.logic;
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn keep_zero(n: i64, erased p: logic.ZeroI<n>) -> i64 ! {} { 10 }
        fn keep_tag(n: i64, erased p: logic.Tag<n>) -> i64 ! {} { 31 }
        fn main() -> i64 ! {panic} {
            let n: i64 = 1;
            keep(n, logic.same(n)) + keep_zero(0, logic.zero_proof()) + keep_tag(0, logic.Tag.Mk::<0>)
        }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 42);
}

#[test]
fn grades_propositions_and_ownership_keep_their_own_obligations() {
    // A grade-zero runtime scalar may still be named by an erased proof type:
    // the dependency is erased and adds no runtime observation.
    let graded = r#"
        fn graded(n: i64 @[0], erased p: Eq<i64, n, n>) -> i64 ! {} { 7 }
        fn exact(n: i64 @[1], erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} { graded(1, refl::<i64>(1)) + exact(35, refl::<i64>(35)) }
    "#;
    assert_eq!(evaluate(graded), 42);

    // Runtime-indexed propositions still support proof irrelevance, and still
    // distinguish different proposition indices.
    let prop = r#"
        prop IsTrue<b: Bool> { Yes: IsTrue<true>, Also: IsTrue<true> }
        prop IsFalse<b: Bool> { No: IsFalse<false> }
        fn consume(b: Bool, erased p: IsTrue<b>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(true, IsTrue.Also::<true>) }
    "#;
    assert_eq!(evaluate(prop), 42);
    rejects(
        r#"
        prop IsTrue<b: Bool> { Yes: IsTrue<true>, Also: IsTrue<true> }
        fn consume(b: Bool, erased p: IsTrue<b>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(false, IsTrue.Also::<true>) }
        "#,
        "proof does not establish",
    );

    // An owning runtime value still cannot enter an erased proposition.
    rejects(
        "prop Bad { Mk(Vec<i64>): Bad }
         fn main() -> i64 ! {} { 0 }",
        "not supported by the logical subset",
    );
    rejects(
        "enum Runtime { A }
         prop Bad { Mk(Runtime): Bad }
         fn main() -> i64 ! {} { 0 }",
        "runtime values cannot enter erased proofs",
    );
    // Erased evidence is never readable at runtime.
    rejects(
        "prop True { Trivial: True }
         fn consume(n: i64, erased p: True) -> i64 ! {} { if p { n } else { 0 } }
         fn main() -> i64 ! {panic} { consume(3, Trivial) }",
        "no runtime value",
    );
}

#[test]
fn machine_literals_are_range_checked_and_distinct_from_naturals() {
    let extremes = r#"
        total fn min_refl() -> Eq<i64, -9223372036854775808, -9223372036854775808> ! {} {
            refl::<i64>(-9223372036854775808)
        }
        total fn max_refl() -> Eq<i64, 9223372036854775807, 9223372036854775807> ! {} {
            refl::<i64>(9223372036854775807)
        }
        fn use_min(erased p: Eq<i64, -9223372036854775808, -9223372036854775808>) -> i64 ! {} { 0 }
        fn main() -> i64 ! {panic} { use_min(min_refl()) }
    "#;
    assert_eq!(evaluate(extremes), 0);
    rejects(
        "total fn bad() -> Eq<i64, 9223372036854775808, 0> ! {} { refl::<i64>(0) }",
        "outside the i64 range",
    );
    rejects(
        "total fn bad() -> Eq<i64, 0, 0> ! {} { refl::<i64>(true) }",
        "type mismatch",
    );
    rejects(
        "total fn bad(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(n + 1) }",
        "expression is not supported",
    );
    // Natural indices stay a separate, unbounded mathematical carrier.
    rejects(
        "total fn bad() -> Eq<Nat, 0, 0> ! {} { refl::<i64>(0) }",
        "type mismatch",
    );
}

#[test]
fn lambda_parameters_and_frozen_mutable_captures_are_symbolic_indices() {
    let source = r#"
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let f: fn(i64) -> i64 ! {} = fn(n: i64) -> i64 ! {} { keep(n, refl::<i64>(n)) };
            f(42)
        }
    "#;
    assert_eq!(evaluate(source), 42);
    // An immutable scalar captured into a closure is frozen at construction
    // and can still index the lambda body's proof.
    let captured = r#"
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic, alloc} {
            let m = 42;
            let f: once fn() -> i64 ! {alloc, panic} =
                fn() -> i64 ! {alloc, panic} { keep(m, refl::<i64>(m)) };
            f()
        }
    "#;
    assert_eq!(evaluate(captured), 42);
    // A mutable scalar is copied into the closure environment at construction.
    // The proof is about that immutable copy, so assigning the outer binding
    // afterwards cannot invalidate it or reinterpret it at the final value.
    let frozen = r#"
        fn keep(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic, alloc} {
            let mut n = 42;
            let f: once fn() -> i64 ! {alloc, panic} =
                fn() -> i64 ! {alloc, panic} { keep(n, refl::<i64>(n)) };
            n = 7;
            f() + n
        }
    "#;
    assert_eq!(evaluate(frozen), 49);
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn reference_and_native_agree_on_symbolic_runtime_indices() {
    use std::process::Command;
    let source = format!(
        "{PRELUDE}
        fn main() -> i64 ! {{panic}} {{
            let five: i64 = 5;
            let b: Bool = true;
            keep(five, refl::<i64>(five))
                + forward(five, same_i64(five))
                + keep(10, refl::<i64>(10))
                + keep_bool(b, refl::<Bool>(b))
                + keep(0, refl::<i64>(0))
                + keep_true(true, true_proof())
                + keep_true(true, IsTrue.Also::<true>)
                + keep_unit((), unit_proof())
                + keep_tag(0, Tag.Mk::<0>)
        }}"
    );
    let program = checked(&source);
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("runtime-indices");
    kush::native::build(&program, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(42));
}
