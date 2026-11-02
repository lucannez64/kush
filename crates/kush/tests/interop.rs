use kush::executable::{Executable, check};

fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}
fn checked(source: &str) -> Executable {
    check(source).unwrap()
}
fn evaluate(source: &str) -> i64 {
    checked(source).evaluate(&mut Vec::new()).unwrap()
}

const PROOFS: &str = r#"
    total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
    total fn use_proof(p: Eq<Nat, 0, 0>) -> Eq<Nat, 0, 0> ! {} { p }
    total fn identity<T: Type>(x: T) -> T ! {} { x }
"#;

#[test]
fn logical_definitions_coexist_with_executable_code_and_are_erased() {
    let source = format!(
        "{PROOFS}
        type Same<T: Type, x: T> = Eq<T, x, x>;
        fn consume(erased p: Eq<Nat, 0, 0>) -> i64 ! {{}} {{ 7 }}
        fn pass(erased p: Eq<Nat, 0, 0>) -> i64 ! {{}} {{ consume(p) }}
        fn main() -> i64 ! {{panic}} {{ pass(use_proof(truth)) + 3 }}"
    );
    let program = checked(&source);
    assert_eq!(program.function_count(), 3); // consume, pass, main
    let mut logical = program.logical_definitions().to_vec();
    logical.sort();
    assert_eq!(logical, ["Same", "identity", "truth", "use_proof"]);
    assert_eq!(evaluate(&source), 10);
}

#[test]
fn kernel_propositions_and_arithmetic_facts_coexist_in_one_signature() {
    let source = format!(
        "{PROOFS}
        fn bounded(
            erased p: Eq<Nat, 0, 0>,
            n: i64,
            erased positive: {{ 0 < n }},
        ) -> i64 ! {{}} {{ n }}
        fn main() -> i64 ! {{panic}} {{ bounded(truth, 3, _) }}"
    );
    assert_eq!(evaluate(&source), 3);
}

#[test]
fn erased_proofs_are_rejected_as_runtime_values_in_both_directions() {
    // A logical definition has no runtime value.
    rejects(
        &format!("{PROOFS} fn main() -> i64 ! {{}} {{ truth() }}"),
        "cannot be called at runtime",
    );
    // An erased proof parameter cannot be read or returned at runtime.
    rejects(
        "total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
         fn f(erased p: Eq<Nat, 0, 0>) -> i64 ! {} { p }
         fn main() -> i64 ! {} { 0 }",
        "no runtime value",
    );
}

#[test]
fn invalid_inapplicable_and_partial_evidence_is_rejected() {
    rejects(
        &format!(
            "{PROOFS}
             fn f(erased p: Eq<Nat, 1, 1>) -> i64 ! {{}} {{ 1 }}
             fn main() -> i64 ! {{}} {{ f(truth) }}"
        ),
        "proof does not establish",
    );
    rejects(
        &format!(
            "{PROOFS}
             fn f(erased p: Eq<Nat, 0, 0>) -> i64 ! {{}} {{ 1 }}
             fn main() -> i64 ! {{}} {{ f(_) }}"
        ),
        "cannot discharge a logical proposition",
    );
    // A false theorem cannot be admitted merely because executable code exists.
    rejects(
        "total fn bad() -> Eq<Nat, 0, 1> ! {} { refl::<Nat>(0) }
         fn main() -> i64 ! {} { 0 }",
        "type mismatch",
    );
    // Effectful total functions are not proof evidence.
    rejects(
        "total fn bad() -> Eq<Nat, 0, 0> ! {io} { refl::<Nat>(0) }
         fn main() -> i64 ! {} { 0 }",
        "empty effect row",
    );
    // A partial function is not a checked logical definition.
    rejects(
        "fn partial() -> i64 ! {} { 0 }
         fn f(erased p: Eq<Nat, 0, 0>) -> i64 ! {} { 1 }
         fn main() -> i64 ! {} { f(partial) }",
        "not a checked logical definition",
    );
}

#[test]
fn relevance_prevents_runtime_values_from_entering_erased_propositions() {
    // A total definition may not call runtime code.
    rejects(
        "fn runtime() -> i64 ! {} { 0 }
         total fn bad() -> Nat ! {} { runtime() }
         fn main() -> i64 ! {} { 0 }",
        "depends on executable or effectful function",
    );
    // Runtime parameters stay out of *mathematical* positions: a machine i64
    // is not Nat, and runtime type generics are never kernel binders.
    rejects(
        "fn f(n: i64, erased p: Eq<Nat, n, n>) -> i64 ! {} { n }
         fn main() -> i64 ! {} { 0 }",
        "type mismatch",
    );
    rejects(
        "fn f<T: Type>(erased p: Eq<T, T, T>) -> i64 ! {} { 1 }
         fn main() -> i64 ! {} { 0 }",
        "runtime or generic binding 'T'",
    );
}

#[test]
fn module_qualified_logical_proofs_are_checked_and_erased() {
    use kush::program::{Memory, load};
    let modules = Memory(vec![
        (
            "app.lemmas".into(),
            "module app.lemmas;
             pub total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }"
                .into(),
        ),
        (
            "app.other".into(),
            "module app.other;
             pub total fn truth() -> Eq<Nat, 1, 1> ! {} { refl::<Nat>(1) }"
                .into(),
        ),
    ]);
    let source = "module app.main;
        use app.lemmas;
        use app.other;
        fn consume_zero(erased p: Eq<Nat, 0, 0>) -> i64 ! {} { 11 }
        fn consume_one(erased p: Eq<Nat, 1, 1>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {panic} { consume_zero(lemmas.truth) + consume_one(other.truth) }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 12);
    let mut logical = checked.logical_definitions().to_vec();
    logical.sort();
    assert_eq!(logical, ["app.lemmas::truth", "app.other::truth"]);
}

#[test]
fn reference_evaluator_and_native_backend_agree_on_erased_proofs() {
    use std::process::Command;
    let source = format!(
        "{PROOFS}
        fn consume(erased p: Eq<Nat, 0, 0>) -> i64 ! {{}} {{ 4 }}
        fn main() -> i64 ! {{panic}} {{ consume(use_proof(truth)) + 1 }}"
    );
    let program = checked(&source);
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 5);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("interop");
    kush::native::build(&program, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(5));
}

#[test]
fn cross_module_finite_and_prop_evidence_is_checked_and_erased() {
    use kush::program::{Memory, load};
    let modules = Memory(vec![(
        "app.finite".into(),
        "module app.finite;
         pub total enum Fin<N: Nat> {
             FZero<n: Nat>: Fin<Nat.succ<n>>,
             FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
         }
         pub total fn fzero<n: Nat>() -> Fin<Nat.succ<n>> ! {} {
             Fin.FZero::<Nat.succ<n>, n>
         }
         pub total fn fsucc<n: Nat>(pred: Fin<n>) -> Fin<Nat.succ<n>> ! {} {
             Fin.FSucc::<Nat.succ<n>, n>(pred)
         }
         pub total fn three() -> Fin<3> ! {} {
             fsucc::<2>(fsucc::<1>(fzero::<0>))
         }
         pub prop IsZero<n: Nat> {
             ZeroIsZero: IsZero<0>,
         }
         pub total fn zero_proof() -> IsZero<0> ! {} {
             IsZero.ZeroIsZero::<0>
         }
         pub type Bootstrapped<n: Nat> = IsZero<n>;
         pub total fn boot_zero() -> Bootstrapped<0> ! {} { zero_proof() }"
            .into(),
    )]);
    let source = "module app.main;
        use app.finite;
        fn consume_fin(erased f: finite.Fin<3>) -> i64 ! {} { 40 }
        fn consume_zero(erased n: Nat, erased p: finite.Bootstrapped<n>) -> i64 ! {} { 2 }
        fn main() -> i64 ! {panic}
            { consume_fin(finite.three()) + consume_zero(0, finite.boot_zero()) }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.function_count(), 3);
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 42);
    let logical = checked.logical_definitions();
    assert!(logical.iter().any(|name| name.ends_with("Fin")));
    assert!(logical.iter().any(|name| name.ends_with("IsZero")));
    assert!(logical.iter().any(|name| name.ends_with("zero_proof")));

    // The proof still has to establish the substituted, index-dependent Prop.
    let wrong = "module app.main;
        use app.finite;
        fn bad(erased n: Nat, erased p: finite.Bootstrapped<n>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {} { bad(1, finite.boot_zero()) }";
    let program = load("main.kush", wrong, &modules).unwrap();
    let error = kush::executable::check_program(&program).unwrap_err();
    assert!(
        error.message.contains("proof does not establish"),
        "{error:?}"
    );
    let wrong_index = "module app.main;
        use app.finite;
        fn bad(erased f: finite.Fin<4>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {} { bad(finite.three()) }";
    let program = load("main.kush", wrong_index, &modules).unwrap();
    let error = kush::executable::check_program(&program).unwrap_err();
    assert!(
        error.message.contains("proof does not establish"),
        "{error:?}"
    );
}

#[test]
fn props_are_erased_evidence_not_runtime_values_or_control_flow() {
    rejects(
        "prop True { Trivial: True }
         fn bad(erased p: True) -> i64 ! {} { if p { 1 } else { 0 } }
         fn main() -> i64 ! {} { 0 }",
        "erased logical proofs have no runtime value",
    );
    rejects(
        "prop True { Trivial: True }
         fn bad(p: True) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "erased before runtime lowering",
    );
    rejects(
        "prop True { Trivial: True }
         total fn partial() -> True ! {io} { Trivial }
         fn main() -> i64 ! {} { 0 }",
        "empty effect row",
    );
    // A logical alias of a proposition is accepted as erased evidence only.
    let source = "prop True { Trivial: True }
        type P = True;
        fn consume(erased p: P) -> i64 ! {} { 5 }
        fn main() -> i64 ! {panic} { consume(Trivial) }";
    assert_eq!(evaluate(source), 5);
    rejects(
        "prop True { Trivial: True }
         type P = True;
         fn bad(p: P) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "erased before runtime lowering",
    );
    // A proposition cannot hide owning runtime data or a runtime container.
    rejects(
        "enum Runtime { A }
         prop Bad { Mk(Runtime): Bad }
         fn main() -> i64 ! {} { 0 }",
        "runtime values cannot enter erased proofs",
    );
    rejects(
        "prop Bad { Mk(values: Vec<i64>): Bad }
         fn main() -> i64 ! {} { 0 }",
        "not supported by the logical subset",
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_prop_and_finite_evidence() {
    use std::process::Command;
    let source = r#"
        prop IsZero<n: Nat> { ZeroIsZero: IsZero<0> }
        total enum Fin<N: Nat> {
            FZero<n: Nat>: Fin<Nat.succ<n>>,
            FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
        }
        total fn fzero<n: Nat>() -> Fin<Nat.succ<n>> ! {} {
            Fin.FZero::<Nat.succ<n>, n>
        }
        total fn fsucc<n: Nat>(pred: Fin<n>) -> Fin<Nat.succ<n>> ! {} {
            Fin.FSucc::<Nat.succ<n>, n>(pred)
        }
        total fn three() -> Fin<3> ! {} {
            fsucc::<2>(fsucc::<1>(fzero::<0>))
        }
        total fn zero_proof() -> IsZero<0> ! {} { IsZero.ZeroIsZero::<0> }
        fn consume(erased f: Fin<3>, erased p: IsZero<0>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(three(), zero_proof()) }
    "#;
    let program = checked(source);
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("prop_finite");
    kush::native::build(&program, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(42));
}

#[test]
fn erased_prop_parameters_are_first_class_logical_evidence() {
    let source = r#"
        prop True { Trivial: True }
        prop False {}
        fn consume(erased P: Prop, erased p: P) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(True, Trivial) }
    "#;
    assert_eq!(evaluate(source), 42);
    rejects(
        r#"
        prop True { Trivial: True }
        prop False {}
        fn consume(erased P: Prop, erased p: P) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(False, Trivial) }
        "#,
        "proof does not establish",
    );
}

#[test]
fn cross_module_prop_constructors_are_visible_when_exported() {
    use kush::program::{Memory, load};
    let modules = Memory(vec![(
        "app.finite".into(),
        "module app.finite;
         pub prop IsZero<n: Nat> { ZeroIsZero: IsZero<0> }"
            .into(),
    )]);
    let source = "module app.main;
        use app.finite;
        fn consume(erased p: finite.IsZero<0>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(finite.IsZero.ZeroIsZero::<0>) }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 42);
}

#[test]
fn proof_irrelevance_is_applied_to_erased_call_site_evidence() {
    let source = r#"
        prop Two { First: Two, Second: Two }
        total enum Indexed<p: Two> { Mk: Indexed<p> }
        fn consume(erased x: Indexed<Second>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(Indexed.Mk::<First>) }
    "#;
    assert_eq!(evaluate(source), 42);
    // The boundary still distinguishes different propositions.
    rejects(
        r#"
        prop Two { First: Two, Second: Two }
        prop True { Trivial: True }
        total enum Indexed<p: Two> { Mk: Indexed<p> }
        fn consume(erased x: Indexed<Second>) -> i64 ! {} { 42 }
        fn main() -> i64 ! {panic} { consume(Indexed.Mk::<True>) }
        "#,
        "proof does not establish",
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_cross_module_prop_evidence() {
    use kush::program::{Memory, load};
    use std::process::Command;
    let modules = Memory(vec![(
        "app.logic".into(),
        "module app.logic;
         pub prop True { Trivial: True }
         pub total enum Fin<N: Nat> {
             FZero<n: Nat>: Fin<Nat.succ<n>>,
             FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
         }
         pub total fn three() -> Fin<3> ! {} {
             Fin.FSucc::<3, 2>(Fin.FSucc::<2, 1>(Fin.FZero::<1, 0>))
         }"
        .into(),
    )]);
    let source = "module app.main;
        use app.logic;
        fn consume(erased f: logic.Fin<3>, erased p: logic.True) -> i64 ! {} { 21 }
        fn main() -> i64 ! {panic} {
            consume(logic.three(), logic.True.Trivial) + consume(logic.three(), logic.True.Trivial)
        }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 42);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("cross_module_prop");
    kush::native::build(&checked, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(42));
}
