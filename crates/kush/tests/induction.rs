use kush::{check, kernel::Term as T};

fn nat(n: u32) -> T {
    T::natural(u64::from(n).into())
}
fn rejects(source: &str, expected: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected:?}, got {error:?}"
    );
}

#[test]
fn source_induction_defines_addition_and_proves_right_identity() {
    let checked = check(include_str!("../../../examples/induction.kush")).unwrap();
    assert_eq!(checked.definitions.len(), 11);
    let k = &checked.kernel;
    for n in [0, 1, 3] {
        let sum = T::app(T::app(T::global("add"), nat(n)), nat(2));
        assert_eq!(k.normalize_closed(&sum).unwrap(), nat(n + 2));
        let proof = T::app(T::global("right_identity"), nat(n));
        k.check_closed(&proof, &T::eq(T::Nat, nat(n), nat(n)))
            .unwrap();
        assert_eq!(k.normalize_closed(&proof).unwrap(), T::refl(T::Nat, nat(n)));
    }
    assert_eq!(
        k.normalize_closed(&T::global("addition_example")).unwrap(),
        T::refl(T::Nat, nat(5))
    );
    // The theorem itself quantifies over n. Checking it did not enumerate n.
    k.check_closed(
        &T::global("right_identity"),
        &T::pi(
            T::Nat,
            T::eq(
                T::Nat,
                T::app(T::app(T::global("add"), T::Var(0)), T::Zero),
                T::Var(0),
            ),
        ),
    )
    .unwrap();
}

#[test]
fn source_transport_derives_symmetry_for_a_generic_carrier() {
    let checked = check(include_str!("../../../examples/induction.kush")).unwrap();
    let proof = T::app(
        T::app(
            T::app(T::app(T::global("symmetry"), T::Nat), nat(2)),
            nat(2),
        ),
        T::refl(T::Nat, nat(2)),
    );
    assert_eq!(
        checked.kernel.normalize_closed(&proof).unwrap(),
        T::refl(T::Nat, nat(2))
    );
    // Distinct endpoints cannot be related by passing bogus reflexivity evidence.
    let bad = T::app(
        T::app(
            T::app(T::app(T::global("symmetry"), T::Nat), nat(1)),
            nat(2),
        ),
        T::refl(T::Nat, nat(1)),
    );
    assert!(checked.kernel.infer_closed(&bad).is_err());
}

#[test]
fn pure_nondependent_function_types_shift_anonymous_binders() {
    let source = "
        type Endo<T: Type> = fn(T) -> T ! {};
        total fn apply<T: Type>(f: Endo<T>, x: T) -> T ! {} { f(x) }
        total fn test() -> Nat ! {} { apply::<Nat>(Nat.succ, 2) }
    ";
    let checked = check(source).unwrap();
    assert_eq!(
        checked.kernel.normalize_closed(&T::global("test")).unwrap(),
        nat(3)
    );
}

#[test]
fn mixed_named_and_anonymous_function_binders_preserve_dependencies() {
    let source = "
        type Family<T: Type> = fn(x: T, T) -> Eq<T, x, x> ! {};
        total fn proof<T: Type>(x: T, y: T) -> Eq<T, x, x> ! {} { refl::<T>(x) }
        total fn apply<T: Type>(f: Family<T>, x: T) -> Eq<T, x, x> ! {} { f(x, x) }
        total fn result() -> Eq<Nat, 2, 2> ! {} { apply::<Nat>(proof::<Nat>, 2) }
    ";
    let checked = check(source).unwrap();
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&T::global("result"))
            .unwrap(),
        T::refl(T::Nat, nat(2))
    );
}

#[test]
fn function_type_binders_are_local_and_annotations_precede_binding() {
    rejects(
        "type F = fn(n: Nat) -> Nat ! {}; total fn bad() -> Nat ! {} { n }",
        "unknown name 'n'",
    );
    rejects(
        "type F = fn(x: Later, Later: Type) -> Nat ! {};",
        "unknown name 'Later'",
    );
    rejects(
        "type F = fn(n: Nat, n: Nat) -> Nat ! {};",
        "duplicate binder",
    );
    rejects(
        "total fn bad(n: Nat) -> fn(n: Nat) -> Nat ! {} ! {} { n }",
        "type mismatch",
    );
    // The function-type's n cannot leak and shadow the outer n in the body.
    check("total fn good(n: Nat, f: fn(n: Nat) -> Nat ! {}) -> Nat ! {} { n }").unwrap();
    rejects(
        "type F = fn(Nat) -> missing ! {};",
        "unknown name 'missing'",
    );
}

#[test]
fn higher_order_logical_functions_require_empty_effect_rows() {
    rejects("type F = fn(Nat) -> Nat ! {io};", "empty effect row");
    rejects("type F = fn(Nat) -> Nat ! {suspend};", "empty effect row");
    rejects("type F = fn() -> Nat ! {};", "nullary function-type");
}

#[test]
fn eliminators_require_exact_arity_and_cannot_be_used_bare() {
    for (body, expected) in [
        ("Nat.induct", "fully applied"),
        ("Nat.induct(0)", "exactly four"),
        ("Nat.induct(0, 0, 0, 0, 0)", "exactly four"),
        ("Nat.induct::<Nat>(0, 0, 0, 0)", "no generic arguments"),
        ("Eq.transport", "fully applied"),
        ("Eq.transport(0, 0, 0, 0, 0)", "one carrier type"),
        (
            "Eq.transport::<Nat, Nat>(0, 0, 0, 0, 0)",
            "one carrier type",
        ),
        ("Eq.transport::<Nat>(0)", "exactly five"),
    ] {
        rejects(
            &format!("total fn bad() -> Nat ! {{}} {{ {body} }}"),
            expected,
        );
    }
}

#[test]
fn induction_checks_motive_base_step_and_scrutinee_from_source() {
    let prelude =
        "type P<n: Nat> = Nat; total fn step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }";
    for body in [
        "Nat.induct(Nat, 0, step, 2)",
        "Nat.induct(P, Type, step, 2)",
        "Nat.induct(P, 0, Nat.succ, 2)",
        "Nat.induct(P, 0, step, Type)",
    ] {
        let source = format!("{prelude} total fn bad() -> Nat ! {{}} {{ {body} }}");
        assert!(check(&source).is_err(), "{source}");
    }
    let false_theorem = include_str!("../../../examples/induction.kush")
        .replace("refl::<Nat>(5)", "refl::<Nat>(4)");
    rejects(&false_theorem, "type mismatch");
}

#[test]
fn transport_checks_carrier_endpoints_motive_evidence_and_value() {
    let prelude = "type P<n: Nat> = Nat;";
    for body in [
        "Eq.transport::<Nat>(0, 1, P, refl::<Nat>(0), 0)",
        "Eq.transport::<Nat>(0, 0, P, 0, 0)",
        "Eq.transport::<Nat>(0, 0, P, refl::<Nat>(0), Type)",
        "Eq.transport::<Nat>(0, 0, Nat, refl::<Nat>(0), 0)",
        "Eq.transport::<0>(0, 0, P, refl::<Nat>(0), 0)",
    ] {
        assert!(
            check(&format!(
                "{prelude} total fn bad() -> Nat ! {{}} {{ {body} }}"
            ))
            .is_err(),
            "{body}"
        );
    }
}

#[test]
fn intrinsic_detection_respects_local_shadowing_and_module_qualification() {
    rejects(
        "total fn bad(Nat: Type, x: Nat) -> Nat ! {} { Nat.induct(x, x, x, x) }",
        "member projection",
    );
    rejects(
        "total fn bad(Eq: Type, x: Eq) -> Eq ! {} { Eq.transport::<Eq>(x, x, x, x, x) }",
        "member projection",
    );
    check(
        "module m; type P<n: Nat> = Nat;
        total fn step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }
        total fn value() -> Nat ! {} { m.Nat.induct(P, 0, step, 2) }",
    )
    .unwrap();
    rejects(
        "type P<n: Nat> = Nat; total fn f() -> Nat ! {} { Nat.induct(P, 0, f, 2) }",
        "cyclic logical definitions",
    );
}

#[test]
fn induction_infers_the_motives_universe_instead_of_fixing_it_to_zero() {
    let source = "
        type TypeFamily<n: Nat> = Type;
        total fn step(n: Nat, previous: Type) -> Type ! {} { previous }
        total fn selected_type(n: Nat) -> Type ! {} {
            Nat.induct(TypeFamily, Nat, step, n)
        }
    ";
    let checked = check(source).unwrap();
    let selected = T::app(T::global("selected_type"), nat(2));
    assert_eq!(checked.kernel.normalize_closed(&selected).unwrap(), T::Nat);
}
