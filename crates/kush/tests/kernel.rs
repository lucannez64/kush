use kush::kernel::{Kernel, Limits, Term as T};

fn nat(n: u32) -> T {
    T::natural(u64::from(n).into())
}
fn identity() -> T {
    T::lam(T::universe(0), T::lam(T::Var(0), T::Var(0)))
}
fn identity_type() -> T {
    T::pi(T::universe(0), T::pi(T::Var(0), T::Var(1)))
}

#[test]
fn universes_are_stratified_and_noncumulative() {
    let k = Kernel::default();
    assert_eq!(k.infer_closed(&T::universe(0)).unwrap(), T::universe(1));
    assert_eq!(k.infer_closed(&T::universe(3)).unwrap(), T::universe(4));
    assert!(k.check_closed(&T::universe(0), &T::universe(0)).is_err());
    assert!(k.check_closed(&T::Nat, &T::universe(1)).is_err());
    assert!(k.infer_closed(&T::universe(u32::MAX)).is_err());
    assert_eq!(
        k.infer_closed(&T::pi(T::universe(2), T::universe(1)))
            .unwrap(),
        T::universe(3)
    );
}
#[test]
fn polymorphic_identity_and_dependent_application() {
    let k = Kernel::default();
    k.check_closed(&identity(), &identity_type()).unwrap();
    let applied = T::app(T::app(identity(), T::Nat), nat(3));
    assert_eq!(k.infer_closed(&applied).unwrap(), T::Nat);
    assert_eq!(k.normalize_closed(&applied).unwrap(), nat(3));
    assert!(k.check_closed(&identity(), &T::Nat).is_err());
}
#[test]
fn beta_reduction_does_not_capture_variables() {
    let k = Kernel::default();
    // λx:Nat. (λy:Nat. λz:Nat. y) x  ==> λx:Nat. λz:Nat. x
    let term = T::lam(
        T::Nat,
        T::app(T::lam(T::Nat, T::lam(T::Nat, T::Var(1))), T::Var(0)),
    );
    assert_eq!(
        k.normalize_closed(&term).unwrap(),
        T::lam(T::Nat, T::lam(T::Nat, T::Var(1)))
    );
    // The result *type* of an application must substitute its type argument too.
    assert_eq!(
        k.infer_closed(&T::app(identity(), T::Nat)).unwrap(),
        T::pi(T::Nat, T::Nat)
    );
}
#[test]
fn dependent_binder_types_are_shifted_on_lookup() {
    let k = Kernel::default();
    // ∀A:Type. ∀x:A. ∀B:Type. x : A, with A at index 2 in the body.
    let term = T::lam(
        T::universe(0),
        T::lam(T::Var(0), T::lam(T::universe(0), T::Var(1))),
    );
    let expected = T::pi(
        T::universe(0),
        T::pi(T::Var(0), T::pi(T::universe(0), T::Var(2))),
    );
    k.check_closed(&term, &expected).unwrap();
}
#[test]
fn free_variables_malformed_types_and_bad_calls_are_rejected() {
    let k = Kernel::default();
    for term in [
        T::Var(0),
        T::Var(usize::MAX),
        T::global("missing"),
        T::app(T::Zero, T::Zero),
        T::succ(T::Nat),
        T::lam(T::Zero, T::Var(0)),
        T::pi(T::Nat, T::Zero),
        T::app(T::lam(T::Nat, T::Var(0)), T::universe(0)),
    ] {
        assert!(k.infer_closed(&term).is_err(), "{term:?}");
    }
    // Normalization must not become an unchecked reduction API for ill-typed input.
    assert!(k.normalize_closed(&T::app(T::Zero, T::Zero)).is_err());
}
#[test]
fn equality_reflexivity_rejects_false_statements() {
    let k = Kernel::default();
    let proof = T::refl(T::Nat, nat(2));
    k.check_closed(&proof, &T::eq(T::Nat, nat(2), nat(2)))
        .unwrap();
    assert!(
        k.check_closed(&proof, &T::eq(T::Nat, nat(2), nat(3)))
            .is_err()
    );
    assert!(k.infer_closed(&T::eq(T::Nat, T::Nat, T::Zero)).is_err());
    assert!(k.infer_closed(&T::refl(T::Nat, T::universe(0))).is_err());
}
fn induction() -> T {
    T::NatElim {
        motive: Box::new(T::lam(T::Nat, T::eq(T::Nat, T::Var(0), T::Var(0)))),
        zero: Box::new(T::refl(T::Nat, T::Zero)),
        step: Box::new(T::lam(
            T::Nat,
            T::lam(
                T::eq(T::Nat, T::Var(0), T::Var(0)),
                T::refl(T::Nat, T::succ(T::Var(1))),
            ),
        )),
        value: Box::new(nat(3)),
    }
}
#[test]
fn natural_induction_has_a_genuinely_dependent_motive() {
    let k = Kernel::default();
    let proof = induction();
    k.check_closed(&proof, &T::eq(T::Nat, nat(3), nat(3)))
        .unwrap();
    assert_eq!(k.normalize_closed(&proof).unwrap(), T::refl(T::Nat, nat(3)));
    // Normalization under a binder leaves elimination on a neutral variable stuck.
    let T::NatElim {
        motive, zero, step, ..
    } = induction()
    else {
        unreachable!()
    };
    let proof = T::lam(
        T::Nat,
        T::NatElim {
            motive,
            zero,
            step,
            value: Box::new(T::Var(0)),
        },
    );
    let ty = T::pi(T::Nat, T::eq(T::Nat, T::Var(0), T::Var(0)));
    k.check_closed(&proof, &ty).unwrap();
    k.normalize_closed(&proof).unwrap();
}
#[test]
fn induction_checks_every_premise() {
    let k = Kernel::default();
    for field in 0..4 {
        let mut proof = induction();
        let T::NatElim {
            motive,
            zero,
            step,
            value,
        } = &mut proof
        else {
            unreachable!()
        };
        match field {
            0 => **motive = T::Nat,
            1 => **zero = T::Zero,
            2 => **step = T::lam(T::Nat, T::Zero),
            _ => **value = T::Nat,
        }
        assert!(k.infer_closed(&proof).is_err());
    }
}
fn transport() -> T {
    T::Transport {
        ty: Box::new(T::Nat),
        from: Box::new(T::Zero),
        to: Box::new(T::Zero),
        motive: Box::new(T::lam(T::Nat, T::eq(T::Nat, T::Var(0), T::Var(0)))),
        proof: Box::new(T::refl(T::Nat, T::Zero)),
        value: Box::new(T::refl(T::Nat, T::Zero)),
    }
}
#[test]
fn transport_checks_equality_and_transports_the_dependent_type() {
    let k = Kernel::default();
    k.check_closed(&transport(), &T::eq(T::Nat, T::Zero, T::Zero))
        .unwrap();
    assert_eq!(
        k.normalize_closed(&transport()).unwrap(),
        T::refl(T::Nat, T::Zero)
    );
    let mut bad = transport();
    let T::Transport { to, .. } = &mut bad else {
        unreachable!()
    };
    **to = nat(1);
    assert!(k.infer_closed(&bad).is_err());
    let mut bad = transport();
    let T::Transport { value, .. } = &mut bad else {
        unreachable!()
    };
    **value = nat(1);
    assert!(k.infer_closed(&bad).is_err());
}
#[test]
fn opaque_equality_proof_is_not_reduced_to_reflexivity() {
    let k = Kernel::default();
    // Under a proof binder, transport must remain neutral, not pretend that
    // every proof is definitionally reflexivity (no proof irrelevance axiom).
    let body = T::Transport {
        ty: Box::new(T::Nat),
        from: Box::new(T::Zero),
        to: Box::new(T::Zero),
        motive: Box::new(T::lam(T::Nat, T::Nat)),
        proof: Box::new(T::Var(0)),
        value: Box::new(T::Zero),
    };
    let term = T::lam(T::eq(T::Nat, T::Zero, T::Zero), body);
    let normal = k.normalize_closed(&term).unwrap();
    let T::Lam { body, .. } = normal else {
        panic!()
    };
    assert!(matches!(*body, T::Transport { .. }));
}
#[test]
fn global_admission_is_atomic_and_rejects_recursion_or_axioms() {
    let mut k = Kernel::default();
    assert!(k.define("bad".into(), T::Nat, T::Nat).is_err());
    assert!(!k.contains("bad"));
    assert!(k.define("loop".into(), T::Nat, T::global("loop")).is_err());
    assert!(!k.contains("loop"));
    k.define("id".into(), identity_type(), identity()).unwrap();
    let value = T::app(T::app(T::global("id"), T::Nat), nat(2));
    k.define("two".into(), T::Nat, value).unwrap();
    assert_eq!(k.normalize_closed(&T::global("two")).unwrap(), nat(2));
    assert!(k.define("two".into(), T::Nat, T::Zero).is_err());
    assert_eq!(k.definition_type("two"), Some(&T::Nat));
}
#[test]
fn computation_limits_fail_closed() {
    let tiny = Kernel::new(Limits {
        steps: 1,
        depth: 128,
    });
    assert!(
        tiny.infer_closed(&identity())
            .unwrap_err()
            .0
            .contains("budget")
    );
    let shallow = Kernel::new(Limits {
        steps: 10_000,
        depth: 4,
    });
    assert!(
        shallow
            .infer_closed(&(0..10).fold(T::Zero, |n, _| T::succ(n)))
            .unwrap_err()
            .0
            .contains("nesting")
    );
    let mut tiny = Kernel::new(Limits {
        steps: 0,
        depth: 128,
    });
    assert!(tiny.define("zero".into(), T::Nat, T::Zero).is_err());
    assert!(!tiny.contains("zero"));
}

#[test]
fn induction_shifts_a_free_motive_under_both_step_binders() {
    let k = Kernel::default();
    // Generic induction: P, z, and s are variables, not closed syntactic lambdas.
    let motive_type = T::pi(T::Nat, T::universe(0));
    let zero_type = T::app(T::Var(0), T::Zero);
    let step_type = T::pi(
        T::Nat,
        T::pi(
            T::app(T::Var(2), T::Var(0)),
            T::app(T::Var(3), T::succ(T::Var(1))),
        ),
    );
    let term = T::lam(
        motive_type.clone(),
        T::lam(
            zero_type.clone(),
            T::lam(
                step_type.clone(),
                T::lam(
                    T::Nat,
                    T::NatElim {
                        motive: Box::new(T::Var(3)),
                        zero: Box::new(T::Var(2)),
                        step: Box::new(T::Var(1)),
                        value: Box::new(T::Var(0)),
                    },
                ),
            ),
        ),
    );
    let expected = T::pi(
        motive_type,
        T::pi(
            zero_type,
            T::pi(step_type, T::pi(T::Nat, T::app(T::Var(3), T::Var(0)))),
        ),
    );
    k.check_closed(&term, &expected).unwrap();
    let applied = T::app(
        T::app(
            T::app(T::app(term, T::lam(T::Nat, T::Nat)), T::Zero),
            T::lam(T::Nat, T::lam(T::Nat, T::succ(T::Var(0)))),
        ),
        nat(3),
    );
    assert_eq!(k.normalize_closed(&applied).unwrap(), nat(3));
}

#[test]
fn open_checking_validates_hypotheses_instead_of_trusting_them() {
    let k = Kernel::default();
    let hypothesis = T::eq(T::Nat, T::Zero, T::Zero);
    // h : Eq(Nat, 0, 0) |- h : Eq(Nat, 0, 0)
    k.check_open(&T::Var(0), &hypothesis, std::slice::from_ref(&hypothesis))
        .unwrap();
    // A different proposition is not established by that hypothesis.
    assert!(
        k.check_open(
            &T::Var(0),
            &T::eq(T::Nat, T::Zero, T::natural(1u64.into())),
            std::slice::from_ref(&hypothesis),
        )
        .is_err()
    );
    // Context entries must themselves be well-formed types.
    assert!(k.check_open(&T::Var(0), &T::Nat, &[T::Zero]).is_err());
    // Unbound indices remain errors.
    assert!(k.check_open(&T::Var(1), &T::Nat, &[T::Nat]).is_err());
}

use kush::kernel::{ConstructorSpec, DataSpec};
fn vect() -> Kernel {
    let mut k = Kernel::default();
    k.define_data(DataSpec {
        name: "Vect".into(),
        params: vec![T::Nat],
        constructors: vec![
            ConstructorSpec {
                name: "Vect::nil".into(),
                fields: vec![],
                result: vec![T::Zero],
            },
            ConstructorSpec {
                name: "Vect::cons".into(),
                fields: vec![T::Nat, T::app(T::global("Vect"), T::Var(1))],
                result: vec![T::succ(T::Var(2))],
            },
        ],
    })
    .unwrap();
    k
}
fn nil() -> T {
    T::app(T::global("Vect::nil"), T::Zero)
}
fn cons(n: u32, head: T, tail: T) -> T {
    T::app(T::app(T::app(T::global("Vect::cons"), nat(n)), head), tail)
}
fn length_motive() -> T {
    T::lam(T::Nat, T::lam(T::app(T::global("Vect"), T::Var(0)), T::Nat))
}
fn length_branches() -> Vec<T> {
    vec![
        T::lam(T::Nat, T::Zero),
        T::lam(
            T::Nat,
            T::lam(
                T::Nat,
                T::lam(
                    T::app(T::global("Vect"), T::Var(1)),
                    T::lam(T::Nat, T::succ(T::Var(0))),
                ),
            ),
        ),
    ]
}

#[test]
fn positive_logical_data_is_admitted_with_checked_constructors() {
    let k = vect();
    let info = k.data("Vect").unwrap();
    assert_eq!(info.params.len(), 1);
    assert_eq!(info.sort, 0.into());
    assert_eq!(info.constructors.len(), 2);
    assert!(info.constructors[0].recursive.is_empty());
    assert_eq!(info.constructors[1].recursive, [false, true]);
    // Vect : Nat -> Universe(0), constructors are checked globals.
    k.check_closed(&nil(), &T::app(T::global("Vect"), T::Zero))
        .unwrap();
    k.check_closed(&cons(0, nat(5), nil()), &T::app(T::global("Vect"), nat(1)))
        .unwrap();
    assert!(
        k.check_closed(&cons(0, nat(5), nil()), &T::app(T::global("Vect"), nat(2)))
            .is_err()
    );
    assert!(k.data("Vect::nil").is_none());
    assert!(k.data("missing").is_none());
}

#[test]
fn dependent_elimination_reduces_on_constructor_scrutinees() {
    let k = vect();
    let one = cons(0, nat(5), nil());
    let term = T::elim("Vect", length_motive(), length_branches(), one.clone());
    k.check_closed(&term, &T::Nat).unwrap();
    assert_eq!(k.normalize_closed(&term).unwrap(), nat(1));
    let two = cons(1, nat(7), one);
    let term = T::elim("Vect", length_motive(), length_branches(), two);
    assert_eq!(k.normalize_closed(&term).unwrap(), nat(2));
    // The empty constructor branch is selected without evaluating recursion.
    let term = T::elim("Vect", length_motive(), length_branches(), nil());
    assert_eq!(k.normalize_closed(&term).unwrap(), T::Zero);
}

#[test]
fn elimination_on_a_neutral_scrutinee_stays_stuck() {
    let k = vect();
    let body = T::elim("Vect", length_motive(), length_branches(), T::Var(0));
    let term = T::lam(T::app(T::global("Vect"), T::Zero), body);
    let expected = T::pi(T::app(T::global("Vect"), T::Zero), T::Nat);
    k.check_closed(&term, &expected).unwrap();
    let normal = k.normalize_closed(&term).unwrap();
    let T::Lam { body, .. } = normal else {
        panic!()
    };
    assert!(matches!(*body, T::IndElim { .. }));
}

#[test]
fn elimination_checks_motive_branches_and_scrutinee() {
    let k = vect();
    let scrutinee = cons(0, nat(5), nil());
    // Wrong branch count.
    let bad = T::elim(
        "Vect",
        length_motive(),
        vec![T::lam(T::Nat, T::Zero)],
        scrutinee.clone(),
    );
    assert!(k.infer_closed(&bad).is_err());
    // Motive that does not take the eliminated value.
    let bad = T::elim(
        "Vect",
        T::lam(T::Nat, T::Nat),
        length_branches(),
        scrutinee.clone(),
    );
    assert!(k.infer_closed(&bad).is_err());
    // Branch of the wrong type.
    let bad = T::elim(
        "Vect",
        length_motive(),
        vec![T::lam(T::Nat, T::Zero), T::lam(T::Nat, T::Zero)],
        scrutinee.clone(),
    );
    assert!(k.infer_closed(&bad).is_err());
    // Scrutinee of another type.
    let bad = T::elim("Vect", length_motive(), length_branches(), nat(3));
    assert!(k.infer_closed(&bad).is_err());
    // Unknown family.
    let bad = T::elim("Missing", length_motive(), vec![], scrutinee);
    assert!(k.infer_closed(&bad).is_err());
}

#[test]
fn negative_nested_and_malformed_data_are_rejected_atomically() {
    let mut k = Kernel::default();
    let reject =
        |k: &mut Kernel, name: &str, params: Vec<T>, constructors: Vec<ConstructorSpec>| {
            let error = k
                .define_data(DataSpec {
                    name: name.into(),
                    params,
                    constructors,
                })
                .unwrap_err();
            assert!(!k.contains(name));
            error
        };
    // Negative occurrence: Bad appears in the domain of a field function.
    let error = reject(
        &mut k,
        "Bad",
        vec![],
        vec![ConstructorSpec {
            name: "Bad::mk".into(),
            fields: vec![T::pi(T::global("Bad"), T::Nat)],
            result: vec![],
        }],
    );
    assert!(error.0.contains("non-strictly-positive"), "{error}");
    // Nested occurrence inside another admitted family.
    let mut nested = vect();
    let error = nested
        .define_data(DataSpec {
            name: "Nested".into(),
            params: vec![],
            constructors: vec![ConstructorSpec {
                name: "Nested::mk".into(),
                fields: vec![T::app(T::global("Vect"), T::global("Nested"))],
                result: vec![],
            }],
        })
        .unwrap_err();
    assert!(error.0.contains("non-strictly-positive"), "{error}");
    assert!(!nested.contains("Nested"));
    // A direct recursive field whose index mentions the family.
    let error = reject(
        &mut k,
        "Indexed",
        vec![T::universe(0)],
        vec![ConstructorSpec {
            name: "Indexed::mk".into(),
            fields: vec![T::app(T::global("Indexed"), T::global("Indexed"))],
            result: vec![T::Var(0)],
        }],
    );
    assert!(error.0.contains("non-strictly-positive"), "{error}");
    // Self-reference in a parameter/kind.
    let error = reject(&mut k, "SelfParam", vec![T::global("SelfParam")], vec![]);
    assert!(error.0.contains("own parameter"), "{error}");
    // Result arity.
    let error = reject(
        &mut k,
        "Arity",
        vec![T::Nat],
        vec![ConstructorSpec {
            name: "Arity::mk".into(),
            fields: vec![],
            result: vec![],
        }],
    );
    assert!(error.0.contains("exactly 1 index"), "{error}");
    // Malformed result index type.
    let error = reject(
        &mut k,
        "Malformed",
        vec![T::Nat],
        vec![ConstructorSpec {
            name: "Malformed::mk".into(),
            fields: vec![],
            result: vec![T::global("Vect")],
        }],
    );
    assert!(error.0.contains("unknown kernel global"), "{error}");
    // Duplicate constructors and collisions with existing globals.
    let error = k
        .define_data(DataSpec {
            name: "Duplicate".into(),
            params: vec![],
            constructors: vec![
                ConstructorSpec {
                    name: "Duplicate::mk".into(),
                    fields: vec![],
                    result: vec![],
                },
                ConstructorSpec {
                    name: "Duplicate::mk".into(),
                    fields: vec![],
                    result: vec![],
                },
            ],
        })
        .unwrap_err();
    assert!(error.0.contains("duplicate constructor"), "{error}");
    assert!(!k.contains("Duplicate"));
    k.define("taken".into(), T::Nat, T::Zero).unwrap();
    let error = k
        .define_data(DataSpec {
            name: "Collision".into(),
            params: vec![],
            constructors: vec![ConstructorSpec {
                name: "taken".into(),
                fields: vec![],
                result: vec![],
            }],
        })
        .unwrap_err();
    assert!(error.0.contains("collides"), "{error}");
    assert!(!k.contains("Collision"));
}

#[test]
fn empty_data_families_are_sound_and_have_zero_branches() {
    let mut k = Kernel::default();
    k.define_data(DataSpec {
        name: "Void".into(),
        params: vec![],
        constructors: vec![],
    })
    .unwrap();
    assert!(k.data("Void").unwrap().constructors.is_empty());
    let motive = T::lam(T::global("Void"), T::Nat);
    let term = T::elim("Void", motive, vec![], T::Var(0));
    k.check_open(&term, &T::Nat, &[T::global("Void")]).unwrap();
}

#[test]
fn equality_elimination_j_checks_and_reduces() {
    let k = Kernel::default();
    let motive = T::lam(T::Nat, T::lam(T::eq(T::Nat, T::Zero, T::Var(0)), T::Nat));
    let proof = T::refl(T::Nat, T::Zero);
    let term = T::eq_elim(T::Nat, T::Zero, T::Zero, motive.clone(), nat(7), proof);
    k.check_closed(&term, &T::Nat).unwrap();
    assert_eq!(k.normalize_closed(&term).unwrap(), nat(7));
    // A non-reflexivity proof stays neutral.
    let body = T::eq_elim(T::Nat, T::Zero, T::Var(1), motive, nat(7), T::Var(0));
    let term = T::lam(T::Nat, T::lam(T::eq(T::Nat, T::Zero, T::Var(0)), body));
    k.check_closed(
        &term,
        &T::pi(T::Nat, T::pi(T::eq(T::Nat, T::Zero, T::Var(0)), T::Nat)),
    )
    .unwrap();
    let T::Lam { body, .. } = k.normalize_closed(&term).unwrap() else {
        panic!()
    };
    let T::Lam { body, .. } = *body else { panic!() };
    assert!(matches!(*body, T::EqElim { .. }));
    // Wrong reflection case, wrong proof, and a motive without the proof argument.
    let bad = T::eq_elim(
        T::Nat,
        T::Zero,
        T::Zero,
        T::lam(T::Nat, T::lam(T::eq(T::Nat, T::Zero, T::Var(0)), T::Nat)),
        T::universe(0),
        T::refl(T::Nat, T::Zero),
    );
    assert!(k.infer_closed(&bad).is_err());
    let bad = T::eq_elim(
        T::Nat,
        T::Zero,
        nat(1),
        T::lam(T::Nat, T::lam(T::eq(T::Nat, T::Zero, T::Var(0)), T::Nat)),
        nat(7),
        T::refl(T::Nat, T::Zero),
    );
    assert!(k.infer_closed(&bad).is_err());
    let bad = T::eq_elim(
        T::Nat,
        T::Zero,
        T::Zero,
        T::lam(T::Nat, T::Nat),
        nat(7),
        T::refl(T::Nat, T::Zero),
    );
    assert!(k.infer_closed(&bad).is_err());
}

#[test]
fn constructor_results_may_depend_on_field_values_at_the_kernel_level() {
    let mut k = Kernel::default();
    k.define_data(DataSpec {
        name: "Dep".into(),
        params: vec![T::Nat],
        constructors: vec![ConstructorSpec {
            name: "Dep::mk".into(),
            fields: vec![T::Nat],
            result: vec![T::Var(0)],
        }],
    })
    .unwrap();
    // mk 0 3 : Dep 3, because the result index is the field itself.
    let value = T::app(T::app(T::global("Dep::mk"), T::Zero), nat(3));
    k.check_closed(&value, &T::app(T::global("Dep"), nat(3)))
        .unwrap();
    let motive = T::lam(T::Nat, T::lam(T::app(T::global("Dep"), T::Var(0)), T::Nat));
    let branch = T::lam(T::Nat, T::lam(T::Nat, T::Var(0)));
    let term = T::elim("Dep", motive, vec![branch], value);
    assert_eq!(k.normalize_closed(&term).unwrap(), nat(3));
}

#[test]
fn data_admission_obeys_the_computation_budget_atomically() {
    let spec = DataSpec {
        name: "Budgeted".into(),
        params: vec![T::Nat],
        constructors: vec![ConstructorSpec {
            name: "Budgeted::mk".into(),
            fields: vec![],
            result: vec![T::Var(0)],
        }],
    };
    let mut tiny = Kernel::new(Limits {
        steps: 0,
        depth: 128,
    });
    let error = tiny.define_data(spec.clone()).unwrap_err();
    assert!(error.0.contains("budget"), "{error}");
    assert!(!tiny.contains("Budgeted"));
    let mut shallow = Kernel::new(Limits {
        steps: 100_000,
        depth: 1,
    });
    assert!(shallow.define_data(spec).is_err());
    assert!(!shallow.contains("Budgeted"));
}

#[test]
fn data_universes_are_derived_instead_of_escaping() {
    let mut k = Kernel::default();
    // A field in Universe(1) raises the family to Universe(1); it is not
    // silently truncated to Universe(0), and the family cannot inhabit itself.
    k.define_data(DataSpec {
        name: "Large".into(),
        params: vec![],
        constructors: vec![ConstructorSpec {
            name: "Large::mk".into(),
            fields: vec![T::universe(0)],
            result: vec![],
        }],
    })
    .unwrap();
    assert_eq!(k.data("Large").unwrap().sort, 1.into());
    k.check_closed(&T::global("Large"), &T::universe(1))
        .unwrap();
    assert!(
        k.check_closed(&T::global("Large"), &T::universe(0))
            .is_err()
    );
    // Small data remains small even with a Type-valued index parameter.
    let mut k = Kernel::default();
    k.define_data(DataSpec {
        name: "Phantom".into(),
        params: vec![T::universe(0)],
        constructors: vec![ConstructorSpec {
            name: "Phantom::mk".into(),
            fields: vec![],
            result: vec![T::Var(0)],
        }],
    })
    .unwrap();
    assert_eq!(k.data("Phantom").unwrap().sort, 0.into());
    k.check_closed(
        &T::app(T::global("Phantom::mk"), T::Nat),
        &T::app(T::global("Phantom"), T::Nat),
    )
    .unwrap();
}

use kush::kernel::{IndexedConstructorSpec, IndexedDataSpec, Sort};

fn fin() -> Kernel {
    let mut k = Kernel::default();
    k.define_indexed_data(IndexedDataSpec {
        name: "Fin".into(),
        params: vec![T::Nat],
        prop: false,
        levels: 0,
        constructors: vec![
            IndexedConstructorSpec {
                name: "Fin::fzero".into(),
                locals: vec![T::Nat],
                fields: vec![],
                result: vec![T::succ(T::Var(0))],
            },
            IndexedConstructorSpec {
                name: "Fin::fsucc".into(),
                locals: vec![T::Nat],
                fields: vec![T::app(T::global("Fin"), T::Var(0))],
                result: vec![T::succ(T::Var(1))],
            },
        ],
    })
    .unwrap();
    k
}
fn fin_fzero(n: u32, m: u32) -> T {
    T::app(T::app(T::global("Fin::fzero"), nat(n)), nat(m))
}
fn fin_fsucc(n: u32, m: u32, pred: T) -> T {
    T::app(
        T::app(T::app(T::global("Fin::fsucc"), nat(n)), nat(m)),
        pred,
    )
}
fn fin_type(n: u32) -> T {
    T::app(T::global("Fin"), nat(n))
}

#[test]
fn constructor_local_binders_produce_finite_index_values() {
    let k = fin();
    let info = k.data("Fin").unwrap();
    assert_eq!(info.params.len(), 1);
    assert_eq!(info.constructors[0].locals, [T::Nat]);
    assert_eq!(info.constructors[1].locals, [T::Nat]);
    // fzero n has result index succ n, independently of the family parameter.
    k.check_closed(&fin_fzero(9, 1), &fin_type(2)).unwrap();
    assert!(
        k.check_closed(&fin_fzero(9, 1), &fin_type(3)).is_err(),
        "the declared family parameter is not the result index"
    );
    // fsucce n pred has result index succ n, with pred : Fin n.
    let value = fin_fsucc(3, 2, fin_fzero(1, 1));
    k.check_closed(&value, &fin_type(3)).unwrap();
    assert!(k.check_closed(&value, &fin_type(2)).is_err());
    // The predecessor field must have exactly the local index.
    assert!(
        k.check_closed(&fin_fsucc(3, 2, fin_fzero(1, 0)), &fin_type(3))
            .is_err()
    );
}

#[test]
fn elimination_over_constructor_local_binders_checks_and_reduces() {
    let k = fin();
    let motive = T::lam(T::Nat, T::lam(T::app(T::global("Fin"), T::Var(0)), T::Nat));
    // (N) -> (n) -> Nat
    let zero_branch = T::lam(T::Nat, T::lam(T::Nat, T::Zero));
    // (N) -> (n) -> (pred : Fin n) -> (motive n pred) -> Nat
    let succ_branch = T::lam(
        T::Nat,
        T::lam(
            T::Nat,
            T::lam(
                T::app(T::global("Fin"), T::Var(0)),
                T::lam(T::Nat, T::succ(T::Var(0))),
            ),
        ),
    );
    let value = fin_fsucc(3, 2, fin_fzero(1, 1));
    let term = T::elim(
        "Fin",
        motive.clone(),
        vec![zero_branch.clone(), succ_branch],
        value,
    );
    k.check_closed(&term, &T::Nat).unwrap();
    assert_eq!(k.normalize_closed(&term).unwrap(), nat(1));
    // A branch that ignores the constructor-local telescope is still checked
    // against the full branch type.
    let bad = T::elim(
        "Fin",
        motive.clone(),
        vec![zero_branch, T::lam(T::Nat, T::Zero)],
        fin_fzero(1, 1),
    );
    assert!(k.infer_closed(&bad).is_err());
    // Wrong motive index domain.
    let bad = T::elim(
        "Fin",
        T::lam(T::universe(0), T::Nat),
        vec![],
        fin_fzero(1, 1),
    );
    assert!(k.infer_closed(&bad).is_err());
}

#[test]
fn prop_is_a_sort_not_a_member_of_itself_and_is_impredicative() {
    let k = Kernel::default();
    assert_eq!(k.infer_closed(&T::Prop).unwrap(), T::universe(0));
    assert!(k.check_closed(&T::Prop, &T::Prop).is_err());
    // `Prop` is a Type at level 0; it is not itself a proposition, and there
    // is no cumulativity to higher Type levels.
    k.check_closed(&T::Prop, &T::universe(0)).unwrap();
    assert!(k.check_closed(&T::Prop, &T::universe(1)).is_err());
    // `Prop` is itself a sort/type, not a proposition: quantifying over a
    // universe and returning the sort `Prop` is a Type-level function.
    assert_eq!(
        k.sort_closed(&T::pi(T::universe(3), T::Prop)).unwrap(),
        Sort::Type(4.into())
    );
    // Prop is impredicative: quantification into an actual proposition stays
    // in Prop, regardless of the domain's universe.
    let props = true_prop();
    assert_eq!(
        props
            .sort_closed(&T::pi(T::universe(3), T::global("True")))
            .unwrap(),
        Sort::Prop
    );
    assert_eq!(
        props
            .sort_closed(&T::pi(T::Prop, T::global("True")))
            .unwrap(),
        Sort::Prop
    );
    // But predicative Type-valued quantification still raises the level.
    assert_eq!(
        k.sort_closed(&T::pi(T::universe(3), T::universe(0)))
            .unwrap(),
        Sort::Type(4.into())
    );
    assert_eq!(
        k.sort_closed(&T::pi(T::Prop, T::universe(0))).unwrap(),
        Sort::Type(1.into())
    );
}

fn true_prop() -> Kernel {
    let mut k = Kernel::default();
    k.define_indexed_data(IndexedDataSpec {
        name: "True".into(),
        params: vec![],
        prop: true,
        levels: 0,
        constructors: vec![IndexedConstructorSpec {
            name: "True::trivial".into(),
            locals: vec![],
            fields: vec![],
            result: vec![],
        }],
    })
    .unwrap();
    k
}
fn two_prop() -> Kernel {
    let mut k = true_prop();
    k.define_indexed_data(IndexedDataSpec {
        name: "Two".into(),
        params: vec![],
        prop: true,
        levels: 0,
        constructors: vec![
            IndexedConstructorSpec {
                name: "Two::first".into(),
                locals: vec![],
                fields: vec![],
                result: vec![],
            },
            IndexedConstructorSpec {
                name: "Two::second".into(),
                locals: vec![],
                fields: vec![],
                result: vec![],
            },
        ],
    })
    .unwrap();
    // A Type-valued family indexed by a proof.
    k.define_indexed_data(IndexedDataSpec {
        name: "Indexed".into(),
        params: vec![T::global("Two")],
        prop: false,
        levels: 0,
        constructors: vec![IndexedConstructorSpec {
            name: "Indexed::mk".into(),
            locals: vec![],
            fields: vec![],
            result: vec![T::Var(0)],
        }],
    })
    .unwrap();
    k
}

#[test]
fn proof_irrelevance_is_limited_to_prop_inhabitants() {
    let k = two_prop();
    let first = T::global("Two::first");
    let second = T::global("Two::second");
    assert!(k.proof_closed(&first).unwrap());
    assert!(k.proof_closed(&second).unwrap());
    assert!(!k.proof_closed(&T::Zero).unwrap());
    assert!(!k.proof_closed(&T::succ(T::Zero)).unwrap());
    assert!(!k.proof_closed(&T::Nat).unwrap());
    // Type-valued functions and functions returning the *sort* Prop are not
    // proofs either.
    assert!(!k.proof_closed(&T::lam(T::Nat, T::Zero)).unwrap());
    assert!(!k.proof_closed(&T::pi(T::Nat, T::Prop)).unwrap());
    // mk first : Indexed first is accepted where Indexed second is expected.
    let mk_first = T::app(T::global("Indexed::mk"), first.clone());
    let indexed_second = T::app(T::global("Indexed"), second.clone());
    k.check_closed(&mk_first, &indexed_second).unwrap();
    // But two different propositions are not interchangeable.
    let indexed_true = T::app(T::global("Indexed"), T::global("True"));
    assert!(k.check_closed(&mk_first, &indexed_true).is_err());
    // Type-valued indices remain distinct; Nat values are not proofs.
    let mut at = two_prop();
    at.define_indexed_data(IndexedDataSpec {
        name: "At".into(),
        params: vec![T::Nat],
        prop: false,
        levels: 0,
        constructors: vec![IndexedConstructorSpec {
            name: "At::mk".into(),
            locals: vec![],
            fields: vec![],
            result: vec![T::Var(0)],
        }],
    })
    .unwrap();
    let mk_zero = T::app(T::global("At::mk"), T::Zero);
    assert!(
        at.check_closed(&mk_zero, &T::app(T::global("At"), nat(1)))
            .is_err()
    );
}

#[test]
fn prop_elimination_into_type_is_rejected_but_prop_motives_work() {
    let k = two_prop();
    let first = T::global("Two::first");
    let second = T::global("Two::second");
    let type_motive = T::lam(T::global("Two"), T::Nat);
    let term = T::elim("Two", type_motive, vec![T::Zero, nat(1)], first.clone());
    let error = k.infer_closed(&term).unwrap_err();
    assert!(error.0.contains("large elimination"), "{error}");
    // The same family can be eliminated into a proposition.
    let true_motive = T::lam(T::global("Two"), T::global("True"));
    let branch = T::global("True::trivial");
    let term = T::elim("Two", true_motive, vec![branch.clone(), branch], first);
    k.check_closed(&term, &T::global("True")).unwrap();
    // Reduction still selects the constructor branch.
    assert_eq!(
        k.normalize_closed(&term).unwrap(),
        T::global("True::trivial")
    );
    let _ = second;
}

#[test]
fn malformed_prop_and_local_data_declarations_are_rejected_atomically() {
    let mut k = Kernel::default();
    // A Type-valued value cannot be a constructor field of a prop.
    let error = k
        .define_indexed_data(IndexedDataSpec {
            name: "BadField".into(),
            params: vec![],
            prop: true,
            levels: 0,
            constructors: vec![IndexedConstructorSpec {
                name: "BadField::mk".into(),
                locals: vec![],
                fields: vec![T::Zero],
                result: vec![],
            }],
        })
        .unwrap_err();
    assert!(error.0.contains("expected a type"), "{error}");
    assert!(!k.contains("BadField"));
    // Constructor-local binders may not mention the family.
    let error = k
        .define_indexed_data(IndexedDataSpec {
            name: "BadLocal".into(),
            params: vec![],
            prop: true,
            levels: 0,
            constructors: vec![IndexedConstructorSpec {
                name: "BadLocal::mk".into(),
                locals: vec![T::global("BadLocal")],
                fields: vec![],
                result: vec![],
            }],
        })
        .unwrap_err();
    assert!(error.0.contains("constructor-local binder"), "{error}");
    assert!(!k.contains("BadLocal"));
    // A result index with the wrong type is rejected, not coerced.
    let error = k
        .define_indexed_data(IndexedDataSpec {
            name: "BadResult".into(),
            params: vec![T::Nat],
            prop: false,
            levels: 0,
            constructors: vec![IndexedConstructorSpec {
                name: "BadResult::mk".into(),
                locals: vec![],
                fields: vec![],
                result: vec![T::Nat],
            }],
        })
        .unwrap_err();
    assert!(error.0.contains("type mismatch"), "{error}");
    assert!(!k.contains("BadResult"));
    // Duplicate local names are not kernel-level constructs, but duplicate
    // constructor names still fail atomically.
    let error = k
        .define_indexed_data(IndexedDataSpec {
            name: "Duplicate".into(),
            params: vec![],
            prop: true,
            levels: 0,
            constructors: vec![
                IndexedConstructorSpec {
                    name: "Duplicate::mk".into(),
                    locals: vec![],
                    fields: vec![],
                    result: vec![],
                },
                IndexedConstructorSpec {
                    name: "Duplicate::mk".into(),
                    locals: vec![],
                    fields: vec![],
                    result: vec![],
                },
            ],
        })
        .unwrap_err();
    assert!(error.0.contains("duplicate constructor"), "{error}");
    assert!(!k.contains("Duplicate"));
}

#[test]
fn constructor_local_universes_raise_type_valued_families() {
    let mut k = Kernel::default();
    k.define_indexed_data(IndexedDataSpec {
        name: "Code".into(),
        params: vec![],
        prop: false,
        levels: 0,
        constructors: vec![IndexedConstructorSpec {
            name: "Code::mk".into(),
            // The local is a type at level 0, so it can be exposed by
            // elimination and the family must not remain in Universe(0).
            locals: vec![T::universe(0)],
            fields: vec![],
            result: vec![],
        }],
    })
    .unwrap();
    assert_eq!(k.data("Code").unwrap().sort, 1.into());
    k.check_closed(&T::global("Code"), &T::universe(1)).unwrap();
    assert!(k.check_closed(&T::global("Code"), &T::universe(0)).is_err());
    // A Prop family ignores local universe levels because elimination stays
    // inside Prop.
    let mut props = Kernel::default();
    props
        .define_indexed_data(IndexedDataSpec {
            name: "PropCode".into(),
            params: vec![],
            prop: true,
            levels: 0,
            constructors: vec![IndexedConstructorSpec {
                name: "PropCode::mk".into(),
                locals: vec![T::universe(0)],
                fields: vec![],
                result: vec![],
            }],
        })
        .unwrap();
    assert!(props.data("PropCode").unwrap().prop);
    assert_eq!(
        props.sort_closed(&T::global("PropCode")).unwrap(),
        Sort::Prop
    );
}

#[test]
fn open_sort_and_proof_classification_validate_the_context() {
    let k = two_prop();
    // P : Prop, p : P
    let context = vec![T::Prop, T::Var(0)];
    // P is a proposition; p is a proof; P is not itself a proof.
    assert_eq!(k.sort_open(&T::Var(1), &context).unwrap(), Sort::Prop);
    assert!(k.proof_open(&T::Var(0), &context).unwrap());
    assert!(!k.proof_open(&T::Var(1), &context).unwrap());
    // A value is not a well-formed hypothesis type.
    assert!(k.sort_open(&T::Prop, &[T::Zero]).is_err());
    assert!(k.proof_open(&T::Var(0), &[T::Zero]).is_err());
}

#[test]
fn machine_scalar_carriers_are_checked_symbolic_indices_not_proofs() {
    let k = Kernel::default();
    // Carriers are ordinary types and literals have the matching carrier.
    assert_eq!(k.infer_closed(&T::i64_type()).unwrap(), T::universe(0));
    assert_eq!(k.infer_closed(&T::bool_type()).unwrap(), T::universe(0));
    assert_eq!(k.infer_closed(&T::unit_type()).unwrap(), T::universe(0));
    assert_eq!(k.infer_closed(&T::i64(i64::MIN)).unwrap(), T::i64_type());
    assert_eq!(k.infer_closed(&T::i64(i64::MAX)).unwrap(), T::i64_type());
    assert_eq!(k.infer_closed(&T::boolean(true)).unwrap(), T::bool_type());
    assert_eq!(k.infer_closed(&T::unit()).unwrap(), T::unit_type());

    // Equality over a machine carrier is Type-valued, so it is not proof
    // irrelevance and cannot be mistaken for a proposition.
    assert_eq!(
        k.sort_closed(&T::eq(T::i64_type(), T::i64(3), T::i64(3)))
            .unwrap(),
        kush::kernel::Sort::Type(0.into())
    );
    let proof = T::refl(T::i64_type(), T::i64(3));
    k.check_closed(&proof, &T::eq(T::i64_type(), T::i64(3), T::i64(3)))
        .unwrap();
    assert!(
        k.check_closed(&proof, &T::eq(T::i64_type(), T::i64(3), T::i64(4)))
            .is_err()
    );

    // A runtime scalar is an open symbolic value, not a proof. `n : i64`
    // supports `refl<i64>(n) : Eq<i64, n, n>` but cannot inhabit a proposition.
    let context = vec![T::i64_type()];
    k.check_open(
        &T::refl(T::i64_type(), T::Var(0)),
        &T::eq(T::i64_type(), T::Var(0), T::Var(0)),
        &context,
    )
    .unwrap();
    assert!(!k.proof_open(&T::Var(0), &context).unwrap());
    assert_eq!(k.normalize_open(&T::Var(0), &context).unwrap(), T::Var(0));

    // There is no machine arithmetic, cast, elimination, or implicit Nat
    // conversion in the kernel.
    for term in [
        T::app(T::i64_type(), T::i64(1)),
        T::succ(T::i64(1)),
        T::eq(T::i64_type(), T::i64(1), T::natural(1u64.into())),
        T::eq(T::bool_type(), T::boolean(true), T::i64(1)),
    ] {
        assert!(k.infer_closed(&term).is_err(), "{term:?}");
    }
    assert!(
        k.check_open(&T::boolean(true), &T::i64_type(), &[])
            .is_err()
    );
    // A scalar value is not a valid hypothesis type either.
    assert!(k.sort_open(&T::Prop, &[T::i64(1)]).is_err());
}

#[test]
fn functions_are_convertible_up_to_eta() {
    let k = Kernel::default();
    let arrow = T::pi(T::Nat, T::Nat);
    // f : Nat -> Nat ⊢ refl(f) : Eq(Nat -> Nat, λx. f x, f), in both orders.
    let eta = T::lam(T::Nat, T::app(T::Var(1), T::Var(0)));
    let context = vec![arrow.clone()];
    for (left, right) in [(eta.clone(), T::Var(0)), (T::Var(0), eta.clone())] {
        k.check_open(
            &T::refl(arrow.clone(), T::Var(0)),
            &T::eq(arrow.clone(), left, right),
            &context,
        )
        .unwrap();
    }
    // Nested: λx. λy. g x y ≡ g for g : Nat -> Nat -> Nat.
    let binary = T::pi(T::Nat, T::pi(T::Nat, T::Nat));
    let nested = T::lam(
        T::Nat,
        T::lam(T::Nat, T::app(T::app(T::Var(2), T::Var(1)), T::Var(0))),
    );
    k.check_open(
        &T::refl(binary.clone(), T::Var(0)),
        &T::eq(binary.clone(), nested, T::Var(0)),
        std::slice::from_ref(&binary),
    )
    .unwrap();
    // Eta through a global: λx. succ' x ≡ succ' for a defined function.
    let mut k = Kernel::default();
    k.define(
        "succ'".into(),
        arrow.clone(),
        T::lam(T::Nat, T::succ(T::Var(0))),
    )
    .unwrap();
    let global = T::global("succ'");
    k.check_closed(
        &T::refl(arrow.clone(), global.clone()),
        &T::eq(
            arrow.clone(),
            T::lam(T::Nat, T::app(global.clone(), T::Var(0))),
            global,
        ),
    )
    .unwrap();
}

#[test]
fn eta_does_not_identify_different_functions() {
    let k = Kernel::default();
    let arrow = T::pi(T::Nat, T::Nat);
    let context = vec![arrow.clone(), arrow.clone()];
    // Context: f = Var(1), g = Var(0); under one more binder f = Var(2).
    // λx. f x is not g, λx. f (succ x) is not f, and λx. f (f x) is not f.
    for (left, right) in [
        (T::lam(T::Nat, T::app(T::Var(2), T::Var(0))), T::Var(0)),
        (
            T::lam(T::Nat, T::app(T::Var(2), T::succ(T::Var(0)))),
            T::Var(1),
        ),
        (
            T::lam(T::Nat, T::app(T::Var(2), T::app(T::Var(2), T::Var(0)))),
            T::Var(1),
        ),
    ] {
        // Both sides are well-typed, so only conversion can fail.
        k.check_open(&left, &arrow, &context).unwrap();
        assert!(
            k.check_open(
                &T::refl(arrow.clone(), left.clone()),
                &T::eq(arrow.clone(), left.clone(), right.clone()),
                &context,
            )
            .is_err(),
            "{left:?} ~ {right:?}"
        );
    }
}

#[test]
fn deep_terms_grow_the_stack_instead_of_overflowing_it() {
    // A test thread has a 2 MiB stack; these recurse tens of thousands of
    // levels deep, so the kernel must continue on stacks of its own.
    let k = Kernel::default();
    let unary = (0..60_000).fold(T::Zero, |n, _| T::succ(n));
    assert_eq!(k.normalize_closed(&unary).unwrap(), nat(60_000));
    let count = T::NatElim {
        motive: Box::new(T::lam(T::Nat, T::Nat)),
        zero: Box::new(T::Zero),
        step: Box::new(T::lam(T::Nat, T::lam(T::Nat, T::succ(T::Var(0))))),
        value: Box::new(nat(20_000)),
    };
    assert_eq!(k.normalize_closed(&count).unwrap(), nat(20_000));
    // The nesting cap still turns a pathological depth into an error.
    let shallow = Kernel::new(Limits {
        steps: 100_000_000,
        depth: 1_000,
    });
    assert!(
        shallow
            .normalize_closed(&unary)
            .unwrap_err()
            .0
            .contains("nesting")
    );
}

#[test]
#[ignore = "measurement: cargo test --release -- --ignored kernel_throughput --nocapture"]
fn kernel_throughput() {
    let k = Kernel::new(Limits {
        steps: usize::MAX,
        depth: 1_000_000,
    });
    let count = T::NatElim {
        motive: Box::new(T::lam(T::Nat, T::Nat)),
        zero: Box::new(T::Zero),
        step: Box::new(T::lam(T::Nat, T::lam(T::Nat, T::succ(T::Var(0))))),
        value: Box::new(nat(100_000)),
    };
    let start = std::time::Instant::now();
    k.normalize_closed(&count).unwrap();
    let elapsed = start.elapsed();
    let mut budget = Kernel::new(Limits {
        steps: 1,
        depth: 1_000_000,
    });
    // Find the steps it used by bisection on the budget.
    let (mut low, mut high) = (1usize, 1usize << 40);
    while low < high {
        let mid = (low + high) / 2;
        budget = Kernel::new(Limits {
            steps: mid,
            depth: 1_000_000,
        });
        if budget.normalize_closed(&count).is_ok() {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    let _ = budget;
    eprintln!(
        "{low} steps in {elapsed:?}: {:.1} M steps/s",
        low as f64 / elapsed.as_secs_f64() / 1e6
    );
}
