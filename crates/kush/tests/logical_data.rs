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

/// Indexed vectors with a checked length function and a dependent proof.
const VECT: &str = r#"
    total enum Vect<T: Type, N: Nat> {
        Nil: Vect<T, 0>,
        Cons(T, Vect<T, N>): Vect<T, Nat.succ<N>>,
    }
    type LengthMotive<T: Type, N: Nat, v: Vect<T, N>> = Nat;
    total fn nil_length<T: Type, N: Nat>() -> Nat ! {} { 0 }
    total fn cons_length<T: Type, N: Nat>(x: T, xs: Vect<T, N>, ih: Nat) -> Nat ! {} {
        Nat.succ(ih)
    }
    total fn length<T: Type, N: Nat>(v: Vect<T, N>) -> Nat ! {} {
        Data.elim::<Vect>(LengthMotive, nil_length, cons_length, v)
    }
    total fn two() -> Vect<Nat, 2> ! {} {
        Vect.Cons::<Nat, 1>(1, Vect.Cons::<Nat, 0>(2, Vect.Nil::<Nat, 0>))
    }
    total fn zero() -> Vect<Nat, 0> ! {} { Vect.Nil::<Nat, 0> }
    total fn length_two() -> Eq<Nat, length<Nat, 2, two>, 2> ! {} { refl::<Nat>(2) }
"#;

#[test]
fn indexed_logical_data_is_erased_but_feeds_checked_signatures() {
    let source = format!(
        "{VECT}
        fn consume(erased v: Vect<Nat, 2>) -> i64 ! {{}} {{ 42 }}
        fn main() -> i64 ! {{panic}} {{ consume(two()) }}"
    );
    let program = checked(&source);
    assert_eq!(program.function_count(), 2); // consume, main
    let mut logical = program.logical_definitions().to_vec();
    logical.sort();
    assert!(logical.contains(&"Vect".to_owned()));
    assert!(logical.contains(&"length".to_owned()));
    // Constructors are kernel globals but not source-level definitions.
    assert!(!logical.iter().any(|name| name.contains("::Cons")));
    assert_eq!(evaluate(&source), 42);
    let (value, stats) = checked(&source)
        .evaluate_with_stats(&mut Vec::new())
        .unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, stats.deallocations);
}

#[test]
fn dependent_erased_signatures_consume_indexed_evidence() {
    let source = format!(
        "{VECT}
        fn consume_at(erased n: Nat, erased v: Vect<Nat, n>) -> i64 ! {{}} {{ 7 }}
        fn outer(erased n: Nat, erased v: Vect<Nat, n>) -> i64 ! {{}}
            {{ consume_at(n, v) }}
        fn main() -> i64 ! {{panic}}
            {{ consume_at(2, two()) + consume_at(0, zero()) + outer(0, zero()) }}"
    );
    assert_eq!(evaluate(&source), 21);
}

#[test]
fn wrong_indexes_and_runtime_uses_of_logical_data_are_rejected() {
    rejects(
        &format!(
            "{VECT}
             fn consume(erased v: Vect<Nat, 3>) -> i64 ! {{}} {{ 1 }}
             fn main() -> i64 ! {{}} {{ consume(two()) }}"
        ),
        "proof does not establish",
    );
    // A logical data type has no runtime representation.
    rejects(
        &format!(
            "{VECT}
             fn consume(v: Vect<Nat, 2>) -> i64 ! {{}} {{ 1 }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "erased before runtime lowering",
    );
    rejects(
        &format!(
            "{VECT}
             fn bad() -> i64 ! {{}} {{ length(two()) }}
             fn main() -> i64 ! {{}} {{ bad() }}"
        ),
        "erased",
    );
    // A logical constructor is not a runtime constructor.
    rejects(
        &format!(
            "{VECT}
             fn main() -> i64 ! {{}} {{ Vect.Nil::<Nat, 0> }}"
        ),
        "no runtime value",
    );
}

#[test]
fn partial_code_and_owning_data_cannot_enter_logical_data() {
    rejects(
        "enum Runtime { A }
         total enum Logical { Mk(Runtime): Logical }
         fn main() -> i64 ! {} { 0 }",
        "runtime values cannot enter erased proofs",
    );
    rejects(
        "enum Runtime { A }
         total fn bad(r: Runtime) -> Nat ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "runtime values cannot enter erased proofs",
    );
    rejects(
        "total enum Even { EvenZero: Even, EvenSucc(Even): Even }
         fn partial(e: Even) -> Even ! {} { e }
         total fn bad() -> Even ! {} { partial(EvenZero) }
         fn main() -> i64 ! {} { 0 }",
        "depends on executable or effectful function",
    );
}

#[test]
fn module_qualified_logical_data_is_checked_and_erased() {
    use kush::program::{Memory, load};
    let modules = Memory(vec![(
        "app.even".into(),
        "module app.even;
         pub total enum Even { EvenZero: Even, EvenSucc(Even): Even }
         pub type EvenMotive<e: Even> = Nat;
         pub total fn zero_branch() -> Nat ! {} { 0 }
         pub total fn succ_branch(e: Even, ih: Nat) -> Nat ! {} { Nat.succ(ih) }
         pub total fn count(e: Even) -> Nat ! {} {
             Data.elim::<Even>(EvenMotive, zero_branch, succ_branch, e)
         }
         pub total fn two_even() -> Even ! {} { EvenSucc(EvenSucc(EvenZero)) }
         pub total fn count_two() -> Eq<Nat, count<two_even>, 2> ! {} { refl::<Nat>(2) }"
            .into(),
    )]);
    let source = "module app.main;
        use app.even;
        total fn zero_even() -> even.Even ! {} { even.Even.EvenZero }
        fn consume(erased e: even.Even) -> i64 ! {} { 11 }
        fn main() -> i64 ! {panic}
            { consume(even.two_even()) + consume(zero_even()) }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 22);
    let logical = checked.logical_definitions();
    assert!(logical.iter().any(|name| name.ends_with("Even")));
    assert!(logical.iter().any(|name| name.ends_with("two_even")));
}

#[test]
fn logical_data_example_checks_and_runs() {
    let program =
        kush::executable::check(include_str!("../../../examples/logical-data.kush")).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn reference_evaluator_and_native_backend_agree_on_erased_logical_data() {
    use std::process::Command;
    let source = format!(
        "{VECT}
        fn consume(erased v: Vect<Nat, 2>) -> i64 ! {{}} {{ 42 }}
        fn main() -> i64 ! {{panic}} {{ consume(two()) }}"
    );
    let program = checked(&source);
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("logical_data");
    kush::native::build(&program, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(42));
}

/// `Fin` uses a constructor-local binder `<n: Nat>` so the result index can
/// vary with the predecessor. This is the standard finite-index encoding, now
/// expressible from source rather than only through the kernel API.
const FIN: &str = r#"
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
    type FinMotive<N: Nat, f: Fin<N>> = Nat;
    total fn fzero_branch<N: Nat, n: Nat>() -> Nat ! {} { 0 }
    total fn fsucc_branch<N: Nat, n: Nat>(pred: Fin<n>, ih: Nat) -> Nat ! {} {
        Nat.succ(ih)
    }
    total fn fin_count<N: Nat>(f: Fin<N>) -> Nat ! {} {
        Data.elim::<Fin>(FinMotive, fzero_branch, fsucc_branch, f)
    }
    type FinTotal<N: Nat, f: Fin<N>> = Eq<Nat, N, N>;
    total fn fzero_total<N: Nat, n: Nat>() -> Eq<Nat, Nat.succ<n>, Nat.succ<n>> ! {} {
        refl::<Nat>(Nat.succ(n))
    }
    total fn fsucc_total<N: Nat, n: Nat>(pred: Fin<n>, ih: Eq<Nat, n, n>)
        -> Eq<Nat, Nat.succ<n>, Nat.succ<n>> ! {} {
        refl::<Nat>(Nat.succ(n))
    }
    total fn fin_total<N: Nat>(f: Fin<N>) -> FinTotal<N, f> ! {} {
        Data.elim::<Fin>(FinTotal, fzero_total, fsucc_total, f)
    }
    total fn count_three() -> Eq<Nat, fin_count<3, three>, 2> ! {} {
        refl::<Nat>(2)
    }
    total fn total_three() -> Eq<Nat, 3, 3> ! {} { fin_total::<3>(three) }
"#;

#[test]
fn finite_index_data_uses_constructor_local_binders_from_source() {
    let checked = kush::check(FIN).unwrap();
    assert!(checked.definitions.contains(&"Fin".to_owned()));
    let three = kush::kernel::Term::Global("three".into());
    let count = kush::kernel::Term::app(
        kush::kernel::Term::app(
            kush::kernel::Term::Global("fin_count".into()),
            kush::kernel::Term::natural(3u64.into()),
        ),
        three,
    );
    assert_eq!(
        checked.kernel.normalize_closed(&count).unwrap(),
        kush::kernel::Term::natural(2u64.into())
    );
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&kush::kernel::Term::Global("count_three".into()))
            .unwrap(),
        kush::kernel::Term::refl(
            kush::kernel::Term::Nat,
            kush::kernel::Term::natural(2u64.into())
        )
    );
    // The dependent motive is instantiated at each constructor's result index.
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&kush::kernel::Term::Global("total_three".into()))
            .unwrap(),
        kush::kernel::Term::refl(
            kush::kernel::Term::Nat,
            kush::kernel::Term::natural(3u64.into())
        )
    );
}

#[test]
fn finite_index_evidence_is_erased_at_the_executable_boundary() {
    let source = format!(
        "{FIN}
        fn consume_fin(erased f: Fin<3>) -> i64 ! {{}} {{ 40 }}
        fn main() -> i64 ! {{panic}} {{ consume_fin(three()) + 2 }}"
    );
    let program = checked(&source);
    assert_eq!(program.function_count(), 2);
    assert_eq!(evaluate(&source), 42);
    let (value, stats) = checked(&source)
        .evaluate_with_stats(&mut Vec::new())
        .unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    // The logical family and its constructors are gone from the runtime IR.
    let logical = program.logical_definitions();
    assert!(logical.contains(&"Fin".to_owned()));
    assert!(!logical.iter().any(|name| name.contains("FSucc")));
}

#[test]
fn finite_index_wrong_evidence_and_malformed_scoping_are_rejected() {
    rejects(
        &format!(
            "{FIN}
             fn consume_fin(erased f: Fin<4>) -> i64 ! {{}} {{ 1 }}
             fn main() -> i64 ! {{}} {{ consume_fin(three()) }}"
        ),
        "proof does not establish",
    );
    // A constructor-local binder does not leak into another constructor.
    rejects(
        "total enum Fin<N: Nat> {
             FZero<n: Nat>: Fin<Nat.succ<n>>,
             Bad: Fin<n>,
         }",
        "unknown name 'n'",
    );
    // A named field does not bind in its own type.
    rejects(
        &format!(
            "{FIN}
             total enum Pair<N: Nat> {{ Mk(first: Fin<second>, second: Nat): Pair<N> }}"
        ),
        "unknown name 'second'",
    );
    // Field names from another variant are not in scope either.
    rejects(
        "total enum Tagged<N: Nat> { Tag(value: Nat): Tagged<value>, Other: Tagged<value> }",
        "unknown name 'value'",
    );
    // Branches are checked against the constructor-local telescope and IH.
    rejects(
        &format!(
            "{FIN}
             total fn bad_branch<N: Nat, n: Nat>(pred: Fin<n>) -> Nat ! {{}} {{ 0 }}
             total fn bad<N: Nat>(f: Fin<N>) -> Nat ! {{}} {{
                 Data.elim::<Fin>(FinMotive, fzero_branch, bad_branch, f)
             }}"
        ),
        "type mismatch",
    );
    // The result index must have the family parameter's type.
    rejects(
        "total enum Bad<N: Nat> { Mk(value: Type): Bad<value> }",
        "type mismatch",
    );
    // A wrong constructor-local type is not coerced.
    rejects(
        "total enum Bad<N: Nat> { Mk<n: Type>: Bad<n> }",
        "type mismatch",
    );
}

const NAMED_FIELDS: &str = r#"
    total enum Tagged<N: Nat> {
        Tag(value: Nat): Tagged<value>,
    }
    total fn tag3() -> Tagged<3> ! {} { Tagged.Tag::<3>(3) }
    type TaggedMotive<N: Nat, t: Tagged<N>> = Nat;
    total fn tag_branch<N: Nat, value: Nat>() -> Nat ! {} { Nat.succ(value) }
    total fn tag_value<N: Nat>(t: Tagged<N>) -> Nat ! {} {
        Data.elim::<Tagged>(TaggedMotive, tag_branch, t)
    }
    total fn value3() -> Eq<Nat, tag_value<3, tag3>, 4> ! {} { refl::<Nat>(4) }

    total enum SizedVect<T: Type, N: Nat> {
        Empty: SizedVect<T, 0>,
        Push(head: T, tail: SizedVect<T, N>): SizedVect<T, Nat.succ<N>>,
    }
    total fn one_item() -> SizedVect<Nat, 1> ! {} {
        SizedVect.Push::<Nat, 0>(7, SizedVect.Empty::<Nat, 0>)
    }
"#;

#[test]
fn named_logical_fields_bind_in_later_fields_and_result_indices() {
    let checked = kush::check(NAMED_FIELDS).unwrap();
    let tag3 = kush::kernel::Term::Global("tag3".into());
    let value = kush::kernel::Term::app(
        kush::kernel::Term::app(
            kush::kernel::Term::Global("tag_value".into()),
            kush::kernel::Term::natural(3u64.into()),
        ),
        tag3,
    );
    assert_eq!(
        checked.kernel.normalize_closed(&value).unwrap(),
        kush::kernel::Term::natural(4u64.into())
    );
    let one = kush::kernel::Term::Global("one_item".into());
    assert!(
        checked
            .kernel
            .check_closed(
                &one,
                &kush::kernel::Term::app(
                    kush::kernel::Term::app(
                        kush::kernel::Term::Global("SizedVect".into()),
                        kush::kernel::Term::Nat
                    ),
                    kush::kernel::Term::natural(1u64.into())
                )
            )
            .is_ok()
    );
    // The field value, not the family parameter, determines the result index.
    rejects(
        &format!(
            "{NAMED_FIELDS}
             total fn wrong() -> Tagged<4> ! {{}} {{ Tagged.Tag::<3>(3) }}"
        ),
        "type mismatch",
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_finite_index_evidence() {
    use std::process::Command;
    let source = format!(
        "{FIN}
        fn consume_fin(erased f: Fin<3>) -> i64 ! {{}} {{ 42 }}
        fn main() -> i64 ! {{panic}} {{ consume_fin(three()) }}"
    );
    let program = checked(&source);
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("finite_indices");
    kush::native::build(&program, &binary).unwrap();
    let status = Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(42));
}

#[test]
fn finite_proofs_example_checks_and_runs() {
    let program =
        kush::executable::check(include_str!("../../../examples/finite-proofs.kush")).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert!(program.logical_definitions().iter().any(|n| n == "Fin"));
    assert!(program.logical_definitions().iter().any(|n| n == "True"));
}

#[test]
fn runtime_enums_do_not_gain_logical_constructor_syntax() {
    rejects(
        "enum E { A<T: Type>(x: i64): E }
         fn main() -> i64 ! {} { 0 }",
        "constructor-local binders are only supported",
    );
    rejects(
        "enum E { A(x: i64): E }
         fn main() -> i64 ! {} { 0 }",
        "named logical constructor fields are only supported",
    );
}

#[test]
fn constructor_local_binders_may_depend_on_earlier_locals() {
    let source = r#"
        total enum Fin<N: Nat> {
            FZero<n: Nat>: Fin<Nat.succ<n>>,
            FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
        }
        total fn fzero<n: Nat>() -> Fin<Nat.succ<n>> ! {} {
            Fin.FZero::<Nat.succ<n>, n>
        }
        total enum Witness<N: Nat> {
            Mk<n: Nat, pred: Fin<n>>(tag: Nat): Witness<N>,
        }
        total fn witness<n: Nat>(p: Fin<n>) -> Witness<3> ! {} {
            Witness.Mk::<3, n, p>(7)
        }
        type WitnessMotive<N: Nat, w: Witness<N>> = Nat;
        total fn witness_branch<N: Nat, n: Nat, p: Fin<n>>(tag: Nat) -> Nat ! {} {
            tag
        }
        total fn witness_tag<N: Nat>(w: Witness<N>) -> Nat ! {} {
            Data.elim::<Witness>(WitnessMotive, witness_branch, w)
        }
        total fn tag_value()
            -> Eq<Nat, witness_tag<3, witness<1, fzero<0>>>, 7> ! {} {
            refl::<Nat>(7)
        }
    "#;
    let checked = kush::check(source).unwrap();
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&kush::kernel::Term::Global("tag_value".into()))
            .unwrap(),
        kush::kernel::Term::refl(
            kush::kernel::Term::Nat,
            kush::kernel::Term::natural(7u64.into())
        )
    );
}

#[test]
fn later_named_fields_may_depend_on_earlier_field_values() {
    let source = r#"
        total enum Fin<N: Nat> {
            FZero<n: Nat>: Fin<Nat.succ<n>>,
            FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
        }
        total fn fzero<n: Nat>() -> Fin<Nat.succ<n>> ! {} {
            Fin.FZero::<Nat.succ<n>, n>
        }
        total enum Bounded<N: Nat> {
            Mk<n: Nat>(size: Nat, p: Fin<size>): Bounded<N>,
        }
        total fn bounded() -> Bounded<3> ! {} {
            Bounded.Mk::<3, 0>(2, fzero::<1>)
        }
        type BM<N: Nat, b: Bounded<N>> = Nat;
        total fn b_branch<N: Nat, n: Nat, size: Nat, p: Fin<size>>() -> Nat ! {} {
            size
        }
        total fn b_size<N: Nat>(b: Bounded<N>) -> Nat ! {} {
            Data.elim::<Bounded>(BM, b_branch, b)
        }
        total fn check() -> Eq<Nat, b_size<3, bounded>, 2> ! {} { refl::<Nat>(2) }
    "#;
    let checked = kush::check(source).unwrap();
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&kush::kernel::Term::Global("check".into()))
            .unwrap(),
        kush::kernel::Term::refl(
            kush::kernel::Term::Nat,
            kush::kernel::Term::natural(2u64.into())
        )
    );
    // The field's index uses the actual earlier field value, not just its type.
    rejects(
        &format!(
            "{source}
             total fn bad() -> Bounded<3> ! {{}} {{
                 Bounded.Mk::<3, 0>(2, Fin.FZero::<0, 0>)
             }}"
        ),
        "type mismatch",
    );
}
