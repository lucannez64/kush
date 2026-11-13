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
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}
#[test]
fn checks_source_proofs_and_computes_through_forward_references() {
    let result = check(include_str!("../../../examples/proofs.kush")).unwrap();
    assert_eq!(result.definitions.len(), 8);
    assert!(
        result.definitions.iter().position(|n| n == "next").unwrap()
            < result
                .definitions
                .iter()
                .position(|n| n == "answer")
                .unwrap()
    );
    assert_eq!(
        result
            .kernel
            .normalize_closed(&T::global("answer"))
            .unwrap(),
        nat(2)
    );
    assert_eq!(
        result
            .kernel
            .normalize_closed(&T::global("proof_of_answer"))
            .unwrap(),
        T::refl(T::Nat, nat(2))
    );
}
#[test]
fn proof_terms_really_depend_on_value_parameters() {
    let result =
        check("total fn same<T: Type>(x: T) -> Eq<T, x, x> ! {} { refl::<T>(x) }").unwrap();
    let applied = T::app(T::app(T::global("same"), T::Nat), nat(4));
    result
        .kernel
        .check_closed(&applied, &T::eq(T::Nat, nat(4), nat(4)))
        .unwrap();
    assert_eq!(
        result.kernel.normalize_closed(&applied).unwrap(),
        T::refl(T::Nat, nat(4))
    );
}
#[test]
fn false_proof_and_wrong_application_are_rejected() {
    rejects(
        "total fn bad() -> Eq<Nat, 0, 1> ! {} { refl::<Nat>(0) }",
        "type mismatch",
    );
    rejects(
        "total fn bad(x: Nat) -> Eq<Nat, x, 0> ! {} { refl::<Nat>(x) }",
        "type mismatch",
    );
    rejects(
        "total fn bad() -> Nat ! {} { Nat.succ(Type) }",
        "type mismatch",
    );
    rejects("total fn bad() -> Nat ! {} { 0(1) }", "non-function");
    rejects("total fn bad() -> Nat ! {} { Nat }", "type mismatch");
}
#[test]
fn generic_and_let_shadowing_is_capture_avoiding() {
    let result =
        check("total fn f<T: Type>(x: T) -> T ! {} { let x: T = x; { let y: T = x; y } }").unwrap();
    let applied = T::app(T::app(T::global("f"), T::Nat), nat(3));
    assert_eq!(result.kernel.normalize_closed(&applied).unwrap(), nat(3));
    // A local called refl must not accidentally invoke the builtin proof constructor.
    rejects(
        "total fn bad(refl: Nat) -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }",
        "non-function",
    );
}
#[test]
fn universes_are_explicit_and_not_type_in_type() {
    check("total fn good() -> Type<1> ! {} { Type }").unwrap();
    rejects("total fn bad() -> Type ! {} { Type }", "type mismatch");
    rejects("type U = Type<256>;", "universe levels");
    rejects("type U = Type<Nat>;", "expected a universe level");
    // No implicit cumulativity.
    rejects("total fn bad() -> Type<1> ! {} { Nat }", "type mismatch");
}
#[test]
fn ordinary_code_axioms_effects_erasure_and_resource_contracts_are_not_trusted() {
    for (source, expected) in [
        ("fn f() -> Nat ! {} { 0 }", "only total fn"),
        ("total fn f() -> Nat ! {};", "require a body"),
        ("total fn f() -> Nat ! {io} { 0 }", "empty effect row"),
        (
            "#[noalloc] total fn f() -> Nat ! {} { 0 }",
            "resource contracts",
        ),
        ("enum E { A }", "positivity"),
        ("struct S { x: Nat }", "positivity"),
    ] {
        rejects(source, expected);
    }
    // Erased parameters are ordinary logical binders in a total definition.
    check("total fn f(erased x: Nat) -> Nat ! {} { x }").unwrap();
}
#[test]
fn all_dependency_cycles_are_rejected_before_kernel_admission() {
    for source in [
        "total fn spin() -> Nat ! {} { spin() }",
        "total fn a() -> Nat ! {} { b() } total fn b() -> Nat ! {} { a() }",
        "type A = B; type B = A;",
        "total fn n() -> A ! {} { 0 } type A = n;",
    ] {
        rejects(source, "cyclic logical definitions");
    }
}
#[test]
fn aliases_must_be_types_and_can_be_dependent() {
    let result = check("type Same<T: Type, x: T> = Eq<T, x, x>; total fn p(x: Nat) -> Same<Nat, x> ! {} { refl::<Nat>(x) }").unwrap();
    assert_eq!(result.definitions.len(), 2);
    rejects("type NotAType = 0;", "must return a type");
    rejects("type NotAType<T: Type> = 0;", "must return a type");
    rejects(
        "type Identity<T: Type> = T; total fn p() -> Identity<Nat> ! {} { Type }",
        "type mismatch",
    );
}
#[test]
fn unimplemented_forms_are_rejected_instead_of_erasing_their_meaning() {
    for source in [
        "type X = &Nat;",
        "type X = Nat | Nat;",
        "type X = Nat & Nat;",
        "type X = Nat @[1];",
        "type X = (Nat, Nat);",
        "type X = [Nat];",
        "type X = fn() -> Nat ! {};",
    ] {
        rejects(source, "not supported by logical checking");
    }
    rejects(
        "total fn f() -> Nat ! {} { let x = 0; x }",
        "explicitly typed let",
    );
    rejects(
        "total fn f() -> Nat ! {} { let mut x: Nat = 0; x }",
        "immutable",
    );
    rejects(
        "total fn f() -> Nat ! {} { 1 + 2 }",
        "expression is not supported",
    );
    check("total fn f() -> Nat ! {} { 33 }").unwrap();
    // Machine carriers and literals are admitted as checked logical values.
    check("total fn f() -> Bool ! {} { true }").unwrap();
    rejects(
        "total fn f() -> Bool ! {} { 1 }",
        "cannot have a Bool or Unit carrier",
    );
}
#[test]
fn namespace_resolution_and_dependency_order_are_deterministic() {
    let source =
        "module m; total fn first() -> Nat ! {} { m.last() } total fn last() -> Nat ! {} { 1 }";
    let result = check(source).unwrap();
    assert_eq!(result.definitions, ["last", "first"]);
    assert_eq!(
        result.kernel.normalize_closed(&T::global("first")).unwrap(),
        nat(1)
    );
    let first = check(include_str!("../../../examples/proofs.kush"))
        .unwrap()
        .definitions;
    let second = check(include_str!("../../../examples/proofs.kush"))
        .unwrap()
        .definitions;
    assert_eq!(first, second);
}

#[test]
fn empty_calls_do_not_silently_erase_application_of_nonfunctions() {
    for source in [
        "total fn f() -> Nat ! {} { 0() }",
        "total fn f() -> Type<1> ! {} { Type() }",
        "total fn f(n: Nat) -> Nat ! {} { n() }",
        "total fn id(n: Nat) -> Nat ! {} { n } total fn f() -> Nat ! {} { id() }",
        "total fn generic<T: Type>() -> Type ! {} { T } total fn f() -> Type ! {} { generic() }",
    ] {
        rejects(source, "empty call requires");
    }
    check("total fn a() -> Nat ! {} { 0 } total fn b() -> Nat ! {} { a() }").unwrap();
    check("total fn generic<T: Type>() -> Type ! {} { T } total fn f() -> Type ! {} { generic::<Nat>() }").unwrap();
}

const EVEN: &str = r#"
    total enum Even {
        EvenZero: Even,
        EvenSucc(Even): Even,
    }
    total fn double_step(n: Nat, e: Even) -> Even ! {} { EvenSucc(e) }
    type ConstantEven<n: Nat> = Even;
    total fn double(n: Nat) -> Even ! {} { Nat.induct(ConstantEven, EvenZero, double_step, n) }
    type EvenMotive<e: Even> = Nat;
    total fn even_zero_branch() -> Nat ! {} { 0 }
    total fn even_succ_branch(e: Even, ih: Nat) -> Nat ! {} { Nat.succ(ih) }
    total fn count(e: Even) -> Nat ! {} {
        Data.elim::<Even>(EvenMotive, even_zero_branch, even_succ_branch, e)
    }
    total fn count_two() -> Eq<Nat, count<double<2>>, 2> ! {} { refl::<Nat>(2) }
"#;

#[test]
fn total_enums_are_admitted_and_eliminate_by_checked_recursion() {
    let result = check(EVEN).unwrap();
    assert!(result.definitions.contains(&"Even".to_owned()));
    assert!(result.definitions.contains(&"count".to_owned()));
    assert!(
        result.definitions.iter().position(|n| n == "Even").unwrap()
            < result
                .definitions
                .iter()
                .position(|n| n == "count")
                .unwrap()
    );
    let applied = T::app(T::global("double"), nat(3));
    assert_eq!(
        result.kernel.infer_closed(&applied).unwrap(),
        T::global("Even")
    );
    // `double 3` is an Even value, and count computes its height.
    let count = T::app(T::global("count"), applied);
    assert_eq!(result.kernel.normalize_closed(&count).unwrap(), nat(3));
    assert_eq!(
        result
            .kernel
            .normalize_closed(&T::global("count_two"))
            .unwrap(),
        T::refl(T::Nat, nat(2))
    );
}

#[test]
fn indexed_vector_data_supports_dependent_motive_proofs() {
    let source = r#"
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
        total fn length_two() -> Eq<Nat, length<Nat, 2, two>, 2> ! {} { refl::<Nat>(2) }
    "#;
    let result = check(source).unwrap();
    assert_eq!(
        result
            .kernel
            .normalize_closed(&T::global("length_two"))
            .unwrap(),
        T::refl(T::Nat, nat(2))
    );
    let two = T::global("two");
    let length = T::app(T::app(T::app(T::global("length"), T::Nat), nat(2)), two);
    assert_eq!(result.kernel.normalize_closed(&length).unwrap(), nat(2));
}

#[test]
fn unsound_or_unsupported_logical_data_is_rejected() {
    rejects(
        "total enum Bad { Mk(fn(x: Bad) -> Nat ! {}): Bad }",
        "non-strictly-positive",
    );
    rejects(
        "total enum Vect<N: Nat> { Nil: Vect<0>, Cons(Vect<N>): Vect<Nat.succ<N>> }
         total enum Bad { Mk(Vect<Bad>): Bad }",
        "non-strictly-positive",
    );
    rejects("total enum E { A: Nat }", "must name its own");
    rejects("total enum E { A(Nat, Nat): E<Nat> }", "expects 0 index");
    rejects(
        "total enum A { Mk(B): A } total enum B { Mk(A): B }",
        "cyclic logical definitions",
    );
    rejects("enum E { A }", "positivity");
    rejects("total enum R { Mk { x: Nat }: R }", "record payloads");
    rejects(
        "total enum E { A, B } total fn f(e: E) -> Nat ! {} { Data.elim::<E>(f2, f3, e) }
         total fn f2(e: E) -> Type ! {} { Nat } total fn f3(e: E) -> Type ! {} { Nat }",
        "Data.elim expects",
    );
    rejects(
        "total enum E { A, B } type M<e: E> = Nat;
         total fn f(e: E) -> Nat ! {} { Data.elim::<E>(M, A, B, e) }",
        "type mismatch",
    );
}

#[test]
fn general_equality_elimination_is_available_for_proofs() {
    let source = r#"
        type Sym<T: Type, x: T, y: T> = Eq<T, y, x>;
        total fn SymMotive<T: Type, x: T, y: T, p: Eq<T, x, y>>() -> Type ! {} {
            Sym::<T, x, y>
        }
        total fn j_symmetry<T: Type>(x: T, y: T, proof: Eq<T, x, y>) -> Eq<T, y, x> ! {} {
            Eq.elim::<T>(x, y, SymMotive::<T, x>, refl::<T>(x), proof)
        }
    "#;
    let result = check(source).unwrap();
    let applied = T::app(
        T::app(T::app(T::global("j_symmetry"), T::Nat), nat(3)),
        nat(3),
    );
    let applied = T::app(applied, T::refl(T::Nat, nat(3)));
    assert_eq!(
        result.kernel.normalize_closed(&applied).unwrap(),
        T::refl(T::Nat, nat(3))
    );
}

#[test]
fn non_recursive_fields_can_hold_other_logical_data() {
    let source = r#"
        total enum B { Only: B }
        total enum A { Mk(B): A }
        type AMotive<x: A> = B;
        total fn id_b(b: B) -> B ! {} { b }
        total fn mk() -> A ! {} { Mk(Only) }
        total fn un_mk(a: A) -> B ! {} { Data.elim::<A>(AMotive, id_b, a) }
        total fn round_trip() -> Eq<B, un_mk<mk>, Only> ! {} { refl::<B>(Only) }
    "#;
    let result = check(source).unwrap();
    assert_eq!(
        result
            .kernel
            .normalize_closed(&T::global("round_trip"))
            .unwrap(),
        T::refl(T::global("B"), T::global("B::Only"))
    );
    let value = T::app(T::global("un_mk"), T::global("mk"));
    assert_eq!(
        result.kernel.normalize_closed(&value).unwrap(),
        T::global("B::Only")
    );
}

#[test]
fn multiple_recursive_fields_interleave_induction_hypotheses() {
    let source = r#"
        total enum Tree {
            Leaf: Tree,
            Node(Tree, Tree): Tree,
        }
        type Size<t: Tree> = Nat;
        type ConstantNat<n: Nat> = Nat;
        total fn add_step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }
        total fn add(n: Nat, m: Nat) -> Nat ! {} { Nat.induct(ConstantNat, m, add_step, n) }
        total fn leaf_size() -> Nat ! {} { 0 }
        total fn node_size(a: Tree, iha: Nat, b: Tree, ihb: Nat) -> Nat ! {} {
            Nat.succ(add(iha, ihb))
        }
        total fn size(t: Tree) -> Nat ! {} {
            Data.elim::<Tree>(Size, leaf_size, node_size, t)
        }
        total fn value() -> Nat ! {} { size(Node(Leaf, Node(Leaf, Leaf))) }
    "#;
    let result = check(source).unwrap();
    assert_eq!(
        result.kernel.normalize_closed(&T::global("value")).unwrap(),
        nat(2)
    );
}

#[test]
fn prop_declarations_are_checked_as_propositions() {
    let source = r#"
        prop True {
            Trivial: True,
        }
        prop And<P: Prop, Q: Prop> {
            Both(left: P, right: Q): And<P, Q>,
        }
        total enum Boxed<P: Prop> {
            Mk(value: P): Boxed<P>,
        }
        type P = True;
        total fn t() -> True ! {} { Trivial }
        total fn both() -> And<True, True> ! {} {
            And.Both::<True, True>(Trivial, Trivial)
        }
        total fn boxed() -> Boxed<True> ! {} { Boxed.Mk::<True>(Trivial) }
    "#;
    let result = check(source).unwrap();
    assert!(result.definitions.contains(&"True".to_owned()));
    assert!(result.definitions.contains(&"And".to_owned()));
    assert_eq!(
        result.kernel.normalize_closed(&T::global("both")).unwrap(),
        T::app(
            T::app(
                T::app(
                    T::app(T::global("And::Both"), T::global("True")),
                    T::global("True")
                ),
                T::global("True::Trivial")
            ),
            T::global("True::Trivial")
        )
    );
    // A proposition is not a Type and Prop is not a proposition.
    rejects("total fn bad() -> Prop ! {} { Prop }", "type mismatch");
    rejects("total fn bad() -> Type ! {} { Type }", "type mismatch");
    // Prop aliases are logical aliases, but a proof is not a type.
    rejects("type Bad = Trivial;", "unknown name");
}

#[test]
fn proof_irrelevance_applies_only_to_checkable_propositions() {
    let source = r#"
        prop True { Trivial: True }
        prop Two { First: Two, Second: Two }
        total enum Indexed<p: Two> { Mk: Indexed<p> }
        total fn same_proof() -> Indexed<Second> ! {} { Indexed.Mk::<First> }
        total fn equal_proofs() -> Eq<Two, First, Second> ! {} {
            refl::<Two>(First)
        }
    "#;
    check(source).unwrap();
    // Different propositions are not interchangeable.
    rejects(
        "prop True { Trivial: True }
         prop Two { First: Two, Second: Two }
         total enum Indexed<p: Two> { Mk: Indexed<p> }
         total fn bad() -> Indexed<True> ! {} { Indexed.Mk::<First> }",
        "type mismatch",
    );
    // Natural numbers are not Prop inhabitants and stay distinct.
    rejects(
        "total enum At<n: Nat> { MkN: At<n> }
         total fn bad() -> At<1> ! {} { At.MkN::<0> }",
        "type mismatch",
    );
    // Equality at a Prop carrier follows the same irrelevance boundary, but
    // it does not become propositional extensionality.
    rejects(
        "prop Two { First: Two, Second: Two }
         prop True { Trivial: True }
         total fn bad() -> Eq<Two, First, True> ! {} { refl::<Two>(First) }",
        "type mismatch",
    );
    rejects(
        "prop Two { First: Two, Second: Two }
         prop True { Trivial: True }
         total fn bad() -> Eq<Prop, Two, True> ! {} { refl::<Prop>(Two) }",
        "type mismatch",
    );
}

#[test]
fn prop_elimination_is_confined_to_prop_motives() {
    let source = r#"
        prop True { Trivial: True }
        prop False {}
        type TrueMotive<t: True> = True;
        total fn true_elim(t: True) -> True ! {} {
            Data.elim::<True>(TrueMotive, Trivial, t)
        }
        type FalseMotive<f: False> = True;
        total fn ex_falso(f: False) -> True ! {} {
            Data.elim::<False>(FalseMotive, f)
        }
    "#;
    check(source).unwrap();
    rejects(
        "prop Two { First: Two, Second: Two }
         type CountMotive<t: Two> = Nat;
         total fn a() -> Nat ! {} { 0 }
         total fn b() -> Nat ! {} { 1 }
         total fn count(t: Two) -> Nat ! {} {
             Data.elim::<Two>(CountMotive, a, b, t)
         }",
        "large elimination from proposition",
    );
    // Prop elimination cannot smuggle in effectful or partial evidence.
    rejects(
        "prop True { Trivial: True }
         type M<t: True> = True;
         total fn bad() -> True ! {io} { Data.elim::<True>(M, Trivial, Trivial) }",
        "empty effect row",
    );
}

#[test]
fn malformed_proposition_declarations_are_rejected() {
    rejects(
        "prop Bad { Mk { x: Nat }: Bad }",
        "record payloads belong to runtime enums",
    );
    rejects(
        "prop Bad { Mk(f: fn(x: Bad) -> Nat ! {}): Bad }",
        "non-strictly-positive",
    );
    rejects("prop Bad { Mk(x: Nat): Bad<Nat> }", "expects 0 index");
    rejects(
        "enum Runtime { A }
         prop Bad { Mk(Runtime): Bad }",
        "only 'total enum'",
    );
    // A constructor-local binder does not leak into another constructor.
    rejects(
        "prop Fin<N: Nat> {
             FZero<n: Nat>: Fin<Nat.succ<n>>,
             Bad: Fin<n>,
         }",
        "unknown name 'n'",
    );
}

#[test]
fn abstract_prop_motives_work_but_proof_returning_functions_are_not_motives() {
    let source = r#"
        prop True { Trivial: True }
        total fn elim_true(
            motive: fn(t: True) -> Prop ! {},
            branch: motive<Trivial>,
            t: True,
        ) -> motive<t> ! {} {
            Data.elim::<True>(motive, branch, t)
        }
    "#;
    check(source).unwrap();
    rejects(
        "prop True { Trivial: True }
         total fn bad(motive: fn(t: True) -> True ! {}, t: True) -> True ! {} {
             Data.elim::<True>(motive, Trivial, t)
         }",
        "returning a type or proposition",
    );
}

#[test]
fn prop_valued_motives_work_for_nat_induction_and_equality_elimination() {
    let source = r#"
        prop True { Trivial: True }
        type TrueMotiveN<n: Nat> = True;
        total fn zero_t() -> True ! {} { Trivial }
        total fn step_t(n: Nat, ih: True) -> True ! {} { Trivial }
        total fn always_true(n: Nat) -> True ! {} {
            Nat.induct(TrueMotiveN, zero_t, step_t, n)
        }
        type EqMotive<x: Nat, p: Eq<Nat, 0, x>> = True;
        total fn refl_case() -> True ! {} { Trivial }
        total fn j_true(x: Nat, p: Eq<Nat, 0, x>) -> True ! {} {
            Eq.elim::<Nat>(0, x, EqMotive, refl_case, p)
        }
        type TrueMotive<x: Nat> = True;
        total fn transport_true(x: Nat, p: Eq<Nat, 0, x>) -> True ! {} {
            Eq.transport::<Nat>(0, x, TrueMotive, p, Trivial)
        }
        prop Two { First: Two, Second: Two }
        type TwoMotive<x: Two, p: Eq<Two, First, x>> = True;
        total fn two_refl() -> True ! {} { Trivial }
        total fn j_two(x: Two, p: Eq<Two, First, x>) -> True ! {} {
            Eq.elim::<Two>(First, x, TwoMotive, two_refl, p)
        }
        total fn j_two_value() -> True ! {} {
            j_two(Second, refl::<Two>(First))
        }
    "#;
    check(source).unwrap();
}

#[test]
fn props_support_constructor_local_indices() {
    let source = r#"
        prop NonZero<n: Nat> {
            Succ<n: Nat>: NonZero<Nat.succ<n>>,
        }
        prop True { Trivial: True }
        total fn one_nonzero() -> NonZero<1> ! {} { NonZero.Succ::<1, 0> }
        type NZMotive<n: Nat, p: NonZero<n>> = True;
        total fn nz_branch<N: Nat, n: Nat>() -> True ! {} { Trivial }
        total fn nz_true<N: Nat>(p: NonZero<N>) -> True ! {} {
            Data.elim::<NonZero>(NZMotive, nz_branch, p)
        }
        total fn derive() -> True ! {} { nz_true::<1>(one_nonzero) }
    "#;
    check(source).unwrap();
    // The wrong local index does not produce NonZero<1>.
    rejects(
        "prop NonZero<n: Nat> { Succ<n: Nat>: NonZero<Nat.succ<n>> }
         total fn bad() -> NonZero<1> ! {} { NonZero.Succ::<1, 1> }",
        "type mismatch",
    );
}

#[test]
fn logical_alias_bounds_may_be_function_types_returning_props() {
    let source = r#"
        prop True { Trivial: True }
        type Constant<T: Type, P: fn(x: T) -> Prop ! {}> = True;
        total fn constant<T: Type, P: fn(x: T) -> Prop ! {}>()
            -> Constant<T, P> ! {} { Trivial }
        type SameProof<P: Prop, p: P, q: P> = Eq<P, p, q>;
        total fn same_proof<P: Prop, p: P>() -> SameProof<P, p, p> ! {} {
            refl::<P>(p)
        }
    "#;
    check(source).unwrap();
}

#[test]
fn props_support_multiple_recursive_fields() {
    let source = r#"
        prop BothTrue {
            Leaf: BothTrue,
            Node(BothTrue, BothTrue): BothTrue,
        }
        prop True { Trivial: True }
        type M<b: BothTrue> = True;
        total fn leaf_branch() -> True ! {} { Trivial }
        total fn node_branch(a: BothTrue, iha: True, b: BothTrue, ihb: True)
            -> True ! {} { Trivial }
        total fn all_true(b: BothTrue) -> True ! {} {
            Data.elim::<BothTrue>(M, leaf_branch, node_branch, b)
        }
    "#;
    check(source).unwrap();
}

#[test]
fn finite_indexed_data_can_be_eliminated_into_propositions() {
    let source = r#"
        total enum Fin<N: Nat> {
            FZero<n: Nat>: Fin<Nat.succ<n>>,
            FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
        }
        prop True { Trivial: True }
        type FM<N: Nat, f: Fin<N>> = True;
        total fn fz_branch<N: Nat, n: Nat>() -> True ! {} { Trivial }
        total fn fs_branch<N: Nat, n: Nat>(p: Fin<n>, ih: True) -> True ! {} {
            Trivial
        }
        total fn all_fin<N: Nat>(f: Fin<N>) -> True ! {} {
            Data.elim::<Fin>(FM, fz_branch, fs_branch, f)
        }
    "#;
    check(source).unwrap();
}

#[test]
fn source_functions_are_equal_up_to_eta() {
    // `apply<f>` normalizes to `λn. f n`, which is convertible with `f` only
    // through eta.
    check(
        "type Arrow = fn(n: Nat) -> Nat ! {};
         total fn apply(f: Arrow, n: Nat) -> Nat ! {} { f(n) }
         total fn eta(f: Arrow) -> Eq<Arrow, apply<f>, f> ! {} { refl::<Arrow>(f) }",
    )
    .unwrap();
    rejects(
        "type Arrow = fn(n: Nat) -> Nat ! {};
         total fn twice(f: Arrow, n: Nat) -> Nat ! {} { f(f(n)) }
         total fn bad(f: Arrow) -> Eq<Arrow, twice<f>, f> ! {} { refl::<Arrow>(f) }",
        "type mismatch",
    );
}
