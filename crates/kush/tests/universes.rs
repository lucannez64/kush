//! Universe polymorphism in the kernel: canonical levels, polymorphic
//! definitions and data families, and explicit instantiation.
use kush::kernel::{IndexedConstructorSpec, IndexedDataSpec, Kernel, Level, Term as T};

fn u(index: u32) -> Level {
    Level::param(index)
}
fn sort(level: Level) -> T {
    T::Universe(level)
}
fn at(name: &str, levels: Vec<Level>) -> T {
    T::Global(name.into(), levels)
}

#[test]
fn levels_have_a_canonical_form() {
    let one = Level::constant(1);
    // max(u, u + 1) = u + 1 and max(u + 1, 1) = u + 1: parameters are >= 0.
    assert_eq!(u(0).max(&u(0).succ().unwrap()), u(0).succ().unwrap());
    assert_eq!(u(0).succ().unwrap().max(&one), u(0).succ().unwrap());
    // max(u, 1) is not u: at u = 0 they differ.
    assert_ne!(u(0).max(&one), u(0));
    // max is commutative and idempotent on the canonical form.
    assert_eq!(u(0).max(&u(1)), u(1).max(&u(0)));
    assert_eq!(u(0).max(&u(0)), u(0));
    // succ distributes over max.
    assert_eq!(
        u(0).max(&one).succ().unwrap(),
        u(0).succ().unwrap().max(&Level::constant(2))
    );
    assert!(u(0).leq(&u(0).max(&u(1))));
    assert!(!u(1).leq(&u(0)));
    assert!(Level::zero().leq(&u(3)));
    assert!(!one.leq(&u(0)));
    assert_eq!(u(0).max(&one).to_string(), "max(1, u0)");
    assert_eq!(u(2).succ().unwrap().to_string(), "u2+1");
    assert!(Level::constant(u32::MAX).succ().is_err());
}

fn kernel_with_identity() -> Kernel {
    let mut k = Kernel::default();
    // id.{u} : (A : Type u) -> A -> A
    k.define_polymorphic(
        "id".into(),
        1,
        T::pi(sort(u(0)), T::pi(T::Var(0), T::Var(1))),
        T::lam(sort(u(0)), T::lam(T::Var(0), T::Var(0))),
    )
    .unwrap();
    k
}

#[test]
fn a_polymorphic_definition_is_used_at_several_levels() {
    let k = kernel_with_identity();
    let three = T::natural(3u64.into());
    // id.{0} Nat 3 : Nat, and it computes.
    let small = T::app(T::app(at("id", vec![0.into()]), T::Nat), three.clone());
    assert_eq!(k.infer_closed(&small).unwrap(), T::Nat);
    assert_eq!(k.normalize_closed(&small).unwrap(), three);
    // id.{1} Type Nat : Type: the same definition one universe up.
    let large = T::app(T::app(at("id", vec![1.into()]), T::universe(0)), T::Nat);
    assert_eq!(k.infer_closed(&large).unwrap(), T::universe(0));
    // id.{0} cannot take Type, which lives in Type 1.
    let wrong = T::app(T::app(at("id", vec![0.into()]), T::universe(0)), T::Nat);
    assert!(k.infer_closed(&wrong).is_err());
    // The instantiated type is reported.
    assert_eq!(
        k.infer_closed(&at("id", vec![2.into()])).unwrap(),
        T::pi(T::universe(2), T::pi(T::Var(0), T::Var(1)))
    );
}

#[test]
fn universe_arguments_must_match_and_be_in_scope() {
    let mut k = kernel_with_identity();
    // Wrong number of level arguments.
    assert!(k.infer_closed(&T::global("id")).is_err());
    assert!(k.infer_closed(&at("id", vec![0.into(), 0.into()])).is_err());
    // A closed term cannot mention a level parameter.
    assert!(k.infer_closed(&sort(u(0))).is_err());
    assert!(k.infer_closed(&at("id", vec![u(0)])).is_err());
    // A monomorphic definition cannot mention one either.
    assert!(k.define("bad".into(), T::universe(1), sort(u(0))).is_err());
    assert!(!k.contains("bad"));
    // Inside a polymorphic definition, only its own parameters are in scope.
    assert!(
        k.define_polymorphic("bad".into(), 1, T::universe(5), sort(u(1)))
            .is_err()
    );
    // The open APIs follow the frontend's level scope.
    assert!(k.sort_open(&sort(u(0)), &[]).is_err());
    k.set_level_scope(1);
    assert!(k.sort_open(&sort(u(0)), &[]).is_ok());
    k.set_level_scope(0);
}

#[test]
fn polymorphic_definitions_compose_and_unfold_at_instantiated_levels() {
    let mut k = kernel_with_identity();
    // Pi over two universes lands in their maximum.
    k.set_level_scope(2);
    assert_eq!(
        k.infer_open(&T::pi(sort(u(0)), sort(u(1))), &[]).unwrap(),
        T::Universe(u(0).succ().unwrap().max(&u(1).succ().unwrap()))
    );
    k.set_level_scope(0);
    // twice.{u} (A : Type u) (x : A) := id.{u} A (id.{u} A x)
    let id_at = |level: Level| at("id", vec![level]);
    k.define_polymorphic(
        "twice".into(),
        1,
        T::pi(sort(u(0)), T::pi(T::Var(0), T::Var(1))),
        T::lam(
            sort(u(0)),
            T::lam(
                T::Var(0),
                T::app(
                    T::app(id_at(u(0)), T::Var(1)),
                    T::app(T::app(id_at(u(0)), T::Var(1)), T::Var(0)),
                ),
            ),
        ),
    )
    .unwrap();
    // twice.{1} Type Nat = Nat, by delta unfolding at level 1.
    let term = T::app(T::app(at("twice", vec![1.into()]), T::universe(0)), T::Nat);
    assert_eq!(k.normalize_closed(&term).unwrap(), T::Nat);
    // Levels convert by their canonical form: Type u : Type (max(u + 1, 1)),
    // but not Type (max(u, 1) + 1), which is a different level at u = 0
    // (there is no cumulativity).
    k.set_level_scope(1);
    let next = u(0).succ().unwrap();
    k.check_open(&sort(u(0)), &sort(next.max(&Level::constant(1))), &[])
        .unwrap();
    let higher = u(0).max(&Level::constant(1)).succ().unwrap();
    assert!(k.check_open(&sort(u(0)), &sort(higher), &[]).is_err());
    k.set_level_scope(0);
}

/// List.{u} (A : Type u) : Type u with nil and cons.
fn list(levels: u32, recursive_level: Level) -> IndexedDataSpec {
    IndexedDataSpec {
        name: "List".into(),
        params: vec![sort(u(0))],
        constructors: vec![
            IndexedConstructorSpec {
                name: "nil".into(),
                locals: vec![],
                fields: vec![],
                result: vec![T::Var(0)],
            },
            IndexedConstructorSpec {
                name: "cons".into(),
                locals: vec![],
                // head : A, tail : List.{u} A
                fields: vec![
                    T::Var(0),
                    T::app(at("List", vec![recursive_level]), T::Var(1)),
                ],
                result: vec![T::Var(2)],
            },
        ],
        prop: false,
        levels,
    }
}

#[test]
fn a_polymorphic_family_lives_in_its_parameter_universe() {
    let mut k = Kernel::default();
    k.define_indexed_data(list(1, u(0))).unwrap();
    let info = k.data("List").unwrap();
    assert_eq!(info.sort, u(0));
    assert_eq!(info.levels, 1);
    assert_eq!(k.global_levels("cons"), Some(1));
    // List.{1} Type : Type 1, a list of types.
    let types = T::app(at("List", vec![1.into()]), T::universe(0));
    assert_eq!(k.infer_closed(&types).unwrap(), T::universe(1));
    // cons.{1} Type Nat (nil.{1} Type) : List.{1} Type
    let value = T::app(
        T::app(T::app(at("cons", vec![1.into()]), T::universe(0)), T::Nat),
        T::app(at("nil", vec![1.into()]), T::universe(0)),
    );
    assert_eq!(k.infer_closed(&value).unwrap(), types);
    // The same constructor at level 0 cannot hold a type.
    let wrong = T::app(
        T::app(T::app(at("cons", vec![0.into()]), T::universe(0)), T::Nat),
        T::app(at("nil", vec![0.into()]), T::universe(0)),
    );
    assert!(k.infer_closed(&wrong).is_err());

    // length.{1} over that list: eliminate with motive λA l. Nat.
    let motive = T::lam(
        T::universe(1),
        T::lam(T::app(at("List", vec![1.into()]), T::Var(0)), T::Nat),
    );
    let nil_branch = T::lam(T::universe(1), T::Zero);
    let cons_branch = T::lam(
        T::universe(1),
        T::lam(
            T::Var(0),
            T::lam(
                T::app(at("List", vec![1.into()]), T::Var(1)),
                T::lam(T::Nat, T::succ(T::Var(0))),
            ),
        ),
    );
    let length = T::IndElim {
        data: "List".into(),
        motive: Box::new(motive),
        branches: vec![nil_branch, cons_branch],
        scrutinee: Box::new(value),
    };
    assert_eq!(k.infer_closed(&length).unwrap(), T::Nat);
    assert_eq!(
        k.normalize_closed(&length).unwrap(),
        T::natural(1u64.into())
    );
}

#[test]
fn recursive_fields_use_the_family_at_its_own_levels() {
    // A cons whose tail is List.{0} inside List.{u} is non-uniform: rejected.
    let mut k = Kernel::default();
    assert!(k.define_indexed_data(list(1, Level::zero())).is_err());
    assert!(!k.contains("List"));
    // A family cannot mention parameters it does not declare.
    let mut spec = list(1, u(0));
    spec.params = vec![sort(u(1))];
    assert!(k.define_indexed_data(spec).is_err());
    assert!(!k.contains("List"));
}

const POLYMORPHIC: &str = "
total fn id<u: Level, T: Type<u>>(x: T) -> T ! {} { x }
total fn three() -> Nat ! {} { id::<0, Nat>(3) }
total fn nat_type() -> Type ! {} { id::<1, Type>(Nat) }
total fn computes() -> Eq<Nat, id<0, Nat, 3>, 3> ! {} { refl::<Nat>(3) }

type Big<u: Level> = Type<Level.succ<u>>;
total fn type_is_big() -> Big<0> ! {} { Type }
type Both<u: Level, v: Level> = Type<Level.max<u, v>>;
total fn nat_in_both() -> Both<0, 0> ! {} { Nat }

total enum List<u: Level, A: Type<u>> {
    Nil: List<u, A>,
    Cons(A, List<u, A>): List<u, A>,
}
type LengthMotive<u: Level, A: Type<u>, l: List<u, A>> = Nat;
total fn nil_length<u: Level, A: Type<u>>() -> Nat ! {} { 0 }
total fn cons_length<u: Level, A: Type<u>>(x: A, xs: List<u, A>, ih: Nat) -> Nat ! {} {
    Nat.succ(ih)
}
total fn length<u: Level, A: Type<u>>(l: List<u, A>) -> Nat ! {} {
    Data.elim::<List>(LengthMotive::<u>, nil_length::<u>, cons_length::<u>, l)
}
total fn types() -> List<1, Type> ! {} { Cons::<1, Type>(Nat, Cons::<1, Type>(Bool, Nil::<1, Type>)) }
total fn numbers() -> List<0, Nat> ! {} { Cons::<0, Nat>(7, Nil::<0, Nat>) }
total fn two_types() -> Eq<Nat, length<1, Type, types>, 2> ! {} { refl::<Nat>(2) }
total fn one_number() -> Eq<Nat, length<0, Nat, numbers>, 1> ! {} { refl::<Nat>(1) }
";

#[test]
fn source_level_universe_polymorphism() {
    let checked = kush::check(POLYMORPHIC).unwrap();
    let kernel = &checked.kernel;
    assert_eq!(kernel.global_levels("id"), Some(1));
    assert_eq!(kernel.global_levels("Both"), Some(2));
    assert_eq!(kernel.data("List").unwrap().sort, u(0));
}

fn rejects(source: &str, expected: &str) {
    let error = kush::check(source).unwrap_err().message;
    assert!(
        error.contains(expected),
        "expected '{expected}' in: {error}"
    );
}

#[test]
fn source_level_universe_errors() {
    let id = "total fn id<u: Level, T: Type<u>>(x: T) -> T ! {} { x }\n";
    // Level arguments are required and come first.
    rejects(
        &format!("{id}total fn bad() -> Nat ! {{}} {{ id(3) }}"),
        "universe polymorphic",
    );
    // id at level 0 cannot take Type, which lives in Type<1>.
    rejects(
        &format!("{id}total fn bad() -> Type ! {{}} {{ id::<0, Type>(Nat) }}"),
        "type mismatch",
    );
    // There is still no cumulativity.
    rejects(
        "type Big<u: Level> = Type<Level.succ<u>>;
         total fn bad() -> Big<1> ! {} { Nat }",
        "type mismatch",
    );
    rejects(
        "total fn bad<T: Type, u: Level>(x: T) -> T ! {} { x }",
        "must come before",
    );
    rejects(
        "total fn bad<u: Level>(x: u) -> Nat ! {} { 0 }",
        "only appear in Type",
    );
    rejects(
        "total fn bad<T: Type>(x: T) -> Type<T> ! {} { Nat }",
        "expected a universe level",
    );
    // A recursive field must use the family's own levels.
    rejects(
        "total enum List<u: Level, A: Type<u>> {
             Nil: List<u, A>,
             Cons(A, List<0, A>): List<u, A>,
         }",
        "own universe parameters",
    );
    rejects(
        "total enum List<u: Level, A: Type<u>> {
             Nil: List<0, A>,
         }",
        "own universe levels",
    );
}

#[test]
fn the_universes_example_checks() {
    let checked = kush::check(include_str!("../../../examples/universes.kush")).unwrap();
    assert_eq!(checked.kernel.global_levels("length"), Some(1));
    // Replacing a true count with a false one is rejected.
    let false_proof = include_str!("../../../examples/universes.kush").replace(
        "length<1, Type, types>, 3> ! {} { refl::<Nat>(3) }",
        "length<1, Type, types>, 2> ! {} { refl::<Nat>(2) }",
    );
    assert!(kush::check(&false_proof).is_err());
}
