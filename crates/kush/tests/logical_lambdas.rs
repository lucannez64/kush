//! LOGIC-LAMBDA: lambda expressions in the logical fragment. They elaborate
//! to kernel lambdas, so motives, steps and higher-order arguments no longer
//! need a named total function each.
use kush::{check, kernel::Term as T};

fn nat(n: u64) -> T {
    T::natural(n.into())
}

fn rejects(source: &str, expected: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected:?}, got {error:?}"
    );
}

const ADD: &str = "
total fn add(n: Nat, m: Nat) -> Nat ! {} {
    Nat.induct(fn(k) { Nat }, m, fn(k, acc) { Nat.succ(acc) }, n)
}
";

#[test]
fn lambdas_as_arguments_motives_and_steps() {
    let source = format!(
        "{ADD}
        total fn twice(f: fn(n: Nat) -> Nat ! {{}}, n: Nat) -> Nat ! {{}} {{ f(f(n)) }}
        // The parameter type comes from twice's first parameter.
        total fn four() -> Nat ! {{}} {{ twice(fn(x) {{ Nat.succ(x) }}, 2) }}
        // Fully annotated, with a result type.
        total fn six() -> Nat ! {{}} {{ twice(fn(x: Nat) -> Nat ! {{}} {{ add(x, 1) }}, 4) }}
        total fn five() -> Eq<Nat, add<2, 3>, 5> ! {{}} {{ refl::<Nat>(5) }}
        total fn four_is() -> Eq<Nat, four, 4> ! {{}} {{ refl::<Nat>(4) }}
        total fn six_is() -> Eq<Nat, six, 6> ! {{}} {{ refl::<Nat>(6) }}"
    );
    let checked = check(&source).unwrap();
    assert_eq!(
        checked.kernel.normalize_closed(&T::global("four")).unwrap(),
        nat(4)
    );
}

#[test]
fn lambdas_capture_and_take_their_types_from_the_result() {
    let source = format!(
        "{ADD}
        // The returned lambda's parameter comes from the declared result type,
        // and its body refers to the enclosing parameter n.
        total fn adder(n: Nat) -> fn(m: Nat) -> Nat ! {{}} ! {{}} {{ fn(m) {{ add(n, m) }} }}
        total fn seven() -> Eq<Nat, adder<3, 4>, 7> ! {{}} {{ refl::<Nat>(7) }}
        // Through a let, and a lambda bound by a typed let.
        total fn nine() -> Nat ! {{}} {{
            let inc: fn(k: Nat) -> Nat ! {{}} = fn(k) {{ Nat.succ(k) }};
            inc(add(4, 4))
        }}
        total fn nine_is() -> Eq<Nat, nine, 9> ! {{}} {{ refl::<Nat>(9) }}"
    );
    check(&source).unwrap();
}

#[test]
fn dependent_motives_for_transport_and_j() {
    check(
        "total fn symmetry<T: Type>(x: T, y: T, p: Eq<T, x, y>) -> Eq<T, y, x> ! {} {
             Eq.transport::<T>(x, y, fn(z) { Eq::<T, z, x> }, p, refl::<T>(x))
         }
         total fn symmetry_j<T: Type>(x: T, y: T, p: Eq<T, x, y>) -> Eq<T, y, x> ! {} {
             Eq.elim::<T>(x, y, fn(z, q) { Eq::<T, z, x> }, refl::<T>(x), p)
         }",
    )
    .unwrap();
}

#[test]
fn proofs_by_induction_with_lambda_motives() {
    let source = format!(
        "{ADD}
        // add(n, 0) = n, by induction on n with a dependent lambda motive.
        total fn congruence(a: Nat, b: Nat, p: Eq<Nat, a, b>) -> Eq<Nat, Nat.succ<a>, Nat.succ<b>> ! {{}} {{
            Eq.transport::<Nat>(a, b, fn(z) {{ Eq::<Nat, Nat.succ<a>, Nat.succ<z>> }}, p, refl::<Nat>(Nat.succ(a)))
        }}
        total fn add_zero(n: Nat) -> Eq<Nat, add<n, 0>, n> ! {{}} {{
            Nat.induct(
                fn(k) {{ Eq::<Nat, add<k, 0>, k> }},
                refl::<Nat>(0),
                fn(k, ih) {{ congruence(add(k, 0), k, ih) }},
                n,
            )
        }}"
    );
    check(&source).unwrap();
}

#[test]
fn lambdas_in_data_elimination() {
    check(
        "total enum Even { EvenZero: Even, EvenSucc(Even): Even }
         total fn height(e: Even) -> Nat ! {} {
             Data.elim::<Even>(fn(v) { Nat }, 0, fn(v: Even, ih: Nat) { Nat.succ(ih) }, e)
         }
         total fn two() -> Eq<Nat, height<EvenSucc<EvenSucc<EvenZero>>>, 2> ! {} { refl::<Nat>(2) }",
    )
    .unwrap();
}

#[test]
fn lambda_errors() {
    rejects(
        "total fn bad() -> Nat ! {} { let f: Nat = fn(x) { x }; f }",
        "annotate the type of lambda parameter 'x'",
    );
    rejects(
        "total fn apply(f: fn(n: Nat) -> Nat ! {}, n: Nat) -> Nat ! {} { f(n) }
         total fn bad() -> Nat ! {} { apply(fn(x: Nat) -> Type { x }, 1) }",
        "declared result type",
    );
    rejects(
        "total fn apply(f: fn(n: Nat) -> Nat ! {}, n: Nat) -> Nat ! {} { f(n) }
         total fn bad() -> Nat ! {} { apply(fn(x: Nat) ! {io} { x }, 1) }",
        "empty effect row",
    );
    rejects(
        "total fn apply(f: fn(n: Nat) -> Nat ! {}, n: Nat) -> Nat ! {} { f(n) }
         total fn bad() -> Nat ! {} { apply(fn(x: Type) { x }, 1) }",
        "type mismatch",
    );
    // Data.elim branches carry their types: no expected type supplies them.
    rejects(
        "total enum Even { EvenZero: Even, EvenSucc(Even): Even }
         total fn bad(e: Even) -> Nat ! {} {
             Data.elim::<Even>(fn(v) { Nat }, 0, fn(v, ih) { Nat.succ(ih) }, e)
         }",
        "annotate the type",
    );
}

#[test]
fn lambdas_in_logical_definitions_beside_executable_code() {
    // The executable checker admits the logical half (with its lambdas)
    // through the same kernel, then erases it.
    kush::executable::check(
        "total fn twice(f: fn(n: Nat) -> Nat ! {}, n: Nat) -> Nat ! {} { f(f(n)) }
         total fn four_by_lambda() -> Nat ! {} { twice(fn(x) { Nat.succ(x) }, 2) }
         total fn four() -> Eq<Nat, four_by_lambda, 4> ! {} { refl::<Nat>(4) }
         fn main() -> i64 ! {io, panic} { print_i64(7); 0 }",
    )
    .unwrap();
}
