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

#[test]
fn const_lengths_are_inferred_and_explicitly_specialized() {
    let source = r#"
        #[noalloc]
        fn identity<T: Type, N: Nat>(xs: [T; N]) -> [T; N] ! {} { xs }

        #[noalloc]
        fn last<T: Type, N: Nat>(xs: [T; N]) -> T ! {panic} { xs[N - 1] }

        fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [10, 20, 12];
            let b = identity(a);
            let c = identity::<i64, 3>(b);
            last(c)
        }
    "#;
    assert_eq!(evaluate(source), 12);
    // `*` and `/` share a precedence level and associate left to right.
    assert_eq!(
        evaluate("fn main() -> i64 ! {panic} { let a: [i64; 2 * 3 / 2] = [1, 2, 3]; a[2] }"),
        3
    );

    // A literal array argument infers both the element type and the length.
    let literal = r#"
        #[noalloc]
        fn identity<T: Type, N: Nat>(xs: [T; N]) -> [T; N] ! {} { xs }
        fn main() -> i64 ! {panic} {
            let a = identity([10, 20, 12]);
            a[0] + a[1] + a[2]
        }
    "#;
    assert_eq!(evaluate(literal), 42);
    // Constant slice bounds may also use the checked natural fragment.
    let bounded = r#"
        #[noalloc]
        fn second<T: Type, N: Nat>(a: [T; N]) -> T ! {panic} {
            let view: &[T] = &a[0..N - 1];
            view[0]
        }
        fn main() -> i64 ! {panic} { second([42, 1, 2]) }
    "#;
    assert_eq!(evaluate(bounded), 42);
}

#[test]
fn kernel_normalized_arithmetic_folds_array_lengths_and_indices() {
    let source = r#"
        type Constant<n: Nat> = Nat;
        total fn step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }
        total fn add(n: Nat, m: Nat) -> Nat ! {} { Nat.induct(Constant, m, step, n) }

        #[noalloc]
        fn middle(xs: [i64; add<1, 1>]) -> i64 ! {panic} { xs[add(0, 1)] }

        fn main() -> i64 ! {panic} {
            let a: [i64; (1 + 1) * 2 - 2] = [20, 22];
            middle(a) + 20
        }
    "#;
    assert_eq!(evaluate(source), 42);
    // The same checked kernel computation is also an index out of bounds.
    rejects(
        r#"
        type Constant<n: Nat> = Nat;
        total fn step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }
        total fn add(n: Nat, m: Nat) -> Nat ! {} { Nat.induct(Constant, m, step, n) }
        fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [1, 2, 3];
            a[add(2, 1)]
        }
        "#,
        "out of bounds",
    );
}

#[test]
fn nested_and_generic_records_keep_symbolic_lengths() {
    let source = r#"
        struct Buffer<N: Nat> { data: [i64; N] }
        struct Pair { left: i64, right: i64 }

        #[noalloc]
        fn first<N: Nat>(b: Buffer<N>) -> i64 ! {panic} { b.data[0] }

        fn main() -> i64 ! {panic} {
            let b: Buffer<3> = Buffer { data: [0, 20, 22] };
            let nested: [[i64; 2]; 2] = [[1, 2], [20, 22]];
            let row = nested[1];
            first(b) + row[0] + row[1]
        }
    "#;
    assert_eq!(evaluate(source), 42);
}

#[test]
fn different_and_runtime_dependent_lengths_are_rejected() {
    rejects(
        r#"
        fn same<T: Type, N: Nat>(a: [T; N], b: [T; N]) -> T ! {panic} { a[0] }
        fn main() -> i64 ! {panic} { same([1, 2], [3, 4, 5]) }
        "#,
        "array length mismatch",
    );
    rejects(
        "fn bad(n: i64) -> [i64; n] ! {} { [] } fn main() -> i64 ! {} { 0 }",
        "runtime value",
    );
    rejects(
        "fn bad<N: Type>(xs: [i64; N]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "must be a compile-time natural",
    );
    rejects(
        "struct Bad<N: Nat> { value: N } fn main() -> i64 ! {} { 0 }",
        "not a runtime type",
    );
    rejects(
        "struct Bad<M: Type> { data: [i64; M] } fn main() -> i64 ! {} { 0 }",
        "must be a compile-time natural",
    );
    rejects(
        "type Bad<N: Type> = [i64; N]; fn main() -> i64 ! {} { 0 }",
        "must be a compile-time natural",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: [i64; 2] = [1, 2]; a[-1] }",
        "nonnegative",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: [i64; 1 - 2] = []; 0 }",
        "nonnegative",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: [i64; 1 / 0] = []; 0 }",
        "constant nonnegative",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: [i64; 1 + nope] = []; 0 }",
        "constant expression",
    );
}

#[test]
fn grades_types_and_natural_parameters_stay_separate() {
    let source = r#"
        fn mixed<G: Grade, N: Nat, T: Type>(x: T @[G], xs: [T; N]) -> T ! {panic} { x; xs[0] }
        fn main() -> i64 ! {panic} {
            let xs: [i64; 2] = [42, 0];
            mixed::<1, 2, i64>(0, xs)
        }
    "#;
    assert_eq!(evaluate(source), 42);
    rejects(
        "fn bad<G: Grade>(xs: [i64; G]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "must be a compile-time natural",
    );
    rejects(
        "fn bad<N: Nat>(x: [N; 2]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "not a runtime type",
    );
    rejects(
        "fn bad<G: Grade, N: Nat>(x: i64 @[G], xs: [i64; N]) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { bad(1, [2, 3]) }",
        "cannot infer usage grade",
    );
}

#[test]
fn executable_aliases_are_transparent_across_arrays_unions_and_generics() {
    let source = r#"
        type Number = i64;
        type Pair<T> = [T; 2];
        type Fixed<N: Nat> = [i64; N];
        type Value = Number | Bool;
        type ReadOnly = Pair<i64>;

        #[noalloc]
        fn pick(v: Value) -> i64 ! {panic} {
            match v {
                i64 @ n => n,
                Bool @ b => if b { 1 } else { 0 },
            }
        }

        fn main() -> i64 ! {panic} {
            let p: ReadOnly = [20, 20];
            let n: Number = p[0] + p[1];
            let f: Fixed<2> = [0, 0];
            pick(n) + pick(true) + pick(1) + f[0]
        }
    "#;
    let program = checked(source);
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);
}

#[test]
fn generic_aliases_participate_in_length_inference() {
    let source = r#"
        type Arr<T, N: Nat> = [T; N];
        #[noalloc]
        fn first<T, N: Nat>(xs: Arr<T, N>) -> T ! {panic} { xs[0] }
        #[noalloc]
        fn identity<T, N: Nat>(xs: Arr<T, N>) -> Arr<T, N> ! {} { xs }
        fn main() -> i64 ! {panic} {
            let a: Arr<i64, 3> = [20, 21, 1];
            identity(a)[2] + first(a)
        }
    "#;
    assert_eq!(evaluate(source), 21);
}

#[test]
fn aliases_cross_modules_and_enforce_visibility() {
    use kush::program::{Memory, load};
    let modules = Memory(vec![
        (
            "app.types".into(),
            "module app.types;
             pub type Numbers = [i64; 2];
             pub type Either<T> = T | Bool;
             type Hidden = [i64; 2];"
                .into(),
        ),
        (
            "app.other".into(),
            "module app.other;
             use app.types.Hidden;
             pub fn hidden() -> Hidden ! {} { [1, 2] }"
                .into(),
        ),
    ]);
    let source = "module app.main;
        use app.types;
        fn main() -> i64 ! {panic} {
            let xs: types.Numbers = [20, 22];
            let v: types.Either<i64> = xs[0];
            match v { i64 @ n => n, Bool @ b => 0 }
        }";
    let program = load("main.kush", source, &modules).unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 20);

    let private = load(
        "main.kush",
        "module app.main; use app.other; fn main() -> i64 ! {} { 0 }",
        &modules,
    )
    .unwrap();
    let error = kush::executable::check_program(&private).unwrap_err();
    assert!(error.message.contains("private"), "{error:?}");
}

#[test]
fn alias_cycles_and_logical_alias_boundaries_stay_checked() {
    rejects(
        "type A = B; type B = A; fn main() -> i64 ! {} { let x: A = 1; x }",
        "cyclic type alias",
    );
    rejects(
        "type A = [i64; A]; fn main() -> i64 ! {} { let x: A = []; 0 }",
        "cyclic type alias",
    );
    // A runtime alias cannot be cited by an erased proof definition.
    rejects(
        "type Numbers = [i64; 2];
         fn main() -> i64 ! {panic} { let xs: Numbers = [1, 2]; xs[0] }
         total fn bad(x: Numbers) -> Nat ! {} { 0 }",
        "unchecked alias",
    );
    // A declaration that only looks like a runtime alias but is never used by
    // runtime code stays on the logical side of the boundary. Machine scalar
    // carriers are admitted logical values now, so this one checks.
    let checked = check("type A = i64; fn main() -> Unit ! {} {}").unwrap();
    assert!(checked.logical_definitions().iter().any(|name| name == "A"));
    rejects(
        "type A = Char; fn main() -> Unit ! {} {}",
        "not supported by the logical subset",
    );
}

#[test]
fn dependent_erased_parameters_use_open_contexts_and_call_site_substitution() {
    let source = r#"
        total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
        fn consume(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { 7 }
        fn outer(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { consume(n, p) }
        fn main() -> i64 ! {panic} { consume(0, truth()) + outer(0, truth()) }
    "#;
    assert_eq!(evaluate(source), 14);
    // An erased natural *value* parameter is still a kernel term, not a runtime
    // value; passing the same proof through two erased binders is checked.
    let nested = r#"
        total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
        fn consume(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { 9 }
        fn main() -> i64 ! {} { consume(0, truth()) }
    "#;
    assert_eq!(evaluate(nested), 9);
}

#[test]
fn dependent_erased_parameters_reject_wrong_proofs_and_runtime_values() {
    rejects(
        r#"
        total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }
        fn consume(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { 7 }
        fn main() -> i64 ! {} { consume(1, truth()) }
        "#,
        "proof does not establish",
    );
    rejects(
        "fn consume(erased n: Nat) -> i64 ! {} { n }
         fn main() -> i64 ! {} { 0 }",
        "no runtime value",
    );
    rejects(
        "fn consume(erased n: Nat) -> i64 ! {} { 7 }
         fn main() -> i64 ! {} { let n = 0; consume(n) }",
        "runtime scalar is a symbolic index, not erased evidence",
    );
    // A machine i64 is not mathematically Nat: no implicit cast makes a
    // runtime scalar into an unbounded logical index.
    rejects(
        "fn bad(n: i64, erased p: Eq<Nat, n, n>) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "type mismatch",
    );
    rejects(
        "fn bad<T: Type>(erased p: Eq<T, T, T>) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "runtime or generic binding 'T'",
    );
    rejects(
        "fn bad(erased n: Nat) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { bad(_) }",
        "cannot discharge a logical proposition",
    );
}

#[test]
fn dependent_arrays_agree_between_reference_and_native_and_do_not_allocate() {
    use std::process::Command;
    let source = r#"
        #[noalloc]
        fn identity<T: Type, N: Nat>(xs: [T; N]) -> [T; N] ! {} { xs }
        #[noalloc]
        fn last<T: Type, N: Nat>(xs: [T; N]) -> T ! {panic} { xs[N - 1] }
        fn main() -> i64 ! {panic} {
            let a: [i64; 4] = [1, 2, 3, 42];
            let b = identity(a);
            last(b)
        }
    "#;
    let program = checked(source);
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);

    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("dependent-arrays");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(binary).output().unwrap();
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stderr.is_empty());
}

#[test]
fn dependent_array_layout_and_specialization_budgets_are_explicit() {
    rejects(
        "fn main() -> i64 ! {panic} { let a: [i64; 32] = []; 0 }",
        "32-word",
    );
    // Each distinct natural argument is a distinct checked instance.
    let mut body = String::from(
        "fn count<N: Nat>(x: i64) -> i64 ! {} { x } fn main() -> i64 ! {panic} { let mut s = 0;",
    );
    for n in 0..260 {
        body.push_str(&format!(" s = count::<{n}>(s);"));
    }
    body.push_str(" s }");
    rejects(&body, "256 function instances");
}
