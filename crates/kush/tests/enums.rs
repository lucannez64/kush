use kush::executable::check;
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
}
fn evaluate(source: &str) -> (i64, String) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let code = program.evaluate(&mut output).unwrap();
    (code, String::from_utf8(output).unwrap())
}
#[test]
fn result_parser_checks_and_evaluates() {
    assert_eq!(
        evaluate(include_str!("../../../examples/results.kush")),
        (0, "42\n65\n7\n99\n".into())
    );
}
#[test]
fn constructors_are_nominal_typed_and_have_checked_arity() {
    rejects(
        "enum A { X(i64) } enum B { X(i64) } fn f() -> A ! {} { B.X(1) }",
        "different enum",
    );
    rejects(
        "enum E { A(i64), B } fn main() -> Unit ! {} { let x: E = E.A(true); }",
        "type mismatch",
    );
    rejects(
        "enum E { A(i64), B } fn main() -> Unit ! {} { let x = E.A(); }",
        "arity",
    );
    rejects(
        "enum E { A(i64), B } fn main() -> Unit ! {} { let x = E.A; }",
        "tuple variants",
    );
    rejects(
        "enum E { A(i64), B } fn main() -> Unit ! {} { let x = E.B(); }",
        "unit variants",
    );
    rejects(
        "enum E { A(i64) } fn main() -> Unit ! {} { let x = E.A(1); x == x; }",
        "enum equality",
    );
    rejects(
        "enum E { A } fn main() -> Unit ! {} { let x = E.A; x + 1; }",
        "type mismatch",
    );
}
#[test]
fn generic_constructors_use_context_or_explicit_specialization() {
    let source = "enum Option<T> { None, Some(T) }
        fn f(x: Option<i64>) -> i64 ! {} { match x { Some(n) => n, None => 0 } }
        fn main() -> i64 ! {} {
            let mut x: Option<i64> = Some(3); x = None;
            let y = Some::<i64>(7); f(y)
        }";
    assert_eq!(evaluate(source).0, 7);
    rejects(
        "enum Option<T> { None, Some(T) } fn main() -> Unit ! {} { let x = None; }",
        "expected enum type",
    );
    rejects(
        "enum Option<T> { None, Some(T) } fn main() -> Unit ! {} { let x: Option<Bool> = Some::<i64>(1); }",
        "type mismatch",
    );
    rejects(
        "enum Option<T> { None, Some(T) } fn main() -> Unit ! {} { let x: Option = None; }",
        "type arguments",
    );
    rejects(
        "enum Option<T> { None, Some(T) } fn main() -> Unit ! {} { let x = None::<i64, Bool>; }",
        "type arguments",
    );
}
#[test]
fn nested_payload_coverage_checks_cross_arm_combinations() {
    let prefix = "enum E { Pair(Bool, Bool), Empty } ";
    check(&format!("{prefix} fn f(x: E) -> i64 ! {{}} {{ match x {{ E.Pair(true, _) => 1, E.Pair(false, true) => 2, E.Pair(false, false) => 3, E.Empty => 4 }} }}")).unwrap();
    rejects(
        &format!(
            "{prefix} fn f(x: E) -> i64 ! {{}} {{ match x {{ E.Pair(true, _) => 1, E.Pair(_, true) => 2, E.Empty => 4 }} }}"
        ),
        "non-exhaustive",
    );
    rejects(
        &format!(
            "{prefix} fn f(x: E) -> i64 ! {{}} {{ match x {{ E.Pair(_, _) => 1, E.Pair(false, true) => 2, E.Empty => 4 }} }}"
        ),
        "unreachable",
    );
    rejects(
        &format!(
            "{prefix} fn f(x: E) -> i64 ! {{}} {{ match x {{ E.Pair(_, _) if true => 1, E.Empty => 4 }} }}"
        ),
        "non-exhaustive",
    );
    rejects(
        "enum E { A(i64), B } fn f(x: E) -> i64 ! {} { match x { E.A(0) => 1, E.B => 2 } }",
        "non-exhaustive",
    );
    rejects(
        "enum A { X } enum B { X } fn f(x: A) -> i64 ! {} { match x { B.X => 1, _ => 0 } }",
        "different enum",
    );
}
#[test]
fn coverage_matches_an_independent_finite_domain_model() {
    // Independently enumerate the five values of Pair(Bool,Bool) | Empty.
    let patterns = [
        ("E.Pair(true, true)", 0b00001),
        ("E.Pair(true, false)", 0b00010),
        ("E.Pair(false, true)", 0b00100),
        ("E.Pair(false, false)", 0b01000),
        ("E.Pair(true, _)", 0b00011),
        ("E.Pair(_, false)", 0b01010),
        ("E.Pair(_, _)", 0b01111),
        ("E.Empty", 0b10000),
        ("_", 0b11111),
    ];
    for selection in 0..512_u32 {
        let mut covered = 0;
        let mut reachable = true;
        let mut arms = Vec::new();
        for (index, (pattern, mask)) in patterns.iter().enumerate() {
            if selection & (1 << index) == 0 {
                continue;
            }
            reachable &= mask & !covered != 0;
            covered |= mask;
            arms.push(format!("{pattern} => {index}"));
        }
        let source = format!(
            "enum E {{ Pair(Bool, Bool), Empty }} fn f(x: E) -> i64 ! {{}} {{ match x {{ {} }} }}",
            arms.join(",")
        );
        assert_eq!(
            check(&source).is_ok(),
            reachable && covered == 0b11111,
            "{source}"
        );
    }
}
#[test]
fn alternatives_bind_identical_names_with_identical_types() {
    let source = "enum E { Left(i64, Bool), Right(Bool, i64) }
        fn f(x: E) -> i64 ! {} { match x { E.Left(n, _) | E.Right(_, n) => n } }
        fn main() -> i64 ! {} { f(E.Right(true, 19)) }";
    assert_eq!(evaluate(source).0, 19);
    rejects(
        "enum E { A(i64), B(Bool) } fn f(x: E) -> Unit ! {} { match x { E.A(n) | E.B(n) => () } }",
        "type mismatch",
    );
    rejects(
        "enum E { A(i64), B(i64) } fn f(x: E) -> Unit ! {} { match x { E.A(a) | E.B(b) => () } }",
        "same names",
    );
    rejects(
        "enum E { A(i64) } fn f(x: E) -> i64 ! {} { match x { E.A() => 0 } }",
        "arity",
    );
    rejects(
        "enum E { A(Bool) } fn f(x: E) -> i64 ! {} { match x { E.A(0) => 0, _ => 1 } }",
        "type mismatch",
    );
}
#[test]
fn try_requires_exact_result_shape_and_identical_error_types() {
    rejects("fn main() -> i64 ! {} { 1? }", "conventional enum Result");
    rejects(
        "enum Result<T,E> { Ok(T), Err(E) } fn f(x: Result<i64, Bool>) -> i64 ! {} { x? }",
        "conventional enum Result",
    );
    rejects(
        "enum Result<T,E> { Ok(T), Err(E) } fn f(x: Result<i64, Bool>) -> Result<i64, i64> ! {} { Ok(x?) }",
        "type mismatch",
    );
    rejects(
        "enum Result<T,E> { Ok(E), Err(T) } fn f(x: Result<i64, i64>) -> Result<i64, i64> ! {} { Ok(x?) }",
        "conventional enum Result",
    );
    rejects(
        "enum Result<T,E> { Ok(T), Err(E), Extra } fn f(x: Result<i64, i64>) -> Result<i64, i64> ! {} { Ok(x?) }",
        "conventional enum Result",
    );
}
#[test]
fn finite_inline_layouts_have_explicit_limits() {
    rejects("enum Empty {} fn main() -> Unit ! {} {}", "1..64");
    rejects(
        "enum Recursive { Again(Recursive) } fn main() -> Unit ! {} {}",
        "recursive inline",
    );
    rejects(
        "enum A { Again(B) } enum B { Again(A) } fn main() -> Unit ! {} {}",
        "recursive inline",
    );
    rejects(
        "enum G<T> { Again(G<T>) } fn f(x: G<i64>) -> Unit ! {} {}",
        "recursive inline",
    );
    rejects(
        "enum G<n: Nat> { Value(i64) } fn main() -> Unit ! {} {}",
        "ordinary types",
    );
    rejects(
        "enum G<T: Type> { Value(T): G<i64> } fn main() -> Unit ! {} {}",
        "without indexed",
    );
    rejects(
        "enum G { Value { n: i64 } } fn main() -> Unit ! {} {}",
        "unit or tuple",
    );
    let fields = vec!["i64"; 32].join(",");
    rejects(
        &format!("enum Wide {{ Value({fields}) }} fn main() -> Unit ! {{}} {{}}"),
        "32-word",
    );
    rejects("enum E { A } fn main() -> E ! {} { E.A }", "main must");
}

#[test]
fn coverage_budget_and_constructor_shadowing_fail_with_diagnostics() {
    let arms = (0..350)
        .map(|n| format!("{n} => 0"))
        .collect::<Vec<_>>()
        .join(",");
    rejects(
        &format!("fn f(n: i64) -> i64 ! {{}} {{ match n {{ {arms}, _ => 1 }} }}"),
        "coverage budget",
    );
    rejects(
        "enum E { A } fn main() -> Unit ! {} { let A = 1; let x: E = A; }",
        "enum constructor pattern requires an enum value",
    );
}
