use kush::executable::check;

fn value(source: &str, expected: i64) {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
}
fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[test]
fn natural_grades_require_exact_copyable_use_counts() {
    value(
        "fn two(x: i64 @[2]) -> i64 ! {panic} { x + x } fn main() -> i64 ! {panic} { two(21) }",
        42,
    );
    value(
        "fn three(x: i64 @[3]) -> i64 ! {panic} { x + x + x } fn main() -> i64 ! {panic} { three(14) }",
        42,
    );
    value(
        "fn sum(x: i64 @[1 + 1]) -> i64 ! {panic} { x + x } fn main() -> i64 ! {panic} { sum(21) }",
        42,
    );
    value(
        "fn four(x: i64 @[(1 + 1) * 2]) -> i64 ! {panic} { x + x + x + x } fn main() -> i64 ! {panic} { four(1) }",
        4,
    );
    value(
        "fn unlimited(x: i64 @[many]) -> i64 ! {panic} { x + x + x } fn main() -> i64 ! {panic} { unlimited(14) }",
        42,
    );
    value(
        "fn ghost(x: i64 @[0]) -> i64 ! {} { 42 } fn main() -> i64 ! {} { ghost(1) }",
        42,
    );
    // Annihilation: a zero-use result cannot duplicate even under `many`.
    value(
        "fn zero(x: i64 @[many * 0]) -> i64 ! {} { 42 } fn main() -> i64 ! {} { zero(1) }",
        42,
    );
    rejects(
        "fn zero(x: i64 @[many * 0]) -> i64 ! {} { x } fn main() -> i64 ! {} { zero(1) }",
        "grade @[0]",
    );
    // A zero-grade local is legal when nothing observes it.
    value("fn main() -> i64 ! {} { let x: i64 @[0] = 7; 42 }", 42);
    rejects(
        "fn f(x: i64 @[2]) -> i64 ! {} { x } fn main() -> i64 ! {} { f(1) }",
        "requires exactly 2",
    );
    rejects(
        "fn f(x: i64 @[2]) -> i64 ! {panic} { x + x + x } fn main() -> i64 ! {panic} { f(1) }",
        "requires exactly 2",
    );
    rejects(
        "fn f(x: i64 @[0]) -> i64 ! {} { x } fn main() -> i64 ! {} { f(1) }",
        "grade @[0]",
    );
    // `@[1]` still means exactly one use for a copyable value.
    value("fn main() -> i64 ! {} { let x: i64 @[1] = 42; x }", 42);
    rejects(
        "fn main() -> i64 ! {} { let x: i64 @[1] = 1; 42 }",
        "requires exactly 1",
    );
}

#[test]
fn grade_expressions_and_annotated_positions_are_checked() {
    rejects(
        "fn f(x: i64 @[18446744073709551615 + 1]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "overflows",
    );
    rejects(
        "fn f(x: i64 @[1 - 1]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "expected ']' after grade",
    );
    rejects(
        "fn f(x: i64 @[Nope]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "unknown name",
    );
    rejects(
        "fn f() -> i64 @[1] ! {} { 1 } fn main() -> i64 ! {} { f() }",
        "must-use `@[1]` contract",
    );
    rejects(
        "struct S { x: i64 @[1] } fn main() -> i64 ! {} { 0 }",
        "stored fields",
    );
    rejects(
        "fn f(b: Box<i64 @[1]>) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "nested type arguments",
    );
    rejects(
        "fn f(erased p: {1 == 1} @[1]) -> i64 ! {} { 1 } fn main() -> i64 ! {} { f(_) }",
        "erased parameters",
    );
    // A destructuring binding cannot hide a single grade over several values.
    rejects(
        "struct P { a: i64, b: i64 } fn f() -> i64 ! {} { let P { a, b }: P @[1] = P { a: 1, b: 2 }; a + b } fn main() -> i64 ! {} { f() }",
        "simple name binding",
    );
}

#[test]
fn grades_can_be_abstract_and_are_specialized_explicitly() {
    value(
        "fn dup<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x } fn main() -> i64 ! {panic} { dup::<2>(21) }",
        42,
    );
    rejects(
        "fn dup<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x } fn main() -> i64 ! {panic} { dup::<1>(21) }",
        "requires exactly 1",
    );
    rejects(
        "fn dup<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x } fn main() -> i64 ! {panic} { dup(21) }",
        "cannot infer usage grade",
    );
    value(
        "fn first<T, G: Grade>(x: T @[G], fallback: T) -> T ! {} { x } fn main() -> i64 ! {} { first::<i64, 1>(42, 0) }",
        42,
    );
    value(
        "fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x } fn main() -> i64 ! {panic} { four::<1 + 1>(1) }",
        4,
    );
    rejects(
        "fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x } fn main() -> i64 ! {panic} { four::<1>(1) }",
        "requires exactly 2",
    );
    // A caller's abstract grade is forwarded to another abstract grade.
    value(
        "fn twice<H: Grade>(x: i64 @[H]) -> i64 ! {panic} { x + x } \
         fn four<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { twice::<G>(x) } \
         fn main() -> i64 ! {panic} { four::<2>(21) }",
        42,
    );
    rejects(
        "fn twice<H: Grade>(x: i64 @[H]) -> i64 ! {panic} { x + x } \
         fn four<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { twice::<G>(x) } \
         fn main() -> i64 ! {panic} { four::<1>(21) }",
        "requires exactly 1",
    );
}

#[test]
fn owning_and_linear_storage_is_never_duplicated_or_silently_discarded() {
    for (source, fragment) in [
        (
            "fn f(b: Box<i64> @[2]) -> i64 ! {alloc,panic} { Box.take(b) } fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "would duplicate",
        ),
        (
            "fn f(b: Box<i64> @[0]) -> i64 ! {alloc,panic} { 1 } fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "silently discard",
        ),
        (
            "fn f(b: Box<i64> @[many]) -> i64 ! {alloc,panic} { Box.take(b) } fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "owns resources",
        ),
        (
            "#[linear] enum L { A(i64) } fn f(x: L @[2]) -> i64 ! {} { match x { L.A(n) => n } } fn main() -> i64 ! {} { f(L.A(1)) }",
            "would duplicate",
        ),
        (
            "struct S { b: Bytes } fn f(s: S @[2]) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
            "would duplicate",
        ),
    ] {
        rejects(source, fragment);
    }
    // Borrowing is not a consumption: one borrow plus one take is one move.
    value(
        "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { Box.read(&b) + Box.take(b) } fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
        2,
    );
    rejects(
        "fn f(b: Box<i64> @[1]) -> i64 ! {} { Box.read(&b) } fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
        "linear value is not consumed",
    );
    // A wildcard/omitted field would silently destroy a `@[1]` owner.
    for source in [
        "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { match b { _ => 0 } } \
         fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
        "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { let _ = b; 0 } \
         fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
        "enum E { A(Box<i64>, Box<i64>) } \
         fn f(e: E @[1]) -> i64 ! {alloc,panic} { match e { E.A(x, _) => Box.take(x) } } \
         fn main() -> i64 ! {alloc,panic} { f(E.A(Box.new(1), Box.new(2))) }",
        "enum E { A(Box<i64>) } \
         fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { match E.A(b) { _ => 0 } } \
         fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
    ] {
        rejects(source, "ignores a linear value");
    }
    // Linearity is not laundered through ungraded locals, statement discards,
    // constructors, or ungraded callees.
    for (source, fragment) in [
        (
            "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { let y = b; 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is not consumed",
        ),
        (
            "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { b; 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is discarded",
        ),
        (
            "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { drop({ b }); 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear values cannot be dropped",
        ),
        (
            "fn g(y: Box<i64>) -> i64 ! {alloc,panic} { 0 } \
             fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { g(b) } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "ungraded parameter",
        ),
        (
            "enum E { A(Box<i64>) } fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { E.A(b); 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is discarded",
        ),
        (
            "enum E { A(Box<i64>) } fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { let y = E.A(b); 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is not consumed",
        ),
        (
            "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { Box.new(b); 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is discarded",
        ),
        (
            "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { \
                let mut y = Box.new(0); y = b; 0 } \
             fn main() -> i64 ! {alloc,panic} { f(Box.new(1)) }",
            "linear value is not consumed",
        ),
        (
            "fn f(v: Vec<i64> @[1]) -> i64 ! {alloc,panic} { let w = Vec.push(v, 1); 0 } \
             fn main() -> i64 ! {alloc,panic} { let v: Vec<i64> = Vec.new(); f(v) }",
            "vector operation would store",
        ),
    ] {
        rejects(source, fragment);
    }
    value(
        "fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { \
            let mut y = Box.new(0); y = b; Box.take(y) } \
         fn main() -> i64 ! {alloc,panic} { f(Box.new(42)) }",
        42,
    );
    value(
        "fn g(y: Box<i64> @[1]) -> i64 ! {alloc,panic} { Box.take(y) } \
         fn f(b: Box<i64> @[1]) -> i64 ! {alloc,panic} { g(b) } \
         fn main() -> i64 ! {alloc,panic} { f(Box.new(42)) }",
        42,
    );
    // A copyable `@[1]` local is exactly-once and, like the original linear
    // semantics, may not be implicitly destroyed by `drop`.
    rejects(
        "fn main() -> i64 ! {} { let x: i64 @[1] = 1; drop(x); 42 }",
        "linear values cannot be dropped",
    );
}

#[test]
fn branch_short_circuit_and_early_exit_paths_must_agree() {
    value(
        "fn f(c: Bool, x: i64 @[2]) -> i64 ! {panic} { if c { x + x } else { x + x } } \
         fn main() -> i64 ! {panic} { f(true, 21) }",
        42,
    );
    rejects(
        "fn f(c: Bool, x: i64 @[2]) -> i64 ! {panic} { if c { x + x } else { x } } \
         fn main() -> i64 ! {panic} { f(true, 21) }",
        "different number of times",
    );
    value(
        "enum E { A, B } fn f(e: E, x: i64 @[2]) -> i64 ! {panic} { match e { E.A => x + x, E.B => x + x } } \
         fn main() -> i64 ! {panic} { f(E.B, 21) }",
        42,
    );
    rejects(
        "enum E { A, B } fn f(e: E, x: i64 @[2]) -> i64 ! {panic} { match e { E.A => x + x, E.B => x } } \
         fn main() -> i64 ! {panic} { f(E.A, 21) }",
        "different number of times",
    );
    rejects(
        "fn f(c: Bool, x: i64 @[1]) -> i64 ! {panic} { if c && { x; true } { 1 } else { 0 } } \
         fn main() -> i64 ! {panic} { f(true, 1) }",
        "short-circuit",
    );
    // Guards may run a path-dependent number of times.
    rejects(
        "enum E { A, B } fn f(e: E, x: i64 @[2]) -> i64 ! {panic} { match e { E.A if x > 0 => x, _ => x + x } } \
         fn main() -> i64 ! {panic} { f(E.A, 1) }",
        "match guard",
    );
    rejects(
        "enum E { A, B } fn f(e: E) -> i64 ! {panic} { let mut x: i64 @[1] = 1; \
         match e { E.A if { x = 2; true } => 0, _ => x } } \
         fn main() -> i64 ! {panic} { f(E.A) }",
        "inside a match guard",
    );
    value(
        "fn f(c: Bool, x: i64 @[1]) -> i64 ! {panic} { if c { return x; } x } \
         fn main() -> i64 ! {panic} { f(true, 42) }",
        42,
    );
    rejects(
        "fn f(c: Bool, x: i64 @[1]) -> i64 ! {} { if c { return 0; } x } fn main() -> i64 ! {} { f(true, 42) }",
        "before this return",
    );
    value(
        "enum Result<T,E>{Ok(T),Err(E)} \
         fn f(x: i64 @[1], r: Result<i64,i64>) -> Result<i64,i64> ! {panic} { let y = x; let z = r?; Ok(y) } \
         fn main() -> i64 ! {panic} { match f(42, Ok(1)) { Ok(n) => n, Err(e) => e } }",
        42,
    );
    rejects(
        "enum Result<T,E>{Ok(T),Err(E)} \
         fn f(x: i64 @[1], r: Result<i64,i64>) -> Result<i64,i64> ! {panic} { let y = r?; Ok(x) } \
         fn main() -> i64 ! {panic} { match f(42, Ok(1)) { Ok(n) => n, Err(e) => e } }",
        "early error return",
    );
}

#[test]
fn loops_restore_outer_counts_and_check_per_iteration_obligations() {
    value(
        "fn f(n: i64, x: i64 @[1]) -> i64 ! {panic} { let mut i = 0; while i < n { i = i + 1; } x } \
         fn main() -> i64 ! {panic} { f(3, 42) }",
        42,
    );
    rejects(
        "fn f(n: i64, x: i64 @[1]) -> i64 ! {panic} { let mut i = 0; while i < n { x; i = i + 1; } x } \
         fn main() -> i64 ! {panic} { f(3, 42) }",
        "unknown number of times",
    );
    // Use and reassign each iteration restores the loop-head count.
    value(
        "fn f(n: i64) -> i64 ! {panic} { \
           let mut x: i64 @[1] = 0; let mut i = 0; \
           while i < n { x; x = i; i = i + 1; } x } \
         fn main() -> i64 ! {panic} { f(3) }",
        2,
    );
    value(
        "fn f(n: i64) -> i64 ! {panic} { \
           let mut i = 0; \
           while i < n { let y: i64 @[2] = i; y + y; i = i + 1; } i } \
         fn main() -> i64 ! {panic} { f(3) }",
        3,
    );
    rejects(
        "fn f(n: i64) -> i64 ! {panic} { \
           let mut i = 0; \
           while i < n { let y: i64 @[2] = i; y; i = i + 1; } i } \
         fn main() -> i64 ! {panic} { f(3) }",
        "requires exactly 2",
    );
    rejects(
        "fn f(x: i64 @[1]) -> i64 ! {panic} { while x > 0 { } 0 } fn main() -> i64 ! {panic} { f(0) }",
        "while condition",
    );
    // A `loop` break may consume an outer exact-grade value exactly once.
    value(
        "fn f(x: i64 @[1]) -> i64 ! {panic} { loop { break x; } } fn main() -> i64 ! {panic} { f(42) }",
        42,
    );
    // `while` may not run at all, so a break-path use is not exact.
    rejects(
        "fn f(c: Bool, x: i64 @[1]) -> i64 ! {panic} { while c { x; break; } x } \
         fn main() -> i64 ! {panic} { f(false, 42) }",
        "zero-iteration and break paths",
    );
}

#[test]
fn calls_compose_parameter_usage_demands() {
    value(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x } \
         fn four(x: i64 @[4]) -> i64 ! {panic} { twice(x) + twice(x) } \
         fn main() -> i64 ! {panic} { four(10) }",
        40,
    );
    value(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x } \
         fn four(x: i64 @[4]) -> i64 ! {panic} { twice(x) + twice(x) } \
         fn six(x: i64 @[6]) -> i64 ! {panic} { twice(x) + four(x) } \
         fn main() -> i64 ! {panic} { six(7) }",
        42,
    );
    rejects(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x } \
         fn four(x: i64 @[2]) -> i64 ! {panic} { twice(x) + twice(x) } \
         fn main() -> i64 ! {panic} { four(10) }",
        "used 4 time",
    );
    // An explicit `many` demand is not compatible with a finite exact bind.
    rejects(
        "fn use_many(x: i64 @[many]) -> i64 ! {panic} { x + x } \
         fn main() -> i64 ! {panic} { let y: i64 @[2] = 1; use_many(y) }",
        "exactly 2",
    );
}

#[test]
fn graded_parameters_coexist_with_erased_logical_proofs() {
    value(
        "fn f(x: i64 @[2], erased p: { 0 == 0 }) -> i64 ! {panic} { x + x } \
         fn main() -> i64 ! {panic} { f(21, _) }",
        42,
    );
    rejects(
        "fn f(x: i64 @[2], erased p: { 0 == 1 }) -> i64 ! {panic} { x + x } \
         fn main() -> i64 ! {panic} { f(21, _) }",
        "cannot prove",
    );
}

#[test]
fn native_and_reference_execution_agree_on_graded_programs() {
    use std::process::Command;

    let source = "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x } \
         fn four(x: i64 @[4]) -> i64 ! {panic} { twice(x) + twice(x) } \
         fn main() -> i64 ! {alloc, panic} { \
             let boxed: Box<i64> @[1] = Box.new(four(10) + 2); \
             let mut owner = Box.new(0); \
             owner = boxed; \
             Box.take(owner) }";
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations);

    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("grades");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(binary).output().unwrap();
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stderr.is_empty());
}

#[test]
fn linear_once_closures_transfer_exact_grades_to_their_captures() {
    // A copyable @[1] capture becomes a linear-once callable: the closure must
    // be called and the capture observed exactly once.
    value(
        "fn main() -> i64 ! {alloc, panic} {
            let x: i64 @[1] = 41;
            let f: linear once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} { x + 1 };
            f()
         }",
        42,
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let x: i64 @[1] = 41;
            let f = fn() -> i64 ! {panic} { x + 1 };
            42
         }",
        "linear value is not consumed",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let x: i64 @[2] = 41;
            let f = fn() -> i64 ! {panic} { x + x };
            f()
         }",
        "graded @[2]",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let x: i64 @[0] = 41;
            let f = fn() -> i64 ! {panic} { x };
            f()
         }",
        "graded @[0]",
    );
    // Ordinary affine captures remain ordinary affine once closures.
    value(
        "fn main() -> i64 ! {alloc, panic} {
            let n = Box.new(41);
            let f = fn() -> i64 ! {panic} { Box.take(n) };
            let unused = fn() -> i64 ! {panic} { 0 };
            f()
         }",
        41,
    );
}
