use kush::executable::check;

fn value(source: &str) -> i64 {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    result
}

fn balanced(source: &str) -> i64 {
    value(source)
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[test]
fn named_and_explicitly_specialized_function_values_are_callable() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn id<T>(x: T) -> T ! {panic} { x }
             fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn main() -> i64 ! {panic} { apply(id::<i64>) }"
        ),
        42
    );
    // A generic function value can also be inferred from the expected arrow type.
    assert_eq!(
        value(
            "fn id<T>(x: T) -> T ! {panic} { x }
             fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn main() -> i64 ! {panic} { apply(id) }"
        ),
        42
    );
    // Function-valued results and immediate calls.
    assert_eq!(
        value(
            "type Unary = fn(i64) -> i64 ! {panic};
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn get() -> Unary ! {panic} { inc }
             fn main() -> i64 ! {panic} { get()(41) }"
        ),
        42
    );
}

#[test]
fn explicit_noncapturing_lambdas_are_function_pointers() {
    let program = check(
        "fn main() -> i64 ! {panic} {
            let double = fn(x: i64) -> i64 ! {panic} { x * 2 };
            double(21)
        }",
    )
    .unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(
        stats.allocations, 0,
        "a noncapturing lambda is not a heap object"
    );
}

#[test]
fn capturing_closures_move_affine_owners_into_an_owned_environment() {
    let program = check(
        "fn main() -> i64 ! {alloc, panic} {
            let n = Box.new(41);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            f(1)
        }",
    )
    .unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stats.allocations > 0);
}

#[test]
fn captured_owners_are_cleaned_on_drop_return_try_and_partial_arguments() {
    // Dropped without a call.
    assert_eq!(
        balanced(
            "fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
                42
            }"
        ),
        42
    );
    // Returned, then dropped by the caller.
    assert_eq!(
        balanced(
            "fn make() -> (once fn(i64) -> i64 ! {alloc, panic}) ! {alloc, panic} {
                let n = Box.new(1);
                fn(x: i64) -> i64 ! {panic} { Box.take(n) + x }
            }
            fn main() -> i64 ! {alloc, panic} { let f = make(); 42 }"
        ),
        42
    );
    // `?` error path inside an enclosing function.
    assert_eq!(
        balanced(
            "enum Result<T, E> { Ok(T), Err(E) }
             fn bad() -> Result<i64, i64> ! {} { Err(7) }
             fn useit(r: Result<i64, i64>) -> Result<i64, i64> ! {alloc, panic} {
                let n = Box.new(1);
                let g = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
                let x = r?;
                Ok(g(x))
             }
             fn main() -> i64 ! {alloc, panic} {
                match useit(bad()) { Ok(v) => v, Err(e) => e + 35 }
             }"
        ),
        42
    );
    // `?` error path inside the closure body itself.
    assert_eq!(
        balanced(
            "enum Result<T, E> { Ok(T), Err(E) }
             fn bad() -> Result<i64, i64> ! {} { Err(7) }
             fn useit(r: Result<i64, i64>) -> Result<i64, i64> ! {alloc, panic} {
                let n = Box.new(1);
                let f = fn() -> Result<i64, i64> ! {alloc, panic} {
                    let x = r?;
                    Ok(Box.take(n) + x)
                };
                f()
             }
             fn main() -> i64 ! {alloc, panic} {
                match useit(bad()) { Ok(v) => v, Err(e) => e + 35 }
             }"
        ),
        42
    );
    // An early return inside the closure body drops its remaining captures.
    assert_eq!(
        balanced(
            "fn call(f: once fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(1) }
             fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let g = fn(x: i64) -> i64 ! {panic} {
                    if x > 0 { return 5; }
                    Box.take(n) + x
                };
                call(g)
             }"
        ),
        5
    );
    // An early return while evaluating a later argument still drops the callee.
    assert_eq!(
        balanced(
            "fn call(f: once fn(i64, i64) -> i64 ! {panic}) -> i64 ! {panic} {
                f(1, { return 5; })
             }
             fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let g = fn(a: i64, b: i64) -> i64 ! {panic} { Box.take(n) + a + b };
                call(g)
             }"
        ),
        5
    );
}

#[test]
fn arrow_subtyping_is_contravariant_covariant_and_effect_inclusive() {
    // Parameter contravariance: a callee accepting a wider union can be used
    // where only a narrower argument domain is promised.
    assert_eq!(
        value(
            "fn classify(x: i64 | Bool) -> i64 ! {panic} {
                match x { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } }
             }
             fn apply(g: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { g(42) }
             fn main() -> i64 ! {panic} { apply(classify) }"
        ),
        42
    );
    // Result covariance: a narrower result can be used where a wider union is
    // expected.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply(f: fn(i64) -> i64 | Bool ! {panic}) -> i64 ! {panic} {
                match f(41) { i64 @ n => n, Bool @ _ => 0 }
             }
             fn main() -> i64 ! {panic} { apply(inc) }"
        ),
        42
    );
    // Effect-row inclusion: fewer effects may be used where more are allowed.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply(f: fn(i64) -> i64 ! {alloc, panic}) -> i64 ! {alloc, panic} {
                f(41)
             }
             fn main() -> i64 ! {alloc, panic} { apply(inc) }"
        ),
        42
    );
    // An allocating/effectful callee may not be hidden behind a pure signature.
    rejects(
        "fn make(x: i64) -> i64 ! {alloc, panic} { Box.take(Box.new(x)) }
         fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
         fn main() -> i64 ! {panic} { apply(make) }",
        "type mismatch",
    );
    // The wrong parameter direction is rejected.
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn apply(g: fn(i64 | Bool) -> i64 ! {panic}) -> i64 ! {panic} { g(42) }
         fn main() -> i64 ! {panic} { apply(inc) }",
        "type mismatch",
    );
    // A wider result cannot be narrowed.
    rejects(
        "fn choose() -> i64 | Bool ! {panic} { 1 }
         fn apply(f: fn() -> i64 ! {panic}) -> i64 ! {panic} { f() }
         fn main() -> i64 ! {panic} { apply(choose) }",
        "type mismatch",
    );
}

#[test]
fn function_grade_contracts_reject_unsound_modality_conversions() {
    assert_eq!(
        value(
            "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
             fn apply(f: fn(i64 @[2]) -> i64 ! {panic}, x: i64 @[2]) -> i64 ! {panic} { f(x) }
             fn main() -> i64 ! {panic} { apply(twice, 21) }"
        ),
        42
    );
    rejects(
        "fn once(x: i64 @[1]) -> i64 ! {panic} { x }
         fn apply(f: fn(i64 @[2]) -> i64 ! {panic}) -> i64 ! {panic} { f(21) }
         fn main() -> i64 ! {panic} { apply(once) }",
        "type mismatch",
    );
    rejects(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn apply(f: fn(i64 @[1]) -> i64 ! {panic}) -> i64 ! {panic} { f(21) }
         fn main() -> i64 ! {panic} { apply(twice) }",
        "type mismatch",
    );
    rejects(
        "fn any(x: i64) -> i64 ! {panic} { x + x }
         fn apply(f: fn(i64 @[1]) -> i64 ! {panic}) -> i64 ! {panic} { f(21) }
         fn main() -> i64 ! {panic} { apply(any) }",
        "type mismatch",
    );
}

#[test]
fn parameter_and_result_union_repacking_uses_checked_adapters() {
    assert_eq!(
        value(
            "fn classify(x: i64 | Bool | Bytes) -> i64 ! {panic} {
                match x { i64 @ n => n, Bool @ b => if b { 41 } else { 0 }, Bytes @ _ => 0 }
             }
             fn apply(g: fn(i64 | Bool) -> i64 ! {panic}) -> i64 ! {panic} { g(true) }
             fn main() -> i64 ! {panic} { apply(classify) }"
        ),
        41
    );
    assert_eq!(
        value(
            "fn make() -> i64 | Bool ! {panic} { 41 }
             fn apply(f: fn() -> i64 | Bool | Bytes ! {panic}) -> i64 ! {panic} {
                match f() { i64 @ n => n, Bool @ _ => 0, Bytes @ _ => 0 }
             }
             fn main() -> i64 ! {panic} { apply(make) }"
        ),
        41
    );
    // A dynamic once value needs a capturing adapter. The adapter owns the
    // source closure and releases both environments on the call.
    assert_eq!(
        balanced(
            "fn apply(f: once fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let g: once fn(i64 | Bool) -> i64 ! {panic} = fn(x: i64 | Bool) -> i64 ! {panic} {
                    match x { i64 @ v => v, Bool @ b => if b { 1 } else { 0 } } + Box.take(n)
                };
                apply(g)
             }"
        ),
        43
    );
}

#[test]
fn pure_function_pointers_require_no_allocation_and_noalloc_rejects_adapters() {
    assert_eq!(
        value(
            "#[noalloc]
             fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    // A representation-changing pure adapter is still generated code, not heap.
    assert_eq!(
        value(
            "#[noalloc]
             fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn classify(x: i64 | Bool) -> i64 ! {panic} {
                match x { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } }
             }
             fn main() -> i64 ! {panic} { apply(classify) }"
        ),
        42
    );
    rejects(
        "#[noalloc]
         fn make(n: Box<i64>) -> i64 ! {panic} {
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            f(41)
         }
         fn main() -> i64 ! {alloc, panic} { make(Box.new(1)) }",
        "requires effects {alloc}",
    );
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         #[noalloc]
         fn use_once(f: once fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(41) }
         #[noalloc]
         fn main() -> i64 ! {panic} {
            let g: fn(i64) -> i64 ! {panic} = inc;
            use_once(g)
         }",
        "requires effects {alloc}",
    );
}

#[test]
fn capturing_borrows_are_scoped_and_linear_captures_are_checked() {
    // A borrowed immutable view may be captured by a lexical `once fn` and
    // called while the owner is live. Construction allocates the environment.
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let values: [i64; 3] = [10, 20, 30];
                let view: &[i64] = &values[..];
                let f = fn(i: i64) -> i64 ! {panic} { Slice.get(view, i) + 1 };
                f(1)
             }"
        ),
        21
    );
    // Capturing a borrowed view cannot be used to launder it through an
    // ordinary function value or an alias.
    rejects(
        "fn id<T>(value: T) -> T ! {panic} { value }
         fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [1, 2];
            let view: &[i64] = &values[..];
            let f = fn(x: i64) -> i64 ! {panic} { Slice.get(view, 0) + x };
            id(f)(0)
         }",
        "scoped",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [1, 2];
            let view: &[i64] = &values[..];
            let f = fn(x: i64) -> i64 ! {panic} { Slice.get(view, 0) + x };
            let alias = f;
            alias(0)
         }",
        "scoped",
    );
    // A linear capture is legal, but the resulting callable is linear-once and
    // the lambda body must consume the capture on every path.
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { x };
            f(42)
         }",
        "linear value is not consumed",
    );
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f: linear once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                f(21)
             }"
        ),
        42
    );
}

#[test]
fn function_values_do_not_bypass_erased_evidence_and_unions_narrow_callables() {
    rejects(
        "fn pos(x: i64, erased proof: { x >= 0 }) -> i64 ! {} { x }
         fn main() -> i64 ! {} { let f = pos; 0 }",
        "erased proof parameters",
    );
    // Distinct callable signatures are heterogeneous union alternatives and
    // are narrowed by a checked type pattern.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn answer() -> i64 ! {panic} { 42 }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
                let g: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = answer;
                let a = match f {
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                let b = match g {
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                a + b - 42
             }"
        ),
        42
    );
    // Incomparable arrows need overloads, not a false claim of disjointness.
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn flag(x: Bool) -> Bool ! {} { x }
         fn main() -> i64 ! {panic} {
            let f: fn(i64) -> i64 ! {panic} & fn(Bool) -> Bool ! {} = inc;
            0
         }",
        "incomparable callable intersections",
    );
}

#[test]
fn wrong_signatures_and_use_after_move_are_rejected() {
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
            let f: fn(i64) -> i64 ! {panic} = inc;
            f(true)
         }",
        "type mismatch",
    );
    rejects(
        "fn zero() -> i64 ! {} { 42 }
         fn main() -> i64 ! {panic} {
            let f: fn() -> i64 ! {} = zero;
            f(1)
         }",
        "wrong argument count",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            f(1);
            f(2)
         }",
        "use after move",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n = Box.new(1);
            let f: fn(i64) -> i64 ! {panic} = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            0
         }",
        "capturing lambda",
    );
}

#[test]
fn indirect_recursion_and_aggregate_arguments_and_results_work() {
    assert_eq!(
        value(
            "fn apply(f: fn(i64) -> i64 ! {panic}, n: i64) -> i64 ! {panic} { f(n) }
             fn down(n: i64) -> i64 ! {panic} {
                if n == 0 { 0 } else { 1 + apply(down, n - 1) }
             }
             fn main() -> i64 ! {panic} { down(8) }"
        ),
        8
    );
    assert_eq!(
        value(
            "struct Pair { left: i64, right: i64 }
             fn make(x: i64) -> Pair ! {panic} { Pair { left: x, right: x + 2 } }
             fn sum(p: Pair) -> i64 ! {panic} { p.left + p.right }
             fn apply(f: fn(i64) -> Pair ! {panic}, x: i64) -> i64 ! {panic} {
                let p = f(x);
                sum(p)
             }
             fn main() -> i64 ! {panic} { apply(make, 20) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn take(b: Box<i64>) -> i64 ! {panic} { Box.take(b) }
             fn apply(f: fn(Box<i64>) -> i64 ! {panic}, b: Box<i64>) -> i64 ! {panic} { f(b) }
             fn main() -> i64 ! {alloc, panic} { apply(take, Box.new(42)) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn make(x: i64) -> Box<i64> ! {alloc, panic} { Box.new(x) }
             fn apply(f: fn(i64) -> Box<i64> ! {alloc, panic}) -> i64 ! {alloc, panic} {
                Box.take(f(42))
             }
             fn main() -> i64 ! {alloc, panic} { apply(make) }"
        ),
        42
    );
}

#[test]
fn generic_higher_order_apply_and_map_infer_and_specialize() {
    assert_eq!(
        value(
            "fn apply<T, U>(x: T, f: fn(T) -> U ! {panic}) -> U ! {panic} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(41, inc) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn map<T, U>(values: Vec<T>, f: fn(T) -> U ! {alloc, panic}) -> Vec<U> ! {alloc, panic} {
                let mut out: Vec<U> = Vec.new();
                let mut i = 0;
                while i < Vec.len(&values) {
                    out = Vec.push(out, f(Vec.get(&values, i)));
                    i = i + 1;
                }
                out
             }
             fn double(x: i64) -> i64 ! {panic} { x * 2 }
             fn main() -> i64 ! {alloc, panic} {
                let mut v: Vec<i64> = Vec.new();
                v = Vec.push(v, 10); v = Vec.push(v, 11);
                let w = map(v, double);
                Vec.get(&w, 0) + Vec.get(&w, 1)
             }"
        ),
        42
    );
    // An explicit specialization produces a distinct callable value.
    assert_eq!(
        value(
            "fn id<T>(x: T) -> T ! {panic} { x }
             fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn main() -> i64 ! {panic} { apply(id::<i64>) }"
        ),
        42
    );
}

#[test]
fn function_example_matches_its_documented_output() {
    let source = include_str!("../../../examples/functions.kush");
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_io_and_stats(&mut std::io::empty(), &mut output)
        .unwrap();
    assert_eq!(result, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    assert_eq!(
        String::from_utf8(output).unwrap(),
        "42\n42\n42\n42\n42\n42\n42\n42\n"
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod native_functions {
    use super::*;
    use kush::native::{self, Scratch};
    use std::{fs, process::Command};

    fn compare(source: &str) {
        let program = check(source).unwrap();
        let mut expected_output = Vec::new();
        let expected_exit = program.evaluate(&mut expected_output).unwrap();
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("program");
        native::build(&program, &binary).unwrap();
        let output = Command::new(&binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_exit as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected_output);
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(&fs::read(binary).unwrap()[..4], b"\x7fELF");
    }

    #[test]
    fn native_and_reference_agree_on_function_values_adapters_and_closures() {
        compare(include_str!("../../../examples/functions.kush"));
        compare(
            "fn apply(f: once fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
             fn classify(x: i64 | Bool) -> i64 ! {panic} {
                match x { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } }
             }
             fn main() -> i64 ! {panic} { apply(classify) }",
        );
    }

    #[test]
    fn native_and_reference_agree_on_effect_rows_callable_unions_and_linear_closures() {
        compare(include_str!("../../../examples/effectful-functions.kush"));
        compare(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn answer() -> i64 ! {panic} { 42 }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
                let w: i64 | fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = f;
                match w {
                    i64 @ n => n,
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                }
             }",
        );
        compare(
            "fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f: linear once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                let g: linear once fn(i64) -> i64 ! {panic} = f;
                g(21)
             }",
        );
        compare(
            "fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f: linear once fn(i64 | Bool) -> i64 ! {panic} =
                    fn(x: i64 | Bool) -> i64 ! {panic} {
                        Box.take(n) + match x { i64 @ v => v + 1, Bool @ _ => 0 }
                    };
                let g: linear once fn(i64) -> i64 ! {panic} = f;
                g(21)
             }",
        );
        compare(
            "struct Pair { left: i64, right: i64 }
             fn make(x: i64) -> Pair ! {panic} { Pair { left: x, right: x + 2 } }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> Pair ! {panic} | fn() -> Pair ! {panic} = make;
                let p = match f {
                    fn(i64) -> Pair ! {panic} @ h => h(20),
                    fn() -> Pair ! {panic} @ h => h(),
                };
                p.left + p.right
             }",
        );
    }
}

#[test]
fn arrow_intersection_preserves_subtype_absorption() {
    let p=check("fn f(x:i64)->i64 ! {} {x} fn main()->i64 ! {panic} {let both:(fn(i64)->i64 ! {}) & (fn(i64)->i64 ! {panic})=f;both(42)}").unwrap();
    assert_eq!(p.evaluate(&mut Vec::new()).unwrap(), 42);
}

#[test]
fn effect_polymorphic_higher_order_functions_infer_and_propagate() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {io, panic} { apply(io_inc, 41) }"
        ),
        42
    );
    // A pure callable infers the empty row for a sole row variable.
    assert_eq!(
        value(
            "fn id(x: i64) -> i64 ! {} { x }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {panic} { apply(id, 42) }"
        ),
        42
    );
    // Explicit row specialization is a separate generic category.
    assert_eq!(
        value(
            "fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {io, panic} { apply::<io | panic>(io_inc, 41) }"
        ),
        42
    );
    // The instantiating effect propagates transitively through a polymorphic
    // caller rather than being hidden by the intermediate signature.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn outer<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                apply(f, x)
             }
             fn main() -> i64 ! {panic} { outer(inc, 41) }"
        ),
        42
    );
    // Effect-polymorphic function type aliases are transparent.
    assert_eq!(
        value(
            "type Mapper<e: Effects> = fn(i64) -> i64 ! {e};
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn map_one<e: Effects>(f: Mapper<e>, x: i64) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {panic} { map_one(inc, 41) }"
        ),
        42
    );
    // Type, effect, and grade parameters can coexist in declaration order.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn mix<T, e: Effects, G: Grade>(x: T @[G], f: fn(T) -> T ! {e}) -> T ! {panic, e} {
                f(x)
             }
             fn main() -> i64 ! {panic} { mix::<i64, panic, 1>(41, inc) }"
        ),
        42
    );
    // A generic effect-polymorphic function value can be inferred from the
    // expected arrow type's effect row.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
             fn take(g: fn(fn(i64) -> i64 ! {panic}, i64) -> i64 ! {panic}) -> i64 ! {panic} {
                g(inc, 41)
             }
             fn main() -> i64 ! {panic} { take(apply) }"
        ),
        42
    );
    // A lambda's declared effect row may mention an enclosing row variable.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn wrap<e: Effects>(f: fn(i64) -> i64 ! {e}) -> once fn(i64) -> i64 ! {e} ! {alloc, panic} {
                fn(x: i64) -> i64 ! {e} { f(x) }
             }
             fn main() -> i64 ! {alloc, panic} {
                let g = wrap(inc);
                g(41)
             }"
        ),
        42
    );
    // Effect-polymorphic map over a vector propagates the callable's row
    // through the loop and the result signature.
    assert_eq!(
        value(
            "fn double(x: i64) -> i64 ! {panic} { x * 2 }
             fn map<T, U, e: Effects>(values: Vec<T>, f: fn(T) -> U ! {e}) -> Vec<U> ! {alloc, panic, e} {
                let mut out: Vec<U> = Vec.new();
                let mut i = 0;
                while i < Vec.len(&values) {
                    out = Vec.push(out, f(Vec.get(&values, i)));
                    i = i + 1;
                }
                out
             }
             fn main() -> i64 ! {alloc, panic} {
                let mut v: Vec<i64> = Vec.new();
                v = Vec.push(v, 10);
                v = Vec.push(v, 11);
                let w = map(v, double);
                Vec.get(&w, 0) + Vec.get(&w, 1)
             }"
        ),
        42
    );
}

#[test]
fn effect_specialization_is_checked_and_stays_separate_from_other_categories() {
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} { f(x) }
         fn main() -> i64 ! {panic} { apply::<io>(alloc_id, 1) }",
        "type mismatch",
    );
    // An unconstrained open row defaults to the principal (least) row `{}`.
    // The call's result row is therefore exactly `{panic}`; the body is
    // rechecked under that specialization, so defaulting cannot hide an effect
    // the body actually performs.
    assert_eq!(
        value(
            "fn apply<e: Effects>(x: i64) -> i64 ! {panic, e} { x }
             fn main() -> i64 ! {panic} { apply(1) }"
        ),
        1
    );
    rejects(
        "fn apply<e: Effects>(x: i64) -> i64 ! {panic, e} { alloc_id(x) }
         fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn main() -> i64 ! {alloc, panic} { apply(1) }",
        "requires effects {alloc}",
    );
    rejects(
        "fn apply<e: Effects>(x: i64) -> i64 ! {panic, e} { x }
         fn main() -> i64 ! {panic} { apply::<i64>(1) }",
        "only io, alloc, suspend, and panic",
    );
    // A shared row variable accumulates the union of every higher-order
    // argument. The specializing caller must declare that union; otherwise the
    // call would hide an effect introduced by a later argument.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
             fn two<e: Effects>(f: fn(i64) -> i64 ! {e}, g: fn(i64) -> i64 ! {e}, x: i64)
                 -> i64 ! {panic, e} { g(f(x)) }
             fn main() -> i64 ! {io, panic} { two(inc, io_inc, 1) }"
        ),
        3
    );
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
         fn two<e: Effects>(f: fn(i64) -> i64 ! {e}, g: fn(i64) -> i64 ! {e}, x: i64)
             -> i64 ! {panic, e} { g(f(x)) }
         fn main() -> i64 ! {panic} { two(inc, io_inc, 1) }",
        "requires effects {io}",
    );
    rejects(
        "fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x }
         fn main() -> i64 ! {panic} { four::<io>(1) }",
        "grade",
    );
    rejects(
        "fn first<N: Nat>(xs: [i64; N]) -> i64 ! {panic} { xs[0] }
         fn main() -> i64 ! {panic} { first::<i64>([42, 0]) }",
        "array length must be a constant",
    );
    rejects(
        "#[noalloc]
         fn poly<e: Effects>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e} { f(1) }
         fn main() -> i64 ! {panic} { 42 }",
        "noalloc contracts cannot be effect-polymorphic",
    );
}

#[test]
fn noalloc_higher_order_contracts_are_checked_independently_of_specialization() {
    assert_eq!(
        value(
            "#[noalloc]
             fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         #[noalloc]
         fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }
         fn main() -> i64 ! {alloc, panic} { apply(alloc_id, 1) }",
        "type mismatch",
    );
}

#[test]
fn callable_values_are_heterogeneous_union_alternatives() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn answer() -> i64 ! {panic} { 42 }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
                let g: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = answer;
                let a = match f {
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                let b = match g {
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                a + b - 42
             }"
        ),
        42
    );
    // Union widening repacks a callable alternative into the larger union.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn answer() -> i64 ! {panic} { 42 }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
                let w: i64 | fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = f;
                match w {
                    i64 @ n if n > 0 => n,
                    i64 @ n => n,
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                }
             }"
        ),
        42
    );
    // A once closure is an owning active payload. Calling it consumes the
    // environment exactly once.
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(20);
                let c: i64 | once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                match c {
                    i64 @ v => v,
                    once fn(i64) -> i64 ! {panic} @ f => f(21),
                }
             }"
        ),
        42
    );
    // Dropping a union whose active alternative is an uncalled once closure
    // still releases its captured environment.
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let c: i64 | once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
                42
             }"
        ),
        42
    );
    // The same active-alternative cleanup happens on an early return.
    assert_eq!(
        value(
            "fn f(flag: Bool) -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let c: i64 | once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
                if flag { return 42; } else { 0 }
             }
             fn main() -> i64 ! {alloc, panic} { f(true) }"
        ),
        42
    );
    // A pure callable injected into a once alternative is wrapped by a
    // no-allocation null-environment thunk, never reinterpreted as a once ABI.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} {
                let u: i64 | once fn(i64) -> i64 ! {panic} = inc;
                match u {
                    i64 @ n => n,
                    once fn(i64) -> i64 ! {panic} @ f => f(41),
                }
             }"
        ),
        42
    );
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
            let f: i64 | fn(i64) -> i64 ! {panic} = inc;
            let w: i64 | once fn(i64) -> i64 ! {panic} = f;
            42
         }",
        "would change its representation",
    );
    // A callable alternative whose representation would change is not narrowed
    // by a type pattern without an adapter.
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
            let f: fn(i64) -> i64 ! {panic} | once fn(i64) -> i64 ! {panic} = inc;
            match f { fn(i64) -> i64 ! {panic} @ h => h(1) }
         }",
        "type patterns narrow a heterogeneous union",
    );
}

#[test]
fn canonical_callable_equivalences_keep_a_deterministic_representative() {
    // Unannotated and `@[many]` parameter grades are mutually subtype arrows.
    // They must not absorb each other into `Never`.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} {
                let a: fn(i64) -> i64 ! {panic} | fn(i64 @[many]) -> i64 ! {panic} = inc;
                let b: (fn(i64) -> i64 ! {panic}) & (fn(i64 @[many]) -> i64 ! {panic}) = inc;
                a(40) + b(1)
             }"
        ),
        43
    );
    // Reversing the written order selects the same representative, so the
    // union is not heterogeneous.
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
            let a: fn(i64 @[many]) -> i64 ! {panic} | fn(i64) -> i64 ! {panic} = inc;
            match a {
                fn(i64 @[many]) -> i64 ! {panic} @ f => f(1),
                fn(i64) -> i64 ! {panic} @ f => f(1),
            }
         }",
        "type patterns narrow a heterogeneous union",
    );
    // The canonical representative prefers the more permissive unannotated
    // contract, so a `@[1]` argument is not forced into an exact `many` demand.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} {
                let a: fn(i64 @[many]) -> i64 ! {panic} | fn(i64) -> i64 ! {panic} = inc;
                let x: i64 @[1] = 41;
                a(x)
             }"
        ),
        42
    );
}

#[test]
fn linear_once_closures_consume_captures_exactly_once_and_resist_laundering() {
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f: linear once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                f(21)
             }"
        ),
        42
    );
    // Passing it to a linear-once parameter is a checked consumption.
    assert_eq!(
        value(
            "fn consume(f: linear once fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }
             fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                consume(f, 21)
             }"
        ),
        42
    );
    // Returning a linear-once closure transfers the obligation to the caller.
    assert_eq!(
        value(
            "fn make(n: Box<i64> @[1]) -> linear once fn(i64) -> i64 ! {panic} ! {alloc, panic} {
                fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 }
             }
             fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f = make(n);
                f(21)
             }"
        ),
        42
    );
    // Constructing and destructuring a linear aggregate preserves the
    // obligation on its callable field.
    assert_eq!(
        value(
            "struct Holder { f: linear once fn(i64) -> i64 ! {panic} }
             fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let c = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                let h = Holder { f: c };
                let Holder { f } = h;
                f(21)
             }"
        ),
        42
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            42
         }",
        "linear value is not consumed",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            drop(f);
            42
         }",
        "linear values cannot be dropped",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            let g: once fn(i64) -> i64 ! {panic} = f;
            42
         }",
        "type mismatch",
    );
    rejects(
        "fn id<T>(x: T) -> T ! {panic} { x }
         fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            let g = id(f);
            42
         }",
        "linear value is not consumed",
    );
    rejects(
        "fn ignore<T>(x: T) -> i64 ! {panic} { 42 }
         fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            ignore(f)
         }",
        "linear value is not consumed",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
            f(1);
            f(2)
         }",
        "use after move",
    );
    rejects(
        "fn f(flag: Bool) -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(20);
            let l: linear once fn(i64) -> i64 ! {panic} =
                fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
            if flag { return 42; } else { l(21) }
         }
         fn main() -> i64 ! {alloc, panic} { f(false) }",
        "linear value is not consumed before this return",
    );
    // A linear-once closure can be adapted without changing the calling
    // convention; the adapter remains linear.
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f: linear once fn(i64 | Bool) -> i64 ! {panic} =
                    fn(x: i64 | Bool) -> i64 ! {panic} {
                        Box.take(n) + match x { i64 @ v => v + 1, Bool @ _ => 0 }
                    };
                let g: linear once fn(i64) -> i64 ! {panic} = f;
                g(21)
             }"
        ),
        42
    );
    // Effect polymorphism and linear-once parameters compose.
    assert_eq!(
        value(
            "fn run<e: Effects>(f: linear once fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                f(x)
             }
             fn main() -> i64 ! {alloc, panic} {
                let n: Box<i64> @[1] = Box.new(20);
                let f = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
                run(f, 21)
             }"
        ),
        42
    );
}

#[test]
fn effectful_function_example_matches_its_documented_output() {
    let source = include_str!("../../../examples/effectful-functions.kush");
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_io_and_stats(&mut std::io::empty(), &mut output)
        .unwrap();
    assert_eq!(result, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    assert_eq!(
        String::from_utf8(output).unwrap(),
        "42\n42\n42\n42\n42\n42\n42\n42\n42\n"
    );
}
