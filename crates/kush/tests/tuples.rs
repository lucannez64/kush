//! Anonymous tuples: 2..16 inline elements, positional `.N` projection,
//! destructuring, generic inference, unions/callables, early exits, and
//! ownership boundaries. Every executable case also runs natively.
use kush::executable::check;

const PREFIX: &str = "use std.option.Option;\nuse std.result.Result;\n";

fn rejects(source: &str, fragment: &str) {
    let source = format!("{PREFIX}{source}");
    let error = check(&source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("tuples-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = format!("{PREFIX}{source}");
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    if let Some(output) = native(&source) {
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

#[test]
fn tuple_example_matches_documented_output() {
    let program = check(include_str!("../../../examples/tuples.kush")).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "3\n9\n21\n12\n");
}

#[test]
fn owning_nested_and_generic_tuples_agree_natively() {
    agrees(
        "fn swap<T, U>(p: (T, U)) -> (U, T) ! {} { (p.1, p.0) }
        fn first<T>(p: (T, i64)) -> T ! {} { p.0 }
        fn main() -> i64 ! {io, alloc, panic} {
            let pair = (1, 2);
            print_i64(pair.0);
            print_i64(pair.1);
            let nested = ((10, 20), 30);
            print_i64(nested.0.1);
            print_i64(nested.1);
            let swapped = swap(pair);
            print_i64(swapped.0);
            print_i64(swapped.1);
            let owned: (String, i64) = (\"hé\", 7);
            let (text, n) = owned;
            print_i64(String.len(&text));
            print_i64(String.scalar_len(&text));
            print_i64(n);
            first((9, 1))
        }",
        9,
        "1\n2\n20\n30\n2\n1\n3\n2\n7\n",
    );
}

#[test]
fn tuple_unions_and_callable_elements_keep_representation_coercions() {
    agrees(
        "fn classify(p: (i64 | Bool, i64)) -> i64 ! {panic} {
            match p.0 {
                i64 @ n => n + p.1,
                Bool @ b => if b { p.1 } else { -p.1 },
            }
        }
        fn make(flag: Bool) -> (i64 | Bool, i64) ! {} {
            if flag { (1, 2) } else { (true, 3) }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            print_i64(classify(make(true)));
            print_i64(classify(make(false)));
            let f = fn(x: i64) -> i64 ! {panic} { x + 10 };
            let callable: (fn(i64) -> i64 ! {panic}, i64) = (f, 32);
            print_i64(callable.0(callable.1));
            let adapted: (once fn(i64) -> i64 ! {alloc, panic}, i64) = (f, 32);
            let (once_f, n) = adapted;
            print_i64(once_f(n));
            print_i64(classify((5, 6)));
            0
        }",
        0,
        "3\n3\n42\n42\n11\n",
    );
}

#[test]
fn tuple_early_return_and_question_mark_stop_later_fields() {
    agrees(
        "fn early() -> (i64, i64) ! {panic} { (return (4, 5), panic()) }
        fn propagate(r: Result<i64, i64>) -> Result<(i64, i64), i64> ! {panic} {
            (r?, panic())
        }
        fn main() -> i64 ! {io, panic} {
            let direct = early();
            print_i64(direct.0);
            print_i64(direct.1);
            match propagate(Result.Err(7)) {
                Result.Ok(p) => print_i64(p.0),
                Result.Err(e) => print_i64(e),
            }
            0
        }",
        0,
        "4\n5\n7\n",
    );
}

#[test]
fn tuple_patterns_destructure_and_nested_projection() {
    agrees(
        "enum Shape { Pair(i64, i64), Empty }
        fn main() -> i64 ! {io, alloc, panic} {
            let nested = ((1, 2), (3, (4, 5)));
            let ((a, b), (c, (d, e))) = nested;
            print_i64(a + b + c + d + e);
            let p = (10, 20);
            let (x, y) = p;
            print_i64(x * y);
            let made = (Shape.Pair(6, 7), 8);
            match made.0 {
                Shape.Pair(m, n) => print_i64(m + n + made.1),
                Shape.Empty => print_i64(-1),
            }
            0
        }",
        0,
        "15\n200\n21\n",
    );
}

#[test]
fn tuple_arity_and_one_tuple_boundaries_are_explicit() {
    rejects(
        "fn f<T>(p: (T, T)) -> T ! {} { p.0 }
        fn main() -> i64 ! {} { f((1, 2, 3)) }",
        "tuple expression has 3 elements, but the expected tuple type has 2",
    );
    rejects(
        "fn f<T>(p: (T, T)) -> Bool ! {} { true }
        fn main() -> i64 ! {} { if f((1, 2, 3)) { 1 } else { 0 } }",
        "tuple type has 2 elements, but the value has 3",
    );
    rejects(
        "fn main() -> Unit ! {} { let p: (i64, i64, i64) = (1, 2); }",
        "tuple expression has 2 elements, but the expected tuple type has 3",
    );
    rejects(
        "fn main() -> Unit ! {} { let p = (1,); }",
        "one-element tuples are not supported",
    );
    rejects(
        "fn main() -> Unit ! {} { let p: (i64,) = (1, 2); }",
        "one-element tuples are not supported",
    );
    rejects(
        "fn main() -> Unit ! {} { let (x,) = (1, 2); }",
        "one-element tuple patterns are not supported",
    );
    let wide = (0..17).map(|_| "i64").collect::<Vec<_>>().join(", ");
    rejects(
        &format!("fn main() -> Unit ! {{}} {{ let p: ({wide}) = (0); }}"),
        "tuples have 2 to 16 elements",
    );
    rejects(
        "fn main() -> Unit ! {} { let p = (1, 2); let x = p.2; }",
        "tuple",
    );
}

#[test]
fn tuple_storage_of_borrows_and_tasks_stays_rejected() {
    rejects(
        "fn main() -> Unit ! {panic} { let values: [i64; 2] = [1, 2]; let v = &values[..]; let p = (v, 1); }",
        "tuples cannot store references, slice views, or borrowed records",
    );
    rejects(
        "fn use_task(p: (Task<i64>, i64)) -> Unit ! {} {} fn main() -> Unit ! {} {}",
        "task handles cannot be stored in tuples",
    );
}

#[test]
fn owning_tuples_move_destructure_and_cleanup_exactly_once() {
    let source = format!(
        "{PREFIX}fn main() -> Unit ! {{io, alloc, panic}} {{
            let p: (String, (String, i64)) = (\"left\", (\"right\", 3));
            let (left, nested) = p;
            let (right, n) = nested;
            print_i64(String.len(&left) + String.scalar_len(&right) + n);
        }}"
    );
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "12\n");
    assert_eq!(stats.allocations, stats.deallocations);
    if let Some(output) = native(&source) {
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap(), "12\n");
    }
}

#[test]
fn tuple_linear_and_owned_field_laundering_is_rejected() {
    rejects(
        "fn consume(t: Token) -> Unit ! {} {}
        #[linear] struct Token { value: i64 }
        fn main() -> Unit ! {} { let t = Token { value: 1 }; let p = (t, 2); }",
        "linear value is not consumed before the function returns",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let p = (\"owned\", 1); let s = p.0; }",
        "cannot move owned field '0'",
    );
    rejects(
        "#[linear] struct Token { value: i64 }
        fn main() -> Unit ! {} { let p = (Token { value: 1 }, 2); let (t, n) = p; drop(t); drop(n); }",
        "linear values cannot be dropped",
    );
}
