use kush::executable::check;
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}
fn evaluate(source: &str) -> (i64, String) {
    let checked = check(source).unwrap();
    let mut output = Vec::new();
    let value = checked.evaluate(&mut output).unwrap();
    (value, String::from_utf8(output).unwrap())
}
#[test]
fn first_working_program_evaluates() {
    assert_eq!(
        evaluate(include_str!("../../../examples/first.kush")),
        (0, "42\n720\n42\n".into())
    );
}
#[test]
fn scalar_types_are_not_coerced_and_function_signatures_are_checked() {
    for source in [
        "fn main() -> i64 ! {} { true }",
        "fn main() -> i64 ! {} {}",
        "fn main() -> Unit ! {} { 1 }",
        "fn main() -> i64 ! {panic} { 1 + true }",
        "fn main() -> i64 ! {} { if 1 { 2 } else { 3 } }",
        "fn main() -> i64 ! {} { if true { 1 } else { false } }",
        "fn f(x: Bool) -> Bool ! {} { x } fn main() -> Unit ! {} { f(1); }",
        "fn main() -> Unit ! {} { let x: Bool = 1; }",
    ] {
        rejects(source, "type mismatch");
    }
    rejects(
        "fn main() -> Unit ! {} { let x = 1; x = 2; }",
        "immutable binding",
    );
    rejects("fn main() -> Unit ! {} { 1 = 2; }", "mutable local");
    rejects(
        "fn f(x: i64) -> i64 ! {} { x } fn main() -> i64 ! {} { f() }",
        "argument count",
    );
    rejects("fn main() -> i64 ! {} { 9223372036854775808 }", "i64 range");
    rejects(
        "fn main() -> i64 ! {} { -9223372036854775809 }",
        "i64 range",
    );
}
#[test]
fn arithmetic_io_and_callee_effects_are_enforced() {
    rejects(
        "fn main() -> i64 ! {} { 1 + 2 }",
        "requires effects {panic}",
    );
    rejects(
        "fn main() -> Unit ! {} { print_i64(1); }",
        "requires effects {io, panic}",
    );
    rejects(
        "fn f() -> i64 ! {panic} { 1 } fn main() -> i64 ! {} { f() }",
        "requires effects {panic}",
    );
    rejects(
        "fn main() -> Unit ! {io} { print_i64(1); }",
        "requires effects {panic}",
    );
    rejects(
        "fn main() -> i64 ! {} { -(-1) }",
        "requires effects {panic}",
    );
    rejects(
        "fn main() -> Unit ! {state} {}",
        "only io, alloc, suspend, and panic",
    );
    rejects("fn main() -> Unit ! {panic, panic} {}", "duplicate effect");
}
#[test]
fn lexical_scopes_forward_calls_mutation_and_early_returns() {
    let source = "module demo;
        fn main() -> i64 ! {panic} {
            let mut x = later(2); { let x = 99; x; } if x == 4 { x = 6; }
            if x == 6 { return demo.later(x); }; -1
        }
        fn later(x: i64) -> i64 ! {panic} { x * 2 }
    ";
    assert_eq!(evaluate(source).0, 12);
    rejects(
        "fn main() -> i64 ! {} { { let hidden = 1; }; hidden }",
        "unknown name",
    );
    rejects(
        "fn main() -> i64 ! {} { return 1; 2 }",
        "unreachable expression",
    );
    rejects("fn main() -> i64 ! {} { return true; }", "type mismatch");
    rejects("fn main() -> i64 ! {} { return; }", "type mismatch");
}
#[test]
fn bool_and_integer_matches_require_exhaustiveness() {
    assert_eq!(
        evaluate("fn main() -> i64 ! {} { match true { false => 1, true => 2 } }").0,
        2
    );
    assert_eq!(
        evaluate("fn main() -> i64 ! {} { match 3 { 0 | 1 => 0, n if n > 1 => n, _ => -1 } }").0,
        3
    );
    rejects(
        "fn main() -> i64 ! {} { match 2 { 2 => 0 } }",
        "non-exhaustive",
    );
    rejects(
        "fn main() -> i64 ! {} { match true { true if true => 0, false => 1 } }",
        "non-exhaustive",
    );
    rejects(
        "fn main() -> i64 ! {} { match 1 { _ => 0, 1 => 1 } }",
        "unreachable match arm",
    );
    rejects(
        "fn main() -> i64 ! {} { match 1 { 1 => 0, 1 => 1, _ => 2 } }",
        "unreachable match",
    );
    rejects(
        "fn main() -> i64 ! {} { match true { 1 => 1, _ => 2 } }",
        "type mismatch",
    );
}
#[test]
fn left_to_right_evaluation_and_short_circuiting() {
    let source = "fn pair(x: i64, y: i64) -> i64 ! {panic} { x * 10 + y }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            let value = pair({ n = 1; n }, { n = 2; n });
            false && panic(); true || panic();
            value
        }";
    assert_eq!(evaluate(source).0, 12);
}
#[test]
fn every_checked_integer_failure_fails_in_the_reference_evaluator() {
    for expr in [
        "9223372036854775807 + 1",
        "-9223372036854775808 - 1",
        "9223372036854775807 * 2",
        "1 / 0",
        "1 % 0",
        "-9223372036854775808 / -1",
        "-9223372036854775808 % -1",
        "-(-9223372036854775808)",
    ] {
        let program = check(&format!("fn main() -> i64 ! {{panic}} {{ {expr} }}")).unwrap();
        assert!(
            program
                .evaluate(&mut Vec::new())
                .unwrap_err()
                .message
                .contains("panic:")
        );
    }
}
#[test]
fn unsupported_runtime_features_cannot_enter_the_checked_ir() {
    // A total `main` is erased: it checks logically but provides no runtime entry.
    let logical_main = check("total fn main() -> Nat ! {} { 0 }").unwrap();
    assert_eq!(logical_main.function_count(), 0);
    assert!(
        logical_main
            .evaluate(&mut Vec::new())
            .unwrap_err()
            .message
            .contains("needs fn main")
    );
    rejects(
        "fn main<T: Type>() -> Unit ! {} {}",
        "main must not be generic",
    );
    rejects("fn main() -> Nat ! {} { 0 }", "logical Nat");
    rejects("#[unknown] fn main() -> Unit ! {} {}", "contracts");
    // A scalar alias used only logically is a checked machine-carrier alias.
    let scalar_alias = check("type A = i64; fn main() -> Unit ! {} {}").unwrap();
    assert!(
        scalar_alias
            .logical_definitions()
            .iter()
            .any(|name| name == "A")
    );
    rejects(
        "type A = Char; fn main() -> Unit ! {} {}",
        "not supported by the logical subset",
    );
    rejects("fn main() -> Unit ! {};", "require a body");
    rejects(
        "fn main() -> Unit ! {} { let x = (1,); }",
        "one-element tuples are not supported",
    );
    rejects(
        "fn main() -> Unit ! {} { let x = [1]; }",
        "requires effects {alloc, panic}",
    );
    rejects("fn main() -> Bool ! {} { true }", "main must");
    rejects("fn main(n: i64) -> i64 ! {} { n }", "main must");
    rejects(
        "fn main() -> Unit ! {} { let print_i64 = 1; print_i64(0); }",
        "not an executable function",
    );
}
#[test]
fn entry_requirements_and_reference_recursion_limits_are_explicit() {
    let lib = check("fn library() -> i64 ! {} { 1 }").unwrap();
    assert!(
        lib.evaluate(&mut Vec::new())
            .unwrap_err()
            .message
            .contains("needs fn main")
    );
    let looped =
        check("fn forever() -> i64 ! {} { forever() } fn main() -> i64 ! {} { forever() }")
            .unwrap();
    assert!(
        looped
            .evaluate(&mut Vec::new())
            .unwrap_err()
            .message
            .contains("budget")
    );
}
