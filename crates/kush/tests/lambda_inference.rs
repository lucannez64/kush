//! I-LAMBDA-INFER: omitted lambda parameter, result and effect annotations
//! (docs/functions.md, "Lambda annotation inference").
//!
//! Every accepted program runs in the reference evaluator and the native
//! backend with balanced allocations; every rejection names the annotation
//! it needs.

use kush::executable::{MemoryStats, check};

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected: i64, stdout: &str) -> MemoryStats {
    let (result, output, stats) = run(source);
    assert_eq!(result, expected, "{source}");
    assert_eq!(output, stdout, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lambda-inference");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
    }
    stats
}

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

const APPLY: &str = "fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} { f(x) }";
const GENERIC: &str = "fn generic<T, e: Effects>(f: fn(T) -> T ! {e}, x: T) -> T ! {e} { f(x) }";

#[test]
fn an_expected_arrow_fills_every_omitted_annotation() {
    agrees(
        &format!("{APPLY} fn main() -> i64 ! {{panic}} {{ apply(fn(x) {{ x * 2 }}, 21) }}"),
        42,
        "",
    );
    agrees(
        "fn main() -> i64 ! {panic} {
             let f: fn(i64, Bool) -> i64 ! {panic} = fn(x, b) { if b { x + 1 } else { x } };
             f(41, true)
         }",
        42,
        "",
    );
    // Partial annotations combine with inference.
    agrees(
        "fn main() -> i64 ! {panic} {
             let a = fn(x: i64) { x + 1 };
             let b = fn(x) -> i64 { x * 2 };
             let c = fn(x) ! {panic} { x - 1 };
             a(1) + b(20) + c(1)
         }",
        42,
        "",
    );
}

#[test]
fn a_generic_call_infers_the_lambda_after_the_other_arguments() {
    // `T` comes from `21`, the row variable `e` from the lambda's body.
    agrees(
        &format!("{GENERIC} fn main() -> i64 ! {{panic}} {{ generic(fn(x) {{ x * 2 }}, 21) }}"),
        42,
        "",
    );
    agrees(
        &format!(
            "{GENERIC} fn main() -> i64 ! {{io, panic}} {{ generic(fn(x) {{ print_i64(x); x + 1 }}, 41) }}"
        ),
        42,
        "41\n",
    );
    agrees(
        "fn make<T>(f: fn() -> T ! {}) -> T ! {} { f() }
         fn main() -> i64 ! {} { make(fn() { 7 }) }",
        7,
        "",
    );
}

#[test]
fn the_first_use_of_a_let_binding_fixes_the_lambda() {
    agrees(
        &format!(
            "{GENERIC} fn main() -> i64 ! {{panic}} {{ let double = fn(x) {{ x * 2 }}; generic(double, 21) }}"
        ),
        42,
        "",
    );
    agrees(
        "fn main() -> i64 ! {panic} {
             let n = 40;
             let flag = true;
             let add = fn(x, y, b) { if b { x + y } else { 0 } };
             add(n, 2, flag)
         }",
        42,
        "",
    );
    agrees(
        "fn main() -> i64 ! {panic} {
             let f = fn(x) { x + 1 };
             let g: fn(i64) -> i64 ! {panic} = f;
             g(41)
         }",
        42,
        "",
    );
    agrees(
        &format!(
            "{APPLY} fn main() -> i64 ! {{panic}} {{ let inc = fn(x) {{ x + 1 }}; apply(inc, 41) }}"
        ),
        42,
        "",
    );
}

#[test]
fn inferred_rows_are_minimal_and_checked_against_the_context() {
    // A body without effects has the empty row, so it fits a pure arrow.
    agrees(
        "fn pure(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }
         fn main() -> i64 ! {} { pure(fn(x) { x }, 42) }",
        42,
        "",
    );
    rejects(
        &format!(
            "{APPLY} fn main() -> i64 ! {{io, panic}} {{ let f = fn(x: i64) {{ print_i64(x); x }}; apply(f, 1) }}"
        ),
        "found fn(i64) -> i64 ! {panic, io}",
    );
    // A handled body takes its row from the expected arrow.
    agrees(
        "fn run(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(20) }
         fn main() -> i64 ! {panic} {
             run(fn(x) {
                 handle Ask: i64 -> i64 with fn(
                     v: i64,
                     resume: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {panic} { resume(v + 1) } { perform Ask(x) * 2 }
             })
         }",
        42,
        "",
    );
}

#[test]
fn capturing_and_owning_lambdas_clean_up_exactly_once() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
             let k = Box.new(3);
             let f = fn(x) { Box.take(k) + x };
             f(39)
         }",
        42,
        "",
    );
    // The box and the closure environment.
    assert_eq!(stats.allocations, 2);
    // Dropped uncalled: the environment is still released.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
             let k = Box.new(3);
             let f = fn(x: i64) { Box.take(k) + x };
             7
         }",
        7,
        "",
    );
    assert_eq!(stats.allocations, 2);
    // An inferred owning result is moved out exactly once.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
             let make = fn(x) { Box.new(x) };
             let b = make(42);
             Box.take(b)
         }",
        42,
        "",
    );
    assert_eq!(stats.allocations, 1);
}

#[test]
fn missing_context_asks_for_the_annotation() {
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(x) { x + 1 }; 0 }",
        "cannot infer the type of lambda parameter 'x'",
    );
    // The first use's argument is declared after the lambda.
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(x) { x + 1 }; let k = 41; f(k) }",
        "cannot infer the type of lambda parameter 'x'",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(c: Bool) { if c { 1 } else { true } }; 0 }",
        "it would be a union",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(x: i64) { return x; }; f(1) }",
        "uses 'return'",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(x: i64) { loop {} }; 0 }",
        "never returns",
    );
    rejects(
        "fn main() -> i64 ! {panic} {
             let f = fn(x: i64) {
                 handle Ask: i64 -> i64 with fn(
                     v: i64,
                     resume: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {panic} { resume(v) } { perform Ask(x) }
             };
             f(1)
         }",
        "handles or performs",
    );
}

#[test]
fn inference_does_not_decide_borrows_grades_or_unions() {
    // Borrowed parameter types stay explicit.
    rejects(
        "fn sum(f: fn(&[i64]) -> i64 ! {panic}) -> i64 ! {panic} { let a = [1, 2]; f(&a[..]) }
         fn main() -> i64 ! {panic} { sum(fn(s) { 1 }) }",
        "borrowed, task and uninhabited parameter types are not inferred",
    );
    // Inferred parameters are ungraded, so a graded contract still needs
    // the annotation.
    rejects(
        "fn once(f: fn(i64 @[1]) -> i64 ! {panic}) -> i64 ! {panic} { f(1) }
         fn main() -> i64 ! {panic} { once(fn(x) { x }) }",
        "type mismatch",
    );
    agrees(
        "fn once(f: fn(i64 @[1]) -> i64 ! {panic}) -> i64 ! {panic} { f(42) }
         fn main() -> i64 ! {panic} { once(fn(x: i64 @[1]) { x }) }",
        42,
        "",
    );
    // A later use at another type is an ordinary mismatch.
    rejects(
        "fn main() -> i64 ! {panic} { let f = fn(x) { x + 1 }; f(1) + f(true) }",
        "expected i64, found Bool",
    );
}

#[test]
fn annotated_lambdas_are_unchanged() {
    agrees(
        "fn main() -> i64 ! {panic} {
             let f = fn(x: i64) -> i64 ! {panic} { x + 1 };
             f(41)
         }",
        42,
        "",
    );
    rejects(
        "fn main() -> i64 ! {} { let f = fn(x: i64) -> i64 ! {} { x + 1 }; f(1) }",
        "operation requires effects {panic}",
    );
}

#[test]
fn an_inferred_result_never_carries_a_runtime_length_array() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
             let n = 2;
             let a: [i64; n <= 4] = [1, 2];
             let f = fn() { a };
             0
         }",
        "runtime-length array",
    );
}
