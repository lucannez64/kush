//! Explicit linear result contracts: `-> Box<i64> @[1]`.
//!
//! These tests exercise the restricted, sound subset: a static `@[1]` result
//! contract on an owning or intrinsically linear result. The grade is
//! compile-time metadata only; payload representations and the runtime ABI are
//! unchanged. Inference, custom grade semirings, grade-zero erasure, and
//! cancellation-time linear cleanup remain out of scope.
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

fn check_ok(source: &str) {
    if let Err(error) = check(source) {
        panic!("expected acceptance, got {error:?}: {source}");
    }
}

#[test]
fn factories_and_annotated_identity_transfer_exactly_once() {
    // A factory constructs the resource and hands the obligation to its caller.
    value(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
         fn main() -> i64 ! {alloc, panic} { let b = make(); Box.take(b) }",
        42,
    );
    // An annotated identity moves the parameter obligation into the result.
    value(
        "fn identity(b: Box<i64> @[1]) -> Box<i64> @[1] ! {} { b }
         fn main() -> i64 ! {alloc, panic} {
            let b = Box.new(21);
            let c = identity(b);
            Box.take(c)
         }",
        21,
    );
    // The same transfer through an alias result and a generic identity.
    value(
        "type Handle<T> = Box<T> @[1];
         fn identity<T>(b: Box<T> @[1]) -> Handle<T> ! {} { b }
         fn main() -> i64 ! {alloc, panic} {
            let b = Box.new(7);
            let c = identity(b);
            Box.take(c)
         }",
        7,
    );
    // Box.take is a legitimate consumer of the owned box and returns its
    // affine payload; it does not create a new obligation for a scalar.
    value(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(9) }
         fn main() -> i64 ! {alloc, panic} { Box.take(make()) }",
        9,
    );
}

#[test]
fn unsupported_result_grades_are_rejected_explicitly() {
    for grade in ["0", "2", "many"] {
        rejects(
            &format!(
                "fn f() -> Box<i64> @[{grade}] ! {{alloc, panic}} {{ Box.new(1) }} fn main() -> i64 ! {{}} {{ 0 }}"
            ),
            "result",
        );
    }
    // A copyable result now transfers a must-use @[1] obligation. Returning it
    // through an ungraded result is still rejected because the caller would
    // lose the obligation.
    rejects(
        "fn f() -> i64 @[1] ! {} { 1 } fn main() -> i64 ! {} { f() }",
        "must-use `@[1]` contract",
    );
    // A borrowed view is copyable and keeps its owning status unchanged; its
    // @[1] result is a must-use observation contract, not a move.
    check_ok("fn f<'a>(s: &'a [i64]) -> &'a [i64] @[1] ! {} { s } fn main() -> i64 ! {} { 0 }");
    // An abstract result grade is only meaningful with a concrete
    // specialization; @[1] is then accepted, @[2] is rejected.
    value(
        "fn f<G: Grade>(b: Box<i64> @[1]) -> Box<i64> @[G] ! {} { b }
         fn main() -> i64 ! {alloc, panic} { let b = Box.new(3); let c = f::<1>(b); Box.take(c) }",
        3,
    );
    rejects(
        "fn f<G: Grade>(b: Box<i64> @[1]) -> Box<i64> @[G] ! {} { b }
         fn main() -> i64 ! {alloc, panic} { let b = Box.new(3); f::<2>(b) }",
        "result",
    );
    rejects(
        "fn f<G: Grade>(b: Box<i64> @[1]) -> Box<i64> @[G] ! {} { b }
         fn main() -> i64 ! {alloc, panic} { let b = Box.new(3); f(b) }",
        "cannot infer usage grade",
    );
}

#[test]
fn an_ungraded_result_cannot_launder_a_linear_binding() {
    // The previously documented affine-return gap is now an explicit error:
    // the caller would otherwise receive an ordinary affine Box.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn leak() -> Box<i64> ! {alloc, panic} { let b = make(); b }
         fn main() -> i64 ! {alloc, panic} { Box.take(leak()) }",
        "ungraded result",
    );
    rejects(
        "fn identity(b: Box<i64> @[1]) -> Box<i64> ! {} { b }
         fn main() -> i64 ! {alloc, panic} { let b = Box.new(1); Box.take(identity(b)) }",
        "ungraded result",
    );
    // The graded replacement is the accepted form.
    value(
        "fn identity(b: Box<i64> @[1]) -> Box<i64> @[1] ! {} { b }
         fn main() -> i64 ! {alloc, panic} { let b = Box.new(1); Box.take(identity(b)) }",
        1,
    );
    // Intrinsic linear data keeps its obligation in the type, so an ungraded
    // result is still sound.
    value(
        "#[linear] enum Ticket { Live }
         fn keep(t: Ticket) -> Ticket ! {} { t }
         fn consume(t: Ticket) -> i64 ! {} { match t { Ticket.Live => 5 } }
         fn main() -> i64 ! {} { consume(keep(Ticket.Live)) }",
        5,
    );
}

#[test]
fn callers_must_consume_a_graded_result_exactly_once() {
    let prefix = "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) } ";
    // Dropped at statement position / scope end / wildcard / explicit drop.
    rejects(
        &format!("{prefix} fn main() -> i64 ! {{alloc, panic}} {{ make(); 0 }}"),
        "linear value is discarded",
    );
    rejects(
        &format!("{prefix} fn main() -> i64 ! {{alloc, panic}} {{ let b = make(); 0 }}"),
        "not consumed",
    );
    rejects(
        &format!("{prefix} fn main() -> i64 ! {{alloc, panic}} {{ let _ = make(); 0 }}"),
        "ignores a linear value",
    );
    rejects(
        &format!("{prefix} fn main() -> i64 ! {{alloc, panic}} {{ drop(make()); 0 }}"),
        "cannot be dropped",
    );
    // An ungraded parameter could drop the transferred resource.
    rejects(
        &format!(
            "{prefix} fn sink(b: Box<i64>) -> i64 ! {{}} {{ Box.take(b) }}
             fn main() -> i64 ! {{alloc, panic}} {{ sink(make()) }}"
        ),
        "ungraded parameter",
    );
    // A graded @[1] parameter is a legitimate consumer.
    value(
        &format!(
            "{prefix} fn sink(b: Box<i64> @[1]) -> i64 ! {{}} {{ Box.take(b) }}
             fn main() -> i64 ! {{alloc, panic}} {{ sink(make()) }}"
        ),
        1,
    );
    // A vector push would store the resource in an affine container.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let values: Vec<Box<i64>> = Vec.new();
            let values = Vec.push(values, make());
            0
         }",
        "linear",
    );
}

#[test]
fn callable_arrows_keep_result_contracts_through_calls_and_lambdas() {
    // A named function used as a graded arrow value and called indirectly.
    value(
        "fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
         fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            let b = f(24);
            Box.take(b)
         }
         fn main() -> i64 ! {alloc, panic} { apply(make) }",
        24,
    );
    // A typed lambda with a graded result, called through its arrow.
    value(
        "fn apply(f: fn() -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
            let b = f();
            Box.take(b)
         }
         fn main() -> i64 ! {alloc, panic} {
            let make: fn() -> Box<i64> @[1] ! {alloc, panic} =
                fn() -> Box<i64> @[1] ! {alloc, panic} { Box.new(20) };
            apply(make)
         }",
        20,
    );
    // Dropping or widening the result obligation in an arrow is rejected.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let widened: fn() -> Box<i64> ! {alloc, panic} = make;
            0
         }",
        "type mismatch",
    );
    rejects(
        "fn make() -> Box<i64> ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let narrowed: fn() -> Box<i64> @[1] ! {alloc, panic} = make;
            0
         }",
        "type mismatch",
    );
    // A union alternative must carry the same result contract; an ungraded
    // alternative cannot be injected where a graded one is expected.
    rejects(
        "fn other() -> Box<i64> ! {alloc, panic} { Box.new(2) }
         fn main() -> i64 ! {alloc, panic} {
            let f: (fn() -> Box<i64> @[1] ! {alloc, panic}) | i64 = other;
            0
         }",
        "type mismatch",
    );
}

#[test]
fn traits_methods_and_generic_methods_thread_the_result_contract() {
    // An owning method returns a resource obligation.
    value(
        "struct Factory { n: i64 }
         impl Factory {
            fn create(self: Self) -> Box<i64> @[1] ! {alloc, panic} { Box.new(self.n) }
         }
         fn main() -> i64 ! {alloc, panic} {
            let factory = Factory { n: 42 };
            let b = factory.create();
            Box.take(b)
         }",
        42,
    );
    // A static trait contract compares the graded result exactly.
    value(
        "trait Make { fn create(self: Self) -> Box<i64> @[1] ! {alloc, panic}; }
         struct Factory { n: i64 }
         impl Make for Factory {
            fn create(self: Self) -> Box<i64> @[1] ! {alloc, panic} { Box.new(self.n) }
         }
         fn run<T: Make>(value: T) -> i64 ! {alloc, panic} { Box.take(value.create()) }
         fn main() -> i64 ! {alloc, panic} { run(Factory { n: 6 }) }",
        6,
    );
    // A generic method preserves the contract at each specialization.
    value(
        "struct Factory { n: i64 }
         impl Factory {
            fn create<T>(self: Self, witness: T) -> Box<i64> @[1] ! {alloc, panic} {
                Box.new(self.n)
            }
         }
         fn main() -> i64 ! {alloc, panic} {
            let factory = Factory { n: 4 };
            let b = factory.create::<i64>(0);
            Box.take(b)
         }",
        4,
    );
    // A trait and impl that disagree about the result contract are rejected.
    rejects(
        "trait Make { fn create(self: Self) -> Box<i64> @[1] ! {alloc, panic}; }
         struct Factory { n: i64 }
         impl Make for Factory {
            fn create(self: Self) -> Box<i64> ! {alloc, panic} { Box.new(self.n) }
         }
         fn main() -> i64 ! {alloc, panic} { 0 }",
        "does not match the trait signature exactly",
    );
}

#[test]
fn closures_capture_and_consume_returned_resources() {
    // A closure capturing a graded result becomes linear-once and must be
    // called exactly once.
    value(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(41) }
         fn main() -> i64 ! {alloc, panic} {
            let b = make();
            let f: linear once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} { Box.take(b) };
            f() + 1
         }",
        42,
    );
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let b = make();
            let f = fn() -> i64 ! {panic} { Box.take(b) };
            0
         }",
        "linear value is not consumed",
    );
    // A lambda body that returns the captured graded obligation must declare
    // the graded result instead of widening it to an affine arrow.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let b = make();
            let f = fn() -> Box<i64> ! {alloc, panic} { b };
            0
         }",
        "ungraded result",
    );
    value(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} {
            let b = make();
            let f = fn() -> Box<i64> @[1] ! {alloc, panic} { b };
            Box.take(f())
         }",
        1,
    );
}

#[test]
fn loops_assign_and_break_graded_resources() {
    // Consume the current resource and install a fresh one before the
    // back-edge, restoring the loop-head obligation.
    value(
        "fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
         fn main() -> i64 ! {alloc, panic} {
            let mut i = 0;
            let mut b: Box<i64> @[1] = Box.new(-1);
            while i < 3 {
                let old = b;
                Box.take(old);
                b = make(i);
                i = i + 1;
            }
            Box.take(b)
         }",
        2,
    );
    // A loop break result transfers the obligation to the loop expression.
    value(
        "fn main() -> i64 ! {alloc, panic} {
            let b = loop { let inner: Box<i64> @[1] = Box.new(11); break inner; };
            Box.take(b)
         }",
        11,
    );
    // A back-edge that installs an obligation into an outer affine binding
    // would let the next iteration discard it.
    rejects(
        "fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
         fn main() -> i64 ! {alloc, panic} {
            let mut b = Box.new(0);
            let mut i = 0;
            while i < 3 {
                b = make(i);
                i = i + 1;
            }
            Box.take(b)
         }",
        "loop back-edge",
    );
}

#[test]
fn question_mark_and_aggregates_preserve_transfer_obligations() {
    const RESULT: &str = "enum Result<T, E> { Ok(T), Err(E) } ";
    // `?` on a graded Result consumes it and transfers the obligation to the
    // owning success payload.
    value(
        &format!(
            "{RESULT}
             fn produce(c: Bool) -> Result<Box<i64>, i64> @[1] ! {{alloc, panic}} {{
                if c {{ Ok(Box.new(13)) }} else {{ Err(0) }}
             }}
             fn consume(c: Bool) -> Result<i64, i64> ! {{alloc, panic}} {{
                let b = produce(c)?;
                Ok(Box.take(b))
             }}
             fn main() -> i64 ! {{alloc, panic}} {{
                match consume(true) {{ Ok(n) => n, Err(e) => e }}
             }}"
        ),
        13,
    );
    // A copyable success payload is observed by `?` itself: the graded Result
    // value is consumed exactly once, and the extracted scalar is an ordinary
    // copyable value with no residual obligation.
    value(
        &format!(
            "{RESULT}
             fn produce() -> Result<i64, Box<i64>> @[1] ! {{alloc, panic}} {{ Ok(1) }}
             fn consume() -> Result<i64, Box<i64>> ! {{alloc, panic}} {{
                let n = produce()?;
                Ok(n + 1)
             }}
             fn main() -> i64 ! {{alloc, panic}} {{
                match consume() {{ Ok(n) => n, Err(b) => Box.take(b) }}
             }}"
        ),
        2,
    );
    // An owning aggregate can carry the contract, and destructuring transfers
    // the obligation to its owning fields.
    value(
        "struct Pair { a: Box<i64>, b: Box<i64> }
         fn make() -> Pair @[1] ! {alloc, panic} { Pair { a: Box.new(1), b: Box.new(2) } }
         fn main() -> i64 ! {alloc, panic} {
            let Pair { a, b } = make();
            Box.take(a) + Box.take(b)
         }",
        3,
    );
    // Hiding a graded result inside an aggregate returned through an ungraded
    // result is rejected.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         struct Pair { a: Box<i64>, b: Box<i64> }
         fn leak() -> Pair ! {alloc, panic} { Pair { a: make(), b: Box.new(2) } }
         fn main() -> i64 ! {alloc, panic} { 0 }",
        "ungraded result",
    );
    // A wildcard/omitted field may not drop the transferred obligation.
    rejects(
        "struct Pair { a: Box<i64>, b: Box<i64> }
         fn make() -> Pair @[1] ! {alloc, panic} { Pair { a: Box.new(1), b: Box.new(2) } }
         fn main() -> i64 ! {alloc, panic} {
            let Pair { a, .. } = make();
            Box.take(a)
         }",
        "ignores a linear value",
    );
}

#[test]
fn pending_graded_results_cannot_be_abandoned_by_early_exits() {
    // An already-evaluated graded result in an earlier constructor field is
    // still pending when a later field returns.
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         struct Pair { a: Box<i64>, b: i64 }
         fn f() -> i64 ! {alloc, panic} {
            let pair = Pair { a: make(), b: { return 0; } };
         }
         fn main() -> i64 ! {alloc, panic} { f() }",
        "pending linear value",
    );
}

#[test]
fn linear_task_results_are_transferred_or_rejected_when_unjoined() {
    value(
        "use std.task.TaskExit;
         fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let task: Task<Box<i64>> = Task.spawn(make);
                match Task.join(task) {
                    TaskExit.Completed(b) => Box.take(b),
                    TaskExit.Cancelled => 0,
                }
            })
         }",
        1,
    );
    rejects(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(1) }
         fn main() -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let task: Task<Box<i64>> =
                    Task.spawn(fn() -> Box<i64> @[1] ! {alloc, panic, suspend} { make() });
            })
         }",
        "linear",
    );
}

#[test]
fn callable_arrow_aliases_and_checked_reuse_preserve_the_contract() {
    // A transparent alias may name a graded arrow type.
    value(
        "type Factory = fn(i64) -> Box<i64> @[1] ! {alloc, panic};
         fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
         fn apply(f: Factory, n: i64) -> i64 ! {alloc, panic} { Box.take(f(n)) }
         fn main() -> i64 ! {alloc, panic} { apply(make, 5) }",
        5,
    );
    // Checked in-place reuse consumes the owning box and returns a fresh one
    // with the same obligation.
    value(
        "fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
         fn bump(b: Box<i64> @[1]) -> Box<i64> @[1] ! {panic} {
            let current = Box.read(&b);
            Box.reuse(b, current + 1)
         }
         fn main() -> i64 ! {alloc, panic} {
            let b = make(41);
            let c = bump(b);
            Box.take(c)
         }",
        42,
    );
    rejects(
        "fn bump(b: Box<i64> @[1]) -> Box<i64> ! {panic} {
            let current = Box.read(&b);
            Box.reuse(b, current + 1)
         }
         fn main() -> i64 ! {alloc, panic} { 0 }",
        "ungraded result",
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_execution_agree_on_graded_results() {
    use std::process::Command;

    let source = "enum Result<T, E> { Ok(T), Err(E) }
        fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
        fn identity(b: Box<i64> @[1]) -> Box<i64> @[1] ! {} { b }
        struct Factory { n: i64 }
        impl Factory {
            fn create(self: Self) -> Box<i64> @[1] ! {alloc, panic} { Box.new(self.n) }
        }
        fn produce(c: Bool) -> Result<Box<i64>, i64> @[1] ! {alloc, panic} {
            if c { Ok(make(1)) } else { Err(0) }
        }
        fn unwrap(c: Bool) -> Result<i64, i64> ! {alloc, panic} {
            let b = produce(c)?;
            Ok(Box.take(b))
        }
        fn main() -> i64 ! {alloc, panic} {
            let first = identity(make(20));
            let factory = Factory { n: 21 };
            let second = factory.create();
            let third = loop { break make(0); };
            let captured = make(0);
            let closure: linear once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} { Box.take(captured) };
            let fourth = closure();
            let fifth = match unwrap(true) { Ok(n) => n, Err(e) => e };
            Box.take(first) + Box.take(second) + Box.take(third) + fourth + fifth
        }";
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations);

    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("linear-resources");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(binary).output().unwrap();
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stderr.is_empty());
}

#[test]
fn hidden_returns_in_conditions_scrutinees_and_guards_keep_result_obligations() {
    for body in [
        "if { if flag { return make(); } false } { Box.new(1) } else { Box.new(2) }",
        "while { if flag { return make(); } false } {} Box.new(2)",
        "match { if flag { return make(); } false } { true => Box.new(1), false => Box.new(2) }",
        "match false { _ if { if flag { return make(); } true } => Box.new(1), _ => Box.new(2) }",
    ] {
        let source = format!(
            "fn make() -> Box<i64> @[1] ! {{alloc,panic}} {{ Box.new(7) }}
            fn hidden(flag: Bool) -> Box<i64> ! {{alloc,panic}} {{ {body} }}
            fn main() -> i64 ! {{alloc,panic}} {{ Box.take(hidden(true)) }}"
        );
        rejects(&source, "ungraded result");
        // The same control flow is valid when the transfer is declared.
        let graded = source.replace(
            "hidden(flag: Bool) -> Box<i64>",
            "hidden(flag: Bool) -> Box<i64> @[1]",
        );
        value(&graded, 7);
    }
}

#[test]
fn return_nested_inside_try_operand_cannot_hide_a_linear_result() {
    let source = "use std.result.Result;
        fn make() -> Box<i64> @[1] ! {alloc,panic} { Box.new(7) }
        fn hidden(flag: Bool) -> Result<Box<i64>,i64> ! {alloc,panic} {
            let n: i64 = { if flag { return Ok(make()); } Ok::<i64, i64>(0) }?;
            Ok(Box.new(n))
        }
        fn main() -> i64 ! {alloc,panic} {
            match hidden(true) { Ok(b) => Box.take(b), Err(code) => code }
        }";
    rejects(source, "ungraded result");
    let graded = source.replace(
        "hidden(flag: Bool) -> Result<Box<i64>,i64>",
        "hidden(flag: Bool) -> Result<Box<i64>,i64> @[1]",
    );
    value(&graded, 7);
}

#[test]
fn a_later_affine_assignment_cannot_erase_an_earlier_linear_return() {
    let source = "fn hidden(b: Box<i64> @[1], flag: Bool) -> Box<i64> ! {alloc,panic} {
            let mut current = b;
            if flag { return current; }
            Box.take(current);
            current = Box.new(0);
            current
        }
        fn main() -> i64 ! {alloc,panic} { Box.take(hidden(Box.new(7), true)) }";
    rejects(source, "ungraded result");
    let graded = source.replace(
        "hidden(b: Box<i64> @[1], flag: Bool) -> Box<i64>",
        "hidden(b: Box<i64> @[1], flag: Bool) -> Box<i64> @[1]",
    );
    value(&graded, 7);
}
