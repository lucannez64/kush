//! Handled bodies as resumable state machines (docs/effect-state-machines.md).
//!
//! Every feature has positive, rejection, cleanup (balanced allocations), and
//! reference-evaluator/native parity tests.

use kush::executable::{MemoryStats, check};

fn evaluate(source: &str) -> (i64, MemoryStats, String) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
    (result, stats, String::from_utf8(output).unwrap())
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

/// The reference evaluator and the native backend agree on the result and
/// on standard output, and the evaluator's allocations are balanced.
fn agrees(source: &str, expected: i64, stdout: &str) {
    let (reference, _, output) = evaluate(source);
    assert_eq!(reference, expected, "{source}");
    assert_eq!(output, stdout, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        use std::process::Command;
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("effect-state-machines");
        kush::native::build(&program, &binary).unwrap();
        let native = Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
    }
}

/// A non-tail handler: it runs code after `resume`, so it observes the
/// continuation and the body becomes a state machine.
const DOUBLING: &str = r#"handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x * 10); r + 1 }"#;

fn with_handler(before: &str, body: &str) -> String {
    format!("fn main() -> i64 ! {{alloc, panic}} {{ {before} {DOUBLING} {{ {body} }} }}")
}

// ---------------------------------------------------------------------------
// Loops, branches and several performs (E-MULTI-PERFORM)
// ---------------------------------------------------------------------------

#[test]
fn the_design_worked_example_resumes_inside_a_loop() {
    // Three performs inside a loop: each handler activation adds one after
    // the rest of the body returns, so the result is 0 + 10 + 20 + 3.
    let source = with_handler(
        "",
        "let mut sum = 0;
         let mut i = 0;
         while i < 3 {
             let a = perform Ask(i);
             sum = sum + a;
             i = i + 1;
         }
         sum",
    );
    agrees(&source, 33, "");
}

#[test]
fn performs_in_both_arms_of_a_branch_and_in_nested_loops() {
    let branches = with_handler(
        "",
        "let c = 2;
         let a = if c > 1 { perform Ask(1) } else { perform Ask(2) };
         let b = if c > 5 { perform Ask(3) + 1 } else { 0 };
         a + b",
    );
    // a = 10, b = 0; one activation.
    agrees(&branches, 11, "");
    let nested = with_handler(
        "",
        "let mut sum = 0;
         let mut i = 0;
         while i < 2 {
             let mut j = 0;
             loop {
                 if j == 2 { break; }
                 sum = sum + perform Ask(i + j);
                 j = j + 1;
             }
             i = i + 1;
         }
         sum",
    );
    // asks 0,1,1,2 -> 40, four activations.
    agrees(&nested, 44, "");
    let matched = format!(
        "enum Pick {{ A(i64), B }} {}",
        with_handler(
            "",
            "let p: Pick = Pick.A(4);
             let r = match p {
                 Pick.A(n) => { let a = perform Ask(n); a + n },
                 Pick.B => 0,
             };
             r",
        )
    );
    agrees(&matched, 45, "");
}

#[test]
fn owned_values_cross_performs_and_are_dropped_once() {
    // A box is live across two performs: it travels through two resumption
    // environments and is freed exactly once at the end of the body.
    let source = with_handler(
        "",
        "let b = Box.new(5);
         let x = perform Ask(1);
         let y = perform Ask(2);
         Box.take(b) + x + y",
    );
    let (result, stats, _) = evaluate(&source);
    assert_eq!(result, 37);
    // One box, two capturing resumption environments.
    assert_eq!(stats.allocations, 3);
    agrees(&source, 37, "");
    // A box that is dead after the first perform stays with the suspended
    // code and is dropped when the handled body is left.
    let dead = with_handler(
        "",
        "let b = Box.new(5);
         let n = Box.take(b);
         let v = Box.new(7);
         let x = perform Ask(n);
         x",
    );
    agrees(&dead, 51, "");
    // A box created inside the loop body is dropped at each iteration end,
    // including the iterations resumed from a perform.
    let looped = with_handler(
        "",
        "let mut i = 0;
         let mut s = 0;
         while i < 3 {
             let b = Box.new(i);
             let a = perform Ask(1);
             s = s + a + Box.take(b);
             i = i + 1;
         }
         s",
    );
    agrees(&looped, 36, "");
}

#[test]
fn outer_locals_are_copied_or_moved_into_the_resumption() {
    // A copyable outer local is read after the perform; the outer function
    // keeps its own copy.
    let copied = r#"
        fn main() -> i64 ! {alloc, panic} {
            let base = 100;
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                let a = perform Ask(1);
                a + base
            };
            r + base
        }"#;
    agrees(copied, 202, "");
    // An owned outer local used only inside the body moves into it.
    let moved = r#"
        fn main() -> i64 ! {alloc, panic} {
            let b = Box.new(9);
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                let a = perform Ask(1);
                a + Box.take(b)
            }
        }"#;
    agrees(moved, 11, "");
    // Using it after the handle would observe a moved value.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let v: Vec<i64> = [1, 2];
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                let a = perform Ask(1);
                a + Vec.len(&v)
            };
            r + Vec.len(&v)
        }"#,
        "is used after the 'handle'",
    );
    // Writing an outer local after a perform would update only the copy.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 1;
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                let a = perform Ask(1);
                n = a;
                a
            };
            r + n
        }"#,
        "cannot write a local of the enclosing function",
    );
    // Writing it before the first perform runs in place and is visible.
    let before = r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 1;
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                n = 5;
                let a = perform Ask(n);
                a
            };
            r + n
        }"#;
    agrees(before, 11, "");
}

#[test]
fn borrows_and_handler_written_locals_cannot_cross_a_perform() {
    rejects(
        &with_handler(
            "",
            "let v = [1, 2, 3];
             let s = &v[0..2];
             let a = perform Ask(1);
             a + Slice.len(s)",
        ),
        "cannot stay live across a non-tail 'perform'",
    );
    // A loan that ends before the perform is fine.
    let ended = with_handler(
        "",
        "let v = [1, 2, 3];
         let n = Slice.len(&v[0..2]);
         let a = perform Ask(1);
         a + n",
    );
    agrees(&ended, 13, "");
}

// ---------------------------------------------------------------------------
// Performs inside expressions (E-EXPR)
// ---------------------------------------------------------------------------

/// A handler that prints the payload before resuming and after the rest of
/// the body returns, so output shows where each suspension happens.
const TRACING: &str = r#"handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} { print_i64(100 + x); let r = resume(x * 10); print_i64(200 + x); r }"#;

fn traced(helpers: &str, body: &str) -> String {
    format!(
        "fn note(n: i64) -> i64 ! {{io, panic}} {{ print_i64(n); n }}
         fn add(a: i64, b: i64, c: i64) -> i64 ! {{panic}} {{ a + b + c }}
         {helpers}
         fn main() -> i64 ! {{io, alloc, panic}} {{ {TRACING} {{ {body} }} }}"
    )
}

#[test]
fn operands_left_of_a_perform_are_evaluated_before_it() {
    // Binary operands, call arguments and constructor fields keep their
    // left-to-right order: 1 is printed before the perform, 3 after.
    let binary = traced("", "note(1) + perform Ask(2) + note(3)");
    agrees(&binary, 24, "1\n102\n3\n202\n");
    let call = traced("", "add(note(1), perform Ask(2), note(3))");
    agrees(&call, 24, "1\n102\n3\n202\n");
    let nested = traced("", "add(note(1), perform Ask(perform Ask(2) + 1), note(3))");
    // Inner perform: payload 2 resumes with 20; outer payload 21 resumes 210.
    agrees(&nested, 214, "1\n102\n121\n3\n221\n202\n");
    let record = traced(
        "struct Pair { a: i64, b: i64 }",
        "let p = Pair { a: note(1), b: perform Ask(2) }; p.a + p.b",
    );
    agrees(&record, 21, "1\n102\n202\n");
}

#[test]
fn conditions_and_short_circuits_suspend_only_when_evaluated() {
    let condition = traced("", "if perform Ask(1) > 5 { note(7) } else { 0 }");
    agrees(&condition, 7, "101\n7\n201\n");
    // `false && perform` never performs; `true || perform` neither.
    let skipped = traced(
        "",
        "let a = 1 > 2 && perform Ask(1) > 0;
         let b = 1 < 2 || perform Ask(2) > 0;
         if a { 0 } else if b { 5 } else { 1 }",
    );
    agrees(&skipped, 5, "");
    let taken = traced(
        "",
        "let a = 1 < 2 && perform Ask(1) > 0;
         if a { 5 } else { 1 }",
    );
    agrees(&taken, 5, "101\n201\n");
    // A while condition suspends once per test, including the failing one.
    let looped = traced(
        "",
        "let mut i = 0;
         while perform Ask(i) < 20 { i = i + 1; }
         i",
    );
    agrees(&looped, 2, "100\n101\n102\n202\n201\n200\n");
    let scrutinee = traced("", "match perform Ask(1) { 10 => note(4), _ => 0 }");
    agrees(&scrutinee, 4, "101\n4\n201\n");
}

#[test]
fn unsupported_perform_positions_are_rejected() {
    rejects(
        &traced("", "match 1 { n if perform Ask(n) > 0 => 1, _ => 0 }"),
        "cannot appear in a match guard",
    );
}

// ---------------------------------------------------------------------------
// Control flow across suspension points (E-CONTROL)
// ---------------------------------------------------------------------------

#[test]
fn break_and_continue_after_a_perform_are_state_transitions() {
    let source = with_handler(
        "",
        "let mut i = 0;
         let mut sum = 0;
         loop {
             i = i + 1;
             let a = perform Ask(i);
             if a == 20 { continue; }
             if a > 30 { break; }
             sum = sum + a;
         }
         sum",
    );
    // asks 1..=4: adds 10 and 30; continue skips 20; breaks at 40.
    agrees(&source, 44, "");
    // A loop with a value: break carries it out of the rebuilt loop.
    let valued = with_handler(
        "",
        "let mut i = 0;
         let found = loop {
             i = i + 1;
             let a = perform Ask(i);
             if a > 15 { break a; }
         };
         found",
    );
    agrees(&valued, 22, "");
}

#[test]
fn early_exits_drop_every_live_owned_value_once() {
    // Boxes live across the perform are dropped by break, continue and the
    // normal iteration end, in the resumed iterations as well.
    let source = with_handler(
        "",
        "let mut i = 0;
         let mut sum = 0;
         let keep = Box.new(1000);
         while i < 5 {
             i = i + 1;
             let b = Box.new(i);
             let a = perform Ask(i);
             if a == 20 { continue; }
             if a == 40 { break; }
             sum = sum + Box.take(b);
         }
         sum + Box.take(keep)",
    );
    // takes 1 and 3; four handler activations.
    let (result, stats, _) = evaluate(&source);
    assert_eq!(result, 1008);
    assert_eq!(stats.allocations, stats.deallocations);
    agrees(&source, 1008, "");
}

#[test]
fn capture_free_continuations_allocate_nothing() {
    // Nothing is live after the perform except its own result, so the
    // resumption is a plain code pointer, as before the state machines.
    let source = with_handler("", "let a = perform Ask(4); a + 1");
    let (result, stats, _) = evaluate(&source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 0);
    agrees(&source, 42, "");
    // And the tail-resumptive identity path allocates nothing in a loop.
    let tail = r#"
        fn main() -> i64 ! {panic} {
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x + 1) } {
                let mut i = 0;
                let mut sum = 0;
                while i < 10 { sum = sum + perform Ask(i); i = i + 1; }
                sum
            }
        }"#;
    let (result, stats, _) = evaluate(tail);
    assert_eq!(result, 55);
    assert_eq!(stats.allocations, 0);
    agrees(tail, 55, "");
}

#[test]
fn handler_written_locals_cannot_cross_a_perform() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut seen = 0;
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { seen = x; let r = resume(x); r } {
                let a = perform Ask(1);
                a + seen
            }
        }"#,
        "the handler writes through its capture",
    );
}

#[test]
fn references_cannot_cross_a_perform_but_pinned_values_can() {
    rejects(
        &format!(
            "struct P {{ x: i64, y: i64 }} {}",
            with_handler(
                "",
                "let mut p = P { x: 1, y: 2 };
                 let r = &mut p;
                 let a = perform Ask(1);
                 r.x = a;
                 p.x",
            )
        ),
        "cannot stay live across a non-tail 'perform'",
    );
    // The record's address is taken, but every reference ends before the
    // perform, so the resumption holds the record by value.
    let pinned = format!(
        "struct P {{ x: i64, y: i64 }} {}",
        with_handler(
            "",
            "let mut p = P { x: 1, y: 2 };
             let r = &mut p;
             r.x = 5;
             let a = perform Ask(1);
             p.x + p.y + a",
        )
    );
    agrees(&pinned, 18, "");
}

#[test]
fn linear_values_and_declared_operations_cross_non_tail_performs() {
    // The linear token moves into the resumption environment and is consumed
    // exactly once by the continuation.
    let linear = format!(
        "#[linear] struct Token {{ id: i64 }} {}",
        with_handler(
            "let token = Token { id: 5 };",
            "let a = perform Ask(1);
             let b = perform Ask(2);
             let Token { id } = token;
             a + b + id",
        )
    );
    agrees(&linear, 37, "");
    // A declared operation also pushes a dynamic frame around the body; the
    // suspension and resumption happen inside it.
    let declared = r#"
        effect Ask: i64 -> i64;
        fn main() -> i64 ! {alloc, panic} {
            let mut i = 0;
            let mut sum = 0;
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let r = resume(x | 16); r ^ 1 } {
                while i < 3 {
                    sum = sum + perform Ask(i);
                    i = i + 1;
                }
                sum
            }
        }"#;
    // 16 + 17 + 18 = 51; three activations each flip the low bit: 50.
    agrees(declared, 50, "");
}

// ---------------------------------------------------------------------------
// Resumption across calls (E-CALLEE-COLOR, E-DYN-RESUME)
// ---------------------------------------------------------------------------

/// A non-tail handler for a declared operation (declared handlers are pure,
/// hence bitwise arithmetic): a perform yields `x ^ 1`, and every handler
/// activation flips bit 12 of the final result after the rest of the body
/// returns. `{helpers}` holds the called functions.
fn declared(helpers: &str, row: &str, body: &str) -> String {
    format!(
        "effect Op: i64 -> i64;
         {helpers}
         fn main() -> i64 ! {{{row}}} {{
             handle Op: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {{}},
             ) -> i64 ! {{}} {{ let r = resume(x ^ 1); r ^ 4096 }} {{ {body} }}
         }}"
    )
}

#[test]
fn a_called_function_perform_resumes_the_rest_of_the_body() {
    // resume(21) returns from call() with 21, the body triples it, and the
    // handler flips bit 12 of the body's result: (21 * 3) ^ 4096. With the
    // old identity resumption the flip would have happened before the
    // multiplication: (21 ^ 4096) * 3 = 12351.
    let source = declared(
        "fn call() -> i64 ! {Op, panic} { perform Op(20) }",
        "panic",
        "call() * 3",
    );
    let (result, stats, _) = evaluate(&source);
    assert_eq!(result, 4159);
    assert_eq!(stats.allocations, 0);
    agrees(&source, 4159, "");
    // Two levels of calls: (21 + 1) * 3, flipped once. `call` has work left
    // after `deep` returns, so its continuation is an environment.
    let deep = declared(
        "fn deep() -> i64 ! {Op, panic} { perform Op(20) }
         fn call() -> i64 ! {Op, panic} { deep() + 1 }",
        "alloc, panic",
        "call() * 3",
    );
    agrees(&deep, 4162, "");
    // A called function that performs twice captures its live values; the
    // handled body continues afterwards. a = 5, b = 4, (504 * 3) flipped
    // twice.
    let work = declared(
        "fn twice(n: i64) -> i64 ! {Op, panic} {
             let a = perform Op(n);
             let b = perform Op(a);
             a * 100 + b
         }",
        "alloc, panic",
        "let v = twice(4); v * 3",
    );
    agrees(&work, 1512, "");
}

#[test]
fn called_functions_resume_inside_loops_with_owned_values() {
    let source = declared(
        "fn sum(n: i64) -> i64 ! {Op, alloc, panic} {
             let mut i = 0;
             let mut s = 0;
             let keep = Box.new(7);
             while i < n {
                 let b = Box.new(i);
                 s = s + perform Op(Box.take(b));
                 i = i + 1;
             }
             s + Box.take(keep)
         }",
        "alloc, panic",
        "let a = sum(3); let b = sum(1); a + b",
    );
    // sum(3) = 1 + 0 + 3 + 7 = 11, sum(1) = 1 + 7 = 8; four flips cancel.
    let (result, stats, _) = evaluate(&source);
    assert_eq!(result, 19);
    assert_eq!(stats.allocations, stats.deallocations);
    agrees(&source, 19, "");
}

#[test]
fn return_and_try_in_a_called_function_continue_the_caller() {
    let early = declared(
        "fn pick(n: i64) -> i64 ! {Op, panic} {
             let a = perform Op(n);
             if a > 5 { return a * 10; }
             a
         }",
        "alloc, panic",
        "pick(1) + pick(9)",
    );
    // pick(1) = 0, pick(9) = 80; two flips cancel.
    agrees(&early, 80, "");
    let tried = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        effect Op: i64 -> i64;
        fn check(n: i64) -> Result<i64, i64> ! {Op, panic} {
            let a = perform Op(n);
            if a > 5 { Result.Err(a) } else { Result.Ok(a) }
        }
        fn both(n: i64) -> Result<i64, i64> ! {Op, alloc, panic} {
            let a = check(n)?;
            let b = check(a)?;
            Result.Ok(a + b)
        }
        fn main() -> i64 ! {alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let r = resume(x ^ 1); r ^ 4096 } {
                let first = match both(1) { Result.Ok(v) => v, Result.Err(e) => 0 - e };
                let second = match both(7) { Result.Ok(v) => v, Result.Err(e) => 0 - e };
                first * 100 + second
            }
        }"#;
    // both(1): a = 0, b = 1, Ok(1). both(7): check(7) yields 6 -> Err(6).
    // 100 - 6 = 94, flipped by an odd number (three) of activations.
    agrees(tried, 4190, "");
}

#[test]
fn recursive_called_functions_resume_at_every_level() {
    let source = declared(
        "fn countdown(n: i64) -> i64 ! {Op, alloc, panic} {
             if n == 0 { return 0; }
             let a = perform Op(n);
             a + countdown(n - 1)
         }",
        "alloc, panic",
        "countdown(3)",
    );
    // 2 + 3 + 0 = 5, flipped three times.
    agrees(&source, 4101, "");
}

#[test]
fn tail_resumptive_handlers_keep_the_direct_entry() {
    // The same called function under a tail-resumptive handler runs through
    // its ordinary entry and allocates nothing.
    let source = r#"
        effect Op: i64 -> i64;
        fn sum(n: i64) -> i64 ! {Op, panic} {
            let mut i = 0;
            let mut s = 0;
            while i < n { s = s + perform Op(i); i = i + 1; }
            s
        }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x ^ 1) } {
                sum(4) + 1
            }
        }"#;
    // 1 + 0 + 3 + 2 + 1.
    let (result, stats, _) = evaluate(source);
    assert_eq!(result, 7);
    assert_eq!(stats.allocations, 0);
    agrees(source, 7, "");
}

#[test]
fn unresumable_calls_are_rejected() {
    rejects(
        &declared(
            "fn call() -> i64 ! {Op, panic} { perform Op(20) }
             fn apply(f: fn() -> i64 ! {Op, panic}) -> i64 ! {Op, panic} { f() }",
            "panic",
            "apply(call) + 1",
        ),
        "cannot be resumed",
    );
    rejects(
        &declared(
            "fn call() -> i64 ! {Op, panic} { perform Op(20) }",
            "panic",
            "let f: fn() -> i64 ! {Op, panic} = call; f() + 1",
        ),
        "calling a function value that may perform 'Op'",
    );
    // A borrow held across a perform inside a called function.
    rejects(
        &declared(
            "fn view(v: Vec<i64>) -> i64 ! {Op, alloc, panic} {
                 let s = &v[0..1];
                 let a = perform Op(1);
                 a + Slice.len(s)
             }",
            "alloc, panic",
            "view([1, 2])",
        ),
        "cannot stay live across a non-tail 'perform'",
    );
    // Under real resumption the handler returns the body's result, so a
    // body that calls such functions must have the operation result type.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn call() -> i64 ! {Op, panic} { perform Op(20) }
        fn main() -> i64 ! {panic} {
            let positive = handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let r = resume(x ^ 1); r ^ 4096 } { call() > 0 };
            if positive { 1 } else { 0 }
        }"#,
        "must produce the operation result type",
    );
}

// ---------------------------------------------------------------------------
// Multishot by copying the live values (E-MULTISHOT-COPY, E-MULTISHOT-DECL)
// ---------------------------------------------------------------------------

#[test]
fn multishot_resumptions_each_get_a_copy_of_the_live_values() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let n = 100;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} {
                let a = resume(1);
                let b = resume(2);
                a * 1000 + b
            } {
                let base = n + 5;
                let v = perform Op(0);
                v + base
            }
        }"#;
    let (result, stats, _) = evaluate(source);
    assert_eq!(result, 106107);
    // Copyable values travel as arguments: nothing is allocated.
    assert_eq!(stats.allocations, 0);
    agrees(source, 106107, "");
    // Every combination of choices through a loop with mutable state:
    // s = c0 + 2 * c1 summed over the four combinations.
    let choices = r#"
        fn main() -> i64 ! {panic} {
            handle Choose: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let a = resume(0); let b = resume(1); a + b } {
                let mut s = 0;
                let mut i = 0;
                while i < 2 {
                    let c = perform Choose(i);
                    s = s + c * (i + 1);
                    i = i + 1;
                }
                s
            }
        }"#;
    agrees(choices, 6, "");
}

#[test]
fn multishot_rejects_owned_values_and_escaping_tokens() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let a = resume(1); let b = resume(2); a + b } {
                let b = Box.new(5);
                let v = perform Op(0);
                v + Box.take(b)
            }
        }"#,
        "owned, linear, or graded and cannot be copied",
    );
    rejects(
        r#"
        fn apply(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }
        fn main() -> i64 ! {panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let a = apply(resume, 1); a } {
                let v = perform Op(0);
                v + n
            }
        }"#,
        "only calls its resumption directly",
    );
}

#[test]
fn declared_operations_accept_multishot_handlers() {
    // Pure handler: bitwise arithmetic only. Each perform yields 0 then 1;
    // the handler ORs the two runs, so the result has both bits.
    let source = r#"
        effect Choose: i64 -> i64;
        fn main() -> i64 ! {panic} {
            handle Choose: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let a = resume(0); let b = resume(1); a | b } {
                let shift = 4;
                let c = perform Choose(1);
                let d = perform Choose(2);
                (c << shift) | d
            }
        }"#;
    agrees(source, 17, "");
    rejects(
        r#"
        effect Choose: i64 -> i64;
        fn pick() -> i64 ! {Choose, panic} { perform Choose(1) }
        fn main() -> i64 ! {panic} {
            handle Choose: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(0) } { pick() }
        }"#,
        "multishot resumption of 'Choose' through a called function is not supported",
    );
}

// ---------------------------------------------------------------------------
// Performance shape (E-PERF)
// ---------------------------------------------------------------------------

/// A million tail-resumptive performs, lexical and through a called
/// function, run natively under a 256 KiB stack: they continue in place, so
/// the stack does not grow with the number of performs.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn a_million_tail_resumptive_performs_run_in_constant_stack() {
    use std::process::Command;
    let lexical = r#"
        fn main() -> i64 ! {panic} {
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x + 1) } {
                let mut i = 0;
                let mut s = 0;
                while i < 1000000 { s = (s + perform Ask(i)) & 1023; i = i + 1; }
                s & 255
            }
        }"#;
    let dynamic = r#"
        effect Ask: i64 -> i64;
        fn step(x: i64) -> i64 ! {Ask, panic} { perform Ask(x) }
        fn main() -> i64 ! {panic} {
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x ^ 1) } {
                let mut i = 0;
                let mut s = 0;
                while i < 1000000 { s = (s + step(i)) & 1023; i = i + 1; }
                s & 255
            }
        }"#;
    // Expected values: the low byte of the masked running sums.
    let expected = |shift: fn(i64) -> i64| {
        let mut s = 0i64;
        for i in 0..1_000_000i64 {
            s = (s + shift(i)) & 1023;
        }
        s & 255
    };
    for (source, value) in [
        (lexical, expected(|i| i + 1)),
        (dynamic, expected(|i| i ^ 1)),
    ] {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("million-performs");
        kush::native::build(&program, &binary).unwrap();
        let output = Command::new("sh")
            .arg("-c")
            .arg(format!("ulimit -s 256; exec {}", binary.display()))
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(value as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn tail_and_non_tail_loops_agree_in_both_backends() {
    // The same loop through the identity path and the state machine. The
    // reference evaluator bounds nesting depth, and every pending non-tail
    // handler activation nests, so the loop is short.
    let body = "let mut i = 0;
                let mut s = 0;
                while i < 8 { s = (s + perform Ask(i)) & 1023; i = i + 1; }
                s";
    let tail = format!(
        "fn main() -> i64 ! {{alloc, panic}} {{ handle Ask: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{panic}} {{ resume(x + 1) }} {{ {body} }} }}"
    );
    let non_tail = format!(
        "fn main() -> i64 ! {{alloc, panic}} {{ handle Ask: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{panic}} {{ let r = resume(x + 1); r }} {{ {body} }} }}"
    );
    let mut s = 0i64;
    for i in 0..8 {
        s = (s + i + 1) & 1023;
    }
    agrees(&tail, s, "");
    agrees(&non_tail, s, "");
}

// ---------------------------------------------------------------------------
// Independent review regressions (E-REVIEW)
// ---------------------------------------------------------------------------

#[test]
fn review_a_resumable_call_cannot_borrow_a_value_its_continuation_captures() {
    // The callee would write the original vector while the continuation
    // holds a moved copy (native use after free before the fix).
    rejects(
        &declared(
            "fn grow(v: &mut Vec<i64>) -> i64 ! {Op, alloc, panic} {
                 Vec.push(v, 9); Vec.push(v, 10);
                 perform Op(1)
             }",
            "alloc, panic",
            "let mut v: Vec<i64> = [1];
             let a = grow(&mut v);
             Vec.len(&v) * 100 + a",
        ),
        "can suspend while it borrows a value that is still used after it",
    );
    rejects(
        &declared(
            "fn bump(p: &mut i64) -> i64 ! {Op, panic} { *p = 5; perform Op(1) }",
            "alloc, panic",
            "let mut n = 1; let a = bump(&mut n); n * 100 + a",
        ),
        "can suspend while it borrows a value that is still used after it",
    );
    // Borrowing a value that is dead after the call is fine.
    let dead = declared(
        "fn bump(p: &mut i64) -> i64 ! {Op, panic} { *p = 5; perform Op(1) }",
        "alloc, panic",
        "let mut n = 1; let a = bump(&mut n); a * 3",
    );
    agrees(&dead, 4096, "");
    // Under a tail-resumptive handler nothing suspends, so the borrow is
    // ordinary.
    let tail = r#"
        effect Op: i64 -> i64;
        fn grow(v: &mut Vec<i64>) -> i64 ! {Op, alloc, panic} {
            Vec.push(v, 9); Vec.push(v, 10);
            perform Op(1)
        }
        fn main() -> i64 ! {alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x ^ 2) } {
                let mut v: Vec<i64> = [1];
                let a = grow(&mut v);
                Vec.len(&v) * 100 + a
            }
        }"#;
    agrees(tail, 303, "");
}

#[test]
fn review_closures_capturing_by_reference_cannot_cross_or_write_through_a_perform() {
    rejects(
        &with_handler(
            "",
            "let mut m = 1;
             let f = fn() -> Unit ! {panic} { m = m + 100; };
             let a = perform Ask(1);
             f();
             a + m",
        ),
        "cannot stay live across a non-tail 'perform'",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 1;
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x); r + 1 } {
                let a = perform Ask(1);
                let f = fn() -> Unit ! {panic} { n = n + 100; };
                f();
                a
            };
            r * 1000 + n
        }"#,
        "cannot write a local of the enclosing function",
    );
}

#[test]
fn review_task_scopes_that_may_perform_are_rejected_without_other_points() {
    rejects(
        &declared(
            "fn call() -> i64 ! {Op, panic} { perform Op(20) }",
            "alloc, panic, suspend",
            "let mut out = 0;
             Task.scope(fn() -> Unit ! {Op, alloc, panic, suspend} { out = call(); });
             out * 3",
        ),
        "cannot be resumed",
    );
}

#[test]
fn review_performs_on_the_left_of_short_circuits_and_in_borrowed_temporaries() {
    let left = with_handler(
        "",
        "let i = 1; if perform Ask(i) < 40 && i < 10 { 1 } else { 2 }",
    );
    agrees(&left, 2, "");
    let looped = with_handler(
        "",
        "let mut i = 0;
         while perform Ask(i) < 40 && i < 10 { i = i + 1; }
         i",
    );
    // Five performs (0, 10, 20, 30, 40), each adding one on the way out.
    agrees(&looped, 9, "");
    let temporary = declared(
        "fn mk(n: i64) -> Vec<i64> ! {Op, alloc, panic} { let a = perform Op(n); [a, a] }",
        "alloc, panic",
        "let n = Vec.len(&mk(2)); n * 3",
    );
    agrees(&temporary, 4102, "");
}

#[test]
fn review_resumption_tokens_cannot_escape_the_handle() {
    // Returning the token inside the result would let the rest of the body
    // run after the handle, outside its effect row and dynamic handlers.
    rejects(
        r#"
        enum G { Done(i64), More(i64, fn(G) -> G ! {}) }
        fn make() -> G ! {io, panic} {
            handle Yield: i64 -> G with fn(
                x: i64,
                resume: fn(G) -> G ! {},
            ) -> G ! {} { G.More(x, resume) } {
                let r = perform Yield(1);
                print_i64(555);
                r
            }
        }
        fn main() -> i64 ! {io, panic} { match make() { G.Done(n) => n, G.More(x, k) => x } }"#,
        "could return its resumption token",
    );
    rejects(
        r#"
        enum G { Done(i64), More(i64, linear once fn(G) -> G ! {}) }
        fn make() -> G ! {io, alloc, panic} {
            let n = 4;
            handle Yield: i64 -> G with fn(
                x: i64,
                resume: linear once fn(G) -> G ! {},
            ) -> G ! {} { G.More(x, resume) } {
                let r = perform Yield(1);
                print_i64(n);
                r
            }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            match make() { G.Done(n) => n, G.More(x, k) => match k(G.Done(1)) { G.Done(n) => n, G.More(y, k2) => y } }
        }"#,
        // A one-shot token makes the result type linear, which a non-tail
        // resumption already refuses.
        "linear operation result",
    );
}

#[test]
fn review_continuations_cannot_write_locals_the_handler_reads() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 1;
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { let r = resume(x * 10); r + n } {
                let a = perform Ask(1);
                n = 50;
                a
            }
        }"#,
        "cannot write a local of the enclosing function",
    );
}

#[test]
fn review_jumps_in_while_conditions_keep_their_target_or_are_rejected() {
    rejects(
        &with_handler(
            "",
            "let mut s = 0;
             let mut i = 0;
             loop {
                 i = i + 1;
                 let mut j = 0;
                 while { if j == 2 { break; } j < 5 } { let a = perform Ask(j); s = s + a; j = j + 1; }
                 if i > 3 { break; }
             }
             s",
        ),
        "inside the condition of a while loop",
    );
    rejects(
        &with_handler(
            "",
            "let mut j = 0;
             loop {
                 while { if j == 2 { break; } perform Ask(j) < 5 } { j = j + 1; }
                 break;
             }
             j",
        ),
        "inside a while condition",
    );
    // Leaving the handled body from a while condition after a perform is a
    // jump out of the continuation (an internal error before the fix).
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut out = 0;
            loop {
                let r = handle Ask: i64 -> i64 with fn(
                    x: i64,
                    resume: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {panic} { let r = resume(x * 10); r + 1 } {
                    let a = perform Ask(1);
                    let mut j = 0;
                    while { if a > 5 { break; } j < 3 } { j = j + 1; }
                    a + j
                };
                out = r;
                break;
            }
            out
        }"#,
        "cannot 'break' or 'continue' to a loop outside the handled body",
    );
}

#[test]
fn review_borrows_that_end_inside_the_payload_are_accepted() {
    let source = with_handler(
        "",
        "let v: Vec<i64> = [1, 2, 3];
         let b = perform Ask(Vec.len(&v));
         b + Vec.len(&v)",
    );
    agrees(&source, 34, "");
}

#[test]
fn review_tokens_cannot_escape_through_containers_or_tasks() {
    rejects(
        r#"
        enum G { Done(i64), More(i64, ArenaBox<fn(G) -> G ! {}>) }
        fn make() -> G ! {io, alloc, panic} {
            handle Yield: i64 -> G with fn(
                x: i64,
                resume: fn(G) -> G ! {},
            ) -> G ! {alloc, panic} {
                let a = Arena.new();
                G.More(x, Arena.alloc(&a, resume))
            } {
                let r = perform Yield(1);
                print_i64(555);
                G.Done(1)
            }
        }
        fn main() -> i64 ! {io, alloc, panic} { match make() { G.Done(n) => n, G.More(x, b) => x } }"#,
        "could return its resumption token",
    );
    rejects(
        r#"
        use std.task.TaskExit;
        effect D: i64 -> i64;
        fn d() -> i64 ! {D, panic} { perform D(1) }
        fn main() -> i64 ! {io, alloc, panic, suspend} {
            let base = 40;
            handle D: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x | base) } {
                handle Ask: i64 -> i64 with fn(
                    x: i64,
                    resume: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {alloc, panic, suspend} {
                    Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                        let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} { resume(x) });
                        match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
                    })
                } {
                    let a = perform Ask(1);
                    a + d()
                }
            }
        }"#,
        "cannot be moved into a spawned task",
    );
}

#[test]
fn review_handlers_that_return_early_are_not_tail_resumptive() {
    // The handler stops the body without resuming when x > 5.
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} { if x > 5 { return 7; } resume(x) } {
                let a = perform Ask(9);
                a + 100
            }
        }"#;
    agrees(source, 7, "");
}

#[test]
fn review_resumed_code_does_not_see_frames_the_handler_pushed() {
    // The outer handler re-handles D around resume. Deep semantics: the
    // resumed continuation (including called functions) is handled by the
    // outer handler again, exactly as when the performs are written
    // lexically.
    let called = r#"
        effect D: i64 -> i64;
        fn d(n: i64) -> i64 ! {D, panic} { let a = perform D(n); a ^ 1 }
        fn main() -> i64 ! {alloc, panic} {
            handle D: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} {
                handle D: i64 -> i64 with fn(
                    y: i64,
                    r2: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {} { let z = r2(y ^ 4); z ^ 16 } {
                    resume(x ^ 8)
                }
            } {
                let a = d(32);
                let b = d(64);
                a ^ b ^ 0
            }
        }"#;
    let lexical = r#"
        effect D: i64 -> i64;
        fn main() -> i64 ! {alloc, panic} {
            handle D: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} {
                handle D: i64 -> i64 with fn(
                    y: i64,
                    r2: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {} { let z = r2(y ^ 4); z ^ 16 } {
                    resume(x ^ 8)
                }
            } {
                let a = perform D(32) ^ 1;
                let b = perform D(64) ^ 1;
                a ^ b ^ 0
            }
        }"#;
    agrees(lexical, 96, "");
    agrees(called, 96, "");
}

#[test]
fn review_tasks_spawned_in_continuations_inherit_visible_frames() {
    // The redirect frame pushed for the resumed continuation is skipped, not
    // a barrier: the child still inherits the copyable F frame below it.
    let source = r#"
        use std.task.TaskExit;
        effect D: i64 -> i64;
        effect E: i64 -> i64;
        effect F: i64 -> i64;
        fn f(n: i64) -> i64 ! {F, panic} { perform F(n) }
        fn main() -> i64 ! {alloc, panic, suspend} {
            handle F: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y ^ 16) } {
                handle D: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {
                    handle E: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y) } { resume(x) }
                } {
                    let a = perform D(1);
                    let v = Task.scope(fn() -> i64 ! {alloc, panic, suspend, F} {
                        let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend, F} { f(2) });
                        match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
                    });
                    a ^ v
                }
            }
        }"#;
    agrees(source, 19, "");
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn review_redirect_frames_fit_deep_native_chains() {
    use std::process::Command;
    // A handler that wraps resume in another handle keeps one handler frame
    // and redirect frames per pending perform; forty pending performs used
    // to exceed the 64-frame native handler stack.
    let source = r#"
        effect D: i64 -> i64;
        effect E: i64 -> i64;
        fn d(n: i64) -> i64 ! {D, panic} { perform D(n) }
        fn main() -> i64 ! {alloc, panic} {
            handle D: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {
                handle E: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y) } { resume(x ^ 1) }
            } {
                let mut i = 0;
                let mut s = 0;
                while i < 40 { s = s ^ d(i); i = i + 1; }
                s
            }
        }"#;
    let expected = (0..40i64).fold(0, |s, i| s ^ (i ^ 1));
    let program = check(source).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("deep-redirects");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn review_lexical_handles_also_hide_handler_frames_from_resumed_code() {
    let source = r#"
        effect E: i64 -> i64;
        fn e(n: i64) -> i64 ! {E, panic} { perform E(n) }
        fn main() -> i64 ! {alloc, panic} {
            handle E: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y ^ 1) } {
                handle Ask: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {alloc, panic} {
                    handle E: i64 -> i64 with fn(y: i64, r: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { r(y ^ 64) } {
                        let v = resume(x);
                        v
                    }
                } {
                    let a = perform Ask(2);
                    let b = e(16);
                    a ^ b
                }
            }
        }"#;
    agrees(source, 19, "");
}

#[test]
fn review_more_escape_and_write_routes_are_rejected() {
    // A continuation writing an outer array through a mutable slice.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut arr: [i64; 3] = [1, 2, 3];
            let r = handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let y = resume(x); y } {
                let a = perform Ask(1);
                Slice.set(&mut arr[..], 0, 50);
                a
            };
            arr[0] + r
        }"#,
        "cannot write a local of the enclosing function",
    );
    // A token boxed before a spawned task captures it.
    rejects(
        r#"
        use std.task.TaskExit;
        fn main() -> i64 ! {alloc, panic, suspend} {
            handle Ask: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {alloc, panic, suspend} {
                let b = Box.new(resume);
                Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                    let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} { let r = Box.take(b); r(x) });
                    match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
                })
            } {
                let a = perform Ask(1);
                a + 1
            }
        }"#,
        "cannot be moved into a spawned task",
    );
    // A capturing handler cannot serve resumable performs in called functions.
    rejects(
        r#"
        effect D: i64 -> i64;
        fn d(n: i64) -> i64 ! {D, panic} { perform D(n) }
        fn main() -> i64 ! {alloc, panic} {
            let base = 2;
            handle D: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { let r = resume(x ^ base); r } {
                d(1) ^ d(4)
            }
        }"#,
        "cannot resume performs in called functions",
    );
}
