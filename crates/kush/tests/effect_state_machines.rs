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
