//! EFF-CAP-LEXICAL: second-class lexical effect capabilities
//! (docs/effect-capabilities.md section 3).
//!
//! `handle Op: P -> R as op with h { body }` binds a capability `op` to this
//! handle activation; `cap Op ! {e}` parameters receive it; `perform op(x)`
//! calls exactly that handler with no dynamic lookup. Every accepted program
//! runs in the reference evaluator and natively with balanced allocations.

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
        let binary = scratch.path().join("effect-capabilities");
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

/// A pure tail-resumptive handler for the declared `Ask` that adds 100.
const HANDLE: &str = "handle Ask: i64 -> i64 as ask with fn(
    x: i64,
    resume: linear once fn(i64) -> i64 ! {},
) -> i64 ! {panic} { resume(x + 100) }";

fn program(helpers: &str, row: &str, body: &str) -> String {
    format!(
        "effect Ask: i64 -> i64;
         {helpers}
         fn main() -> i64 ! {{{row}}} {{ {HANDLE} {{ {body} }} }}"
    )
}

#[test]
fn a_capability_reaches_its_handler_through_calls() {
    agrees(
        &program(
            "fn step(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { perform op(x) + 1 }
             fn twice(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { step(op, step(op, x)) }",
            "panic",
            "twice(ask, 1)",
        ),
        203,
        "",
    );
    // The capability in its own body behaves like the lexical perform.
    agrees(
        &program("", "panic", "perform ask(2) + perform Ask(3)"),
        205,
        "",
    );
}

#[test]
fn a_capability_perform_needs_no_operation_row_or_panic() {
    // `step` performs through the capability without `Ask` or `panic` for a
    // missing handler; the handler's own row `{}` is all it adds.
    agrees(
        "effect Ask: i64 -> i64;
         fn step(op: cap Ask ! {}, x: i64) -> i64 ! {} { perform op(x) }
         fn main() -> i64 ! {} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x | 64) } { step(ask, 2) }
         }",
        66,
        "",
    );
    // The handler's row is added to the performer's row.
    rejects(
        "effect Ask: i64 -> i64;
         fn step(op: cap Ask ! {io, panic}, x: i64) -> i64 ! {panic} { perform op(x) }
         fn main() -> i64 ! {panic} { 0 }",
        "operation requires effects {io}",
    );
}

#[test]
fn capabilities_name_one_activation_not_the_innermost_handler() {
    // An inner (pure, dynamic) handler for Ask does not intercept the
    // capability, while a dynamic perform by name sees the inner one.
    agrees(
        &program(
            "fn via_cap(op: cap Ask ! {panic}) -> i64 ! {panic} { perform op(1) }
             fn via_name() -> i64 ! {Ask, panic} { perform Ask(1) }",
            "panic",
            "handle Ask: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x | 4096) } { via_cap(ask) * 10000 + via_name() }",
        ),
        101 * 10000 + 4097,
        "",
    );
}

#[test]
fn only_pure_capability_handlers_are_dynamically_visible() {
    // A pure handler bound `as ask` is also the dynamic handler for Ask.
    agrees(
        "effect Ask: i64 -> i64;
         fn via_name() -> i64 ! {Ask, panic} { perform Ask(2) }
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x | 64) } { via_name() + perform ask(1) }
         }",
        66 + 65,
        "",
    );
    // A handler with effects is capability-only: it is not on the dynamic
    // stack and does not discharge `Ask`, so a called function's `Ask` must
    // appear in the enclosing row instead of aborting at run time.
    rejects(
        "effect Ask: i64 -> i64;
         fn via_name() -> i64 ! {Ask, panic} { perform Ask(2) }
         fn main() -> i64 ! {io, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {io, panic} { print_i64(x); resume(x) } { perform ask(1) + via_name() }
         }",
        "operation requires effects {Ask}",
    );
}

#[test]
fn capability_rows_are_subeffects() {
    agrees(
        "effect Ask: i64 -> i64;
         fn wide(op: cap Ask ! {io, panic}, x: i64) -> i64 ! {io, panic} { perform op(x) }
         fn main() -> i64 ! {io, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(x * 2) } { wide(ask, 21) }
         }",
        42,
        "",
    );
    rejects(
        "effect Ask: i64 -> i64;
         fn narrow(op: cap Ask ! {}, x: i64) -> i64 ! {} { perform op(x) }
         fn main() -> i64 ! {io, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {io, panic} { print_i64(x); resume(x) } { narrow(ask, 21) }
         }",
        "type mismatch",
    );
}

#[test]
fn capabilities_are_second_class() {
    for (helpers, body, fragment) in [
        ("", "let c = ask; 0", "second-class"),
        // Lambda captures: `a_lambda_capturing_a_capability_is_scoped`.
        (
            "fn leak(op: cap Ask ! {panic}) -> cap Ask ! {panic} ! {panic} { op }",
            "0",
            "capability",
        ),
        ("struct Holder { op: cap Ask ! {panic} }", "0", "capability"),
        (
            "fn call(op: cap Ask ! {panic}) -> i64 ! {panic} { op(1, 2) }",
            "0",
            "second-class",
        ),
        (
            "fn take(f: fn(i64) -> i64 ! {}) -> i64 ! {} { 0 }",
            "take(ask)",
            "second-class",
        ),
        (
            "fn step(op: cap Ask ! {panic}) -> i64 ! {panic} { perform op(1) }",
            "let g = step; 0",
            "capability parameter",
        ),
    ] {
        rejects(&program(helpers, "panic", body), fragment);
    }
    // Only declared operations have capability types.
    rejects(
        "fn f(op: cap Nope ! {}) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "declared effect operation",
    );
}

// ---------------------------------------------------------------------------
// EFF-CAP-RESUME: non-tail, multishot and capturing capability handlers
// ---------------------------------------------------------------------------

/// The same body performed through the capability and by name must agree.
fn same_as_by_name(handler: &str, row: &str, body: &str, expected: i64) {
    for (binding, target) in [("as ask ", "ask"), ("", "Ask")] {
        let source = format!(
            "effect Ask: i64 -> i64;
             fn main() -> i64 ! {{{row}}} {{
                 handle Ask: i64 -> i64 {binding}with {handler} {{ {} }}
             }}",
            body.replace("TARGET", target)
        );
        agrees(&source, expected, "");
    }
}

#[test]
fn non_tail_capability_handlers_resume_in_their_own_body() {
    // The handler runs code after `resume`: each perform suspends the rest
    // of the body; an owned box is live across every perform.
    let stats_body = "let b = Box.new(7);
         let mut sum = 0;
         let mut i = 0;
         while i < 3 { sum = sum + perform TARGET(i); i = i + 1; }
         sum + Box.take(b)";
    same_as_by_name(
        "fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { let r = resume(x | 16); r ^ 1 }",
        "alloc, panic",
        stats_body,
        // (16 + 17 + 18 + 7) with the low bit flipped by three activations.
        ((16 + 17 + 18 + 7) ^ 1) as i64,
    );
}

#[test]
fn multishot_capability_handlers_copy_the_continuation() {
    same_as_by_name(
        "fn(x: i64, resume: fn(i64) -> i64 ! {}) -> i64 ! {} { let a = resume(1); let b = resume(2); a ^ (b | 1024) }",
        "panic",
        "let base = 40; let v = perform TARGET(0); v + base",
        41 ^ (42 | 1024),
    );
}

#[test]
fn capturing_capability_handlers_run_in_their_own_body() {
    agrees(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {alloc, panic} {
             let k = 100;
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(x + k) } { perform ask(1) + 2 }
         }",
        103,
        "",
    );
}

#[test]
fn capturing_and_multishot_capabilities_stay_in_their_body() {
    // EFF-CAP-RESUME-CALLS lets non-tail one-shot noncapturing handlers
    // cross calls (tests in `capability_resumption_across_calls` below).
    let step = "fn step(op: cap Ask ! {}, x: i64) -> i64 ! {} { perform op(x) }";
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             {step}
             fn main() -> i64 ! {{panic}} {{
                 handle Ask: i64 -> i64 as ask with fn(x: i64, resume: fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{ resume(x) }} {{ step(ask, 1) }}
             }}"
        ),
        "capturing or multishot",
    );
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             {step}
             fn main() -> i64 ! {{alloc, panic}} {{
                 let k = 4;
                 handle Ask: i64 -> i64 as ask with fn(
                     x: i64,
                     resume: linear once fn(i64) -> i64 ! {{}},
                 ) -> i64 ! {{}} {{ resume(x | k) }} {{ step(ask, 1) }}
             }}"
        ),
        "capturing or multishot",
    );
}

#[test]
fn a_non_tail_capability_names_its_activation_inside_a_nested_handle() {
    // Performing the outer non-tail capability inside a nested handle for
    // the same operation would have to reinstate the inner handler.
    rejects(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { let r = resume(x); r ^ 1 } {
                 let a = perform ask(1);
                 handle Ask: i64 -> i64 with fn(
                     y: i64,
                     resume: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {} { resume(y) } { let b = perform ask(2); a + b }
             }
         }",
        "nested 'handle",
    );
    rejects(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 as op with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x) } { 0 }
         }
         fn other() -> i64 ! {panic} {
             handle Local: i64 -> i64 as op with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(x) } { perform op(1) }
         }",
        "declared effect operation",
    );
}

#[test]
fn identifiers_named_cap_and_as_still_work() {
    agrees(
        "struct Pair { cap: i64, as: i64 }
         fn main() -> i64 ! {panic} {
             let cap = 40;
             let as = 2;
             let p = Pair { cap: cap, as: as };
             p.cap + p.as
         }",
        42,
        "",
    );
}

#[test]
fn capability_performs_clean_up_owned_values() {
    let stats = agrees(
        &program(
            "fn boxed(op: cap Ask ! {panic}, b: Box<i64>) -> i64 ! {alloc, panic} {
                 let v = Box.take(b);
                 let w = Box.new(v);
                 perform op(Box.take(w))
             }",
            "alloc, panic",
            "let keep = Box.new(5); let r = boxed(ask, Box.new(1)); r + Box.take(keep)",
        ),
        106,
        "",
    );
    assert_eq!(stats.allocations, 3);
}

// Review regressions.

#[test]
fn a_capability_only_handler_does_not_discharge_called_performs() {
    // The handler has effects, so it is not on the dynamic stack; a called
    // function's `Ask` must stay in the enclosing row.
    rejects(
        "effect Ask: i64 -> i64;
         fn g() -> i64 ! {Ask, panic} { perform Ask(1) }
         fn h() -> i64 ! {panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(x + 100) } { g() }
         }
         fn main() -> i64 ! {panic} { h() }",
        "operation requires effects {Ask}",
    );
    // With the outer handler in scope the row is honest and the outer
    // handler serves the call.
    agrees(
        "effect Ask: i64 -> i64;
         fn g() -> i64 ! {Ask, panic} { perform Ask(1) }
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(7) } {
                 handle Ask: i64 -> i64 as ask with fn(
                     x: i64,
                     resume: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {panic} { resume(x + 100) } { g() + perform ask(1) }
             }
         }",
        108,
        "",
    );
}

#[test]
fn a_capability_whose_handler_performs_declared_operations_stays_local() {
    // In a callee its `Log` would be caught by the callee's own handlers.
    rejects(
        "effect Ask: i64 -> i64;
         effect Log: i64 -> i64;
         fn f(op: cap Ask ! {Log, panic}) -> i64 ! {Log, panic} { perform op(1) }
         fn main() -> i64 ! {panic} {
             handle Log: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(9) } {
                 handle Ask: i64 -> i64 as ask with fn(
                     x: i64,
                     resume: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {Log, panic} { resume(perform Log(x)) } { f(ask) }
             }
         }",
        "performs declared operations",
    );
    // Builtin effects travel with a passed capability.
    agrees(
        "effect Ask: i64 -> i64;
         fn f(op: cap Ask ! {io, panic}) -> i64 ! {io, panic} { perform op(2) }
         fn main() -> i64 ! {io, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {io, panic} { print_i64(x); resume(x) } { f(ask) }
         }",
        2,
        "2\n",
    );
}

/// EFF-CAP-RESUME-CALLS: a non-tail, one-shot, noncapturing handler's
/// capability may be passed to `cap` parameters. A function that performs
/// through such a parameter (directly or by passing it on) gets a resumable
/// entry keyed by the parameter index, and calls that pass the capability
/// become await points of the handled body.
#[test]
fn capability_resumption_across_calls() {
    const NON_TAIL: &str = "handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        k: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} { let r = k(x * 10); r ^ 1 }";
    // Two calls deep, with an owned value live across the first perform.
    agrees(
        &format!(
            "effect Ask: i64 -> i64;
             fn step(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ perform op(x) + 1 }}
             fn twice(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{alloc, panic}} {{
                 let b = Box.new(x);
                 let y = step(op, Box.take(b));
                 let c = Box.new(y);
                 step(op, Box.take(c))
             }}
             fn main() -> i64 ! {{alloc, panic}} {{ {NON_TAIL} {{ twice(ask, 1) }} }}"
        ),
        111,
        "",
    );
    const PLUS_ONE: &str = "handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        k: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} { let r = k(x + 1); r }";
    // Points in a callee loop, recursion, and a callee that only forwards.
    agrees(
        &format!(
            "effect Ask: i64 -> i64;
             fn sum(op: cap Ask ! {{panic}}, n: i64) -> i64 ! {{alloc, panic}} {{
                 let mut acc = 0;
                 let mut i = 0;
                 while i < n {{ let t = Box.new(i); acc = acc + perform op(Box.take(t)); i = i + 1; }}
                 acc
             }}
             fn rec(op: cap Ask ! {{panic}}, n: i64) -> i64 ! {{alloc, panic}} {{
                 if n == 0 {{ 0 }} else {{
                     let keep = Box.new(n);
                     perform op(n) + rec(op, n - 1) + Box.take(keep) - n
                 }}
             }}
             fn ignore(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ x * 2 }}
             fn forward(op: cap Ask ! {{panic}}, n: i64) -> i64 ! {{alloc, panic}} {{ sum(op, n) }}
             fn main() -> i64 ! {{alloc, panic}} {{
                 {PLUS_ONE} {{
                     let held = Box.new(100);
                     let a = forward(ask, 3);
                     let b = rec(ask, 3);
                     a + b + ignore(ask, 5) + perform ask(1) + Box.take(held)
                 }}
             }}"
        ),
        6 + 9 + 10 + 2 + 100,
        "",
    );
    // A capability-only handler with effects runs its code after `resume`.
    agrees(
        "effect Ask: i64 -> i64;
         fn f(op: cap Ask ! {io, panic}) -> i64 ! {io, panic} { perform op(2) + perform op(3) }
         fn main() -> i64 ! {io, alloc, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 k: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {io, panic} { print_i64(x); let r = k(x); print_i64(r); r + 100 } { f(ask) }
         }",
        205,
        "2\n3\n5\n105\n",
    );
    // A declared, dynamically visible non-tail handler: the capability and
    // by-name performs in callees reach the same activation.
    agrees(
        "effect Ask: i64 -> i64;
         fn by_cap(op: cap Ask ! {}, x: i64) -> i64 ! {} { perform op(x) }
         fn by_name(x: i64) -> i64 ! {Ask, panic} { perform Ask(x) }
         fn main() -> i64 ! {alloc, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 k: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { let r = k(x ^ 4); r ^ 1 } { by_cap(ask, 1) ^ by_name(2) }
         }",
        ((1 ^ 4) ^ (2 ^ 4)) ^ 1 ^ 1,
        "",
    );
}

#[test]
fn capability_resumption_across_calls_is_checked() {
    const NON_TAIL: &str = "handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        k: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} { let r = k(x); r ^ 1 }";
    // A call given the capability inside a nested dynamic handle.
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             effect Log: i64 -> i64;
             fn step(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ perform op(x) }}
             fn main() -> i64 ! {{panic}} {{
                 {NON_TAIL} {{
                     handle Log: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{ k(x) }} {{ step(ask, 1) }}
                 }}
             }}"
        ),
        "inside a nested handler",
    );
    // A callee performing through the capability inside its own handle.
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             effect Log: i64 -> i64;
             fn step(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{
                 handle Log: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{ k(x) }} {{ perform op(x) }}
             }}
             fn main() -> i64 ! {{panic}} {{ {NON_TAIL} {{ step(ask, 1) }} }}"
        ),
        "nested handler or handled body",
    );
    // The handled body must produce the operation result.
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             fn step(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ perform op(x) }}
             fn f() -> Bool ! {{panic}} {{ {NON_TAIL} {{ step(ask, 1) == 1 }} }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "must produce the operation result type",
    );
}

/// EFF-CAP-LAMBDA: a lambda may capture a capability whose handler runs in
/// place. The closure is a scoped borrow of the capability (the
/// borrowed-capture closure rules): bound directly to a local or called
/// immediately, never moved, returned, stored or passed on, and never live
/// across a non-tail perform.
const IN_PLACE: &str = "handle Ask: i64 -> i64 as ask with fn(
    x: i64,
    k: linear once fn(i64) -> i64 ! {},
) -> i64 ! {panic} { k(x + 100) }";

fn in_place(helpers: &str, body: &str) -> String {
    format!(
        "effect Ask: i64 -> i64;
         {helpers}
         fn main() -> i64 ! {{alloc, panic}} {{ {IN_PLACE} {{ {body} }} }}"
    )
}

#[test]
fn a_lambda_performs_through_a_captured_capability() {
    agrees(
        &in_place(
            "fn step(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { perform op(x) * 2 + 1 }",
            "let g = fn(y: i64) -> i64 ! {alloc, panic} {
                 let h = fn(z: i64) -> i64 ! {panic} { step(ask, z) };
                 h(y) + perform ask(0)
             };
             g(1)",
        ),
        303,
        "",
    );
    // With owned values in the closure environment and around it.
    agrees(
        &in_place(
            "",
            "let b = Box.new(5);
             let owned = Box.new(7);
             let f = fn() -> i64 ! {alloc, panic} { perform ask(Box.take(owned)) };
             f() + Box.take(b)",
        ),
        112,
        "",
    );
}

#[test]
fn a_lambda_capturing_a_capability_is_scoped() {
    let scoped = "is scoped";
    rejects(
        &in_place("", "let f = fn() -> i64 ! {panic} { perform ask(1) }; f")
            .replace(
                "fn main() -> i64 ! {alloc, panic} {",
                "fn main() -> i64 ! {alloc, panic} { let g = ",
            )
            .replace("; f } }", "; f }; g() }"),
        scoped,
    );
    rejects(
        &in_place(
            "fn call(f: once fn() -> i64 ! {panic}) -> i64 ! {panic} { f() }",
            "let f = fn() -> i64 ! {panic} { perform ask(1) }; call(f)",
        ),
        scoped,
    );
    rejects(
        &in_place(
            "",
            "let v: Vec<once fn() -> i64 ! {panic}> = Vec.new();
             let w = Vec.push(v, fn() -> i64 ! {panic} { perform ask(1) }); 0",
        ),
        "must be called immediately or bound directly to a local",
    );
    rejects(
        "effect Ask: i64 -> i64;
         fn leak(op: cap Ask ! {panic}) -> once fn() -> i64 ! {panic} ! {alloc, panic} {
             fn() -> i64 ! {panic} { perform op(1) }
         }
         fn main() -> i64 ! {} { 0 }",
        "a 'cap' parameter may be bound to a handler with code after 'resume'",
    );
    // Still second-class inside the lambda.
    rejects(
        &in_place("", "let f = fn() -> i64 ! {panic} { let c = ask; 0 }; f()"),
        "second-class capability",
    );
    // Not live across a non-tail perform of another handler.
    rejects(
        &in_place(
            "",
            "handle G: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {panic} { let r = k(x); r + 1 } {
                 let f = fn() -> i64 ! {panic} { perform ask(1) };
                 let a = perform G(1);
                 f() + a
             }",
        ),
        "cannot stay live across a non-tail 'perform'",
    );
    // Only capabilities whose handler runs in place can be captured.
    rejects(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {alloc, panic} {
             handle Ask: i64 -> i64 as ask with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {panic} { let r = k(x); r + 1 } {
                 let f = fn() -> i64 ! {panic} { perform ask(1) }; f()
             }
         }",
        "whose handler runs in place",
    );
}

/// Review findings for EFF-CAP-RESUME-CALLS / EFF-CAP-LAMBDA: each case
/// previously ran a handler with code after `resume` in place (the shallow
/// answer) or let an unpassable capability through.
#[test]
fn review_regressions_for_capability_resumption() {
    const NON_TAIL: &str = "handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        k: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} { let r = k(x * 10); r ^ 1 }";
    const STEP: &str =
        "fn step(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { perform op(x) + 1 }";
    // A lambda cannot capture a `cap` parameter: it may be non-tail.
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             fn step(op: cap Ask ! {{panic}}, x: i64) -> i64 ! {{alloc, panic}} {{
                 let f = fn(y: i64) -> i64 ! {{panic}} {{ perform op(y) }};
                 f(x) + 1
             }}
             fn main() -> i64 ! {{alloc, panic}} {{ {NON_TAIL} {{ step(ask, 1) }} }}"
        ),
        "a 'cap' parameter may be bound to a handler with code after 'resume'",
    );
    // The same non-tail capability passed to two parameters of one call.
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             fn two(a: cap Ask ! {{panic}}, b: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ perform b(x) + 1 }}
             fn main() -> i64 ! {{panic}} {{ {NON_TAIL} {{ two(ask, ask, 1) }} }}"
        ),
        "cannot be passed to two parameters of one call",
    );
    rejects(
        &format!(
            "effect Ask: i64 -> i64;
             fn two(a: cap Ask ! {{panic}}, b: cap Ask ! {{panic}}, x: i64) -> i64 ! {{panic}} {{ perform b(x) + 1 }}
             fn fwd(op: cap Ask ! {{panic}}) -> i64 ! {{panic}} {{ two(op, op, 1) }}
             fn main() -> i64 ! {{panic}} {{ {NON_TAIL} {{ fwd(ask) }} }}"
        ),
        "cannot be passed to two parameters of one call",
    );
    // A call nested in the operand of another suspension point is an await
    // point too: same answer as the hoisted form.
    for body in [
        "perform ask(step(ask, 1))",
        "let a = step(ask, 1); perform ask(a)",
    ] {
        agrees(
            &format!(
                "effect Ask: i64 -> i64;
                 {STEP}
                 fn main() -> i64 ! {{alloc, panic}} {{ {NON_TAIL} {{ {body} }} }}"
            ),
            110,
            "",
        );
    }
    // A lambda inside a non-tail handle body does not inherit the outer
    // handle's resumable capabilities.
    rejects(
        "effect Ask: i64 -> i64;
         effect Log: i64 -> i64;
         fn step(op: cap Ask ! {Log, panic}, x: i64) -> i64 ! {Log, panic} { perform op(x) }
         fn main() -> i64 ! {alloc, panic} {
             handle Ask: i64 -> i64 as outer with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {panic} { let r = k(x); r ^ 1 } {
                 let f = fn() -> i64 ! {alloc, panic} {
                     handle Log: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { k(x) } {
                         handle Ask: i64 -> i64 as c with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {Log, panic} { k(perform Log(x)) } {
                             step(c, 1)
                         }
                     }
                 };
                 let a = perform outer(1);
                 a + f()
             }
         }",
        "can only be performed in its own 'handle' body",
    );
}
