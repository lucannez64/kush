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
    // A handler with effects is capability-only: a called function
    // performing Ask by name finds no handler and the program aborts in both
    // backends, so the handler's effects are never hidden from a row.
    let source = "effect Ask: i64 -> i64;
         fn via_name() -> i64 ! {Ask, panic} { perform Ask(2) }
         fn main() -> i64 ! {io, panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {io, panic} { print_i64(x); resume(x) } { perform ask(1) + via_name() }
         }";
    let program = check(source).unwrap();
    assert!(program.evaluate(&mut Vec::new()).is_err());
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("effect-capabilities-abort");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert!(!native.status.success());
        assert_eq!(String::from_utf8_lossy(&native.stdout), "1\n");
    }
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
        (
            "",
            "let f = fn() -> i64 ! {panic} { perform ask(1) }; f()",
            "second-class",
        ),
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

#[test]
fn only_noncapturing_tail_resumptive_handlers_bind_capabilities() {
    rejects(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { let r = resume(x); r + 1 } { perform ask(1) }
         }",
        "tail-resumptive",
    );
    rejects(
        "effect Ask: i64 -> i64;
         fn main() -> i64 ! {alloc, panic} {
             let b = Box.new(1);
             handle Ask: i64 -> i64 as ask with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(x + Box.take(b)) } { perform ask(1) }
         }",
        "noncapturing",
    );
    rejects(
        "fn main() -> i64 ! {panic} {
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
