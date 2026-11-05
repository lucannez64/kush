//! Abortive (non-resuming) handlers, docs/abortive-handlers.md.
//!
//! E-ABORT-LEXICAL: an operation whose result type is `Never` is abortive;
//! its handler takes only the payload and returns the `handle`'s value. A
//! `perform` lexically inside the `handle` in the same function leaves the
//! body like a labelled early exit with the cleanup of `?`. Every accepted
//! program runs in the reference evaluator and natively with balanced
//! allocations.

use kush::executable::{MemoryStats, check};

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
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
        let binary = scratch.path().join("abortive-handlers");
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

const FAIL: &str = "effect Fail: i64 -> Never;";
const HANDLER: &str = "fn(code: i64) -> i64 ! {panic} { code + 40 }";

fn handled(body: &str) -> String {
    format!("handle Fail: i64 -> Never with {HANDLER} {{ {body} }}")
}

#[test]
fn an_abortive_perform_leaves_the_handle_with_the_handler_value() {
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{ {} }}",
            handled("1 + perform Fail(2)")
        ),
        42,
        "",
    );
    // No abort: the body's value.
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{ {} }}",
            handled("let x = 5; x + 2")
        ),
        7,
        "",
    );
    // An undeclared (lexical) operation, from inside nested loops and a match.
    agrees(
        "fn main() -> i64 ! {panic} {
             let found = handle Found: i64 -> Never with fn(at: i64) -> i64 ! {} { at } {
                 let mut i = 0;
                 while i < 10 {
                     let mut j = 0;
                     loop {
                         if j == 4 { break; }
                         match i * 10 + j { 23 => perform Found(i * 10 + j), _ => {} }
                         j = j + 1;
                     }
                     i = i + 1;
                 }
                 0 - 1
             };
             found
         }",
        23,
        "",
    );
    // A `break` inside the body still targets the user's loop.
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 let mut sum = 0;
                 let mut i = 0;
                 while i < 5 {{
                     sum = sum + {};
                     i = i + 1;
                 }}
                 sum
             }}",
            handled("if i == 3 { perform Fail(0) } else { if i == 4 { 1 } else { 2 } }")
        ),
        2 + 2 + 2 + 40 + 1,
        "",
    );
}

#[test]
fn the_handler_runs_with_its_effects_and_captures() {
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{io, panic}} {{
                 handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {{io, panic}} {{ print_i64(code); code * 2 }} {{
                     print_i64(1);
                     if true {{ perform Fail(21) }};
                     print_i64(2);
                     0
                 }}
             }}"
        ),
        42,
        "1\n21\n",
    );
    // A capturing `once` handler consumes its environment on the abort path
    // and is dropped on the normal path.
    for (flag, expected) in [("true", 47), ("false", 3)] {
        agrees(
            &format!(
                "{FAIL} fn main() -> i64 ! {{alloc, panic}} {{
                     let kept = Box.new(7);
                     let h: once fn(i64) -> i64 ! {{alloc, panic}} = fn(code: i64) -> i64 ! {{alloc, panic}} {{ Box.take(kept) + code }};
                     handle Fail: i64 -> Never with h {{ if {flag} {{ perform Fail(40) }} else {{ 3 }} }}
                 }}"
            ),
            expected,
            "",
        );
    }
}

#[test]
fn an_abort_drops_owned_values_live_in_the_body() {
    // Locals, a pending temporary argument and a value inside a loop.
    let stats = agrees(
        &format!(
            "{FAIL}
             fn add(a: Box<i64>, b: i64) -> i64 ! {{alloc, panic}} {{ Box.take(a) + b }}
             fn main() -> i64 ! {{alloc, panic}} {{
                 let outer = Box.new(100);
                 let r = {};
                 Box.take(outer) + r
             }}",
            "handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {alloc, panic} { code } {
                 let a = Box.new(1);
                 let v: Vec<i64> = Vec.new();
                 let mut i = 0;
                 while i < 3 {
                     let inner = Box.new(i);
                     if i == 2 { add(Box.new(5), perform Fail(Box.take(inner))); }
                     i = i + 1;
                 }
                 Box.take(a)
             }"
        ),
        102,
        "",
    );
    assert!(stats.allocations >= 4, "{stats:?}");
    // The same body that does not abort.
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{alloc, panic}} {{
                 {}
             }}",
            handled(
                "let a = Box.new(1); let b = Box.new(2); if Box.take(b) == 3 { perform Fail(0) }; Box.take(a)"
            )
        ),
        1,
        "",
    );
}

#[test]
fn nested_handles_and_dynamic_frames() {
    // The innermost abortive handle for the same operation catches it.
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {{panic}} {{ c + 1000 }} {{
                     let inner = handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {{}} {{ c }} {{ perform Fail(5) }};
                     inner + 10
                 }}
             }}"
        ),
        15,
        "",
    );
    // An abort to an outer handle of another operation leaves the inner one.
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {{panic}} {{ c + 1 }} {{
                     handle Stop: i64 -> Never with fn(c: i64) -> i64 ! {{panic}} {{ c + 100 }} {{ perform Fail(5) }}
                 }}
             }}"
        ),
        6,
        "",
    );
    // An abort out of a declared tail-resumptive handle pops its dynamic
    // frame: the later dynamic perform reaches the outer handler.
    agrees(
        "effect Fail: i64 -> Never;
         effect Ask: i64 -> i64;
         fn ask(x: i64) -> i64 ! {Ask, panic} { perform Ask(x) }
         fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { k(x ^ 64) } {
                 let r = handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {} { c } {
                     handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { k(x ^ 1) } {
                         let first = ask(1);
                         perform Fail(first)
                     }
                 };
                 r + ask(0)
             }
         }",
        64,
        "",
    );
}

#[test]
fn grades_agree_across_abort_paths() {
    agrees(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 let x: i64 @[1] = 2;
                 {}
             }}",
            handled("if x > 1 { perform Fail(0) } else { 0 }")
        ),
        40,
        "",
    );
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 let x: i64 @[1] = 2;
                 let y = {};
                 y
             }}",
            handled("if true { perform Fail(0) } else { x }")
        ),
        "used a different number of times on different paths",
    );
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{ {} }}",
            handled("let z: i64 @[1] = 3; perform Fail(1)")
        ),
        "this abortive perform leaves its 'handle'",
    );
}

#[test]
fn pending_linear_values_reject_the_abort() {
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{alloc, panic}} {{ {} }}",
            handled("let b: Box<i64> @[1] = Box.new(1); perform Fail(1)")
        ),
        "linear value is not consumed before this abortive perform",
    );
    rejects(
        &format!(
            "{FAIL} #[linear] struct Token {{ id: i64 }}
             fn eat(t: Token, x: i64) -> i64 ! {{panic}} {{ let Token {{ id }} = t; id + x }}
             fn main() -> i64 ! {{panic}} {{ {} }}",
            handled("eat(Token { id: 1 }, perform Fail(1))")
        ),
        "pending linear value",
    );
    // An outer linear value consumed only on the normal path.
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{alloc, panic}} {{
                 let b: Box<i64> @[1] = Box.new(1);
                 {}
             }}",
            handled("if true { perform Fail(1) } else { Box.take(b) }")
        ),
        "consumed on one branch but not the other",
    );
}

#[test]
fn handler_and_operation_shapes_are_checked() {
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 handle Fail: i64 -> Never with fn(c: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{ c }} {{ 0 }}
             }}"
        ),
        "takes only the payload and no resumption token",
    );
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 handle Fail: i64 -> Never with fn(c: i64) -> Bool ! {{}} {{ true }} {{ 0 }}
             }}"
        ),
        "returns Bool, but the handled body produces i64",
    );
    rejects(
        "effect Fail: i64 -> i64; fn main() -> i64 ! {panic} {
             handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {} { c } { 0 }
         }",
        "must use the declared operation signature",
    );
    rejects(
        "effect Bad: Never -> i64; fn main() -> i64 ! {} { 0 }",
        "executable values support",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
             let v = [1, 2];
             handle Stop: &[i64] -> Never with fn(s: &[i64]) -> i64 ! {} { 0 } { perform Stop(&v) }
         }",
        "cannot hold a borrow",
    );
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 let h: linear once fn(i64) -> i64 ! {{}} = fn(c: i64) -> i64 ! {{}} {{ c }};
                 handle Fail: i64 -> Never with h {{ 0 }}
             }}"
        ),
        "not a linear one",
    );
    // `Never` stays rejected outside an operation result.
    rejects(
        "fn f() -> Never ! {} { f() } fn main() -> i64 ! {} { 0 }",
        "",
    );
    // Capabilities serve resumptive operations only.
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{panic}} {{
                 handle Fail: i64 -> Never as fail with fn(c: i64) -> i64 ! {{}} {{ c }} {{ 0 }}
             }}"
        ),
        "cannot be bound as a capability",
    );
    rejects(
        &format!(
            "{FAIL} fn f(op: cap Fail ! {{}}) -> i64 ! {{}} {{ 0 }} fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "names an abortive operation",
    );
}

#[test]
fn lexical_scope_limits_are_reported() {
    // A perform in a called function or a lambda is not lexically inside.
    rejects(
        &format!(
            "{FAIL} fn parse() -> i64 ! {{Fail, panic}} {{ perform Fail(1) }}
             fn main() -> i64 ! {{panic}} {{ {} }}",
            handled("parse()")
        ),
        "must be lexically inside its 'handle'",
    );
    rejects(
        &format!(
            "{FAIL} fn main() -> i64 ! {{alloc, panic}} {{ {} }}",
            handled("let f = fn(x: i64) -> i64 ! {Fail, panic} { perform Fail(x) }; f(1)")
        ),
        "must be lexically inside its 'handle'",
    );
    // A non-tail perform of another operation inside the abortive body.
    rejects(
        "fn main() -> i64 ! {panic} {
             handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {panic} { k(x) + 1 } {
                 handle Stop: i64 -> Never with fn(c: i64) -> i64 ! {} { c } {
                     let a = perform Ask(1);
                     a
                 }
             }
         }",
        "inside the body of the abortive 'handle Stop'",
    );
    // An abort out of a body whose handler has code after `resume`.
    rejects(
        "fn main() -> i64 ! {panic} {
             handle Stop: i64 -> Never with fn(c: i64) -> i64 ! {} { c } {
                 handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {panic} { k(x) + 1 } {
                     let a = perform Ask(1);
                     perform Stop(a)
                 }
             }
         }",
        "cannot leave the body of 'handle Ask'",
    );
}

#[test]
fn an_abortive_handle_inside_a_non_tail_body_moves_with_its_continuation() {
    // The abortive handle sits before and after a suspension point of an
    // enclosing non-tail handler, so the lowering moves it into a
    // continuation closure together with its exits.
    for (flag, expected) in [("1", 1 + 10 + 20 + 1), ("2", 2 + 2 + 20 + 1)] {
        agrees(
            &format!(
                "fn main() -> i64 ! {{alloc, panic}} {{
                     handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{panic}} {{ k(x) + 1 }} {{
                         let before = Box.new(20);
                         let early = handle Stop: i64 -> Never with fn(c: i64) -> i64 ! {{}} {{ c }} {{
                             let t = Box.new(3);
                             if Box.take(t) == 3 {{ perform Stop(Box.take(before)) }} else {{ 0 }}
                         }};
                         let a = perform Ask({flag});
                         let b = Box.new(a);
                         let r = handle Stop: i64 -> Never with fn(c: i64) -> i64 ! {{}} {{ c }} {{
                             let inner = Box.new(4);
                             if a == 1 {{ perform Stop(10) }} else {{ Box.take(inner) - 2 }}
                         }};
                         Box.take(b) + r + early
                     }}
                 }}"
            ),
            expected,
            "",
        );
    }
}
