//! EFF-CAP-RESUME-MULTISHOT: multishot resumption tokens (`multi fn`) and
//! multishot capabilities across calls (docs/multishot-capabilities.md).
//!
//! A `multi fn(R) -> R` token is copyable and second-class; its environment
//! lives on the task's continuation stack and is released when the token
//! call or `handle` that pushed it returns.

use kush::executable::{MemoryStats, check};

/// Run in the reference evaluator (allocations balanced: every continuation
/// environment was released) and natively with the continuation stack
/// poisoned on release, and compare.
fn agrees(source: &str, expected: i64, stdout: &str) -> MemoryStats {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_stats(&mut output)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(result, expected, "{source}");
    assert_eq!(String::from_utf8(output).unwrap(), stdout, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("multishot-capabilities");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary)
            .env("KUSH_KSTACK_POISON", "1")
            .output()
            .unwrap();
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

/// A multishot handler whose body is `{body}`, around a handled body that
/// performs `Choose` once and adds the live value `base`.
fn handler_body(helpers: &str, body: &str) -> String {
    format!(
        "{helpers}
         fn main() -> i64 ! {{alloc, panic}} {{
             let base = 10;
             handle Choose: i64 -> i64 with fn(
                 n: i64,
                 resume: multi fn(i64) -> i64 ! {{}},
             ) -> i64 ! {{alloc, panic}} {{ {body} }} {{
                 let c = perform Choose(2);
                 c + base
             }}
         }}"
    )
}

// ---------------------------------------------------------------------------
// MS-TYPE: the token type and its second-class rules
// ---------------------------------------------------------------------------

#[test]
fn a_token_cannot_be_returned() {
    rejects(
        &handler_body(
            "fn pass(r: multi fn(i64) -> i64 ! {}) -> multi fn(i64) -> i64 ! {} ! {} { r }",
            "resume(0)",
        ),
        "a function cannot return it",
    );
}

#[test]
fn a_token_cannot_be_stored() {
    rejects(
        &handler_body(
            "struct Holder { r: multi fn(i64) -> i64 ! {} }",
            "let h = Holder { r: resume }; resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
    rejects(
        &handler_body(
            "enum Maybe { None, Some(multi fn(i64) -> i64 ! {}) }",
            "let m = Maybe.Some(resume); resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
    rejects(
        &handler_body(
            "",
            "let mut v: Vec<multi fn(i64) -> i64 ! {}> = Vec.new(); resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
}

#[test]
fn a_token_cannot_be_captured() {
    rejects(
        &handler_body(
            "",
            "let again = fn(x: i64) -> i64 ! {} { resume(x) }; again(0)",
        ),
        "a closure cannot capture it",
    );
}

#[test]
fn a_token_is_not_a_function_pointer() {
    rejects(
        &handler_body(
            "fn apply(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }",
            "apply(resume, 0)",
        ),
        "found multi fn(i64) -> i64 ! {}",
    );
    rejects(
        &handler_body(
            "fn apply(f: once fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }",
            "apply(resume, 0)",
        ),
        "found multi fn(i64) -> i64 ! {}",
    );
}

#[test]
fn a_handler_names_the_token_forms() {
    rejects(
        "fn main() -> i64 ! {panic} {
             handle Op: i64 -> i64 with fn(
                 x: i64,
                 resume: multi fn(i64) -> Bool ! {},
             ) -> i64 ! {panic} { 0 } { perform Op(1) }
         }",
        "'multi fn(i64) -> i64'",
    );
}

#[test]
fn multi_stays_an_ordinary_name() {
    // `multi` is contextual: only `multi fn` and `cap multi Op` are special.
    let program = check(
        "fn multi(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
             let m = multi(1);
             let multi = 2;
             multi + m
         }",
    );
    assert!(program.is_ok(), "{:?}", program.err());
}

// ---------------------------------------------------------------------------
// MS-TOKEN: lexical performs with `multi fn` tokens
// ---------------------------------------------------------------------------

#[test]
fn each_resumption_starts_from_the_same_live_values() {
    let stats = agrees(
        &handler_body("", "let a = resume(1); let b = resume(2); a * 1000 + b"),
        11012,
        "",
    );
    // One environment for the perform's continuation (it holds `base`).
    assert_eq!(stats.allocations, 1);
    // A token is copied into a local and passed to a helper.
    agrees(
        &handler_body(
            "fn twice(r: multi fn(i64) -> i64 ! {}, x: i64) -> i64 ! {panic} { r(x) + r(x + 1) }",
            "let again = resume; again(5) + twice(resume, 1)",
        ),
        15 + 11 + 12,
        "",
    );
}

#[test]
fn a_handler_may_resume_any_number_of_times() {
    agrees(&handler_body("", "n + 40"), 42, "");
    agrees(&handler_body("", "resume(n)"), 12, "");
    agrees(
        &handler_body(
            "",
            "let a = resume(1); let b = resume(2); let c = resume(3); a + b + c",
        ),
        36,
        "",
    );
}

#[test]
fn every_combination_of_choices_through_a_loop() {
    // Each of `n` performs yields 0 then 1; the handler sums both runs, so
    // the result sums `s` over all 2^n combinations, where s counts the
    // ones weighted by position: sum = 2^(n-1) * (1 + 2 + ... + n).
    let source = |n: i64| {
        format!(
            "fn main() -> i64 ! {{alloc, panic}} {{
                 handle Choose: i64 -> i64 with fn(
                     x: i64,
                     resume: multi fn(i64) -> i64 ! {{}},
                 ) -> i64 ! {{panic}} {{ resume(0) + resume(1) }} {{
                     let mut s = 0;
                     let mut i = 0;
                     while i < {n} {{
                         let c = perform Choose(i);
                         s = s + c * (i + 1);
                         i = i + 1;
                     }}
                     s
                 }}
             }}"
        )
    };
    agrees(&source(2), 6, "");
    agrees(&source(4), 80, "");
}

#[test]
fn printing_resumptions_run_in_order() {
    agrees(
        "fn main() -> i64 ! {alloc, io, panic} {
             handle Choose: i64 -> i64 with fn(
                 x: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { let a = resume(1); let b = resume(2); a + b } {
                 let label = 7;
                 let c = perform Choose(0);
                 print_i64(label * 10 + c);
                 c
             }
         }",
        3,
        "71\n72\n",
    );
}

#[test]
fn multishot_live_values_must_be_copyable() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
             handle Choose: i64 -> i64 with fn(
                 x: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(0) + resume(1) } {
                 let b = Box.new(5);
                 let c = perform Choose(0);
                 c + Box.take(b)
             }
         }",
        "owned, linear, or graded and cannot be copied",
    );
}

#[test]
fn a_token_cannot_stay_live_across_a_perform() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
             handle Choose: i64 -> i64 with fn(
                 x: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {alloc, panic} {
                 handle Inner: i64 -> i64 with fn(
                     y: i64,
                     k: linear once fn(i64) -> i64 ! {},
                 ) -> i64 ! {panic} { let r = k(y); r + 1 } {
                     let a = perform Inner(1);
                     resume(a)
                 }
             } {
                 let c = perform Choose(0);
                 c + 1
             }
         }",
        "cannot stay live across a 'perform'",
    );
}

// ---------------------------------------------------------------------------
// MS-CAP: `cap multi Op` across calls
// ---------------------------------------------------------------------------

/// `main` handles `Choose` with a multishot handler whose body is
/// `{handler}` and runs `{body}` with the capability `op`.
fn across(helpers: &str, handler: &str, body: &str) -> String {
    format!(
        "effect Choose: i64 -> i64;
         {helpers}
         fn main() -> i64 ! {{alloc, panic}} {{
             handle Choose: i64 -> i64 as op with fn(
                 n: i64,
                 resume: multi fn(i64) -> i64 ! {{}},
             ) -> i64 ! {{panic}} {{ {handler} }} {{ {body} }}
         }}"
    )
}

const CAP: &str = "op: cap multi Choose ! {panic}";

#[test]
fn a_callee_performs_twice_through_a_multishot_capability() {
    // a in {0, 1}, b in {0, 2}: (100 + 102) + (110 + 112).
    agrees(
        &across(
            &format!(
                "fn two({CAP}, base: i64) -> i64 ! {{panic}} {{
                     let a = perform op(1);
                     let b = perform op(2);
                     base + a * 10 + b
                 }}"
            ),
            "resume(0) + resume(n)",
            "two(op, 100)",
        ),
        424,
        "",
    );
}

#[test]
fn live_values_at_every_level_of_a_chain_are_kept() {
    let helpers = format!(
        "fn leaf({CAP}, x: i64) -> i64 ! {{panic}} {{ let c = perform op(2); x * 10 + c }}
         fn middle({CAP}, x: i64) -> i64 ! {{panic}} {{
             let y = x + 1;
             let r = leaf(op, y);
             r + y * 1000
         }}
         fn top({CAP}, x: i64) -> i64 ! {{panic}} {{
             let z = x * 2;
             let r = middle(op, z);
             r + z * 100000
         }}"
    );
    agrees(
        &across(&helpers, "resume(0) + resume(1)", "top(op, 1)"),
        406061,
        "",
    );
    // The handled body's own live value survives both resumptions too.
    agrees(
        &across(
            &helpers,
            "resume(0) * 1000000 + resume(1)",
            "let k = 7; top(op, 1) + k",
        ),
        203037 * 1000000 + 203038,
        "",
    );
}

/// Counting the leaves of a binary choice tree of depth `depth`.
fn leaves(depth: i64) -> String {
    across(
        &format!(
            "fn count({CAP}, depth: i64) -> i64 ! {{panic}} {{
                 if depth == 0 {{
                     1
                 }} else {{
                     let c = perform op(2);
                     count(op, depth - 1) + c * 0
                 }}
             }}"
        ),
        "resume(0) + resume(1)",
        &format!("count(op, {depth})"),
    )
}

#[test]
fn recursive_search_resumes_through_every_level() {
    agrees(&leaves(3), 8, "");
}

/// All placements of `n` queens: `Choose(n)` picks the column of the next
/// row; the board is one copyable integer (three bits per row).
fn queens(n: i64) -> String {
    across(
        &format!(
            "fn safe(placed: i64, row: i64, column: i64) -> Bool ! {{panic}} {{
                 let mut ok = true;
                 let mut k = 1;
                 let mut rest = placed;
                 while k <= row {{
                     let other = rest % 8;
                     if other == column || other - column == k || column - other == k {{
                         ok = false;
                     }}
                     rest = rest / 8;
                     k = k + 1;
                 }}
                 ok
             }}
             fn place({CAP}, n: i64, row: i64, placed: i64) -> i64 ! {{panic}} {{
                 if row == n {{
                     1
                 }} else {{
                     let column = perform op(n);
                     if safe(placed, row, column) {{
                         place(op, n, row + 1, placed * 8 + column)
                     }} else {{
                         0
                     }}
                 }}
             }}"
        ),
        "let mut total = 0;
         let mut i = 0;
         while i < n {
             total = total + resume(i);
             i = i + 1;
         }
         total",
        &format!("place(op, {n}, 0, 0)"),
    )
}

#[test]
fn queens_are_counted_by_a_multishot_search() {
    agrees(&queens(4), 2, "");
}

/// Deeper searches run natively only: the evaluator's nesting budget is
/// small. The continuation stack stays proportional to the depth.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn deep_searches_run_natively() {
    for (source, expected) in [(leaves(12), 4096_i64), (queens(6), 4)] {
        let program = check(&source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("multishot-deep");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary)
            .env("KUSH_KSTACK_POISON", "1")
            .output()
            .unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
    }
}

#[test]
fn return_in_a_callee_continues_every_resumption() {
    agrees(
        &across(
            &format!(
                "fn early({CAP}, x: i64) -> i64 ! {{panic}} {{
                     let c = perform op(2);
                     if c == 1 {{
                         return x + 100;
                     }}
                     x + c
                 }}"
            ),
            "resume(0) * 1000 + resume(1)",
            "early(op, 5) + 1",
        ),
        6106,
        "",
    );
}

#[test]
fn a_handler_that_never_resumes_releases_the_chain() {
    let stats = agrees(
        &across(
            &format!(
                "fn deep({CAP}, x: i64) -> i64 ! {{panic}} {{
                     let y = x + 1;
                     let c = perform op(1);
                     c + y
                 }}"
            ),
            "n + 41",
            "let k = 3; deep(op, k) + k",
        ),
        42,
        "",
    );
    assert!(stats.allocations > 0);
}

#[test]
fn a_tail_resumptive_multishot_capability_runs_in_place() {
    let stats = agrees(
        &across(
            &format!(
                "fn two({CAP}, x: i64) -> i64 ! {{panic}} {{
                     let a = perform op(x);
                     let b = perform op(a);
                     a + b
                 }}"
            ),
            "resume(n + 1)",
            "two(op, 1)",
        ),
        5,
        "",
    );
    assert_eq!(stats.allocations, 0);
}

#[test]
fn one_shot_and_multishot_capabilities_do_not_mix() {
    // A multishot handler passed to a one-shot 'cap' parameter.
    rejects(
        &across(
            "fn one(op: cap Choose ! {panic}) -> i64 ! {panic} { perform op(1) }",
            "resume(0) + resume(1)",
            "one(op)",
        ),
        "type mismatch",
    );
    // A one-shot handler passed to a 'cap multi' parameter.
    rejects(
        &format!(
            "effect Choose: i64 -> i64;
             fn several({CAP}) -> i64 ! {{panic}} {{ perform op(1) }}
             fn main() -> i64 ! {{alloc, panic}} {{
                 handle Choose: i64 -> i64 as op with fn(
                     n: i64,
                     resume: linear once fn(i64) -> i64 ! {{}},
                 ) -> i64 ! {{panic}} {{ let r = resume(n); r + 1 }} {{ several(op) }}
             }}"
        ),
        "type mismatch",
    );
}

#[test]
fn callee_live_values_must_be_copyable_too() {
    rejects(
        &across(
            "fn owned(op: cap multi Choose ! {alloc, panic}) -> i64 ! {alloc, panic} {
                 let b = Box.new(5);
                 let c = perform op(1);
                 c + Box.take(b)
             }",
            "resume(0) + resume(1)",
            "owned(op)",
        ),
        "owned, linear, or graded and cannot be copied",
    );
}

#[test]
fn a_multishot_handler_cannot_abort_past_its_tokens() {
    // A `multi fn` token is pure, so an abort cannot leave a handled body
    // through it, and a handler that may abort is rejected: nothing can
    // leave a multishot `handle` without its continuation-stack restore.
    // (Natively, abortive scopes also restore the stack where they land.)
    rejects(
        "effect Fail: i64 -> Never;
         fn main() -> i64 ! {alloc, panic} {
             handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {panic} { c + 10 } {
                 handle Choose: i64 -> i64 with fn(
                     x: i64,
                     resume: multi fn(i64) -> i64 ! {},
                 ) -> i64 ! {Fail, panic} {
                     let a = resume(1);
                     if a > 0 { perform Fail(a) };
                     a
                 } {
                     let base = 5;
                     let c = perform Choose(0);
                     c + base
                 }
             }
         }",
        "must name the abortive operation in its row",
    );
}

// ---------------------------------------------------------------------------
// MS-STRESS-DOCS: the continuation stack holds the search path, not the search
// ---------------------------------------------------------------------------

/// Peak continuation-stack bytes of a native run (`KUSH_KSTACK_STATS`).
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn peak_stack_bytes(source: &str, expected: i64) -> u64 {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("multishot-stress");
    kush::native::build_with_stats(&program, &binary, true).unwrap();
    let native = std::process::Command::new(&binary)
        .env("KUSH_KSTACK_POISON", "1")
        .env("KUSH_KSTACK_STATS", "1")
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&native.stderr);
    assert_eq!(
        native.status.code(),
        Some((expected as u64 & 255) as i32),
        "{stderr}"
    );
    stderr
        .lines()
        .find_map(|line| line.strip_prefix("kstack-stats: peak-bytes="))
        .unwrap_or_else(|| panic!("no stack statistics: {stderr}"))
        .parse()
        .unwrap()
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_stack_grows_with_the_depth_not_with_the_branches() {
    // 2^16 leaves: about 131,000 resumptions.
    let shallow = peak_stack_bytes(&leaves(8), 0);
    let deep = peak_stack_bytes(&leaves(16), 0);
    assert!(shallow > 0);
    // Twice the depth holds about twice the environments, however many
    // branches were explored and abandoned.
    assert!(
        deep <= 2 * shallow + 64,
        "depth 8: {shallow} bytes, depth 16: {deep} bytes"
    );
}

// ---------------------------------------------------------------------------
// Capturing multishot handlers across calls
// ---------------------------------------------------------------------------

#[test]
fn a_capturing_multishot_handler_serves_callees() {
    // The handler captures `scale` (copyable): it lives in a private,
    // reusable frame that the callee reaches through a trampoline, once per
    // perform and per resumed branch. a in {0, 1}, b in {0, 2}, scaled.
    let source = |row: &str| {
        format!(
            "effect Choose: i64 -> i64;
             fn two(op: cap multi Choose ! {{{row}}}, base: i64) -> i64 ! {{{row}}} {{
                 let a = perform op(1);
                 let b = perform op(2);
                 base + a * 10 + b
             }}
             fn main() -> i64 ! {{alloc, panic}} {{
                 let scale = 3;
                 handle Choose: i64 -> i64 as op with fn(
                     n: i64,
                     resume: multi fn(i64) -> i64 ! {{}},
                 ) -> i64 ! {{panic}} {{ resume(0) + resume(n * scale) * 0 + resume(n) }} {{
                     two(op, 100)
                 }}
             }}"
        )
    };
    // Each choice sums three runs (0, n * scale weighted 0, n).
    agrees(&source("panic"), 424, "");
    // The trampoline can panic (a missing frame), so the parameter must
    // allow it, as for capturing one-shot capabilities.
    rejects(&source(""), "this capability's handler is capturing");
}

#[test]
fn a_multishot_handler_owning_a_capture_stays_rejected() {
    rejects(
        "effect Choose: i64 -> i64;
         fn one(op: cap multi Choose ! {panic}) -> i64 ! {panic} { perform op(1) }
         fn main() -> i64 ! {alloc, panic} {
             let b = Box.new(3);
             handle Choose: i64 -> i64 as op with fn(
                 n: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {panic} { resume(0) + Box.take(b) } { one(op) }
         }",
        "capturing or multishot",
    );
}

// ---------------------------------------------------------------------------
// Tokens that name abortive operations
// ---------------------------------------------------------------------------

/// The multishot abort test of `abortive_handlers.rs` with a `multi fn`
/// token: an abort out of one resumption leaves the handler (later
/// resumptions do not run), past the continuation stack of the multishot
/// `handle`, which the abortive scope releases where it lands.
fn aborting(limit: &str) -> String {
    format!(
        "effect Fail: i64 -> Never;
         fn main() -> i64 ! {{io, alloc, panic}} {{
             let r = handle Fail: i64 -> Never with fn(c: i64) -> i64 ! {{}} {{ c ^ 1024 }} {{
                 let keep = Box.new(3);
                 let v = handle Pick: i64 -> i64 with fn(
                     x: i64,
                     k: multi fn(i64) -> i64 ! {{Fail}},
                 ) -> i64 ! {{Fail}} {{
                     k(x) ^ k(x ^ {limit})
                 }} {{
                     let base = 2;
                     let a = perform Pick(base);
                     if a > 10 {{ perform Fail(a + base) }};
                     print_i64(a);
                     a * 100 + base
                 }};
                 v + Box.take(keep)
             }};
             r
         }}"
    )
}

#[test]
fn an_abort_leaves_through_a_token_that_names_it() {
    // Both resumptions finish: (202 ^ 302) + 3.
    agrees(&aborting("1"), (202 ^ 302) + 3, "2\n3\n");
    // The second resumption (2 ^ 20 = 22) aborts with 22 + 2; the first one
    // printed.
    agrees(&aborting("20"), 24 ^ 1024, "2\n");
    // In a loop, so a leftover continuation environment would accumulate.
    agrees(
        &format!(
            "{}",
            aborting("20")
                .replace("fn main()", "fn once()")
                .replace("effect Fail: i64 -> Never;", "")
                + "effect Fail: i64 -> Never;
                   fn main() -> i64 ! {io, alloc, panic} {
                       let mut total = 0;
                       let mut i = 0;
                       while i < 50 { total = total + once(); i = i + 1; }
                       total & 255
                   }"
        ),
        (50 * (24 ^ 1024)) & 255,
        &"2\n".repeat(50),
    );
    // Without the operation in its row, the abort cannot leave.
    rejects(
        &aborting("20").replace(
            "k: multi fn(i64) -> i64 ! {Fail},\n                 ) -> i64 ! {Fail}",
            "k: multi fn(i64) -> i64 ! {},\n                 ) -> i64 ! {Fail}",
        ),
        "cannot leave the body of 'handle Pick'",
    );
}

#[test]
fn a_pure_tail_resumptive_multishot_capability_runs_in_place_in_a_loop() {
    // Found by the benchmark: a pure handler for a declared operation used
    // to be treated as dynamically visible and made the whole loop a state
    // machine. Bound `as op`, a multishot handler is capability-only.
    let stats = agrees(
        "effect Tick: i64 -> i64;
         fn work(op: cap multi Tick ! {}, x: i64) -> i64 ! {} { perform op(x) }
         fn main() -> i64 ! {panic} {
             handle Tick: i64 -> i64 as tick with fn(
                 x: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x ^ 5) } {
                 let mut s = 0;
                 let mut i = 0;
                 while i < 1000 { s = (s + work(tick, i)) & 1023; i = i + 1; }
                 s & 255
             }
         }",
        // sum of (i ^ 5) masked: computed below.
        (0..1000_i64).fold(0, |s, i| (s + (i ^ 5)) & 1023) & 255,
        "",
    );
    assert_eq!(stats.allocations, 0);
    // A callee performing `Tick` by name is not served by it.
    rejects(
        "effect Tick: i64 -> i64;
         fn named(x: i64) -> i64 ! {Tick} { perform Tick(x) }
         fn main() -> i64 ! {panic} {
             handle Tick: i64 -> i64 as tick with fn(
                 x: i64,
                 resume: multi fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x ^ 5) } { named(1) }
         }",
        "operation requires effects {Tick}",
    );
}
