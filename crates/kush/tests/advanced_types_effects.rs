//! Advanced types and effects: structural records, constrained subtype
//! inference, effect handlers, general row constraints, versioned runtime
//! proofs, and runtime-sized inline arrays.
//!
//! Each feature has positive, rejection, cleanup, and native/reference tests.
//! The tests describe the supported fragment, not a claim that the full v0.1
//! dependent/algebraic/effect calculus is implemented.

use kush::executable::{MemoryStats, check};

fn evaluate(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
    (result, stats)
}

fn value(source: &str) -> i64 {
    evaluate(source).0
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn agrees(source: &str, expected: i64) {
    use std::process::Command;
    let program = check(source).unwrap();
    let (reference, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(reference, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("advanced-types-effects");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
}

// ---------------------------------------------------------------------------
// Algebraic subtype inference
// ---------------------------------------------------------------------------

#[test]
fn contextual_union_inference_accumulates_literal_constraints() {
    // Each shape enumerates every matching union alternative, checks the
    // literal under each candidate, and requires exactly one survivor.
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 2] | [Bool; 2] = [20, 22];
            let b: Vec<i64> | Vec<Bool> = [1, 2];
            let c: (i64, i64) | (Bool, Bool) = (3, 4);
            match a {
                [i64; 2] @ xs => xs[0] + xs[1] + match b {
                    Vec<i64> @ vs => Vec.len(&vs) - 2,
                    Vec<Bool> @ _ => 0,
                } + match c {
                    (i64, i64) @ _ => 0,
                    (Bool, Bool) @ _ => 0,
                },
                [Bool; 2] @ _ => 0,
            }
        }"#;
    assert_eq!(value(source), 42);
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] | [Bool; 2] = [1, true];
            0
        }"#,
        "type mismatch",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let v: Vec<i64> | Vec<Bool> = Vec.new();
            0
        }"#,
        "fits several union alternatives",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let t: (i64, i64) | (Bool, Bool) = (1, true);
            0
        }"#,
        "type mismatch",
    );
}

#[test]
fn union_patterns_infer_the_residual_type_variable() {
    let source = r#"
        fn pick<T>(x: T | i64) -> i64 ! {panic} {
            match x {
                i64 @ n => n,
                _ => 0,
            }
        }
        fn three(c: i64) -> i64 | Bool | Unit ! {panic} {
            if c == 0 { 1 } else { if c == 1 { true } else { () } }
        }
        fn main() -> i64 ! {panic} {
            pick(three(0)) + pick(true)
        }"#;
    assert_eq!(value(source), 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 1);
    rejects(
        r#"
        fn pick<T>(x: T | i64) -> i64 ! {panic} { match x { i64 @ n => n, _ => 0 } }
        fn main() -> i64 ! {panic} { pick(1) }"#,
        "residual binding is not unique",
    );
    rejects(
        r#"
        fn pick<T, U>(x: T | U | i64) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} { pick(true) }"#,
        "cannot infer type parameter",
    );
}

#[test]
fn structural_literals_accumulate_contextual_union_candidates() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let v: struct { x: i64 } | struct { x: Bool } = struct { x: 40 };
            match v {
                struct { x: i64 } @ struct { x: n } => n + 2,
                struct { x: Bool } @ struct { x: _ } => 0,
            }
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // The contextual hint is not just cosmetic: the same literal text would
    // default to i64 without the expected Bool alternative.
    let hinted = r#"
        fn main() -> i64 ! {panic} {
            let v: struct { x: Bool } = struct { x: true };
            match v { struct { x } => if x { 42 } else { 0 } }
        }"#;
    assert_eq!(value(hinted), 42);
}

#[test]
fn generic_inference_across_union_alternatives_reports_conflicts() {
    rejects(
        r#"
        fn sized<T>(v: Vec<T>) -> i64 ! {panic} { Vec.len(&v) }
        fn make(c: Bool) -> Vec<i64> | Vec<Bool> ! {alloc, panic} {
            if c { [1, 2] } else { [true, false] }
        }
        fn main() -> i64 ! {alloc, panic} { sized(make(true)) }"#,
        "union alternatives disagree on type parameter 'T'",
    );
}

// ---------------------------------------------------------------------------
// General effect-row constraints
// ---------------------------------------------------------------------------

#[test]
fn row_constraints_accumulate_across_every_higher_order_argument() {
    // One shared row variable sees `{panic}` from `f` and `{io, panic}` from
    // `g`. The solver takes their union rather than letting the first argument
    // choose the row. The caller must declare the resulting union.
    let source = r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn two<e: Effects>(f: fn(i64) -> i64 ! {e}, g: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { g(f(x)) }
        fn main() -> i64 ! {io, panic} { two(inc, io_inc, 1) }"#;
    assert_eq!(value(source), 3);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 3);
    rejects(
        r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn two<e: Effects>(f: fn(i64) -> i64 ! {e}, g: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { g(f(x)) }
        fn main() -> i64 ! {panic} { two(inc, io_inc, 1) }"#,
        "requires effects {io}",
    );
}

#[test]
fn separate_row_variables_get_their_own_evidence() {
    let source = r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn both<e1: Effects, e2: Effects>(
            f: fn(i64) -> i64 ! {e1},
            g: fn(i64) -> i64 ! {e2},
        ) -> i64 ! {panic, e1, e2} { g(f(1)) }
        fn main() -> i64 ! {io, panic} { both(inc, io_inc) }"#;
    assert_eq!(value(source), 3);
}

#[test]
fn row_constraints_support_required_effects_and_combined_bounds() {
    // A lower bound requires `io` even though both callable arguments are
    // pure. The inferred specialization is therefore `{io}` and the caller
    // must declare it; `panic` still comes from the callable actuals.
    let inferred = r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn apply<e: Effects + io>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { f(x) }
        fn main() -> i64 ! {io, panic} { apply(inc, 41) }"#;
    assert_eq!(value(inferred), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(inferred, 42);
    let explicit = r#"
        fn inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn apply<e: Effects + (io | alloc) - suspend>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { f(x) }
        fn main() -> i64 ! {io, alloc, panic} { apply::<io | alloc | panic>(inc, 41) }"#;
    assert_eq!(value(explicit), 42);
    rejects(
        r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn apply<e: Effects + io>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { f(x) }
        fn main() -> i64 ! {panic} { apply(inc, 1) }"#,
        "requires effects {io}",
    );
    rejects(
        r#"
        fn inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn apply<e: Effects + alloc>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { f(x) }
        fn main() -> i64 ! {io, alloc, panic} { apply::<io | panic>(inc, 1) }"#,
        "required by '<e: Effects + alloc>'",
    );
    rejects(
        r#"
        fn apply<e: Effects + io - io>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e} { f(1) }
        fn main() -> i64 ! {panic} { 0 }"#,
        "both includes and excludes",
    );
    rejects(
        r#"
        #[noalloc]
        fn apply<e: Effects + alloc>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e} { f(1) }
        fn main() -> i64 ! {panic} { 0 }"#,
        "noalloc",
    );
}

#[test]
fn row_constraint_solver_rejects_ambiguity_and_exclusions() {
    rejects(
        r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn split<e1: Effects, e2: Effects>(f: fn(i64) -> i64 ! {e1, e2}, x: i64)
            -> i64 ! {panic, e1, e2} { f(x) }
        fn main() -> i64 ! {panic} { split(inc, 1) }"#,
        "incomparable minimal",
    );
    rejects(
        r#"
        fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn only<e: Effects - io>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, e} { f(x) }
        fn main() -> i64 ! {io, panic} { only(io_inc, 1) }"#,
        "is excluded by",
    );
}

// ---------------------------------------------------------------------------
// One-shot tail-resumptive effect handlers
// ---------------------------------------------------------------------------

#[test]
fn handler_resumes_once_and_returns_the_operation_result() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} {
                let r = resume(x + 1);
                r * 2
            } {
                let a = perform Op(20);
                a + 1
            }
        }"#;
    assert_eq!(value(source), 43);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 43);
}

#[test]
fn handlers_shadow_lexically_and_pure_handlers_serve_many_performs() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x + 1) } {
                let outer = perform Op(1);
                let inner = handle Op: i64 -> i64 with fn(
                    x: i64,
                    resume: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {panic} { resume(x + 10) } {
                    perform Op(2)
                };
                outer + inner
            }
        }"#;
    assert_eq!(value(source), 14);
}

#[test]
fn resumption_is_linear_and_cannot_be_duplicated_or_ignored() {
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} {
                let a = resume(x);
                let b = resume(x + 1);
                a + b
            } { perform Op(20) }
        }"#,
        "use after move",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { 0 } { perform Op(20) }
        }"#,
        "consumed",
    );
}

#[test]
fn owning_handler_payload_and_result_cleanup_once() {
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            handle Op: Box<i64> -> Box<i64> with fn(
                x: Box<i64>,
                resume: linear once fn(Box<i64>) -> Box<i64> ! {},
            ) -> Box<i64> ! {alloc, panic} {
                resume(x)
            } {
                let b = perform Op(Box.new(42));
                Box.take(b)
            }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn linear_values_survive_a_perform_without_duplication() {
    let source = r#"
        #[linear]
        struct Token { id: i64 }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 5 };
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let a = perform Op(1);
                let Token { id } = token;
                a + id
            }
        }"#;
    assert_eq!(value(source), 6);
}

#[test]
fn handler_effects_are_part_of_the_handle_contract() {
    let source = r#"
        fn main() -> Unit ! {io, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} {
                print_i64(x);
                resume(x + 1)
            } {
                print_i64(perform Op(41));
            }
        }"#;
    check(source).unwrap();
    rejects(
        r#"
        fn main() -> Unit ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} {
                print_i64(x);
                resume(x + 1)
            } { print_i64(perform Op(41)); }
        }"#,
        "requires effects {io}",
    );
}

#[test]
fn declared_effects_reach_handlers_through_called_functions() {
    let source = r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {panic} { perform Op(20) }
        fn call() -> i64 ! {panic} { deep() + 1 }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                call()
            }
        }"#;
    assert_eq!(value(source), 21);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 21);
    // A copyable noncapturing handler serves several performs from different
    // called functions.
    let many = r#"
        effect Op: i64 -> i64;
        fn a() -> i64 ! {panic} { perform Op(20) }
        fn b() -> i64 ! {panic} { perform Op(1) }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                a() + b() + 1
            }
        }"#;
    assert_eq!(value(many), 22);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(many, 22);
    // An early return leaves the handled body before the normal pop. The
    // function-entry depth restoration must make the next perform handlerless.
    let loop_restore = r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {panic} {
            let mut i = 0;
            let mut sum = 0;
            while i < 2 {
                handle Op: i64 -> i64 with fn(
                    x: i64,
                    resume: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {} { resume(x) } {
                    if i == 0 {
                        i = i + 1;
                        continue;
                    }
                    sum = sum + perform Op(1);
                }
                i = i + 1;
            }
            sum + i
        }"#;
    assert_eq!(value(loop_restore), 3);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(loop_restore, 3);
    let restored = r#"
        effect Op: i64 -> i64;
        fn scoped() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                return perform Op(1);
            }
        }
        fn main() -> i64 ! {panic} {
            let x = scoped();
            perform Op(2) + x
        }"#;
    let program = check(restored).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("no dynamically active handler"),
        "{error:?}"
    );
    rejects(
        r#"
        effect Op: i64 -> i64;
        effect Op: Bool -> Bool;
        fn main() -> i64 ! {panic} { 0 }"#,
        "duplicate or reserved declaration",
    );
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {io, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} { print_i64(x); resume(x) } {
                perform Op(1)
            }
        }"#,
        "dynamically visible handler must be pure",
    );
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {alloc, panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x + n) } {
                perform Op(1)
            }
        }"#,
        "noncapturing 'fn' value",
    );
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {panic} {
            handle Op: Bool -> i64 with fn(
                x: Bool,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(1) } {
                perform Op(1)
            }
        }"#,
        "declared operation signature",
    );
}

#[test]
fn performs_require_a_lexical_handler_and_a_exact_resume_contract() {
    rejects(
        "fn main() -> i64 ! {panic} { perform Op(1) }",
        "no lexically enclosing handler",
    );
    rejects(
        r#"
        fn call() -> i64 ! {panic} { perform Op(1) }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } { call() }
        }"#,
        "no lexically enclosing handler",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let f: once fn() -> i64 ! {alloc, panic} =
                    fn() -> i64 ! {alloc, panic} { perform Op(1) };
                f()
            }
        }"#,
        "no lexically enclosing handler",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } { perform Op(1) }
        }"#,
        "second parameter must be exactly",
    );
}

// ---------------------------------------------------------------------------
// Versioned runtime-dependent proofs
// ---------------------------------------------------------------------------

#[test]
fn mutable_scalar_locals_index_erased_proofs_at_their_current_version() {
    let source = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 5;
            let a = keep(n, refl::<i64>(n));
            n = 7;
            let b = keep(n, refl::<i64>(n));
            a + b
        }"#;
    assert_eq!(value(source), 12);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 12);
}

#[test]
fn total_logical_evidence_is_independent_and_versioned() {
    let source = r#"
        total fn same_i64(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(n) }
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 5;
            let a = keep(n, same_i64(n));
            n = 7;
            let b = keep(n, same_i64(n));
            a + b
        }"#;
    assert_eq!(value(source), 12);
}

#[test]
fn an_old_value_proof_cannot_be_reused_after_a_write() {
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 5;
            let a = keep(n, refl::<i64>(n));
            n = 6;
            a + keep(n, refl::<i64>(5))
        }"#,
        "proof does not establish",
    );
}

#[test]
fn scalar_aliases_keep_the_copied_kernel_index_and_freeze_before_mutation() {
    let source = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n: i64 = 5;
            let m = n;
            keep(n, refl::<i64>(m)) + keep(m, refl::<i64>(n))
        }"#;
    assert_eq!(value(source), 10);
    let frozen = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n: i64 = 5;
            let m = n;
            n = 6;
            keep(m, refl::<i64>(m)) + n
        }"#;
    assert_eq!(value(frozen), 11);
    // The alias froze at the old version, so it cannot prove a proposition
    // about the newly assigned source value.
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n: i64 = 5;
            let m = n;
            n = 6;
            keep(n, refl::<i64>(m))
        }"#,
        "proof does not establish",
    );
    // Chained aliases resolve to the original binder rather than stacking
    // fresh unconstrained indices.
    let chained = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n: i64 = 4;
            let a = n;
            let b = a;
            keep(n, refl::<i64>(b))
        }"#;
    assert_eq!(value(chained), 4);
}

#[test]
fn proof_parameters_survive_unrelated_versioned_binders() {
    let source = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn outer(n: i64, erased p: Eq<i64, n, n>) -> i64 ! {panic} {
            let mut x = 3;
            x = 4;
            keep(n, p) + x
        }
        fn main() -> i64 ! {panic} { outer(5, refl::<i64>(5)) }"#;
    assert_eq!(value(source), 9);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 9);
}

#[test]
fn mutable_scalar_capture_is_a_frozen_independent_snapshot() {
    // The closure copies the runtime scalar when it is constructed. Its proof
    // is about that independent snapshot, not a later value of the mutable
    // binding, so the write after capture is sound.
    let source = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 5;
            let f = fn() -> i64 ! {alloc, panic} { keep(n, refl::<i64>(n)) };
            n = 6;
            f() + n
        }"#;
    assert_eq!(value(source), 11);
}

// ---------------------------------------------------------------------------
// Runtime-sized inline arrays
// ---------------------------------------------------------------------------

#[test]
fn runtime_sized_inline_arrays_push_grow_and_read() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = DynArray.new::<i64, 4>();
            let mut i = 0;
            while i < 3 {
                a = DynArray.push(a, i * 10);
                i = i + 1;
            }
            DynArray.len(&a) + DynArray.get(&a, 0) + DynArray.get(&a, 2)
        }"#;
    assert_eq!(value(source), 23);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 23);
}

#[test]
fn runtime_sized_arrays_drop_only_the_initialized_owning_prefix() {
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 3> = DynArray.new::<Box<i64>, 3>();
            let a = DynArray.push(a, Box.new(1));
            let a = DynArray.push(a, Box.new(2));
            DynArray.len(&a)
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 2);
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 2);
}

#[test]
fn runtime_sized_arrays_check_capacity_and_bounds_at_runtime() {
    let overflow = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 1> = DynArray.new::<i64, 1>();
            let a = DynArray.push(a, 1);
            let a = DynArray.push(a, 2);
            DynArray.len(&a)
        }"#;
    let program = check(overflow).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("capacity exceeded"), "{error:?}");
    let bounds = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 2> = DynArray.new::<i64, 2>();
            let a = DynArray.push(a, 1);
            DynArray.get(&a, 1)
        }"#;
    let program = check(bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("index out of bounds"), "{error:?}");
}

#[test]
fn runtime_sized_arrays_set_and_pop_copyable_slots() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = DynArray.new::<i64, 4>();
            let a = DynArray.push(a, 1);
            let a = DynArray.push(a, 2);
            let a = DynArray.push(a, 3);
            let a = DynArray.set(a, 1, 40);
            let (a, last) = DynArray.pop(a);
            DynArray.len(&a) + DynArray.get(&a, 0) + DynArray.get(&a, 1) + last
        }"#;
    assert_eq!(value(source), 46);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 46);
    // Popping back to empty is checked, not a sentinel value.
    let drained = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 2> = DynArray.new::<i64, 2>();
            let a = DynArray.push(a, 7);
            let (a, x) = DynArray.pop(a);
            let (a, y) = DynArray.pop(a);
            DynArray.len(&a) + x + y
        }"#;
    let program = check(drained).unwrap();
    assert!(program.evaluate(&mut Vec::new()).is_err());
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 2> = DynArray.new();
            let a = DynArray.push(a, Box.new(1));
            let (a, _) = DynArray.pop(a);
            DynArray.len(&a)
        }"#,
        "owning, linear, and view elements",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 2> = DynArray.new();
            let a = DynArray.push(a, Box.new(1));
            let a = DynArray.set(a, 0, Box.new(2));
            DynArray.len(&a)
        }"#,
        "owning, linear, and view elements",
    );
    let out_of_bounds = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 2> = DynArray.new::<i64, 2>();
            let a = DynArray.push(a, 1);
            let a = DynArray.set(a, 1, 2);
            DynArray.len(&a)
        }"#;
    let program = check(out_of_bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("index out of bounds"), "{error:?}");
}

#[test]
fn runtime_sized_array_layout_contracts_are_checked() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} { let a: DynArray<i64, 32> = DynArray.new(); 0 }",
        "capacity must be 1..31",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: DynArray<i64, 0> = DynArray.new(); 0 }",
        "capacity must be 1..31",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 2] = [1, 2];
            let a: DynArray<&mut [i64], 1> = DynArray.new();
            0
        }"#,
        "non-borrowed",
    );
}

// ---------------------------------------------------------------------------
// Structural records
// ---------------------------------------------------------------------------

#[test]
fn structural_width_coercion_reorders_and_drops_affine_fields() {
    // The target row is canonical (sorted), so the source declaration order is
    // irrelevant. `extra: Box<i64>` is absent from the target and must be
    // dropped exactly once by the checked conversion.
    let source = r#"
        struct Wide { b: i64, a: i64, extra: Box<i64> }
        fn sum(v: struct { a: i64, b: i64 }) -> i64 ! {panic} { v.a + v.b }
        fn main() -> i64 ! {alloc, panic} {
            let w = Wide { b: 20, a: 22, extra: Box.new(1) };
            sum(w)
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn structural_alias_and_parameter_share_the_canonical_row() {
    let source = r#"
        struct Point { x: i64, y: i64, tag: Bool }
        type Pair = struct { y: i64, x: i64 };
        fn read(p: Pair) -> i64 ! {panic} { p.x - p.y }
        fn main() -> i64 ! {panic} {
            read(Point { x: 42, y: 0, tag: true })
        }"#;
    assert_eq!(value(source), 42);
}

#[test]
fn structural_missing_field_and_changed_borrowed_leaf_are_rejected() {
    rejects(
        r#"
        struct Point { x: i64 }
        fn read(p: struct { x: i64, y: i64 }) -> i64 ! {panic} { p.x + p.y }
        fn main() -> i64 ! {panic} { read(Point { x: 1 }) }"#,
        "no field 'y'",
    );
    rejects(
        r#"
        struct Window<'a> { view: &'a mut [i64], n: i64 }
        fn keep<'a>(w: struct { view: &'a [i64], n: i64 }) -> i64 ! {} { w.n }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            keep(Window { view: &mut a[..], n: 1 })
        }"#,
        "cannot convert field 'view'",
    );
}

#[test]
fn structural_width_cannot_erase_a_linear_field() {
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        struct Wide { a: i64, token: Token }
        fn read(v: struct { a: i64 }) -> i64 ! {panic} { v.a }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 1 };
            read(Wide { a: 1, token: token })
        }"#,
        "linear obligation",
    );
}

#[test]
fn structural_nested_width_and_field_union_injection_coerce() {
    let source = r#"
        struct Inner { x: i64, extra: Box<i64> }
        struct Outer { inner: Inner, tag: i64 }
        fn read(v: struct { inner: struct { x: i64 }, tag: i64 | Bool }) -> i64 ! {panic} {
            match v.tag {
                i64 @ n => v.inner.x + n,
                Bool @ _ => 0,
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            read(Outer { inner: Inner { x: 40, extra: Box.new(1) }, tag: 2 })
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    let nested_union = r#"
        struct Inner { v: i64 | Bool }
        struct Outer { inner: Inner }
        fn read(v: struct { inner: struct { v: i64 | Bool | Unit } }) -> i64 ! {panic} {
            match v.inner.v {
                i64 @ n => n,
                Bool @ _ => 0,
                Unit @ _ => 0,
            }
        }
        fn main() -> i64 ! {panic} { read(Outer { inner: Inner { v: 40 } }) + 2 }"#;
    assert_eq!(value(nested_union), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(nested_union, 42);
}

#[test]
fn structural_record_literals_and_generic_patterns_share_the_canonical_row() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let r = struct { b: 2, a: 40 };
            let n = match r {
                struct { a, b } => a + b,
            };
            let s: struct { b: i64, a: i64 } = struct { a: n, b: 0 };
            match s {
                struct { a, .. } => a,
            }
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // A literal is a real source row: width coercion drops extra fields and a
    // retained atom may still be injected into a union field.
    let coercing = r#"
        fn main() -> i64 ! {alloc, panic} {
            let wide = struct { extra: Box.new(1), a: 41, tag: true };
            let narrow: struct { a: i64 | Bool } = wide;
            match narrow.a {
                i64 @ n => n + 1,
                Bool @ _ => 0,
            }
        }"#;
    let (result, stats) = evaluate(coercing);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(coercing, 42);
    // A structural pattern may narrow a union when exactly one alternative has
    // all named fields.
    let narrowed = r#"
        struct A { left: i64, right: i64 }
        struct B { flag: Bool }
        fn main() -> i64 ! {panic} {
            let value: A | B = A { left: 20, right: 22 };
            match value {
                struct { left, right } => left + right,
                B { flag } => if flag { 1 } else { 0 },
            }
        }"#;
    assert_eq!(value(narrowed), 42);
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let r = struct { a: 1 };
            match r { struct { missing } => missing }
        }"#,
        "no field 'missing'",
    );
}

#[test]
fn structural_callable_field_adapts_arrow_representation() {
    // A retained field of pure function type is converted to a `once` arrow.
    // The calling convention changes (an environment word appears), so the
    // structural conversion must generate a checked adapter instead of copying
    // the code pointer.
    let source = r#"
        fn widen(value: i64 | Bool) -> i64 ! {panic} {
            match value { i64 @ n => n, Bool @ _ => 0 }
        }
        struct Holder { f: fn(i64 | Bool) -> i64 ! {panic}, tag: Bool }
        fn call(v: struct { f: once fn(i64) -> i64 ! {panic} }) -> i64 ! {panic} {
            let struct { f } = v;
            f(21) * 2
        }
        fn main() -> i64 ! {alloc, panic} {
            call(Holder { f: widen, tag: true })
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // A pure-to-pure conversion that changes a parameter representation cannot
    // capture the dynamic code pointer in a pure arrow, so it stays rejected.
    rejects(
        r#"
        fn both(value: i64 | Bool) -> i64 ! {panic} {
            match value { i64 @ n => n, Bool @ _ => 0 }
        }
        struct Holder { f: fn(i64 | Bool) -> i64 ! {panic} }
        fn read(v: struct { f: fn(i64) -> i64 ! {panic} }) -> i64 ! {panic} { v.f(42) }
        fn main() -> i64 ! {panic} { read(Holder { f: both }) }"#,
        "pure function has no environment",
    );
}

#[test]
fn structural_callable_field_preserves_borrow_and_linear_obligations() {
    // A callable field cannot be mixed into a borrowed record, so the
    // callable adapter cannot hide a borrowed leaf behind its environment. The
    // ordinary structural borrow-provenance tests cover reordered view fields;
    // this hostile case keeps the callable path from weakening that rule.
    rejects(
        r#"struct Window<'a> { start: i64, view: &'a [i64], f: fn(i64) -> i64 ! {panic} }
        fn noop(n: i64) -> i64 ! {panic} { n }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [40];
            let w = Window { start: 0, view: &data[..], f: noop };
            let narrow: struct { f: once fn(i64) -> i64 ! {panic}, view: &[i64] } = w;
            match narrow { struct { view, .. } => { data = [9]; Slice.get(view, 0) } }
        }"#,
        "mixed borrowed record",
    );
    // A captured linear callable is moved into the adapter environment exactly
    // once. Calling the converted field consumes it and releases the
    // environment exactly once.
    let source = r#"
        fn widen(value: i64 | Bool) -> i64 ! {panic} {
            match value { i64 @ n => n, Bool @ _ => 0 }
        }
        struct Holder { f: linear once fn(i64 | Bool) -> i64 ! {panic}, tag: Bool }
        fn call(v: struct { f: linear once fn(i64) -> i64 ! {panic} }) -> i64 ! {alloc, panic} {
            let struct { f } = v;
            f(42)
        }
        fn main() -> i64 ! {alloc, panic} {
            let make: linear once fn(i64 | Bool) -> i64 ! {panic} =
                fn(value: i64 | Bool) -> i64 ! {panic} { widen(value) };
            call(Holder { f: make, tag: true })
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert!(stats.allocations == stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // A linear callable retained by the conversion still imposes its
    // obligation: the converted record cannot simply be discarded.
    rejects(
        r#"fn noop(n: i64) -> i64 ! {panic} { n }
        struct Holder { f: linear once fn(i64) -> i64 ! {panic} }
        fn main() -> i64 ! {alloc, panic} {
            let f: linear once fn(i64) -> i64 ! {panic} =
                fn(n: i64) -> i64 ! {panic} { noop(n) };
            let h = Holder { f: f };
            let narrow: struct { f: linear once fn(i64) -> i64 ! {panic} } = h;
            drop(narrow);
            0
        }"#,
        "linear",
    );
}

#[test]
fn structural_borrowed_field_transfer_keeps_cleanup_balanced() {
    let source = r#"
        struct View<'a> { view: &'a mut [i64], n: i64, extra: Box<i64> }
        fn keep<'a>(v: struct { n: i64, view: &'a mut [i64] }) -> i64 ! {} { v.n }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            keep(View { view: &mut a[..], n: 42, extra: Box.new(1) })
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn open_row_parameters_accept_records_with_the_named_fields() {
    // `..` is an erased open-row contract: the callee sees exactly the named
    // fields in canonical order and unmentioned fields are dropped once at the
    // call boundary. It is width subtyping with an explicit spelling, not row
    // unification that preserves the extra fields.
    let source = r#"
        struct Wide { flag: Bool, x: i64, extra: Box<i64> }
        fn read(v: struct { x: i64, .. }) -> i64 ! {panic} { v.x }
        fn main() -> i64 ! {alloc, panic} {
            read(Wide { flag: true, x: 42, extra: Box.new(1) })
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // An open row still requires every named field.
    rejects(
        r#"
        struct Point { y: i64 }
        fn read(v: struct { x: i64, .. }) -> i64 ! {panic} { v.x }
        fn main() -> i64 ! {panic} { read(Point { y: 1 }) }"#,
        "no field 'x'",
    );
    // Erasing an extra linear field is not allowed: the target cannot consume
    // it, exactly as for a closed width conversion.
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        struct Wide { x: i64, token: Token }
        fn read(v: struct { x: i64, .. }) -> i64 ! {panic} { v.x }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 1 };
            read(Wide { x: 1, token: token })
        }"#,
        "linear obligation",
    );
    // Impl headers match one exact canonical row; an open row there would make
    // dispatch depend on width compatibility, so it stays rejected.
    rejects(
        r#"
        impl struct { x: i64, .. } {
            fn read_x(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "open row",
    );
}

#[test]
fn structural_records_are_impl_receivers() {
    // A concrete structural row is a first-class impl receiver. The nominal
    // record is coerced once to the canonical structural row and dispatch then
    // uses that row's type identity.
    let source = r#"
        impl struct { x: i64, y: i64 } {
            fn sum(self: Self) -> i64 ! {panic} { self.x + self.y }
        }
        struct Point { x: i64, y: i64, tag: Bool }
        fn main() -> i64 ! {panic} {
            let p: struct { x: i64, y: i64 } = Point { x: 20, y: 22, tag: true };
            p.sum()
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // An inherent impl may take a borrowed receiver of the structural row.
    let borrowed = r#"
        impl struct { x: i64 } {
            fn twice(self: &Self) -> i64 ! {panic} { self.x * 2 }
        }
        fn main() -> i64 ! {panic} {
            let r: struct { x: i64 } = struct { x: 21 };
            r.twice()
        }"#;
    assert_eq!(value(borrowed), 42);
    // A generic structural header binds its parameter from the canonical row.
    let generic = r#"
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<T> Tag for struct { value: T } {
            fn tag(self: Self) -> i64 ! {panic} { 42 }
        }
        fn main() -> i64 ! {panic} {
            let r: struct { value: Bool } = struct { value: true };
            r.tag()
        }"#;
    assert_eq!(value(generic), 42);
    // Two headers for the same canonical row are not specializing: they
    // overlap exactly and remain a duplicate-implementation error.
    rejects(
        r#"
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl Tag for struct { value: i64 } { fn tag(self: Self) -> i64 ! {panic} { 1 } }
        impl Tag for struct { value: i64 } { fn tag(self: Self) -> i64 ! {panic} { 2 } }
        fn main() -> i64 ! {panic} { 0 }"#,
        "duplicate implementation",
    );
    // Structural and nominal impls of the same trait stay disjoint: a
    // structural header never matches a nominal record implicitly.
    let disjoint = r#"
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        struct Point { x: i64 }
        impl Tag for Point { fn tag(self: Self) -> i64 ! {panic} { 40 } }
        impl Tag for struct { x: i64 } { fn tag(self: Self) -> i64 ! {panic} { 42 } }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 1 };
            let s: struct { x: i64 } = struct { x: 2 };
            let a = p.tag();
            let b = s.tag();
            if a == 40 { b } else { 0 }
        }"#;
    assert_eq!(value(disjoint), 42);
}

#[test]
fn dynamically_resolved_perform_requires_panic() {
    // With no active handler the program aborts, so an empty row cannot
    // perform a declared operation outside a lexical handler.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn pure() -> i64 ! {} { perform Op(20) }
        fn main() -> i64 ! {} { pure() }"#,
        "requires effects {panic}",
    );
}
