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
fn union_patterns_partition_multiple_variables_principally() {
    // `T | U | i64` over `Bool | Unit | i64` leaves the residual `Bool | Unit`.
    // Both T=Bool,U=Unit and T=Unit,U=Bool fit, and the body can tell them
    // apart, so inference reports the ambiguity instead of choosing one.
    let three = r#"
        fn three(c: i64) -> Bool | Unit | i64 ! {panic} {
            if c == 0 { true } else { if c == 1 { () } else { 41 } }
        }"#;
    rejects(
        &format!(
            "{three}
            fn pick<T, U>(x: T | U | i64) -> i64 ! {{panic}} {{
                match x {{ i64 @ n => n, T @ _ => 1, U @ _ => 2 }}
            }}
            fn main() -> i64 ! {{panic}} {{ pick(three(0)) }}"
        ),
        "type inference for 'pick' is ambiguous: the union alternatives can be split as [T = Bool, U = Unit] or [T = Unit, U = Bool]",
    );
    // An explicit specialization is the escape hatch.
    let source = format!(
        "{three}
        fn pick<T, U>(x: T | U | i64) -> i64 ! {{panic}} {{
            match x {{ i64 @ n => n, T @ _ => 1, U @ _ => 42 }}
        }}
        fn main() -> i64 ! {{panic}} {{ pick::<Unit, Bool>(three(0)) }}"
    );
    assert_eq!(value(&source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 42);
    // Cross-parameter backtracking: the first canonical partition is
    // T=Bool, U=Unit, but the second parameter requires T=Unit. The bounded
    // replay reruns the whole constraint group and selects T=Unit, U=Bool.
    let replayed = r#"
        fn pick<T, U>(x: T | U | i64, first: T) -> i64 ! {panic} { 0 }
        fn two(c: i64) -> Bool | Unit ! {panic} {
            if c == 0 { true } else { () }
        }
        fn main() -> i64 ! {panic} { pick(two(0), ()) }"#;
    assert_eq!(value(replayed), 0);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(replayed, 0);
    // No partition can satisfy both parameters here: the residual can only
    // bind T to Bool or Unit, never to i64.
    rejects(
        r#"
        fn pick<T, U>(x: T | U | i64, first: T) -> i64 ! {panic} { 0 }
        fn two(c: i64) -> Bool | Unit ! {panic} {
            if c == 0 { true } else { () }
        }
        fn main() -> i64 ! {panic} { pick(two(0), 1) }"#,
        "no partition",
    );
    // A single residual alternative cannot bind two unbound variables.
    rejects(
        r#"
        fn pick<T, U>(x: T | U | i64) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} { pick(true) }"#,
        "no partition binds every variable",
    );
}

#[test]
fn call_site_constraints_decide_a_deferred_partition() {
    // The partition is not committed by the union argument alone: the
    // expected result type and a callable argument each leave one solution.
    let source = r#"
        enum Option<T> { None, Some(T) }
        fn three(c: i64) -> Bool | Unit | i64 ! {panic} {
            if c == 0 { true } else { if c == 1 { () } else { 41 } }
        }
        fn tag<T, U>(x: T | U | i64) -> Option<T> ! {panic} {
            match x { T @ t => Option.Some(t), _ => Option.None }
        }
        fn wrap<T, U>(x: T | U | i64, f: fn(T) -> i64 ! {}) -> i64 ! {panic} {
            match x { T @ t => f(t), _ => 7 }
        }
        fn score(b: Bool) -> i64 ! {} { if b { 40 } else { 1 } }
        fn main() -> i64 ! {panic} {
            let r: Option<Unit> = tag(three(1));
            let k = match r { Option.Some(_) => 2, Option.None => 0 };
            k + wrap(three(0), score)
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // Without the expected type the same call is ambiguous.
    rejects(
        r#"
        enum Option<T> { None, Some(T) }
        fn three(c: i64) -> Bool | Unit | i64 ! {panic} {
            if c == 0 { true } else { if c == 1 { () } else { 41 } }
        }
        fn tag<T, U>(x: T | U | i64) -> Option<T> ! {panic} {
            match x { T @ t => Option.Some(t), _ => Option.None }
        }
        fn main() -> i64 ! {panic} {
            let r = tag(three(1));
            match r { Option.Some(_) => 2, Option.None => 0 }
        }"#,
        "is ambiguous",
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

#[test]
fn indexed_union_patterns_assign_members_per_constructor() {
    // Each actual member goes to one constructor alternative; T and U are
    // solved separately instead of being merged into one Option<...>.
    let source = r#"
        enum Option<T> { None, Some(T) }
        fn get<T>(x: Option<T> | i64, d: T) -> T ! {panic} {
            match x {
                i64 @ _ => d,
                Option<T> @ o => match o { Option.Some(v) => v, Option.None => d },
            }
        }
        fn sz<T, U>(x: Vec<T> | Vec<U> | i64, t: T) -> i64 ! {panic} {
            match x { i64 @ n => n, Vec<T> @ v => Vec.len(&v), Vec<U> @ v => 100 + Vec.len(&v) }
        }
        fn make(c: i64) -> Vec<i64> | Vec<Bool> | i64 ! {alloc, panic} {
            if c == 0 { let v: Vec<i64> = [1, 2]; v }
            else { if c == 1 { let v: Vec<Bool> = [true]; v } else { 7 } }
        }
        fn main() -> i64 ! {alloc, panic} {
            let a: Option<i64> | i64 = 4;
            let b: Option<i64> | i64 = Option.Some(40);
            get(a, 2) + get(b, 0) + sz(make(0), 0) + sz(make(1), 0) + sz(make(2), 0) - 110
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn indexed_union_patterns_cover_every_constructor_shape() {
    let source = r#"
        enum Option<T> { None, Some(T) }
        struct Pair<A, B> { a: A, b: B }
        fn one<T, U>(x: T | Option<U>, u: U) -> i64 ! {panic} {
            match x { Option<U> @ _ => 1, T @ _ => 2 }
        }
        fn arr<T, U, N: Nat, M: Nat>(x: [T; N] | [U; M], t: T) -> i64 ! {panic} {
            match x { [T; N] @ _ => 2, [U; M] @ _ => 30 }
        }
        fn tup<T>(x: (T, i64) | Bool) -> i64 ! {panic} {
            match x { Bool @ _ => 0, (T, i64) @ (_, k) => k }
        }
        fn single<T>(x: Option<T> | i64) -> i64 ! {panic} { match x { i64 @ n => n, _ => 3 } }
        fn nest<T>(x: Option<Vec<T>> | i64) -> i64 ! {panic} {
            match x { i64 @ n => n, Option<Vec<T>> @ _ => 4 }
        }
        fn rec<A, B>(x: Pair<A, i64> | Pair<B, Bool>) -> i64 ! {panic} {
            match x { Pair<A, i64> @ p => p.b, Pair<B, Bool> @ _ => 5 }
        }
        fn main() -> i64 ! {alloc, panic} {
            let x: Bool | Option<i64> = Option.Some(3);
            let y: [i64; 2] | [Bool; 3] = [true, false, true];
            let z: (Bool, i64) | Bool = (true, 6);
            let s: Option<Bool> = Option.Some(true);
            let w: Option<Vec<Bool>> | i64 = 0;
            let q: Pair<Bool, i64> = Pair { a: true, b: 7 };
            let p: Pair<Bool, i64> | Pair<i64, Bool> = q;
            one(x, 1) + arr(y, 0) + tup(z) + single(s) + nest(w) + rec(p)
        }"#;
    // `T | Option<U>` keeps Option<i64> with the constructor alternative (1),
    // `t` fixes T = i64 so the [Bool; 3] member binds U and M (30), and a
    // single non-union actual
    // still picks its constructor alternative (3).
    assert_eq!(value(source), 47);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 47);
}

#[test]
fn indexed_union_assignments_are_unique_or_ambiguous() {
    // The first canonical assignment gives T the i64 member, but the second
    // parameter needs T=Bool, so the bounded replay swaps the assignment.
    let replayed = r#"
        enum Option<T> { None, Some(T) }
        fn pick<T, U>(x: Option<T> | Option<U>, t: T) -> i64 ! {panic} {
            match x { Option<T> @ _ => 10, Option<U> @ _ => 20 }
        }
        fn make(c: Bool) -> Option<i64> | Option<Bool> ! {panic} {
            if c { let o: Option<i64> = Option.Some(1); o }
            else { let o: Option<Bool> = Option.Some(true); o }
        }
        fn main() -> i64 ! {panic} { pick(make(true), true) + pick(make(false), 5) + 2 }"#;
    assert_eq!(value(replayed), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(replayed, 42);
    // Without the deciding parameter, both assignments fit in either operand
    // order, so the call is ambiguous rather than ordered by declaration.
    let ordered = |pattern: &str, decider: &str, call: &str| {
        format!(
            "enum Option<T> {{ None, Some(T) }}
            fn pick<T, U>(x: {pattern}{decider}) -> i64 ! {{panic}} {{
                match x {{ Option<T> @ _ => 1, Option<U> @ _ => 2 }}
            }}
            fn main() -> i64 ! {{panic}} {{
                let o: Option<Bool> = Option.Some(true);
                let x: Option<i64> | Option<Bool> = o;
                {call}
            }}"
        )
    };
    for pattern in ["Option<T> | Option<U>", "Option<U> | Option<T>"] {
        assert_eq!(value(&ordered(pattern, ", u: U", "pick(x, true)")), 2);
        assert_eq!(value(&ordered(pattern, "", "pick::<Bool, i64>(x)")), 1);
        rejects(&ordered(pattern, "", "pick(x)"), "is ambiguous");
    }
}

#[test]
fn indexed_union_patterns_never_merge_invariant_arguments() {
    // One constructor alternative cannot cover Vec<i64> and Vec<Bool>: that
    // would need the unsound Vec<i64 | Bool>.
    rejects(
        r#"
        fn sz<T>(x: Vec<T> | i64) -> i64 ! {panic} { 0 }
        fn make(c: i64) -> Vec<i64> | Vec<Bool> | i64 ! {alloc, panic} {
            if c == 0 { let v: Vec<i64> = [1, 2]; v }
            else { if c == 1 { let v: Vec<Bool> = [true]; v } else { 7 } }
        }
        fn main() -> i64 ! {alloc, panic} { sz(make(0)) }"#,
        "never merged into one Option<...>",
    );
    rejects(
        r#"
        enum Option<T> { None, Some(T) }
        struct Pair<A, B> { a: A, b: B }
        fn rec<A>(x: Pair<A, i64> | Pair<A, Bool>) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} {
            let q: Pair<Bool, i64> = Pair { a: true, b: 7 };
            let p: Pair<Bool, i64> | Pair<i64, Bool> = q;
            rec(p)
        }"#,
        "no assignment of the alternatives",
    );
    // A member that fits a constructor alternative never goes to a bare
    // variable, so with only Option<i64> the bare T has nothing to bind.
    rejects(
        r#"
        enum Option<T> { None, Some(T) }
        fn pick<T, U>(x: T | Option<U>) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} { let o: Option<i64> = Option.None; pick(o) }"#,
        "every bare variable needs at least one alternative",
    );
    // Symmetric constructor alternatives with nothing else to decide them.
    rejects(
        r#"
        fn sz<T, U>(x: Vec<T> | Vec<U> | i64) -> i64 ! {panic} { 0 }
        fn make(c: i64) -> Vec<i64> | Vec<Bool> | i64 ! {alloc, panic} {
            if c == 0 { let v: Vec<i64> = [1, 2]; v }
            else { if c == 1 { let v: Vec<Bool> = [true]; v } else { 7 } }
        }
        fn main() -> i64 ! {alloc, panic} { sz(make(0)) }"#,
        "type inference for 'sz' is ambiguous",
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
// One-shot effect handlers
// ---------------------------------------------------------------------------

#[test]
fn handler_resumes_nonlinearly_and_returns_the_continuation_result() {
    // `resume(x + 1)` runs the rest of the handled body (`a + 1`) and returns
    // its result 22 to the handler, which then computes 44.
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
    assert_eq!(value(source), 44);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 44);
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
    // A resumption token cannot escape into a container that might drop or
    // copy the continuation.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {alloc, panic} {
                let v: Vec<linear once fn(i64) -> i64 ! {}> = Vec.new();
                let v = Vec.push(v, resume);
                Vec.len(&v)
            } { let a = perform Op(20); a }
        }"#,
        "vectors cannot hold linear values",
    );
}

#[test]
fn owning_handler_payload_and_result_cleanup_once() {
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            Box.take(handle Op: Box<i64> -> Box<i64> with fn(
                x: Box<i64>,
                resume: linear once fn(Box<i64>) -> Box<i64> ! {},
            ) -> Box<i64> ! {alloc, panic} {
                resume(x)
            } {
                let b = perform Op(Box.new(42));
                b
            })
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
    // The continuation owns the linear token after the perform, so building its
    // environment requires `alloc`.
    let source = r#"
        #[linear]
        struct Token { id: i64 }
        fn main() -> i64 ! {alloc, panic} {
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
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 6);
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
                let a = perform Op(41);
                print_i64(a);
                a
            };
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
            } {
                let a = perform Op(41);
                print_i64(a);
                a
            };
        }"#,
        "requires effects {io}",
    );
}

#[test]
fn declared_effects_reach_handlers_through_called_functions() {
    let source = r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn call() -> i64 ! {Op, panic} { deep() + 1 }
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
        fn a() -> i64 ! {Op, panic} { perform Op(20) }
        fn b() -> i64 ! {Op, panic} { perform Op(1) }
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
    // An early continue leaves the handled body before the normal pop. The
    // function-entry depth restoration must make the next perform handlerless.
    let loop_restore = r#"
        effect Op: i64 -> i64;
        fn next() -> i64 ! {Op, panic} { perform Op(1) }
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
                    sum = sum + next();
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
        fn next() -> i64 ! {Op, panic} { perform Op(1) }
        fn scoped() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                return next();
            }
        }
        fn main() -> i64 ! {Op, panic} {
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
        "dynamically visible handler must be pure",
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
fn capturing_dynamic_handlers_own_their_environment() {
    // A pure once handler may capture copyable values. The frame owns its
    // environment, the first dynamic perform consumes it, and the callee frees
    // the environment exactly once.
    let source = r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn main() -> i64 ! {alloc, panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(n) } {
                deep()
            }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 1);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 1);

    // A capturing handler that is never performed is dropped when its lexical
    // frame pops.
    let unused = r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {alloc, panic} {
            let n = 1;
            let r = handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(n) } {
                5
            };
            r + n
        }"#;
    let (result, stats) = evaluate(unused);
    assert_eq!(result, 6);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(unused, 6);

    // Early return crosses the dynamic frame boundary. The function epilogue
    // must drop the unconsumed owning handler exactly once.
    let early = r#"
        effect Op: i64 -> i64;
        fn scoped() -> i64 ! {alloc, panic} {
            let n = 5;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(n) } {
                return n;
            }
        }
        fn main() -> i64 ! {alloc, panic} { scoped() }"#;
    let (result, stats) = evaluate(early);
    assert_eq!(result, 5);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(early, 5);
}

#[test]
fn a_once_dynamic_handler_is_consumed_by_its_first_perform() {
    // The first called function consumes the single owning environment. A
    // second perform finds no active copyable frame and aborts rather than
    // reusing freed state.
    let source = r#"
        effect Op: i64 -> i64;
        fn a() -> i64 ! {Op, panic} { perform Op(1) }
        fn b() -> i64 ! {Op, panic} { perform Op(2) }
        fn main() -> i64 ! {alloc, panic} {
            let n = 10;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(n) } {
                a() + b()
            }
        }"#;
    let program = check(source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("no dynamically active handler"),
        "{error:?}"
    );
}

#[test]
fn tasks_inherit_copyable_dynamic_frames_with_isolated_extents() {
    // A copyable noncapturing handler frame crosses a structured task spawn,
    // so a child can resolve the operation its parent installed.
    let inherited = r#"
        use std.task.TaskExit;
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(10) }
        fn main() -> i64 ! {suspend, alloc, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                Task.scope(fn() -> i64 ! {suspend, alloc, Op, panic} {
                    let t: Task<i64> = Task.spawn(fn() -> i64 ! {Op, panic} { deep() });
                    match Task.join(t) {
                        TaskExit.Completed(v) => v,
                        TaskExit.Cancelled => 0,
                    }
                })
            }
        }"#;
    assert_eq!(value(inherited), 10);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(inherited, 10);

    // A capturing once frame is a task boundary: its owned environment is not
    // shared with the child, so the child cannot resolve the operation.
    let isolated = r#"
        use std.task.TaskExit;
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(10) }
        fn main() -> i64 ! {suspend, alloc, panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(n) } {
                Task.scope(fn() -> i64 ! {suspend, alloc, Op, panic} {
                    let t: Task<i64> = Task.spawn(fn() -> i64 ! {Op, panic} { deep() });
                    match Task.join(t) {
                        TaskExit.Completed(v) => v,
                        TaskExit.Cancelled => 0,
                    }
                })
            }
        }"#;
    let program = check(isolated).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("no dynamically active handler"),
        "{error:?}"
    );
}

#[test]
fn declared_effect_names_are_checked_row_entries() {
    // A declared operation contributes a row bit. A function that performs it
    // dynamically must list it, and a lexical handle discharges it for the
    // body while still requiring the handler's own effects.
    let source = r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn call() -> i64 ! {Op, panic} { deep() + 1 }
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
    // Omitting the declared row entry is an ordinary effect-row error.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {panic} { perform Op(20) }
        fn main() -> i64 ! {panic} { deep() }"#,
        "requires effects {Op}",
    );
    // The handle removes the operation from the enclosing requirement but not
    // the handler's or the body's other effects.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {io, panic} { print_i64(x); resume(x) } {
                deep()
            }
        }"#,
        "requires effects {io}",
    );
    // An unknown row name remains rejected.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn main() -> i64 ! {Missing, panic} { 0 }"#,
        "unknown name",
    );
    // Declared effects participate in ordinary row inference and exclusions.
    let inferred = r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn apply<e: Effects>(f: fn() -> i64 ! {e}) -> i64 ! {panic, e} { f() }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                apply(deep)
            }
        }"#;
    assert_eq!(value(inferred), 20);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(inferred, 20);
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn only<e: Effects - Op>(f: fn() -> i64 ! {e}) -> i64 ! {panic, e} { f() }
        fn main() -> i64 ! {panic} { only(deep) }"#,
        "excluded",
    );
    // A declared operation's dynamic perform supplies the one-shot token, so a
    // multishot handler contract cannot be shared with called functions.
    rejects(
        r#"
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(20) }
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                deep()
            }
        }"#,
        "multishot resumption is not supported for a declared operation",
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
                resume: fn(Bool) -> i64 ! {},
            ) -> i64 ! {panic} { resume(true) } { perform Op(1) }
        }"#,
        "second parameter must be exactly",
    );
}

// ---------------------------------------------------------------------------
// Non-tail one-shot resumption
// ---------------------------------------------------------------------------

#[test]
fn a_tail_perform_keeps_the_allocation_free_identity_resumption() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x + 1) } {
                perform Op(20)
            }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 21);
    assert_eq!(stats.allocations, 0);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 21);
}

#[test]
fn non_tail_resumption_rejects_unsupported_continuation_shapes() {
    // The perform must be the whole value of a top-level statement; a nested
    // operand would need a more general expression continuation.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let a = perform Op(20) + 1;
                a
            }
        }"#,
        "non-tail 'perform' must be the entire value",
    );
    // Two non-tail performs would need a multi-prompt continuation.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let a = perform Op(1);
                let b = perform Op(2);
                a + b
            }
        }"#,
        "non-tail 'perform' must be the entire value",
    );
    // The body result is the operation result under real resumption.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let a = perform Op(20);
                a > 0
            }
        }"#,
        "type mismatch",
    );
    // Control transfers cannot cross the resumption boundary.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { resume(x) } {
                let a = perform Op(20);
                return a;
            }
        }"#,
        "cannot 'return' out of the handled body",
    );
    // A linear operation result would let the continuation transfer an
    // obligation the linear resume token cannot describe.
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        fn main() -> i64 ! {panic} {
            handle Op: Token -> Token with fn(
                x: Token,
                resume: linear once fn(Token) -> Token ! {},
            ) -> Token ! {panic} { resume(x) } {
                let a = perform Op(Token { id: 1 });
                a
            }
        }"#,
        "linear operation result",
    );
}

#[test]
fn multishot_resumption_reuses_a_capture_free_continuation() {
    // A copyable `fn(R) -> R` resumption token may be called more than once.
    // The continuation owns no environment, so each call re-runs the suffix
    // from the perform point with the supplied value.
    let source = r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} {
                let a = resume(1);
                resume(2)
            } {
                let v = perform Op(0);
                v + 1
            }
        }"#;
    assert_eq!(value(source), 3);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 3);
    // A tail perform with a copyable token is the allocation-free identity
    // resumption, callable repeatedly.
    let tail = r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} {
                resume(x)
            } {
                perform Op(7)
            }
        }"#;
    assert_eq!(value(tail), 7);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(tail, 7);
    // A captured environment would make the token owning, so multishot with
    // captures stays an explicit rejection rather than silently sharing it.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: fn(i64) -> i64 ! {},
            ) -> i64 ! {} {
                resume(x)
            } {
                let v = perform Op(0);
                v + n
            }
        }"#,
        "multishot resumption requires a continuation with no captured values",
    );
    // Owning operation results still cannot travel through a resumption.
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        fn main() -> i64 ! {panic} {
            handle Op: Token -> Token with fn(
                x: Token,
                resume: fn(Token) -> Token ! {},
            ) -> Token ! {} { resume(x) } {
                let a = perform Op(Token { id: 1 });
                a
            }
        }"#,
        "linear operation result",
    );
}

#[test]
fn non_tail_continuation_effects_are_visible_at_the_handle() {
    // The handler is pure, but its resumption runs the rest of the body, which
    // prints. The enclosing row must still require io.
    rejects(
        r#"
        fn main() -> Unit ! {panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                let a = perform Op(1);
                print_i64(a);
                a
            };
        }"#,
        "requires effects {io}",
    );
    let source = r#"
        fn main() -> Unit ! {io, panic} {
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } {
                let a = perform Op(41);
                print_i64(a);
                a
            };
        }"#;
    check(source).unwrap();
}

#[test]
fn non_tail_resumption_preserves_handler_and_continuation_order() {
    // The handler runs before and after `resume`; the continuation observes the
    // resumed value, and the handler sees the continuation result.
    let source = r#"
        fn main() -> i64 ! {alloc, panic} {
            let n = 1;
            handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} {
                let r = resume(x + 1);
                r * 2 + n
            } {
                let a = perform Op(20);
                a + 1
            }
        }"#;
    // resume(21) -> 21 + 1 = 22; handler -> 22 * 2 + 1 = 45.
    assert_eq!(value(source), 45);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 45);
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
fn branch_and_loop_joins_preserve_only_agreed_literal_indices() {
    let same_branches = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            if true { n = 6; } else { n = 6; }
            let a = keep(n, refl::<i64>(6));
            let b = keep(n, refl::<i64>(n));
            a + b
        }"#;
    assert_eq!(value(same_branches), 12);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(same_branches, 12);
    // A literal proof may not survive a branch that changes the value on one
    // side only: one route reaches 0, the other 1, and the joined index is a
    // fresh opaque value.
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            if true { n = 0; } else { n = 1; }
            keep(n, refl::<i64>(0))
        }"#,
        "proof does not establish",
    );
    // A loop that may assign the value invalidates a literal proof even when
    // the condition happens to be false at run time.
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 6;
            while false { n = 7; }
            keep(n, refl::<i64>(6))
        }"#,
        "proof does not establish",
    );
    // A loop that never assigns keeps the joined literal index alive.
    let loop_preserves = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            if true { n = 6; } else { n = 6; }
            while false { let _copy = n; }
            keep(n, refl::<i64>(6))
        }"#;
    assert_eq!(value(loop_preserves), 6);
}

#[test]
fn proof_valued_locals_are_erased_aliases_with_checked_terms() {
    let source = r#"
        total fn same_i64(n: i64) -> Eq<i64, n, n> ! {} { refl::<i64>(n) }
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n = 5;
            let p = same_i64(n);
            let q = p;
            keep(n, p) + keep(n, q)
        }"#;
    assert_eq!(value(source), 10);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 10);
    // A proof-valued local has no runtime representation.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let p = refl::<i64>(1);
            p
        }"#,
        "has no runtime value",
    );
    // The stored term must establish the callee's proposition at the use site.
    rejects(
        r#"
        prop ZeroI<n: i64> { Zero: ZeroI<0> }
        total fn zero_proof() -> ZeroI<0> ! {} { ZeroI.Zero::<0> }
        fn keep_zero(n: i64, erased p: ZeroI<n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let n = 1;
            let p = zero_proof();
            keep_zero(n, p)
        }"#,
        "proof does not establish",
    );
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
fn mutable_scalar_capture_is_a_live_view_with_a_checked_loan() {
    // The closure captures the caller's scalar location, not a copy. The
    // location stays loaned until the closure's last call, so a write before
    // that call is rejected; after the call the binding is free again.
    let source = r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 5;
            let f = fn() -> i64 ! {alloc, panic} { keep(n, refl::<i64>(n)) };
            let value = f();
            n = 6;
            value + n
        }"#;
    assert_eq!(value(source), 11);
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {alloc, panic} {
            let mut n = 5;
            let f = fn() -> i64 ! {alloc, panic} { keep(n, refl::<i64>(n)) };
            n = 6;
            f() + n
        }"#,
        "while a closure capturing it is live",
    );
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
    // An empty open row accepts any record whose fields can be erased.
    let empty = r#"
        struct Wide { x: i64, extra: Box<i64> }
        fn ignore(v: struct { .. }) -> i64 ! {panic} { 42 }
        fn main() -> i64 ! {alloc, panic} {
            ignore(Wide { x: 1, extra: Box.new(2) })
        }"#;
    let (result, stats) = evaluate(empty);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(empty, 42);
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
        "requires effects {panic, Op}",
    );
}

#[test]
fn runtime_sized_array_literals_set_the_runtime_length() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [10, 20, 30];
            let empty: DynArray<i64, 2> = [];
            DynArray.len(&a) + DynArray.get(&a, 2) + DynArray.len(&empty)
        }"#;
    assert_eq!(value(source), 33);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 33);
    // The literal length is statically bounded by the capacity; the reused
    // push guards are unreachable, so no `panic` effect is required.
    let literal = r#"
        fn main() -> i64 ! {} {
            let a: DynArray<i64, 2> = [4, 5];
            DynArray.len(&a)
        }"#;
    assert_eq!(value(literal), 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(literal, 2);
    // Owning elements in a literal are dropped as a prefix.
    let owning = r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 3> = [Box.new(1), Box.new(2)];
            DynArray.len(&a)
        }"#;
    let (result, stats) = evaluate(owning);
    assert_eq!(result, 2);
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(owning, 2);
    rejects(
        r#"
        fn main() -> i64 ! {} {
            let a: DynArray<i64, 2> = [1, 2, 3];
            0
        }"#,
        "DynArray literal has 3 elements but the capacity is 2",
    );
    // Multi-word elements keep their layout through a literal and a view.
    let widened = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<[i64; 2], 3> = [[1, 2], [3, 4]];
            let view: &[[i64; 2]] = &a[..];
            let row = Slice.get(view, 1);
            row[0] + row[1]
        }"#;
    assert_eq!(value(widened), 7);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(widened, 7);
}

#[test]
fn runtime_sized_array_slice_views_cover_the_live_prefix() {
    let source = r#"
        fn head(s: &[i64]) -> i64 ! {panic} { Slice.get(s, 0) }
        fn main() -> i64 ! {io, panic} {
            let a: DynArray<i64, 4> = [10, 20, 30];
            let all: &[i64] = &a[..];
            let middle = &a[1..3];
            {
                let inner: &[i64] = &a[2..];
                print_i64(Slice.len(inner));
            }
            Slice.len(all) + head(all) + Slice.len(middle) + Slice.get(middle, 1) + all[2]
        }"#;
    assert_eq!(value(source), 3 + 10 + 2 + 30 + 30);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 75);
    // The range is checked against the runtime length, not the capacity.
    let out_of_bounds = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2, 3];
            let bad: &[i64] = &a[0..4];
            Slice.len(bad)
        }"#;
    let program = check(out_of_bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("slice range out of bounds"),
        "{error:?}"
    );
    // A view is invalidated by push, pop, assignment, or moving the owner.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            let view: &[i64] = &a[..];
            a = DynArray.push(a, 3);
            Slice.len(view)
        }"#,
        "slice view or reference borrows it",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            let view: &[i64] = &a[..];
            drop(a);
            Slice.len(view)
        }"#,
        "move",
    );
    let runtime_bounds = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            let bad: &[i64] = &a[0..3];
            Slice.len(bad)
        }"#;
    let program = check(runtime_bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("slice range out of bounds"),
        "{error:?}"
    );
    rejects(
        "fn f() -> &[i64] ! {} { let a: DynArray<i64, 2> = [1, 2]; &a[..] } fn main() -> Unit ! {} {}",
        "cannot be returned",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 2> = [Box.new(1)];
            let view: &[Box<i64>] = &a[..];
            Slice.len(view)
        }"#,
        "owning or linear elements",
    );
    // Releasing the view at the end of its block permits a later push.
    let released = r#"
        fn main() -> i64 ! {io, panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            { let view: &[i64] = &a[..]; print_i64(Slice.len(view)); }
            a = DynArray.push(a, 3);
            DynArray.len(&a)
        }"#;
    assert_eq!(value(released), 3);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(released, 3);
}

#[test]
fn runtime_sized_array_mutable_views_write_the_live_prefix() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [10, 20, 30];
            {
                let view: &mut [i64] = &mut a[1..3];
                Slice.set(view, 0, 7);
                Slice.set(view, 1, 9);
            }
            DynArray.len(&a) + DynArray.get(&a, 1) + DynArray.get(&a, 2)
        }"#;
    assert_eq!(value(source), 3 + 7 + 9);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 19);
    // Writes through the view are visible to the owner and survive a later
    // push after the view is released.
    let released = r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1];
            {
                let view: &mut [i64] = &mut a[..];
                Slice.set(view, 0, 5);
            }
            let a = DynArray.push(a, 6);
            DynArray.get(&a, 0) + DynArray.get(&a, 1)
        }"#;
    assert_eq!(value(released), 11);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(released, 11);
    // A mutable view requires a mutable owner and an exclusive range.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            let view: &mut [i64] = &mut a[..];
            Slice.len(view)
        }"#,
        "immutable binding",
    );
    // Two exclusive views of the same live prefix alias, so they are rejected.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            let first: &mut [i64] = &mut a[..];
            let second: &mut [i64] = &mut a[..];
            Slice.len(first) + Slice.len(second)
        }"#,
        "another view of the same owner is live",
    );
    // A shared view and an exclusive view cannot coexist.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            let shared: &[i64] = &a[..];
            let exclusive: &mut [i64] = &mut a[..];
            Slice.len(shared) + Slice.len(exclusive)
        }"#,
        "cannot create an exclusive",
    );
    // The owner cannot be read, pushed, set, popped, moved, or dropped while
    // the exclusive view is live.
    for body in [
        "let b = DynArray.push(a, 3); Slice.len(view) + DynArray.len(&b)",
        "let b = DynArray.set(a, 0, 3); Slice.len(view) + DynArray.len(&b)",
        "let (b, _) = DynArray.pop(a); Slice.len(view) + DynArray.len(&b)",
        "drop(a); Slice.len(view)",
    ] {
        let source = format!(
            r#"
            fn main() -> i64 ! {{panic}} {{
                let mut a: DynArray<i64, 4> = [1, 2];
                let view: &mut [i64] = &mut a[..];
                {body}
            }}"#
        );
        rejects(&source, "");
    }
    // The descriptor length is the live prefix, so an out-of-prefix write
    // panics instead of touching an uninitialized capacity slot.
    let out_of_bounds = r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            let view: &mut [i64] = &mut a[..];
            Slice.set(view, 2, 3);
            0
        }"#;
    let program = check(out_of_bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("index out of bounds"), "{error:?}");
}

#[test]
fn runtime_sized_array_field_views_alias_the_record_storage() {
    let source = r#"
        struct Holder { tag: i64, xs: DynArray<i64, 4> }
        fn main() -> i64 ! {panic} {
            let mut holder = Holder { tag: 5, xs: [10, 20, 30] };
            {
                let shared: &[i64] = &holder.xs[..];
                let middle: &[i64] = &holder.xs[1..3];
                Slice.len(shared) + Slice.len(middle) + Slice.get(middle, 1)
            }
        }"#;
    assert_eq!(value(source), 3 + 2 + 30);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 35);
    // An exclusive field view writes the record field in place.
    let write = r#"
        struct Inner { xs: DynArray<i64, 4> }
        struct Holder { tag: i64, inner: Inner }
        fn main() -> i64 ! {panic} {
            let mut holder = Holder { tag: 1, inner: Inner { xs: [4, 5, 6] } };
            {
                let view: &mut [i64] = &mut holder.inner.xs[1..];
                Slice.set(view, 0, 50);
            }
            let inner = holder.inner;
            let xs = inner.xs;
            holder.tag + DynArray.len(&xs) + DynArray.get(&xs, 1)
        }"#;
    assert_eq!(value(write), 1 + 3 + 50);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(write, 54);
    // The field loan blocks replacing or mutating the record while the view
    // is live, and an exclusive field view needs a mutable record binding.
    rejects(
        r#"
        struct Holder { xs: DynArray<i64, 4> }
        fn main() -> i64 ! {panic} {
            let mut holder = Holder { xs: [1] };
            let view: &[i64] = &holder.xs[..];
            holder = Holder { xs: [2] };
            Slice.len(view)
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"
        struct Holder { xs: DynArray<i64, 4> }
        fn main() -> i64 ! {panic} {
            let holder = Holder { xs: [1] };
            let view: &mut [i64] = &mut holder.xs[..];
            Slice.len(view)
        }"#,
        "immutable record binding",
    );
    // Moving an affine record while its field view is live is rejected.
    rejects(
        r#"
        struct Holder { xs: DynArray<i64, 4>, boxed: Box<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let holder = Holder { xs: [1], boxed: Box.new(2) };
            let view: &[i64] = &holder.xs[..];
            let moved = holder;
            let Holder { xs, boxed } = moved;
            Slice.len(view) + DynArray.len(&xs) + Box.take(boxed)
        }"#,
        "cannot move an owner while it is borrowed",
    );
    // A view through a temporary record is not pinned and is rejected.
    rejects(
        r#"
        struct Holder { xs: DynArray<i64, 4> }
        fn make() -> Holder ! {panic} { Holder { xs: [1] } }
        fn main() -> i64 ! {panic} {
            let view: &[i64] = &make().xs[..];
            Slice.len(view)
        }"#,
        "bind the record to a local first",
    );
    // A view of a by-value parameter's inline field cannot escape the call.
    rejects(
        r#"
        struct Holder { xs: DynArray<i64, 4> }
        fn leak(holder: Holder) -> &[i64] ! {} { &holder.xs[..] }
        fn main() -> Unit ! {} {}"#,
        "cannot be returned",
    );
}

#[test]
fn runtime_sized_array_equality_compares_the_live_prefix() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let same: DynArray<i64, 4> = [1, 2, 3];
            let copy: DynArray<i64, 4> = [1, 2, 3];
            let shorter: DynArray<i64, 4> = [1, 2];
            let longer: DynArray<i64, 4> = [1, 2, 3, 0];
            let differs: DynArray<i64, 4> = [1, 2, 4];
            (if same == copy { 1 } else { 0 })
                + (if same == shorter { 10 } else { 0 })
                + (if same == longer { 100 } else { 0 })
                + (if same == differs { 1000 } else { 0 })
                + (if same != differs { 1 } else { 0 })
        }"#;
    assert_eq!(value(source), 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 2);
    let floats = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<f64, 3> = [1.5, 2.5];
            let b: DynArray<f64, 3> = [1.5, 2.5];
            let c: DynArray<f64, 3> = [1.5, 2.75];
            (if a == b { 1 } else { 0 }) + (if a == c { 10 } else { 0 })
        }"#;
    assert_eq!(value(floats), 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(floats, 1);
    // Owning and non-scalar elements are not comparable by value.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 2> = [Box.new(1)];
            let b: DynArray<Box<i64>, 2> = [Box.new(1)];
            if a == b { 1 } else { 0 }
        }"#,
        "owning, linear, and view elements are not comparable",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<[i64; 2], 2> = [[1, 2]];
            let b: DynArray<[i64; 2], 2> = [[1, 2]];
            if a == b { 1 } else { 0 }
        }"#,
        "comparable one-word elements",
    );
}

#[test]
fn runtime_sized_array_patterns_match_length_and_tail() {
    let source = r#"
        fn classify(a: DynArray<i64, 4>) -> i64 ! {panic} {
            match a {
                [] => 0,
                [x] => x,
                [x, y] => x + y,
                [first, ..rest] => first + DynArray.len(&rest),
                _ => 99
            }
        }
        fn main() -> i64 ! {panic} {
            let empty: DynArray<i64, 4> = [];
            let one: DynArray<i64, 4> = [5];
            let two: DynArray<i64, 4> = [1, 2];
            let many: DynArray<i64, 4> = [10, 20, 30];
            classify(empty) + classify(one) + classify(two) + classify(many)
        }"#;
    assert_eq!(value(source), 5 + 3 + 12);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 20);
    // A named rest binds a copy of the tail with the same capacity, so its
    // prefix is readable and its length is the remaining live count.
    let tail = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2, 3];
            match a {
                [first, ..rest] => first + DynArray.len(&rest) * 10 + DynArray.get(&rest, 1),
                _ => 0
            }
        }"#;
    assert_eq!(value(tail), 24);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(tail, 24);
    // Literals and an unnamed rest participate in element patterns.
    let literal = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [7, 8, 9];
            match a {
                [7, y, ..] => y,
                _ => 0
            }
        }"#;
    assert_eq!(value(literal), 8);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(literal, 8);
    // A guard can fall through to a later arm, including the catch-all.
    let guarded = r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            match a {
                [x, ..] if x == 9 => 100,
                [x, y] => x + y,
                _ => 0
            }
        }"#;
    assert_eq!(value(guarded), 3);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(guarded, 3);
    // The runtime length is not statically exhaustive.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1];
            match a {
                [] => 0,
                [x] => x
            }
        }"#,
        "non-exhaustive match",
    );
    // An earlier catch-all makes a later length pattern unreachable.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1];
            match a {
                _ => 0,
                [x] => x
            }
        }"#,
        "unreachable match arm",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<Box<i64>, 2> = [Box.new(1)];
            match a {
                [x] => 0,
                _ => 1
            }
        }"#,
        "owning, linear, and view elements cannot be matched by value",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 2> = [1, 2, 3];
            a
        }"#,
        "capacity",
    );
}

#[test]
fn match_arms_join_scalar_proof_indices() {
    rejects(
        r#"
        fn pick() -> Bool ! {} { false }
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            n = 6;
            match pick() {
                true => { n = 7; 0 },
                false => { keep(n, refl::<i64>(7)) },
            }
        }"#,
        "proof does not establish",
    );
    rejects(
        r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0; n = 6;
            match false { true => { n = 7; }, false => { } }
            keep(n, refl::<i64>(7))
        }"#,
        "proof does not establish",
    );
    assert_eq!(
        value(
            r#"
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 0;
            match false { true => { n = 7; }, false => { n = 7; } }
            keep(n, refl::<i64>(7))
        }"#
        ),
        7
    );
}

#[test]
fn nested_block_mutation_does_not_alias_scalar_proof_indices() {
    rejects(
        r#"
        fn same(a: i64, b: i64, erased p: Eq<i64, a, b>) -> i64 ! {panic} { a - b }
        fn main() -> i64 ! {panic} {
            let mut n = 6;
            { n = n + 1; }
            let m = 5;
            same(n, m, refl::<i64>(m))
        }"#,
        "proof does not establish",
    );
    assert_eq!(
        value(
            r#"
        fn get() -> i64 ! {panic} { 7 }
        fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }
        fn main() -> i64 ! {panic} {
            let mut n = 6;
            { n = get(); }
            keep(n, refl::<i64>(n))
        }"#
        ),
        7
    );
}

#[test]
fn non_tail_continuations_reject_try_but_allow_local_loops_and_mut_results() {
    rejects(
        r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn work() -> i64 ! {panic} {
            let r = handle Op: i64 -> Result<i64, i64> with fn(
                x: i64, resume: linear once fn(Result<i64, i64>) -> Result<i64, i64> ! {},
            ) -> Result<i64, i64> ! {panic} { resume(Err(7)) } {
                let a = perform Op(1);
                let v = a?;
                Ok(v + 1)
            };
            match r { Ok(v) => v, Err(e) => e }
        }
        fn main() -> i64 ! {panic} { work() }"#,
        "cannot use '?'",
    );
    assert_eq!(
        value(
            r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {})
                -> i64 ! {panic} { resume(x) } {
                let a = perform Op(1);
                let mut i = 0; let mut s = 0;
                while i < 3 {
                    i = i + 1;
                    if i == 2 { continue; }
                    s = s + i;
                }
                a + s
            }
        }"#
        ),
        5
    );
    assert_eq!(
        value(
            r#"
        fn main() -> i64 ! {panic} {
            handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {})
                -> i64 ! {panic} { resume(x) + 10 } {
                let mut a = perform Op(1);
                a = a + 1;
                a
            }
        }"#
        ),
        12
    );
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn union_injection_converts_structural_members_and_drops_erased_fields() {
    agrees(
        r#"
        struct Wide { a: i64, b: i64, c: i64 }
        fn main() -> i64 ! {panic} {
            let v: struct { c: i64 } | Bool = Wide { a: 11, b: 22, c: 33 };
            match v { struct { c } => c, Bool @ _ => 0 }
        }"#,
        33,
    );
    agrees(
        r#"
        struct Wide { a: i64, b: Box<i64> }
        fn pass(v: struct { a: i64, .. } | Bool) -> i64 ! {panic} {
            match v { struct { a } => a, Bool @ _ => 0 }
        }
        fn main() -> i64 ! {alloc, panic} {
            pass(Wide { a: 42, b: Box.new(1) })
        }"#,
        42,
    );
    agrees(
        r#"
        struct Wide { a: i64, b: i64, c: Box<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let u: struct { c: Box<i64> } | Bool = Wide { a: 7, b: 8, c: Box.new(5) };
            match u { struct { c } => Box.take(c), Bool @ _ => 0 }
        }"#,
        5,
    );
    rejects(
        r#"
        struct Wide { a: i64, b: i64, c: i64 }
        fn main() -> i64 ! {panic} {
            let u: Wide | Bool = Wide { a: 1, b: 2, c: 3 };
            let v: struct { c: i64 } | Bool = u;
            match v { struct { c } => c, Bool @ _ => 0 }
        }"#,
        "would change its representation",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let u: struct { inner: struct { a: i64, b: i64, c: i64 } | Bool } =
                struct { inner: struct { a: 1, b: 2, c: 3 } };
            let v: struct { inner: struct { c: i64 } | Bool } = u;
            match v.inner { struct { c } => c, Bool @ _ => 0 }
        }"#,
        "would change a member representation",
    );
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn callable_field_adapters_inside_dynarray_push_build_natively() {
    agrees(
        r#"
        fn widen(value: i64 | Bool) -> i64 ! {panic} {
            match value { i64 @ n => n, Bool @ _ => 0 }
        }
        struct Holder { f: fn(i64 | Bool) -> i64 ! {panic}, tag: Bool }
        fn main() -> i64 ! {alloc, panic} {
            let a: DynArray<struct { f: once fn(i64) -> i64 ! {panic} }, 2> =
                DynArray.new::<struct { f: once fn(i64) -> i64 ! {panic} }, 2>();
            let a = DynArray.push(a, Holder { f: widen, tag: true });
            42
        }"#,
        42,
    );
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn structural_borrowed_results_transfer_a_nominal_field() {
    // A nominal borrowed field narrows into an anonymous structural result.
    // The declared result label is tied to the parameter record's field
    // lifetime, and the caller keeps the owner loaned until the result's last
    // use.
    agrees(
        r#"
        struct W<'a> { n: i64, view: &'a [i64] }
        fn ret<'a>(v: W<'a>) -> struct { view: &'a [i64] } ! {panic} {
            let W { view, .. } = v;
            struct { view: view }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = ret(W { n: 1, view: &values[..] });
            Slice.get(out.view, 0) + 2
        }"#,
        42,
    );
}

#[test]
fn union_partition_follows_declaration_order_not_operand_order() {
    let source = |pattern: &str| {
        format!(
            "fn pick<A, B>(x: {pattern}, a: A) -> i64 ! {{panic}} {{ 0 }}
            fn two(c: i64) -> Bool | Unit | i64 ! {{panic}} {{
                if c == 0 {{ true }} else {{ if c == 1 {{ () }} else {{ 41 }} }}
            }}
            fn main() -> i64 ! {{panic}} {{ pick(two(0), true) }}"
        )
    };
    assert_eq!(value(&source("A | B | i64")), 0);
    assert_eq!(value(&source("B | A | i64")), 0);
}

#[test]
fn dynarray_pop_waits_for_live_views() {
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            let v: &[i64] = &a[..];
            let (a, x) = DynArray.pop(a);
            Slice.len(v) + x
        }"#,
        "cannot pop from a DynArray while a slice view",
    );
    assert_eq!(
        value(
            r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            let n = { let v: &[i64] = &a[..]; Slice.len(v) };
            let (a, x) = DynArray.pop(a);
            n + x
        }"#
        ),
        4
    );
}

#[test]
fn row_variables_preserve_unmentioned_fields() {
    // The row variable is monomorphized to the argument's residual canonical
    // row, so `extra: Box<i64>` and `flag: Bool` survive the call and the
    // returned value can read them. The retained box is dropped exactly once.
    let source = r#"
        struct Wide { flag: Bool, x: i64, extra: Box<i64> }
        fn keep<r>(v: struct { x: i64, ..r }) -> struct { x: i64, ..r } ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let w = Wide { flag: true, x: 40, extra: Box.new(1) };
            let r = keep(w);
            if r.flag { r.x + 2 } else { 0 }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // Row unification recurses through nested structural fields.
    let nested = r#"
        fn keep<r>(v: struct { inner: struct { a: i64, ..r } })
            -> struct { inner: struct { a: i64, ..r } } ! {panic} { v }
        fn main() -> i64 ! {panic} {
            let out = keep(struct { inner: struct { a: 40, extra: true } });
            if out.inner.extra { out.inner.a + 2 } else { 0 }
        }"#;
    assert_eq!(value(nested), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(nested, 42);
    // A linear residual field travels through the row and is consumed once by
    // the exact-row consumer.
    let linear = r#"
        #[linear]
        struct Token { id: i64 }
        fn keep<r>(v: struct { n: i64, ..r }) -> struct { n: i64, ..r } ! {panic} { v }
        fn consume(v: struct { n: i64, token: Token }) -> i64 ! {panic} {
            let struct { n, token } = v;
            let Token { id } = token;
            n + id
        }
        fn main() -> i64 ! {panic} {
            let out = keep(struct { n: 1, token: Token { id: 41 } });
            consume(out)
        }"#;
    assert_eq!(value(linear), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(linear, 42);
    // A borrowed residual field stays live for the call and is dropped with
    // the consumed row, so replacing the owner afterwards is legal.
    let borrowed = r#"
        fn first<r>(v: struct { view: &[i64], ..r }) -> i64 ! {alloc, panic} {
            let out = Slice.get(v.view, 1);
            drop(v);
            out
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [1, 41];
            let n = first(struct { view: &data[..], flag: true });
            data = [9, 9];
            n + 1
        }"#;
    assert_eq!(value(borrowed), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(borrowed, 42);
}

#[test]
fn row_variables_reject_erased_linear_and_borrowed_escapes() {
    // Closing a row that still carries a linear field would drop it without a
    // consumer, exactly like ordinary width erasure.
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        fn erase<r>(v: struct { n: i64, ..r }) -> struct { n: i64 } ! {panic} { v }
        fn main() -> i64 ! {panic} {
            let t = Token { id: 1 };
            let out = erase(struct { n: 1, token: t });
            out.n
        }"#,
        "linear obligation",
    );
    // The preserved view keeps its loan through the row-variable parameter, so
    // an exclusive borrow of the same owner while the row is live is rejected.
    rejects(
        r#"fn keep<r>(v: struct { view: &[i64], ..r }, values: &mut Vec<i64>)
            -> i64 ! {alloc, panic} {
            Vec.clear(values);
            Slice.get(v.view, 0)
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [1, 2];
            keep(struct { view: &data[..], n: 1 }, &mut data)
        }"#,
        "exclusive '&mut Record'",
    );
    // A returned structural row whose borrowed fields are elided on both the
    // parameter and the result has no signature lifetime identity to relate
    // them. An elided parameter field does not supply an input lifetime, so
    // this remains an explicit rejection rather than an invented equality.
    rejects(
        r#"fn keep<r>(v: struct { view: &[i64], ..r })
            -> struct { view: &[i64], ..r } ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let data: Vec<i64> = [1, 2];
            let out = keep(struct { view: &data[..], n: 1 });
            Slice.get(out.view, 0)
        }"#,
        "no borrowed input to infer it from",
    );
    // One row variable must receive the same residual row from every
    // parameter; otherwise the specialization is not determined.
    rejects(
        r#"fn pair<r>(a: struct { x: i64, ..r }, b: struct { x: i64, ..r })
            -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} {
            pair(struct { x: 1, left: true }, struct { x: 2, right: true })
        }"#,
        "residual row",
    );
}

#[test]
fn structural_cast_renames_fields_explicitly() {
    // `from` names the source field of one target field. Unmentioned fields
    // are dropped with ordinary cleanup, including an owning `extra`.
    let source = r#"
        struct Wide { a: i64, extra: Box<i64>, flag: Bool }
        fn main() -> i64 ! {alloc, panic} {
            let w = Wide { a: 40, extra: Box.new(1), flag: true };
            let r = w as struct { b: i64 from a, flag: Bool };
            if r.flag { r.b + 2 } else { 0 }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    rejects(
        r#"struct Wide { a: i64, b: i64 }
        fn main() -> i64 ! {panic} {
            let w = Wide { a: 1, b: 2 };
            let r = w as struct { x: i64 from a, y: i64 from a };
            r.x
        }"#,
        "more than one target field",
    );
    rejects(
        r#"struct Wide { a: i64 }
        fn main() -> i64 ! {panic} {
            let w = Wide { a: 1 };
            let r = w as struct { x: i64 from missing };
            r.x
        }"#,
        "no field 'missing'",
    );
    rejects(
        r#"#[linear]
        struct Token { id: i64 }
        struct Wide { a: i64, token: Token }
        fn main() -> i64 ! {panic} {
            let w = Wide { a: 1, token: Token { id: 2 } };
            let r = w as struct { b: i64 from a };
            r.b
        }"#,
        "linear obligation",
    );
    // Renaming metadata is only meaningful in the explicit cast, never in a
    // general structural type.
    rejects(
        r#"fn read(v: struct { b: i64 from a }) -> i64 ! {panic} { v.b }
        fn main() -> i64 ! {panic} { 0 }"#,
        "field renaming",
    );
}

#[test]
fn structural_equality_compares_every_canonical_field() {
    let source = r#"
        fn main() -> i64 ! {panic} {
            let a = struct { x: 1, y: true, z: struct { q: 3, r: 4 } };
            let b = struct { z: struct { r: 4, q: 3 }, y: true, x: 1 };
            let c = struct { x: 1, y: true, z: struct { q: 3, r: 5 } };
            if a == b && a != c { 42 } else { 0 }
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // Owning, borrowed, floating-point, union, nominal, and callable leaves
    // are not comparable without an explicit field match.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let a = struct { b: Box.new(1) };
            let b = struct { b: Box.new(1) };
            if a == b { 1 } else { 0 }
        }"#,
        "structural equality requires",
    );
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let a = struct { x: 1.0 };
            let b = struct { x: 1.0 };
            if a == b { 1 } else { 0 }
        }"#,
        "structural equality requires",
    );
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let a: struct { x: i64 | Bool } = struct { x: 1 };
            let b: struct { x: i64 | Bool } = struct { x: true };
            if a == b { 1 } else { 0 }
        }"#,
        "structural equality requires",
    );
}

#[test]
fn open_row_impl_headers_monomorphize_per_receiver() {
    // A trait impl header may leave a named row tail. Dispatch binds the
    // residual row and instantiates the checked method once per receiver row.
    let source = r#"
        trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<r> Tag for struct { x: i64, ..r } {
            fn tag(self: Self) -> i64 ! {panic} { self.x }
        }
        impl<r> struct { n: i64, ..r } {
            fn double(self: Self) -> i64 ! {panic} { self.n * 2 }
        }
        fn main() -> i64 ! {panic} {
            let s = struct { x: 40, extra: true };
            let t = struct { n: 1, flag: false };
            s.tag() + t.double()
        }"#;
    assert_eq!(value(source), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
    // Open-row impls remain structural-only: a nominal record has its own
    // identity and must be coerced explicitly first.
    rejects(
        r#"trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<r> Tag for struct { x: i64, ..r } {
            fn tag(self: Self) -> i64 ! {panic} { self.x }
        }
        struct Point { x: i64 }
        fn main() -> i64 ! {panic} { Point { x: 1 }.tag() }"#,
        "no method 'tag'",
    );
    // Two incomparable open-row headers for one trait can both match a wider
    // row; coherence rejects that ambiguity instead of choosing one.
    rejects(
        r#"trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
        impl<r> Tag for struct { x: i64, ..r } {
            fn tag(self: Self) -> i64 ! {panic} { self.x }
        }
        impl<r> Tag for struct { y: i64, ..r } {
            fn tag(self: Self) -> i64 ! {panic} { self.y }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "incomparable",
    );
    // A bare `..` has no parameter to bind the residual row, so it stays an
    // explicit rejection rather than an unconstrained blanket impl.
    rejects(
        r#"impl struct { x: i64, .. } {
            fn read_x(self: Self) -> i64 ! {panic} { self.x }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "open row",
    );
}

#[test]
fn task_handler_barriers_do_not_expose_shadowed_outer_frames() {
    let source = r#"
        use std.task.TaskExit;
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(0) }
        fn main() -> i64 ! {suspend, alloc, panic} {
            handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { resume(100) } {
                let n = 7;
                handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} { resume(n) } {
                    Task.scope(fn() -> i64 ! {suspend, alloc, Op, panic} {
                        let t: Task<i64> = Task.spawn(fn() -> i64 ! {Op, panic} { deep() });
                        match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
                    })
                }
            }
        }"#;
    let program = check(source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("no dynamically active handler"),
        "{error:?}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("handler-barrier");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "a shadowed outer handler became visible"
        );
    }
}

#[test]
fn tasks_inherit_copyable_handler_suffix_above_an_owned_barrier() {
    let source = r#"
        use std.task.TaskExit;
        effect Op: i64 -> i64;
        fn deep() -> i64 ! {Op, panic} { perform Op(0) }
        fn run_child() -> i64 ! {Op, suspend, alloc, panic} {
            Task.scope(fn() -> i64 ! {suspend, alloc, Op, panic} {
                let task: Task<i64> = Task.spawn(fn() -> i64 ! {Op, panic} {deep()});
                match Task.join(task) {TaskExit.Completed(v) => v, TaskExit.Cancelled => 0}
            })
        }
        fn main() -> i64 ! {suspend, alloc, panic} {
            handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {resume(100)} {
                let n = 7;
                handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {resume(n)} {
                    handle Op: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {resume(9)} {
                        run_child()
                    }
                }
            }
        }"#;
    assert_eq!(value(source), 9);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 9);
}

#[test]
fn structural_equality_operands_are_ownership_checked() {
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let v: Vec<i64> = [1, 2];
            let a = struct { x: 1 };
            let b = struct { x: 1 };
            let same = a == { drop(v); b };
            if same { Vec.len(&v) } else { 0 }
        }"#,
        "moved owner",
    );
    rejects(
        r#"
        #[linear]
        enum Token { Live }
        fn take(t: Token) -> i64 ! {} { match t { Token.Live => 1 } }
        fn main() -> i64 ! {panic} {
            let t = Token.Live;
            let a = struct { x: 1 };
            let same = a == struct { x: take(t) };
            take(t)
        }"#,
        "use after move",
    );
    assert_eq!(
        value(
            r#"
        fn main() -> i64 ! {panic} {
            let a = struct { x: 1, y: 2 };
            let b = struct { y: 2, x: 1 };
            if a == b { if a != struct { x: 1, y: 3 } { 7 } else { 0 } } else { 0 }
        }"#
        ),
        7
    );
}

#[test]
fn open_row_impls_specialize_by_field_set() {
    let impls = |second: &str| {
        format!(
            "trait Tag {{ fn tag(self: Self) -> i64 ! {{panic}}; }}
            impl<r> Tag for struct {{ x: i64, ..r }} {{ fn tag(self: Self) -> i64 ! {{panic}} {{ 1 }} }}
            {second}
            fn main() -> i64 ! {{panic}} {{
                let a = struct {{ x: 1, y: 2 }};
                let b = struct {{ x: 1, z: true }};
                a.tag() * 10 + b.tag()
            }}"
        )
    };
    for second in [
        "impl<r> Tag for struct { x: i64, y: i64, ..r } { fn tag(self: Self) -> i64 ! {panic} { 2 } }",
        "impl Tag for struct { x: i64, y: i64 } { fn tag(self: Self) -> i64 ! {panic} { 2 } }",
    ] {
        assert_eq!(value(&impls(second)), 21);
    }
    rejects(
        &impls(
            "impl<s> Tag for struct { x: i64, ..s } { fn tag(self: Self) -> i64 ! {panic} { 2 } }",
        ),
        "duplicate implementation",
    );
    rejects(
        &impls(
            "impl<r> Tag for struct { y: i64, ..r } { fn tag(self: Self) -> i64 ! {panic} { 2 } }",
        ),
        "incomparable",
    );
}

#[test]
fn a_result_hint_cannot_fix_a_row_variable_before_the_arguments() {
    assert_eq!(
        value(
            r#"
        fn keep<r>(v: struct { x: i64, ..r }) -> struct { x: i64, ..r } ! {panic} { v }
        fn main() -> i64 ! {panic} {
            let w = struct { x: 40, junk: true };
            let narrow: struct { x: i64 } = keep(w);
            narrow.x + 2
        }"#
        ),
        42
    );
}
