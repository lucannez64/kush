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
fn structural_nested_representation_change_is_explicitly_rejected() {
    rejects(
        r#"
        struct Inner { x: i64 }
        struct Outer { inner: Inner }
        fn read(v: struct { inner: struct { x: i64 } }) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} { read(Outer { inner: Inner { x: 1 } }) }"#,
        "nested representation change",
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
