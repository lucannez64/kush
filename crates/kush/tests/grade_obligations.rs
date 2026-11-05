//! GRADE-OBLIG-TESTS: one test per obligation of docs/grade-model.md
//! sections 2-5. Each obligation has at least one positive program, run in the
//! reference evaluator and the native backend with balanced allocations, and
//! at least one hostile program that the checker must reject for that
//! obligation's reason.
//!
//! Γ is the graded zone (copyable values, counted observations); Δ is the
//! linear zone (owners: affine or obligatory).

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

/// Positive program: evaluator and native agree on result and output.
fn holds(source: &str, expected: i64, stdout: &str) -> MemoryStats {
    let (result, output, stats) = run(source);
    assert_eq!(result, expected, "{source}");
    assert_eq!(output, stdout, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("grade-obligations");
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

/// Hostile program: rejected, with a diagnostic naming the obligation.
fn violates(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted a hostile program:\n{source}"),
        Err(error) => {
            if std::env::var("SHOW_REASONS").is_ok() {
                eprintln!("REASON[{fragment}] {}", error.message);
            }
            assert!(
                error.message.contains(fragment),
                "expected {fragment:?}, got {error:?}\n{source}"
            )
        }
    }
}

fn main_fn(row: &str, body: &str) -> String {
    format!("fn main() -> i64 ! {{{row}}} {{ {body} }}")
}

// ---------------------------------------------------------------------------
// Section 2: structural rules per zone
// ---------------------------------------------------------------------------

#[test]
fn gamma_weakening_only_at_zero_and_many() {
    // Grade 0, unannotated and `many` copyable bindings may be discarded.
    holds(
        &main_fn(
            "panic",
            "let a: i64 @[0] = 1; let b = 2; let c: i64 @[many] = 3; 4",
        ),
        4,
        "",
    );
    // An exact grade must be met on every normal path.
    violates(
        &main_fn("panic", "let a: i64 @[1] = 1; 4"),
        "used 0 time(s)",
    );
    violates(
        &main_fn("panic", "let a: i64 @[2] = 1; a + 4"),
        "used 1 time(s)",
    );
    violates(
        &main_fn(
            "panic",
            "let a: i64 @[1] = 1; let c = true; if c { a } else { 4 }",
        ),
        "different number of times on different paths",
    );
}

#[test]
fn gamma_contraction_adds_counts() {
    holds(&main_fn("panic", "let a: i64 @[3] = 2; a + a * a"), 6, "");
    violates(
        &main_fn("panic", "let a: i64 @[2] = 2; a + a + a"),
        "used 3 time(s)",
    );
}

#[test]
fn delta_weakening_drops_affine_owners_and_rejects_obligations() {
    // Affine owner: implicit drop, cleanup emitted.
    let stats = holds(&main_fn("alloc, panic", "let b = Box.new(5); 7"), 7, "");
    assert_eq!(stats.allocations, 1);
    // Obligatory owners can never be discarded on a normal exit.
    violates(
        &main_fn("alloc, panic", "let b: Box<i64> @[1] = Box.new(5); 7"),
        "linear",
    );
    violates(
        "#[linear] struct Token { id: i64 }
         fn main() -> i64 ! {} { let t = Token { id: 1 }; 7 }",
        "linear",
    );
    violates(
        &main_fn(
            "alloc, panic",
            "let x: i64 @[1] = 41;
             let f: linear once fn() -> i64 ! {panic} = fn() -> i64 ! {panic} { x + 1 };
             7",
        ),
        "linear",
    );
}

#[test]
fn delta_has_no_contraction() {
    holds(
        &main_fn(
            "alloc, panic",
            "let b: Box<i64> @[1] = Box.new(5); Box.take(b)",
        ),
        5,
        "",
    );
    violates(
        &main_fn(
            "alloc, panic",
            "let b = Box.new(5); let c = b; Box.take(b) + Box.take(c)",
        ),
        "use after move",
    );
}

#[test]
fn exchange_both_zones_are_unordered() {
    // Obligations in either order; evaluation order stays left to right.
    holds(
        &main_fn(
            "io, alloc, panic",
            "let x: i64 @[1] = 1; let b: Box<i64> @[1] = Box.new(10);
             let y: i64 @[1] = 100;
             print_i64(y); let t = Box.take(b); print_i64(x); t",
        ),
        10,
        "100\n1\n",
    );
}

#[test]
fn a_borrow_observes_the_view_not_the_owner() {
    // One borrow plus one move satisfies an owner's @[1].
    let stats = holds(
        "fn peek(b: &Box<i64>) -> i64 ! {panic} { 1 }
         fn main() -> i64 ! {alloc, panic} {
             let b: Box<i64> @[1] = Box.new(5);
             let p = peek(&b);
             p + Box.take(b)
         }",
        6,
        "",
    );
    assert_eq!(stats.allocations, 1);
    // A borrow alone does not consume the obligation.
    violates(
        "fn peek(b: &Box<i64>) -> i64 ! {panic} { 1 }
         fn main() -> i64 ! {alloc, panic} {
             let b: Box<i64> @[1] = Box.new(5);
             peek(&b)
         }",
        "linear",
    );
}

#[test]
fn paths_alternatives_agree_and_early_exits_check_obligations() {
    holds(
        "fn f(c: Bool, x: i64 @[2]) -> i64 ! {panic} { if c { x + x } else { x * x } }
         fn main() -> i64 ! {panic} { f(true, 3) + f(false, 3) }",
        15,
        "",
    );
    violates(
        "fn f(c: Bool, x: i64 @[2]) -> i64 ! {panic} { if c { x + x } else { x } }
         fn main() -> i64 ! {panic} { f(true, 3) }",
        "different number of times on different paths",
    );
    // An early return leaves the owner's obligation unconsumed.
    violates(
        "fn f(c: Bool) -> i64 ! {alloc, panic} {
             let b: Box<i64> @[1] = Box.new(5);
             if c { return 0; }
             Box.take(b)
         }
         fn main() -> i64 ! {alloc, panic} { f(true) }",
        "linear",
    );
    // A loop must restore exact counts at its head.
    violates(
        "fn f(n: i64, x: i64 @[1]) -> i64 ! {panic} {
             let mut i = 0; let mut s = 0;
             while i < n { s = s + x; i = i + 1; }
             s
         }
         fn main() -> i64 ! {panic} { f(2, 1) }",
        "unknown number of times by the loop",
    );
}

// ---------------------------------------------------------------------------
// Section 3: scaling substitution r·Γ₁ + Γ₂, side condition Δ₁ empty or r = 1
// ---------------------------------------------------------------------------

#[test]
fn scaling_at_zero_still_evaluates_the_argument_once() {
    // Demand on an argument to an @[0] parameter is 1: it runs once, and a
    // must-use @[1] value passed there counts one observation.
    holds(
        "fn ignore(a: i64 @[0], b: i64) -> i64 ! {} { b }
         fn main() -> i64 ! {io, panic} {
             let x: i64 @[1] = 5;
             ignore({ print_i64(7); x }, 2)
         }",
        2,
        "7\n",
    );
    // The callee cannot observe its erased parameter.
    violates(
        "fn bad(a: i64 @[0]) -> i64 ! {} { a }
         fn main() -> i64 ! {} { bad(1) }",
        "grade @[0] forbids runtime observation",
    );
}

#[test]
fn scaling_at_one_and_n_multiplies_demand() {
    holds(
        "fn once(x: i64 @[1]) -> i64 ! {} { x }
         fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn four(x: i64 @[4]) -> i64 ! {panic} { twice(x) + twice(x) }
         fn main() -> i64 ! {panic} { let a: i64 @[1] = 3; let b: i64 @[4] = 1; once(a) + four(b) }",
        7,
        "",
    );
    violates(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn main() -> i64 ! {panic} { let a: i64 @[1] = 3; twice(a) }",
        "used 2 time(s)",
    );
}

#[test]
fn scaling_at_many_needs_an_unbounded_binding() {
    holds(
        "fn all(x: i64 @[many]) -> i64 ! {panic} { x + x + x }
         fn main() -> i64 ! {panic} { let a = 2; let b: i64 @[many] = 1; all(a) + all(b) }",
        9,
        "",
    );
    violates(
        "fn all(x: i64 @[many]) -> i64 ! {panic} { x + x + x }
         fn main() -> i64 ! {panic} { let a: i64 @[1] = 2; all(a) }",
        "used many time(s)",
    );
}

#[test]
fn owners_substitute_only_at_grade_one() {
    // Δ₁ nonempty requires r = 1; a consuming use counts once under any
    // demand, so a copyable result of the owner may still be duplicated.
    let stats = holds(
        "fn keep(b: Box<i64> @[1]) -> i64 ! {panic} { Box.take(b) }
         fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn main() -> i64 ! {alloc, panic} {
             let b: Box<i64> @[1] = Box.new(4);
             let c: Box<i64> @[1] = Box.new(5);
             keep(b) + twice(Box.take(c))
         }",
        14,
        "",
    );
    assert_eq!(stats.allocations, 2);
    for grade in ["0", "2", "many"] {
        violates(
            &format!(
                "fn f(b: Box<i64> @[{grade}]) -> i64 ! {{}} {{ 0 }}
                 fn main() -> i64 ! {{alloc, panic}} {{ f(Box.new(1)) }}"
            ),
            "Box<i64>",
        );
    }
}

// ---------------------------------------------------------------------------
// Section 4: erasure obligations E1-E6
// ---------------------------------------------------------------------------

#[test]
fn e1_erasure_keeps_effects_in_order() {
    holds(
        "fn pick(a: i64 @[0], b: i64, c: i64 @[0]) -> i64 ! {} { b }
         fn compute() -> i64 @[0] ! {io, panic} { print_i64(3); 42 }
         fn main() -> i64 ! {io, panic} {
             let v: i64 @[0] = { print_i64(1); 1 };
             compute();
             pick({ print_i64(4); 0 }, { print_i64(5); 9 }, { print_i64(6); 0 })
         }",
        9,
        "1\n3\n4\n5\n6\n",
    );
}

#[test]
fn e2_erased_bindings_are_never_observed() {
    for body in [
        "let v: i64 @[0] = 1; v",
        "let v: i64 @[0] = 1; let r = &v; 0",
        "let v: i64 @[0] = 1; let f = fn() -> i64 ! {} { v }; f()",
        "let v: i64 @[0] = 1; match v { 1 => 1, _ => 0 }",
        "let v: i64 @[0] = 1; let w = v; 0",
    ] {
        violates(&main_fn("panic", body), "graded @[0]");
    }
}

#[test]
fn e3_erased_positions_need_a_physical_adapter_one_way() {
    holds(
        "fn skip(a: i64 @[0], b: i64) -> i64 ! {} { b }
         fn call(f: fn(i64, i64) -> i64 ! {}) -> i64 ! {} { f(1, 8) }
         fn main() -> i64 ! {} { call(skip) }",
        8,
        "",
    );
    violates(
        "fn plain(a: i64, b: i64) -> i64 ! {} { b }
         fn main() -> i64 ! {} {
             let f: fn(i64 @[0], i64) -> i64 ! {} = plain;
             f(1, 2)
         }",
        "type mismatch: expected fn(i64 @[0], i64)",
    );
}

#[test]
fn e4_obligations_are_never_erased() {
    // An affine owner at @[0] is "evaluate and drop at the binding site".
    let stats = holds(
        &main_fn("alloc, panic", "let value: Box<i64> @[0] = Box.new(9); 3"),
        3,
        "",
    );
    assert_eq!(stats.allocations, 1);
    violates(
        "fn make() -> Box<i64> @[0] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} { make(); 0 }",
        "result graded @[0] would silently discard",
    );
    violates(
        "fn f(b: Box<i64> @[0]) -> i64 ! {} { 0 }
         fn main() -> i64 ! {alloc, panic} { f(Box.new(1)) }",
        "grade @[0] would silently discard the owning/linear value",
    );
    violates(
        "#[linear] struct Token { id: i64 }
         fn main() -> i64 ! {} { let t: Token @[0] = Token { id: 1 }; 0 }",
        "silently discard the linear obligation",
    );
}

#[test]
fn e5_proof_erasure_is_separate_from_grade_zero() {
    // An @[0] scalar may be named by an erased proof type: a compile-time
    // observation, not a runtime use.
    holds(
        "fn graded(n: i64 @[0], erased p: Eq<i64, n, n>) -> i64 ! {} { 7 }
         fn main() -> i64 ! {panic} { graded(1, refl::<i64>(1)) }",
        7,
        "",
    );
    // A graded erased proof parameter is rejected.
    violates(
        "fn f(erased p: {1 == 1} @[1]) -> i64 ! {} { 1 }
         fn main() -> i64 ! {} { f(_) }",
        "cannot carry a usage grade",
    );
}

const USAGE: &str = "algebra Usage {
    elements { None, Once }
    zero = None; one = Once;
    add {
        None + None = None, None + Once = Once,
        Once + None = Once, Once + Once = Once,
    }
    mul {
        None * None = None, None * Once = None,
        Once * None = None, Once * Once = Once,
    }
}";

#[test]
fn e6_algebra_zero_erases_but_an_idempotent_one_is_not_exactly_once() {
    holds(
        &format!(
            "{USAGE}
             fn main() -> i64 ! {{io, panic}} {{
                 let z: i64 @[Usage.None] = {{ print_i64(3); 1 }};
                 let o: i64 @[Usage.Once] = 2;
                 o + o + o
             }}"
        ),
        6,
        "3\n",
    );
    violates(
        &format!(
            "{USAGE}
             fn main() -> i64 ! {{panic}} {{ let z: i64 @[Usage.None] = 1; z }}"
        ),
        "graded @[Usage.None] is not used consistently",
    );
    // Builtin @[1] stays exactly one physical observation.
    violates(
        &main_fn("panic", "let o: i64 @[1] = 2; o + o"),
        "used 2 time(s)",
    );
}

// ---------------------------------------------------------------------------
// Section 5: boundaries
// ---------------------------------------------------------------------------

const ASK: &str = "handle Ask: i64 -> i64 with fn(
    x: i64,
    resume: linear once fn(i64) -> i64 ! {},
) -> i64 ! {panic} { let r = resume(x + 1); r * 2 }";

const MULTI: &str = "handle Op: i64 -> i64 with fn(
    x: i64,
    resume: fn(i64) -> i64 ! {},
) -> i64 ! {panic} { let a = resume(1); let b = resume(2); a + b }";

#[test]
fn one_shot_frames_preserve_both_zones() {
    holds(
        &main_fn(
            "alloc, panic",
            &format!("{ASK} {{ let once: i64 @[1] = 5; let a = perform Ask(0); a + once }}"),
        ),
        12,
        "",
    );
    let stats = holds(
        &main_fn(
            "alloc, panic",
            &format!(
                "{ASK} {{ let b: Box<i64> @[1] = Box.new(7); let a = perform Ask(0); a + Box.take(b) }}"
            ),
        ),
        16,
        "",
    );
    assert_eq!(stats.allocations, stats.deallocations);
    violates(
        &main_fn(
            "alloc, panic",
            &format!("{ASK} {{ let once: i64 @[1] = 5; let a = perform Ask(0); a }}"),
        ),
        "used 0 time(s)",
    );
}

#[test]
fn multishot_frames_carry_only_unrestricted_copyable_slots() {
    holds(
        &main_fn(
            "panic",
            &format!("{MULTI} {{ let n = 10; let v = perform Op(0); v + n }}"),
        ),
        23,
        "",
    );
    violates(
        &main_fn(
            "panic",
            &format!("{MULTI} {{ let n: i64 @[1] = 10; let v = perform Op(0); v + n }}"),
        ),
        "owned, linear, or graded and cannot be copied",
    );
    violates(
        &main_fn(
            "alloc, panic",
            &format!("{MULTI} {{ let b = Box.new(1); let v = perform Op(0); v + Box.take(b) }}"),
        ),
        "owned, linear, or graded and cannot be copied",
    );
}

#[test]
fn erased_slots_are_not_captured_across_a_perform() {
    holds(
        &main_fn(
            "io, panic",
            &format!(
                "{ASK} {{ let z: i64 @[0] = {{ print_i64(4); 1 }}; let a = perform Ask(0); a }}"
            ),
        ),
        2,
        "4\n",
    );
    violates(
        &main_fn(
            "panic",
            &format!("{ASK} {{ let z: i64 @[0] = 1; let a = perform Ask(0); a + z }}"),
        ),
        "grade @[0] forbids runtime observation",
    );
}

#[test]
fn task_results_with_obligations_are_delivered_not_dropped() {
    let stats = holds(
        "use std.task.TaskExit;
         fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
         fn main() -> i64 ! {alloc, panic, suspend} {
             Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                 let task: Task<Box<i64>> = Task.spawn(make);
                 match Task.join(task) {
                     TaskExit.Completed(b) => Box.take(b),
                     TaskExit.Cancelled => 0,
                 }
             })
         }",
        42,
        "",
    );
    assert!(stats.allocations >= 1, "{stats:?}");
    violates(
        "fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }
         fn main() -> i64 ! {alloc, panic, suspend} {
             Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                 let task: Task<Box<i64>> = Task.spawn(make);
             });
             0
         }",
        "linear",
    );
}

// ---------------------------------------------------------------------------
// GRADE-ARROW-AXES: parameter grades and closure mode are independent axes
// ---------------------------------------------------------------------------

/// A `linear once fn(i64 @[0]) -> i64`: it captures a must-use `@[1]` value
/// and erases its parameter.
const LINEAR_ERASED: &str =
    "let k: i64 @[1] = 5; let f = fn(x: i64 @[0]) -> i64 ! {panic} { k + 1 };";

#[test]
fn linear_once_never_widens_through_an_erased_position_adapter() {
    // The grade axis may adapt the erased parameter, but only to another
    // linear-once target, which must then be called exactly once.
    for target in [
        "linear once fn(i64) -> i64 ! {panic}",
        "linear once fn(i64 @[1]) -> i64 ! {panic}",
        "linear once fn(i64 @[0]) -> i64 ! {panic}",
    ] {
        let stats = holds(
            &main_fn(
                "alloc, panic",
                &format!("{LINEAR_ERASED} let g: {target} = f; g(1)"),
            ),
            6,
            "",
        );
        assert!(stats.allocations >= 1, "{target}: {stats:?}");
        violates(
            &main_fn(
                "alloc, panic",
                &format!("{LINEAR_ERASED} let g: {target} = f; 0"),
            ),
            "linear value is not consumed",
        );
    }
    holds(
        &format!(
            "fn use_lin(g: linear once fn(i64) -> i64 ! {{panic}}) -> i64 ! {{panic}} {{ g(2) }}
             {}",
            main_fn("alloc, panic", &format!("{LINEAR_ERASED} use_lin(f)"))
        ),
        6,
        "",
    );
    // Neither a grade change nor the erased adapter widens it to `once`.
    for target in [
        "once fn(i64) -> i64 ! {panic}",
        "once fn(i64 @[0]) -> i64 ! {panic}",
        "fn(i64) -> i64 ! {panic}",
    ] {
        violates(
            &main_fn(
                "alloc, panic",
                &format!("{LINEAR_ERASED} let g: {target} = f; g(1)"),
            ),
            "type mismatch: expected",
        );
    }
    violates(
        &format!(
            "fn use_once(g: once fn(i64) -> i64 ! {{panic}}) -> i64 ! {{panic}} {{ g(2) }}
             {}",
            main_fn("alloc, panic", &format!("{LINEAR_ERASED} use_once(f)"))
        ),
        "found linear once fn(i64 @[0])",
    );
    // Two steps: first a grade change that stays linear, then the mode.
    violates(
        &main_fn(
            "alloc, panic",
            &format!(
                "{LINEAR_ERASED}
                 let g: linear once fn(i64 @[1]) -> i64 ! {{panic}} = f;
                 let h: once fn(i64) -> i64 ! {{panic}} = g;
                 h(1)"
            ),
        ),
        "found linear once fn(i64 @[1])",
    );
    // A join with an affine alternative stays linear.
    violates(
        &main_fn(
            "alloc, panic",
            &format!(
                "{LINEAR_ERASED}
                 let c = true;
                 let g = if c {{ f }} else {{ fn(x: i64 @[0]) -> i64 ! {{panic}} {{ 1 }} }};
                 let h: once fn(i64) -> i64 ! {{panic}} = g;
                 h(1)"
            ),
        ),
        "found linear once fn(i64 @[0])",
    );
    // A generic identity cannot launder the obligation either.
    violates(
        &format!(
            "fn id<T>(x: T) -> T ! {{}} {{ x }}
             {}",
            main_fn("alloc, panic", &format!("{LINEAR_ERASED} let g = id(f); 0"))
        ),
        "linear value is not consumed",
    );
}

#[test]
fn the_grade_axis_is_checked_regardless_of_the_mode() {
    // Reverse erasure is rejected for every mode.
    for (lambda, target) in [
        (
            "let k: i64 @[1] = 5; let f = fn(x: i64) -> i64 ! {panic} { k + x };",
            "linear once fn(i64 @[0]) -> i64 ! {panic}",
        ),
        (
            "let b = Box.new(5); let f = fn(x: i64) -> i64 ! {panic} { Box.take(b) + x };",
            "once fn(i64 @[0]) -> i64 ! {panic}",
        ),
        (
            "let f = fn(x: i64) -> i64 ! {panic} { x };",
            "fn(i64 @[0]) -> i64 ! {panic}",
        ),
    ] {
        violates(
            &main_fn("alloc, panic", &format!("{lambda} let g: {target} = f; 0")),
            "type mismatch: expected",
        );
    }
    // An exact grade cannot be disguised as another exact grade, in any mode.
    violates(
        &main_fn(
            "alloc, panic",
            "let k: i64 @[1] = 5; let f = fn(x: i64 @[2]) -> i64 ! {panic} { k + x + x };
             let g: linear once fn(i64 @[1]) -> i64 ! {panic} = f; g(1)",
        ),
        "type mismatch: expected",
    );
}

#[test]
fn the_mode_axis_is_checked_regardless_of_grades() {
    // An affine `once` source never becomes a copyable `fn`, even when the
    // erased adapter is needed anyway.
    violates(
        &main_fn(
            "alloc, panic",
            "let b = Box.new(5); let f = fn(x: i64 @[0]) -> i64 ! {panic} { Box.take(b) };
             let g: fn(i64) -> i64 ! {panic} = f; g(1)",
        ),
        "type mismatch: expected fn(i64)",
    );
    // An affine erased-parameter closure through the adapter: the source
    // environment is released exactly once.
    let stats = holds(
        &main_fn(
            "alloc, panic",
            "let b = Box.new(5); let f = fn(x: i64 @[0]) -> i64 ! {panic} { Box.take(b) };
             let g: once fn(i64) -> i64 ! {panic} = f; g(1)",
        ),
        5,
        "",
    );
    assert!(stats.allocations >= 2, "{stats:?}");
    // Dropping the adapted affine closure uncalled also releases the box.
    holds(
        &main_fn(
            "alloc, panic",
            "let b = Box.new(5); let f = fn(x: i64 @[0]) -> i64 ! {panic} { Box.take(b) };
             let g: once fn(i64) -> i64 ! {panic} = f; 4",
        ),
        4,
        "",
    );
    // A copyable erased-parameter function used at a linear-once target
    // must be called exactly once.
    holds(
        "fn skip(x: i64 @[0]) -> i64 ! {} { 7 }
         fn main() -> i64 ! {alloc, panic} { let g: linear once fn(i64) -> i64 ! {} = skip; g(1) }",
        7,
        "",
    );
    violates(
        "fn skip(x: i64 @[0]) -> i64 ! {} { 7 }
         fn main() -> i64 ! {alloc, panic} { let g: linear once fn(i64) -> i64 ! {} = skip; 0 }",
        "linear value is not consumed",
    );
}

#[test]
fn an_unannotated_target_parameter_is_one_pass_of_a_copyable_value() {
    // Documented behaviour (grade-model.md section 3): an unannotated
    // parameter has demand 1 at the call and the callee may copy it, so a
    // source graded @[2] stands behind it exactly as `fn dup(x: i64)` does.
    holds(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn dup(x: i64) -> i64 ! {panic} { x + x }
         fn apply(f: fn(i64) -> i64 ! {panic}, v: i64) -> i64 ! {panic} { f(v) }
         fn main() -> i64 ! {panic} {
             let a: i64 @[1] = 3;
             let b: i64 @[1] = 4;
             apply(twice, a) + dup(b)
         }",
        14,
        "",
    );
    // An exact target is not that: @[2] is not @[1].
    violates(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn main() -> i64 ! {} { let f: fn(i64 @[1]) -> i64 ! {panic} = twice; 0 }",
        "type mismatch: expected fn(i64 @[1])",
    );
}
