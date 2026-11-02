//! Bounded concrete effect exclusion and finite row subtraction.
//!
//! `<e: Effects - alloc>` and `<e: Effects - (alloc | suspend)>` restrict which
//! concrete rows a specialization may supply. Separately, a declared row may
//! subtract effects (`{e - io}`) inside the finite four-bit row algebra.
use kush::executable::{MemoryStats, check};

fn run(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats)
}

fn value(source: &str) -> i64 {
    run(source).0
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

/// Run the checked program natively as well as in the reference evaluator.
/// The native backend observes the same compile-time effect bitset, so a
/// positive constrained program must compile and run identically.
fn native_agrees(source: &str, expected: i64) {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("effect-constraints-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    let _ = (source, expected);
}

#[test]
fn inferred_callback_row_must_respect_the_exclusion() {
    let source = "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 f(x)
             }
             fn main() -> i64 ! {panic} { apply(inc, 41) }";
    assert_eq!(value(source), 42);
    native_agrees(source, 42);
    // An explicit empty/pure row is also allowed.
    assert_eq!(
        value(
            "fn id(x: i64) -> i64 ! {} { x }
             fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 f(x)
             }
             fn main() -> i64 ! {panic} { apply(id, 42) }"
        ),
        42
    );
}

#[test]
fn explicit_effect_arguments_are_checked() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 f(x)
             }
             fn main() -> i64 ! {panic} { apply::<panic>(inc, 41) }"
        ),
        42
    );
    assert_eq!(
        value(
            "fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
             fn apply<e: Effects - (alloc | suspend)>(
                 f: fn(i64) -> i64 ! {e}, x: i64
             ) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {io, panic} { apply::<io | panic>(io_inc, 41) }"
        ),
        42
    );
    // The same union may be written without redundant parentheses.
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn apply<e: Effects - alloc | suspend>(
                 f: fn(i64) -> i64 ! {e}, x: i64
             ) -> i64 ! {panic, e} { f(x) }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
}

#[test]
fn noalloc_and_nosuspend_contracts_accept_fully_constrained_rows() {
    // A `noalloc` function may quantify over a row that can never contain
    // alloc, including a callback that performs the remaining effects.
    assert_eq!(
        value(
            "#[noalloc]
             fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 f(x)
             }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    assert_eq!(
        value(
            "#[nosuspend]
             fn apply<e: Effects - suspend>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 f(x)
             }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    assert_eq!(
        value(
            "#[noalloc]
             #[nosuspend]
             fn apply<e: Effects - (alloc | suspend)>(
                 f: fn(i64) -> i64 ! {e}, x: i64
             ) -> i64 ! {panic, e} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    native_agrees(
        "#[noalloc]
         #[nosuspend]
         fn apply<e: Effects - (alloc | suspend)>(
             f: fn(i64) -> i64 ! {e}, x: i64
         ) -> i64 ! {panic, e} { f(x) }
         fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} { apply(inc, 41) }",
        42,
    );
}

#[test]
fn a_forwarded_row_is_checked_at_the_inner_specialization() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn inner<d: Effects - alloc>(f: fn(i64) -> i64 ! {d}, x: i64) -> i64 ! {panic, d} {
                 f(x)
             }
             fn outer<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
                 inner::<e>(f, x)
             }
             fn main() -> i64 ! {panic} { outer(inc, 41) }"
        ),
        42
    );
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn inner<d: Effects - alloc>(f: fn(i64) -> i64 ! {d}, x: i64) -> i64 ! {panic, d} {
             f(x)
         }
         fn outer<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
             inner::<e>(f, x)
         }
         fn main() -> i64 ! {alloc, panic} { outer(alloc_id, 1) }",
        "is excluded by",
    );
    // Inference of the inner row from the forwarded callable is checked too.
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn inner<d: Effects - alloc>(f: fn(i64) -> i64 ! {d}, x: i64) -> i64 ! {panic, d} {
             f(x)
         }
         fn outer<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
             inner(f, x)
         }
         fn main() -> i64 ! {alloc, panic} { outer(alloc_id, 1) }",
        "is excluded by",
    );
}

#[test]
fn allocating_or_suspending_specializations_are_rejected() {
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
             f(x)
         }
         fn main() -> i64 ! {alloc, panic} { apply::<alloc | panic>(alloc_id, 1) }",
        "is excluded by",
    );
    rejects(
        "fn suspend_id(x: i64) -> i64 ! {suspend, panic} { x }
         fn apply<e: Effects - suspend>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
             f(x)
         }
         fn main() -> i64 ! {suspend, panic} { apply::<suspend | panic>(suspend_id, 1) }",
        "is excluded by",
    );
    // An inferred row that includes the excluded effect is rejected too.
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn apply<e: Effects - alloc>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
             f(x)
         }
         fn main() -> i64 ! {alloc, panic} { apply(alloc_id, 1) }",
        "is excluded by",
    );
}

#[test]
fn an_unconstrained_row_variable_keeps_the_contract_rejection() {
    rejects(
        "#[noalloc]
         fn poly<e: Effects>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e} { f(1) }
         fn main() -> i64 ! {panic} { 42 }",
        "noalloc contracts cannot be effect-polymorphic",
    );
    rejects(
        "#[nosuspend]
         fn poly<e: Effects>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e} { f(1) }
         fn main() -> i64 ! {panic} { 42 }",
        "nosuspend contracts cannot be effect-polymorphic",
    );
    // Every row variable must exclude the effect; one unconstrained variable
    // keeps the declaration unsound and rejected.
    rejects(
        "#[noalloc]
         fn poly<e: Effects - alloc, d: Effects>(
             f: fn(i64) -> i64 ! {e}, g: fn(i64) -> i64 ! {d}
         ) -> i64 ! {panic, e, d} { f(g(1)) }
         fn main() -> i64 ! {panic} { 42 }",
        "noalloc contracts cannot be effect-polymorphic",
    );
    // A fixed forbidden effect is still rejected even when every row variable
    // is constrained.
    rejects(
        "#[noalloc]
         fn poly<e: Effects - alloc>(x: i64) -> i64 ! {alloc, e} { x }
         fn main() -> i64 ! {panic} { 42 }",
        "noalloc contract forbids the alloc effect",
    );
    rejects(
        "#[nosuspend]
         fn poly<e: Effects - suspend>(x: i64) -> i64 ! {suspend, e} { x }
         fn main() -> i64 ! {panic} { 42 }",
        "nosuspend contract forbids the suspend effect",
    );
}

#[test]
fn constraints_are_rejected_on_non_effects_binders_and_unsupported_declarations() {
    rejects(
        "fn f<T: Type - alloc>(x: T) -> T ! {panic} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "effect exclusions require an effect-row binder",
    );
    rejects(
        "type Mapper<e: Effects - alloc> = fn(i64) -> i64 ! {e};
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
    rejects(
        "struct S<e: Effects - alloc> { x: i64 }
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
    rejects(
        "enum E<e: Effects - alloc> { A }
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
    rejects(
        "trait T<e: Effects - alloc> { fn m(self: Self) -> i64 ! {e}; }
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
    rejects(
        "total fn f<e: Effects - alloc>(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
    rejects(
        "prop P<e: Effects - alloc> { Mk }
         fn main() -> i64 ! {panic} { 0 }",
        "only supported on executable function and method effect binders",
    );
}

#[test]
fn effect_exclusions_must_name_concrete_effects() {
    rejects(
        "fn f<e: Effects - T, T: Type>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "unknown name 'T'",
    );
    // An in-scope effect or type variable is not a concrete effect.
    rejects(
        "fn f<T: Type, e: Effects - T>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "is not a concrete effect",
    );
    rejects(
        "fn f<d: Effects, e: Effects - d>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "is not a concrete effect",
    );
    rejects(
        "fn f<e: Effects - NoSuchEffect>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "unknown name 'NoSuchEffect'",
    );
    rejects(
        "fn f<e: Effects - i64>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "is not a concrete effect",
    );
    rejects(
        "fn f<e: Effects - Vec>(x: i64) -> i64 ! {e} { x }
         fn main() -> i64 ! {panic} { 0 }",
        "is not a concrete effect",
    );
}

#[test]
fn trait_and_impl_method_contracts_include_the_constraint() {
    assert_eq!(
        value(
            "trait Apply {
                 fn apply<e: Effects - alloc>(
                     self: Self, f: fn(i64) -> i64 ! {e}
                 ) -> i64 ! {panic, e};
             }
             impl Apply for i64 {
                 fn apply<e: Effects - alloc>(
                     self: Self, f: fn(i64) -> i64 ! {e}
                 ) -> i64 ! {panic, e} { f(self) }
             }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { let n = 41; n.apply(inc) }"
        ),
        42
    );
    // A materialized default method keeps the constrained binder and is checked
    // at its specialization point.
    assert_eq!(
        value(
            "trait Apply {
                 fn apply<e: Effects - alloc>(
                     self: Self, f: fn(i64) -> i64 ! {e}
                 ) -> i64 ! {panic, e} { f(self) }
             }
             impl Apply for i64 {}
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { let n = 41; n.apply(inc) }"
        ),
        42
    );
    // A trait and impl may write the same exclusion union in either order.
    assert_eq!(
        value(
            "trait Apply {
                 fn apply<e: Effects - (alloc | suspend)>(
                     self: Self, f: fn(i64) -> i64 ! {e}
                 ) -> i64 ! {panic, e};
             }
             impl Apply for i64 {
                 fn apply<e: Effects - (suspend | alloc)>(
                     self: Self, f: fn(i64) -> i64 ! {e}
                 ) -> i64 ! {panic, e} { f(self) }
             }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { let n = 41; n.apply(inc) }"
        ),
        42
    );
    // A stricter or looser implementation must not be accepted silently.
    rejects(
        "trait Apply {
             fn apply<e: Effects - alloc>(
                 self: Self, f: fn(i64) -> i64 ! {e}
             ) -> i64 ! {panic, e};
         }
         impl Apply for i64 {
             fn apply<e: Effects>(
                 self: Self, f: fn(i64) -> i64 ! {e}
             ) -> i64 ! {panic, e} { f(self) }
         }
         fn main() -> i64 ! {panic} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Apply {
             fn apply<e: Effects>(
                 self: Self, f: fn(i64) -> i64 ! {e}
             ) -> i64 ! {panic, e};
         }
         impl Apply for i64 {
             fn apply<e: Effects - alloc>(
                 self: Self, f: fn(i64) -> i64 ! {e}
             ) -> i64 ! {panic, e} { f(self) }
         }
         fn main() -> i64 ! {panic} { 0 }",
        "does not match the trait signature exactly",
    );
}

// ---------------------------------------------------------------------------
// Finite row subtraction
// ---------------------------------------------------------------------------

#[test]
fn row_subtraction_removes_concrete_effects_from_a_polymorphic_row() {
    let source = "fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
                      -> i64 ! {panic, e - io} { f(x) }
                  fn inc(x: i64) -> i64 ! {panic} { x + 1 }
                  fn main() -> i64 ! {panic} { apply(inc, 41) }";
    assert_eq!(value(source), 42);
    native_agrees(source, 42);
    // A union on the right of `-` removes every named effect.
    assert_eq!(
        value(
            "fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
                 -> i64 ! {panic, e - (io | alloc)} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
    // Subtraction is part of a higher-order row too: the callback may not be
    // specialized with the removed effect.
    rejects(
        "fn take<e: Effects>(f: fn(i64) -> i64 ! {e - io}) -> i64 ! {panic, e} { f(1) }
         fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
         fn main() -> i64 ! {io, panic} { take(io_inc) }",
        "is excluded by",
    );
    // The checked function body still needs every effect it actually performs;
    // subtraction in the declared row cannot hide the callback's io.
    rejects(
        "fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}) -> i64 ! {panic, e - io} { f(1) }
         fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
         fn main() -> i64 ! {io, panic} { apply(io_inc) }",
        "requires effects {io}",
    );
    // A row subtraction that leaves a concrete effect is still checked by the
    // enclosing row, and an explicit specialization is respected.
    assert_eq!(
        value(
            "fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
                 -> i64 ! {panic, e - io} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply::<panic>(inc, 41) }"
        ),
        42
    );
}

#[test]
fn row_subtraction_solves_principal_minimal_rows() {
    // `e - io` only needs to cover panic, so the principal (least) solution is
    // e = {panic}; the solver does not arbitrarily pick a larger row.
    let source = "fn apply<e: Effects>(f: fn(i64) -> i64 ! {e})
                      -> i64 ! {panic, e - io} { f(1) }
                  fn inc(x: i64) -> i64 ! {panic} { x + 1 }
                  fn main() -> i64 ! {panic} { apply(inc) }";
    assert_eq!(value(source), 2);
    // Two unbound rows with subtraction remain in the finite four-bit
    // universe: the solver enumerates all assignments and rejects incomparable
    // minima rather than choosing one.
    rejects(
        "fn apply<e: Effects, f: Effects>(g: fn(i64) -> i64 ! {e - io, f})
             -> i64 ! {panic, e, f} { g(1) }
         fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} { apply(inc) }",
        "incomparable minimal",
    );
}

// ---------------------------------------------------------------------------
// Named effect rows
// ---------------------------------------------------------------------------

#[test]
fn unconstrained_rows_default_to_the_principal_lower_bound() {
    // No callable argument mentions `e`, so the principal choice is `{}`.
    assert_eq!(
        value(
            "fn apply<e: Effects>(x: i64) -> i64 ! {panic, e} { x }
             fn main() -> i64 ! {panic} { apply(41) + 1 }"
        ),
        42
    );
    // A required lower bound defaults to exactly the required bits.
    assert_eq!(
        value(
            "fn apply<e: Effects + io>(x: i64) -> i64 ! {panic, e} { x }
             fn main() -> i64 ! {io, panic} { apply(41) + 1 }"
        ),
        42
    );
    rejects(
        "fn apply<e: Effects + io>(x: i64) -> i64 ! {panic, e} { x }
         fn main() -> i64 ! {panic} { apply(41) }",
        "requires effects {io}",
    );
    // Defaulting never hides the body: the body is checked under the chosen
    // empty specialization.
    rejects(
        "fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }
         fn apply<e: Effects>(x: i64) -> i64 ! {panic, e} { alloc_id(x) }
         fn main() -> i64 ! {alloc, panic} { apply(41) }",
        "requires effects {alloc}",
    );
}

#[test]
fn recursive_row_expressions_share_one_variable_with_subtraction() {
    let source = r#"
        fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn split<e: Effects>(
            f: fn(i64) -> i64 ! {e},
            g: fn(i64) -> i64 ! {e - io},
        ) -> i64 ! {panic, e} { f(g(1)) }
        fn main() -> i64 ! {io, panic} { split(io_inc, inc) }"#;
    assert_eq!(value(source), 3);
    native_agrees(source, 3);
    // The same variable cannot simultaneously require `io` and subtract it
    // from the second callback's row when the second callback performs it.
    rejects(
        "fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
         fn split<e: Effects>(
             f: fn(i64) -> i64 ! {e},
             g: fn(i64) -> i64 ! {e - io},
         ) -> i64 ! {panic, e} { f(g(1)) }
         fn main() -> i64 ! {io, panic} { split(io_inc, io_inc) }",
        "no specialization of the effect row parameters",
    );
}

#[test]
fn nested_difference_rows_are_finite_and_checked() {
    // Union and subtraction nest arbitrarily; `(e | alloc) - io - alloc`
    // leaves exactly `e - io`.
    let source = r#"
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn take<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
            -> i64 ! {panic, (e | alloc) - io - alloc} { f(x) }
        fn main() -> i64 ! {panic} { take(inc, 41) }"#;
    assert_eq!(value(source), 42);
    native_agrees(source, 42);
    rejects(
        "fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }
         fn take<e: Effects>(f: fn(i64) -> i64 ! {e})
             -> i64 ! {panic, (e | alloc) - io} { f(1) }
         fn main() -> i64 ! {io, panic} { take(io_inc) }",
        "requires effects {",
    );
}

#[test]
fn effect_row_aliases_expand_transparently() {
    let source = "effect row IoPanic = {io, panic};
                  fn io_inc(x: i64) -> i64 ! {IoPanic} { x + 1 }
                  fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
                      -> i64 ! {panic, e} { f(x) }
                  fn main() -> i64 ! {IoPanic} { apply(io_inc, 41) }";
    assert_eq!(value(source), 42);
    native_agrees(source, 42);
    // An alias may name another alias, and may be unioned with concrete names.
    assert_eq!(
        value(
            "effect row Io = {io};
             effect row IoPanic = {Io, panic};
             fn inc(x: i64) -> i64 ! {IoPanic} { x + 1 }
             fn main() -> i64 ! {Io | panic} { inc(41) }"
        ),
        42
    );
    // Subtraction sees the expanded alias bits, never the alias name.
    assert_eq!(
        value(
            "effect row Io = {io};
             fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
                 -> i64 ! {panic, e - Io} { f(x) }
             fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn main() -> i64 ! {panic} { apply(inc, 41) }"
        ),
        42
    );
}

#[test]
fn effect_row_aliases_cannot_hide_required_effects() {
    rejects(
        "effect row IoPanic = {io, panic};
         fn io_inc(x: i64) -> i64 ! {IoPanic} { x + 1 }
         fn main() -> i64 ! {panic} { io_inc(1) }",
        "requires effects {io}",
    );
    // An alias used in a subtraction position is still checked by the body.
    rejects(
        "effect row Io = {io};
         fn io_id(x: i64) -> i64 ! {io, panic} { x }
         fn apply<e: Effects>(f: fn(i64) -> i64 ! {e})
             -> i64 ! {panic, e - Io} { f(1) }
         fn main() -> i64 ! {io, panic} { apply(io_id) }",
        "requires effects {io}",
    );
}

#[test]
fn effect_row_aliases_are_finite_and_cannot_take_arguments() {
    rejects(
        "effect row A = {B};
         effect row B = {A};
         fn main() -> i64 ! {A} { 0 }",
        "is recursive",
    );
    rejects(
        "effect row Io = {io};
         fn main() -> i64 ! {Io<i64>} { 0 }",
        "does not take arguments",
    );
    rejects(
        "effect row Io = {io};
         fn main() -> i64 ! {panic} { let x: Io = 1; x }",
        "is not a runtime type",
    );
}

// ---------------------------------------------------------------------------
// Per-bit row solver beyond three variables
// ---------------------------------------------------------------------------

#[test]
fn per_bit_solver_handles_more_than_three_unbound_rows() {
    let source = r#"
        fn f1(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn f2(x: i64) -> i64 ! {alloc, panic} { x + 1 }
        fn f3(x: i64) -> i64 ! {suspend, panic} { x + 1 }
        fn f4(x: i64) -> i64 ! {panic} { x + 1 }
        fn f5(x: i64) -> i64 ! {} { x }
        fn five<
            e1: Effects,
            e2: Effects,
            e3: Effects,
            e4: Effects,
            e5: Effects,
        >(
            g1: fn(i64) -> i64 ! {e1},
            g2: fn(i64) -> i64 ! {e2},
            g3: fn(i64) -> i64 ! {e3},
            g4: fn(i64) -> i64 ! {e4},
            g5: fn(i64) -> i64 ! {e5},
            x: i64,
        ) -> i64 ! {panic, e1, e2, e3, e4, e5} {
            g5(g4(g3(g2(g1(x)))))
        }
        fn main() -> i64 ! {io, alloc, suspend, panic} {
            five(f1, f2, f3, f4, f5, 40)
        }"#;
    assert_eq!(value(source), 44);
    native_agrees(source, 44);
    // The same group without one argument's io evidence must reject the caller
    // that omitted io, proving the solver still checks every bit.
    rejects(
        r#"
        fn f1(x: i64) -> i64 ! {io, panic} { x + 1 }
        fn f2(x: i64) -> i64 ! {panic} { x + 1 }
        fn f3(x: i64) -> i64 ! {panic} { x + 1 }
        fn f4(x: i64) -> i64 ! {panic} { x + 1 }
        fn f5(x: i64) -> i64 ! {} { x }
        fn five<
            e1: Effects,
            e2: Effects,
            e3: Effects,
            e4: Effects,
            e5: Effects,
        >(
            g1: fn(i64) -> i64 ! {e1},
            g2: fn(i64) -> i64 ! {e2},
            g3: fn(i64) -> i64 ! {e3},
            g4: fn(i64) -> i64 ! {e4},
            g5: fn(i64) -> i64 ! {e5},
            x: i64,
        ) -> i64 ! {panic, e1, e2, e3, e4, e5} {
            g5(g4(g3(g2(g1(x)))))
        }
        fn main() -> i64 ! {panic} {
            five(f1, f2, f3, f4, f5, 40)
        }"#,
        "requires effects {io}",
    );
}
