//! Bounded concrete effect exclusion on effect-row binders.
//!
//! `<e: Effects - alloc>` and `<e: Effects - (alloc | suspend)>` restrict which
//! concrete rows a specialization may supply. They are a bound on valid
//! specialization, not row subtraction: the declaration's own effect row is
//! unchanged and its body may still perform every effect the row declares.
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
