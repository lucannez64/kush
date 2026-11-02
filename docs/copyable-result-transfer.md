# Copyable exact-use result transfer

Status: implemented for the executable subset. A copyable `@[1]` result is a
**must-use** contract. It is deliberately distinct from an owning `@[1]`
transfer: a copyable result never becomes a move-owning value, never creates a
resource slot, and never changes the runtime representation or ABI.

## Contract

`fn f(...) -> T @[1]` where `T` is copyable (a scalar, tuple of copyables, a
copyable record/enum/union, or a borrowed view) promises that every caller
performs exactly one runtime observation of the returned value on every normal
path. The same surface grade is used for both obligations:

| Result type | `@[1]` meaning |
| --- | --- |
| owning (`Box`, `Bytes`, `Vec`, `String`, owning record/enum/union) or intrinsic `#[linear]` data | owning linear transfer: the caller acquires a resource that must be consumed exactly once |
| copyable | must-use transfer: the caller must observe the copy exactly once |

The distinction is computed from the checked result type in the executable
checker, the ownership pass, and the grade pass. It is never inferred from the
spelling of the annotation.

## Transfer and observation positions

A value-position expression transfers the obligation instead of observing it:

- `let x = f(...)` binds `x` as `@[1]` (a copyable `x` is tracked by the grade
  pass; an owning `x` is tracked by ownership);
- assignment to a binding already graded `@[1]` starts a fresh obligation;
- `return` through a function whose result is the matching copyable `@[1]`;
- block tails, `if`/`else` tails, `match` arm bodies, loop break values, and
  checked coercions preserve it.

The following positions discharge the obligation by observing the result
exactly once: a call argument, a constructor/aggregate field, a read or
projection, a match scrutinee, a `?` operand, and a capture. A capture of a
`@[1]` copyable local makes the closure `linear once`, so the closure must be
called exactly once.

The following discard positions are rejected:

- an expression statement whose value is unused;
- `let _ = ...`, a destructuring `let`, or any pattern that does not bind one
  simple name;
- `drop(...)`;
- an unused `let x = ...` binding (the grade pass requires one observation);
- assignment to an ungraded binding;
- returning through an ungraded result;
- using the value a different number of times on different paths, in a match
  guard, or across a loop back-edge.

The obligation is checked per path by the existing exact-use grade analysis.
A call result used directly as a call argument, aggregate field, or `?` operand
is observed by that operation and does not need an intermediate binding.

## Preserved ownership rules

- Copyable results are still copyable. They are not moved, not dropped as
  resources, and are not tracked by `ValueMovesLinear`.
- An owning `@[1]` result keeps all previous linear-resource rules, including
  the rejection of ungraded returns and the requirement to consume the value on
  every normal exit.
- Arrow subtyping still requires an exact result-grade match. A copyable `@[1]`
  arrow cannot be widened to an ungraded one, which could drop the obligation.
- `@[0]`, finite `n > 1`, and `many` results remain rejected for both owning and
  copyable results.

## Tests and examples

`crates/kush/tests/copyable_result_transfer.rs` covers call arguments, `let`
transfer, branch/loop/alias propagation, `?`, aggregates, captures, every
discard position, ungraded returns, the copyable/non-moving distinction, and
native/reference agreement. `crates/kush/tests/result_grade_inference.rs` covers
copyable results through result aliases.

The implementation is internal to the compiler. No runtime tag, allocation,
check, or ABI change is introduced.
