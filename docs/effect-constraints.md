# Bounded effect exclusion

Status: implemented for executable function and method effect-row binders.
`<e: Effects - alloc>` and `<e: Effects - (alloc | suspend)>` restrict which
concrete rows a specialization may supply. This is a **constraint on valid
specialization**, not row subtraction, not an effect handler, and not a new
effect. The runtime effect bitset and its representation are unchanged.

```rust
#[noalloc]
fn apply<e: Effects - alloc>(
    f: fn(i64) -> i64 ! {e},
    x: i64,
) -> i64 ! {panic, e} {
    f(x)
}

fn inc(x: i64) -> i64 ! {panic} { x + 1 }

fn main() -> i64 ! {panic} {
    apply(inc, 41)
}
```

Both the reference evaluator and the native Cranelift backend execute this
program. See also [first-class functions](functions.md) and
[structured async](async.md) for the existing effect vocabulary.

## Syntax

```text
binder   = name (":" "Effects" ("-" exclusion)?)?
exclusion = effect
          | "(" exclusion ("|" exclusion)* ")"
effect    = "io" | "alloc" | "suspend" | "panic"
```

- The binder must be a direct `Effects` row parameter. A constraint on a type,
  grade, or natural binder is rejected instead of being ignored.
- Exclusion leaves must be concrete effect names. Effect variables, aliases,
  records, and arbitrary type expressions are rejected with a diagnostic.
- A `|` union may be written with or without parentheses:
  `<e: Effects - (alloc | suspend)>` and `<e: Effects - alloc | suspend>` mean
  the same set. Duplicate names are harmless and collapse to one bit.
- A `-` lists **forbidden** specializations. It cannot add an effect and cannot
  remove an effect from the function's declared row.

Only executable function and method binders accept the constraint. Trait
parameters, data declarations (`struct`, `enum`, `prop`), constructor binders,
type aliases, and total logical functions reject it explicitly. A trait or impl
*method* may use it because a method signature has its own effect row.

## What it checks

At `Functions::instance`, the single specialization choke point shared by
explicit effect arguments, inference from callable arguments, forwarding through
an enclosing row variable, methods, and materialized trait defaults, every
effect argument is intersected with the binder's excluded set. A nonempty
intersection is an error:

```rust
fn alloc_id(x: i64) -> i64 ! {alloc, panic} { x }

fn apply<e: Effects - alloc>(
    f: fn(i64) -> i64 ! {e},
    x: i64,
) -> i64 ! {panic, e} { f(x) }

fn main() -> i64 ! {alloc, panic} {
    apply(alloc_id, 1) // error: inferred row {alloc, panic} includes alloc
}
```

The diagnostic is reported at the call or specialization site and names both the
excluded effect and the offending argument. There is no path that bypasses the
check: a local or remote call site, a nested generic forwarding the outer
variable, an inferred callable row, and an inherited default method all pass
through the same specialization step.

The constraint is *checked only*. The callee still declares and performs the
effects in its own row. For example, `apply<e: Effects - alloc>` above may still
perform `panic` and whatever `e` supplies; `alloc` is simply never a valid
specialization.

## Accumulated row constraints

A call may mention more than one effect row on its higher-order parameters,
and the same row variable may occur in several parameter types. Inference no
longer commits to the first callable argument's row. It accumulates one
**inclusion constraint** per callable argument:

```text
fixed | e1 | e2 ...  covers  actual
```

After every argument has been checked, `solve_effect_constraints` solves the
group by finite enumeration over the four-effect universe. The supported
decidable fragment is:

- up to **three** unbound row variables per call group (at most `16^3 = 4096`
  assignments); a larger group is rejected with a request for explicit
  `::<...>` specialization;
- every row equation is an inclusion (union coverage), never row subtraction;
- a row variable bound by an explicit specialization is folded into the
  constraint's fixed part before solving;
- a variable that no constraint mentions is an error, not `{}`, because
  defaulting it could hide an effect promised by the caller;
- a valid solution must be **unique componentwise-minimal**. Several
  incomparable minimal assignments are reported as ambiguous instead of
  choosing one arbitrarily;
- an exclusion bound (`<e: Effects - io>`) removes bits from the variable's
  finite domain. If an argument requires an excluded effect, the diagnostic
  names the excluded effect and the row parameter.

For example, a shared row variable receives the union of every argument:

```rust
fn inc(x: i64) -> i64 ! {panic} { x + 1 }
fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }

fn two<e: Effects>(
    f: fn(i64) -> i64 ! {e},
    g: fn(i64) -> i64 ! {e},
    x: i64,
) -> i64 ! {panic, e} { g(f(x)) }

fn main() -> i64 ! {io, panic} { two(inc, io_inc, 1) }  // e = {io, panic}
```

Omitting `io` from `main` is rejected; the solver cannot satisfy the second
argument's evidence with a smaller row. Separate variables `e1`/`e2` are
solved from their own arguments, and a single row with two variables is
ambiguous when the actual effects can be partitioned in several ways.

`infer_function_value` uses the same solver for a generic function value: the
expected arrow's effect row is added as one more constraint, so a callable
parameter and the expected result contract are considered together.

This is a finite constraint solver, not a general row-unification calculus.
There are no lower bounds (`+ io`), no row subtraction, no polymorphic row
aliases, no recursive row constraints, and no principal inference for open
rows. Exceeding the four-bit universe or the 4096-assignment budget is an
explicit diagnostic.

## `#[noalloc]` and `#[nosuspend]`

Before this feature, these attributes rejected every effect-polymorphic
signature because a row variable could later be specialized with the forbidden
effect. They now accept a polymorphic row **only when every row variable in the
signature excludes the corresponding effect**:

```rust
#[noalloc]
#[nosuspend]
fn apply<e: Effects - (alloc | suspend)>(
    f: fn(i64) -> i64 ! {e},
) -> i64 ! {panic, e} { f(1) }
```

The relaxation is deliberately conservative:

- a fixed `alloc`/`suspend` effect in the row is still rejected;
- an unconstrained `<e: Effects>` still produces the existing
  "cannot be effect-polymorphic" error;
- a signature with several row variables rejects the attribute unless *all* of
  them exclude the effect;
- the attribute is checked at declaration time, independently of any particular
  specialization.

## Trait and impl contracts

The effect-exclusion set is part of a method's alpha-normalized contract. A
trait method and its impl method must agree on the binder, its bound, and its
excluded effects. An impl that drops an exclusion is rejected as too permissive;
an impl that adds one is rejected as too strict. Default trait methods keep the
attribute and are checked when their specialization is materialized.

## Boundaries

- No row subtraction, row difference, aliasing rows, or subtyping on exclusion
  sets.
- No lower bounds (`<e: Effects + alloc>`), no inference of exclusion lists from
  a body, and no general recursive row unification. The implemented solver is
  the finite inclusion/equality group described above.
- Only the four concrete effects `io`, `alloc`, `suspend`, and `panic` may be
  excluded. There are no user-defined effects.
- Exclusions do not change runtime representation, calls, or optimization. They
  add no effect bit and generate no runtime check.
- The checker, evaluator, Cranelift backend, and C runtime remain trusted; this
  is a checked interface restriction, not a formal soundness proof.

## Implementation and tests

- `crates/kush/src/parser.rs` parses the binder suffix.
- `crates/kush/src/resolve.rs` resolves the excluded names and rejects
  non-effect binders and unsupported declaration forms.
- `crates/kush/src/runtime_types.rs` provides `effect_excludes`, which maps a
  validated binder to its concrete forbidden bits.
- `crates/kush/src/executable.rs` enforces the bound in `Functions::instance`,
  relaxes `#[noalloc]`/`#[nosuspend]`, and includes the constraint in
  `method_contract_key`.
- `crates/kush/tests/effect_constraints.rs` covers inference, explicit
  specialization, forwarding, methods and defaults, native/reference execution,
  non-effect binders, unsupported declarations, and the retained
  unconstrained-contract rejection.
