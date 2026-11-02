# Bounded effect exclusion and finite row subtraction

Status: implemented for executable function and method effect-row binders.
`<e: Effects - alloc>` and `<e: Effects - (alloc | suspend)>` restrict which
concrete rows a specialization may supply. Separately, a declared **effect row**
may subtract concrete effects or row variables with `{e - io}`. This is a
finite Boolean row algebra over the four concrete effects, not a general row
unification calculus. The runtime effect bitset and its representation are
unchanged.

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
binder    = name (":" "Effects" ("+" includes)? ("-" exclusion)?)?
inclusion = effect
          | "(" inclusion ("|" inclusion)* ")"
exclusion = effect
          | "(" exclusion ("|" exclusion)* ")"
effect    = "io" | "alloc" | "suspend" | "panic"
row       = effect ("|" effect)* ("-" effect)*
```

- The binder must be a direct `Effects` row parameter. A constraint on a type,
  grade, or natural binder is rejected instead of being ignored.
- Exclusion and inclusion leaves are concrete effect names. Effect variables,
  aliases, records, and arbitrary type expressions are rejected with a
  diagnostic.
- A `|` union may be written with or without parentheses:
  `<e: Effects - (alloc | suspend)>` and `<e: Effects - alloc | suspend>` mean
  the same set. Duplicate names are harmless and collapse to one bit.
- A `-` on a binder lists **forbidden** specializations. It cannot add an
  effect and cannot remove an effect from the function's declared row.
- In a declared effect row, `-` is row subtraction: `{e - io}` removes every
  bit selected by `io` from the row selected by `e`. Subtraction binds looser
  than `|`, so `(a | b) - c` needs parentheses when the union should be
  subtracted. Both sides may be concrete effects or row variables.
- Row union is idempotent: `{panic, panic}` denotes the same bit as
  `{panic}`.

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
**row inclusion constraint** per callable argument:

```text
row-expression  covers  actual
```

where a row expression is a finite union/subtraction tree over the four
concrete bits and row variables. After every argument has been checked,
`solve_effect_constraints` solves the group by finite enumeration over the
four-effect universe. The supported decidable fragment is:

- up to **three** unbound row variables per call group (at most
  `16^3 = 4096` assignments); a larger group is rejected with a request for
  explicit `::<...>` specialization;
- every row equation is an inclusion (the declared row must cover the actual
  callable row), with union and subtraction inside the declared row;
- a row variable bound by an explicit specialization is evaluated directly and
  is not part of the remaining assignment search;
- a variable that no constraint mentions is an error, not `{}`, because
  defaulting it could hide an effect promised by the caller;
- a valid solution must be **unique componentwise-minimal**. Several
  incomparable minimal assignments are reported as ambiguous instead of
  choosing one arbitrarily. For monotone union-only rows this is the principal
  row; subtraction is still finite, but it can make the solution set smaller or
  empty and the same uniqueness check applies;
- an exclusion bound (`<e: Effects - io>`) removes bits from the variable's
  finite domain. If an argument requires an excluded effect, the diagnostic
  names the excluded effect and the row parameter;
- an inclusion bound (`<e: Effects + io>`) removes assignments that omit the
  required bits. The bound is checked at the same specialization choke point as
  exclusions, so an explicit `::<...>` argument that omits a required effect is
  rejected, and a lower bound that conflicts with an exclusion in the same
  binder is rejected at declaration time. `#[noalloc]`/`#[nosuspend]` treat a
  required forbidden effect as a declaration error rather than a guarantee.

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

Row subtraction is checked at each specialization rather than believed:

```rust
fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64)
    -> i64 ! {panic, e - io} { f(x) }

fn io_inc(x: i64) -> i64 ! {io, panic} { x + 1 }

fn main() -> i64 ! {io, panic} { apply(io_inc, 1) }
// rejected: the specialization has e = {io, panic}, so e - io = {panic},
// but the body still calls f and requires the io it promised.
```

The declared row is recomputed for every specialization. Subtracting an effect
from a declaration is not a promise that the body no longer performs it; the
body's own `require` check still sees the concrete callable row.

This is a finite Boolean row solver, not a general row-unification calculus.
Lower (`+`) and upper/exclusion (`-`) bounds are both finite domain
restrictions; declared rows may additionally union and subtract row terms.
There is no row difference predicate, no polymorphic row aliases, no recursive
row constraints, and no principal inference for an open row variable that no
constraint mentions. Exceeding the four-bit universe or the 4096-assignment
budget is an explicit diagnostic.

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

- No row aliases, no subtyping on bound sets, and no recursive row unification.
- An unconstrained open row variable is still an error rather than defaulting
  to `{}`; the solver has a principal minimal solution only when every variable
  is mentioned by at least one constraint.
- Subtraction is a finite bit operation over the same four effects. It is not a
  general set-difference constraint language for arbitrary first-class rows.
- Only the four concrete effects `io`, `alloc`, `suspend`, and `panic` may be
  excluded or subtracted. There are no user-defined effects.
- Exclusions and subtraction do not change runtime representation, calls, or
  optimization. They add no effect bit and generate no runtime check.
- The checker, evaluator, Cranelift backend, and C runtime remain trusted; this
  is a checked interface restriction, not a formal soundness proof.

## Implementation and tests

- `crates/kush/src/parser.rs` parses the binder suffix and effect-row
  subtraction.
- `crates/kush/src/resolve.rs` resolves the excluded names and rejects
  non-effect binders and unsupported declaration forms.
- `crates/kush/src/runtime_types.rs` provides `EffectRowTerm`,
  `effect_row_term`, and `effect_excludes`; rows are evaluated over the finite
  four-bit universe.
- `crates/kush/src/executable.rs` enforces the bound in `Functions::instance`,
  relaxes `#[noalloc]`/`#[nosuspend]`, includes the constraint in
  `method_contract_key`, and solves accumulated inclusion constraints by finite
  enumeration.
- `crates/kush/tests/effect_constraints.rs` covers inference, explicit
  specialization, forwarding, methods and defaults, native/reference execution,
  non-effect binders, unsupported declarations, the retained
  unconstrained-contract rejection, and row subtraction on declarations and
  higher-order callback rows.
