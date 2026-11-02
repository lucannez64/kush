# Bounded effect exclusion and finite row subtraction

Status: implemented for executable function and method effect-row binders.
`<e: Effects - alloc>` and `<e: Effects - (alloc | suspend)>` restrict which
concrete rows a specialization may supply. Separately, a declared **effect row**
may union, subtract, and name a declared row alias, as in `{e - io}`,
`{(e | alloc) - io}`, or `{IoAlloc}`. This is a finite Boolean row algebra over
the four concrete effects. The runtime effect bitset and its representation are
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
alias     = "effect" "row" NAME "=" "{" row ("," row)* "}" ";"
```

An effect row alias is transparent and expands to the union of its elements
wherever an effect row is written, including inside a subtraction. Aliases may
name other aliases; a cycle is rejected instead of being unfolded forever. An
alias does not take arguments and cannot be used as a runtime type.

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
- An alias such as `effect row IoAlloc = {io, alloc};` denotes exactly its
  expanded elements. `{IoAlloc, panic}` and `{io, alloc, panic}` are the same
  row, and `e - IoAlloc` subtracts both alias bits.

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
`solve_effect_constraints` solves the group with a **per-bit** Boolean solver.
The four concrete effects are independent bits and every row operation is
bitwise, so one bit has `2^n` assignments instead of `16^n` whole rows. The
supported decidable fragment is:

- up to **16** unbound row variables per call group (`2^16` assignments per
  effect bit, solved independently); a larger group is rejected with a request
  for explicit `::<...>` specialization;
- every row equation is an inclusion (the declared row must cover the actual
  callable row), with arbitrarily nested union and subtraction inside the
  declared row and inside row aliases;
- a row variable bound by an explicit specialization is evaluated directly and
  is not part of the remaining assignment search;
- a variable that no constraint mentions is **defaulted to its principal least
  row**: `{}` when the binder has no lower bound, or exactly the bits required
  by `<e: Effects + ...>` otherwise. Defaulting is sound because the callee body
  is rechecked under the chosen specialization; a body that performs an effect
  outside its declared row is rejected before the call can hide it;
- a valid solution must be **unique componentwise-minimal**. For one bit, the
  bitwise AND of every valid assignment is the unique minimal assignment exactly
  when it is itself valid; otherwise several incomparable minimal assignments
  exist and the call is reported as ambiguous instead of choosing one
  arbitrarily. For monotone union-only rows this is the principal row;
  subtraction is still finite, and the same uniqueness check applies;
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

This is a finite Boolean row solver, not an infinite row-unification calculus.
Lower (`+`) and upper/exclusion (`-`) bounds are both finite domain
restrictions; declared rows may additionally union and subtract row terms, and
a row alias expands recursively to a finite union. Because every row is a
four-bit vector, "unification" is exactly solving the accumulated inclusion
constraints: there is no recursive row structure left to unify, and the
principal solution is unique when the per-bit check above succeeds. Exceeding
the four-bit universe or the 16-variable per-group budget is an explicit
diagnostic.

Row aliases without parameters keep the expansion finite and decidable.
Parameterized row aliases, a first-class row *value* type, a row equality
predicate, and user-defined effect universes remain outside this subset.

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

- Row aliases are finite, non-generic unions. Parameterized aliases, first-class
  row values, row equality constraints, and subtyping on bound sets are absent.
- An unconstrained open row variable defaults to its principal least row; there
  is no separate "must be mentioned" error anymore.
- Subtraction is a finite bit operation over the same four effects, available
  on the declared side of a row and in effects visible to the solver. It is not
  a general set-difference constraint language for arbitrary first-class rows.
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
  `#[noalloc]`/`#[nosuspend]` unconstrained-contract rejection, principal
  defaults with and without lower bounds, per-bit solving of five simultaneous
  row variables, recursive row aliases and cycle rejection, alias hiding
  attempts, and nested row subtraction on declarations and higher-order
  callback rows.
