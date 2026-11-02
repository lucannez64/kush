# Runtime scalar indices in erased proofs

Status: implemented restricted fragment. An executable function may have an
erased logical parameter whose type depends on an earlier runtime parameter or
local of an admitted machine carrier (`i64`, `Bool`, or `Unit`).
The runtime value is a symbolic kernel index, not a proof: the kernel checks the
proposition, and the proof is still erased before reference evaluation and
native lowering.

```sh
cargo run -p kush -- check examples/runtime-indices.kush
cargo run -p kush -- eval  examples/runtime-indices.kush   # exit status 42
cargo run -p kush -- run   examples/runtime-indices.kush   # native exit status 42
cargo test --offline --test runtime_indices
cargo test --offline --test kernel
```

This extends the closed/open erased-proof boundary documented in
[propositions](propositions.md), [logical data](logical-data.md), and
[dependent indices](dependent-indices.md). It is an independently checking
implementation, not a mechanized soundness proof.

## 1. The shape

```rust
total fn truth() -> Eq<i64, 0, 0> ! {} { refl::<i64>(0) }

fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }

fn main() -> i64 ! {panic} {
    let five: i64 = 5;
    keep(five, refl::<i64>(five))       // symbolic local
        + keep(10, refl::<i64>(10))     // literal frozen at the call site
        + keep(0, truth())              // checked logical definition
}
```

`n` remains an ordinary runtime parameter. It is absent from the proof's runtime
representation only because `same` is erased; `n` itself is still passed and
returned normally. At the call site the callee's erased type becomes
`Eq<i64, a, a>` for the frozen actual `a`, and the kernel checks `refl(i64, a)`
against it.

User-defined predicates and logical data may be indexed by the same carriers, so
this is not an equality-only special case:

```rust
prop ZeroI<n: i64> { Zero: ZeroI<0> }
prop IsTrue<b: Bool> { Yes: IsTrue<true>, Also: IsTrue<true> }
prop UnitTag<u: Unit> { Mk: UnitTag<()> }
total enum Tag<n: i64> { Mk: Tag<n> }

fn keep_zero(n: i64, erased p: ZeroI<n>) -> i64 ! {} { n }
fn keep_true(b: Bool, erased p: IsTrue<b>) -> i64 ! {} { 4 }
```

The payload-less constructor results use type-directed machine literals:
`ZeroI<0>` reads `0` as `i64`, while `IsTrue<true>` and `UnitTag<()>` use the
`Bool` and `Unit` carriers. Without that expected carrier, an integer in a type
position remains the mathematical `Nat` literal it has always been.

## 2. Kernel model

The kernel has three new carrier **types** and their canonical literals:

```text
i64 : Universe(0)       n : i64   =>   n : i64
Bool : Universe(0)      true, false : Bool
Unit : Universe(0)      () : Unit
```

A literal stores its checked host value (`i64` stores an `i64`, `Bool` a bool,
`Unit` the unique value). There is no separate source-level literal form that
can produce an out-of-range kernel value: surface elaboration parses through the
host range check before constructing a term.

The kernel deliberately provides:

- **no machine arithmetic, casts, comparisons, or eliminator** for these
  carriers. A runtime function call is never reduced or treated as a total
  operation, and `n + 1` is not a kernel index;
- **no `Nat` conversion**. `Eq<i64, n, n>` and `Eq<Nat, n, n>` are different
  propositions; the latter is rejected when `n` is a machine scalar. Machine
  arithmetic is not assumed to be mathematical unbounded arithmetic;
- **no proof status**. `Eq<i64, x, y>` is Type-valued exactly like other
  equality, and `n : i64` is never a proof of a proposition. `proof_open` is
  false for a machine scalar;
- **no reduction budget escape**. Literal inference/normalization is charged to
  the same kernel budget, and invalid or ill-typed literals fail checking.

Machine carrier types and literals are ordinary kernel terms, so `Eq`, `refl`,
transport, equality elimination, user `total enum`/`prop` families, and their
checked eliminators all work over them. There is no axiom and no unchecked
global.

## 3. Open contexts and call-site substitution

An erased logical parameter is elaborated in the callee's open kernel context.
That context now contains, in source order:

1. earlier erased logical binders (their proposition or logical type);
2. earlier runtime scalar parameters and locals (`i64`, `Bool`, `Unit` as
   hypothesis *types*), with one binder per mutable version.

Later parameter types may mention both. Every entry is validated as a type
relative to the earlier entries. At a call:

1. runtime scalar actuals are translated to kernel terms in the caller context;
2. earlier proof actuals are elaborated and kernel-checked;
3. both are substituted for the callee's kernel binders, and the current
   evidence is checked against the resulting type in the caller's context.

Runtime type generics, grades, compile-time `Nat` parameters, owning values,
borrows, and containers are never added to this context. A proof type that
mentions one fails elaboration instead of approximating it.

Aliases are transparent on both sides. A logical alias such as
`type MyInt = i64;` or `type Same<T: Type, x: T> = Eq<T, x, x>;` works as an
index carrier or proof type. A structured runtime alias is still not a logical
definition and cannot enter a proof.

## 4. Freezing, mutation, and joins

The central soundness rule is:

> A proof index is frozen at its source evaluation point. It is never
> reinterpreted from the final value of a mutable binding.

Implemented consequences:

- Immutable and mutable scalar locals and parameters are admitted as symbolic
  indices. A proof use translates the **current version** of a mutable local.
  Assignment appends a fresh kernel binder for the new value instead of
  rewriting the old hypothesis; a later `refl::<i64>(n)` therefore describes
  the new value, and an old literal proof such as `refl::<i64>(5)` no longer
  establishes `Eq<i64, n, n>` after `n = 6`.
- An assignment of a canonical machine literal records that literal as the
  current index value. This is what makes `let mut n = 0; n = 6;
  keep(n, refl::<i64>(6))` check.
- A **branch join** keeps a scalar index only when both reaching branches agree.
  If both branches assign the same literal, that literal survives; if one
  branch changes the value and the other does not, or the branches disagree,
  the joined index is a fresh opaque binder. A proof about an older value is
  rejected against the new binder. The join also handles one branch that
  diverges with `return`/`panic`. A `match` joins all of its reaching arms the
  same way; every arm is checked from the scalar state before the match.
- **Leaving a nested scope** (block, `let`-pattern body, lambda, continuation)
  truncates the proof context. A scalar whose current index was introduced in
  that scope gets a fresh opaque binder at the outer level, so it can never
  alias a binder appended later for a different local.
- A **loop join** keeps a scalar index only when the body never changes it. Any
  scalar the body may assign becomes a fresh opaque binder after the loop, so a
  literal proof cannot survive a loop iteration that might have replaced the
  value, even when the loop condition is false at run time.
- An actual argument to a scalar-indexed parameter must be a canonical literal
  or the **name** of an in-scope scalar (immutable or mutable). An arbitrary
  evaluated expression such as `keep(make(3), refl::<i64>(3))` is rejected with
  a request to bind a local first. The compiler does not execute user code to
  decide an index.
- A simple `let alias = scalar` is a by-value copy. The alias denotes the
  **same frozen kernel binder** as the source at the binding point, so a proof
  about the source value applies to the alias and conversely. A later
  assignment to the source appends a new binder and leaves the alias frozen at
  the old value; using the alias to prove a proposition about the new source
  value is rejected. Chained aliases resolve to the original binder.
- A **proof-valued local** `let p = <proof>` is erased like an erased
  parameter. The right-hand side is elaborated to a checked kernel term at the
  binding point and each use re-checks that term at the current context (free
  variables are shifted as later binders are appended). A proof-valued local
  may alias another such local, may shadow, and has no runtime slot, so it
  cannot be returned, stored, or read as a runtime value.
- A closure capture of a scalar is a **copy made when the closure is
  constructed**. That copy is an independent immutable snapshot: it may index
  proofs in the lambda body even if the outer binding is later assigned. The
  lambda observes the captured value, never the final mutable value.
- Block scopes truncate symbolic binders, so a proof cannot mention a local
  after its scope. Local shadowing resolves to the innermost binder.
- A proof parameter cannot be stored in a runtime value, returned as a runtime
  value, captured as evidence, or read in a runtime branch, so there is no
  runtime location that can retain an old-value proof across mutation. Runtime
  scalar values may appear **inside proof terms** (for example as `refl`'s
  value) but a bare runtime scalar is rejected as erased evidence of a
  proposition.

The version rule is structural rather than a general def-use solver: each
assignment produces a new binder for the mutable name, and older proof terms
keep their own prefix context. It does not attempt to prove that an arbitrary
expression over a mutable local is unchanged. It never accepts a proof about an
older value after an assignment that is not known to agree on every path. The
implementation is tested by `crates/kush/tests/advanced_types_effects.rs` with
current-value proofs, old-literal rejection, unrelated versioned binders,
branch/loop join agreement and disagreement, proof-valued locals, and a frozen
closure snapshot.

## 5. Erasure, grades, ownership, and `Prop`

- Runtime scalars are ordinary copyable runtime values. Using one in an erased
  proof type adds no runtime observation, allocation, or branch. The parameter
  is still subject to its normal usage grade; a `@[0]` scalar named only by an
  erased proof type remains accepted and produces no runtime use.
- Proofs, `total fn` definitions, `prop` declarations, and machine-indexed
  logical data are erased before reference evaluation and native lowering. They
  are not stored, allocated, returned, or inspected at runtime.
- Proof irrelevance still applies only to `Prop` inhabitants. It can identify
  two proofs of `IsTrue<true>` regardless of constructor, but it cannot
  fabricate a runtime value, turn a scalar into a proof, or make
  `IsTrue<true>` equal `IsTrue<false>`.
- Only copyable machine scalars are indices. An owning enum, `Vec`, `Box`,
  borrow, slice, record, or linear capability still cannot enter an erased type.
  A proof cannot launder ownership or consume an owner.
- Ordinary calls, I/O, general recursion, and effectful code are never run
  during logical normalization. A `total fn` may depend only on checked logical
  definitions.

## 6. Diagnostics

Representative rejected forms:

```text
let mut n = 4; keep(n, refl::<i64>(3))
  -> proof does not establish the erased proposition (old literal, new value)

keep(make(3), refl::<i64>(3))
  -> a symbolic proof index must be a literal or the name of an in-scope scalar local

fn f(n: i64, erased p: Eq<Nat, n, n>)
  -> type mismatch: expected Nat, inferred Scalar(I64)

keep(false, refl::<Bool>(true))
  -> proof does not establish the erased proposition

fn consume(erased p: Eq<i64, 0, 0>); consume(n)
  -> a runtime scalar is a symbolic index, not erased evidence
```

## 7. Deliberate limits

- Only `i64`, `Bool`, and `Unit` are admitted machine carriers. `i8`/`u32`/
  `usize`/floats/`Char` and machine vectors are not kernel carriers yet. Float
  values are executable scalars but are deliberately rejected in erased proof
  indices; their bits are never reinterpreted as integers.
- There is no machine arithmetic, comparison, cast, or literal expression in
  the kernel. A constraint such as `n > 0` must use the separate erased
  arithmetic `{ ... }` fragment or an explicit logical predicate over a
  symbolic value, not machine evaluation.
- There is no implicit `i64`/`Nat` conversion and no implicit `Nat`→machine
  truncation. `Nat` stays unbounded and separate.
- Runtime `Unit` is a singleton. An admitted `Unit` hypothesis/actual is
  encoded by the canonical unit literal, so `let u: Unit = (); keep_unit(u,
  unit_proof())` works without an extra equality proof. This is a checked
  encoding for `Unit` only; there is no general singleton elimination for other
  types.
- Only simple `let` names, by-value scalar aliases, function/lambda
  parameters, scalar closure captures, and erased proof-valued locals are
  symbolic. Destructured pattern bindings and temporary compiler slots are
  conservatively not admitted. A mutable name is admitted at its current
  version; assignment appends a fresh version binder and removes any alias
  status from the assigned name.
- A branch or loop join tracks only a canonical literal that every reaching
  path agrees on. It does not solve arbitrary path equalities or machine
  arithmetic; disagreement becomes an opaque binder. Mutable captures remain
  rejected, so a closure never observes a live mutable location.
- Proof-valued locals are erased aliases of checked logical terms. There is no
  runtime proof storage, no proof-returning function, and no proof-valued
  closure capture at run time.
- An admitted local is a symbolic kernel value, not its source initializer.
  `let n = 0; keep_zero(n, zero_proof())` does not by itself identify `n` with
  the literal `0`; pass the literal directly or supply an explicit logical
  equality proof. Assignments and agreeing branch joins are the only places
  where the checker records a literal value for a binding. This conservative
  choice keeps freezing simple and avoids reusing an initializer after
  arbitrary control flow.
- Runtime scalar values cannot size inline arrays. `[T; n]` still requires a
  compile-time `Nat` length; use `Vec<T>` or `&[T]` for runtime lengths.
- There is no proof search, implicit argument, tactic, arithmetic solver, or
  user-supplied axiom. Evidence must be a checked logical term.

These are implementation budget and fragment limits, not claims that the full
[v0.1 dependent design](spec-v0.1.md) is complete.
