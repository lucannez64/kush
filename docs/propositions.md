# Propositions, proof irrelevance, and elided evidence

Status: implemented conservative fragment. The kernel has a `Prop` sort,
positive inductive proposition declarations (`prop`), proof irrelevance for
inhabitants of propositions, and a checked erasure boundary shared with the
executable subset. Large elimination from a user proposition is rejected. The
implementation is independently checking but is **not** a mechanized soundness
proof; the Rust implementation, compiler, and machine remain trusted.

```sh
cargo run -p kush -- check examples/finite-proofs.kush
cargo run -p kush -- eval  examples/finite-proofs.kush   # exit status 42
cargo run -p kush -- run   examples/finite-proofs.kush   # native exit status 42
cargo test --offline --test kernel
cargo test --offline --test check
cargo test --offline --test logical_data
cargo test --offline --test interop
```

Proofs are logical evidence. They are never runtime values. The surface syntax
for finite indices and constructor-local binders is described in
[logical data](logical-data.md); the separate compile-time `Nat` indices used by
arrays are described in [dependent indices](dependent-indices.md).

## 1. Sort model

The kernel has two kinds of sort:

```text
Sort ::= Type(u)     -- predicative, explicit level u : u32
       | Prop        -- the sort of propositions
```

Formation rules:

```text
Prop : Universe(0)                  -- Prop is a Type, not a Prop
Universe(u) : Universe(u + 1)       -- no Type : Type
Γ ⊢ A : s       Γ, x:A ⊢ B : Sort
----------------------------------- (Pi formation)
Γ ⊢ (x : A) -> B : sort-of-B
```

The result sort is:

- `Prop` when the codomain `B` is a proposition. This is **impredicative**:
  quantifying over any universe and returning a proposition stays in `Prop`.
- `Type(max(level(A), level(B)))` when the codomain is a Type. `level(Prop)` is
  `0`, so a proposition used as a domain does not raise a Type.

Consequences:

- There is no `Prop : Prop`. Checking `Prop` against `Prop` fails; `Prop`
  inhabits `Universe(0)`.
- There is no `Type : Type` and no cumulativity. `Type<1>` does not establish
  `Type<0>`, and `Prop` is not silently accepted where `Type<0>` is required.
- `(P : Prop) -> Prop` is a Type-level function type (returning the *sort*
  `Prop`), not a proposition. `(P : Prop) -> P` is a proposition because its
  codomain is the proposition `P`; it is a proof of a universally quantified
  proposition by impredicativity.
- A function returning a proposition has a Type-valued function type. For
  example, `fn(t: True) -> Prop ! {}` is a Type-level function from proofs of
  `True` to propositions. A function returning a *proof* has type
  `fn(t: True) -> True ! {}`, which is itself a proposition.

### Equality stays Type-valued

Built-in `Eq<A, x, y>` keeps its previous universe rule: it lives in the
carrier's universe (`Prop` carriers contribute level 0). In particular:

- `Eq` is **not** a `Prop` family in this fragment. Equality proofs are logical
  data, erased at runtime, but they are not automatically proof-irrelevant.
- `Eq<A, x, y>` and `refl::<A>(x)` accept a Type at any supported level or a
  proposition as the carrier. Equality of two proofs of the same proposition is
  inhabited by `refl` through proof irrelevance. Equality of two *different*
  propositions is not: there is no propositional extensionality.
- `refl`, `Eq.transport`, and `Eq.elim` (J) keep their existing rules and
  reduction equations. Their motives may now return either a Type or a
  proposition.
- Prop elimination cannot target an `Eq` proposition: since `Eq` is Type-valued,
  doing so would be large elimination from a proposition and is rejected. Use
  the equality eliminators directly for equality reasoning, or declare a
  `prop` family when a genuinely propositional relation is required.

Making `Eq` itself a proposition would make every equality proof irrelevant, but
would also require a cumulativity or sort-polymorphism design for existing
motive helpers (`Nat -> Type` cannot receive a `Nat -> Prop` alias). This
implementation deliberately keeps the established equality semantics instead of
silently changing it.

## 2. Proposition declarations

`prop` declares a strictly positive inductive proposition:

```rust
prop True {
    Trivial: True,
}

prop False {}

prop And<P: Prop, Q: Prop> {
    Both(left: P, right: Q): And<P, Q>,
}

prop IsZero<n: Nat> {
    ZeroIsZero: IsZero<0>,
}

prop Exists<T: Type, P: fn(x: T) -> Prop ! {}> {
    Witness(witness: T, proof: P<witness>): Exists<T, P>,
}
```

Rules:

- Every generic parameter of the `prop` becomes a family index parameter. A
  generic bounded by `Prop` is a proposition parameter; ordinary bounds such as
  `Type` and `Nat` are still available.
- The family lives in `Prop`: `True : Prop`, `And<P,Q> : Prop`, and so on.
- Constructors are unit, tuple, or named-tuple payloads. Named fields bind in
  later fields and in the result indices, just like `total enum`. Record
  payloads (`{ ... }`) are reserved for runtime enums and rejected here.
- Constructor-local binders (`FZero<n: Nat>`) are supported and are distinct
  from the family parameters. See [logical data](logical-data.md).
- Result indices are checked in the context of family parameters, constructor
  local binders, and all fields. A result must name its own family with exactly
  one index per family parameter.
- Strict positivity is the same first-order fragment as `total enum`: a
  recursive occurrence must be a whole field whose head is the family and whose
  index arguments do not mention it. Nested, higher-order, negative, and mutual
  occurrences are rejected.
- Constructor field types may be ordinary Types or propositions. A proposition
  can therefore store a witness or a proof, but its computational contents stay
  inaccessible because of the elimination restriction below.
- There is no axiom declaration, unchecked proof insertion, or assumed
  proposition. Every declared proposition has constructors and is checked.

## 3. Elimination and large-elimination restriction

`Data.elim::<D>` is available for `prop` families with the same dependent
eliminator shape as logical data:

```text
motive   : (p1:P1) -> ... -> (pk:Pk) -> D p1...pk -> Sort
branch_c : (p1:P1) -> ... -> (pk:Pk) -> (locals) -> fields with induction
           hypotheses -> motive (result indices) (c ...)
scrutinee: D a1...ak
result   : motive a1...ak scrutinee
```

The critical restriction is:

> A motive for a `prop` family must return a proposition (`Sort::Prop`).
> Elimination into `Type(u)` is rejected as large elimination.

This is the standard safe restriction for an impredicative `Prop`. It means:

- `Data.elim::<True>` with a motive returning `True`, `And<...>`, or another
  proposition is accepted.
- `Data.elim::<True>` with a motive returning `Nat` or `Eq<...>` (Type-valued)
  is rejected, even if the branch would ignore the proof.
- `False` can be eliminated into any proposition (`ex falso`), but not into a
  Type. The empty proposition therefore cannot fabricate a runtime value.
- Branches are ordinary proof terms. Because the result is a proposition, proof
  irrelevance makes the particular branch value unobservable in conversion.

Type-valued logical data (`total enum`) may still be eliminated into a
proposition. That is proof production, not large elimination from `Prop`:

```rust
total enum Even { EvenZero: Even, EvenSucc(Even): Even }
prop IsEvenHeight<e: Even> { ... }
```

`Nat.induct` and `Eq.elim` also accept proposition-valued motives:

```rust
type TrueMotiveN<n: Nat> = True;
total fn zero_t() -> True ! {} { Trivial }
total fn step_t(n: Nat, ih: True) -> True ! {} { Trivial }
total fn always_true(n: Nat) -> True ! {} {
    Nat.induct(TrueMotiveN, zero_t, step_t, n)
}
```

An abstract motive is allowed when it is a function returning propositions:

```rust
total fn elim_true(
    motive: fn(t: True) -> Prop ! {},
    branch: motive<Trivial>,
    t: True,
) -> motive<t> ! {} {
    Data.elim::<True>(motive, branch, t)
}
```

A function returning *proofs* of a fixed `P : Prop`, such as
`fn(t: True) -> P ! {}`, is not a motive: its codomain is `P`, not a sort, so
the kernel rejects it.

## 4. Proof irrelevance

Two terms are proof-irrelevant when **all** of the following hold:

1. both terms are well typed;
2. the type of each term is classified by `Prop` (the term is a proof of a
   checked proposition); and
3. those two proposition types are convertible.

Then conversion accepts them as equal even if their proof terms differ:

```rust
prop Two { First: Two, Second: Two }
total enum Indexed<p: Two> { Mk: Indexed<p> }

// Accepted: First and Second are both proofs of Two.
total fn same_proof() -> Indexed<Second> ! {} { Indexed.Mk::<First> }
```

Boundaries:

- `0` and `1` are inhabitants of `Nat`, not proofs, so they remain distinct.
- Two constructors of a Type-valued enum are not irrelevant.
- Proofs of two different propositions are not interchangeable, even if both
  are propositions. `Indexed Mk<First>` cannot be used as `Indexed<True>`.
- Proof irrelevance is a conversion rule, not a reduction rule. An opaque
  equality proof is not treated as `refl`, so `Eq.elim`/`Eq.transport` remain
  stuck unless the proof actually reduces to `Refl`. This preserves the
  existing false-proof rejection tests.
- There is no propositional extensionality: `Prop` equality does not make two
  distinct propositions convertible.
- Proof irrelevance does not erase runtime effects, ownership, or effects rows.
  Those are separate checks.

The kernel exposes the boundary directly:

```rust
kernel.proof_closed(&term)          // true only for proofs of propositions
kernel.proof_open(&term, &context)  // validated open context
kernel.sort_closed(&term)           // Sort::Type(u) or Sort::Prop
kernel.sort_open(&term, &context)
```

## 5. Relevance and erasure at the executable boundary

Proposition declarations, `total enum` declarations, constructors, `total fn`
definitions, and logical aliases are kernel globals with no runtime
representation. They are erased before executable body checking, reference
evaluation, and native lowering.

- A proposition may appear in an `erased` parameter:
  `fn consume(erased p: True) -> i64 ! {} { 42 }`. The type is elaborated in an
  open kernel context, validated by `sort_open`, and the actual proof is checked
  by the kernel at each call site.
- Later erased parameters may depend on earlier erased binders, including
  proposition-indexed ones:
  `fn consume(erased n: Nat, erased p: IsZero<n>)`.
- A proposition proof has no runtime value: reading it, returning it, or using
  it as an `if`/`match` condition is a diagnostic. Erased evidence cannot
  influence an executable branch.
- Owning runtime data, runtime type generics, grades, and natural const
  parameters may not appear in an erased proposition. Immutable machine scalar
  parameters/locals (`i64`, `Bool`, `Unit`) may appear as symbolic indices only;
  see [runtime indices](runtime-indices.md). A `prop` or `total enum` that
  mentions an owning enum fails the dependency audit.
- A `total fn` may not call a partial or effectful function. Effect rows must
  be empty; nonempty rows are rejected before kernel admission.
- A runtime value cannot be fabricated by eliminating a proof: Prop elimination
  stays in Prop, and all proof data is erased before runtime lowering.
- Native and reference execution agree because neither receives the erased
  evidence at all. Tests cover both, including cross-module use.

## 6. Remaining limits

Deliberate, checked limits of this fragment:

- No `Prop : Prop`, no `Type : Type`, and no universe cumulativity.
- `Eq` remains Type-valued and is not automatically proof-irrelevant; there is
  no built-in Prop-valued equality, transport of propositional equality, or
  bridge from `Eq` to a `prop` family.
- Large elimination from user `prop` families into Type is rejected. There is no
  singleton-elimination exception.
- No record payloads for logical data or propositions, no mutual/nested
  inductive propositions, and no higher-order or negative recursion.
- No quotients, propositional extensionality, classical axioms, proof search,
  implicit arguments, runtime representation of proofs, or general recursive
  totals. Proofs are first-class *logical* terms (they can be bound, returned
  by total functions, and passed to erased parameters), never runtime values.
  Immutable `i64`/`Bool`/`Unit` scalars may be symbolic indices in those terms;
  that bridge never treats a scalar as proof evidence (see
  [runtime indices](runtime-indices.md)).
- Proof irrelevance is implemented in conversion; normalization does not
  collapse proof terms to a canonical inhabitant. Programs should not depend on
  the normal form of a proof.
- Resource, effect, ownership, subtyping, and grading checks are separate from
  logical validity. A checked proposition does not by itself establish any of
  those properties.

These are implementation boundaries, not claims that the full
[v0.1 design](spec-v0.1.md) is complete.
