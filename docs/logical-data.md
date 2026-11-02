# User-defined logical data and dependent elimination

Status: implemented restricted positive fragment. `total enum` declarations are
admitted by the trusted kernel together with their constructors; `Data.elim` is
a checked dependent eliminator with computation on constructor scrutinees.
`Eq.elim` provides full identity elimination (`J`). Constructors may add local
binders (`FSucc<n: Nat>`) and named fields, so standard `Fin<N>` and
`Vect<T,N>` are expressible from source. Everything admitted here is erased
before runtime lowering. Propositions declared with `prop` and proof
irrelevance are documented in [propositions](propositions.md).

```sh
cargo run -p kush -- check examples/logical-data.kush
cargo run -p kush -- eval  examples/logical-data.kush   # exit status 42
cargo run -p kush -- run   examples/logical-data.kush   # native exit status 42
cargo test --offline --test logical_data
```

This is an independently checking implementation, not a mechanized soundness
proof. The Rust implementation, the compiler, and the machine remain trusted.
Elaboration must still be correct to connect a source declaration to the
mathematical statement the author intended.

## 1. Surface distinction: `total enum` versus `enum`

Ordinary `enum` declarations are nominal, owning, zero-cost runtime data. They
are checked for executable layout and pattern matching, but they are **not**
logical evidence: a field, value, or constructor of an owning enum cannot enter
an erased proposition, and a `total fn` that depends on one is rejected by the
dependency audit.

`total enum` declares logical data:

```rust
total enum Even {
    EvenZero: Even,
    EvenSucc(Even): Even,
}

total enum Vect<T: Type, N: Nat> {
    Nil: Vect<T, 0>,
    Cons(head: T, tail: Vect<T, N>): Vect<T, Nat.succ<N>>,
}

// Constructor-local binders: `<n: Nat>` belongs to this constructor only and
// is distinct from the family parameter N.
total enum Fin<N: Nat> {
    FZero<n: Nat>: Fin<Nat.succ<n>>,
    FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
}
```

Semantics of the declaration:

- Every generic parameter of the `total enum` becomes one argument of the
  kernel family. There is no separate uniform-parameter class: the eliminator
  motive quantifies over the whole argument telescope, so a uniform parameter is
  simply an index that the motive ignores. This keeps the rule uniform and
  avoids silent specialization.
- A variant without `: Result` returns the family applied to the declaration's
  own parameters in order. For example `total enum Even { EvenZero: Even }`
  needs no explicit result.
- A variant with `: Result` must name **its own** `total enum` and supply exactly
  one index argument per generic parameter. `Vec<Nat>` on `Vect<T, N>` is
  rejected as a malformed result.
- Binders written after the variant name (`FSucc<n: Nat>`) are
  **constructor-local**. They are universally quantified for that constructor
  only. They may appear in later field types and in result indices, and they do
  not leak to another variant or to the family. Constructor-local binders and
  named fields share a nested lexical scope; shadowing a family parameter is
  legal but the innermost binder wins, so distinct names are preferable.
- Payloads are unit (`Nil`), positional tuples (`Cons(T, Vect<T,N>)`), or named
  tuples (`Cons(head: T, tail: Vect<T,N>)`). A named field binds in later fields
  and in the result indices. The names are not runtime record fields; they are
  logical telescope binders.
- A constructor may still contain direct recursive fields. Constructor-local
  binders are not recursive fields.
- Record payloads (`Mk { x: T }`) remain runtime-enum syntax and are rejected for
  logical data.
- Constructor names are qualified globals (`Vect.Cons`); the short form works
  when unambiguous, exactly like runtime enums.

Constructor generics are explicit. `Vect.Nil::<Nat, 0>` supplies both indices;
the kernel has no implicit inference or metavariables. When a constructor has
local binders, specialization supplies the family parameters first and then the
constructor-local binders: `Fin.FZero::<Nat.succ<n>, n>`. Named total wrappers
keep source readable:

```rust
total fn fzero<n: Nat>() -> Fin<Nat.succ<n>> ! {} {
    Fin.FZero::<Nat.succ<n>, n>
}
total fn fsucc<n: Nat>(pred: Fin<n>) -> Fin<Nat.succ<n>> ! {} {
    Fin.FSucc::<Nat.succ<n>, n>(pred)
}
```

Surface indices are terms, but the type grammar writes applications with the
existing `<...>` form:

```rust
type EvenIsDouble<e: Even> = Eq<Nat, even_height<e>, even_height<e>>;
total fn two_items() -> Vect<Nat, 2> ! {} {
    Vect.Cons::<Nat, 1>(1, Vect.Cons::<Nat, 0>(2, Vect.Nil::<Nat, 0>))
}
```

## 2. Kernel data declaration

The public kernel API is

```rust
Kernel::define_data(DataSpec) -> Result<()>
Kernel::define_indexed_data(IndexedDataSpec) -> Result<()>
Kernel::data(name) -> Option<&DataInfo>
```

with

```rust
pub struct DataSpec {
    pub name: String,
    /// Telescope: entry i is a type relative to entries < i.
    pub params: Vec<Term>,
    pub constructors: Vec<ConstructorSpec>,
}
pub struct ConstructorSpec {
    pub name: String,
    /// Field telescope relative to params and earlier fields.
    pub fields: Vec<Term>,
    /// One result index per parameter, relative to params and all fields.
    pub result: Vec<Term>,
}

// Extended form used by surface `total enum` / `prop` elaboration.
pub struct IndexedDataSpec {
    pub name: String,
    pub params: Vec<Term>,
    pub constructors: Vec<IndexedConstructorSpec>,
    pub prop: bool,
}
pub struct IndexedConstructorSpec {
    pub name: String,
    /// Constructor-local telescope relative to params and earlier locals.
    pub locals: Vec<Term>,
    /// Field telescope relative to params, locals, and earlier fields.
    pub fields: Vec<Term>,
    /// One result index per parameter, relative to params, locals, and fields.
    pub result: Vec<Term>,
}
```

`define_data` is the original no-locals, Type-valued entry point;
`define_indexed_data` is its generalization. `DataInfo` records the family's
universe (`sort`), whether it lives in `Prop` (`prop`), and each constructor's
local telescope. For a family with `k` parameters and a universe `u`, admission
produces:

```text
D : (p1 : P1) -> ... -> (pk : Pk) -> Universe(u)     -- or Prop

c : (p1 : P1) -> ... -> (pk : Pk)
    -> (l1 : L1) -> ... -> (lj : Lj)
    -> (f1 : F1) -> ... -> (fm : Fm)
    -> D R1 ... Rk
```

where each `Li`, `Fi`, and `Rj` is checked in the context of the parameters,
earlier locals, and earlier fields. Constructor **result indices may depend on
local binders and field values** (`Mk(n): D<n>`). Named fields make those
binders addressable from source; unnamed fields remain anonymous.

`define_data` is atomic. It validates the parameters, positivity, every field
type, every index type, the result universe, and every constructor name before
inserting anything. There is no axiom, unchecked global, or partial-insertion
API.

### Universes

For a Type-valued family the universe is

```text
u = max(0, universe of every non-recursive field,
          universe of every constructor-local binder)
```

A recursive field has the family's own universe, so it does not raise it.
Constructor-local binders are existentially quantified for a constructor and
can be exposed by the eliminator, so their universe must be included. Family
parameters are fixed inputs and do not raise the family's sort. A field whose
type lives above `u` cannot be hidden: admission recomputes the universe and
rejects any constructor whose field or result index would escape it. `Prop`
fields contribute level 0. There is no cumulativity. Large elimination from a
Type-valued family is allowed: the motive may return a type in any universe.
A `prop` family stays in `Prop` regardless of local universes because its
elimination is confined to propositions.

A `prop` family instead lives in `Prop`; its fields may be Types or
propositions, and it may only be eliminated into a proposition. See
[propositions](propositions.md) for the sort model and the large-elimination
restriction.

## 3. Positivity and termination restrictions

Recursive occurrences are deliberately first-order:

- a recursive occurrence is accepted only when an entire field's type is the
  family itself applied to exactly `k` index arguments;
- those index arguments may not mention the family;
- every other occurrence of the family anywhere in a field type is rejected,
  including nested occurrences inside another data type, occurrences inside a
  function type (negative or higher-order position), and occurrences in the
  family's own parameter/index kinds;
- mutual recursion between two `total enum` declarations is rejected by the
  source dependency cycle check; there are no mutual or nested recursors;
- there is no general fixpoint, partial recursion, or termination proof
  argument. Recursion in proofs goes through `Nat.induct` or `Data.elim`, which
  are structurally checked.

The source elaborator classifies data in dependency order. A forward reference
from one data declaration to a later one is accepted when acyclic; a cycle is
reported explicitly rather than approximated.

## 4. Dependent eliminator

```text
Data.elim::<D>(motive, branch1, ..., branchn, scrutinee)
```

`D` is the bare family name (no indices). Branches appear in declaration order
and must match the constructor count exactly.

The kernel term is

```rust
Term::IndElim { data, motive, branches, scrutinee }
```

with these premises, checked independently of surface syntax:

```text
motive  : (p1 : P1) -> ... -> (pk : Pk) -> (x : D p1 ... pk) -> Universe(v)
branchc : (p1 : P1) -> ... -> (pk : Pk)
          -> constructor-local telescope of c
          -> field telescope of c, with one induction hypothesis after every
             direct recursive field
          -> motive R1 ... Rk (c p1 ... pk locals fields)
scrutinee : D a1 ... ak
result    : motive a1 ... ak scrutinee
```

The induction hypothesis inserted after a recursive field `f : D I1 ... Ik` is
`motive I1 ... Ik f`. Hypotheses are interleaved with fields, not collected at
the end, so a branch for `Cons(head, tail)` has the shape

```text
(T: Type) -> (N: Nat) -> (head: T) -> (tail: Vect<T, N>)
  -> motive T N tail
  -> motive T (succ N) (Cons T N head tail)
```

A `Fin.FSucc` branch binds the family parameter `N`, the constructor-local `n`,
the predecessor `pred : Fin n`, and the induction hypothesis:

```text
(N: Nat) -> (n: Nat) -> (pred: Fin n) -> motive n pred
  -> motive (succ n) (FSucc N n pred)
```

Branches are ordinary logical values. In practice they are named `total fn`
definitions, aliases of function type, or partially specialized constants; the
surface language has no lambda expression syntax. Because the branch binds the
whole index telescope, a generic total function can serve as a branch:

```rust
total fn cons_length<T: Type, N: Nat>(x: T, xs: Vect<T, N>, ih: Nat) -> Nat ! {} {
    Nat.succ(ih)
}
```

The motive is a function, not a type family alias by itself. With a type-family
alias `LengthMotive<T, N, v>`, pass the alias *as a function* only if it has the
value argument; otherwise write a total function returning a type. For example
`type LengthMotive<T, N, v: Vect<T, N>> = Nat;` already has type
`(T) -> (N) -> (v : Vect<T, N>) -> Universe(0)` when referenced by name.

### Reduction

```text
elim P Bs (c a1 ... ak l1 ... lj f1 ... fm)
  -> Bc a1 ... ak l1 ... lj f1 (elim P Bs f1) ... fm (elim P Bs fm)
```

Only direct recursive fields receive a recursive `elim`; non-recursive fields
are passed through. Constructor-local arguments are passed before the fields.
The elimination is neutral on an open or otherwise stuck scrutinee. Reduction is
ordinary kernel conversion, so proofs such as `count(double<2>) = 2` check by
`refl` without runtime execution. Budget exhaustion is an error, never an
accepted proof.

## 5. Full equality elimination (`J`)

The kernel now has identity elimination in addition to transport:

```text
motive : (y : A) -> Eq(A, x, y) -> Universe(v)
refl   : motive x (Refl(A, x))
proof  : Eq(A, x, y)
--------------------------------------------------
J      : motive y proof
```

Surface syntax:

```rust
Eq.elim::<T>(left, right, motive, refl_case, proof)
```

Reduction: `Eq.elim(... Refl ...) -> refl_case`. An opaque or neutral proof stays
in the `EqElim` term. `Eq` is Type-valued, so equality proofs are not automatic
`Prop` inhabitants; proof irrelevance for explicitly declared propositions does
not assert that every equality is reflexive. Transport remains available and
keeps its existing reduction rule. See [propositions](propositions.md).

## 6. Erasure and the executable boundary

Logical data, `prop` propositions, their constructors, all `total fn`
definitions, and aliases are kernel globals with no runtime representation:

- `Executable::logical_definitions()` includes the names of admitted logical data,
  propositions, and total functions/aliases. Constructors are kernel globals but
  are not counted as source-level definitions.
- An executable function may use a logical type in an `erased` parameter, for
  example `fn proof_required(erased v: Vect<Nat, 2>) -> i64 ! {} { 42 }`.
  The type is elaborated in an open kernel context, validated as a universe
  member, and checked against a proof term at each call site.
- Later erased parameters may depend on earlier erased binders, so
  `fn consume_at(erased n: Nat, erased v: Vect<Nat, n>)` is checked with the
  actual earlier index substituted at the call site.
- Immutable runtime scalars (`i64`, `Bool`, `Unit`) may also index logical data
  and propositions symbolically; they are frozen at the call site and never
  treated as evidence. See [runtime indices](runtime-indices.md).
- Runtime type generics, mutable values, grades, natural const parameters, and
  ordinary owning data may not appear in an erased logical type.
- A runtime binding of a logical type, a runtime call of a logical function, or
  a runtime construction of a logical constructor is a diagnostic. Logical data
  is removed before reference evaluation and native lowering; the native and
  reference application tests agree.
- A `total fn` may depend only on other checked logical declarations. Calling a
  partial or effectful function, or citing an owning data declaration, fails the
  dependency audit instead of silently erasing a runtime dependency.

Modules keep the normal visibility rules. A `pub total enum` and its
constructors are exported and can be used from another module in erased
signatures; the enum type is reached through the module path (`even.Even`), and
constructors through the enum-qualified path (`even.Even.EvenZero`). Importing
the enum item itself (`use even.Even;`) also imports its constructors through
the existing resolver rules. Qualified logical data and constructors are checked
and erased in the same way as local ones.

## 7. Limits and remaining gaps

Implemented and tested:

- positive first-order indexed data with unit, tuple, and named-tuple
  constructors;
- constructor-local binders, including predecessor-varying result indices such
  as `Fin` and field-dependent result indices;
- checked constructor kinds, result arity and index types, universe computation,
  duplicate/collision rejection, and atomic insertion;
- dependent elimination with a value-dependent motive, validation of every
  branch, and constructor reduction;
- `Eq.elim` (`J`) with conversion on `Refl`;
- erased executable evidence, dependent erased parameters, module qualification,
  reference/native agreement, and rejection of runtime or partial uses.

Deliberately unsupported (each fails with a diagnostic rather than being
approximated):

- record payloads and named record field selection in logical terms (use named
  tuple fields instead);
- mutual, nested, higher-order, and negative recursion; general recursive total
  functions; termination arguments beyond structural eliminators;
- indexed pattern matching and impossible-branch reasoning;
- a `Prop` sort for `Eq` itself, large elimination from `prop`, quotients,
  extensionality, classical axioms, and automatic proof search (see
  [propositions](propositions.md));
- universe cumulativity and implicit arguments.

Compiler resource limits still apply. Data declarations allow at most 64
parameters, 64 constructors, and 64 constructor-local binders per constructor.
Kernel operations start with 100000 weighted units and 128 nested frames per
public call; admission failure leaves no partial global. Module checking remains
limited to 256 selected logical definitions. These are implementation budgets,
not mathematical restrictions.
