# Dependent array lengths and compile-time indices

Status: implemented for compile-time natural length parameters on inline arrays,
generic records/enums, function signatures, and transparent executable aliases.
This is still a deliberately restricted dependent fragment: lengths are checked
compile-time naturals, never runtime values, and an inline array must have a
statically representable layout.

```sh
cargo run -p kush -- run examples/dependent-arrays.kush   # exit status 42
cargo test --offline --test dependent
```

## Const length parameters

A generic parameter bounded by `Nat` is a compile-time natural parameter, not a
runtime type and not a usage grade:

```rust
#[noalloc]
fn identity<T: Type, N: Nat>(xs: [T; N]) -> [T; N] ! {} { xs }

#[noalloc]
fn last<T: Type, N: Nat>(xs: [T; N]) -> T ! {panic} { xs[N - 1] }
```

The three generic kinds are separate:

| Declaration | Kind | Specialized with |
| --- | --- | --- |
| `T`, `T: Type` | runtime type | a type such as `i64` or `Pair<i64>` |
| `N: Nat` | compile-time natural | a natural constant such as `3` or `1 + 2` |
| `G: Grade` | abstract usage grade | a grade such as `1`, `many`, or `G * 2` |

A natural parameter can be used as an array length or a compile-time index. It
cannot be used as a runtime type, and a type or grade parameter cannot be used
as a length. Those mistakes are rejected at the declaration, even when a generic
function is never instantiated.

Explicit specialization follows declaration order and always supplies every
generic argument:

```rust
identity::<i64, 3>(values)
mixed::<1, 2, i64>(0, values)   // G = 1, N = 2, T = i64
```

Length inference is intentionally narrow and unambiguous. It works from:

- an argument whose runtime type is an inline array of the declared shape, e.g.
  a local of type `[i64; 3]` passed to `[T; N]`; and
- an inline array literal passed directly to an array parameter, e.g.
  `identity([10, 20, 12])`, where the literal length binds `N` and its elements
  bind an otherwise-unconstrained element type.

Nested literal arrays without an expected element shape are still ambiguous
with `Vec<T>` and therefore require an annotation or an array-typed local. The
compiler does not guess an array interpretation.

## Length expressions

A length expression is checked before any layout is built. The same evaluator
also folds constant array indices and compile-time slice-range endpoints;
runtime-dependent endpoints still take the existing checked path. The admitted
fragment is:

```text
length ::= natural
         | N                         -- an in-scope <N: Nat>
         | logical_name<args...>     -- an admitted total logical definition
         | (length)
         | length + length | length - length
         | length * length | length / length | length % length
```

Evaluation is total and checked:

- subtraction below zero, division/remainder by zero, and `usize` overflow are
  errors;
- a runtime parameter or local, an effectful function, an arbitrary executable
  function, or an unbound generic is an error;
- `logical_name<args...>` is reduced by the dependent kernel. Only definitions
  admitted by the trusted kernel are eligible, and every argument must itself
  be a compile-time natural. The result must normalize to a `Nat` numeral;
- at most 256 nodes are evaluated per length or index expression.

For example, with an admitted total addition:

```rust
type Constant<n: Nat> = Nat;
total fn step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }
total fn add(n: Nat, m: Nat) -> Nat ! {} { Nat.induct(Constant, m, step, n) }

fn second(xs: [i64; add<1, 1>]) -> i64 ! {panic} { xs[add(0, 1)] }
```

The length folds to `2` and the index folds to `1` through kernel
normalization, not through arbitrary code execution. A logical computation that
does not normalize within the kernel budget is a diagnostic, never an
approximation.

## Constant indices and dynamic indices

An array index is lowered in one of two ways:

1. If the index expression is in the compile-time fragment above, it is
   evaluated, bounds-checked against the array length, and projected directly.
   No runtime check and no `panic` effect are needed.
2. Otherwise it is a genuinely runtime index. It lowers to the existing
   whole-array view plus a checked element read, requires the `panic` effect,
   and is checked at run time in both the reference evaluator and native code.

The compiler does not evaluate runtime or effectful code to decide an index.
An expression that references a runtime local simply takes path 2; an
ill-formed constant expression (negative, overflowing, unbound const, or a
failed logical normalization) is a compile error instead of silently becoming a
runtime read.

## Symbolic lengths in data and aliases

Natural parameters may appear in generic record and enum fields:

```rust
struct Buffer<N: Nat> { data: [i64; N] }

#[noalloc]
fn head<N: Nat>(b: Buffer<N>) -> i64 ! {panic} { b.data[0] }

let buffer: Buffer<3> = Buffer { data: [20, 22, 0] };
```

A data declaration's `N: Nat` parameter must be used as an array length
somewhere in its fields or variant payloads. This keeps natural parameters from
being confused with phantom type parameters. The same restriction does not
apply to type parameters.

Syntax:

```rust
Buffer<3>                       // natural argument in declaration position
Pair<i64>                       // type argument
```

Each distinct `(types, naturals)` list creates a distinct memoized inline
layout. Layouts remain subject to the existing limits: at most 32 words
including nested elements, at most 256 layouts, and at most 32 nested
instantiation levels. Exceeding them is an explicit diagnostic. A length that
cannot be evaluated statically is rejected instead of producing an unsafe
dynamic stack layout.

## Executable type aliases

Aliases are transparent. An alias lowers directly to its right-hand side, so an
alias adds no tag, boxing, allocation, or indirection:

```rust
type Number = i64;
type Pair<T> = [T; 2];
type Value = Number | Bool;
type ReadOnly = Pair<i64>;
```

Generic aliases may take type and natural parameters and may mention arrays,
unions, intersections, records, enums, `Box`, `Vec`, bytes, and other aliases.
Aliases work across modules under the normal `pub`/`use` visibility rules.
Recursive aliases are rejected with a dedicated cycle diagnostic, and expansion
is limited to 64 levels. First-order inference expands a generic alias when it
matches a parameter shape, so an alias such as `type Arr<T, N: Nat> = [T; N]`
participates in both type and length inference.

Classification keeps the logical boundary strict:

- aliases whose bodies contain runtime structure (`[T; N]`, `i64 | Bool`,
  records/enums, containers, borrows) are elaborated by the executable type
  checker;
- a plain alias to a scalar is an executable alias only when runtime code
  actually uses it; otherwise it remains a logical alias and must satisfy the
  kernel. This preserves the existing rule that an unused `type A = i64;` is
  rejected by the logical subset rather than acquiring a hidden runtime meaning;
- logical aliases (`type Same<T: Type, x: T> = Eq<T, x, x>;`) continue to be
  kernel-checked and erased. A `total fn` that cites a runtime alias fails the
  dependency audit, so runtime definitions still cannot enter erased proofs;
- executable aliases cannot be used in an erased logical parameter unless they
  are themselves logical definitions.

Hosting containers remain invariant: `Vec<T>` and `Box<T>` do not become
covariant because an alias was used to name them.

## Dependent erased parameters

Erased logical parameters are kernel terms, not runtime values. A parameter may
depend on **earlier erased kernel binders**; its type is elaborated in that open
context, validated as a type in a universe, and at a call site the earlier
actual proof terms are substituted before the new evidence is checked:

```rust
total fn truth() -> Eq<Nat, 0, 0> ! {} { refl::<Nat>(0) }

fn consume(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { 7 }

fn outer(erased n: Nat, erased p: Eq<Nat, n, n>) -> i64 ! {} { consume(n, p) }

fn main() -> i64 ! {panic} { consume(0, truth()) + outer(0, truth()) }
```

`consume(1, truth())` is rejected because substituting `1` for `n` requires
`Eq<Nat, 1, 1>`, which `truth` does not establish. Runtime locals, runtime type
generics, grades, and natural const parameters are not kernel binders and cannot
appear in these types. There is still no proof search or implicit argument.
Proofs are first-class logical terms but have no runtime representation. Proof
irrelevance is available only for inhabitants of checked `prop` propositions;
the Type-valued `Eq` proofs keep their structural conversion rules. See
[propositions](propositions.md).

Immutable **machine scalar** parameters and locals (`i64`, `Bool`, `Unit`) are a
separate, deliberately limited exception: they may be symbolic indices inside
erased proof types, with call-site freezing and no machine arithmetic in the
kernel. See [runtime indices](runtime-indices.md). Mathematical `Nat` and
machine `i64` remain distinct; there is no implicit conversion.

## Remaining gaps

This is a usable restricted dependent fragment, not the full calculus in the
[v0.1 design](spec-v0.1.md):

- **No runtime-sized `[T; n]` layout.** `[T; n]` with a runtime `n` is still
  rejected rather than lowering to a dynamic stack layout. The separate
  `DynArray<T, capacity>` type provides inline storage with a compile-time
  capacity and a runtime length, checked in both backends; see
  [runtime-sized inline arrays](dynamic-arrays.md). There is no implicit
  conversion between `DynArray`, `[T; N]`, `Vec<T>`, or a slice.
- Length inference reads an actual inline array, a literal array, or a generic
  alias whose expansion is an array; it does not solve general equations such as
  `N + 1 = 3`, and there is no partial specialization (`f::<i64>` with `N`
  inferred is not accepted).
- Inference through a union alternative containing an array is not principal;
  use an explicit annotation/specialization.
- Logical calls in a length must be fully applied and reduce to a `Nat` within
  the kernel budget. User-defined `total enum` data and its eliminator are
  available to erased proofs (see [logical data](logical-data.md)), and
  constructor-local binders make `Fin<N>` expressible as logical evidence, but
  there are no general type-level functions returning runtime layouts, no
  arithmetic solver obligations, and no runtime-dependent inline array lengths.
- Aliases are expanded by name in runtime types, but there is no separate
  alias-unification inference for generic runtime parameters.
- A runtime alias is not a first-class logical definition; it is erased from the
  logical environment and its proof-level use is rejected.
- Array lengths are compile-time `usize` values. Logical `Nat` still has no
  machine representation, and conversion is checked rather than truncating.
- Runtime scalar proof indices are a narrow, separate bridge: only immutable
  `i64`/`Bool`/`Unit` values, only as symbolic indices (never arithmetic or
  evidence), and never as inline array lengths. See
  [runtime indices](runtime-indices.md) for its own exact limits.
