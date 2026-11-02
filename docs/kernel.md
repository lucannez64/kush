# Bootstrap dependent kernel and name resolution

This milestone adds single-file name resolution, a small logical kernel, and
restricted source elaboration. It does not implement the entire [v0.1
specification](spec-v0.1.md). A separate [scalar executable subset](executable.md)
now supports Cranelift native code generation. Total logical definitions may
coexist with executable code; they are kernel-checked, relevance-audited, and
erased before runtime lowering. Closed logical propositions, open propositions
depending on earlier erased kernel binders, and positive logical data can appear
as executable erased parameters. Compile-time dependent array lengths and const
`Nat` parameters are implemented separately; immutable machine scalar
parameters/locals (`i64`, `Bool`, `Unit`) may additionally act as symbolic
indices in erased proof types, but general dependent indexing over arbitrary
runtime values and machine arithmetic in the kernel remain outside this
milestone. See
[dependent array lengths](dependent-indices.md),
[runtime indices](runtime-indices.md),
[logical data](logical-data.md), and
[propositions](propositions.md).

```sh
cargo run -p kush -- resolve examples/proofs.kush
cargo run -p kush -- check examples/proofs.kush
cargo run -p kush -- check examples/induction.kush
cargo run -p kush -- check examples/large-naturals.kush
cargo run -p kush -- check examples/finite-proofs.kush
```

`parse` still validates syntax only. `resolve` validates lexical names only.
`check` selects this explicitly supported logical fragment for files without
ordinary executable functions or enum declarations. Files with ordinary `fn` or
enums use the executable value checker, which now also submits every `total fn`
and alias in the program to this kernel and erases the admitted definitions
before runtime checking. The library API `kush::check` remains logical-only.
Unsupported constructs fail instead of being treated as verified. Exit codes
remain 0 for success, 1 for source/checking failures, and 2 for CLI usage errors.

## 1. Trust boundary and public APIs

- `resolve::resolve(&ast::Module)` assigns stable-within-a-pass binding IDs to a
  parsed module. It records references, binder locations, and global dependencies.
- `check(&str)` parses, resolves, elaborates, then submits closed types and terms
  to `kernel::Kernel`. Success returns the checked definitions and their kernel.
- `Kernel::define(name, ty, value)` checks that `ty` inhabits a universe or
  `Prop` and that `value` has type `ty`. The definition becomes visible only
  after both succeed.
- `Kernel::define_data(spec)` checks a positive indexed data family, its
  constructor telescope, and every result index, then inserts the family and all
  constructors atomically. `Kernel::define_indexed_data(spec)` is the extended
  form supporting constructor-local binders and `Prop` families.
  `Kernel::data(name)` exposes the admitted form.
- `Kernel::infer_closed`, `check_closed`, and `normalize_closed` operate on
  explicit kernel terms. Normalization first checks the input; there is no public
  unchecked reduction API.
- `Kernel::sort_closed`/`sort_open` classify a type or proposition as
  `Sort::Type(u)` or `Sort::Prop`. `Kernel::proof_closed`/`proof_open` report
  whether a term is an inhabitant of a proposition. `check_open` and `infer_open`
  check terms under explicit hypothesis types. Every hypothesis is validated as
  a type relative to the preceding entries; this is still checking, not unchecked
  insertion.

The kernel does not consult source syntax, resolver output, effect declarations,
or a frontend claim that a theorem is valid. Its environment is private. There
is no axiom-admission API, unchecked global insertion, or recursive global
insertion. Tests submit malformed core terms directly to exercise this boundary.

This is an independently checking implementation, **not a mechanized soundness
proof or a security-audited proof assistant**. Its implementation, the Rust
compiler/runtime, and the machine remain trusted. Correct elaboration is also
needed to connect an accepted core statement to what a source author intended.
The checker does not establish program ownership, effect, or memory guarantees.

## 2. Core syntax and binding

Core terms are explicit and use zero-based de Bruijn indices. Index 0 denotes
the nearest enclosing binder; binder names do not affect equality.

```text
t, A, B ::= Var(i) | Global(name) | Universe(u) | Prop
          | Pi(A, B) | Lam(A, t) | App(t, t)
          | Nat | Zero | Succ(t) | Literal(natural)
          | NatElim(motive, zero, step, value)
          | Eq(A, x, y) | Refl(A, x)
          | Transport(A, x, y, motive, equality, value)
          | EqElim(A, x, y, motive, refl_case, proof)
          | IndElim(data, motive, branches, scrutinee)
```

Global names include admitted definitions, total logical data families, and
their constructors. Data families and constructors are opaque constants: they do
not unfold during conversion.

`Pi(A, B)` binds one variable in `B`, not in `A`. `Lam(A, t)` binds one variable
in `t`, not in its annotation. Context entries store their types relative to the
context that preceded their introduction. Looking up a variable shifts its
stored type into the full current context. Substitution removes a binder,
decrements outer indices, and shifts a replacement under intervening binders.

For example, polymorphic identity is:

```text
term: Lam(Universe(0), Lam(Var(0), Var(0)))
type: Pi(Universe(0), Pi(Var(0), Var(1)))
```

The distinction between `Var(0)` and `Var(1)` in its type is intentional: under
both binders, the type parameter is one binder away.

## 3. Typing rules

`Γ ⊢ t : A` means that term `t` has type `A` in context `Γ`. `≡` denotes the
conversion relation below. Kernel checking infers a type and compares it to the
expected type by conversion. Lambda annotations are explicit; there are no
kernel metavariables or unchecked holes.

### Universes and functions

```text
Γ ⊢ Universe(u) : Universe(u + 1)
Γ ⊢ Prop : Universe(0)

Γ ⊢ A : s1                 Γ, x:A ⊢ B : s2
------------------------------------------------
Γ ⊢ Pi(A, B) : Prop                    -- when s2 = Prop
Γ ⊢ Pi(A, B) : Universe(max(level(s1), v))  -- when s2 = Universe(v)

Γ ⊢ A : Universe(u)       Γ, x:A ⊢ t : B
----------------------------------------
Γ ⊢ Lam(A, t) : Pi(A, B)

Γ ⊢ f : Pi(A, B)         Γ ⊢ a : A
------------------------------------
Γ ⊢ App(f, a) : B[a/x]
```

Universe levels are explicit `u32` integers with checked successor arithmetic.
Overflow is an error. There is **no cumulativity**: `Nat : Universe(0)` does not
also establish `Nat : Universe(1)`. `Universe(0)` never inhabits itself.

Throughout the rules, `Sort` means `Universe(u)` or `Prop`, and
`level(Prop) = 0`. `Prop` is the sort of propositions. `Prop : Universe(0)`, so
`Prop` is a type but never a proposition: `Prop : Prop` is rejected. `Prop` is
impredicative:

```text
Γ ⊢ A : s       Γ, x:A ⊢ B : Prop
------------------------------------
Γ ⊢ Pi(A, B) : Prop
```

Quantifying into a proposition stays in `Prop` regardless of the domain's
universe. A codomain of `Universe(v)` remains predicative:
`Pi(A, Universe(v))` lives in `Type(max(level(A), v))`, where a proposition
domain contributes level 0. A codomain of `Prop` denotes a function returning
the *sort* `Prop`, not a proposition, and is Type-valued. See
[propositions](propositions.md) for the full model and elimination restriction.

Variables must be bound. Globals must already have been admitted by `define`.
A definition cannot refer to itself or a future unchecked global. Invalid domain
annotations, non-types used as types, and applications of nonfunctions fail.

### Natural numbers and induction

```text
Nat : Universe(0)       Zero : Nat
n : Nat  =>  Succ(n) : Nat
Literal(k) : Nat          (k is a validated canonical natural)
```

Natural induction requires all of these premises:

```text
motive : Pi(Nat, Universe(u))
zero   : motive Zero
step   : (n : Nat) -> motive n -> motive (Succ n)
value  : Nat
```

Its result is `motive value`. The step type is built with capture-avoiding
shifts under both binders. Induction is structurally terminating by construction;
there is no general fixpoint operator. Numerals use compact arbitrary-precision
storage, while `Zero` and `Succ` remain core constructors. Conversion identifies
a numeral with its corresponding constructor form without constructing a unary
tree. Induction still follows the constructor equations and consumes the checking
budget; compact storage does not make every inductive computation cheap.

### Equality and transport

```text
A : Sort       x : A       y : A
---------------------------------------  level(Prop) = 0
Eq(A, x, y) : Universe(level(A))

A : Sort       x : A
------------------------------
Refl(A, x) : Eq(A, x, x)
```

Transport requires a carrier `A` that is a type or proposition, `x : A`,
`y : A`, a family `motive : A -> Sort`, evidence `equality : Eq(A, x, y)`, and
`value : motive x`. Its result has type `motive y`.

This is a transport operation, not the full proof-dependent identity eliminator
`J`. Equality is **Type-valued**: it lives in the same universe as its carrier
(a `Prop` carrier contributes level 0), so equality proofs are ordinary logical
data rather than `Prop` inhabitants. They are erased at runtime but are not
automatically proof-irrelevant. Quotients, extensionality, and classical axioms
are absent. There is no built-in propositional equality; see
[propositions](propositions.md) for the exact relationship between `Eq` and
`Prop`. The kernel itself has no runtime notion; the executable boundary in
section 6 audits relevance and erases proofs before runtime lowering.

### User-defined positive data and propositions

`Kernel::define_data` admits a family `D` of `k` index parameters and a universe
`u`. `Kernel::define_indexed_data` adds constructor-local binders and may place
the family in `Prop`:

```text
D : (p1 : P1) -> ... -> (pk : Pk) -> Universe(u)     -- or Prop

c : (p1 : P1) -> ... -> (pk : Pk)
    -> (l1 : L1) -> ... -> (lj : Lj)
    -> (f1 : F1) -> ... -> (fm : Fm)
    -> D R1 ... Rk
```

`Li`, `Fi`, and `Rj` are checked relative to the parameters, earlier locals, and
earlier fields. Admission computes `u` from the non-recursive field universes
and constructor-local binder universes, rejects fields whose universe escapes
it, and enforces a first-order positivity fragment: a recursive occurrence must
be a whole field of type `D` applied to exactly `k` index arguments that do not
mention `D`. Nested, higher-order, negative, and mutual occurrences are
rejected. Every constructor result must match the family's sort. Admission is
atomic. `Prop` families ignore local universe levels because their elimination
is confined to `Prop`.

Constructor-local binders are universally quantified for one constructor; they
are not family indices. `Fin` is the standard example:

```text
Fin : Nat -> Universe(0)
fzero : (N : Nat) -> (n : Nat) -> Fin (succ n)
fsucc : (N : Nat) -> (n : Nat) -> Fin n -> Fin (succ n)
```

Surface `total enum` and `prop` declarations elaborate into this form. A `prop`
family may only be eliminated into a proposition; see
[propositions](propositions.md).

`Eq.elim` implements full identity elimination:

```text
motive : (y : A) -> Eq(A, x, y) -> Sort
refl   : motive x (Refl(A, x))       proof : Eq(A, x, y)
=> EqElim(...) : motive y proof
```

`IndElim` is a dependent recursor whose motive abstracts over the whole index
telescope and the eliminated value:

```text
motive   : (p1:P1) -> ... -> (pk:Pk) -> D p1...pk -> Sort
branch_c : (p1:P1) -> ... -> (pk:Pk) -> constructor-local telescope
           -> fields, with an induction hypothesis after every direct
              recursive field
           -> motive R1...Rk (c p1...pk locals fields)
scrutinee: D a1...ak                  result: motive a1...ak scrutinee
```

For a Type-valued family any motive sort is allowed (large elimination). For a
`prop` family the motive must return `Prop`; Type-valued motives are rejected.
Branches are in constructor declaration order. See
[logical data](logical-data.md) for the surface syntax, reduction equations, and
the exact unsupported forms.


## 4. Conversion and computation

Conversion compares normal forms structurally after:

- Beta reduction: applying a lambda substitutes its argument into its body.
- Delta reduction: references to checked definitions unfold transparently.
- Compact numeral normalization: literal zero becomes `Zero`, and a closed
  `Succ` becomes its incremented compact numeral. `Succ` of a neutral stays a
  constructor.
- Natural induction reduction on `Zero`, `Succ`, and compact positive numerals.
- Transport reduction when its equality proof reduces to `Refl`.
- Identity elimination (`J`) reduction when its proof reduces to `Refl`.
- Data elimination reduction on a constructor application; recursive fields are
  eliminated recursively and non-recursive fields are passed through.

Normal forms also normalize under binders. Eliminations on neutral variables
remain neutral. There is no eta conversion, implicit coercion, algebraic
subtyping, arithmetic solver, or theorem search.

Conversion is additionally type-directed for **proof irrelevance**: if both
terms are inhabitants of propositions and their proposition types are
convertible, they are convertible regardless of their proof structure. This
applies only to `Prop` inhabitants; `Nat` values, Type-valued data, and runtime
values are still compared structurally. Proof irrelevance is a conversion rule,
not a reduction rule, so opaque equality proofs remain neutral in
`Transport`/`Eq.elim`. See [propositions](propositions.md).

For induction, the reduction equations are:

```text
NatElim(P, z, s, Zero)     -> z
NatElim(P, z, s, Succ(n))  -> s n (NatElim(P, z, s, n))
NatElim(P, z, s, Literal(k + 1))
    -> s Literal(k) (NatElim(P, z, s, Literal(k)))
Transport(A, x, x, P, Refl(A, x), v) -> v
```

The kernel checks elimination premises before reduction is available through a
public API. An arbitrary expression cannot be normalized to bypass type checking.
No theorem is accepted simply because checking timed out.

## 5. Name-resolution rules

Resolution currently uses one lexical namespace for dependent terms and types.
It predeclares top-level functions, aliases, and nominal data names so forward
references work. Ordinary function recursion can resolve; the logical checker
subsequently rejects recursive dependency cycles.

- At most one `module a.b;` header is allowed, first and without modifiers.
- Current-module qualification such as `a.b.identity` is recognized.
- `use` imports fail explicitly; no library or filesystem module loading occurs.
- Top-level duplicates and redeclarations of reserved primitives fail.
- Generic bounds resolve before the generic is introduced. Parameters likewise
  become visible after their annotations, so later parameters may depend on them.
- Function generic/parameter binders must be unique in their shared scope.
- `let` initializers resolve before their pattern introduces new names. Sequential
  lets may shadow earlier bindings; nested blocks and match arms have local scopes.
- Enum constructors have qualified names, such as `Token.Integer`. Short names
  work when unique; ambiguous short names require qualification.
- Constructor names in patterns are resolved; otherwise a simple pattern name
  introduces a binding. Repeated bindings in one pattern fail. Alternatives must
  introduce the same set of names. Their type/ownership compatibility is deferred.
- Record fields and enum variants must have unique names within their owner.
- Unknown qualified enum constructors fail. Fields selected from local values
  resolve their value root; member existence waits for type checking.

Known primitives include scalar type names, `Type`, `Prop`, `Nat`, `Eq`, `refl`,
`Nat.zero`, `Nat.succ`, `Nat.induct`, `Eq.transport`, and built-in effect names. Being known to resolution is
**not** evidence of implementation by the logical checker. Standard-library
container names are not invented as placeholders. The earlier `parser.kush`
fixture remains a syntax example; its undeclared library types prevent full
resolution/checking at this milestone.

Binding IDs are tied to this pass, not serialized symbol identities. This pass
is not a module system, overload resolver, trait resolver, or type checker.

## 6. Checked source subset

`check` currently accepts module headers, transparent type aliases, and acyclic
`total fn` definitions with bodies and empty effect rows. Every accepted
source definition is checked by the kernel. Dependency ordering is deterministic
and permits forward references; any cycle is rejected, even a recursion that
might eventually admit a valid termination proof.

Supported source features are:

- Explicit type/value generic parameters; an omitted generic bound defaults to
  `Type`, meaning `Universe(0)`.
- `Type` and `Type<literal>` for universe levels 0 through 255.
- `Nat`, `Nat.zero`, `Nat.succ(n)`, and compact arbitrary-precision decimal
  logical literals, subject to the significant-digit budget in section 8.
- `Eq<T, x, y>` and `refl::<T>(x)`. These elaborate directly to kernel equality
  and reflexive-proof terms, so the carrier may be a Type at any supported level
  or a proposition. A generic *definition* still binds `T : Type` at level 0
  unless it is written against `Prop`; there is no sort-polymorphic generic.
- Dependent result types referencing earlier parameters or generic values.
- Pure function types, including dependent binders:
  `fn(n: Nat, hypothesis: P<n>) -> P<Nat.succ<n>> ! {}`.
  Named parameters bind in later annotations and the result, and their scope ends
  at the function type. Anonymous parameters also occupy core binder slots.
  Such types denote total logical functions, not arbitrary executable callbacks.
  Empty parameter lists and nonempty effect rows remain unsupported here.
- Function calls, explicit specialization, and nested blocks.
- Immutable, explicitly typed, single-name lets followed by a tail expression.
- Generic aliases that return types, including aliases indexed by term values.
- `total enum` positive indexed data with checked constructors, named tuple
  fields, constructor-local binders, and `Data.elim::<D>(...)`; see
  [logical data](logical-data.md).
- `prop` positive inductive propositions and proof irrelevance; see
  [propositions](propositions.md). Proposition elimination is confined to
  `Prop` motives.
- `Eq.elim::<T>(x, y, motive, refl_case, proof)` for full identity elimination
  in addition to `Eq.transport`. Motives may return a Type or a proposition.

All binder arguments are explicit: generic specialization applies arguments
before ordinary value calls. There is no implicit generic inference or implicit
proof search. Core application is curried, so a partial application remains a
function if its inferred type is a `Pi`.

Nullary total functions lower to transparent constants: `answer` and `answer()`
refer to the same core value. Empty calls are accepted only for named nullary
total functions with all their generic arguments supplied; `0()` and
`Nat.succ()` are rejected. This permits naming function results in type-level
arguments without executing arbitrary runtime code. It is a bootstrap logical
convention, not a definition of future effectful function semantics.

For example:

```rust
total fn identity<T: Type>(x: T) -> T ! {} { x }

type Same<T: Type, x: T> = Eq<T, x, x>;

total fn reflexivity<T: Type>(x: T) -> Same<T, x> ! {} {
    refl::<T>(x)
}

total fn answer() -> Nat ! {} { identity::<Nat>(2) }

total fn proof_of_answer() -> Eq<Nat, answer, 2> ! {} {
    refl::<Nat>(2)
}
```

The last proof succeeds through beta/delta conversion. Replacing its result type
with `Eq<Nat, answer, 1>` fails. A `total` label by itself is never trusted as a
termination argument: only the admitted acyclic subset is accepted.

Finite indices and propositions are surface declarations:

```rust
total enum Fin<N: Nat> {
    FZero<n: Nat>: Fin<Nat.succ<n>>,
    FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
}

prop True { Trivial: True }
prop Two { First: Two, Second: Two }

total enum Indexed<p: Two> { Mk: Indexed<p> }

// Accepted by proof irrelevance: First and Second are both proofs of Two.
total fn same_proof() -> Indexed<Second> ! {} { Indexed.Mk::<First> }
```

### Source-level induction and transport

The source checker now exposes two fully applied operations, lowering directly to
existing kernel constructors without adding axioms or new kernel typing rules:

```rust
Nat.induct(motive, zero, step, value)
Eq.transport::<T>(from, to, motive, proof, value)
```

`Nat.induct` takes exactly four ordinary arguments and no generic arguments:

- `motive` is a total function returning a type or proposition, with an
  inferred `Type<u>` or `Prop` codomain.
- `zero` inhabits `motive<0>`.
- `step` has type `fn(n: Nat, hypothesis: motive<n>)
  -> motive<Nat.succ<n>> ! {}`.
- `value` has type `Nat`; the result inhabits `motive<value>`.

`Eq.transport` takes exactly one generic carrier type and five ordinary arguments.
Its premises and result are the transport rules in section 3: the equality must
connect `from` to `to`, and the supplied value must inhabit the family at `from`.
The result inhabits the family at `to`. The motive's result sort is inferred
by the kernel, not hardcoded by elaboration. `Eq`/`refl` elaborate directly to
kernel equality terms, so a direct application can use a Type at any level or a
proposition as the carrier. Generic helpers still need an explicit `Type` or
`Prop` binder; there is no sort-polymorphic generic.

`Data.elim::<D>` takes a motive, one branch per constructor in declaration order,
and a scrutinee; `Eq.elim::<T>` takes `left`, `right`, a motive, the reflexive
case, and an equality proof. Both are described with their exact premise and
reduction rules in [logical data](logical-data.md). For a `prop` family the
motive must return a proposition.

These operations cannot yet be passed as first-class or partially applied values.
Pass a named total wrapper instead. Bare references, wrong generic arity, or
wrong value arity are rejected. Recognition uses resolved binding IDs, so local
shadowing cannot accidentally invoke an intrinsic. Current-module qualification
continues to work.

Named total functions and partially specialized aliases provide motives and step
functions; lambda expression syntax is not required. For example:

```rust
type ConstantNat<n: Nat> = Nat;

total fn step(n: Nat, accumulated: Nat) -> Nat ! {} {
    Nat.succ(accumulated)
}

total fn add(n: Nat, m: Nat) -> Nat ! {} {
    Nat.induct(ConstantNat, m, step, n)
}

total fn five() -> Eq<Nat, add<2, 3>, 5> ! {} {
    refl::<Nat>(5)
}
```

The complete [induction example](../examples/induction.kush) also derives equality
symmetry through transport and proves `add(n, 0) = n` for every natural `n` through
induction. These theorems are checked generically, not by testing finitely many
inputs. A return type can apply a function using the existing type-argument syntax
`add<n, 0>`; ordinary value expressions use `add(n, 0)`.

Arbitrary user data types are supported only through the restricted `total enum`
and `prop` fragments described in [logical data](logical-data.md) and
[propositions](propositions.md), which supply positivity, dependent elimination,
and safe proof-irrelevance rules. Ordinary owning enums remain runtime data and
never become logical evidence.


### Checked interoperability with executable functions

A file that also contains executable functions (or runtime data) still checks
every `total fn` and every type alias through the kernel before executable body
checking. The logical declarations produce no runtime `Function` IR; they are
erased after admission. `kush::executable::check_program` exposes their checked
names through `Executable::logical_definitions`, while `function_count` counts
only runtime functions.

The boundary is deliberately narrow:

- A logical definition may depend only on other selected logical definitions and
  builtins. Dependencies are audited in the resolver graph, so a `total fn` that
  calls an executable function, uses runtime data, or cites an unchecked alias
  fails instead of having that dependency silently dropped.
- Runtime code may not call a logical definition or read it as a value; there is
  no runtime representation. Such a use is rejected with an erasure diagnostic.
- An executable `erased` parameter is either the existing arithmetic
  `{ ... }` proposition or a supported logical type or proposition, such as
  `Eq<Nat, 0, 0>`, `Fin<3>`, or a `prop`. Logical erased parameter types may
  mention checked logical globals, *earlier erased kernel binders*, and earlier
  **immutable machine scalar** parameters/locals (`i64`, `Bool`, `Unit`) used
  symbolically, but not mutable values, runtime type generics, grades, natural
  const parameters, or owning data. The elaborated type is validated as a Type
  or proposition in that open context.
- At an executable call, an erased logical argument may be `_` only for the
  arithmetic fragment. For a logical proposition it must be a named proof: an
  in-scope erased logical parameter or a checked logical global/application of
  one. The proof term is elaborated without runtime bindings and checked by
  `Kernel::check_open` against the proposition, with in-scope erased parameter
  types as validated hypotheses. Earlier erased actual proof terms are
  substituted into a dependent parameter's type before that check. Proof search
  and implicit arguments are not provided. Proofs are first-class logical terms,
  but they have no runtime representation.
- Runtime scalar values may occur inside an erased proposition only as frozen
  symbolic indices (see [runtime indices](runtime-indices.md)); a bare runtime
  value is never evidence of a proposition. Proof parameters are absent from the
  runtime signature, and all logical declarations are erased before reference
  evaluation or native lowering.

This is checked interoperability for a closed logical fragment, not general
dependent runtime indices. Immutable `i64`/`Bool`/`Unit` scalars can index
erased proof types; arbitrary runtime values, machine arithmetic in the kernel,
dependent propositions over mutable values, and total recursion remain
unsupported. Erased parameters may depend on earlier erased binders; total
logical data, constructor-local indices, proposition declarations, and proof
irrelevance are available in the kernel. Effectful or non-total functions are
never accepted as evidence.

Rejected features include ordinary executable `fn` in the logical-only `check`
API, unchecked function interfaces, nonempty effects, attributes/resource
contracts, ordinary owning structs/enums, borrows, grading,
unions/intersections, tuples/slices, nullary/effectful function-type syntax,
machine types, arithmetic operators, Booleans, match/if, mutation,
destructuring lets, early return, I/O, and async. Parsing many of these features
remains supported; kernel checking does not silently erase them.

## 7. Limits, tests, and remaining work

The frontend's existing input/token/nesting limits still apply. Resolution and
elaboration each have a 128-frame nesting budget. Checked source modules are
limited to 256 definitions. Each public kernel operation starts a fresh budget
of 100000 weighted computation units and 128 nested frames. Traversals consume
units; numeric operations additionally charge by the number of base-10^9 limbs
touched. The significant-digit limit in section 8 bounds numeral storage.
Budget exhaustion is an error, not a logical conclusion. Callers can configure
kernel budgets, but changing budgets cannot admit unchecked globals or terms.

Regression tests cover universe stratification, `Prop` formation and
impredicativity, `Prop : Prop` rejection, proof-irrelevance boundaries, large
elimination rejection, dependent binder shifting, capture-avoiding substitution,
false equalities, malformed core terms, induction premises, neutral elimination,
transport, full equality elimination (`J`), positive data admission,
constructor-local binders, named constructor fields, constructor reduction,
positivity/universe/result-index rejection, atomic global and data admission,
cyclic source definitions, dependency ordering, lexical scopes, constructor
ambiguity, unsupported features, source-level induction, transport, and data
elimination, named/anonymous function-type binder scopes, higher-universe
motives, compact-number conversion, carry/borrow behavior, digit/fuel budgets,
erasure at reference/native boundaries, and CLI diagnostics.

Next work should extend the elaboration/type-checking boundary deliberately:
universe-polymorphic equality helpers and a deliberate choice between
Type-valued `Eq` and a Prop-valued propositional equality. A scalar executable
checker and Cranelift backend now exist, and closed erased kernel propositions
are checked and erased at the runtime boundary (section 6). Dependent erased
parameters have open contexts and call-site substitution. Constructor-local
indices and Prop/proof irrelevance are implemented for the conservative
fragment in [propositions](propositions.md); a narrow symbolic bridge lets
immutable `i64`/`Bool`/`Unit` runtime scalars index erased proof types (see
[runtime indices](runtime-indices.md)). General runtime-indexed propositions,
machine arithmetic in the kernel, large elimination from user propositions,
singleton elimination, and general relevance/irrelevance rules remain research
gates. General recursive totals require termination evidence. Resource
modalities, subtyping, effects, erasure, and suspension still have the research
gates stated in the design spec.


## 8. Compact arbitrary-precision naturals

`natural::Natural` stores little-endian base-10^9 limbs. Its storage is private;
constructors parse nonempty ASCII decimal strings or convert a `u64`. Leading
zeroes normalize away. Zero has no limbs, every limb is below 10^9, and the final
limb of a positive value is nonzero. Display and equality use this canonical
representation. The implementation adds no external dependencies.

The core `Literal(Natural)` form inhabits `Nat`. `Term::natural` constructs a
compact positive numeral or `Zero`. Normalization also canonicalizes a directly
constructed `Literal(0)` to `Zero`. `Succ(Literal(n))` increments the stored
number; it never truncates to a machine word. These operations are part of the
kernel's trusted conversion implementation and are tested against independent
host-integer arithmetic where representable, as well as large carry/borrow
vectors and the original constructor equations.

There is no longer a `0..32` literal restriction. A source literal larger than
`u128::MAX`, such as `340282366920938463463374607431768211456`, can be used in
values, dependent indices, and equality proofs. See the
[large-natural example](../examples/large-naturals.kush).

The current compiler uses a **4096 significant decimal digit** budget per
natural number. Leading zeroes and source separators do not consume that budget;
the frontend's file/token limits still apply. Parsing over-budget literals or
normalizing a successor beyond that budget reports an error. This is an explicit
compiler resource limit, not wrapping arithmetic or a fixed-width machine type.
Checking a definition does not promise that every future application can be
normalized within resource budgets. Mathematical `Nat` remains distinct from
future runtime machine integers and allocator-backed runtime big integers.

Induction on a positive numeral decrements it once and applies the same step
rule as an explicit `Succ`. The recursive hypothesis is substituted rather than
eagerly evaluated by the proof normalizer. A step that ignores its hypothesis can
therefore compute a predecessor of a huge numeral in one induction reduction.
A step requiring all previous cases still consumes computation/nesting budget
and may fail. This describes logical normalization, not a change to Kush's eager
runtime evaluation model.

Kernel fuel includes weighted work for numeric inference, normalizing/cloning
numerals during traversals, successor, and predecessor operations. It is a
coarse resource budget, not an exact instruction count, allocation limit, or
real-time guarantee. A limit failure cannot produce evidence, silently turn a
large value into zero, or partially admit a failed global definition.
