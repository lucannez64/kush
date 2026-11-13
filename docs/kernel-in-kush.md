# Kernel in Kush: design

Status: **implemented** in [examples/kernel](../examples/kernel/README.md)
(milestones M1 to M3): the Kush kernel checks the whole example corpus, data
families included, and agrees with the Rust kernel item by item (section 3);
a specification of its syntax is checked by both kernels and tested against
its substitution (section 4); its API for a tactic engine is section 5. Design approved 2026-11-13 (plan node
KERNEL-IN-KUSH), with the
changes recorded in section 1: the logic is improved in the Rust kernel first
(eta, universe polymorphism), then ported once; the port shares the logic but
not the algorithm.

*Kush checks its own kernel.* This ports the dependent logical kernel
([kernel.md](kernel.md), `crates/kush/src/kernel.rs`) to Kush, in the spirit of
Lean4Lean. The result is an example package, `examples/kernel/`, that reads
kernel terms, checks them and prints its verdicts. Its answers are compared
against the Rust kernel over the example corpus and over generated terms. The
next node, TACTICS-HANDLERS, builds a proof assistant on top of it, so the term
representation and the API are chosen with that client in mind
([showcase roadmap](showcase-roadmap.md)).

This is a second implementation, not a proof of the first. The goal is a
faithful, readable port whose agreement with the Rust kernel is tested
systematically, plus a small logical specification of its syntax whose
theorems the Rust kernel checks.

## 1. Scope and milestones

**Same logic, independent algorithm.** The two kernels accept exactly the same
terms: the typing rules, the conversion relation, `Prop`, irrelevance and the
data rules are identical. If a rule changes, it changes in the Rust kernel
first, as its own plan node with tests, and the port follows; the comparison
then confirms the change in two independent implementations. The *algorithm*
is free: the Kush kernel compares lazily (equal handles first, weak head
normalization, unfolding definitions only on demand) instead of normalizing
both sides fully, which is both faster and a more independent check than a
line-by-line copy. The consequence is that the two kernels run out of budget
on different inputs, so a budget exhaustion on either side is reported as
inconclusive rather than as a disagreement (section 3).

**Logic changes before the port.** Two changes go into the Rust kernel before
porting, so the port is written once against the better logic:

- **Eta for functions** [LOGIC-ETA]: `f ≡ λx. f x` in conversion, as in Lean
  and Rocq.
- **Universe polymorphism** [LOGIC-UNIVERSE-POLY]: definitions and data
  families abstract over universe level variables, instantiated explicitly at
  each use. This replaces both cumulativity and the missing sort polymorphism.

`Eq` in `Prop` (with subsingleton elimination) is a possible later change, a
separate decision. Function extensionality is not planned: as an axiom it
breaks canonicity, so the specification of section 4 states its lemmas
pointwise.

**Library and compiler work before the port.** Arbitrary-precision naturals
[STD-BIGNAT] are a `std` module, so the port handles compact literals from the
start. Lambda expressions in the logical fragment [LOGIC-LAMBDA] and a
per-definition kernel budget [KERNEL-BUDGET-ATTR] are needed by the
specification and come before KIK-SPEC.

**M1, the core** (the first milestone):

- terms with de Bruijn indices, the same constructors as the Rust `Term`;
- `Universe(u)`, `Prop`, `Pi`, `Lam`, `App`, globals with delta unfolding;
- universe levels with variables (the polymorphic levels of LOGIC-UNIVERSE-POLY);
- eta for functions;
- `Nat`, `Zero`, `Succ`, `Literal` (arbitrary precision, from STD-BIGNAT),
  `NatElim`;
- `Eq`, `Refl`, `Transport`, `EqElim` (J);
- `Scalar` and `ScalarLiteral` (they are trivial and can appear in dumps from
  mixed executable files);
- `define`, `check`, `infer`, `normalize`, the step and depth budgets;
- the exchange format, the dump command and the differential harness, passing
  on `examples/proofs.kush` and `examples/induction.kush`.

**M2, inductive families:** `define_indexed_data` (constructor-local binders,
the first-order positivity check, universe computation, `prop` families),
`IndElim` typing (`check_motive`, `branch_type`) and reduction, proof
irrelevance. Passing on `examples/logical-data.kush` and
`examples/finite-proofs.kush`.

**M3, the rest:** the logical specification of section 4, and the API extras
that TACTICS-HANDLERS needs (section 5).

Out of scope: elaboration from Kush source. The Kush kernel reads core terms
produced by the Rust frontend; it does not parse `.kush` files. Self-hosting the
frontend is SELF-HOST.

## 2. Representation

### Terms in an arena

Kush boxes are unique owners: there is no `Rc` and no handle duplication
([ownership.md](ownership.md)). A kernel copies and shares terms constantly
(context lookup, substitution, the motive repeated in every induction step), so
a `Box`-tree port would deep-copy on every share. Instead terms live in an
append-only arena:

```rust
/// A handle to a term in a Store. Copyable; valid for the Store's lifetime.
pub struct Tm { id: i64 }

enum Node {
    Var(i64), Global(i64, i64), Universe(i64), Prop,  // Global: name, level list
    Pi(Tm, Tm), Lam(Tm, Tm), App(Tm, Tm),
    Nat, Zero, Succ(Tm), Literal(i64),
    NatElim(Tm, Tm, Tm, Tm),
    Eq(Tm, Tm, Tm), Refl(Tm, Tm),
    Transport(Tm, Tm, Tm, Tm, Tm, Tm),
    EqElim(Tm, Tm, Tm, Tm, Tm, Tm),
    IndElim(i64, Tm, i64, Tm),   // data, motive, branch list, scrutinee
    Scalar(i64), ScalarLiteral(i64, i64),
}

pub struct Store {
    nodes: Vec<Node>,
    lists: Vec<Tm>,      // branch lists, addressed by (start, length)
    names: Vec<Bytes>,   // interned global names
    table: Vec<i64>,     // open-addressing hash-cons table over nodes
}
```

Universe levels (LOGIC-UNIVERSE-POLY) are hash-consed in the same store as a
small second node kind (`zero`, `succ`, `max`, level variable), so
`Universe` and the level arguments of a `Global` hold level handles.

Every node is **hash-consed**: building a node that already exists returns the
existing handle. Then syntactic equality is handle equality, which turns the
`left == right` fast path of `convert` from a tree walk into one comparison,
and sharing is free. Global names are interned, so a `Global` node holds an
integer, not a byte string.

The arena grows by appending. A handle, once returned, denotes the same term
until the store is rewound past it. That is the property TACTICS-HANDLERS
needs: a backtracking handler that resumes a continuation twice only copies
`Tm` handles, never terms, and both branches can keep allocating into the
same store without invalidating each other.

**Freeing memory.** `store.mark` records the store's size and `store.rewind`
drops every object created since: their slots in the hash table become
tombstones (reclaimed by a rebuild once they fill a quarter of the table),
the cells are reused by later objects, and the traversal caches are
invalidated. A rewind costs time proportional to what it drops. The kernel
rewinds after checking each definition (keeping only its entry; a data
family's types and universe level are rebuilt after the rewind) and the
`check` command after answering each query. 2,000 normalize queries run in
6 MB instead of 26 MB. After a failure the terms are kept, so the failure can
be inspected (`api.last_failure`); `api.mark`/`api.rewind` let a client free
what it built, for instance when a tactic search abandons a branch.

### De Bruijn indices, not locally nameless

The Rust kernel uses zero-based de Bruijn indices throughout, and the port keeps
them. Locally nameless would read better in places (going under a binder with
a fresh free name instead of tracking shifts), but with identical indices the
normal forms both kernels print can be compared as text, with no
alpha-renaming step in the harness. TACTICS-HANDLERS can add named goals on top: its proof states
are its own data and submit closed core terms to the kernel.

### Contexts and environments

A context is a stack of `Tm` types, each relative to the entries before it,
exactly as in Rust (`Vec<Tm>` with push/pop). The global environment maps an
interned name to one of `Definition { ty, value }`, `Data { info, ty }` or
`Constructor { data, index, ty }`. Data descriptions (`DataInfo`,
`ConstructorInfo`) are records of `Tm` lists.

### Errors and budgets

Kernel functions return `Result<T, KernelError>`, propagated with `?`, and are
pure apart from the store: effect rows are `{alloc, panic}`. `KernelError` is
an enum, not a string: `TypeMismatch(expected, actual)`, `NotAFunction(tm)`,
`UnboundVariable(i)`, `UnknownGlobal(name)`, `BudgetExhausted`,
`DepthExhausted`, `Positivity(name)`, and so on, carrying handles so that a
tactic can inspect a failure. The verdict printer maps each to the same
category the Rust kernel reports.

The Kush kernel has its own step budget with the Rust kernel's default
(100,000,000 steps, raised per declaration by `(steps N)` in the exchange
file) but its own charging points. Its nesting cap is the Rust kernel's,
100,000 levels: its command line runs on a 1 GiB stack (`#[stack_size(1024)]`
on `main`, LANG-STACK-SIZE), which holds that depth with a wide margin, while
the default 8 MB stack overflowed near 20,000 levels. A budget exhaustion is
reported as its own outcome, so the harness can tell "gave up" from
"disagrees".

## 3. Comparison against the Rust kernel

### The exchange format

A small canonical S-expression syntax for core terms and declarations, written
by Rust and read by Kush:

```text
(def add (pi nat (pi nat nat)) (lam nat (lam nat (natelim ... ))))
(data Fin (nat) type
  (ctor FZero (nat) () ((succ (var 0))))
  (ctor FSucc (nat) ((Fin (var 0))) ((succ (var 1)))))
(check <term> <type>)          ; a query: expect accept or reject
(normalize <term>)             ; a query: print the normal form
```

Both sides print normal forms with the same canonical printer, so the
comparison is a text diff. The Kush kernel still has a `normalize` entry point
for these queries; only conversion is lazy.

The format is specified in [kernel-exchange.md](kernel-exchange.md) (implemented).

Rust side, behind a new subcommand `kush core <file.kush>`: check the file as
`kush check` does, then print the admitted environment in admission order, one
declaration per line, then a `normalize` query for every definition. This is a
printer over the existing `Term` and `DataInfo`; it adds nothing to the
trusted kernel.

Kush side: `examples/kernel` reads a file in this format, admits each
declaration with its own kernel, answers each query, and prints one line per
item: `ok`, `reject <category>`, `budget`, or a normal form.

### What gets compared

1. **The corpus.** Every logical example (`proofs`, `induction`,
   `logical-data`, `finite-proofs`, `large-naturals`) and the logical parts of
   the test fixtures. Expected: every declaration is admitted and every normal
   form matches.
2. **Mutations of the corpus.** A Rust-side mutator takes each admitted
   definition and applies small edits: shift one variable index, bump a
   universe level, replace `Zero` with `Succ(Zero)`, drop or swap an
   application argument, swap two eliminator branches, flip a family between
   `type` and `prop`. The Rust kernel decides each mutant; the Kush kernel must
   reach the same verdict. Most mutants are rejected, which exercises the error
   paths that the corpus alone never reaches.
3. **Generated terms.** A seeded, dependency-free generator (a small xorshift
   in Rust) builds well-typed terms by construction: pick a goal type, then a
   rule that produces it (a variable of that type from the context, a lambda for
   a Pi, an application with a generated argument, an eliminator with a
   generated motive). Plus random well-scoped but untyped terms for the reject
   side. A failing seed is shrunk by hand and promoted into a fixture.
4. **The negative kernel tests.** The malformed core terms in
   `crates/kush/tests/kernel.rs` are dumped once into a fixture so the Kush
   kernel faces the same boundary cases (positivity, large elimination from
   `Prop`, universe escape, `Prop : Prop`).

Agreement means the same verdict on every item where both kernels finish, and
the same normal form on every accepted `normalize` query. Error categories are
compared coarsely (accept versus reject), since a different algorithm may find
a different first error. A budget exhaustion on either side makes that item
inconclusive; the harness counts inconclusive items and fails if they exceed a
small fraction, so a slow port cannot hide behind them.

### Harness (implemented, KIK-DIFF)

Both kernels answer the same exchange files: `kush kernel FILE` (Rust) and
`kernel check FILE` (the Kush package). The Rust tests compare them item by
item:

- `crates/kush/tests/kernel_in_kush.rs`: the package tests, the corpus
  printed back byte for byte, normal forms of the corpus and of targeted
  reductions, and checking of the corpus files without data families plus a
  file of typing cases that are mostly rejections;
- `crates/kush/tests/kernel_diff.rs`: mutants of every corpus definition
  (index and level bumps, `zero` to `succ zero`, dropped or swapped
  applications, `pi`/`lam` swaps, wrong universe arguments, swapped
  branches), and seeded generated terms (beta redexes, `NatElim`,
  `Transport`, `J`, higher-order functions) with their own mutants.

`scripts/kernel-diff.sh [SEEDS]` runs both with more seeds (2000 by
default). At KIK-DIFF it compared 171,236 generated items and 312 corpus
mutants with no disagreement and no inconclusive item.

## 4. Invariants checked by the Rust kernel

The executable kernel cannot be proved correct inside Kush today: logical
definitions are erased and executable code cannot call or mention them
([kernel.md section 6](kernel.md)). What can be done is to state the kernel's
syntax and its basic operations in the logical fragment, where the Rust kernel
checks them, and to tie that specification to the implementation by testing.

[`examples/kernel/spec/scoped.kush`](../examples/kernel/spec/scoped.kush), a
logical-only file (implemented, KIK-SPEC; 53 definitions):

- **Well-scoped syntax.** `total enum Tm<N: Nat>` with `Var(x: Fin<N>)`,
  `Sort(level: Nat)`, `App`, and the binders `Lam` and `Pi`, whose bodies are
  `Tm<Nat.succ<N>>`. A term of type `Tm<n>` has at most `n` free variables by
  construction. (`Nat`, `Zero` and `Succ` would add only congruence cases.)
- **Variables by recursion.** `Fin<0> = Empty`, `Fin<n + 1> = Maybe<Fin<n>>`,
  defined with `Nat.induct` into `Type`: `None` is the newest variable and
  `Some x` is `x` one binder out. Because `Fin<n + 1>` *is* `Maybe<Fin<n>>` by
  computation, going under a binder is a `Maybe` case analysis. An indexed
  `Fin` family would need index inversion (heterogeneous equality) for the
  lemmas below, which this kernel does not provide.
- **Operations with scope in their types.** `rename<n, m>(t: Tm<n>, r:
  fn(x: Fin<n>) -> Fin<m>) -> Tm<m>`, `lift` of a renaming under a binder,
  `shift<n>(t: Tm<n>) -> Tm<n + 1>`, simultaneous substitution
  `subst<n, m>(t: Tm<n>, s: fn(x: Fin<n>) -> Tm<m>) -> Tm<m>` with `under` (a
  substitution under a binder), and `subst0<n>(b: Tm<n + 1>, u: Tm<n>) ->
  Tm<n>`. That these definitions are admitted *is* the statement "renaming,
  weakening and substitution preserve well-scopedness".
- **Equational lemmas**, by `Data.elim` with pointwise hypotheses (there is
  no function extensionality):
  - `map_id`, `rename_id`: renaming by a pointwise identity is the identity;
  - `under_ext`, `subst_ext`: substitution respects pointwise equality;
  - `under_compose`, `subst_rename`: renaming then substituting is
    substituting the composition;
  - `under_var`, `subst_var`: substituting each variable by itself is the
    identity;
  - `subst0_shift`: `subst0(shift(t), u) = t`, from the three above.
- **Computed examples**: `(λ. 0) u` reduces to `u`, a non-substituted
  variable moves one binder out, and `shift (λ. 0 1) = λ. 0 2`, each proved by
  `refl`.

`kush check` admits the file, so the Rust kernel checks these invariants
(about a minute in a debug build). The Kush kernel admits the same
declarations from the exchange dump, in about 4 seconds, and rejects a
corrupted proof (`crates/kush/tests/kernel_spec.rs`). So Kush checks the proofs
about its own syntax. The full comparison including every normal-form query is
an ignored test that `scripts/kernel-diff.sh` runs.

**Linking the specification to the implementation** (implemented,
KIK-SPEC-DIFF, `crates/kush/tests/kernel_spec_diff.rs`). The Rust kernel
computes with the specification: for generated raw terms `b` (scope `n + 1`)
and `u` (scope `n`), it normalizes `subst0<n>(b, u)` on their encodings as
`Tm` values, and the normal form is decoded back to a raw term. The Kush
kernel normalizes `λⁿ. (λ. b) u`, which runs its own `substitute` (and the
`shift` it applies under binders) at depth `n`. The two terms must be equal.
The generator never puts a lambda in function position and never substitutes
one, so the normal form is exactly one substitution. A planted off-by-one in
the Kush kernel's substitution is caught within the first cases. This is a
differential test of the implementation against a kernel-checked
specification, not a proof; 100 cases run in the default suite and
`scripts/kernel-diff.sh` runs 1000.

Executable-side facts that are arithmetic (a variable index is below the
context depth, a handle is below the arena length) are stated with `ensures`
and erased arithmetic preconditions where the prover can discharge them, and
left as runtime checks where it cannot.

## 5. API for TACTICS-HANDLERS (implemented, KIK-API)

`examples/kernel/src/api.kush` is the interface a client such as a tactic
engine uses. Terms are store ids (`Tm` handles); a **context** is a list of
hypothesis types, outermost first, each relative to the ones before it.

```text
infer(k, context, t)          -> type of t (not normalized)
check_term(k, context, t, ty) -> t : ty
sort(k, context, ty)          -> level id, or check.PROP_SORT
whnf(k, context, t)           -> weak head normal form (a goal's head)
normalize(k, context, t)      -> full normal form
defeq(k, context, a, b)       -> definitional equality (false across types)
abstract(k, t, u)             -> t with u replaced by a new innermost variable
instantiate(k, body, value)   -> body with index 0 replaced by value
last_failure(k, code)         -> Failure { code, term, expected, actual, depth }
describe(code)                -> a short description
```

Declarations are admitted with `check.define` and `check.define_data`; terms
are built with `kernel.term` and read with `reader.read_term`.

- **Everything is checked.** Each operation validates every hypothesis as a
  type or proposition and checks its terms before computing with them, so
  `whnf` and `normalize` refuse an ill-typed term instead of reducing it.
- **`abstract`** is the operation behind `generalize` and `rewrite`: `λy.
  abstract(t, u)` is the motive that replaces `u` in `t`, and
  `instantiate(abstract(t, u), u)` is `t` again (the same id). Occurrences of
  `u` are found shifted under `t`'s binders, and with hash-consing each test
  is one id comparison.
- **Failures are inspectable.** A failing operation returns an error code;
  `last_failure` gives the innermost failing term, the expected and actual
  types where there are such, and the context size they are relative to (the
  operation's context plus the binders it had entered). For a type mismatch
  that is the term, the expected type and the inferred one; for an
  application of a non-function, the function and its type.
- **Proof states are copyable.** A tactic's state holds only `Tm` handles
  (integers), and a handle stays valid and means the same term until the
  store is rewound past it (`api.mark`/`api.rewind`). A multishot `Choose` handler can resume a continuation
  twice and both branches keep allocating into the same store
  ([effect handlers](effect-handlers.md); multishot resumption across calls
  is EFF-CAP-RESUME-MULTISHOT, already a dependency of TACTICS-HANDLERS). The
  store itself is owned by the outermost handler or driver and reached
  through `&mut`, never captured by a resumable continuation.

## 6. Expected language limits

Each of these becomes its own plan node, with compiler tests and docs, when it
actually blocks the port; until then the workaround stands.

- **No shared ownership.** Handled by design with the arena (section 2);
  memory is reclaimed with `mark`/`rewind`.
- **Collections.** The standard library has `Vec`, `Bytes` and a byte-keyed
  `bytemap`, no general hash map. The hash-cons table and the global
  environment are written by hand over `Vec<i64>`. If generic containers with a
  user hash trait become necessary this is a library node, not a compiler one.
- **Enum and function limits.** 64 variants and 32 words per concrete enum,
  1,024 resource slots per function, 256 concrete enum instantiations
  ([enums.md](enums.md)). `Node` fits (21 variants, at most seven words). A
  large `match` in `infer` or `convert` may hit the per-function slot limit and
  need splitting.
- **Recursion depth.** The kernel is recursive. The depth budget of 128 bounds
  it as in Rust, so native stack use stays small; the reader of the exchange
  format must be iterative or depth-limited too.
- **Arbitrary-precision naturals.** There is no big integer type. STD-BIGNAT
  adds a limb-vector natural to `std` before the port, with the operations the
  kernel uses: parse, print, compare, successor, predecessor and the work
  measure.
- **The logical fragment, for section 4.** Lambda expressions are available
  (LOGIC-LAMBDA, [kernel.md](kernel.md#lambda-expressions)), and a long proof
  can raise its step budget with `#[kernel_steps(N)]` (KERNEL-BUDGET-ATTR). No
  implicit arguments, and no function extensionality (hence pointwise lemma
  statements).
- **No link between the logical and executable worlds.** Executable code cannot
  call or mention a logical definition, so the specification and the
  implementation are connected only by testing (section 4). Closing that gap is
  research beyond this node.
- **Text processing.** Parsing the exchange format uses `Bytes` and
  `std.text`; that should be enough, but error positions and diagnostics may
  push on missing formatting helpers.

### Found while building the port

- **No enum equality**, so the store interns every object as a flat list of
  `i64` cells and compares cells; term nodes are read by tag and field index
  instead of by pattern matching on a `Node` enum. This turned out simpler
  than a `Node` enum plus a hand-written equality.
- **Call-scoped `&mut` loans last through later arguments**:
  `f(level_max(&mut s, a, b), level_max(&mut s, b, a))` is rejected, by
  design (`tests/borrowed_records.rs`). Store-building code names each result
  with a `let` first.
- **`std.env.arg` and `std.fs.read` append into the buffer's existing
  capacity** and fail with `EFBIG` when it is full, so a zero-capacity buffer
  always fails; `main.kush` reads files with a doubling retry.
- **No two-phase borrows for calls**: `normal(k, term.field(&k.store, t, 3))`
  is rejected because `k` is lent exclusively while a later argument still
  reads it. Reads of the store are hoisted into `let`s first. Two disjoint
  field borrows (`&mut k.store` beside other fields) work. To fix:
  LANG-TWO-PHASE-CALLS.
- **A `match` scrutinee's exclusive loan lasts through its arms**, even when
  the matched value (`Result<i64, i64>`) holds no borrow; the result is bound
  with a `let` first. To fix: LANG-MATCH-SCRUTINEE-LOAN.
- **Module imports cannot be renamed**: `kernel.env` clashed with `std.env`,
  so the kernel state module is `kernel.engine`. To fix: LANG-IMPORT-ALIAS.
- **`refl` is a reserved name** even for a module function; the constructor is
  `term.reflexive`.
- An explicit `drop` after a condition's borrow was rejected; fixed in the
  compiler (LANG-DROP-AFTER-BORROW).

## 7. Plan

Sub-nodes of KERNEL-IN-KUSH, one small commit each:

| Node | Content | Depends on |
| --- | --- | --- |
| LOGIC-ETA | Eta for functions in the Rust kernel's conversion; tests; docs | |
| LOGIC-UNIVERSE-POLY | Universe level variables in the Rust kernel and elaborator; tests; docs | LOGIC-ETA |
| STD-BIGNAT | Arbitrary-precision naturals in `std` | |
| KIK-EXCHANGE | Exchange format; Rust printer; `kush core` subcommand; tests | LOGIC-UNIVERSE-POLY |
| KIK-STORE | Package skeleton; `Store`, hash-consing, interning; reader and printer; round-trip tests | KIK-EXCHANGE, STD-BIGNAT |
| KIK-SUBST | `shift`, `substitute`, `rewrite_outer`, level substitution; unit tests | KIK-STORE |
| KIK-NORMAL | Weak head and full normalization: beta, delta, `NatElim`, numerals, `Transport`, J; budgets | KIK-SUBST |
| KIK-CHECK | `infer`, `check`, `sort`, lazy conversion with eta, `define`; scalars | KIK-NORMAL |
| KIK-DIFF | Corpus dump, mutator, generator, `scripts/kernel-diff.sh`, Rust test; M1 done | KIK-CHECK |
| KIK-DATA | Indexed families, positivity, `IndElim`, `prop`, proof irrelevance; M2 done | KIK-DIFF |
| LOGIC-LAMBDA | Lambda expressions in the logical fragment | |
| KERNEL-BUDGET-ATTR | Per-definition kernel budget annotation | |
| KIK-SPEC | Well-scoped syntax specification and lemmas (section 4) | KIK-DATA, LOGIC-LAMBDA, KERNEL-BUDGET-ATTR |
| KIK-SPEC-DIFF | Specification-versus-implementation substitution tests | KIK-SPEC |
| KIK-API | `whnf`, `abstract`, structured errors documented for TACTICS-HANDLERS | KIK-DATA |

Language gaps found along the way get their own nodes as they appear.
