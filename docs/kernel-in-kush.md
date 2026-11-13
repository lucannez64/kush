# Kernel in Kush: design

Status: **design, awaiting approval** (plan node KERNEL-IN-KUSH). Nothing here
is implemented yet.

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

The port mirrors the Rust kernel's rules exactly, including its quirks: no
cumulativity, no eta, Type-valued `Eq`, `Prop : Universe(0)` with impredicative
`Pi`, proof irrelevance as a conversion rule only, normalize-then-compare
conversion, and the same step and depth budgets. Matching the reference
exactly is what makes differential testing meaningful. Improvements (weak head
normalization, eta, faster conversion) wait until the port agrees with the
reference, and then go into both kernels together, or into the Kush one only
behind a separate entry point that the comparison does not use.

**M1, the core** (the first milestone):

- terms with de Bruijn indices, the same constructors as the Rust `Term`;
- `Universe(u)`, `Prop`, `Pi`, `Lam`, `App`, globals with delta unfolding;
- `Nat`, `Zero`, `Succ`, `Literal` (64-bit in M1), `NatElim`;
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

**M3, the rest:** arbitrary-precision literals (`examples/large-naturals.kush`),
the logical specification of section 4, and the API extras that
TACTICS-HANDLERS needs (section 5).

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
    Var(i64), Global(i64), Universe(i64), Prop,
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

Every node is **hash-consed**: building a node that already exists returns the
existing handle. Then syntactic equality is handle equality, which turns the
`left == right` fast path of `convert` from a tree walk into one comparison,
and sharing is free. Global names are interned, so a `Global` node holds an
integer, not a byte string.

The arena is append-only. A handle, once returned, stays valid and denotes the
same term forever. That is the property TACTICS-HANDLERS needs: a backtracking
handler that resumes a continuation twice only copies `Tm` handles, never
terms, and both branches can keep allocating into the same store without
invalidating each other. Garbage is never freed during a run; a `mark`/`rewind`
pair (truncate the arena to an earlier length when nothing newer is live) is
the escape hatch if memory becomes a problem.

### De Bruijn indices, not locally nameless

The Rust kernel uses zero-based de Bruijn indices throughout, and the port keeps
them. Locally nameless would read better in places (going under a binder with
a fresh free name instead of tracking shifts), but it would change where
shifting happens, and with it the normal forms the two kernels print and the
order in which fuel is charged. With identical indices, normal forms can be
compared as text. TACTICS-HANDLERS can add named goals on top: its proof states
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

Fuel and depth follow the Rust `Engine` exactly: the same `step` and `charge`
points, defaults of 100,000 steps and depth 128. A budget exhaustion is
reported as its own outcome, so the harness can tell "both gave up" from "they
disagree".

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
comparison is a text diff.

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

Agreement means the same verdict category on every item and the same normal
form on every accepted `normalize` query. Fuel used is printed by both sides
and compared too, but only reported, not required: it is a good canary for an
unfaithful port, but making it a hard requirement would freeze both kernels'
internal traversal order.

### Harness

`scripts/kernel-diff.sh` runs the whole comparison: build the Kush kernel once
with `kush build`, dump each corpus file with `kush core`, generate mutants and
random terms for a fixed list of seeds, run both, diff. A Rust integration test
(`crates/kush/tests/kernel_in_kush.rs`) runs a small fixed slice of it in the
normal test suite; the full run with more seeds is the script.

## 4. Invariants checked by the Rust kernel

The executable kernel cannot be proved correct inside Kush today: logical
definitions are erased and executable code cannot call or mention them
([kernel.md section 6](kernel.md)). What can be done is to state the kernel's
syntax and its basic operations in the logical fragment, where the Rust kernel
checks them, and to tie that specification to the implementation by testing.

`examples/kernel/spec/scoped.kush`, a logical-only file:

- **Well-scoped syntax.** `total enum Tm<n: Nat>` with a `Var(Fin<n>)`
  constructor and binders that take `Tm<Nat.succ<n>>` bodies (the M1 fragment:
  sorts, Pi, Lam, App, Nat, Zero, Succ). A term of type `Tm<n>` has at most `n`
  free variables by construction.
- **Renaming and substitution with scope in their types.**
  `rename: (r: fn(Fin<n>) -> Fin<m>) -> Tm<n> -> Tm<m>`, `lift` of a renaming
  under a binder, `shift: Tm<n> -> Tm<Nat.succ<n>>`, simultaneous substitution
  `fn(Fin<n>) -> Tm<m>`, and `subst0: Tm<Nat.succ<n>> -> Tm<n> -> Tm<n>`. That
  these definitions are accepted *is* the statement "weakening and substitution
  preserve well-scopedness".
- **Equational lemmas**, proved by `Data.elim` with pointwise hypotheses
  (there is no function extensionality): renaming by a pointwise identity is
  the identity; renamings compose; `subst0(shift(t), u) = t`; substituting a
  variable for itself is the identity.

These are checked by `kush check`, so the Rust kernel checks the invariants.
The same file is also in the differential corpus, so the Kush kernel checks the
proofs about its own syntax as well.

**Linking the specification to the implementation.** The Rust kernel can
compute with the specification: normalizing `subst0(t, u)` for concrete closed
`Tm` values yields a concrete `Tm`. A generator produces such cases, the Rust
kernel prints the specification's answer, and the Kush implementation's
`substitute` and `shift` on the corresponding raw terms must produce the same
term. This is a differential test of the implementation against a
kernel-checked specification, not a proof; it is the stretch goal of M3.

Executable-side facts that are arithmetic (a variable index is below the
context depth, a handle is below the arena length) are stated with `ensures`
and erased arithmetic preconditions where the prover can discharge them, and
left as runtime checks where it cannot.

## 5. API for TACTICS-HANDLERS

The kernel is a library module of the package (`kernel.core`), with the
checker as a thin `main` on top. Public functions:

```text
store / build    Store.new, mk_pi, mk_lam, mk_app, ..., view(store, tm) -> Node
admit            define(env, name, ty, value), define_data(env, spec)
check            infer(env, ctx, tm), check(env, ctx, tm, ty), sort(env, ctx, tm)
compute          normalize(env, ctx, tm), whnf(env, ctx, tm), defeq(env, ctx, a, b)
binders          shift(tm, k), instantiate(body, arg), abstract(tm, var)
```

`whnf` and `abstract` are not in the Rust kernel. A tactic engine needs them
(inspect the head of a goal; turn a hypothesis into a binder), and they are not
used by the differential path. A tactic's proof state holds only `Tm` handles,
so it is copyable, which is what a multishot `Choose` handler requires
([effect handlers](effect-handlers.md); multishot resumption across calls is
EFF-CAP-RESUME-MULTISHOT, already a dependency of TACTICS-HANDLERS). The store
itself is owned by the outermost handler or driver and reached through `&mut`,
never captured by a resumable continuation.

## 6. Expected language limits

Each of these becomes its own plan node, with compiler tests and docs, when it
actually blocks the port; until then the workaround stands.

- **No shared ownership.** Handled by design with the arena (section 2). The
  cost is that the arena is never collected during a check.
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
- **Arbitrary-precision naturals.** There is no big integer type. M1 stores
  literals as `i64` and reports larger ones as an unsupported item (its own
  harness category, not a disagreement). M3 adds a limb-vector natural with
  only the operations the kernel uses: parse, print, compare, successor,
  predecessor and the work measure.
- **The logical fragment, for section 4.** No lambda expressions (motives and
  renamings are named `total fn`s and aliases), no implicit arguments, no
  sort polymorphism, no eta and no function extensionality (hence pointwise
  lemma statements), and the default budget of 100,000 steps and depth 128.
  Long equational proofs about `Tm` may exceed the budget; the likely fix is a
  per-file or per-definition budget annotation, which would be a compiler node.
- **No link between the logical and executable worlds.** Executable code cannot
  call or mention a logical definition, so the specification and the
  implementation are connected only by testing (section 4). Closing that gap is
  research beyond this node.
- **Text processing.** Parsing the exchange format uses `Bytes` and
  `std.text`; that should be enough, but error positions and diagnostics may
  push on missing formatting helpers.

## 7. Plan

Sub-nodes of KERNEL-IN-KUSH, one small commit each:

| Node | Content | Depends on |
| --- | --- | --- |
| KIK-EXCHANGE | Exchange format; Rust printer; `kush core` subcommand; tests | |
| KIK-STORE | Package skeleton; `Store`, hash-consing, interning; reader and printer; round-trip tests | KIK-EXCHANGE |
| KIK-SUBST | `shift`, `substitute`, `rewrite_outer`, spine; unit tests | KIK-STORE |
| KIK-NORMAL | Normalization: beta, delta, `NatElim`, numerals, `Transport`, J; budgets | KIK-SUBST |
| KIK-CHECK | `infer`, `check`, `sort`, `convert`, `define`; scalars | KIK-NORMAL |
| KIK-DIFF | Corpus dump, mutator, generator, `scripts/kernel-diff.sh`, Rust test; M1 done | KIK-CHECK |
| KIK-DATA | Indexed families, positivity, `IndElim`, `prop`, proof irrelevance; M2 done | KIK-DIFF |
| KIK-BIGNAT | Arbitrary-precision literals | KIK-DIFF |
| KIK-SPEC | Well-scoped syntax specification and lemmas (section 4) | KIK-DATA |
| KIK-SPEC-DIFF | Specification-versus-implementation substitution tests | KIK-SPEC |
| KIK-API | `whnf`, `abstract`, structured errors documented for TACTICS-HANDLERS | KIK-DATA |

Language gaps found along the way get their own nodes as they appear.
