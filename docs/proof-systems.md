# Kush's two proof systems

Status: **decided**: option P-A (user, 2026-11-24). Decision input for plan node FND-PROOF-DECIDE
([foundations-review.md](foundations-review.md) section 4). It describes both
systems as they are today, what each can and cannot prove, who uses them,
what is trusted, and the options for making them one story. Every "cannot"
below was checked against the release compiler on 2026-11-24.

## 1. Summary

| | Refinement facts | Dependent kernel |
| --- | --- | --- |
| Written as | `erased q: { 0 <= i && i < n }`, `ensures`, `invariant`, `Vec<u8> where len >= N` | `total fn`, `prop`, `total enum`, `Eq<A, x, y>`, `Nat.induct` |
| Talks about | the running program: `i64`, `u8`…`u64`, `Bool`, lengths, record fields, enum tags, call results | mathematical values: `Nat`, user data, functions, universes |
| Proved by | the compiler, automatically, at every call site (`_`) | the programmer, by writing a proof term |
| Checked by | `facts.rs::verify` (Farkas, cut and branch certificates) | `kernel.rs` (type checking of core terms) |
| Code | `facts.rs`, 3,133 lines, verifier about 240 | `kernel.rs`, 2,228 lines, plus elaboration in `check.rs`/`resolve.rs` |
| Used by | std (137 erased preconditions, loop invariants, `ensures`), the Game Boy (353 bounds checks removed), JSON, crypto | showcase examples, the kernel specification in `examples/kernel/spec` |
| Escape when it fails | a runtime `if` that establishes the fact | none needed: proofs are explicit |

The two systems share the `erased` keyword and nothing else. A kernel proof
cannot discharge an arithmetic precondition, and the kernel cannot state a
fact about a machine integer computation.

## 2. Refinement facts

### What you write

```kush
fn word(data: &Bytes, n: i64, at: i64,
        erased q: { 0 <= at && at + 4 <= n && n == Bytes.len(data) }) -> u32 ! {} {
    let b0: u32 = Int.truncate(Bytes.at(data, at, _));   // `_`: prove it here
    ...
}

fn decide(x: i64, limit: i64) -> Decision ! {}
    ensures Accept(v) => { v == x && x <= limit }
    ensures Reject => { x > limit }
{ if x <= limit { Decision.Accept(x) } else { Decision.Reject } }

while n - i >= 3 invariant { 0 <= i && i <= n } { ... }
```

A proposition is a Boolean combination of linear integer comparisons over
locals, constants, lengths, record field paths, enum tags (`d is Accept`) and
call results. The caller writes `_` and the compiler proves the obligation
from the facts that reach the call: branch conditions, guards, loop
conditions, early exits, earlier `ensures` and erased parameters.

### How it is proved

1. **Fact collection** (in `executable.rs` and `facts.rs`): each point in a
   body has a set of facts. Assignment bumps a local's version, so old facts
   stop matching; a `&mut` borrow makes the owner opaque.
2. **Search**: Fourier–Motzkin elimination over exact rationals, then a
   bounded integer fallback (Chvátal–Gomory cuts and a shallow branch), with
   row, pair and coefficient budgets
   ([integer-refutation.md](integer-refutation.md)).
3. **Certificate**: the search records the multipliers, cuts and branches.
   `facts::verify` rechecks the certificate against the recorded hypotheses
   without trusting the search. Results are cached between builds
   ([proof-cache.md](proof-cache.md)).
4. **Use**: a proved access or arithmetic operation loses its runtime check
   (`KUSH_PROOF_REPORT=1` prints the counts). An access the prover cannot
   prove keeps its check, and `kush test --fuzz` attacks it
   ([proof-fuzz.md](proof-fuzz.md)).

### What it cannot prove

| Goal | Result |
| --- | --- |
| `a * a >= 0` from `0 <= a <= 100` | "cannot prove": products of variables are outside the fragment |
| `a % 8 < 8` from `a >= 0` | "cannot prove": `%` and `/` are outside the fragment |
| `a & 7 < 8` | proved (masks with a constant are special-cased) |
| anything needing induction, quantifiers, or a lemma about a user function | not expressible |
| a fact about a `&mut` parameter in `ensures` | rejected |

When it fails the only remedy is a runtime check (`if r < 8 { f(r, _) }`).
There is no way to supply a proof by hand, even a trivial one.

### What is trusted

- `facts::verify` (arithmetic of the certificate);
- fact collection: that every recorded hypothesis really holds at that point
  (versioning, branch facts, `ensures` instantiation, path terms, overflow
  ranges). This is the larger and more delicate part, and it is not checked
  by anything else;
- checked machine arithmetic: a computed value equals its mathematical value
  because overflow panics.

## 3. The dependent kernel

### What you write

```kush
total fn add(n: Nat, m: Nat) -> Nat ! {} { Nat.induct(ConstantNat, m, add_step, n) }

type RightIdentity<n: Nat> = Eq<Nat, add<n, 0>, n>;

total fn right_identity(n: Nat) -> RightIdentity<n> ! {} {
    induction(RightIdentity, refl::<Nat>(0), right_identity_step, n)
}

prop IsTrue<b: Bool> { Yes: IsTrue<true> }
fn keep_true(b: Bool, erased p: IsTrue<b>) -> i64 ! {} { 4 }
```

The kernel is a dependent type theory with universes (`Type<u>`), an
impredicative `Prop` with proof irrelevance, dependent functions, `Nat` with
induction and compact large numerals, Type-valued `Eq` with transport and `J`,
and positive indexed data families with dependent elimination
([kernel.md](kernel.md), [propositions.md](propositions.md),
[logical-data.md](logical-data.md)).

### How it is checked

The elaborator turns source into explicit core terms; `Kernel::define` checks
each definition's type and value with a deterministic step budget. Nothing is
inferred: no implicit arguments, no proof search, no tactics in the compiler
(the tactic engine in `examples/tactics` is a Kush program that drives the
Kush port of the kernel, not the compiler's kernel). Logical definitions are
erased before runtime code is generated.

### What it cannot do

- **Talk about executable code.** Runtime values enter only as frozen
  symbols of type `i64`, `Bool` or `Unit` (`Eq<i64, n, n>`). There is no
  machine arithmetic in the kernel, so it cannot state `at + 4 <= n` about an
  `i64`, and it cannot unfold an ordinary `fn`.
- **Discharge a refinement.** `f(5, t())` where `f` needs `{ x >= 0 }` and
  `t` is a kernel proof is rejected: "an erased argument must be `_` or the
  name of an erased proof parameter".
- **Recursion** other than through eliminators; no pattern-matching recursion,
  no well-founded recursion, no mutual or nested families.
- **Comfort**: every argument is explicit, `Eq` is not a `Prop`, no function
  extensionality, no quotients, no classical axioms.

### What is trusted

`kernel.rs`, and the elaborator's translation from source to core terms (the
kernel checks the term it is given, not that the term means what the source
says). The Kush port in `examples/kernel` is a second implementation compared
against it, not a proof of it.

## 4. What each one is good for

The refinement system is what makes Kush code faster and safer today: bounds
and overflow checks disappear where a fact proves them, preconditions document
and enforce byte ranges in std, and `ensures` lets callers reason about
results. Its weakness is the wall at the edge of linear arithmetic: past it,
the only tool is a runtime check.

The kernel is what lets Kush state real theorems (induction, equality,
well-scoped syntax in `examples/kernel/spec`). Its weakness is that those
theorems cannot be about the program that runs.

## 5. Options

### P-A. Refinements as the surface, the kernel behind them

Refinements stay the everyday tool. The kernel becomes the place where hard
facts are proved and where certificates are checked.

1. Add integers to the kernel (`Int`, built from the compact `Nat`), and
   translate a `{ ... }` proposition over machine values into a kernel
   proposition over `Int`, with each machine variable's range as a
   hypothesis.
2. **Escape hatch**: when the solver fails, the programmer proves a kernel
   lemma (`total fn sq_nonneg(a: Int) -> Le<0, a * a>`) and cites it at the call
   instead of `_`. This fixes the wall in section 2.
3. **One checker**: either translate each Farkas/cut/branch certificate into
   a kernel proof term, or write the certificate checker as a `total fn` in the
   kernel, prove it sound once, and let the kernel run it (proof by
   reflection). Then `facts::verify` leaves the trusted base.

Fact collection stays trusted in every option; this option shrinks the rest
of the trusted base to the kernel. Cost: large; step 2 gives users value
before step 3 is done.

### P-B. The kernel as the surface

Refinement propositions become ordinary kernel propositions, and proofs about
executable functions are written against logical models of those functions
(as in F* or Lean's verified programming). This needs a way to connect an
`fn` body to a logical specification without unfolding partial code, which
the spec forbids today (section 5.1). Cost: a different language; the largest
option.

### P-C. Keep both, document both

Name `facts::verify` and fact collection as a second trusted checker in the
spec and the reference. Cheap and honest, but it leaves the wall in place and
the kernel disconnected from executable code.

### P-D. Refinements only

Keep the refinement system, take `total fn`, `prop` and the kernel out of the
compiler, and keep the Kush kernel (`examples/kernel`) and tactics as
example programs. Removes about 2,200 lines of kernel plus the logical
elaboration, but gives up the spec's first goal ("full dependent programming
and mathematical proofs") and the kernel specification showcase.

## 6. Recommendation

P-A, in stages, with P-C done immediately so the documents are true while the
work happens: (1) name both checkers in the spec now; (2) `Int` in the kernel
and the translation of `{ ... }`; (3) kernel lemmas as the escape hatch;
(4) certificates checked by the kernel. Each stage ships on its own and the
third is the first one users feel.
