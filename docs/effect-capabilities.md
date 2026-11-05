# Lexical capability handlers alongside declared dynamic handlers

Status: **design** (RES-EFFECT-CAPABILITY). Nothing here is implemented. The
decisions below fix the semantics a capability feature must have so that it
can coexist with today's handlers without changing which handler any existing
program observes. Implementation is split into the plan nodes listed at the
end.

Inputs, used as design references, not as transferred results:

- Lexa, "Lexical Effect Handlers, Directly" (OOPSLA 2024) and
  "Zero-Overhead Lexical Effect Handlers" (OOPSLA 2025,
  [paper](https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf)):
  handlers are passed as explicit, second-class capabilities, so a perform
  names its handler statically and needs no search; the 2025 paper keeps the
  mainline (no effect raised, or a tail-resumptive one) as cheap as a call and
  pays only on rare, non-resumptive paths.
- Katsumata, "Parametric Effect Monads and Semantics of Effect Systems"
  (POPL 2014): a graded (effect-indexed) semantics whose index algebra is an
  ordered monoid. Used only to list the algebraic laws Kush's rows must
  satisfy (section 4); no monadic source translation.

## 1. What Kush has today

| Mechanism | How a perform finds its handler | Cost per perform (E-PERF, section 14.3 of effect-state-machines.md) |
| --- | --- | --- |
| Lexical `handle Name` (undeclared name) | innermost enclosing `handle` in the same function, statically | tail-resumptive: ~5-8 ns (in place) |
| Declared `effect Op`, perform in a called function | innermost frame for `Op` on the per-task dynamic handler stack | tail-resumptive: ~11 ns; non-tail: ~210 ns |
| Non-tail handler, lexical perform | static, state machine | ~120 ns |

A direct call costs ~3.5 ns. The dynamic-lookup overhead for a frequent,
tail-resumptive operation in a called function is therefore a few
nanoseconds (search + frame bookkeeping), and non-tail costs are dominated by
continuation environments, not by lookup.

Semantics that must be preserved by anything new:

- **Dynamic scoping of declared operations.** A function declaring `{Op}`
  sees the innermost dynamically active handler at the time of the perform,
  including handlers its caller installed after the callee was written.
- **Missing handler** aborts at run time and is reflected by `panic` in the
  row.
- **Owned frames.** A capturing `once` handler frame owns its environment;
  consumed-once frames stop lookup (user-approved behaviour).
- **Task inheritance barrier.** A spawned task inherits only the contiguous
  suffix of copyable noncapturing frames.
- **One-shot tokens and cleanup**, and the E-CPS rules for resumption across
  calls (resumable entries, redirects).

## 2. The question

Should Kush add Lexa-style capabilities, and if so with which semantics, so
that (a) frequent resumptive operations in called functions can be resolved
statically, (b) existing dynamic programs keep their meaning, and (c) the
rare/exceptional path is handled separately?

## 3. Design

### 3.1 Surface

```text
handle Op as op with h { body }        -- binds a capability `op` in body
fn step(op: cap Op, x: i64) -> i64 ! {panic} { perform op(x) + 1 }
step(op, 1)                             -- pass it explicitly
```

- `cap Op` is a new **second-class** parameter type. Its value is the pair
  (handler code pointer, handler environment pointer) of one specific
  `handle` activation. It is not a row bit.
- `perform op(x)` calls exactly that handler. It never consults the dynamic
  stack and is legal in any function that receives `op`, whatever its row.
- The existing `perform Op(x)` keeps its current meaning (lexical first, then
  dynamic for declared operations). A `handle Op as op` *also* pushes the
  dynamic frame when `Op` is declared, so callees written against the
  dynamic interface still see it. Capability use is opt-in per call site.

### 3.2 Second-class rule

A `cap` value may be passed as an argument and forwarded, but cannot be
stored in a local of another type, a field, a tuple, a closure environment
that escapes, a task, a return value, or a resumption payload. This is
exactly the existing **scoped borrowed-capture** discipline: the capability
is a borrow of the `handle` activation with that activation's extent as its
region. Reusing those rules (and the E-CPS-BORROW argument that suspension
never pops the owning activation) gives the safety argument without a new
lifetime system. A `cap` captured by a non-escaping lambda follows the
by-reference-closure rules, including rejection across a non-tail perform.

### 3.3 Effects

The capability type carries the handler's own row: `cap Op ! {io}`. A call
`perform op(x)` adds that row to the caller's row (it runs the handler's
code), but not a bit for `Op` itself and not `panic` for a missing handler,
since the handler is known to exist. Subtyping: `cap Op ! {e1}` may be used
as `cap Op ! {e2}` when `e1 ⊆ e2`.

### 3.4 Resumption

- **Tail-resumptive handler:** `perform op(x)` is an indirect call of the
  handler with the identity token: the 5-8 ns lexical path, now available
  across calls.
- **Non-tail handler:** a function taking `cap Op` whose body performs through
  it gets a resumable entry exactly like E-CALLEE-COLOR, keyed by the
  capability parameter instead of the row bit. The callee-coloring analysis
  becomes "functions that perform through a cap parameter that may be bound
  to a non-tail handle", computed per call site from the argument, which is
  always statically one `handle` activation or a forwarded cap parameter.
- **Multishot:** unchanged constraints (copyable, ungraded live values).

### 3.5 Frequent versus rare paths

Kush handlers must resume (the token is linear), so there is no
abortive/exceptional handler today: errors use `Result` and `?`. The Zero
Lexa split therefore maps to:

- **mainline**: capability performs with tail-resumptive handlers, compiled
  as calls; this is the only path the feature should optimize;
- **rare**: abort-like handlers that do not resume. They require unwinding
  frames between the perform and the handle while dropping their live owned
  values. Kush has no unwinding; this is a separate design (E-ABORT-DESIGN, decided in
  [abortive handlers](abortive-handlers.md))
  and must not be smuggled in through capabilities.

### 3.6 What does not change

- No existing program changes meaning: `perform Op(x)` lookup, missing-handler
  aborts, frame ownership, task inheritance and redirect frames are untouched.
- No row-polymorphic handler types over operation names.
- Capabilities do not cross task boundaries (second-class), so the inheritance
  barrier needs no change.

## 3.7 As built (EFF-CAP-LEXICAL)

Implemented for **declared** operations and **noncapturing, one-shot,
tail-resumptive** handlers (`crates/kush/tests/effect_capabilities.rs`):

```text
effect Ask: i64 -> i64;
fn step(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { perform op(x) + 1 }
handle Ask: i64 -> i64 as ask with fn(x: i64, resume: linear once fn(i64) -> i64 ! {})
    -> i64 ! {panic} { resume(x + 100) } { step(ask, 1) }
```

- `as` and `cap` are contextual: `as` only after a handled signature, `cap`
  only at the start of a type followed by a name; `let cap = 1; let as = 2;`
  and fields named `cap`/`as` keep working (tested).
- `cap Op ! {e}` lowers to the handler arrow
  `fn(P, linear once fn(R) -> R ! {}) -> R ! {e}`; arrow subtyping gives
  `cap Op ! {e1}` <: `cap Op ! {e2}` for `e1 ⊆ e2`. The runtime value is the
  handler's function pointer: noncapturing, copyable, never dropped, so no
  environment can be freed under a capability.
- `perform op(x)` is an indirect call of that handler with the identity
  token: the existing in-place tail-resumptive path, with no dynamic lookup,
  no `Op` row bit and no `panic` for a missing handler; the handler's row is
  required. A capability names one activation: an inner dynamic handler for
  the same operation does not intercept it (tested).
- **Second class.** A capability local may only be passed by name to a `cap`
  parameter of a named function or used as `perform op(..)`; any other read
  (let, return, field, call, function argument, lambda capture) is rejected.
  `cap` types are allowed only as the whole type of a named function
  parameter; functions with a `cap` parameter cannot become function values.
- **Dynamic visibility (refinement of 3.1).** A pure handler bound `as op`
  also pushes the dynamic frame, as written above. A handler with effects
  cannot be dynamically visible (callers' rows would hide its effects), so it
  is capability-only: performs of `Op` by name inside the body's called
  functions reach an outer handler or abort with `panic`, exactly like a
  missing handler (tested in both backends). No existing program is affected:
  the `as` form is new.
- **Non-tail, multishot and capturing handlers (EFF-CAP-RESUME, scoped with
  the user).** Any handler may be bound `as op`. A perform through the
  capability in its own `handle` body uses the lexical machinery of that
  activation (state machines for non-tail, copied continuations for
  multishot), chosen by activation rather than by name, and agrees with the
  by-name perform in both backends (tested). Only noncapturing, one-shot,
  tail-resumptive capabilities may be passed to `cap` parameters; passing any
  other is rejected, because a callee would need a resumable entry keyed by
  the capability parameter (section 3.4). That cross-call part is
  EFF-CAP-RESUME-CALLS. As before, a capturing (`once`) handler serves one
  perform, by name or by capability.
- Not yet: cross-call non-tail capabilities, capabilities captured by lambdas.

### EFF-CAP-RESUME-CALLS design note

The resumable-entry pipeline (checker await marking, `suspend::performs`
coloring, `g::resumable` entries, real-token handler calls) is keyed by
declared operation ids. The cross-call extension adds a second key, the
capability parameter index: a function whose body performs through cap
parameter `i` (directly or by forwarding it to such a parameter) is colored
for `cap i`; a call site is an await point when the argument is a non-tail
capability or a forwarded cap parameter colored at the caller; inside the
resumable entry, `perform op(x)` calls the capability's handler with the real
continuation token instead of looking up the dynamic stack. The capability
then also carries the activation's frame (for capturing handlers), so it
needs the scoped-borrow representation of section 3.2 rather than a bare
function pointer. Review focus: continuation frames that hold the capability
must not outlive the activation (use-after-free) or copy its environment
(stale copies).

## 3.8 Measured acceptance (EFF-CAP-PERF)

Decision 4's gate, on the E-PERF method with the programs in
[benchmarks/effects](../benchmarks/effects/README.md) (10^7 iterations,
`--release`, best of 7 interleaved runs, start-up subtracted, two runs):

| Path | ns/iteration |
| --- | --- |
| direct call | 1.9-2.2 |
| lexical perform, tail-resumptive | 3.5-3.7 |
| capability perform in its own body | 3.5-3.7 |
| capability perform in a called function | 4.5-4.7 |
| declared perform in a called function (dynamic lookup) | 6.7-7.3 |

A capability perform in a called function costs the lexical in-place path
plus the extra call of the callee (about half a direct call), inside the
5-8 ns band decision 4 names for the lexical path, and about a third less
than the dynamic lookup it replaces. The gate passes; the feature stays.

## 4. Row algebra obligations (Katsumata)

Kush rows are a finite bitset universe (4 builtin + up to 12 declared bits).
Treat the row of a computation as an index in an ordered monoid
`(Rows, ∪, ∅, ⊆)`. A graded-semantics argument needs:

1. **Monoid laws** for sequential composition: `∪` associative, `∅` unit
   (bitsets: immediate).
2. **Monotonicity:** `e1 ⊆ e1'` and `e2 ⊆ e2'` imply `e1 ∪ e2 ⊆ e1' ∪ e2'`
   (subeffecting is a congruence). Implemented by subset inclusion checks at
   calls and arrow subtyping.
3. **Discharge:** `handle Op` types its body at `e ∪ {Op}` and itself at
   `e ∪ h` where `h` is the handler's row. The obligation is that discharge
   commutes with subeffecting (`(e ∪ {Op}) ⊆ (e' ∪ {Op})` when `e ⊆ e'`) and
   that the handler's row is never dropped. The latter is the rule that a
   dynamically visible handler must be pure, and section 3.3 for capabilities.
4. **Idempotence** (`e ∪ e = e`) is what makes rows a *set* rather than a
   count; it is why rows cannot express "performs at most once" and why grades
   (grade-model.md) are a separate axis.
5. **Row variables and subtraction** (`{e - io}`, bounded binders): the finite
   solver must agree with set semantics on every instantiation. This is
   checkable exhaustively per constraint because the universe is 16 bits.

These are statements to test, not a theorem: bitset union being associative
does not show that the *operational* behaviour of handled programs respects
the indices.

**Tested (EFF-ROW-LAWS).** `crates/kush/src/row_laws_tests.rs` checks the
checker's own row operations: term evaluation equals set semantics and is
bitwise (the lemma the per-bit solver relies on); union is an idempotent
commutative monoid and subeffecting a congruence over all 2^16 rows (second
and third rows from a stratified sample); subtraction is antitone on the
right; discharge `(body - {Op}) ∪ h` keeps `h` and is monotone; and the
per-bit solver (`solve_row_bits`, extracted from the checker unchanged)
agrees with an independent whole-row search on solvability, minimal solution
and ambiguity, for one variable over all 2^16 rows and for two variables over
a five-bit sub-universe, including exclusion and inclusion bounds.
`crates/kush/tests/effect_row_laws.rs` checks the language rules over every
subset of the four builtin effects: call monotonicity, sequential
composition, arrow subeffecting, `handle` discharge (only `Op`; the handler
row is kept), per-specialization subtraction `{e - io}`, bounded binders, a
shared row variable receiving the union, and the ambiguity of `{a | b}`.

## 5. Decisions

1. **Add capabilities as an opt-in, second-class, lexical path**; keep
   declared dynamic handlers unchanged and primary for library interfaces.
2. **Reuse the scoped-borrow discipline** for capability escape rather than
   introducing a new region system.
3. **Optimize only the resumptive mainline.** Abortive handlers are a separate
   design that needs unwinding (E-ABORT-DESIGN), not part of capabilities.
4. **Acceptance requires measurement**: a capability perform in a called
   function under a tail-resumptive handler must be within noise of the
   lexical in-place path (5-8 ns) on the E-PERF harness, otherwise the
   feature is not worth its surface.
5. **Row laws are tested exhaustively** over the finite universe before any
   capability row rule lands.

## 6. Follow-up nodes

Added to `plan/plan.json`:

- **EFF-ROW-LAWS** (S): exhaustive tests of section 4 laws (composition,
  monotonicity, discharge, subtraction/binders) over the 16-bit universe,
  against the checker's row operations.
- **EFF-CAP-LEXICAL** (L): `handle Op as op`, `cap Op ! {e}` parameters,
  `perform op(x)` with tail-resumptive handlers, second-class escape
  rejections, evaluator/native parity and cleanup tests; dynamic semantics
  unchanged (regression: every existing handler test).
- **EFF-CAP-RESUME** (M): non-tail and multishot handlers through
  capabilities (resumable entries keyed by cap parameters), depends on
  EFF-CAP-LEXICAL.
- **EFF-CAP-PERF** (S): measured cohort per decision 4.
- **E-ABORT-DESIGN** (M, research): non-resuming handlers and the unwinding
  they need (drop of live owned values between perform and handle, native and
  evaluator), as a separate decision.
