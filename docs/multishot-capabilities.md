# Multishot capabilities across calls (design)

Status: **design, awaiting approval** (plan node EFF-CAP-RESUME-MULTISHOT).
Nothing here is implemented. It removes the blocker recorded in the plan log
on 2026-11-06 and is the base for TACTICS-HANDLERS, whose backtracking search
resumes a continuation captured inside recursive proof-search functions.

Background: [effect handlers](effect-handlers.md),
[state machines](effect-state-machines.md) (sections 10 and 14.2),
[capabilities](effect-capabilities.md) (section 3.7),
[functions and closures](functions.md).

## 1. The problem

A multishot handler today has the token type `fn(R) -> R`: one word, a code
pointer, no environment. A continuation with live values is supported only by
**specializing the handler** at each perform point (E-MULTISHOT-COPY): the
point calls a copy of the handler that takes the live values as extra
parameters, and each `resume(y)` in that copy is a direct call of the
continuation with those values.

That trick needs the handler and the whole continuation to be known at one
place in one function. Across calls neither is true:

- The callee performs through a `cap` parameter. The handler is a run-time
  value (a code pointer), so the callee cannot call a specialization of it.
- The continuation is a **chain**: the callee's live values, then the
  caller's continuation `k`, which holds the caller's live values and its own
  `k`, up to the `handle`. In a recursive search (`search` calls `search`
  calls `search`, each choosing) the chain length depends on run-time data, so
  no finite set of specializations covers it.

So the token handed to the handler must be a **run-time value carrying an
environment**, which can be invoked more than once, and whose environment can
refer to the caller's continuation, which is itself such a value. Kush has no
such value: `fn` has no environment and `once fn` frees its environment on
the first call.

## 2. Surface

Two new spellings, both contextual (like `cap`, `as` and `once`), so `multi`
stays usable as an ordinary name.

```text
multi fn(A) -> B ! {e}           -- a callable that can be called many times,
                                 -- with a shared, immutable environment
cap multi Op ! {e}               -- a capability whose handler may resume
                                 -- several times (spelling approved)
```

`cap multi Op ! {e}` lowers to the handler arrow
`fn(P, multi fn(R) -> R ! {}) -> R ! {e}`, as `cap Op ! {e}` lowers to
`fn(P, linear once fn(R) -> R ! {}) -> R ! {e}` today. A multishot handler
for capabilities declares its token as `multi fn`:

```text
effect Choose: i64 -> i64;

fn pick(op: cap multi Choose ! {alloc, panic}, depth: i64) -> i64 ! {alloc, panic} {
    if depth == 0 { 0 } else {
        let x = perform op(2);              // live after: depth
        x + 10 * pick(op, depth - 1)        // live across the call: x
    }
}

handle Choose: i64 -> i64 as op
    with fn(n: i64, resume: multi fn(i64) -> i64) -> i64 ! {alloc, panic} {
        resume(0) + resume(1)               // two calls, no copy written
    }
    { pick(op, 3) }
```

The same `multi fn` token also serves lexical performs in the handler's own
body (no specialization needed), and `multi fn` lambdas can be written
directly (section 6.4). The existing multishot form with a `fn(R) -> R` token
is unchanged.

The spelling `multi fn` (mirroring `once fn` and the approved `cap multi`) is
part of what this document asks to approve.

## 3. Representation options

Requirements: the value must be callable many times; it must refer to other
such values (the chain); it must be droppable without being called (a handler
that resumes zero times); drops must be deterministic (Kush has no GC); and it
must work the same way in the evaluator and in both native backends.

**A. Shared, reference-counted, immutable environment.** Two words
`(code, env)`. The environment starts with a header holding its drop function
and a reference count. A call borrows the environment: the callee copies its
captures out and leaves the environment alone. Duplication (only done by
generated code, see section 4) increments the count; a drop decrements it and
the last one runs the drop glue (release nested closures, free the cell).

**B. Copied environments (clone glue).** Same two words, but the environment
is uniquely owned. Duplication allocates a new environment and runs generated
clone glue, which recursively duplicates every nested closure in it. This is
the frame-chain copy that section 10 of the state-machine design sketched.

**C. Handle-scoped arena.** Environments are bump-allocated in a region owned
by the `handle` activation and freed when the `handle` returns. The value is
a bitwise-copyable `(code, env)` pair with no drop glue, valid only while the
activation lives (second-class, like `cap`).

**D. Specialize across calls.** Extend E-MULTISHOT-COPY by specializing each
callee's resumable entry per handler and passing live values as parameters.

| | A. Refcount | B. Copy | C. Arena | D. Specialize |
| --- | --- | --- | --- | --- |
| Works for recursive search (unbounded chain) | yes | yes | yes | **no**: needs one specialization per chain shape |
| Cost to create a continuation | one allocation | one allocation | bump | none |
| Cost when a continuation captures `k` | `k`: +1 count | `k`: deep copy of the whole chain | none | none |
| Cost per resumption | copy captures out, +1 per nested closure loaded | same, plus frees | same | a call |
| Memory released | when the last reference goes | when each copy goes | only when the `handle` returns: a long search grows without bound | n/a |
| Drop glue | yes (release) | yes (release) + clone glue | no | no |
| Cycles | impossible (section 5.5) | impossible | n/a | n/a |
| Values outlive the `handle`? | safe if allowed | safe if allowed | must not: a use-after-free otherwise | n/a |
| Ownership pass | unchanged (section 4) | unchanged | new region rule | unchanged |
| Precedent in Kush | `Arena`, `AllocatorContext` use non-atomic counts | none | `Arena` regions | E-MULTISHOT-COPY |

**Recommendation: A.** D cannot express recursion, which is exactly the use
case. B makes every suspension that captures `k` cost the length of the chain,
so a search of depth `d` costs `O(d^2)` copying, and needs a second kind of
glue. C is the cheapest per operation but leaks for the whole duration of a
search (a proof search can run millions of resumptions under one `handle`),
and it would make every `multi fn` second-class. A has a constant cost per
suspension and frees memory as soon as a branch is abandoned. Its usual
drawbacks do not apply here: environments are immutable and point only at
older values, so there are no cycles, and closures already cannot cross
threads, so the count need not be atomic.

## 4. Copyable at run time, affine in the language

The blocker asks for a "copyable token". At run time the recommended value is
copyable: duplicating it is one increment. In the language, the recommendation
is that `multi fn` is an **affine owned value whose calls do not consume it**
(Rust's `Fn` rather than `Copy`):

- `resume(0) + resume(1)` calls the same local twice. A call reads the local
  without moving it, like a call through a `fn` value.
- Moving it (`let r2 = resume;`, passing it to a function, returning it)
  moves it, as for any owned value; a use after the move is the usual error.
- At the end of its scope it is dropped, which releases one reference.
- Only generated code duplicates it: when a continuation stores the
  caller's `k` in a new environment, the lowering emits `Retain`. Users have
  no duplication operation in this node.

Why not make it implicitly copyable at the surface: every non-last read would
need a hidden increment and every copy a scheduled decrement, which changes
the ownership pass in the place where it decides between copy and move, for
every owned type check. The affine form keeps the ownership pass as it is
(a `multi fn` local is owned and dropped like a `Box`; a call is a non-moving
read), keeps every count change visible in the IR, and covers what the
handlers need. An explicit `share` operation or implicit copies can be added
later without changing the ABI.

## 5. Typing rules

### 5.1 Linearity and affinity

- A `multi fn` value is affine: it may be dropped, never duplicated by the
  user. It is not linear, and it cannot be weakened to `once fn` or
  `linear once fn` in this node (that needs an adapter whose call releases
  instead of freeing; a follow-up if anyone needs it). `fn(A) -> B` is a
  subtype of `multi fn(A) -> B` through a generated adapter (a code pointer
  wrapped with a null environment, section 7.1).
- **Captures must survive being read many times.** Each capture of a
  `multi fn` environment must be copyable (scalars, `fn` values, `Tm`-like
  handles, records of those) or itself a `multi fn` (shared: loading it from
  the environment retains it). Rejected, naming the capture: owned values
  (`Vec`, `Box`, `Bytes`, `once fn`, trait objects), linear values, borrows
  and by-reference captures (a user `multi fn` can outlive its scope), and
  capability values other than plain handler pointers.
- **Continuation tokens** follow the same rule for the values live across a
  perform, with the E-CPS-BORROW exception kept: a shared view of storage
  declared outside the handled body may stay live, because a token cannot
  outlive its handler (section 5.4). Exclusive views stay rejected for
  multishot, as today (`outer_borrow`).
- A linear value live across a multishot perform is rejected: it would be
  consumed once per resumption.

### 5.2 Grades

- A capture with an exact grade (`@[1]`, `@[n]`) is rejected: the
  environment may be entered any number of times, so no finite count holds.
  An erased `@[0]` capture is rejected as for other closures.
- Arrow parameter grades and result grades are part of the `multi fn` type
  exactly as for `fn` and `once fn`, with the same covariant checking.
- A `multi fn` local may carry a usage grade like any owned local; each call
  counts as one use. A handler's `resume` is ungraded.
- Grade-effect demand and grade inference treat `multi fn` like `once fn` for
  its arrow and like an owned value for the binding.

### 5.3 Effects

- The call's row is the arrow's row. A token's static row is `{}` as for
  one-shot tokens; the continuation's effects are the body's and are
  required at the `handle` (unchanged rule).
- Creating a capturing `multi fn` or a capturing token allocates: `alloc`
  (and `panic` for allocation failure), as for `once fn` closures and today's
  non-tail tokens. Dropping or calling one does not add effects.
- `cap multi Op ! {e}` adds `e` to the caller's row at each perform, as
  `cap Op ! {e}` does (section 3.3 of the capability design). Subtyping on the
  row is the same arrow subtyping.

### 5.4 Escape

The existing rule "a token must not outlive its handler" applies unchanged to
`multi fn` tokens: an operation result type, a handler payload type or a
handler-written capture that can hold a function value is rejected for
non-tail resumption, and a token cannot be captured by a spawned task. Within
the handler, the token is an ordinary owned local: it may be called, dropped,
moved into a local or passed to a helper whose result cannot hold it. This is
what keeps the E-CPS-BORROW argument (every continuation runs nested inside
the activation that suspended) valid for shared views and for the dynamic
handler frames that capturing-handler trampolines reach.

User-written `multi fn` values are first-class (locals, parameters, results,
captures of other `multi fn` values). In this node they cannot be record or
enum fields, union alternatives, vector elements or trait-object members, and
they cannot be captured by a thread body or a task (closures already cannot
cross threads, which is why a non-atomic count is sound). Those positions
need drop glue in more places and are follow-ups if a client asks.

### 5.5 No cycles

An environment is immutable after creation and can only capture values that
existed before it. A `multi fn` cannot reach a mutable cell (by-reference and
owned captures are rejected), so no environment can come to point at itself.
Reference counting therefore frees everything.

### 5.6 Capabilities

- `cap multi Op ! {e}` is second-class like `cap Op`: passed by name to a
  `cap multi` parameter, or used as `perform op(x)`.
- `cap Op` and `cap multi Op` are not interchangeable in either direction:
  the handler code expects a different token. Passing one where the other is
  expected is an error that names the token type to write.
- Accepted handlers for `cap multi` across calls: a noncapturing handler
  (lambda at the `handle` or function name) with a `multi fn` token. A
  capturing handler whose captures are copyable goes through the existing
  trampoline (its frame is never consumed); a handler that owns a capture
  stays rejected, as for one-shot capturing handlers.
- A multishot handler bound `as op` is not pushed on the dynamic stack (as
  today), so a callee performing `Op` by name under it is still rejected;
  only capability performs reach it.

## 6. Lowering

### 6.1 Resumable entries for `cap multi`

The pipeline of EFF-CAP-RESUME-CALLS is reused with a third entry key,
`EntryKey::MultiCapability(i)`:

- `capability_performs` already computes which `cap` parameters a function
  performs through; it covers `cap multi` parameters as well.
- `g::resumable` for `MultiCapability(i)` takes `k: multi fn(T_g) -> R`
  instead of `linear once fn(T_g) -> R`.
- Each suspension point builds its continuation as a `multi fn` closure
  capturing the point's live values and `k`. `k` is moved into it (the entry
  does not use it again), so building a continuation never touches a count.
- Inside a continuation, captures are loaded by copy; a `multi fn` capture
  (`k`, or a user `multi fn` live across the perform) is loaded with `Retain`
  and dropped or moved like any owned local, so a continuation that awaits a
  callee moves its retained `k` into the callee's continuation.
- Finishing calls `k(v)` and then drops the local `k` (one release).
- A tail point whose only live value is `k` hands `k` itself to the handler,
  as today.
- The `handle` side builds its own continuation (live values of the handled
  body) as a `multi fn` and passes it as the first `k`.
- **Direct entries.** When the handler is known to be tail-resumptive, the
  callee's direct entry runs and `perform op(x)` passes a static identity
  token `(identity, null)`: no allocation, the in-place path.

Ownership is checked before lowering, as for all suspension (check first,
lower after); the lowering is trusted and covered by parity and allocation
balance tests (section 8).

### 6.2 Lexical performs with a `multi fn` token

A handler whose token is `multi fn` uses the same continuations for performs
in its own body. The specialization of E-MULTISHOT-COPY is not needed for it,
so its restrictions (noncapturing handler that only calls its token directly)
do not apply; the `fn(R) -> R` form keeps them.

### 6.3 Interaction with `return`, `?` and loops

Unchanged from one-shot entries: in a resumable entry, `return` and `?` call
`k`; after a perform, `return`, `?`, `break` and `continue` out of the handled
body are rejected. Each resumption re-runs from its own copy of the loop state
because loop-carried values are frame values copied out of the environment.

### 6.4 User `multi fn` lambdas

```text
let base = 40;
let add: multi fn(i64) -> i64 ! {} = multi fn(x: i64) -> i64 ! {} { x + base };
add(1) + add(2)
```

They use the same closure conversion as `once fn` lambdas with the capture
rules of section 5.1 and the shared environment. They are part of this node
because they test the representation directly (counts, drop glue, nested
captures) without going through handlers.

## 7. ABI

### 7.1 Native (Cranelift and LLVM)

LLVM consumes the same verified Cranelift IR (`native/llvm.rs`), so there is
one lowering and the translator needs no new instruction: everything below is
loads, stores, `call_indirect` and calls of runtime helpers that `llvm-link`
inlines.

- **Value.** Two words `(code, env)`, the layout of `once fn`. `env` is null
  for a capture-free closure, a static identity token or an adapted `fn`.
- **Environment.** One `kush_alloc` block:
  `[drop: fn(env) @0][count: u64 @8][captures @16..]`. The drop function stays
  at offset zero, as for `once` environments and handler frames
  (`kush_handler_drop_frame`), so generic code that drops an environment by
  its header keeps working.
- **Runtime helpers** (C runtime, non-atomic):
  `kush_multi_retain(env)`: if `env != 0`, `++count`.
  `kush_multi_release(env)`: if `env != 0` and `--count == 0`, call `drop`,
  which releases nested `multi fn` captures and frees the block. A count of
  zero on entry panics (a double release is an internal error, not a silent
  corruption).
- **Call.** `call_indirect code(env, arguments..., [return buffer])`: the
  `once fn` convention with the environment borrowed. The callee prologue
  loads each capture at its offset, calls `kush_multi_retain` on `multi fn`
  captures, and never frees the environment.
- **Drop.** Dropping a `multi fn` value calls `kush_multi_release(env)`.
- **Adapter `fn` to `multi fn`.** A named function becomes
  `(wrapper, null)`, where the generated wrapper takes and ignores `env` and
  calls the function directly: no allocation. A `fn` value only known at run
  time becomes a one-capture environment holding the code pointer, with a
  wrapper per arrow that calls it.
- **Tokens.** A handler call passes the token as two words, so a `cap multi`
  handler has the native signature `h(payload..., code, env)`. Tail calls
  through the `tail` calling convention are kept where they apply today.

### 7.2 Evaluator

- **Value.** `Value::Function { function, environment: Some(id) }` as for
  `once fn`, where heap cell `id` holds a new
  `Value::SharedClosure { references: usize, captures: Vec<Value> }`.
- **Call.** Clone the captures (bit copies; a nested shared closure gets
  `references += 1`), keep the cell, call `call_with`.
- **Retain / release.** Explicit operations on `references`; the last release
  takes the cell, drops the captures (releasing nested closures) and counts a
  deallocation in the allocation statistics.
- **Checking.** A release at zero, or a dangling cell, is an internal error,
  as for `FrameFree` today. Allocation balance at program exit (existing test
  helpers) turns a missing release into a test failure.
- The evaluator's fixed nesting budget (128) limits how deep a search can go
  under it; tests keep evaluator searches shallow and run the deep ones
  natively.

## 8. Tests

New file `crates/kush/tests/multishot_capabilities.rs`; additions to
`effect_capabilities.rs` and `functions.rs`. Every executable test runs in the
evaluator and natively with allocation balance checked in both, as the
existing handler tests do; the native suite is replayed on LLVM with
`KUSH_BACKEND=llvm` where `clang` is available.

1. **`multi fn` values.** Call twice; drop uncalled; move then use (error);
   a `multi fn` capturing a `multi fn` (nested release); `fn` to `multi fn`
   by name and by value; rejected captures: `Vec`, `Box`, `once fn`, linear,
   `@[1]`, `@[0]`, borrows, by-reference; rejected positions: field, enum,
   union, `Vec` element, `dyn`, thread and task capture; `multi fn` to
   `once fn` rejected; contextual keyword (`let multi = 1;`).
2. **Lexical tokens.** A `multi fn` token with live values resumed 0, 1, 2
   and 3 times; a capturing handler; resumption inside a loop with
   loop-carried state; agreement with the `fn(R) -> R` form on the existing
   multishot tests.
3. **Across calls.** A callee performing twice; a forwarding chain three
   functions deep with live values at each level; recursion (counting the
   leaves of a choice tree, all solutions of 5-queens); `return` and `?` in
   callees under several resumptions; a handler that resumes zero times
   (the whole chain is released); tokens dropped in different orders;
   a tail-resumptive `cap multi` handler on the direct entry (no allocation).
4. **Rejections.** `cap Op` passed as `cap multi Op` and the reverse; an
   owned, linear or graded value live across a perform in a callee; an
   exclusive view live across one; a result type that can hold a function;
   a performing callee under a nested handle; a perform by name under a
   `cap multi` handler.
5. **Stress.** One natively run search with about 10^5 resumptions checks
   allocation balance and that memory stays bounded (no growth with the
   number of abandoned branches).
6. **Measurement.** A row added to `benchmarks/effects` for a `cap multi`
   perform in a called function, so the cost is recorded next to the
   one-shot paths (no gate; this path pays for allocation by design).

## 9. Implementation steps (plan sub-nodes)

Each is one or a few commits with its tests, under EFF-CAP-RESUME-MULTISHOT:

1. **MS-TYPE**: parse `multi fn` and `cap multi`, the `Type::Multi` arrow
   kind, subtyping (`fn` <: `multi fn`), affine ownership with non-moving
   calls, capture, grade and position rules (checker-only tests).
2. **MS-CLOSURE**: `multi fn` lambdas and adapters: IR (`Retain`,
   shared-environment closures), evaluator, native runtime helpers, prologue
   and drop glue; tests of group 1.
3. **MS-TOKEN**: handlers with a `multi fn` token for lexical performs;
   tests of group 2.
4. **MS-CAP**: `cap multi` parameters, `EntryKey::MultiCapability`, the handle
   side, direct entries; tests of groups 3 and 4.
5. **MS-STRESS-DOCS**: groups 5 and 6, an independent review (use-after-free
   and double release), and the as-built sections in this document,
   `effect-capabilities.md` and `effect-handlers.md`.

## 10. Decisions asked for

1. Representation **A** (shared, reference-counted, immutable environments,
   non-atomic counts).
2. Surface **`multi fn`** as an affine value with non-consuming calls, no
   user duplication operation in this node.
3. Capture rule: copyable or `multi fn` captures only, ungraded.
4. User `multi fn` values allowed as locals, parameters, results and
   captures only; fields, unions, vectors, `dyn`, tasks and threads later.
5. `cap Op` and `cap multi Op` kept distinct.
