# Multishot capabilities across calls (design)

Status: **design, awaiting approval** (plan node EFF-CAP-RESUME-MULTISHOT).
Nothing here is implemented. It removes the blocker recorded in the plan log
on 2026-11-06 and is the base for TACTICS-HANDLERS, whose backtracking search
resumes a continuation captured inside recursive proof-search functions.

Revision 2 (2026-11-13): the first draft recommended reference-counted
environments. This version uses a continuation stack released when each
resumption returns (section 3), which the existing no-escape rule for tokens
makes sound (section 5). General first-class `multi fn` closures are left
out of this node.

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
multi fn(R) -> R ! {}            -- a multishot resumption token
cap multi Op ! {e}               -- a capability whose handler may resume
                                 -- several times (spelling approved)
```

`cap multi Op ! {e}` lowers to the handler arrow
`fn(P, multi fn(R) -> R ! {}) -> R ! {e}`, as `cap Op ! {e}` lowers to
`fn(P, linear once fn(R) -> R ! {}) -> R ! {e}` today. A multishot handler
declares its token as `multi fn`:

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
        resume(0) + resume(1)               // two calls of one token
    }
    { pick(op, 3) }
```

`multi fn` is a **token type**, not a general closure: there are no `multi fn`
lambdas. It is copyable and second-class (section 4). The same token serves
lexical performs in the handler's own `handle` body, without the
specialization and its restrictions. The existing multishot form with a
`fn(R) -> R` token is unchanged.

## 3. Representation options

Requirements: the token must be callable many times; its environment must
refer to other tokens' environments (the chain); a handler must be able to
resume zero times; memory must be released deterministically (Kush has no
GC); and the evaluator and both native backends must behave identically.

**A. Shared, reference-counted, immutable environments.** Two words
`(code, env)`; the environment holds a drop function and a count. Sharing `k`
with a new continuation increments; a drop decrements, and the last one runs
drop glue.

**B. Copied environments.** The environment is uniquely owned; duplicating a
token deep-copies the chain through generated clone glue (the frame-chain
copy that section 10 of the state-machine design sketched).

**C. Region per `handle`.** Environments are bump-allocated in a region the
`handle` activation frees when it returns.

**D. Specialize across calls.** Extend E-MULTISHOT-COPY by specializing each
callee's resumable entry per handler.

**E. Continuation stack released on return (recommended).** Environments are
bump-allocated on a per-task continuation stack. Every call of a token, and
every multishot `handle`, saves the stack top before and restores it after.
Section 5 shows that nothing allocated during such a call is reachable after
it returns.

| | A. Refcount | B. Copy | C. Region per `handle` | D. Specialize | **E. Stack, released on return** |
| --- | --- | --- | --- | --- | --- |
| Recursive search (unbounded chain) | yes | yes | yes | **no** | yes |
| Building a continuation | `kush_alloc` | `kush_alloc` | bump | none | bump |
| Continuation keeps the caller's `k` | +1 now, -1 later | deep copy of the chain: `O(depth)` | bit copy | none | bit copy |
| Each resumption | copy captures, count nested tokens | copy, then free | copy captures | a call | copy captures, save and restore the top |
| Memory held during a search | live chain | live chain | **everything since the `handle`**: grows without bound | n/a | live chain, `O(depth)` |
| Drop glue | per environment | per environment, plus clone glue | none | none | none |
| Token at the surface | affine (no user copies) | affine | copyable, second-class | n/a | copyable, second-class |
| If the no-escape rule had a hole | leak | leak | use-after-free | n/a | use-after-free |

**Recommendation: E.** It has C's costs (a bump, bit copies, no glue)
without C's growth: abandoning a branch frees it at once, so a search of depth
`d` holds `O(d)` environments however many branches it explores. Compared
with A it removes every count operation and all drop glue, and the token
becomes copyable. D cannot express recursion, and B costs `O(d^2)` copying
over a search.

What E gives up:

- **Safety rests on the no-escape rule** (section 5). A hole would read
  released memory instead of leaking. Two checks back it: the evaluator tags
  every environment with an epoch and rejects a use of a released one as an
  internal error, and the native runtime can poison released memory in tests
  (section 7.1).
- **Only tokens.** A first-class closure that outlives its scope does not
  follow a stack discipline. If a general copyable closure is ever needed, it
  is a separate node, probably with representation A.
- **No tail call** for a token call that may allocate, since the restore runs
  after it returns. Deep handlers already hold one native frame per pending
  call, so this changes little; the tail-resumptive path keeps its identity
  token, which allocates nothing and needs no bracket.

Stack copying (libmprompt style) stays out for the reasons in the
state-machine design: evaluator parity, and stacks with interior pointers.

## 4. The token type

- **Copyable.** Copying a token is a bit copy of two words; calling it does
  not consume it. `resume(0) + resume(1)`, `let r = resume; r(2)` and passing
  it to a helper are all fine. It has no drop.
- **Second-class**, like `cap`: a value of type `multi fn` may be the
  handler's token parameter, a local of the handler, an argument passed by
  name to a `multi fn` parameter of a named function, or a callee. It cannot
  be returned, stored in a field, enum, union, `Vec` or trait object,
  captured by a lambda, captured by a task or thread, or live across a
  `perform` (which would capture it in a continuation environment). Functions
  with `multi fn` parameters cannot become function values, as for `cap`
  parameters.
- **Arrow.** Parameter and result types, rows and grades follow `fn` arrows,
  with the same arrow subtyping between `multi fn` types. There is no
  subtyping between `multi fn` and `fn`, `once fn` or `linear once fn`.
- **Where tokens come from.** Only the compiler creates them, at suspension
  points of handled bodies and resumable entries whose handler declares a
  `multi fn` token.

## 5. Why release on return is sound

Three invariants:

1. **Only tokens point into the continuation stack.** An environment holds
   copyable values only (section 6.1); nothing else holds a stack address.
2. **Older only.** An environment captures values that exist when it is
   created, so it can only refer to environments allocated before it.
3. **Nothing outlives the call that made it.** A token cannot be returned,
   stored, captured or sent to a task (section 4), and it never reaches the
   handled body: the operation result type, the handler payload type and the
   handler's written captures cannot hold a function value. That last rule
   exists today for one-shot tokens ("the token must not outlive the
   handler"). So when a bracketed call returns (a call of a token, or a
   multishot `handle`), every token created during it has gone.

By 3, nothing allocated after the saved top is reachable once the call
returns, so restoring the top frees only garbage. By 2, an environment that
is still reachable lies below the top. In particular the token being called
was created before its own bracket, so after `resume(0)` returns,
`resume(1)` finds its environment intact.

Example, with `handle` mark `h` and a handler that resumes twice:

```text
handle:  save h
  body suspends at p:   push E_p           (below the top from now on)
  handler(n, (code, E_p))
    resume(0): save m0
      continuation of p runs, suspends at q: push E_q
      handler(.., (code, E_q)) ... returns
    restore m0                              (E_q released; E_p kept)
    resume(1): save m1, ..., restore m1
  handler returns
restore h                                    (E_p released)
```

Paths that leave without a normal return: an abortive operation
(E-ABORT) travels up through returning frames, so each bracket restores on
the way. A `panic` aborts the program. Kush has no unwinding, so there is no
other way out.

### 5.1 Linearity, affinity and grades

- **Live values across a multishot perform** are copied into the
  environment and copied out on every resumption, so each must be copyable
  and ungraded: owned (`Vec`, `Box`, `Bytes`, `once fn`, trait objects),
  linear, `@[n]` and `@[0]` values are rejected, naming the value, as for
  today's multishot. There is no drop glue because no environment owns
  anything. Copyable values include `Tm`-style handles, records of scalars,
  `fn` values and `cap` values (handler code pointers).
- **Borrows.** The E-CPS-BORROW exception stays: a shared view of storage
  declared outside the handled body may be live across a perform, because
  every continuation runs inside the activation that suspended. Exclusive
  views stay rejected for multishot (each resumption would hold the same
  exclusive loan).
- **The token** is copyable, so linearity does not apply to it; a handler
  may resume any number of times, including zero.
- **Grades.** Arrow parameter and result grades are checked as for `fn`. A
  handler's token parameter is ungraded; an explicit grade on it is rejected
  (copies are free and uncounted).

### 5.2 Effects

- A token's static row is `{}`, as for one-shot tokens; the continuation's
  effects are the body's and are required at the `handle` (unchanged).
- Pushing a capturing environment can run out of memory: a `handle` whose
  multishot continuations capture values requires `{alloc, panic}`, as
  non-tail handles do today. Calling a token adds nothing.
- `cap multi Op ! {e}` adds `e` to the caller's row at each perform, as
  `cap Op ! {e}` does (section 3.3 of the capability design).

### 5.3 Capabilities

- `cap multi Op` is second-class like `cap Op`: passed by name to a
  `cap multi` parameter, or used as `perform op(x)`.
- `cap Op` and `cap multi Op` are not interchangeable in either direction:
  the handler code expects a different token. The error names the type to
  write.
- Handlers accepted for `cap multi` across calls: a noncapturing handler (a
  lambda at the `handle` or a function name) with a `multi fn` token, and a
  capturing one whose captures are copyable, through the existing trampoline
  (its frame is never consumed). A handler that owns a capture stays
  rejected.
- A multishot handler bound `as op` is not pushed on the dynamic handler
  stack (as today), so a callee performing `Op` by name under it is still
  rejected; only capability performs reach it.

## 6. Lowering

### 6.1 Resumable entries for `cap multi`

The pipeline of EFF-CAP-RESUME-CALLS is reused with a third entry key,
`EntryKey::MultiCapability(i)`:

- `capability_performs` already computes which `cap` parameters a function
  performs through; it covers `cap multi` parameters as well.
- `g::resumable` for `MultiCapability(i)` takes `k: multi fn(T_g) -> R`
  instead of `linear once fn(T_g) -> R`.
- Each suspension point pushes an environment with the point's live values
  and `k` (bit copies) and builds the token `(continuation, env)`.
- A continuation copies its captures out of the environment into ordinary
  locals; the environment is never modified, so later resumptions see the
  same values.
- Finishing calls `k(v)`. `return` and `?` call `k` as in one-shot entries.
- A tail point whose only live value is `k` hands `k` itself to the handler,
  as today: no push.
- The `handle` side pushes its own continuation (live values of the handled
  body) and passes it as the first `k`.
- **Direct entries.** When the handler is known to be tail-resumptive, the
  callee's direct entry runs and `perform op(x)` passes a static identity
  token `(identity, null)`: no push, the in-place path.

Ownership is checked before lowering, as for all suspension; the lowering is
trusted and covered by parity, epoch and poisoning tests (section 8).

### 6.2 Brackets

- Every call of a value of type `multi fn` is emitted as
  `m = KStackMark; r = call; KStackRestore(m)` (two IR nodes added around the
  call). A call of a known identity token is not bracketed.
- A `handle` whose handler takes a `multi fn` token marks on entry and
  restores on every exit of the `handle` expression, including the abort
  path.

### 6.3 Lexical performs with a `multi fn` token

A handler whose token is `multi fn` uses the same continuations for performs
in its own body. The specialization of E-MULTISHOT-COPY is not needed for it,
so the requirement that the handler be noncapturing and only call its token
directly does not apply; the `fn(R) -> R` form keeps it.

### 6.4 Loops and control

Unchanged from one-shot continuations: after a perform, `return`, `?`,
`break` and `continue` out of the handled body are rejected; loop-carried
values are environment values copied out on each resumption, so each
resumption restarts from its own copy of the loop state.

## 7. ABI

### 7.1 Native (Cranelift and LLVM)

LLVM consumes the same verified Cranelift IR (`native/llvm.rs`), so there is
one lowering, and the translator needs no new instruction: everything below
is loads, stores, `call_indirect` and calls of C runtime helpers, which
`llvm-link` inlines.

- **Token.** Two words `(code, env)`, the layout of `once fn`. `env` is
  null for a capture-free continuation and for the identity token.
- **Environment.** The captures at their usual widths, 8-byte aligned, with
  no header (no drop function, no count).
- **Continuation stack.** One per task, kept beside the task's handler
  context (`kush_handlers()`), and one per OS thread when threads are on.
  It is a list of chunks (64 KiB by default; an environment larger than a
  chunk gets its own) obtained from `kush_alloc`.
- **Runtime helpers.** `kush_kstack_push(bytes) -> env` bumps the top and
  panics on allocation failure. `kush_kstack_mark() -> word` returns the
  top. `kush_kstack_restore(word)` moves the top back and frees the chunks
  above it, keeping one spare chunk to avoid churn at a chunk boundary. A
  restore above the current top panics (internal error).
- **Poisoning.** When the runtime starts with `KUSH_KSTACK_POISON=1`, a
  restore fills the released bytes with a fixed pattern, so a stale read
  produces a wrong value that the tests detect instead of a silent pass.
- **Call.** `call_indirect code(env, arguments..., [return buffer])`: the
  `once fn` convention, with `env` only read. The prologue loads each
  capture at its offset.
- **Handler call.** The token is two words, so a `cap multi` handler has the
  native signature `h(payload..., code, env)`, the same width as a one-shot
  handler.
- **Tasks.** A task switch saves nothing extra: each task has its own stack,
  and tokens cannot cross tasks.

### 7.2 Evaluator

- **Token.** `Value::Function { function, environment: Some(id) }` where
  `id` names an entry of the evaluator's continuation stack, plus the entry's
  epoch.
- **Stack.** `Vec<(epoch, Vec<Value>)>`. Push appends with a new epoch; mark
  is the length; restore truncates. Every access checks that the entry still
  exists with the same epoch; otherwise it is an internal error ("use of a
  released continuation environment"). This is the reference check for the
  soundness argument of section 5.
- **Statistics.** Pushes and releases are counted with the allocation
  statistics, so allocation balance at exit also checks that every bracket
  restored, and the peak stack size is recorded for tests.
- The evaluator's fixed nesting budget (128) limits how deep a search can go
  under it; evaluator tests stay shallow and the deep ones run natively.

## 8. Tests

New file `crates/kush/tests/multishot_capabilities.rs`, plus additions to
`effect_capabilities.rs`. Every executable test runs in the evaluator and
natively (with `KUSH_KSTACK_POISON=1`), with allocation balance checked in
both, as the existing handler tests do; the native suite is replayed on LLVM
with `KUSH_BACKEND=llvm` where `clang` is available.

1. **The token type.** Copy into a local and call both; pass to a
   `multi fn` parameter of a helper and call it there; resume zero times.
   Rejected: returning it, a field, enum, union, `Vec`, `dyn`, lambda
   capture, task or thread capture, live across a perform, a grade on it, a
   `multi fn` parameter on a function used as a value, `multi fn` where `fn`
   or `once fn` is expected and the reverse. `let multi = 1;` still works.
2. **Lexical performs.** A `multi fn` token with live values resumed 0, 1, 2
   and 3 times; a capturing handler; a perform in a loop with loop-carried
   state; the existing `fn(R) -> R` multishot tests give the same results
   when rewritten with `multi fn`.
3. **Across calls.** A callee performing twice; a forwarding chain three
   functions deep with live values at each level; recursion (the leaves of a
   choice tree, all solutions of 5-queens); `return` and `?` in callees under
   several resumptions; handlers that resume zero times and in different
   orders; a tail-resumptive `cap multi` handler on the direct entry (no
   push).
4. **Rejections.** `cap Op` passed as `cap multi Op` and the reverse; an
   owned, linear or graded value live across a perform in a callee; an
   exclusive view live across one; a result or payload type that can hold a
   function; a perform inside a nested handle in a callee; a perform by name
   under a `cap multi` handler.
5. **Stack discipline.** The evaluator's epoch check on a deliberately
   broken lowering (a unit test of the check itself); a natively run search
   with about 10^5 resumptions whose peak stack size, reported by the
   runtime in test mode, stays proportional to the search depth, not to the
   number of branches.
6. **Measurement.** A row in `benchmarks/effects` for a `cap multi` perform
   in a called function, next to the one-shot paths (recorded, no gate).

## 9. Implementation steps (plan sub-nodes)

Each is one or a few commits with its tests, under EFF-CAP-RESUME-MULTISHOT:

1. **MS-TYPE**: parse `multi fn` and `cap multi`; the token type
   (copyable, second-class) and its rules in the checker and ownership pass;
   checker-only tests of group 1.
2. **MS-KSTACK**: the continuation stack in the evaluator (epochs,
   statistics) and the native runtime (chunks, poisoning); `KStackPush`,
   `KStackMark` and `KStackRestore` in the IR, both backends.
3. **MS-TOKEN**: handlers with a `multi fn` token for lexical performs
   (environments on the stack, brackets); executable tests of groups 1 and 2.
4. **MS-CAP**: `cap multi` parameters, `EntryKey::MultiCapability`, the
   handle side, direct entries; tests of groups 3 and 4.
5. **MS-STRESS-DOCS**: groups 5 and 6, an independent review of the
   soundness argument (stale environments, missing restores on exits), and
   the as-built sections here, in `effect-capabilities.md` and in
   `effect-handlers.md`.

Not in this node: general first-class `multi fn` closures (representation
A, if a client needs them); moving one-shot non-tail environments onto the
same stack, which section 5 would also cover and which would save a
`kush_alloc` per suspension (a possible follow-up, measured first).

## 10. Decisions asked for

1. Representation **E**: a per-task continuation stack, saved before and
   restored after every call of a token and every multishot `handle`.
2. `multi fn` as a **copyable, second-class token type** only; no
   `multi fn` lambdas in this node.
3. Live values across a multishot perform: copyable and ungraded, with the
   existing exception for shared views of outer storage.
4. `cap Op` and `cap multi Op` kept distinct.
5. Checks backing the soundness argument: epochs in the evaluator, poisoning
   in native tests.
