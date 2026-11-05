# Non-resuming (abortive) handlers and unwinding

Status: **design, decided** (E-ABORT-DESIGN). Nothing here is implemented.
It answers how a handler that does not resume can discard the computation
between a `perform` and its `handle` while dropping every live owned value
exactly once, in the reference evaluator and natively, and keeps this
separate from lexical capabilities (effect-capabilities.md section 3.5).

## 1. Today

- Every handler receives a **linear** resumption token and must call it
  exactly once (multishot handlers call a copyable one). A handler that
  returns without resuming is rejected: `handle Fail: i64 -> i64 with
  fn(x, resume) { x } { ... }` fails with "linear value is not consumed".
- An operation result type must be a runtime type; `Never` is not accepted
  (checked 2026-11-05).
- Errors use `Result` and `?`. The error path of `?` already does exactly the
  cleanup an abort needs *within one function*: it drops affine locals in
  reverse order with drop flags, releases closure environments and pending
  temporaries, and the grade/ownership passes reject the early exit when a
  linear obligation (`@[1]` owner, `#[linear]`, `linear once fn`, task
  handle, resumption token) is pending.
- A perform in a called function finds its handler on the per-task dynamic
  stack. Under a non-tail handler, callers get CPS **resumable entries**
  (effect-state-machines.md 14.1); under a tail-resumptive one the direct
  entry runs in place, on the native stack.

So the missing piece is crossing *function frames* between the perform and the
handle. Kush has no unwinding tables, and the in-place native path keeps those
frames on the machine stack.

## 2. Options

| | A. Return-path propagation | B. Drop the CPS continuation | C. Native unwinding |
| --- | --- | --- | --- |
| Mechanism | A function whose row contains an abortive operation `F` gets a second return path; every call to such a function checks it and propagates, as an implicit `?` | Force resumable entries for every function that may perform `F`; the handler drops the continuation chain and its environments' drop glue runs | Unwind tables / landing pads emitted by Cranelift, a personality routine in the runtime |
| Cleanup | existing early-exit cleanup of `?`, per frame, in both backends | environment drop glue (new for continuations: tokens are linear today) | new landing-pad cleanup that must mirror drop flags |
| Mainline cost | one compare and branch after each call to a may-abort function, no allocation | a heap frame per call on the path (E-PERF: 120-210 ns per resumable perform) | zero on the non-throwing path |
| Evaluator | one more `Flow` variant, like `Flow::Return` | dropping a continuation value | an abstract unwinding that must be kept in sync with native |
| New trust | small: reuses `?` paths that are already tested for leaks and use-after-free | continuation drop glue and partially reified chains | large: native-only machinery, hard to get parity |

Zero-overhead Lexa (effect-capabilities.md) makes the rare path pay by
switching stacks; Kush has no stack switching, and option C's zero mainline
cost comes with the largest untested surface. Option A's mainline branch is
the same cost Kush already pays for `?`.

## 3. Design (option A)

### 3.1 Surface

```text
effect Fail: i64 -> Never;                 -- abortive operation
fn parse(s: &Text) -> i64 ! {Fail, panic} { ... perform Fail(3) ... }

handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {} { 0 - code } {
    parse(&input) + 1
}
```

- `Never` is accepted **only** as the result type of a declared or lexical
  operation. Such an operation is *abortive*: `perform F(x)` has type `Never`
  (it never returns to its continuation).
- Its handler takes the payload and **no token**, and returns the `handle`'s
  result type. Its value becomes the value of the `handle` expression.
- Today neither form is accepted, so no existing program changes meaning.
  The exact spelling is user-visible syntax and must be confirmed with the
  user before E-ABORT-LEXICAL lands.

### 3.2 Static rules

1. **Rows.** `perform F(x)` adds `F` (and `panic` when the lookup is dynamic,
   as today). `handle F` discharges `F` for its body. A function whose row
   contains `F` is *may-abort for `F`*; this is the row bit, no new analysis.
2. **Obligations on the abort path.** Every perform of `F` and every call of
   a may-abort function is an early exit to the nearest `handle F` that is
   lexically or dynamically outside. The ownership and grade passes check it
   exactly like the error path of `?`: every pending linear obligation is an
   error ("linear value is not consumed before an abortive call to Fail"),
   affine owners get drop flags. This includes resumption tokens of
   enclosing handlers and linear task handles.
3. **Handlers.** A handler of another operation whose code calls its token
   must include the body's abortive bits in the token's row: the abort can
   leave through `resume(...)`, and the handler's own pending values are then
   checked by rule 2. A handler that aborts before resuming leaves its linear
   token pending and is rejected by rule 2.
4. **Barriers.** An abortive operation cannot cross a task boundary: a
   `Task.spawn`/`Task.scope` body whose row contains an unhandled abortive
   bit is rejected. Function values, trait objects and vector callbacks
   carry the bit in their arrow rows, so indirect calls propagate it like
   direct calls.
5. **Missing handler.** A dynamic abortive perform with no handler aborts the
   program, as a missing handler does today (`panic` in the row).

### 3.3 Dynamic semantics

- **Evaluator:** a new `Flow::Abort(op, handle_id, payload)`. Each frame
  propagates it through the same cleanup as `Flow::Return`; the matching
  `handle` (identified by its activation, not by name, so a nested handler for
  the same operation in a callee cannot intercept an abort addressed to an
  outer activation) runs its handler with the payload.
- **Native:** a may-abort function returns its normal result plus a hidden
  abort word in the second return register (0 = normal). After each call to a
  may-abort function the caller tests the word and, if set, takes the early
  exit block that the `?` lowering already builds (drop flags, environment
  releases), returning the word upward. The `handle` compares the word with
  its own activation id and runs the handler. The payload is stored in the
  per-task handler frame before unwinding starts, so it does not need a
  return register.
- **Dynamic lookup:** the perform finds the innermost active `handle F`
  frame as today, writes the payload into it and returns its activation id
  as the abort word.
- **Non-tail handlers:** in a resumable entry an abort is a finish of the
  region that does not call `k`; the continuation `k` is then pending and is
  dropped by the enclosing CPS frame's cleanup. This is the only place an
  abort releases a continuation; it is part of E-ABORT-INTERACT and needs its
  own use-after-free review.

### 3.4 Interaction with capabilities

A `cap F` for an abortive `F` would make `perform op(x)` an early exit to a
statically known activation. That is a strict subset of 3.3 (the abort word
is the capability's activation id) and stays out of EFF-CAP-*: capabilities
optimize only the resumptive mainline (decision 3 of effect-capabilities.md).

## 4. Decisions

1. **Abortive handlers use return-path propagation (option A)**, reusing the
   cleanup and obligation rules of `?`. No native unwinding tables.
2. **Abortive operations are marked by a `Never` result** and their handlers
   take no token. Resumptive operations are unchanged; one operation is never
   both.
3. **Abort addresses a handle activation**, not an operation name, so nested
   handlers cannot intercept it.
4. **No abort across tasks**, and none through a pending linear obligation;
   both are compile-time errors.
5. **Measure the mainline**: a may-abort call that does not abort must stay
   within noise of a direct call plus one branch on the E-PERF harness;
   otherwise the design is revisited before E-ABORT-PROPAGATE is closed.

## 5. Follow-up nodes

- **E-ABORT-LEXICAL** (M): abortive operations whose perform is lexically
  inside its `handle` in the same function (a labelled early exit with `?`
  cleanup); surface syntax confirmed with the user; positive, rejection
  (pending linear values, token-free handler shape), cleanup and parity
  tests.
- **E-ABORT-PROPAGATE** (L): may-abort functions, the hidden abort word,
  call-site checks, dynamic lookup and the evaluator `Flow::Abort`; function
  values, trait objects and vector callbacks; task barrier; the measurement
  of decision 5.
- **E-ABORT-INTERACT** (M): aborts through non-tail and multishot handlers'
  resumptions and resumable entries (dropping a pending continuation), with a
  dedicated use-after-free review.
