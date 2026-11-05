# Effect handlers

Status: implemented. Handlers are **deep** and **one-shot by default**; a
copyable multishot token is available when the continuation's live values can
be copied. A handled body may perform anywhere: in operands, conditions,
branches, loops, and in called functions for a declared operation. When the
handler does work after `resume(x)`, the body is compiled as a resumable state
machine (see [effect state machines](effect-state-machines.md)); when the
handler is a lambda that only ends with `resume(e)`, every perform uses the
allocation-free identity token and continues in place. Checked by the normal
executable type/ownership rules. A handler is directly visible to performs in
its own function body; a declared operation additionally makes the handler
visible through the dynamic handler stack to performs in called functions,
and a declared operation is also a concrete effect-row entry checked exactly
like `io`, `alloc`, `panic`, and `suspend`.

```rust
effect Op: i64 -> i64;

fn call() -> i64 ! {Op, panic} { perform Op(20) }

fn main() -> i64 ! {panic} {
    handle Op: i64 -> i64 with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {} { resume(x) } {
        call() + 1
    }
}
// 21: the called function resolves the dynamically active handler
```

```rust
effect Op: i64 -> i64;

fn call() -> i64 ! {Op, panic} { perform Op(20) }

fn main() -> i64 ! {panic} {
    handle Op: i64 -> i64 with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {} {
        let r = resume(x ^ 1);
        r ^ 4096
    } {
        call() * 3
    }
}
// 4159 = (21 * 3) ^ 4096: resume(21) runs the rest of the body, including the
// code after the call, and the handler sees the body's result
```

```rust
fn main() -> i64 ! {panic} {
    handle Op: i64 -> i64 with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} {
        let r = resume(x + 1);
        r * 2
    } {
        let a = perform Op(20);
        a + 1
    }
}
// 44: resume(21) runs `a + 1`, returns 22, and the handler computes 44
```

## Surface

```text
handle Name: Parameter -> Result with handler {
    body
}

perform Name(payload)
```

- The handler is an ordinary first-class callable. Its contract is
  `fn(Parameter, linear once fn(Result) -> Result) -> Result` (or the `once` /
  `linear once` calling mode), or `fn(Parameter, fn(Result) -> Result) ->
  Result` for multishot. The handler result may be a subtype of
  `Result`; its first parameter may be a supertype of `Parameter`.
- `perform Name(value)` looks up the innermost lexically enclosing `handle`
  with that operation name. The payload is evaluated first, coerced to the
  handler's parameter type, then the handler is called with a fresh resumption
  token.
- The handler is evaluated exactly once when the `handle` expression is
  entered and stored in a hidden local. The body is then evaluated normally.
- A `perform` for an undeclared operation outside a matching lexical handler is
  rejected. A declared operation additionally resolves through the dynamic
  handler stack, so a perform inside a called function is allowed when a
  handler is dynamically active; without one it aborts.

## Declared operations and the dynamic handler stack

```text
effect Name: Parameter -> Result;
```

`effect` declares the payload/result signature of an operation and a concrete
effect-row name. It extends the finite row vocabulary (a 16-bit row with four
built-in bits, so up to twelve declared operations) rather than being a free
string tag. A declared operation may be handled lexically and in addition:

- a `perform Name(value)` requires the declared row bit `Name`, exactly like
  `io`/`alloc`/`panic`/`suspend`;
- a lexical `handle Name` discharges that bit for its body, so called functions
  that declare `{Name}` may be handled there while the enclosing function row
  does not mention `Name`;
- a `perform Name(value)` in a called function uses the declared signature and
  resolves the innermost dynamically active `handle Name` at run time;
- a lexical `handle Name` pushes one frame while its body runs, including while
  it calls other functions, and pops it after normal completion (a multishot
  handler is not pushed: called functions cannot reach it);
- every function records the handler-stack depth at entry and restores it on
  every `return`, dropping any unconsumed owning frame it leaves behind;
- nested handling and shadowing follow the same innermost-first rule as direct
  performs;
- a dynamically resolved `perform` additionally requires `panic` in the
  enclosing row: when no handler is active at run time the program aborts.

A dynamic frame accepts a pure handler of either callable mode. A copyable
noncapturing `fn` frame serves any number of performs. A capturing `once fn`
frame owns its environment: the first perform transfers it to the call (the
callee frees it), a second perform no longer resolves that frame, and an
unconsumed frame is dropped exactly once when the frame pops, or when an early
`return`, `break`, or `continue` leaves the handled body. A handler with
arbitrary effects is rejected because a called function's row would otherwise
omit them. A lexical handler for a declared operation is checked by the same
rules. Handlers for undeclared operation names keep the original lexical
behavior.

The reference evaluator and the native runtime both implement the same stack.
The native stack is per structured task (task 0 is the root) and is restored by
the function epilogue. At `Task.spawn` a child inherits the innermost contiguous
suffix of **copyable noncapturing** frames; a capturing or one-shot frame is a
task boundary because its environment is owned by the parent's dynamic extent.
A child's later pushes and pops are isolated from the parent. `effect`
declarations reject borrowed payload/result types because a stack frame has no
caller lifetime to borrow from.

A perform in a called function is resumed exactly like a lexical one. Under a
handler that does work after `resume`, the handled body calls a **resumable
entry** of every function that may perform the operation: the same body
taking the caller's continuation as an extra parameter, so `resume(x)` runs the
rest of the called function, then the rest of its callers up to the handled
body, and returns the body's result to the handler. Under a tail-resumptive
handler the ordinary entry is called and the token is the identity. Calls that
may perform the operation through a function value, a trait object,
`Task.scope`, a vector callback, or inside a nested handler for another
operation cannot be resumed and are rejected under a non-tail handler. A
spawned child task still resolves an inherited copyable frame with the
identity token: a continuation cannot cross a task boundary.

## One-shot resumption semantics

`resume` has type `linear once fn(Result) -> Result ! {}` by default. The
linear token is consumed on every normal path:

1. The handler must invoke `resume` exactly once on every normal path.
2. Calling it twice is a use-after-move (`linear once` is consumed by the first
   call).
3. Returning without calling it leaves an unconsumed linear obligation.
4. Passing it to another callable transfers the obligation; the ultimate
   consumer must still call it exactly once.
5. A loop that moves the token and iterates again is rejected as a loop-carried
   move, so a token cannot be called a second time on a later iteration.

A handler may instead declare the copyable **multishot** token
`fn(Result) -> Result ! {}` and resume zero, one, or several times; each
resumption re-runs the rest of the body from the perform point with its own
copy of the live values (see the multishot lowering below).

There are three resumption lowerings:

- **Tail-resumptive handler.** A handler written as a lambda at the `handle`
  whose only use of the token is `resume(e)` in tail position computes
  `h(p, k) = k(e)`. Every perform passes the noncapturing identity token and
  the body continues in place: no allocation, constant stack, and `return`,
  `?`, `break` and `continue` behave as in any other code. A perform that is
  the body's tail expression uses the identity token under any handler.
- **Non-tail handler.** Any other handler (code after `resume`, or a handler
  that is not a lambda at the `handle`) makes the body suspendable. Each
  perform is a suspension point: the handler receives a `linear once` token
  whose environment holds exactly the values live after that point, and
  calling it runs the rest of the body from there (through enclosing blocks,
  branches and loops) and returns the body's final result. Code before the
  first perform runs in place. A point whose continuation has no live values
  gets a noncapturing token and allocates nothing.
- **Multishot.** With the copyable `fn(R) -> R` token, a capture-free
  continuation is a plain code pointer. A continuation with live values
  requires the handler to be a noncapturing lambda (or function name) that
  only calls its token directly, and every live value to be copyable and
  ungraded; the handler is then specialized so each `resume(y)` re-runs the
  continuation from its own copy of those values. Owned, linear or graded live
  values, and handlers that pass the token on, are rejected.

Rules for suspendable bodies, checked after ownership:

- the handled body's result type must be the operation result type, because
  that is what the continuation returns to the handler;
- a value holding a borrow (slice or text view, reference, borrowed record,
  task handle) cannot be live across a perform; a loan that ends before the
  perform is fine;
- a local the handler writes through its capture cannot be live across a
  perform;
- a non-copyable local of the enclosing function that is used after a perform
  moves into the continuation and cannot be used after the `handle`; a
  continuation cannot write a local of the enclosing function that is read
  after the `handle`;
- `return`, `?`, and `break`/`continue` to a loop outside the handled body are
  rejected after a perform (Kush has no unwinding to abandon the handler
  activation that is waiting for `resume` to return); in a called function's
  resumable entry, `return` and `?` continue the caller as usual;
- a capturing continuation allocates its environment, so the handle requires
  `{alloc, panic}`;
- a linear operation result is rejected for non-tail resumption;
- a perform nested in a match guard, or inside the body of a nested non-tail
  or declared-operation handler, is rejected.

A one-shot token's linearity makes a second resumption a use-after-move, and a
linear value held across a perform moves into exactly one continuation
environment, so it is never copied or dropped by handling.

## Effects

The handler's own effects and the body's effects are both required by the
`handle` expression. A `handle` whose handler can perform `io` (for example by
calling `print_i64`) cannot appear in a function whose row omits `io`. Handler
effects are ordinary row bits. A declared operation is itself a concrete row
bit: `perform Op` requires `Op` in the enclosing function row, while a lexical
`handle Op` discharges `Op` for its body only. The continuation runs inside the
handler call but its effects are the body's effects; they are therefore already
required at the `handle` site even though the resume token's static arrow is
pure. Undeclared lexical operation names add no row bit.

## Representation

Tail-resumptive performs lower to an indirect handler call with a synthesized
noncapturing identity function as the token. A suspendable body lowers to a
`Region` in the enclosing function plus one continuation function per perform;
a perform becomes an exit from the region whose value is the handler call
with that point's token, a closure over the continuation that captures the
point's live values by move. A resumable entry of a called function is a
second function taking the caller's continuation. Both backends execute the
same lowered IR. Declared-operation frames hold one operation id, one code
pointer, one environment word, and a one-shot flag; a capturing frame's
environment header supplies its drop function, and pop, early function exit,
loop exit and region exit drop an unconsumed environment exactly once. The
stack is a fixed per-task array in the native runtime and a vector in the
reference evaluator.

## Limits

- `return`, `?`, and `break`/`continue` out of the handled body after a perform
  are rejected under non-tail handlers;
- a perform cannot be captured across a nested non-tail handler or a nested
  declared-operation handler (no multi-prompt capture), nor through function
  values, trait objects, `Task.scope` or vector callbacks;
- multishot continuations with live values need a known noncapturing handler
  that only calls its token, and copyable ungraded live values; multishot
  resumption through called functions is not implemented, and a multishot
  handler for a declared operation is not visible to called functions;
- non-tail handlers nest one activation per pending perform, so stack use is
  linear in the number of performs resumed before the body ends; the reference
  evaluator's fixed nesting budget allows only about ten of them;
- a child task resumes inherited copyable frames with the identity token;
- declared effect rows are a finite 16-bit universe: four built-in bits plus at
  most twelve `effect` operations. There is no effect-polymorphic handler type
  over operation names, and the handler contract is a single operation per
  `handle`; several operations use nested handlers;
- borrows of storage outside the handled body cannot be held across a perform
  (plan node E-CPS-BORROW);
- `perform` cannot be used in an erased logical definition or a total function.

The tests in `crates/kush/tests/effect_state_machines.rs` and
`crates/kush/tests/advanced_types_effects.rs` cover both backends with
allocation balance: performs in loops, branches, expressions and called
functions, evaluation order, short-circuits, `break`/`continue`, owned and
linear values across performs, recursion, `return`/`?` in called functions,
multishot copies, a million tail-resumptive performs in constant stack, and
every rejection above.

## Native bookkeeping on handler-free paths

Functions with no local dynamic `HandlerPush` omit function/loop handler-depth
snapshots and exit restorations in both default and release native builds.
An exhaustive checked-IR child scan determines this property. Called functions
restore their own local frames; a function that may install a handler retains
the original guards, including early return, break and continue paths. Dynamic
lookup and task inheritance rules above are unchanged. See [research actions](research-actions.md)
for the proof boundary, codegen tests and paper applicability. This is not a
claim that all Kush effect handling is zero-overhead.
