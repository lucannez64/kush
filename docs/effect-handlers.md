# One-shot effect handlers

Status: implemented restricted handler fragment. Handlers are **one-shot by
default**; a capture-free continuation may instead use a copyable multishot
token. A `perform` in tail position uses the original allocation-free identity
resumption token; a `perform` that is the whole value of a top-level statement
gets a real one-shot continuation, so the handler can run code after
`resume(x)` returns. Checked by the normal executable type/ownership rules. A
handler is directly visible to performs in its own function body; a declared
operation additionally makes the handler visible through the dynamic handler
stack to performs in called functions, and a declared operation is also a
concrete effect-row entry checked exactly like `io`, `alloc`, `panic`, and
`suspend`. Handlers are still not general delimited continuations.

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
  Result` for capture-free multishot. The handler result may be a subtype of
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
  it calls other functions, and pops it after normal completion;
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

Dynamic performs remain **tail-resumptive** in this fragment: the token is the
identity on the operation result. A called function has no continuation of the
caller's handled body, so capturing one would cross an arbitrary call stack.
Lexical non-tail resumption is implemented only where the continuation is
visible in the same function body.

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
`fn(Result) -> Result ! {}`. It is accepted only when the continuation owns no
environment: the tail identity token, or a non-tail continuation that captures
nothing. Calling it any number of times re-runs the captured suffix from the
perform point, so a handler may resume zero, one, or several times. A
continuation with any captured value is instead an owning `once` closure and
stays one-shot; using the multishot token there is an explicit rejection rather
than silently sharing the environment.

There are two resumption lowerings:

- **Tail perform.** When `perform` is the handled body's tail expression, its
  continuation is empty. `resume(x)` returns `x`, the handler's value is the
  handle result, and the token is a noncapturing identity adapter with no
  allocation.
- **Non-tail perform.** When `perform` is the entire value of a top-level
  `let` or expression statement, the rest of the handled body is checked as a
  real continuation closure of type `linear once fn(Result) -> Result` (or the
  capture-free `fn(Result) -> Result` multishot form). Calling `resume(x)` runs
  that continuation with `x` and returns the body's final result to the
  handler. The handler may run code before and after the call, and its return
  value is the handle result.

The non-tail fragment is deliberately explicit:

- exactly one lexical `perform` for the handled operation, at a top-level
  statement of the handled body; a nested operand or a second non-tail perform
  is rejected instead of silently falling back to identity semantics;
- the handled body's result type must be the operation result type, because
  that is what the continuation returns;
- `return` and `?` inside the continuation are rejected; they would return
  across the resumption boundary. `break`/`continue` are allowed for loops
  written inside the continuation, but cannot target a loop outside it.
  Lambdas defined in the continuation are separate functions and may use
  `return`/`?` normally;
- `let mut a = perform Op(x);` keeps its `mut` binding in the continuation;
- the continuation captures values live at the perform point by value. It
  rejects mutable, borrowed, reference, task, and `@[0]` captures rather than
  inventing aliasing or lifetime rules. A capturing continuation allocates its
  environment, so the handle body requires `{alloc, panic}`; a noncapturing
  continuation needs neither;
- a linear operation result is rejected for non-tail resumption;
- arithmetic `{ ... }` facts are reset inside the continuation, so a proof
  obligation there must be re-established from the continuation's own
  bindings; erased proof parameters and symbolic scalar indices remain usable.

After the handler returns, the perform site has already been replaced by the
handler call; there is no captured continuation frame left. A one-shot
continuation's linear token makes a second resumption a use-after-move. A
linear value held across `perform` is never copied or duplicated by handling.
Ordinary ownership rules apply to the body, the payload, and the handler
captures. A capturing `once fn` handler is consumed by its first `perform`, so a
second `perform` is rejected unless the handler mode is copyable `fn`.

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

Tail handles add no value representation and no runtime allocation for their
frames: a tail `perform` lowers to an indirect call with a synthesized
noncapturing identity function as the resumption value. A non-tail `perform`
lowers to an ordinary `once fn` closure (or, when it captures nothing and the
handler requests multishot, a plain `fn`) whose body is the remaining checked
body; it uses the existing closure ABI, so the reference evaluator and
Cranelift backend execute the same checked IR. A dynamic `perform` lowers to a
checked handler-stack lookup followed by an indirect call. The hidden handler
local is released/dropped by the ordinary ownership pass on every exit,
including early `return`, `?`, and loop exits. Declared-operation frames hold
one operation id, one code pointer, one environment word, and a one-shot flag.
A capturing frame's environment header supplies its drop function; pop, early
function exit, and loop exit drop an unconsumed environment exactly once, while
a consumed one is freed by the handler call. The stack is a fixed per-task
array in the native runtime and a vector in the reference evaluator.

## Limits

This is a usable handler fragment, not a general algebraic-effect runtime:

- lexical non-tail resumption is limited to one top-level statement perform per
  handle; general expression contexts, multiple prompts, and nested
  continuations are not implemented. A `perform` nested in an operand, a
  condition, a call argument, or a second non-tail perform is an explicit
  rejection;
- dynamic performs remain tail-resumptive: a called function's `resume` is the
  identity on the operation result and cannot run caller code after it returns.
  A handler cannot capture a continuation across an arbitrary call stack;
- multishot is available only for a capture-free continuation, using the
  copyable `fn(R) -> R` token. A continuation with copyable-but-nonempty
  captures still owns a heap environment and stays one-shot;
- there is no handler reinterpretation of arbitrary control effects, and no
  `return`/`?`/`break`/`continue` through a resumption;
- declared effect rows are a finite 16-bit universe: four built-in bits plus at
  most twelve `effect` operations. There is no effect-polymorphic handler type
  over operation names, and the handler contract is a single operation per
  `handle`; several operations use nested handlers;
- a child task inherits only copyable noncapturing frames. A capturing or
  one-shot frame is an isolation boundary and is not visible to the child;
- `perform` cannot be used in an erased logical definition or a total function.

The tests in `crates/kush/tests/advanced_types_effects.rs` cover execution in
both backends, nested shadowing, multiple pure performs, owning payload/result
cleanup, one-shot resume use-after-move, ignored linear resumption, loop-carried
resumption moves, missing handlers, exact resume-contract checking,
handler-effect propagation, dynamic handler lookup in a called function,
copyable multi-perform handlers, early return stack restoration, real non-tail
resumption in both backends, continuation capture cleanup, rejected nested and
multiple non-tail performs, continuation-effect leakage, rejected linear
operation results, capture-free multishot resumption, rejected multishot with
captures, capturing dynamic handler ownership and early-exit cleanup, one-shot
dynamic consumption, task inheritance and capturing-frame isolation, and
user-declared effect-row checking and discharge.


## Native bookkeeping on handler-free paths

Functions with no local dynamic `HandlerPush` omit function/loop handler-depth
snapshots and exit restorations in both default and release native builds.
An exhaustive checked-IR child scan determines this property. Called functions
restore their own local frames; a function that may install a handler retains
the original guards, including early return, break and continue paths. Dynamic
lookup and task inheritance rules above are unchanged. See [research actions](research-actions.md)
for the proof boundary, codegen tests and paper applicability. This is not a
claim that all Kush effect handling is zero-overhead.
