# One-shot effect handlers

Status: implemented restricted handler fragment. Handlers are **one-shot**.
A `perform` in tail position uses the original allocation-free identity
resumption token; a `perform` that is the whole value of a top-level statement
gets a real one-shot continuation, so the handler can run code after
`resume(x)` returns. Checked by the normal executable type/ownership rules. A
handler is directly visible to performs in its own function body; a declared
operation additionally makes the handler visible through the dynamic handler
stack to performs in called functions. Handlers are still not general
delimited continuations and they do not add user-defined names to the
`{io, alloc, panic, suspend}` effect-row vocabulary.

```rust
effect Op: i64 -> i64;

fn call() -> i64 ! {panic} { perform Op(20) }

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
  `linear once` calling mode). The handler result may be a subtype of `Result`;
  its first parameter may be a supertype of `Parameter`.
- `perform Name(value)` looks up the innermost lexically enclosing `handle`
  with that operation name. The payload is evaluated first, coerced to the
  handler's parameter type, then the handler is called with a fresh resumption
  token.
- The handler is evaluated exactly once when the `handle` expression is
  entered and stored in a hidden local. The body is then evaluated normally.
- `perform` outside a matching lexical handler is rejected. A `perform` inside
  a called function or a nested lambda is outside the enclosing handler scope:
  handlers do not stack dynamically across function calls.

## Declared operations and the dynamic handler stack

```text
effect Name: Parameter -> Result;
```

`effect` declares the payload/result signature of an operation without adding a
name to the four-bit function effect row. A declared operation may be handled
lexically exactly as before, and in addition:

- a `perform Name(value)` in a called function uses the declared signature and
  resolves the innermost dynamically active `handle Name` at run time;
- a lexical `handle Name` pushes one frame while its body runs, including while
  it calls other functions, and pops it after normal completion;
- every function records the handler-stack depth at entry and restores it on
  every `return`, so an early return cannot leave a stale frame visible;
- nested handling and shadowing follow the same innermost-first rule as direct
  performs.
- a dynamically resolved `perform` requires `panic` in the enclosing row: when
  no handler is active at run time the program aborts, so a function with an
  empty row cannot perform a declared operation outside a lexical handler.

The dynamic frame stores only a **noncapturing `fn`** handler and the handler
must have an empty effect row. This is deliberate: a capturing/`once` handler
owns an environment that cannot be shared through a stack entry, and a handler
with arbitrary effects could perform `io`/`alloc`/`panic` while the caller's
row omits them. A lexical handler for a declared operation is checked by the
same rules. Handlers for undeclared operation names keep the original lexical
behavior.

The reference evaluator and the native runtime both implement the same stack.
The native stack is per structured task (task 0 is the root) and is restored by
the function epilogue; a child task does not inherit a parent's dynamic handler
frame. `effect` declarations reject borrowed payload/result types because a
stack frame has no caller lifetime to borrow from.

Dynamic performs remain **tail-resumptive** in this fragment: the token is the
identity on the operation result. A called function has no continuation of the
caller's handled body, so capturing one would cross an arbitrary call stack.
Lexical non-tail resumption is implemented only where the continuation is
visible in the same function body.

## One-shot resumption semantics

`resume` has type `linear once fn(Result) -> Result ! {}`. The linear token is
consumed on every normal path:

1. The handler must invoke `resume` exactly once on every normal path.
2. Calling it twice is a use-after-move (`linear once` is consumed by the first
   call).
3. Returning without calling it leaves an unconsumed linear obligation.
4. Passing it to another callable transfers the obligation; the ultimate
   consumer must still call it exactly once.
5. A loop that moves the token and iterates again is rejected as a loop-carried
   move, so a token cannot be called a second time on a later iteration.

There are two resumption lowerings:

- **Tail perform.** When `perform` is the handled body's tail expression, its
  continuation is empty. `resume(x)` returns `x`, the handler's value is the
  handle result, and the token is a noncapturing identity adapter with no
  allocation.
- **Non-tail perform.** When `perform` is the entire value of a top-level
  `let` or expression statement, the rest of the handled body is checked as a
  real continuation closure of type `linear once fn(Result) -> Result`. Calling
  `resume(x)` runs that continuation with `x` and returns the body's final
  result to the handler. The handler may run code before and after the call,
  and its return value is the handle result. The continuation is one-shot
  because the token is linear; multishot is unrepresentable.

The non-tail fragment is deliberately explicit:

- exactly one lexical `perform` for the handled operation, at a top-level
  statement of the handled body; a nested operand or a second non-tail perform
  is rejected instead of silently falling back to identity semantics;
- the handled body's result type must be the operation result type, because
  that is what the continuation returns;
- `return`, `break`, and `continue` inside the continuation are rejected; they
  would cross the resumption boundary;
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
handler call; there is no captured continuation frame left. Multishot
(calling the continuation a second time after the first resumption) is
unrepresentable, and a linear value held across `perform` is never copied or
duplicated by handling. Ordinary ownership rules apply to the body, the
payload, and the handler captures. A capturing `once fn` handler is consumed by
its first `perform`, so a second `perform` is rejected unless the handler mode
is copyable `fn`.

## Effects

The handler's own effects and the body's effects are both required by the
`handle` expression. A `handle` whose handler can perform `io` (for example by
calling `print_i64`) cannot appear in a function whose row omits `io`. Handler
effects are ordinary row bits; there is no new effect name and no row
subtraction. Performing an operation does not itself add an effect to the
function row: the handler's effects and the body's effects are the complete
observable contract. The continuation runs inside the handler call but its
effects are the body's effects; they are therefore already required at the
`handle` site even though the resume token's static arrow is pure.

## Representation

Tail handles add no value representation and no runtime allocation for their
frames: a tail `perform` lowers to an indirect call with a synthesized
noncapturing identity function as the resumption value. A non-tail `perform`
lowers to an ordinary `once fn` closure whose environment holds the captured
values and whose body is the remaining checked body; it uses the existing
closure ABI, so the reference evaluator and Cranelift backend execute the same
checked IR. A dynamic `perform` lowers to a checked handler-stack lookup
followed by the identity-resumption indirect call. The hidden handler local is
released/dropped by the ordinary ownership pass on every exit, including early
`return`, `?`, and loop exits. Declared-operation frames hold one operation id
plus one code pointer; the stack itself is a fixed per-thread array in the
native runtime and a vector in the reference evaluator.

## Limits

This is a usable handler fragment, not a general algebraic-effect runtime:

- lexical non-tail resumption is limited to one top-level statement perform per
  handle; general expression contexts, multiple prompts, and nested
  continuations are not implemented;
- dynamic performs remain tail-resumptive; declared effects make a handler
  dynamically visible to called functions, but only for pure noncapturing `fn`
  handlers. Capturing/`once` handlers stay lexical, and dynamic frames do not
  cross structured-task boundaries;
- there is no multishot, no handler reinterpretation of arbitrary control
  effects, and no `return`/`break`/`continue` through a resumption;
- effect-row names remain the fixed `{panic, io, alloc, suspend}` vocabulary;
  `effect Name` declares an operation signature, not a new row name, and there
  is no effect-polymorphic handler type over operation names;
- the handler contract is a single operation per `handle`; several operations
  use nested handlers;
- `perform` cannot be used in an erased logical definition or a total function.

The tests in `crates/kush/tests/advanced_types_effects.rs` cover execution in
both backends, nested shadowing, multiple pure performs, owning payload/result
cleanup, one-shot resume use-after-move, ignored linear resumption, loop-carried
resumption moves, missing handlers, exact resume-contract checking,
handler-effect propagation, dynamic handler lookup in a called function,
copyable multi-perform handlers, early return stack restoration, real non-tail
resumption in both backends, continuation capture cleanup, rejected nested and
multiple non-tail performs, continuation-effect leakage, rejected linear
operation results, and rejection of impure/capturing/signature-mismatched
dynamic handlers.
