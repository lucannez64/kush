# One-shot effect handlers

Status: implemented restricted handler fragment. Handlers are **one-shot and
tail-resumptive** and are checked by the normal executable type/ownership
rules. A handler is directly visible to performs in its own function body; a
declared operation additionally makes the handler visible through the dynamic
handler stack to performs in called functions. Handlers are still not general
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
// 43
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

## One-shot resumption semantics

`resume` has type `linear once fn(Result) -> Result ! {}`. It is an identity
capability over the operation result:

1. The handler must invoke `resume` exactly once on every normal path.
2. Calling it twice is a use-after-move (`linear once` is consumed by the first
   call).
3. Returning without calling it leaves an unconsumed linear obligation.
4. Passing it to another callable transfers the obligation; the ultimate
   consumer must still call it exactly once.

After the handler returns, the perform site continues with the handler's
returned value. There is no captured continuation between `perform` and the
handler, so **multishot** (calling the continuation a second time after the
first resumption) is unrepresentable. A linear value held across `perform` is
never copied or duplicated by handling; ordinary ownership rules apply to the
body, the payload, and the handler captures. A capturing `once fn` handler is
consumed by its first `perform`, so a second `perform` is rejected unless the
handler mode is copyable `fn`.

## Effects

The handler's own effects and the body's effects are both required by the
`handle` expression. A `handle` whose handler can perform `io` (for example by
calling `print_i64`) cannot appear in a function whose row omits `io`. Handler
effects are ordinary row bits; there is no new effect name and no row
subtraction. Performing an operation does not itself add an effect to the
function row: the handler's effects and the body's effects are the complete
observable contract.

## Representation

Handlers add no value representation and no runtime allocation for their
frames. A `handle` lowers to an ordinary hidden local binding plus an ordinary
block. A direct `perform` lowers to an indirect call with a synthesized
noncapturing identity function as the resumption value; a dynamic `perform`
lowers to a checked handler-stack lookup followed by the same indirect call.
The resumption value uses the existing `once` callable ABI (a code pointer plus
a null environment), so the reference evaluator and Cranelift backend execute
the same checked IR. The hidden handler local is released/dropped by the
ordinary ownership pass on every exit, including early `return`, `?`, and loop
exits. Declared-operation frames hold one operation id plus one code pointer;
the stack itself is a fixed per-thread array in the native runtime and a vector
in the reference evaluator.

## Limits

This is a usable handler fragment, not a general algebraic-effect runtime:

- no captured delimited continuation, no non-tail continuation capture, no
  multishot handlers, and no handler reinterpretation of arbitrary control
  effects. `resume` is still the identity operation result, so handler-side work
  before and after the call happens around the body rather than inside a
  captured continuation;
- declared effects make a handler dynamically visible to called functions, but
  only for pure noncapturing `fn` handlers. Capturing/`once` handlers stay
  lexical, and dynamic frames do not cross structured-task boundaries;
- effect-row names remain the fixed `{panic, io, alloc, suspend}` vocabulary;
  `effect Name` declares an operation signature, not a new row name, and there
  is no effect-polymorphic handler type over operation names;
- the handler contract is a single operation per `handle`; several operations
  use nested handlers;
- `perform` cannot be used in an erased logical definition or a total function.

The tests in `crates/kush/tests/advanced_types_effects.rs` cover execution in
both backends, nested shadowing, multiple pure performs, owning payload/result
cleanup, one-shot resume use-after-move, ignored linear resumption, missing
handlers, exact resume-contract checking, handler-effect propagation, dynamic
handler lookup in a called function, copyable multi-perform handlers, early
return stack restoration, and rejection of impure/capturing/signature-mismatched
dynamic handlers.
