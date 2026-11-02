# Lexical one-shot effect handlers

Status: implemented restricted handler fragment. Handlers are **lexically
scoped, one-shot, tail-resumptive** and are checked by the normal executable
type/ownership rules. They are not general delimited continuations and they do
not add user-defined effects to the public effect row vocabulary.

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

Handlers add no runtime allocation and no new value representation. A `handle`
lowers to an ordinary hidden local binding plus an ordinary block. `perform`
lowers to an indirect call with a synthesized noncapturing identity function as
the resumption value. The resumption value uses the existing `once` callable
ABI (a code pointer plus a null environment), so the reference evaluator and
Cranelift backend execute the same checked IR. The hidden handler local is
released/dropped by the ordinary ownership pass on every exit, including early
`return`, `?`, and loop exits.

## Limits

This is a usable handler fragment, not a general algebraic-effect runtime:

- handlers are lexical to direct `perform` expressions in the same function
  body; there is no dynamically scoped handler stack across calls;
- no captured delimited continuation, no non-tail resumption, no multishot
  handlers, and no handler reinterpretation of arbitrary control effects;
- no user-defined effect declarations, rows, or effect-polymorphic handler
  types beyond the existing `{panic, io, alloc, suspend}` vocabulary;
- the handler contract is a single operation per `handle`; several operations
  use nested handlers;
- `perform` cannot be used in an erased logical definition or a total function.

The tests in `crates/kush/tests/advanced_types_effects.rs` cover execution in
both backends, nested shadowing, multiple pure performs, owning payload/result
cleanup, one-shot resume use-after-move, ignored linear resumption, missing
handlers (including a called function), exact resume-contract checking, and
handler-effect propagation.
