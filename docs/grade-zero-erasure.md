# Grade-zero runtime erasure

Status: implemented for the executable subset in both backends, across local
bindings, parameters, results, function values, adapters, closures, static and
default trait methods, dynamic dispatch, and structured tasks' callable
boundaries. `@[0]` is both a use restriction and a physical erasure annotation:
the argument/initializer/body is still evaluated because Kush is strict, but no
runtime slot, ABI word, return payload, store, read, or allocation is emitted
for the erased position. Every runtime observation remains a compile-time
error.

A custom algebra's additive identity (`@[Algebra.Zero]`) is erased the same
way, provided the algebra's zero and one are distinct.

## Local bindings

An erased binding is not materialized:

```kush
fn main() -> i64 ! {io, panic} {
    let value: i64 @[0] = { print_i64(7); 1 };
    42
}
```

Both backends print `7` and exit with status `42`. The initializer is evaluated
in source order, may panic, may allocate, and may perform I/O exactly as an
ordinary expression. Allocation diagnostics remain balanced.

Affine owning storage may be erased when the source semantics permit eager
initialization and drop:

```kush
fn main() -> i64 ! {alloc, panic} {
    let value: Box<i64> @[0] = Box.new(9);
    42
}
```

The initializer runs, the allocation is dropped exactly once at the binding
site, and no local storage is created. Assignment to an erased affine binding
evaluates and drops the replacement in the same way. A `#[linear]` value (or an
owning value with a transferred linear obligation) cannot be graded `@[0]`:
silently discarding that obligation is never allowed.

## Parameters: physical ABI erasure

A `@[0]` parameter is still written and evaluated at the call site, but it has
no ABI slot. This is a physical change, not just a use restriction: the erased
parameter is absent from the native calling convention, from indirect-call
signatures, and from the reference evaluator's argument binding. Arguments are
always evaluated left to right, so their effects and order survive:

```kush
fn pick(a: i64 @[0], b: i64, c: i64 @[0]) -> i64 ! {panic} { b }
fn main() -> i64 ! {io, panic} {
    pick({ print_i64(1); 10 }, { print_i64(2); 20 }, { print_i64(3); 30 })
}
```

prints `1`, `2`, `3` and returns `20`. The callee cannot read, move, borrow, or
capture an erased parameter. Owning/linear parameters cannot be graded `@[0]`,
because their argument would have to be discarded.

The erasure applies to:

- named, generic, and default trait methods;
- function values and indirect calls;
- lambdas and once/linear-once closures (captures are unaffected);
- closed-world dynamic dispatch: the dispatcher, every member call, and the
  object-safety agreement all use the same physical arity;
- synthesized pure and once adapters.

`Vec.map_in_place` and `Vec.map_chain_in_place` explicitly reject callbacks
whose element parameter or result is erased: those builtins always observe
every element and store every result, so an erased ABI would not match their
calling loop. This is a diagnostic, not a silent ABI mismatch.

### Arrow subtyping trap

A source parameter graded `@[0]` may be used where an ordinary or stricter
parameter contract is expected (`fn(i64 @[0]) -> T` as `fn(i64) -> T`): the
callee never looks at the argument. The **logical** parameter lists are equal,
but the **physical** arity differs. The compiler therefore does not treat this
as a raw function-pointer cast. It synthesizes a checked adapter that accepts
the target's physical arguments, discards the values the source ignores, and
calls the source's shorter ABI. `same_layout`/`arrow_rep_change` compare erased
positions as representation changes, and pure-to-once, pure-to-pure, capturing,
indirect, and trait-dispatched conversions all go through that path.

The reverse direction (`fn(i64) -> T` as `fn(i64 @[0]) -> T`) is rejected: a
target caller supplies no value for a parameter the source observes, and no
adapter can invent one.

## Results: physical payload erasure

A copyable result may be graded `@[0]`. The body still runs for its effects and
is type-checked against the declared payload type, but the callee returns no
payload and the call has type `Unit`:

```kush
fn compute() -> i64 @[0] ! {io, panic} { print_i64(7); 42 }
fn main() -> i64 ! {io, panic} { compute(); 9 }
```

prints `7` and exits with status `9`. The native function has no return
register/pointer; the reference evaluator returns `Unit` after consuming the
computed value. Nested erased results compose: returning a `Unit` call from
another erased-result function is well-typed, and branches/match arms are
erased before joining.

Because the call expression is `Unit`, there is no value to launder. Binding it
to a typed local, using it as an operand, argument, aggregate field, `?`
operand, coercion, or `return` into a non-erased result is a type error. A
`@[0]` result on an owning or linear value is rejected: the returned resource
would have no observable payload and no transfer point. Consume it inside the
function or declare a `@[1]` result instead.

## Storage and backend behavior

- Native lowering evaluates every argument/initializer/body, filters erased
  parameter words from the call, emits neither a store nor an activation for an
  erased local, and omits erased result words.
- The reference evaluator evaluates and consumes the same expressions, skips
  `store_local`/activation for erased locals, binds only physical arguments, and
  returns `Unit` for erased results. Its frame is a fixed-size host vector, not
  program-visible storage.
- Assignment to an erased affine binding evaluates the replacement for effects
  and drops it; an erased result is dropped at the return boundary exactly once
  when it is affine owned (such results are rejected today, so this is defensive).
- A custom algebra's zero element is erased the same way.
- `@[0]` on a linear obligation is rejected.

## Guarantees and non-guarantees

Guaranteed:

- no runtime observation of an erased binding, parameter, or result;
- initializer/argument effects and their source order preserved;
- allocation/deallocation balance, actual cleanup, and backend agreement;
- erased parameters/results absent from both physical calling conventions;
- checked adapters wherever a logical parameter contract differs physically.

Not claimed:

- elimination of computation inside an initializer, argument, or body;
- a runtime check or tag for erased positions;
- erasure of proof terms beyond the existing erased-parameter mechanism;
- erasure of owning/linear results or owning/linear parameters (rejected);
- erased element parameters/results in the vector map builtins (rejected).

## Tests

`crates/kush/tests/grade_zero_erasure.rs` covers direct and multi-argument
parameter erasure with observable effects, callee rejection, pure and
once adapter bridging in both variance directions, indirect erased calls,
dynamic dispatch, dynamic result erasure, result non-laundering, nested erased
returns, affine eager drop with allocation balance, linear rejection, and native
execution. `crates/kush/tests/grades.rs` retains the grade/demand tests.
