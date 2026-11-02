# Usage grades

Status: implemented for the executable subset on top of affine ownership. This
is a usable, tested grade interface, not a formal soundness proof and not the
complete dependent graded calculus described by the [v0.1 specification](spec-v0.1.md#71-graded-modalities).

Parameter and local binding grades, together with the restricted result-transfer
contract `-> T @[1]` on owning, intrinsically linear, or copyable results, are
implemented. Result grades are static metadata erased at runtime; they do not
add a tag, allocation, or ABI change. On an owning value `@[1]` transfers the
linear resource obligation; on a copyable value it transfers a must-use
observation obligation. See [copyable result transfer](copyable-result-transfer.md).
General graded modalities beyond binding, parameter, and result grades remain
out of scope.

```sh
cargo run -p kush -- check examples/grades.kush
cargo run -p kush -- eval examples/grades.kush   # 42
cargo run -p kush -- run examples/grades.kush    # exit status 42
```

`T @[g]` controls how many times a parameter or local binding may be observed.
The executable checker supports natural multiplicities, unbounded usage, exact
zero-use bindings, compile-time grade arithmetic, and explicitly specialized
abstract grade parameters. Grades are compile-time only; they have no runtime
representation and no runtime check.

## Grade semiring

A grade is an element of the ordered semiring of natural usage bounds extended
with infinity:

```text
g ::= 0 | 1 | 2 | ... | many | G          -- G is an abstract grade parameter
    | Algebra.Element                     -- a validated finite custom algebra
```

Sequential use adds; substitution composes multiplicatively:

```text
0 + g     = g            g + many     = many
g + h     = g + h        (checked 64-bit addition)
0 * g     = 0            g * 0        = 0
1 * g     = g            n * many     = many   (n > 0)
g * h     = g * h        (checked 64-bit multiplication)
many * many = many
```

`0 * many = 0` is intentional: if a result is used zero times, an enclosing
operation cannot duplicate it. Finite grade arithmetic that overflows 64 bits is
rejected; it is never silently rounded to `many`.

Annotations accept natural literals, `many`, grade variables, parentheses, `+`,
and `*`:

```rust
T @[0]
T @[1]
T @[7]
T @[1 + 1]
T @[(2 + 1) * 2]
T @[many]
T @[G]          // with <G: Grade>
T @[G * 2]
```

Grades are a separate grammar from ordinary types. They are meaningful on a
function parameter, a simple `let` binding, and a function result. On a result
only exactly `@[1]` is accepted. It transfers an owning linear obligation for an
owning or intrinsically linear result, and a must-use observation obligation for
a copyable result; `@[0]`, finite `n > 1`, `many`, and abstract grades without a
concrete specialization are rejected explicitly. A grade on a stored field, a
nested type argument, an array element, an erased proof parameter, or a
destructuring binder is rejected explicitly.

## Binding rules

| Grade | Copyable value | Owning/linear value |
| --- | --- | --- |
| none | unrestricted, affine ownership rules apply | affine: moved at most once, automatically dropped |
| `@[0]` | exact zero runtime observations | rejected: would silently discard storage |
| `@[1]` | exactly one observation | exactly one consumption (the linear obligation) |
| `@[n]`, `n >= 2` | exactly `n` observations | rejected: would duplicate storage |
| `@[many]` | unrestricted observations | rejected: would duplicate storage |

A value is owning if it is `Box<T>`, `Bytes`, `Vec<T>`, or an enum/record with
an owning or `#[linear]` part. `@[1]` on an owning value remains a linear
obligation: the existing ownership pass still requires it to be consumed on
every normal exit, and an implicit drop is still an error. `@[1]` on a copyable
value is enforced by the grade checker; it must be observed or passed exactly
once, and explicit `drop` is rejected as it was for the original linear mode.

Grade zero is a **use restriction**, not proof erasure. Its initializer is still
evaluated because Kush is strict, but the resulting binding cannot be read,
moved, borrowed, passed to a call, matched, or otherwise observed. Owning and
linear values cannot be graded zero. True erased logical values remain the
`erased` proof-parameter mechanism described in [kernel.md](kernel.md).

## Result transfer contracts

`fn make() -> Box<i64> @[1]` declares that every caller acquires a linear
obligation for the returned owning value and must consume it exactly once.
`@[1]` keeps its ordinary meaning on a parameter or local binding; on a result
it transfers an obligation outward instead of retaining it in the callee.

```rust
fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }
fn identity(b: Box<i64> @[1]) -> Box<i64> @[1] ! {} { b }

fn main() -> i64 ! {alloc, panic} {
    let b = identity(make(41));   // b is linear
    Box.take(b)                    // exactly one consumption
}
```

- The result contract requires an owning, intrinsically linear, or copyable
  result. On an owning result it transfers a resource obligation. On a copyable
  scalar, tuple, record, or borrowed view it transfers a must-use observation
  obligation, tracked by the grade pass; see
  [copyable result transfer](copyable-result-transfer.md).
- Exactly `@[1]` is implemented. `@[0]` would discard the returned value,
  finite `n > 1` and `many` could duplicate one owner, and abstract result
  grades must be specialized to a concrete `1` before the instance is checked.
- Transparent aliases are expanded in result position, so
  `type Handle<T> = Box<T> @[1]; fn make() -> Handle<i64>` carries the same
  contract. An alias in an arrow result is expanded the same way.
- The contract is threaded through named and generic functions, static trait
  and method signatures (compared exactly), typed lambdas, callable arrow
  types, indirect calls, and checked adapters. Arrow subtyping requires an
  exact result-grade match; a coercion or union injection cannot drop the
  obligation.
- The runtime payload type and ABI are unchanged. `result_grade` is compiler
  metadata only, and no runtime tag, allocation, or check is emitted for it.

The body must satisfy the contract on every normal return, and the caller must
consume or observe the returned value exactly once. An owning call result with
`@[1]` is a linear value at its use site: binding it marks the binding linear,
passing it to an ungraded parameter is rejected, and dropping it,
wildcard-binding it, storing it in an affine container, or leaving it at scope
end is an error. A copyable call result with `@[1]` is a must-use value:
binding it marks the binding `@[1]`, an expression statement or wildcard cannot
discard it, and returning it needs a matching copyable `@[1]` result.

A binding-based linear obligation must not be returned through an *ungraded*
result of a non-linear type. The following is rejected, because the caller
would receive an ordinary affine `Box`:

```rust
fn identity(b: Box<i64> @[1]) -> Box<i64> ! {} { b }   // rejected
```

Annotate the result `@[1]` instead. Intrinsic `#[linear]` data and
`linear once fn(...)` types already carry their obligation in the type, so an
ungraded result remains valid for them.

Transfers are preserved through `let` aliases and assignment, branches and
match arms, loop back-edge fixed points and loop break results, `?` success
payloads, tuple/record/enum constructors and destructuring, `Box.new`,
`Box.take`, `Box.reuse`, and linear-once captures. A graded result in an
earlier field or argument remains pending: an early `return`, `?`, `break`, or
`continue` that abandons it is rejected. `?` on a graded `Result` transfers the
obligation only when the success payload is owning; a copyable success payload
is rejected instead of becoming affine.

Borrowed views and exclusive capabilities are never made owning by a result
grade. Task results remain rejected: cancellation would have to discard the
obligation, and no complete cancel/cleanup contract exists yet. The existing
conservative rejection of linear owners through `String.bytes` and
`String.from_utf8` is unchanged.

## Uses, demands, and calls

A use is a read/copy of a copyable binding or a consumption of an owning/linear
binding. Consuming uses (`Move`, `Box.take`, a move into a call, a constructor
field move) count once even under a larger demand: the callee may duplicate the
resulting copyable value, but it cannot duplicate the owner that produced it.

Copyable observations are scaled by the surrounding duplication demand. A call
argument is evaluated under the callee parameter's grade:

| Callee parameter grade | Demand on a copyable argument expression |
| --- | --- |
| unannotated | 1 |
| `@[0]` | 1 (strict evaluation; the callee may not observe it) |
| `@[n]` | `n` |
| `@[many]` | unbounded |

Demands compose multiplicatively through nested calls. For example:

```rust
fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
fn four(x: i64 @[4]) -> i64 ! {panic} { twice(x) + twice(x) }
fn six(x: i64 @[6]) -> i64 ! {panic} { twice(x) + four(x) }
```

`twice(x)` uses `x` twice, `four(x)` four times, and `six(x)` six times even
though each body has only one syntactic occurrence of `x` per call. The callee's
own body is checked separately, so both the caller's count and the callee's
parameter obligation are enforced. A finite exact binding therefore cannot be
passed to a `@[many]` parameter; use an unannotated or `@[many]` binding when an
unbounded demand is intended.

This is a modal usage count, not a dataflow analysis of side effects. A
side-effecting block passed to a high-demand parameter is conservatively counted
under the higher demand. Programs that need a different accounting should hoist
the effectful computation before the call.

## Branching, short circuit, returns, and `?`

Sequential uses add. Exclusive paths must agree:

```rust
if c { x + x } else { x + x }   // accepted for @[2]
if c { x + x } else { x }       // rejected for @[2]
```

The right operand of `&&`/`||` may be skipped, so a finite exact-grade use there
must not change the count. A match guard may be evaluated a path-dependent number
of times, so finite exact-grade bindings cannot be observed or replaced in a
guard. Owning borrows inside a guard remain legal because borrowing is not a
consumption.

`return` checks every in-scope exact obligation before transferring control. The
error path of `?` does the same: an exact-grade value that would only be used
after the `?` cannot be left unconsumed on the early error return.

```rust
// accepted: used before the early error path
fn f(x: i64 @[1], r: Result<i64, i64>) -> Result<i64, i64> ! {panic} {
    let y = x;
    let z = r?;
    Ok(y)
}
```

Assignment to a graded mutable binding requires the old value to have met its
exact obligation, then starts a fresh obligation for the replacement value.

## Loops

The iteration count of `while` and `loop` is not known statically, so exact
grades must be restored at every loop head:

- Outer exact-grade counts at a `continue`, a fall-through back-edge, or a
  `while` break must equal their counts at the loop head.
- A `loop` may leave with break-path counts; all breaks must agree.
- A `while` may execute zero times, so its break counts must also equal the
  loop-head counts.
- Bindings declared inside the loop body must satisfy their exact grade on every
  iteration and on every `break`/`continue`.
- Using an outer exact-grade value in a `while` condition is rejected unless the
  condition itself restores the count.

This permits a value to be used and reassigned once per iteration:

```rust
let mut x: i64 @[1] = 0;
let mut i = 0;
while i < n {
    x;        // consume the current value once
    x = i;    // satisfy the old obligation, then start a new @[1] obligation
    i = i + 1;
}
x
```

A `loop` break may consume an outer `@[1]` value exactly once:

```rust
fn take_once(x: i64 @[1]) -> i64 ! {panic} { loop { break x; } }
```

## Abstract grades and specialization

A function may declare a grade parameter:

```rust
fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} {
    x + x + x + x
}

fn main() -> i64 ! {panic} {
    four::<2>(10)      // G = 2, parameter grade @[4]
    // four::<1 + 1>(10) is the same specialization
}
```

Grade parameters can be inferred in the restricted fragment described in
[general grade inference](grade-inference.md). A call or function value outside
that fragment must specialize them explicitly. They are not inferred from the
caller's runtime values, and there is no runtime grade value to inspect. Explicit grade arguments may be natural
literals, `many`, in-scope grade variables, or `+`/`*` expressions over those.
Type and grade parameters may be mixed; the explicit argument list follows
declaration order:

```rust
fn first<T, G: Grade>(x: T @[G], fallback: T) -> T ! {} { x }
first::<i64, 1>(42, 0)
```

The body is checked once per concrete instance. Thus an abstract grade constrains
which specializations are legal rather than trusting an unknown runtime value:
`four::<2>` checks the body at grade 4, while `four::<1>` is rejected because the
body uses its parameter four times. A grade variable may be forwarded from one
generic function to another (`twice::<G>(x)`), and arithmetic in the annotation
(`@[G * 2]`) is evaluated during specialization.

A generic function with a grade parameter that is never specialized has no
executable instance and therefore no checked body. It cannot be called without
explicit specialization, so this is not a runtime trust boundary. Polymorphic
recursion is bounded by the existing 256-instance limit.

A `<N: Nat>` parameter is a compile-time natural for array lengths, not a grade;
`<G: Grade>` is a usage multiplicand; `<e: Effects>` is an effect row (see
[functions.md](functions.md#effect-polymorphism)). They may appear together in
one signature, but none is accepted in another's position. See
[dependent array lengths](dependent-indices.md) for the natural fragment.

## Linear captures and linear-once callables

A closure capturing a linear obligation is a `linear once fn(...)` value. The
capture obligation is transferred to the closure environment and propagated
through construction, return, moves, coercions, matching, and calls:

```rust
let x: i64 @[1] = 41;
let f: linear once fn() -> i64 ! {panic} = fn() -> i64 ! {panic} { x + 1 };
f()                                           // exactly one observation
```

- A copyable `@[1]` capture makes the closure linear-once, and the lambda body
  must observe the capture exactly once. An owning `@[1]` or `#[linear]`
  capture makes the closure linear-once, and the body must consume it exactly
  once on every normal exit.
- An uncalled linear-once closure cannot be implicitly dropped, explicitly
  dropped, widened to an affine `once fn(...)`, or laundered through an
  ungraded local or generic call. A linear-once union alternative makes the
  union linear too.
- A closure capturing `@[0]` or `@[n]` with `n > 1` is rejected: the closure
  may be called zero or one times, so an exact multi-use obligation cannot be
  transferred. Ungraded and `@[many]` copyable captures remain legal.
- Ordinary affine captures still produce ordinary affine `once fn(...)`
  values and keep the existing implicit-drop cleanup on every early exit.

An enclosing operation also retains the obligation of any already-evaluated
linear result. An early `return`, `?`, or exit from an enclosing loop in a later
argument cannot discard a pending linear callee or earlier linear argument.
Finishing a loop wholly inside the argument is allowed: the enclosing operation
still consumes the pending value afterward. Affine values keep ordinary cleanup.

## Interaction with ownership, slices, and proofs

- Affine ownership still runs first. The grade pass checks exact copyable use
  counts and the additional zero/unbounded restrictions; it does not replace
  moves, drop flags, resource slots, or native cleanup.
- `@[1]` on an owning/linear type keeps the existing linear diagnostics and the
  requirement that every normal exit consumes the value. Moving such a value
  into an ungraded local, assignment, constructor, `Box.new`, a wildcard pattern,
  or an ungraded function parameter extends or rejects the obligation instead of
  laundering it. Returning it through an ungraded result of a non-linear type is
  rejected; use an explicit `@[1]` result contract. Value-carrying builtins such
  as `Vec.push` and `Bytes.push` reject a linear argument because their ungraded
  result could be dropped.
- A `linear once fn(...)` is an owning linear value. Its captured obligations
  are checked in the lambda body and its own consumption is checked at every
  use site, including inside unions and through generic calls. Callable
  adapters preserve the linear mode.
- `#[linear]` data propagates linearity through its fields. Grades `0`, `n > 1`,
  and `many` are rejected for such data because they would discard or duplicate
  it.
- Immutable `&[T]` slice views and immutable `&Box`/`&Bytes`/`&Vec` borrows keep
  their existing lexical lifetime rules. A borrow is an observation, not a
  consumption, so one borrow plus one move can satisfy `@[1]`. Passing a borrow
  to a higher-demand parameter duplicates only the shared reference, never the
  owner. Reads through a view are uses of the view, not additional uses of the
  owner binding; slice/view construction over owning elements is already
  rejected, so this alias boundary cannot duplicate storage.
- Erased parameters and logical proof terms are unchanged and are not assigned
  grades. This includes `prop` propositions and their proofs. A grade zero
  binding is not a proof and does not enter the kernel. A proof cannot hide a
  graded or owning runtime resource: erased types may admit only immutable
  machine scalars as symbolic indices, never owning or graded resources, so the
  resource obligations of the surrounding executable code are unchanged. Naming
  a `@[0]` scalar in an erased proof type is a compile-time, erased observation
  and does not become a runtime use.

## Diagnostics and resource budgets

Diagnostics name the binding, its grade, the observed count, and the control-flow
reason. Examples include:

```text
a value graded @[2] is used a different number of times on different paths in an if/else
a value graded @[1] is not used consistently before this return
a value graded @[2] is not used consistently before the end of this loop iteration
a value graded @[0] is not used consistently before the function returns; grade @[0] forbids runtime observation
```

Budgets are explicit: grade expressions have a 128-node evaluation budget and
64-bit overflow checks; each function has a 1,000,000-step grade-analysis budget;
function instances retain the existing 256 limit. Exceeding a budget is a
diagnostic, never an assumption that the obligation holds.

## Examples and tests

- `examples/grades.kush` combines a natural grade, an abstract grade, and a
  zero-use binding.
- `examples/linear-resources.kush` is a runnable linear-resource factory,
  annotated identity, static trait and method contracts, a graded arrow value,
  a linear-once capture, and a loop-carried resource.
- `examples/effectful-functions.kush` includes a linear-once closure consuming
  a `Box<i64> @[1]` capture.
- `crates/kush/tests/grades.rs` covers arithmetic grades, specialization,
  ownership/linearity conflicts, branch and short-circuit mismatches, early
  returns and `?`, loop multiplicity, call composition, linear-once capture
  transfer and laundering failures, and native/reference agreement.
- `crates/kush/tests/linear_resources.rs` covers `@[1]` factories, alias and
  generic identity, unsupported result grades, ungraded-return rejection,
  caller consumption, graded arrows and lambda results, trait/method contracts,
  closure captures, loop back-edges and break results, `?` payloads, aggregates
  and destructuring, pending early exits, task rejection, checked reuse, and
  native/reference allocation balance.
- Existing `@[1]` and `#[linear]` tests remain passing. The former
  affine-result tests were tightened to their graded positive and explicit
  negative replacements.

## Remaining research and implementation gaps

This is deliberately a restricted, usable interface. It does not claim perfect
memory management or a complete formal soundness proof. Still missing or
deferred:

- User-defined finite grade algebras with explicit carriers and operation
  tables are implemented and law-checked by enumeration; see
  [grade algebras](grade-algebras.md). Non-finite carriers and custom
  comparison/join structures beyond that semiring are still missing.
- General graded modality introduction/elimination beyond binding, parameter,
  and result grades.
- A principal grade solver. The implemented solver handles a single-occurrence
  affine fragment from explicitly graded arguments and expected arrows; all
  other abstract grades still require explicit specialization. See
  [general grade inference](grade-inference.md).
- Result grades beyond the implemented `@[1]` owning/intrinsic-linear and
  copyable must-use subsets: general inference, custom algebras, or
  unrestricted grade polymorphism; and grade-zero result erasure.
- General dependent grade indices, grades mentioning runtime values, and
  erasure/relevance interaction with graded dependent types.
- Full dependent algebraic subtyping combined with grades, general borrowed-return
  grades, and grade-polymorphic traits or function values. The executable value
  fragment (including owning unions and callable alternatives) is described in
  [subtyping.md](subtyping.md).
- A machine-checked soundness proof for the combination of grades, affine
  ownership, dependent erasure, effect polymorphism, and subtyping.
- Automatic cleanup of a linear result when a task or cancellation path would
  otherwise discard it. Task results that would transfer a `@[1]` or
  binding-based linear obligation stay rejected.
- Actual runtime erasure of grade-zero storage. Grade zero currently restricts
  observations; the initializer is still evaluated and the slot may still be
  allocated on the stack.
- A precise effect-sensitive accounting for side-effecting argument blocks. The
  current multiplicative rule is conservative.
- Loop analyses stronger than "restore the loop-head count" or "all breaks
  agree", such as proving a loop runs exactly once or a fixed number of times.

### Loop-carried owning obligations

A repeating path must preserve both availability and the linear obligations at
its loop head. Assigning a new linear owner into an outer affine (or previously
unavailable) binding before a back-edge is rejected: checking only the first
iteration would allow that owner to be discarded on the next one. Declare the
outer binding `@[1]` before entering the loop and consume/reinitialize it on each
iteration, or consume the replacement before repeating. A guaranteed `break`
does not repeat and can transfer the replacement out of the loop.

### Returns nested in evaluated expressions

The result-transfer scan visits conditions, match scrutinees and guards, loop
conditions, `?` operands, nested `return` operands and task operands as well as
ordinary arguments and block tails. An early return from any of those positions
must retain its linear result contract. Regressions pair rejected ungraded
factories with accepted explicitly graded versions of the same control flow.

Final root validation passes 618 workspace tests, formatting and Clippy on
Boat. Three additional regression tests cover hidden control-flow returns,
returns inside `?` operands and later assignments that must not erase an
earlier return obligation.
