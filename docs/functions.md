# First-class functions and closures

Status: implemented for the executable value fragment. Named functions,
explicit generic specializations, effect-polymorphic higher-order functions
and function types, explicitly typed noncapturing lambdas, owning capturing
closures (including a linear-once mode), scoped borrowed-capture once closures,
function-typed parameters/results/locals, indirect calls, checked arrow
subtyping, callable union alternatives, and checked adapters all execute in both
the reference evaluator and the native Cranelift backend. This is a usable
interface, not a claim of the full dependent/effect-polymorphic function
calculus in the [v0.1 design](spec-v0.1.md#9-effects-and-purity).

```sh
cargo run -p kush -- check examples/functions.kush
cargo run -p kush -- eval examples/functions.kush
cargo run -p kush -- run examples/functions.kush
cargo run -p kush -- run examples/effectful-functions.kush
```

The first example prints `42` on eight lines. The effectful example prints
`42` on nine lines and exercises inferred and explicit effect rows, callable
unions, and linear-once closures.

## Function types

```rust
fn(i64, i64) -> i64 ! {panic}
fn(i64 @[2]) -> i64 ! {panic}
once fn(i64) -> i64 ! {alloc, panic}
linear once fn(i64) -> i64 ! {panic}
type Unary = fn(i64) -> i64 ! {panic};
type Mapper<e: Effects> = fn(i64) -> i64 ! {e};
```

- `fn(...)` is a copyable, noncapturing function pointer. It has no heap
  environment and costs one word at runtime.
- `once fn(...)` is an owning callable with an optional captured environment.
  It is consumed by a call and is normally dropped when it is not called. Its
  representation is a code pointer plus an owned environment pointer (two
  words).
- `linear once fn(...)` (also accepted as `once linear fn(...)`) is a distinct
  linear-once callable mode. It has the same two-word representation, but the
  value itself is a linear obligation: it must be consumed by exactly one call
  (or moved into a return/pass that transfers the obligation). It may not be
  implicitly or explicitly dropped, and it may not be widened to an affine
  `once fn(...)`.
- Parameter effects and usage grades are part of the arrow type. A call
  requires the callee's declared effects, and an argument is evaluated under
  the callee parameter's usage demand.
- Function arrow types may borrow slice views under their own lifetime
  binders, as in `fn<'a>(&'a [T]) -> &'a [T]` or the elided
  `fn(&[T]) -> i64`; see
  [lifetime-aware callable types](lifetimes.md#lifetime-aware-callable-types).
  They cannot spell borrowed references to owners or lifetime-parameterized
  borrowed or mixed records: a callable carrying a record field lifetime would
  erase the per-field provenance the direct-call checker maintains. Borrowed
  parameters such as `fn(&Bytes) -> i64` are accepted; the borrow is supplied
  by each call.
- Function values are heterogeneous union alternatives when their normalized
  signatures are distinct. See [callable unions](#callable-union-alternatives)
  below.

## Effect polymorphism

A function may quantify over an effect row with `<e: Effects>`:

```rust
fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
    f(x)
}

fn twice<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
    f(f(x))
}
```

- `e` is a row variable, not a type, grade, or natural const parameter. The
  generic categories remain separate; `::<...>` arguments are interpreted by
  declared category and may not be supplied in another category's position.
- The supported effect names are `panic`, `io`, `alloc`, and `suspend`.
  Suspension propagates through direct calls, indirect calls, and instantiated
  rows exactly like the other effects; `#[nosuspend]` rejects a reachable
  suspension or an unconstrained row variable.
- A row is the union of fixed effect names and row variables: `! {e}`,
  `! {io, e}`, `! {io | e}` are equivalent spellings.
- An effect row is inferred from a callable argument when exactly one
  unbound row variable occurs in the callee parameter type. For example
  `apply(inc, 41)` instantiates `e = {panic}` and `apply(io_inc, 41)`
  instantiates `e = {io, panic}`. If several row variables are unbound, or the
  row is not mentioned by any callable argument, the call is rejected with a
  request for explicit specialization.
- Explicit effect specialization uses an effect expression:
  `apply::<io | panic>(io_inc, 41)`. A type or grade argument in an effect
  slot (or an effect name in a type/grade slot) is rejected.
- The instantiated row is part of the callable's signature and propagates
  transitively: a polymorphic caller cannot hide an effect required by a
  callee. A function value inferred from an expected arrow type also infers a
  single row variable from that arrow's effect row.
- `#[noalloc]` remains a specialization-independent contract. A `#[noalloc]`
  function may take and call non-allocating function values, but its own effect
  row may not contain an unconstrained row variable, because that variable
  could later be specialized with `alloc`. Concrete effect rows and checked
  adapters enforce the same rule for `nosuspend`/allocation boundaries. An
  effect variable used only inside a parameter arrow cannot make a body
  allocate: calling it requires the instantiated row, so an `alloc`
  instantiation fails the body check unless the function's own row exposes it.

## Callable union alternatives

Distinct callable signatures may be alternatives of a heterogeneous union:

```rust
let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
let g: i64 | once fn(i64) -> i64 ! {panic} = inc;
```

- Normalization is the same as for other alternatives. Two callable
  alternatives that are subtype-related absorb; distinct but mutually subtype
  arrows (for example an unannotated and a `@[many]` parameter grade) normalize
  to one deterministic representative rather than both disappearing into
  `Never`. The representative prefers the more permissive unannotated grade
  contract, so canonicalization does not invent an exact-use demand.
- `fn(...)` is a subtype of `once fn(...)`, so a union mentioning both
  normalizes to the once alternative. Injecting a pure function pointer into a
  once alternative synthesizes a no-allocation null-environment thunk; the raw
  payload is never reinterpreted with the once calling convention.
- `inject`, `repack`, and type-pattern narrowing are coherent and
  deterministic. A union-to-union repack may copy a callable payload only when
  the calling convention and every parameter/result representation agree. A
  repack that would change the callable ABI is rejected explicitly; bind and
  adapt the value as an explicit `once fn` first.
- Narrowing uses a type pattern such as
  `fn(i64) -> i64 ! {panic} @ h => h(41)`. The binder has the narrowed callable
  type and the existing per-signature indirect-call ABI.
- A union is owning if any alternative owns storage and linear if any
  alternative is linear. Dropping a union dispatches on the active tag, so an
  uncalled once closure releases only its own environment. A union containing a
  linear-once alternative is itself linear and must be consumed.

## Named functions and explicit specialization

A function name used in value position becomes a function value:

```rust
fn inc(x: i64) -> i64 ! {panic} { x + 1 }

fn apply(f: fn(i64) -> i64 ! {panic}, x: i64) -> i64 ! {panic} {
    f(x)
}

fn id<T>(x: T) -> T ! {panic} { x }

fn main() -> i64 ! {panic} {
    apply(inc, 41) + apply(id::<i64>, 42) - 42
}
```

A generic function value may be specialized explicitly with `::<...>` or
inferred from an expected arrow type (`apply(id, 42)` above). Inference through
a function-valued parameter also works because `fn(T) -> U` mentions `T` and
`U`. A single effect row variable may also be inferred from the expected
arrow's effect row; multiple row variables or usage-grade parameters still
require explicit specialization.

Functions with erased proof parameters cannot become first-class values: an
indirect call would bypass the proof obligation. Call those functions directly
so the kernel evidence is checked at the call site. Generic functions with
abstract usage grades likewise require explicit specialization.

## Lambdas

A fully annotated lambda:

```rust
let double = fn(x: i64) -> i64 ! {panic} { x * 2 };
let f: fn(i64) -> i64 ! {panic} = double;
```

### Lambda annotation inference

Parameter types, the result type and the effect row of a lambda may be
omitted (I-LAMBDA-INFER, [inference prototype](inference-prototype.md)
decisions 3-4). Inference is local and never inserts a coercion:

```rust
fn apply<T, e: Effects>(f: fn(T) -> T ! {e}, x: T) -> T ! {e} { f(x) }

apply(fn(x) { x * 2 }, 21)            // x: i64 from 21, row {panic} from the body
let double = fn(x) { x * 2 };         // fixed by the first use below
apply(double, 21)
let g: fn(i64) -> i64 ! {panic} = fn(x) { x + 1 };
let h = fn(x: i64) { x + 1 };         // result i64 and row {panic} from the body
```

- **Parameters** come from, in order: the expected arrow type (an annotated
  `let`, a typed parameter, a return position); for a generic call, the other
  arguments, because an unannotated noncapturing lambda argument is checked
  after them (evaluation order is unchanged); for `let f = fn(..) {..}`
  without annotation, the binding's first use: a call `f(a, b)` whose
  arguments are literals or locals declared before the `let`, an argument
  position `g(.., f, ..)` whose declared parameter is an arrow (a generic one
  resolved only through arguments declared as that bare type parameter), or
  `let h: T = f`. The search for the first use is bounded (10,000 nodes,
  depth 256); exhausting it asks for the annotation.
- **Result**: the expected or hinted result; otherwise the body's type. It is
  never a union (no implicit union coercion), never `Never`, never borrowed or
  a task handle, and a body using `return` needs the annotation.
- **Row**: the union of the effects the body requires, the minimal row; a
  coercion to a wider expected row is ordinary arrow subtyping. A body that
  handles or performs takes its row from the expected arrow or needs `! {..}`.
- Inferred parameters are **ungraded** and never borrowed, slice, reference or
  task types: graded, borrowed and owning-versus-borrowed choices stay with the
  annotation (an owning type is accepted only when the use site fixes it).
- Anything else is a diagnostic naming the missing annotation. Annotated
  lambdas are unchanged, and no previously accepted program changes meaning:
  all of these forms were parse errors before.

Corpus (`lambda_corpus_tests`): every lambda in `examples/*.kush` (25) with
all of its annotations removed. 22 are inferred and the program's result and
output are unchanged; 3 ask for an annotation (two have no use site that
fixes a parameter, one would need a borrowed `&[i64]` parameter). Limits:
only noncapturing lambda arguments of generic calls are postponed, first-use
arguments must be literals or earlier locals, and borrowed, graded or union
types always need the annotation.

A lambda that captures no outer runtime binding is a copyable `fn(...)` value
and never allocates.

A noncapturing lambda may return a shared or exclusive slice borrowed from its
single slice parameter. Its result lifetime is elided from that parameter and
preserved through function values and higher-order calls:

```rust
let tail = fn(v: &[i64]) -> &[i64] ! {panic} { &v[1..] };
let identity = fn(v: &mut [i64]) -> &mut [i64] ! {} { v };
```

An exclusive result requires an exclusive input. Returning a local owner's view
is rejected. Capturing slice-returning lambdas, multiple slice inputs, and
explicit lambda lifetime annotations remain rejected; use named functions with
explicit lifetime binders for those signatures. Borrowed records and text-view
results remain outside this lambda subset.

A lambda that captures affine owned storage is an owning `once fn(...)` value:

```rust
let n = Box.new(41);
let add = fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
add(1);
```

Captured values are moved exactly once into the closure environment. They are
not duplicated, and the environment is released on:

- a normal call (the callee takes ownership of the captures);
- dropping an affine closure without calling it;
- `return`, `?`, `break`, or an early exit while an affine closure is live;
- a failed/partial argument evaluation that abandons the call.

Capturing an immutable `&[T]` or exclusive `&mut [T]` slice view creates a
**scoped borrowed-capture** `once fn(...)`. The environment stores the view
descriptor; it points at the original array cell or `Vec`/`Bytes` storage and
never owns or copies that storage. The closure must be constructed directly in
a `let` initializer or called immediately, and the local may only be called or
implicitly dropped in the same lexical scope:

```rust
fn main() -> i64 ! {alloc, panic} {
    let mut values: [i64; 3] = [1, 2, 3];
    let view: &mut [i64] = &mut values[..];
    let bump = fn(by: i64) -> Unit ! {panic} {
        Slice.set(view, 0, Slice.get(view, 0) + by);
    };
    bump(41);
    values[0] // the call releases the mutable loan
}
```

Capturing a mutable view moves the capability into the closure; capturing a
shared view adds another shared alias. Owners, ancestors, and parent views stay
suspended exactly while the closure is live and callable, and the loan ends at
its checked last call or scope end. Checked split siblings can be captured by
two separate closures and remain disjoint. A borrowed-capture closure cannot be
moved to another binding, returned, stored in data or a box, passed to another
function, adapted to a union or other function type, or captured by a task. See
[borrowing and lifetimes](lifetimes.md#scoped-borrowed-closure-captures).

A mutable scalar local (`i64`, another fixed-width integer, `f32`/`f64`,
`Char`, `Bool`, or `Unit`) is captured **by reference**. The environment stores
the address of the caller's binding rather than a copy; a write in the lambda
updates that binding, and a later call observes the current value. These
captures are call-scoped like borrowed views: the closure may only be built as
a direct `let` initializer or called immediately, and the location stays
loaned until the closure's checked last call or lexical scope end. A lambda
that assigns the capture holds an exclusive loan: the caller cannot read,
assign, move, or drop the location while the closure is live. A lambda that
only reads it holds a shared loan, so unrelated reads remain allowed but a
write is rejected. The same restrictions reject returning the closure, storing
it in outliving data, passing it to another function, or sending it to a task.
Both backends implement the pointer representation, so reference evaluation and
native execution agree. Calling a closure that writes the capture invalidates
erased proof facts about its old value; a call to a read-only closure leaves
the established version intact. Write summaries also apply to immediate
`Task.scope` callbacks and effect handlers, including resumed continuations.
Loop headers discard facts for locations that a callable the loop may execute
can write, even before the first checked iteration; merely constructing a
closure leaves those facts intact, and calls to callables the loop cannot
resolve stay conservative. Each captured location has its own
loan mutability: writing one capture leaves read-only captures shared. See
[runtime scalar indices](runtime-indices.md#4-freezing-mutation-and-joins).

A closure that captures a linear `@[1]`/`#[linear]` obligation (or a copyable
value graded `@[1]`) is a `linear once fn(...)` value. Linearity is
propagated, not erased:

```rust
fn main() -> i64 ! {alloc, panic} {
    let n: Box<i64> @[1] = Box.new(20);
    let f: linear once fn(i64) -> i64 ! {panic} =
        fn(x: i64) -> i64 ! {panic} { Box.take(n) + x + 1 };
    f(21)                                  // 42
}
```

- Constructing the closure moves the obligation into its environment.
  Returning, moving, coercing, matching, and passing the closure preserve it.
- The lambda body must consume every linear capture exactly once on every
  normal exit, just like an ordinary linear parameter. Calling the closure
  consumes the captures exactly once.
- An uncalled linear-once closure cannot be implicitly dropped, explicitly
  dropped, widened to an affine `once fn(...)`, or laundered through an
  ungraded local/generic call. The local and any returned value keep the
  linear-once type.
- A callable adapter that changes a callable's parameter/result representation
  preserves the linear mode. A pure-adapter/once-thunk conversion from `fn`
  adds only a null environment and still must be consumed exactly once at a
  linear-once target.
- Capturing a copyable `@[2]`/`@[n>1]` or `@[0]` value is rejected: a closure
  may be called zero or one times, so its exact grade obligation cannot be
  transferred. Ungraded and `@[many]` copyable captures remain allowed.

Creating a capturing closure allocates its environment and therefore requires
`alloc` and `panic`. A `#[noalloc]` function rejects capturing closures and
capturing adapters. Pure function pointers and noncapturing adapters allocate
nothing and remain legal in `noalloc` code.

A linear callee must also be consumed when evaluating a call. An argument that
returns, propagates `?`, or exits an enclosing loop before the call happens
cannot silently discard an already-evaluated linear callee or earlier linear
argument. Ordinary affine callees are cleaned up on these paths. A loop wholly
inside an argument may still break or continue normally: it does not abandon
the enclosing call.

## Arrow subtyping

Function types use the usual arrow variance:

```text
fn(P2) -> R1 ! {e1}  <:  fn(P1) -> R2 ! {e2}
when P1 <: P2, R1 <: R2, e1 subset-of e2, and the usage contracts agree
```

- Parameters are contravariant; results are covariant.
- Effects are an included row, including a row variable after instantiation. A
  pure callee may be used where a wider effect row is allowed. An
  allocating/effectful callee may never hide behind a pure arrow type.
- `fn(...)` may be used as `once fn(...)` because a copyable, noncapturing
  callable is safe to consume once. The reverse direction is rejected.
- A `linear once fn(...)` may only be used where a linear-once arrow is
  expected (or as an adapted linear-once target); it may not be widened to an
  affine `once fn(...)`. An affine callable may be used at a linear-once target
  because the caller then promises to consume it exactly once.
- Parameter grades must agree exactly for a finite contract; a target with
  `@[many]` or no annotation accepts any source demand. A source that uses a
  parameter twice may not be disguised as `@[1]`, and an ungraded source may
  not promise an exact `@[1]` contract.
- Union domains/results participate through the same subtype relation. For
  example a source accepting `i64 | Bool | Bytes` may be used where the caller
  only promises `i64 | Bool`; the smaller union is repacked into the larger one
  by a checked adapter.

## Safe adapters

When a subtype conversion changes an argument or result representation, the
checker synthesizes a checked adapter function. It is ordinary generated IR,
never a function-pointer cast:

- **Static pure source:** a noncapturing adapter applies the existing `Inject`
  or `Repack` coercions to arguments and the result. It allocates nothing and
  is legal under `#[noalloc]`.
- **Static pure source used as `once fn`:** a no-allocation thunk ignores the
  null once-environment and directly calls the source.
- **Dynamic `once fn` source:** a once-consuming capturing adapter owns the
  source callable and releases it after the call. This allocates and therefore
  requires `alloc`/`panic`.
- **Linear-once source or target:** the adapter preserves the linear mode, so
  the result must still be consumed by exactly one call. A linear-once source
  cannot be adapted to an affine once target.
- **Callable union repacking:** a payload may be copied only when the callable
  calling convention and parameter/result representations agree. Injecting a
  pure `fn` atom into a once union alternative is adapted through a null-env
  thunk; a union-to-union repack that would change the ABI is rejected
  explicitly instead of copying raw words.
- **Dynamic pure source with a representation-changing `fn` target:**
  rejected. A capture-free adapter cannot exist without a place to store the
  dynamic source; the diagnostic asks for an explicit `once fn` type or a
  direct function name.
- If an adapter body itself needs to create a capturing adapter (a nested
  function-typed argument/result conversion), the target arrow effect row must
  include `alloc` and `panic`; otherwise the conversion is rejected rather than
  hiding allocation behind a pure signature.

Adapters compose, so a parameter or result that is itself a function type is
converted by the same checked rules.

## Runtime and backend

- Reference evaluation stores a callable as a function index plus an optional
  owned closure environment. A call with an environment moves the captured
  values into the callee frame; normal cleanup drops whatever remains.
- Native lowering uses a code pointer plus an environment pointer. A capturing
  function's prologue loads the captures into ordinary ownership-tracked locals
  and frees the environment cell. Environment headers store a generated drop
  function, so dropping an uncalled closure releases exactly its captured
  values without GC or reference counting.
- Indirect calls use a per-signature Cranelift `call_indirect`. Aggregate
  results use the same caller-owned return buffer as direct calls, so native
  and reference execution agree on records, enums, boxes, and vectors crossing
  a function-value boundary.
- A linear-once callable uses the same two-word calling convention and
  environment drop header as an affine once closure; linearity is a static
  obligation, not an extra runtime tag. Callable union alternatives store the
  code pointer (one word) or code pointer plus environment (two words) behind
  the union discriminator.
- Function instances, including lambdas, adapters, and thunks, share the
  existing 256-instance budget. Function parameters/results count toward the
  existing word-layout limits; there is no limit on parameter words.

## Examples and tests

- `examples/functions.kush` combines named values, a generic higher-order
  `apply`, a specialized generic value, a union-domain adapter, a generic
  `map` over `Vec`, a returned once closure, and a capturing owner.
- `examples/borrowed-closures.kush` exercises scoped immutable and mutable
  view captures, post-call release, split-side closures, and loop reuse.
- `examples/effectful-functions.kush` exercises inferred and explicit effect
  rows, an effect-polymorphic function type alias, transitive propagation,
  callable union alternatives, active-alternative once cleanup, and a
  linear-once closure.
- `crates/kush/tests/functions.rs` covers effect and grade variance, effect
  inference/specialization and category separation, `noalloc` higher-order
  contracts, callable union normalization/injection/repacking/narrowing,
  scoped borrowed-capture rejection/acceptance, canonical arrow equivalences, linear-once consumption and laundering
  failures, parameter and result union repacking, generic specialized values,
  indirect recursion, aggregate and owned arguments/results, early exits and
  partial arguments, captured owners, use-after-move, wrong signatures,
  pure/`noalloc` violations, erased-evidence rejection, and native/reference
  agreement.
- `crates/kush/tests/grades.rs` covers copyable `@[1]` capture transfer and
  rejection of exact `@[0]`/`@[n>1]` captures.
- `examples/reuse.kush` and `crates/kush/tests/reuse.rs` use first-class
  noncapturing callbacks with `Vec.map_in_place`, including effect-row
  propagation, grade contracts, once/linear callback rejection, owning element
  transfer, width-changing layouts, and conservative pure-map fusion. See
  [checked reuse and allocation diagnostics](reuse.md).

## Remaining boundaries

- Effect rows are first-order finite Boolean expressions over the four concrete
  effects. Declared rows may union and subtract row variables (`{e - io}`), and
  a finite solver accumulates inclusion constraints over every higher-order
  argument. There is no general row unification, row aliasing, or principal
  inference for an unconstrained open row. A bounded binder
  `<e: Effects - alloc>` restricts which concrete rows may specialize a
  function or method. Lexical one-shot effect handlers are implemented in the
  restricted fragment described in [effect-handlers.md](effect-handlers.md),
  including real non-tail resumption for a single top-level perform. There is
  still no surface literal for the empty row in an explicit specialization; a
  pure callable argument infers it.
- No function intersections with a synthesized common callable. Identical
  function types intersect to themselves; mutually subtype arrows keep one
  deterministic representative; subtype-related arrows obey absorption.
  Incomparable callable intersections remain explicit diagnostics.
- Scoped borrowed-capture `once fn(...)` closures are supported for borrowed
  slice views and mutable scalar locations. Arrow types describe borrows of
  their arguments, not of captured locations, so a borrowed capture still
  cannot be returned, stored, passed to an ordinary helper, adapted, or
  captured by a task; those escapes are rejected explicitly rather than erased.
  Lambdas may take slice parameters but cannot return slices yet; a
  slice-returning function value must be a named function.
- No union-to-union repack that changes a callable's calling convention or
  argument/result representation. Bind/adapt the value as an explicit
  `once fn` first.
- No dynamic pure `fn` to representation-changing pure `fn` adapter; use a
  direct function name or an explicit `once fn` value.
- Result-transfer contracts are limited to exactly `@[1]` on owning or
  intrinsically linear results. A graded result is threaded through named and
  generic functions, typed lambdas, callable arrow types, static trait/method
  contracts, indirect calls, and checked adapters; arrow subtyping requires an
  exact result-grade match. There is no result-grade inference, no general
  grade-polymorphic function value, and no copyable-result transfer. Abstract
  grade parameters still require explicit specialization.
- The ABI is private and unstable, as with the rest of the executable subset.

### Capture provenance

Capture linearity includes obligations propagated through local moves,
assignment, owning destructuring, constructors, loop results, `?`, and unboxing.
It is determined before selecting the closure signature and checking synthetic
capture locals. The ownership pass independently checks it afterward; an affine
closure cannot hide a still-linear captured binding. Recursive type graphs are
walked as finite graphs when determining intrinsic linearity.
