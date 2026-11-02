# Static traits and user-defined methods

This page is the authoritative description of the implemented trait and method
subset. Static calls are monomorphized. `dyn Trait` has two checked
representations: a finite closed-world union for traits whose member set is
closed and never appears in a nominal field, and a dynamically dispatched
fat object for open/generic member sets and for any trait used inside a nominal
field. Both support owned, shared, and mutable dispatch and stored borrowed
forms. The dynamic form carries a member identifier and an owned payload
pointer, with a compile-time-registered method table per concrete member; the
value layout never enumerates the trait's members. This is still a closed
program analysis with checked object safety, not an FFI-compatible vtable or a
general open-world typeclass system.

```sh
cargo run -p kush -- run examples/traits.kush
# 6, 18, 42, 71, 3 on separate lines
```

The example runs in the reference evaluator and in the Cranelift native
backend. `crates/kush/tests/traits.rs` compares both.

```sh
cargo run -p kush -- run examples/generic_traits.kush
# 42, 1, 23, 5, 3 on separate lines
```

`crates/kush/tests/generic_traits.rs` covers the generic subset described
below, again in both backends.

## Declaration syntax

An inherent method is declared in an `impl Type { ... }` block. A trait method
requires a trait declaration and an explicit `impl Trait for Type { ... }`
block. Every method declares a receiver as its first parameter named `self`.
The examples below use value receivers; call-scoped `&self` and `&mut self`
record receivers are described in the borrowing section:

```kush
struct Point { x: i64, y: i64 }

impl Point {
    fn sum(self: Point) -> i64 ! {panic} {
        self.x + self.y
    }

    fn scale(self: Point, factor: i64) -> Point ! {panic} {
        Point { x: self.x * factor, y: self.y * factor }
    }
}

trait Describe {
    fn describe(self: Self) -> i64 ! {panic};
}

impl Describe for Point {
    fn describe(self: Self) -> i64 ! {panic} {
        self.x * 10 + self.y
    }
}
```

`Self` is the impl target. A value receiver in a trait is written `self: Self`;
an impl may write `self: Self` or the concrete target type. Borrowed record
receivers may use `self: &Self`, `self: &mut Self`, `&self` or `&mut self`,
with the receiver mode matched by the implementation. The
receiver is the first parameter and is removed from the caller's argument list:
`point.describe()` passes one value.

Trait parameters select a specialization; they are static identity, not runtime
values. A trait may take ordinary type parameters, compile-time `Nat` indices,
and `Grade` parameters:

```kush
trait Convert<T> {
    fn render(self: Self) -> T ! {panic};
}

impl Convert<i64> for Point {
    fn render(self: Self) -> i64 ! {panic} { self.x * 10 + self.y }
}

impl Convert<Bool> for Point {
    fn render(self: Self) -> Bool ! {panic} { self.x == 0 }
}
```

`Point` therefore implements `Convert<i64>` and `Convert<Bool>` independently.
The impl signature is compared after substituting the trait arguments into the
trait method, so the impl writes `i64` (or the corresponding concrete type),
not the trait's parameter name. Generic impl headers are supported for ordinary
type parameters and compile-time `Nat` and `Grade` parameters, including
`impl<T> Show for Wrapper<T>`, `impl<N: Nat> First for Buffer<N>`, and
`impl<G: Grade> Weighted<G> for Point`; bounded blanket impls such as
`impl<T: Show> Loud for Box<T>` are supported for type parameters.
Lifetime-parameterized and effect-parameterized impl headers remain rejected.
See [generic and blanket impls](#generic-and-blanket-impls). A concrete generic
nominal target such as `impl First<i64> for Pair<i64>` is supported like any
other concrete target.

Methods themselves may also be generic, in both traits and impls:

```kush
trait Pairing<T> {
    fn pair<U>(self: Self, value: U) -> (T, U) ! {};
}

impl Pairing<i64> for Point {
    fn pair<V>(self: Self, value: V) -> (i64, V) ! {} { (self.x, value) }
}
```

Type, grade, natural, and effect parameters on methods use the same
monomorphization as generic free functions. Calls may infer them from the
arguments and expected result, or write them explicitly:

```kush
let by_inference = point.Pairing::<i64>.pair(true);
let explicit = point.pair::<i64>(7);
```

Trait declarations end a signature-only method with `;`. A method written with
a block is a **default body** that an impl inherits when it omits the method;
see [default method bodies](#default-method-bodies). Associated type and
constant declarations are supported; see [associated
items](#associated-types-and-constants). Effect-row trait parameters are
rejected with an explicit diagnostic. Trait parameters may not themselves
carry trait bounds; put the bound on the function type parameter that uses the
trait. A method parameter may not reuse a trait parameter's name, which would
make substitution ambiguous. `impl Trait` in type position and a trait name used
as a runtime type are rejected. `dyn Trait` is a checked trait object; see
[trait objects](#trait-objects-closed-unions-and-open-dynamic-objects).

## Static dispatch and call lowering

A method call `receiver.name(arguments...)` is checked as follows:

1. The receiver is checked exactly once, before the arguments.
2. If the receiver is a record with a field named `name`, ordinary field
   projection wins and the field is called through the existing callable path.
   An impl is rejected at declaration time if a method name collides with a
   record field, so a method can never become unreachable through this rule.
3. Otherwise an inherent method is preferred.
4. Otherwise exactly one trait method for the concrete receiver type is used.
   With several traits providing the same name, the call is an ambiguity error.
5. No method found is an error naming the receiver type.

The user-defined call lowers to the same `Target::Function` call node as an
ordinary function call, with the checked receiver as argument zero. Static
dispatch adds no vtable, trait value, function pointer, or runtime allocation.
Trait-object dispatch uses a checked closed-world union matcher or a fixed
dynamic member table instead; see
[trait objects](#trait-objects-closed-unions-and-open-dynamic-objects). Receiver evaluation order,
argument order, coercions, erased-proof discharge, effects, grades, and
ownership are the ordinary call rules.

### Default method bodies

A trait method may declare a body instead of ending in `;`:

```kush
trait Scaled {
    fn base(self: Self) -> i64 ! {panic};

    fn scaled(self: Self, factor: i64) -> i64 ! {panic} {
        self.base() * factor
    }
}

struct Point { x: i64 }
impl Scaled for Point {
    fn base(self: Self) -> i64 ! {panic} { self.x + 1 }
    // `scaled` is inherited.
}
```

An impl that omits a default method **inherits** it. The checker materializes
one fresh checked function for each `(impl, method)` pair:

- `Self` is replaced by the concrete impl target everywhere in the default
  signature and body, including parameters, the result, and nested types.
- The trait's type, `Nat`, `Grade`, and effect arguments are substituted into
  the default signature and body, exactly as in the trait's own method
  signatures. For example, `Wrap<i64>::wrapped` sees `T = i64`.
- A default body is checked only when some impl inherits it. Its declared
  effects, grades, erasure markers, lifetimes, and ownership rules are checked
  per specialization, so an inherited default that uses unchecked arithmetic is
  rejected even though the trait declaration itself has no body check.
- The body is checked in the module that declares the trait, which is where its
  free names were resolved. A private helper of the trait's module therefore
  stays callable from the default body even when the impl lives in another
  module; a private helper of the impl's module could not have been named in the
  body anyway.
- An inherited default is registered in the same method tables as an explicit
  impl method. It participates in unqualified dispatch, explicit
  `receiver.Trait.method(...)` qualification, generic-trait ambiguity, and
  visibility checks like any other method.
- An inherited default whose name collides with a record field of the impl
  target is rejected when the impl is registered, because field projection
  would make the method unreachable. Reserved builtin method names are already
  rejected on the trait declaration.

An impl may override a default. The override is still compared with the trait
signature by the exact contract rules below, so an override cannot weaken an
effect, drop a grade, change the receiver mode, or change the result. An
override replaces the default for that impl; trait-level specialization is a
separate, explicitly checked relationship between impl headers.

Inside a materialized default body, an unqualified method call on `Self`
prefers the enclosing trait specialization (for a non-generic trait, the
enclosing trait itself). Without this rule a generic trait implemented at
several specializations could not call a sibling default method
(`self.value()`) without repeating the qualification. Any remaining ambiguity
is still an error. Calls on other receiver types are unaffected.

An impl block may be empty when every method it would need is a default:
`impl Show for Marker { }`. A trait method declared with `;` still requires an
explicit impl, and omitting it is an error even when other methods have
defaults.

Default bodies are not a new runtime mechanism. They lower to ordinary checked
functions and ordinary `Target::Function` calls, so the reference evaluator and
the native backend agree without a vtable, trait value, or extra allocation.

### Explicit disambiguation

`receiver.Trait.method(arguments...)` selects one trait's method. This is the
explicit spelling for a method name provided by several traits:

```kush
trait First { fn value(self: Self) -> i64 ! {}; }
trait Second { fn value(self: Self) -> i64 ! {}; }

impl First for Point { fn value(self: Self) -> i64 ! {} { self.x + 10 } }
impl Second for Point { fn value(self: Self) -> i64 ! {} { self.x + 20 } }

let a = point.First.value();
let b = point.Second.value();
```

The `point.First` selector is checker-only; it is not a runtime field access.

For a generic trait, put the specialization arguments in the same selector with
the ordinary `::<...>` spelling:

```kush
let value = point.Convert::<i64>.render();
let flag = point.Convert::<Bool>.render();
```

An unqualified call is ambiguous when the receiver implements several
specializations that provide the method, and the diagnostic lists the
specializations. A bare `point.Convert.render()` on a generic trait is rejected
with an error asking for `point.Convert::<...>.render()`. A generic method's own
arguments are written after the method name, so
`point.Convert::<i64>.render::<...>()` distinguishes the trait specialization
from the method specialization.

### Builtin precedence and reserved names

Existing builtin receiver methods (`len`, `push`, `get`, `at`, `as_str`,
`sqrt`, integer conversions, and the rest documented in
[basic values](basic-values.md)) keep their current type-directed dispatch and
take precedence over user-defined methods. An inherent or trait method may not
reuse a builtin method name; such a declaration is rejected. This avoids a
silently unreachable user method and keeps both dispatch paths deterministic.
Callable record fields with non-reserved names keep working; field projection
takes precedence as described above.

## Bounded generics

A generic type parameter may declare a declared trait as its bound:

```kush
fn describe_via<T: Describe>(value: T) -> i64 ! {panic} {
    value.describe()
}
```

The body is checked per concrete specialization, as all executable generic
bodies already are. When the specialization chooses `T = Point`, the checker
requires a unique `impl Describe for Point`. A missing impl is an error even if
the body never calls `value.describe()`. Bounds name traits only; naming a
record, enum, alias, or builtin `Type` as a trait bound is rejected.

A bound may carry trait arguments, and those arguments may mention the
enclosing function's generic parameters:

```kush
fn convert_point<T: Convert<i64>>(value: T) -> i64 ! {panic} {
    value.Convert::<i64>.render()
}
```

The obligation is keyed by the trait identity, the canonical checked argument
types, and the concrete receiver. `Convert<i64>` and `Convert<Bool>` are
different obligations, so a missing specialization is reported even when the
body never calls the method. Bound arity is checked at the declaration, while
the actual impl obligation is checked at every specialization. Bounds on a
generic method are enforced in exactly the same way.

This is static monomorphization. Generic and blanket impl headers are solved by
first-order matching. Declaration-time coherence compares every pair of impl
headers for one trait: overlapping headers must be specialization-comparable,
and the unique most-specific applicable impl wins. Incomparable overlaps and
duplicate headers are rejected. A receiver type may have several
specializations of one trait. Generic methods are supported on inherent impls
and trait impls; each call site monomorphizes the method body, and an unused
generic body is not emitted. See [generic and blanket
impls](#generic-and-blanket-impls) and
[specialization](#specialization-and-coherence).

## Associated types and constants

A trait declares associated types and compile-time constants alongside its
methods:

```kush
struct Point { x: i64 }

trait Scaled {
    type Out;
    const FACTOR: i64;
    fn scaled(self: Self) -> Self.Out ! {panic};
    fn bumped(self: Self) -> Self.Out ! {panic} {
        self.scaled() + Self.FACTOR
    }
}

impl Scaled for Point {
    type Out = i64;
    const FACTOR: i64 = 3;
    fn scaled(self: Self) -> i64 ! {panic} { self.x * Self.FACTOR }
}
```

Every impl must define every declared associated type that has no default and
every constant that has no trait default. An impl may not define an associated
item the trait did not declare. An associated type may declare a default,
`type Out = i64;`, which an impl inherits when it omits the item. A default may
mention the trait's parameters and other associated types through
`Self::Other`, but not bare `Self`. Defaults are materialized per impl with that
impl's trait arguments, participate in `Self.Out` projection and object-member
agreement, and are checked as a graph: an unknown projection or any direct or
transitive default cycle is rejected at the trait declaration. An associated
type value is an ordinary type (it may mention an impl parameter in a generic
impl) and may not mention bare `Self`. An associated constant type must be a
compile-time scalar (`i8`/`i16`/`i32`/`i64`, `u8`/`u16`/`u32`/`u64`, `Bool`, or
`Char`) or a finite tuple/inline array of such constants.

Projection normalization is checked and per-impl:

- `Self.Out` in a trait or impl method signature normalizes to the impl's
  supplied type before contract comparison and type lowering. The impl may
  write `Self.Out` or the concrete type.
- `T.Out` in a signature where `T` is a generic parameter with a trait bound
  normalizes from the unique impl selected for the concrete `T`. The projection
  never infers `T` from a result type; `T` is inferred from the ordinary
  parameters first.
- `Self.NAME` in an impl body or inherited default substitutes the impl's
  constant. `T.NAME` projects a constant through a bounded generic parameter
  using the impl selected for the concrete `T`. `Type.NAME` projects a constant
  of a concrete nominal type when exactly one trait or inherent impl provides
  it.
- An inherited constant default may reference constants defined earlier; it is
  evaluated in declaration order.

Constant values are evaluated at check time. The accepted expression subset is
scalar literals, tuple and inline-array literals of constants, earlier
associated constants, checked integer arithmetic (`+ - * / %`, shifts, bitwise
operators), boolean operators, `!`, and integer comparisons. Calls, effects,
runtime values, division by zero, and out-of-range results are rejected. An
array literal must match its declared length; aggregate constants may alias an
earlier constant of the same type. A constant therefore has no runtime storage,
address, or accessor function; it lowers to an ordinary literal or aggregate
construction at every use.

Associated type values and constants participate in the same per-impl
materialization as default bodies, so an inherited default sees `Self.Out` and
`Self.NAME` substituted for the impl that inherits it.

## Generic and blanket impls

An impl header may take ordinary type parameters:

```kush
struct Wrapper<T> { value: T }
trait Show { type Out; fn show(self: Self) -> Self.Out ! {panic}; }

impl<T> Show for Wrapper<T> {
    type Out = T;
    fn show(self: Self) -> T ! {panic} { self.value }
}
```

A parameter may carry one declared trait bound, forming a blanket impl:

```kush
impl<T: Show> Loud for Wrapper<T> {
    fn loud(self: Self) -> i64 ! {panic} { self.value.show() * 2 }
}
```

Trait arguments may also be patterns over the impl parameters:

```kush
impl<T> Convert<T> for Wrapper<T> {
    type Out = T;
    fn render(self: Self) -> T ! {panic} { self.value }
}
```

Supported header patterns are owned nominal applications (`Wrapper<T>`,
`Pair<i64, T>`, `Box<T>`, `Vec<T>`, tuples, and fixed arrays), bare parameters
for blanket impls, primitive scalar types, and natural parameters in fixed
array lengths or `Nat` trait arguments. An impl header may declare `N: Nat` and
`G: Grade` parameters:

```kush
struct Buffer<N: Nat> { data: [i64; N] }
trait First { fn first(self: Self) -> i64 ! {panic}; }
impl<N: Nat> First for Buffer<N> {
    fn first(self: Self) -> i64 ! {panic} { self.data[0] }
}

trait Weighted<G: Grade> { fn weighted(self: Self) -> i64 ! {panic}; }
impl<G: Grade> Weighted<G> for Point {
    fn weighted(self: Self) -> i64 ! {panic} { self.x }
}
```

Matching binds a natural from a concrete array length or `Nat` trait argument
and a grade from a `Grade` trait argument. A header array length must be an
integer literal or a bare natural parameter; arbitrary arithmetic in the header
is rejected so declaration-time coherence remains decidable without an
evaluator. Borrows, slices, function arrows, unions, transparent aliases,
associated projections, and `Self` in an impl header are rejected. Effect
parameters may be declared by the grammar but no impl-header position determines
one, so they are rejected as unconstrained. Lifetime parameters remain rejected
by the parser. Every impl parameter must be constrained by the self type or the
trait arguments, so dispatch can solve it uniquely.

At a call or obligation, matching is first-order:

1. Match the concrete receiver against the impl's self-type pattern.
2. Match the required trait specialization against the impl's trait-argument
   patterns.
3. Bind each impl type parameter consistently; a repeated parameter must match
   the same concrete type.
4. Check each bound on an impl parameter. A missing bound makes that impl
   inapplicable (and produces a missing-trait diagnostic for a direct bound).
5. Intern one instantiation per distinct concrete impl-argument list. The
   method body is checked with `Self` equal to the matched self type and every
   impl parameter substituted, exactly like a default body.

Generic impl methods are not eagerly checked without dispatch: a header with
no matching receiver emits no body, and a concrete implementation selected at a
call is checked once per instantiation.

## Specialization and coherence

Overlap is decided by unifying two impl headers for the same trait. Both the
self-type patterns and the trait-argument patterns must unify. Declaration-time
coherence then applies:

- **Disjoint** headers (no common receiver and specialization) coexist.
- **Specialization-comparable** headers coexist when one pattern is an instance
  of the other. The unique most-specific applicable impl wins. A concrete impl
  is always more specific than a blanket impl; `Pair<T, i64>` is more specific
  than `Pair<T, U>`.
- **Equivalent** headers that cover the same receiver and specialization are a
  duplicate-implementation error.
- **Incomparable** overlaps are rejected. For example `Pair<T, i64>` and
  `Pair<i64, T>` share the instance `Pair<i64, i64>` but neither pattern is more
  specific. Accepting either would make dispatch depend on declaration order,
  so the checker reports the conflict.

Resolution is deterministic: collect all applicable impls, retain the unique
most-specific one, and reject a tie. There is no source-order fallback. A
concrete exact impl is preferred over a generic match. Unqualified method
dispatch considers every trait, so an object or receiver with several traits
providing a name remains an explicit ambiguity error.

Only the specified specialization rule is implemented: a more-specific impl may
replace a blanket one, but there is no `default fn`, negative impl, or arbitrary
overlap accepted as specialization.

## Trait objects: closed unions and open dynamic objects

`dyn Trait` and `dyn Trait<Arguments>` are supported when the trait has a
finite, nonempty set of concrete impls. The object representation is the
normalized union of those concrete impl targets; dispatch is a checked match
over the union alternatives that calls each impl's ordinary method. There is no
vtable, fat pointer, erased function pointer, or runtime allocation.

```kush
struct Point { x: i64 }
struct Flag { on: Bool }

trait Describe { fn describe(self: Self) -> i64 ! {panic}; }
impl Describe for Point { fn describe(self: Self) -> i64 ! {panic} { self.x } }
impl Describe for Flag { fn describe(self: Self) -> i64 ! {panic} { if self.on { 1 } else { 0 } } }

fn main() -> i64 ! {io, panic} {
    let object: dyn Describe = Point { x: 9 };
    print_i64(object.describe());
    0
}
```

A concrete impl value coerces into the object union by the ordinary union
injection rule. Passing the object to a function, returning it, storing it in a
`Box`/`Vec`/tuple/array, and narrowing it are ordinary union operations. Because
the representation is a union, every alternative is still an owning or copyable
value with the same drop behavior as a statically dispatched call. A method
that consumes an owning receiver consumes the object exactly once.

When a trait has a generic or blanket impl, or appears anywhere in a nominal
field (including through an alias), it uses the dynamic representation instead.
`dyn Trait` is then a two-word fat object: a registered member identifier and an
owned payload pointer. Coercion registers the concrete member in the object's
method table, allocates the payload once, and requires the `alloc` effect. The
member table maps every object-safe trait method to the checked function
selected for that concrete type, so generic/blanket impls are instantiated at
coercion and non-type impl parameters (such as `Nat` array lengths) are solved
by the ordinary impl matcher. Dispatch resolves the identifier at runtime and
calls that member's function. Adding an impl or a new instantiation changes the
method table, never the object layout; the representation does not enumerate
the trait's members.

Three receiver modes dispatch dynamically in both representations:

- An owned `self: Self` method consumes the object alternative once. For a
  dynamic object the dispatch loads the payload and releases its allocation
  before the call.
- A shared `self: &Self` method borrows the receiver in place. For a direct
  local or a stored `&dyn`, dispatch passes a reference to the payload; the
  object is not copied, so owning and linear members remain in the object.
- An exclusive `self: &mut Self` method likewise borrows in place. Writes stay
  in the payload and are visible to the owner without an explicit write-back
  step. A dynamic call on a direct object local requires `let mut`.

A *temporary* shared receiver that owns storage or is linear remains an error:
there is no caller-owned place to borrow and copying would duplicate or drop
the payload. Bind it to a local or take a stored reference first. A temporary
mutable receiver is consumed by the ordinary union write-back path and its
updated value is dropped because no later read can observe it.

The checker reserves a borrowed receiver through every later argument, so a
nested argument cannot replace, mutate, or read a receiver reserved by an
exclusive call. Shared calls retain a shared loan through their arguments:
nested shared reads are legal, while replacing or mutably borrowing the object
is rejected. These reservations end before subsequent calls.

A stored `&dyn Trait`/`&mut dyn Trait` is an ordinary checked reference to the
object storage. Shared dispatch reads and calls in place; exclusive dispatch
writes through the same reference. Calling an owning method through a borrowed
object, or an exclusive method through a shared reference, is rejected. Owning
and linear alternatives are therefore usable through both owned objects and
stored borrowed references; a linear object must still be consumed by an owned
method before its binding goes out of scope.

Nominal record and enum declarations may spell `dyn Trait` directly, including
`Box<dyn Trait>`, `Vec<dyn Trait>`, and containers or tuples containing an
object. A trait named this way uses the fixed-width dynamic representation, so
its layout is independent of impl collection. Generic fields written as `T`
may still be instantiated later with an object type, so `Wrap<dyn Trait>` is
also supported.

Method receivers must not move an owning field out of its aggregate. Destructure
an owning tuple or generic wrapper into a local before dispatching. Mutable
dynamic calls on projected fields are rejected; they cannot silently mutate a
temporary copy and discard the update.

Object safety is checked at every `dyn` use:

- open/generic member sets are supported only by the dynamic representation;
  a closed-world union still requires a finite non-generic member set;
- ordinary type parameters only; Nat, Grade, and effect trait parameters are
  not object-safe;
- every trait method takes `self: Self`, `self: &Self`, `&self`,
  `self: &mut Self`, or `&mut self`;
- method type parameters and erased proof parameters are rejected;
- lifetime parameters and borrowed results are accepted when the result is
  tied to a borrowed receiver or another caller-owned argument. The call-site
  lifetime relation is checked against the selected member contract, so the
  returned view cannot outlive its source. An owned receiver cannot return a
  borrowed result (its payload is consumed), and a temporary receiver cannot
  return a view because the receiver is dropped before the result is used;
- no bare `Self` in non-receiver parameters or in the result, so every
  alternative has the same ABI; `Self.Item` is allowed when every impl agrees
  on that associated type, including when the type is inherited from a trait
  default;
- no intrinsically linear or `@[1]` exact-use result through dynamic dispatch;
  ordinary affine owning results such as `Box<i64>` are allowed and dropped
  exactly once per alternative;
- impls of one specialization must agree on every associated type and constant
  value, so projection is unambiguous; an agreed `Self.Item` can appear in an
  object method's parameter and result types. A dynamic member with a different
  ABI, effect row, or associated value is rejected when it is registered.

An object union may represent several traits when their concrete member sets
coincide. If more than one represented trait declares the called method name,
the call is ambiguous; qualify it as `object.Trait.method(...)`. A method that
belongs to only one represented trait needs no qualification. This closed-world
sharing is sound because every member of the union implements every represented
trait, but adding an impl rebuilds the member set. A dynamic object represents
exactly one trait specialization.

Object methods with borrowed *results* tied to a lifetime, references that
escape their owner's scope, and associated projections supplied only by generic
impls whose value depends on the impl parameter remain outside this subset.

## Checked contracts

An impl method must match its trait method exactly, conservatively, after two
capture-avoiding substitutions:

- method generic parameters are alpha-renamed by position and category, so
  `fn pair<U>` and `fn pair<V>` have the same contract but different bounds or
  parameter counts do not;
- `Self` is replaced by the concrete impl target, and each trait parameter in
  the trait signature is replaced by the impl's specialized argument. A generic
  impl's arguments are its own parameters; method parameters must be named
  distinctly from impl and trait parameters, so the substitution cannot
  capture a method binder.

The comparison then includes:

- parameter count, order, names, parameter types, and erasure markers;
- usage grades written on parameters;
- the result type, including an explicit `@[1]` result-transfer contract (trait
  and impl must both spell the same contract);
- the method's generic parameters, categories, and bounds;
- the method's lifetime parameters and outlives bounds (alpha-equivalent, so
  `'a` in a trait matches `'b` in an impl);
- the declared effect row (order-insensitive).

The impl may spell `Self` or the concrete target type; both normalize to the
target. Trait argument substitution is textual and conservative: the impl must
spell the same type syntax as the trait's substituted signature, and aliases
are not unfolded for this comparison. This conservative match is intentional:
it cannot silently weaken an effect, duplicate a linear owner through a grade,
erase proof obligations, or drop a lifetime relationship. An inherited default
does not need this comparison: it *is* the trait signature, materialized with
`Self` and the trait arguments substituted. Ordinary body
checking then applies the same rules as a free function: effects must be
declared, integer arithmetic needs `panic`, `Bytes`/`String` construction needs
`alloc, panic`, erased parameters are discharged in source order, and ownership
cleanup is deterministic.

## Receivers and borrowing boundary

A method receiver is one of:

- the impl target by value, written `self: Self` or the concrete type;
- a shared nominal-record receiver, written `self: &Self`, `self: &'a Self`,
  or the ergonomic `&self`;
- an exclusive nominal-record receiver, written `self: &mut Self`,
  `self: &'a mut Self`, or the ergonomic `&mut self`.

The owned form keeps its previous meaning: copyable records/enums are read
without moving, while owning records, enums, `String`, `Bytes`, `Vec<T>`, and
`Box<T>` are moved exactly once. An owned temporary returned by a call may be
used as a by-value receiver.

Borrowed receivers are supported only for nominal records, not enums, and only
for a **direct local owner**. `point.sum()` auto-borrows `point` exactly once;
`point.shift(2)` creates one exclusive borrow and leaves the updated fields
visible in the caller in both backends. The parser accepts `&self`/`&mut self`
as sugar for `self: &Self`/`self: &mut Self`; an impl must still match the
trait receiver spelling and mutability exactly.

An inherited default receiver is re-validated against every impl target that
materializes it: `&Self`/`&mut Self` defaults are accepted only for nominal
record targets, and an exclusive receiver is rejected for a record with
borrowed fields. The default body then follows the ordinary call-scoped
borrowing rules. In particular, a `&self` default body cannot call another
borrowed method through its own reference, because reference reborrows remain
unsupported; read fields directly or call a value-receiver method instead.

Ordinary functions may similarly take `&Record` or `&mut Record` parameters
and are called with `helper(&owner)` or `helper(&mut owner)`. These references
are call-scoped: they cannot be stored in a `let`, returned, captured by a
closure or task, placed in a record/tuple/container, or used to call a borrowed
method through an existing reference. A shared `&Record` reference permits
reads of scalar/copyable fields, shared aliases, and field access through
nested copyable records. An exclusive `&mut Record` reference additionally
permits replacing copyable, non-owning fields. Owning or linear fields, borrowed slice
fields, and fields containing exclusive leaves cannot be read or replaced
through a reference; destructure or update an owning value instead.

The loan lasts through every later argument of the same call/expression. An
exclusive record loan prevents reads, moves, replacement, drops, and any other
shared or exclusive alias of the same owner. A shared record loan permits
further shared aliases but still prevents moves, drops, replacement, and
exclusive aliases. After the full expression completes, the owner is usable
again at its checked last use.

Statically dispatched methods may still declare ordinary lifetimes and return
borrowed slice/text views tied to their non-receiver parameters; those
signatures use the normal lifetime checks. A borrowed result cannot be tied to
the receiver, and the general `&Self`/`&mut Self` escape or reborrow-alias
system is not implemented. Object methods may also return a borrowed view tied
to a borrowed receiver or another caller-owned argument; dynamic dispatch uses
the selected member's checked borrow contract as the lifetime witness, so the
result's loan is tracked like a static call. An owned or temporary receiver
cannot return a borrowed view.

Generic methods compose with borrowed receivers: the generic parameters are
ordinary inferred/explicit type, grade, natural, or effect arguments, while the
receiver remains exactly `Self`, `&Self`, or `&mut Self`. The receiver is still
evaluated once before the other arguments, and its loan still lasts through
them. A reference, borrowed record, slice view, or `&mut` handle cannot be
passed through an ordinary generic type parameter; such an instantiation is
rejected rather than erasing the loan.

## Visibility

Impl methods support `pub fn`. A method in the caller's module is always
usable. A method declared in another module must be marked `pub`; otherwise the
checker reports that it is private to its defining module. Trait and type names
follow the existing module import and visibility rules.

Trait method declarations cannot carry `pub`; they inherit the trait's
visibility. An inherited default follows the same rule: it is visible outside
its module exactly when the trait declaration is `pub`, and there is no
separate `pub` on the inherited method. A private trait therefore keeps its
inherited defaults private to the module that declares the trait.

## Limits

The following remain intentionally outside the implemented subset:

- FFI-compatible vtables and open-world membership beyond a whole-program
  checked method table; a dynamic object still requires every impl that can be
  coerced in the program to be known at compile time;
- object methods that return a borrowed result through an owned receiver or a
  temporary receiver; borrowed results tied to a borrowed receiver or another
  caller-owned argument are supported through a checked member-contract
  lifetime witness;
- associated projections supplied only by a generic impl when the value depends
  on the impl parameter; a dynamic object needs one agreed projected type, so
  traits without a concrete agreed impl remain rejected for such signatures;
- associated `Nat`/grade/effect values, owning or `String` associated
  constants, and associated constants that depend on an impl type parameter;
- effect parameters on impl headers and lifetime-parameterized impl headers;
- negative impls, `default fn`, and arbitrary-overlap specialization;
- trait bounds on trait parameters themselves;
- borrowed receivers for enums, borrowed-record metadata, stored references to
  anything other than a nominal record/owner handle/copyable object, reference
  reborrows through an existing `&Self`/`&mut Self`, or any escaping reference;
- passing a reference or borrowed record through an ordinary generic type
  parameter, including a generic method parameter;
- operator overloading, automatic deriving, and structural/duck-typed traits.

A default body is type-checked only for the impls that inherit it. A trait
declared with a default method but never implemented does not check that body;
an ill-typed default is reported as soon as an impl inherits it. This matches
the existing rule that unused generic bodies are not emitted. A generic impl
method is checked only for the concrete instantiations dispatch selects.

This is a coherent static-dispatch subset with generic and blanket impls,
associated items and defaults, deterministic specialization, closed-world
owned/shared/mutable/borrowed objects, and fixed-layout dynamic objects for
open/generic member sets. It is not a claim of a complete typeclass system or
Rust-compatible object model.

## Verification

`traits.rs` covers inherent record and enum methods, bounded generic helpers,
trait impls on nominal types and owning buffers, receiver-before-argument
evaluation, owned-receiver moves and allocation balance, duplicate and missing
impls, ambiguous dispatch and explicit qualification, exact effect/grade/
return mismatches, reserved names and field collisions, trait names used as
types, trait-method visibility, shared and exclusive nominal-record receivers,
borrowed receiver contract mismatches, explicit trait qualification, method
type arguments, cross-module visibility and imports, the runnable example, and
native/reference agreement. The borrowed-receiver boundary is covered in
`borrowed_methods.rs`.

`default_methods.rs` adds thirteen tests for inherited defaults: dispatch to
overrides and to other defaults, inherent methods called from a default body,
exact override contracts (result, effects, arity), empty impls, required
bodyless methods, `Self` substitution across two impl targets, trait type and
grade argument substitution into default signatures and bodies, generic method
inference next to a trait parameter, shared and exclusive borrowed receiver
defaults (including an exclusive field write) and their enum rejection,
ambiguity and explicit qualification of inherited defaults, body checking per
impl, record-field collisions, cross-module trait visibility, and the runnable
`examples/default-methods.kush` example in both backends.

`generic_traits.rs` covers concrete generic-trait specializations, duplicate
and ambiguity diagnostics, bounded helpers with missing specializations even in
unused bodies, trait-argument arity at impls and declarations, `Self` and
trait-argument substitution, generic trait methods with alpha-equivalent
parameters and lifetimes, generic method contracts (parameters, effects,
grades, erased evidence, wrong specialization results), generic nominal impl
targets, generic impl headers, identity and owning-type cleanup in both
backends, inferred and explicit method arguments, non-dropped method bounds,
borrowed receivers with generic scalars, loan retention into later arguments,
natural trait parameters, cross-module visibility, and the runnable
`examples/generic_traits.kush` example.

`trait_advanced.rs` adds fifty-three tests for associated type/constant
projection and substitution, `T.Out` in bounded generic results, inherited
constant defaults, tuple/array aggregate constants with aliases and length diagnostics, checked constant arithmetic and range/division diagnostics,
associated type defaults (trait-argument substitution, chained `Self::Other`
projection, object-member agreement, and unknown/cyclic/bare-`Self`
rejections), missing/extra/mistyped associated items, contract rejection when a
projection and impl result disagree, generic and blanket impls with bound
discharge, natural and grade impl-header parameters (array-length and trait
argument solving plus constrained-parameter rejection), generic trait-argument
patterns, borrowed receivers on generic impls, most-specific specialization,
duplicate/incomparable coherence rejection, owned, shared, mutable, and stored
borrowed closed-world trait objects, mutable write-back to a direct local,
temporary mutable receivers, object owning-member cleanup through mutable
dispatch, object-argument dispatch, object return and union coercion,
owning-member cleanup and allocation balance, affine owning dynamic results,
single-specialization generic objects, associated-item agreement, object
methods projecting an agreed associated type, generic method inference,
effect-exclusion bounds, linear `@[1]` results on generic impls, open/generic
object member sets with checked runtime member tables, generic and blanket
member registration, nominal fields spelling `dyn Trait` (including
`Box<dyn Trait>`), borrowed objects with owning and linear members dispatched in
place, lifetime-parameterized object methods that return a view of a caller
argument (both closed union and open dynamic), non-type (`Nat`) impl-parameter
substitution for dynamic members, and explicit object-safety and
borrowed-object rejections (generic methods, associated-type disagreement, no
impls, temporary shared dispatch of an owning object, temporary-receiver
borrowed results, owned-receiver borrowed results, mutable-through-shared
dispatch, and owning-through-borrowed dispatch). Each accepted program is
compared between the reference evaluator and the native backend.
