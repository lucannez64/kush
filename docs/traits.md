# Static traits and user-defined methods

This page is the authoritative description of the implemented trait and method
subset. It is deliberately narrow: method calls are checked static dispatch, not
a general typeclass system.

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
not the trait's parameter name. `impl` headers remain concrete: `impl<T> ...`
blanket/generic impls and lifetime-parameterized impl headers are rejected.
A concrete generic nominal target such as
`impl First<i64> for Pair<i64>` is supported like any other concrete target.

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
see [default method bodies](#default-method-bodies). Associated types and
effect-row trait parameters are rejected with explicit diagnostics. Trait
parameters may not themselves carry trait bounds; put the bound on the function
type parameter that uses the trait. A method parameter may not reuse a trait
parameter's name, which would make substitution ambiguous.
`dyn Trait`, `impl Trait` in type position, and a trait name used as a runtime
type are rejected rather than silently accepted.

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
ordinary function call, with the checked receiver as argument zero. There are
no vtables, trait values, function pointers added for dispatch, or runtime
allocation. Receiver evaluation order, argument order, coercions, erased-proof
discharge, effects, grades, and ownership are the ordinary call rules.

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
effect, drop a grade, change the receiver mode, or change the result. There is
no specialization: an override replaces the default for that impl, it does not
add a second dispatch candidate.

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

This is static monomorphization. There is no trait-object representation, no
blanket-impl overlap solver, and no specialization/coherence reasoning beyond
exact duplicate detection. A receiver type may have several specializations of
one trait, but a duplicate `(trait, arguments, receiver)` impl is rejected.
Generic methods are supported on inherent impls and trait impls; each call site
monomorphizes the method body, and an unused generic body is not emitted.
Generic/blanket impl headers remain rejected.

## Checked contracts

An impl method must match its trait method exactly, conservatively, after two
capture-avoiding substitutions:

- method generic parameters are alpha-renamed by position and category, so
  `fn pair<U>` and `fn pair<V>` have the same contract but different bounds or
  parameter counts do not;
- `Self` is replaced by the concrete impl target, and each trait parameter in
  the trait signature is replaced by the impl's specialized argument. Trait
  arguments are closed types (generic impls are rejected), so they cannot
  capture a method binder. Naming a method parameter like a trait parameter is
  rejected at declaration to keep the substitution unambiguous.

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

Methods may still declare ordinary lifetimes and return borrowed slice/text
views tied to their non-receiver parameters; those signatures use the normal
lifetime checks. A borrowed result cannot be tied to the receiver, and the
general `&Self`/`&mut Self` escape or reborrow-alias system is not implemented.

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

The following are intentionally not implemented and are rejected or excluded:

- dynamic trait objects, vtables, and runtime dispatch;
- associated types or associated constants;
- generic/blanket impl headers, method declarations without bodies in impls,
  and impls that overlap beyond exact duplicate detection;
- specialization: an override must match the default's trait signature exactly
  and replaces it for that impl; there is no `default fn` or more-specific
  impl selection;
- effect-row parameters on a trait declaration (effect parameters remain
  available on generic functions and methods);
- trait bounds on trait parameters themselves;
- borrowed receivers for enums, borrowed-record metadata, stored references,
  reference reborrows through an existing `&Self`/`&mut Self`, or any escaping
  reference;
- passing a reference or borrowed record through an ordinary generic type
  parameter, including a generic method parameter;
- operator overloading, automatic deriving, and structural/duck-typed traits;
- trait objects in `Box`, `Vec`, records, enums, tuples, unions, closures, or
  task results;
- negative impls.

A default body is type-checked only for the impls that inherit it. A trait
declared with a default method but never implemented does not check that body;
an ill-typed default is reported as soon as an impl inherits it. This matches
the existing rule that unused generic bodies are not emitted.

This is a coherent static-dispatch subset with generic traits, generic methods,
and default bodies, not a claim of a complete typeclass system.

## Verification

`traits.rs` covers inherent record and enum methods, bounded generic helpers,
trait impls on nominal types and owning buffers, receiver-before-argument
evaluation, owned-receiver moves and allocation balance, duplicate and missing
impls, ambiguous dispatch and explicit qualification, exact effect/grade/
return mismatches, reserved names and field collisions, trait names used as
types, generic/blanket impls, associated types, trait-method visibility, shared
and exclusive nominal-record receivers, borrowed receiver contract mismatches,
explicit trait qualification, method type arguments, cross-module visibility
and imports, the runnable example, and native/reference agreement. The
borrowed-receiver boundary is covered in `borrowed_methods.rs`.

`default_methods.rs` adds thirteen tests for inherited defaults: dispatch to
overrides and to other defaults, inherent methods called from a default body,
exact override contracts (result, effects, arity), empty impls, required
bodyless methods, `Self` substitution across two impl targets, trait type and
grade argument substitution into default signatures and bodies, generic method
inference next to a trait parameter, shared and exclusive borrowed receiver
defaults (including an exclusive field write) and their enum rejection,
ambiguity and explicit qualification of inherited defaults, body
checking per impl, record-field collisions, cross-module trait visibility, and
the runnable `examples/default-methods.kush` example in both backends.

`generic_traits.rs` adds eighteen tests for concrete generic-trait
specializations, duplicate and ambiguity diagnostics, bounded helpers with
missing specializations even in unused bodies, trait-argument arity at impls
and declarations, `Self`/trait-argument substitution, generic trait methods
with alpha-equivalent parameters and lifetimes, generic method contracts
(parameters, effects, grades, erased evidence, wrong specialization results),
generic nominal impl targets, rejected blanket impls, identity and owning-type
cleanup in both backends, inferred and explicit method arguments, non-dropped
method bounds, borrowed receivers with generic scalars, loan retention into
later arguments, natural trait parameters, cross-module visibility, and the
runnable `examples/generic_traits.kush` example.
