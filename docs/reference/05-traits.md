# 5. Methods and traits

All dispatch is resolved at compile time, except calls on `dyn Trait`
values, which use a checked table.

## Methods

An `impl Type { ... }` block adds methods to a record or enum. The receiver
is written explicitly: `self: Self` (by value), `&self` (shared borrow) or
`&mut self` (exclusive borrow). A function without a receiver is an
associated function, called as `Type.name(...)`; inside the impl, `Self {
... }` builds the record.

```kush eval
struct Counter { n: i64 }

impl Counter {
    fn start(n: i64) -> Counter ! {} { Self { n: n } }
    fn value(&self) -> i64 ! {} { self.n }
    fn bump(&mut self) -> Unit ! {panic} { self.n = self.n + 1; }
    fn finish(self: Self) -> i64 ! {} { self.n }
}

fn main() -> Unit ! {io, panic} {
    let mut c = Counter.start(40);
    c.bump();
    c.bump();
    print_i64(c.value());
    print_i64(c.finish());
}
```

```output
42
42
```

Borrowed receivers are call-scoped: the borrow lasts for the call. Method
names may not reuse builtin method names (`len`, `get`, `push`, …), and a
method may not share its name with a field of the record.

```kush reject
struct Counter { n: i64 }
impl Counter { fn get(&self) -> i64 ! {} { self.n } }
fn main() -> i64 ! {} { 0 }
// error: uses a reserved builtin method name
```

## Traits

A trait lists method signatures; a method with a body is a default. An impl
must match each signature exactly (parameters, result, effects, grades,
lifetimes).

```kush eval
trait Shape {
    fn area(self: Self) -> i64 ! {panic};
    fn doubled(self: Self) -> i64 ! {panic} { self.area() * 2 }
}

struct Square { side: i64 }
struct Rect { w: i64, h: i64 }

impl Shape for Square {
    fn area(self: Self) -> i64 ! {panic} { self.side * self.side }
}

impl Shape for Rect {
    fn area(self: Self) -> i64 ! {panic} { self.w * self.h }
    fn doubled(self: Self) -> i64 ! {panic} { self.w * self.h * 2 }
}

fn report<T: Shape>(shape: T) -> i64 ! {panic} { shape.doubled() }

fn main() -> Unit ! {io, panic} {
    print_i64(report(Square { side: 3 }) + report(Rect { w: 2, h: 3 }));
}
```

```output
30
```

A bound `T: Trait` is checked when the generic function is specialized. When
two traits give a receiver the same method name, qualify the call:
`value.Trait.method(...)`.

```kush reject
trait Shape { fn area(self: Self) -> i64 ! {panic}; }
struct Square { side: i64 }
impl Shape for Square { fn area(self: Self) -> i64 ! {} { self.side } }
fn main() -> i64 ! {} { 0 }
// error: effect
```

## Generic traits, generic impls, associated items

Traits may take type, `Nat` and `Grade` parameters (`trait Convert<T>`).
Impls may be generic (`impl<T> Shape for Wrapper<T>`) or blanket (`impl<T:
Show> Loud for T`). Overlapping impls must be ordered by specificity; the most
specific applicable impl wins, and incomparable overlaps are rejected.

A trait may declare associated types (`type Out;`, with an optional default)
and scalar associated constants (`const FACTOR: i64;`). They are written
`Self.Out` / `Self.FACTOR` inside the trait and `T.Out` through a bound.

```kush eval
trait Scaled {
    type Out;
    const FACTOR: i64;
    fn scaled(self: Self) -> Self.Out ! {panic};
}

struct Point { x: i64 }
struct Wrapper<T> { value: T }

impl Scaled for Point {
    type Out = i64;
    const FACTOR: i64 = 3;
    fn scaled(self: Self) -> i64 ! {panic} { self.x * Self.FACTOR }
}

impl<T> Scaled for Wrapper<T> {
    type Out = T;
    const FACTOR: i64 = 1;
    fn scaled(self: Self) -> T ! {panic} { self.value }
}

fn reveal<T: Scaled>(value: T) -> T.Out ! {panic} { value.scaled() }

fn main() -> Unit ! {io, panic} {
    print_i64(reveal(Point { x: 4 }) + reveal(Wrapper { value: 30 }));
}
```

```output
42
```

## Trait objects

`dyn Trait` holds any value whose type implements the trait. When the set of
implementing types is finite and known, the object is a closed union of them;
when a generic or blanket impl is involved, or the object is stored in a
record field, it is a two-word object (member id, owned heap payload) whose
creation needs `alloc`. `&dyn Trait` and `&mut dyn Trait` borrow one. `dyn A
+ B` combines traits.

```kush eval
trait Describe { fn describe(self: Self) -> i64 ! {panic}; }
struct A { x: i64 }
struct B { y: i64 }
impl Describe for A { fn describe(self: Self) -> i64 ! {panic} { self.x } }
impl Describe for B { fn describe(self: Self) -> i64 ! {panic} { self.y * 10 } }

fn main() -> Unit ! {io, panic} {
    let first: dyn Describe = A { x: 2 };
    let second: dyn Describe = B { y: 4 };
    print_i64(first.describe() + second.describe());
}
```

```output
42
```

An object-safe trait has no `Self` outside the receiver and no erased proof
parameters. Downcasts, upcasting a reference to a multi-trait object and
lifetime bounds on objects (`dyn A + 'a`) are not supported.

## Not supported

Negative impls, `default fn` specialization, operator overloading, automatic
deriving, structural traits, effect parameters on impl headers, and passing a
reference through a generic type parameter (planned: FND-REF-POSITIONS):

```kush reject
fn id<T>(x: T) -> T ! {} { x }
fn main() -> i64 ! {alloc, panic} {
    let s = "hi";
    let v = id::<&str>(s.as_str());
    0
}
// error: cannot be passed through an ordinary generic type parameter
```
