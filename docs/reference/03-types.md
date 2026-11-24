# 3. Types

## Scalars

| Type | Values | Notes |
| --- | --- | --- |
| `i8` `i16` `i32` `i64` | signed integers | `i64` is the default literal type |
| `u8` `u16` `u32` `u64` | unsigned integers | |
| `f32` `f64` | IEEE-754 floats | `f64` is the default float literal type |
| `Bool` | `true`, `false` | |
| `Char` | Unicode scalar values | `'é'` |
| `Unit` (also `()`) | `()` | |
| `Never` | no values | type of `return`, `panic()`, `break`, … |

Every scalar occupies one 64-bit word at run time.

### Integers

A literal must fit its contextual type. Arithmetic is checked in every build
(see [chapter 2](02-syntax.md#operators)). Conversions are explicit builtins;
the target type comes from the expected type or `::<T>`:

| Form | Result |
| --- | --- |
| `Int.convert(x)` | lossless conversion; rejected when it could lose information |
| `Int.try_convert(x)` | `Option<T>`, checked at run time |
| `Int.truncate(x)` | two's-complement truncation |
| `Int.wrapping_add/sub/mul(a, b)` | wraps |
| `Int.saturating_add/sub/mul(a, b)` | clamps |
| `Int.checked_add/sub/mul(a, b)` | `Option<T>`, `None` on overflow |

Each width has `MIN` and `MAX` constants (`u8.MAX`, `i64.MIN`). Integer
methods have receiver spellings (`x.convert()`, `x.wrapping_add(y)`).

```kush eval
fn main() -> Unit ! {io, panic} {
    let byte: u8 = 250;
    let wide: i64 = Int.convert(byte);
    let wrapped: u8 = Int.wrapping_add(byte, 10);
    let low: u8 = Int.truncate(300);
    print_i64(wide);
    print_int(wrapped);
    print_int(low);
    print_int(u8.MAX);
}
```

```output
250
4
44
255
```

```kush reject
fn main() -> i64 ! {panic} {
    let a: u8 = 1;
    let b: i64 = 2;
    a + b
}
// error: type mismatch
```

```kush reject
fn main() -> i64 ! {} {
    let big: i64 = 300;
    let small: u8 = Int.convert(big);
    0
}
// error: Int.convert
```

### Floats

IEEE arithmetic with no `panic` effect: `1.0 / 0.0` is `inf`, `0.0 / 0.0` is
`NaN`. Comparisons follow IEEE. Floats have no bitwise operators and cannot
be matched by literal. Conversions: `Float.from_int` (only when exact for
every value of the source type), `Float.from_int_rounded`,
`Float.try_from_int`, `Float.try_to_int::<I>`, `Float.to_f64`,
`Float.try_to_f32`. Methods: `abs`, `sqrt`, `is_nan`, `is_infinite`,
`is_finite`.

```kush eval
fn main() -> Unit ! {io, panic} {
    let x = -3.5;
    print_float(x.abs());
    print_float(9.0.sqrt());
    let n: i64 = 7;
    let f: f64 = Float.from_int_rounded(n);
    print_float(f / 2.0);
}
```

```output
3.5
3
3.5
```

### Char

`Char.code(c)` gives a `u32`; `Char.from_code(n)` gives `Option<Char>`
(surrogates and values above `U+10FFFF` are `None`). Chars compare with
`==`, `<`, … and match by literal.

## Tuples

Tuples have 2 to 16 elements, are stored inline, and are projected with
`.0`, `.1`, … or destructured. There is no one-element tuple.

```kush eval
fn swap<T, U>(p: (T, U)) -> (U, T) ! {} { (p.1, p.0) }

fn main() -> Unit ! {io, panic} {
    let pair = swap((1, 20));
    let (a, b) = pair;
    print_i64(a + b);
    print_i64(((3, 4), 5).0.1);
}
```

```output
21
4
```

A tuple cannot hold a reference, a slice or text view, a borrowed record or
a task handle:

```kush reject
fn main() -> i64 ! {alloc, panic} {
    let text = "hi";
    let pair = (text.as_str(), 1);
    0
}
// error: tuples cannot store references
```

## Records

Records (`struct`) are nominal. Fields are private to the declaring module
unless marked `pub`. A record value is built with all fields, or with
`..base` for the rest; fields of a `mut` binding can be assigned.

```kush eval
struct Point { x: i64, y: i64 }

fn main() -> Unit ! {io, panic} {
    let mut p = Point { x: 1, y: 2 };
    p.x = 10;
    let q = Point { y: 5, ..p };
    print_i64(q.x + q.y);
}
```

```output
15
```

Records may be generic (`struct Pair<T> { a: T, b: T }`), may take natural
parameters (`struct Buf<N: Nat> { data: [u8; N] }`) and lifetime parameters
for borrowed fields ([chapter 6](06-ownership.md#borrowed-records)). A record
is copyable when all its fields are, otherwise it moves.

## Enums

Enums are nominal sums. Variants are unit (`Red`), positional (`Rgb(u8, u8,
u8)`) or carry named fields. Constructors are written `Enum.Variant(...)` or,
when unique, by the short variant name.

```kush eval
enum Shape { Circle(i64), Rect(i64, i64), Empty }

fn area(s: Shape) -> i64 ! {panic} {
    match s {
        Shape.Circle(r) => 3 * r * r,
        Shape.Rect(w, h) => w * h,
        Shape.Empty => 0,
    }
}

fn main() -> Unit ! {io, panic} {
    print_i64(area(Shape.Circle(2)) + area(Shape.Rect(3, 4)) + area(Shape.Empty));
}
```

```output
24
```

A generic constructor takes its type arguments from the expected type, or
from explicit `::<...>` listing all of them. They are not inferred from the
payload:

```kush reject
use std.option.Option;
fn main() -> i64 ! {} {
    let o = Option.Some(3);
    0
}
// error: generic constructor needs an expected enum type
```

```kush
use std.option.Option;
fn main() -> i64 ! {} {
    let a: Option<i64> = Option.Some(3);
    let b = Option.Some::<i64>(3);
    0
}
```

Enums have no `==`; compare by matching:

```kush reject
enum Color { Red, Green }
fn same() -> Bool ! {} { Color.Red == Color.Green }
fn main() -> i64 ! {} { 0 }
// error: enum equality and opaque-handle equality are not supported
```

Recursive enums need indirection through `Box` ([chapter 6](06-ownership.md)).
An enum cannot store a borrow. Two-variant enums whose payload is a `Box`,
`Bool`, `Char` or reference are stored in one word (niche layout).

### Result and Option

`Option<T>` and `Result<T, E>` are ordinary enums from `std.option` and
`std.result`; there is no prelude, so import them. `?` works on any enum
declared exactly as `enum Result<T, E> { Ok(T), Err(E) }`: on `Err(e)` it
returns `Err(e)` from the enclosing function, whose error type must be
identical (no conversions).

```kush eval
use std.result.Result;

fn half(x: i64) -> Result<i64, i64> ! {panic} {
    if x % 2 == 0 { Result.Ok(x / 2) } else { Result.Err(x) }
}

fn quarter(x: i64) -> Result<i64, i64> ! {panic} {
    let h = half(x)?;
    half(h)
}

fn main() -> Unit ! {io, panic} {
    match quarter(12) { Result.Ok(v) => print_i64(v), Result.Err(e) => print_i64(-e) }
    match quarter(6) { Result.Ok(v) => print_i64(v), Result.Err(e) => print_i64(-e) }
}
```

```output
3
-3
```

## Inline arrays and `DynArray`

`[T; N]` is stored inline; `N` is a compile-time natural (a literal, a `N:
Nat` parameter, or arithmetic on them). Indexing is bounds-checked unless the
prover shows the index is in range ([chapter 9](09-proofs.md)).

```kush eval
fn last<T, N: Nat>(a: [T; N]) -> T ! {panic} { a[N - 1] }

fn total(view: &[i64]) -> i64 ! {panic} {
    let mut sum = 0;
    let mut i = 0;
    while i < view.len() {
        sum = sum + view.get(i);
        i = i + 1;
    }
    sum
}

fn main() -> Unit ! {io, panic} {
    let a: [i64; 3] = [1, 2, 3];
    print_i64(last(a));
    print_i64(total(&a[..]));
}
```

```output
3
6
```

`N` is a compile-time length and index, not a run-time value; loop over a
slice view of the array instead:

```kush reject
fn count<N: Nat>(a: [i64; N]) -> i64 ! {} { N }
fn main() -> i64 ! {} { let a: [i64; 2] = [1, 2]; count(a) }
// error: function values are not supported yet
```

`DynArray<T, C>` holds up to `C` elements inline with a run-time length, and
supports rest patterns:

```kush eval
fn main() -> Unit ! {io, panic} {
    let mut a: DynArray<i64, 4> = DynArray.new::<i64, 4>();
    a = DynArray.push(a, 1);
    a = DynArray.push(a, 7);
    print_i64(match a { [x, .., z] => x + z, _ => 0 });
}
```

```output
8
```

## Bytes, String and text views

| Type | What it is |
| --- | --- |
| `Bytes` | an owned, growable byte buffer |
| `String` | owned text, always valid UTF-8; same representation as `Bytes` |
| `&str` | a borrowed view of part of a `String`, at scalar boundaries |
| `&mut str` | an exclusive view that allows only length-preserving edits |

A string literal is a `String` and allocates. `String.from_utf8(bytes)`
validates and returns `Result<String, Bytes>`; there is no unchecked
conversion. Lengths are in bytes unless the name says `scalar`.

```kush eval
fn main() -> Unit ! {io, alloc, panic} {
    let text = "héllo";
    print_i64(text.len());
    print_i64(text.scalar_len());
    let view = text.substr(0, 3);
    print_i64(view.scalar_len());
    let mut bytes = Bytes.from("ab");
    bytes = bytes.push(99);
    print_i64(bytes.len());
}
```

```output
6
5
2
3
```

`Bytes.push` and `Vec.push` consume the buffer and return it, so method
syntax is written `v = v.push(x)` ([planned change](../foundations-review.md):
FND-STD-MUT). `String` has no `==`; text helpers in `std.text` work on
`Bytes`:

```kush reject
fn same() -> Bool ! {alloc, panic} { "a" == "a" }
fn main() -> i64 ! {} { 0 }
// error: Equality requires integers, floats, Char, Bool, or Unit
```

## Vec and Box

`Vec<T>` is an owned growable vector; `Box<T>` owns one heap value.

```kush eval
fn main() -> Unit ! {io, alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(10);
    v = v.push(32);
    print_i64(v.get(0) + v.get(1));
    let b = Box.new(5);
    print_i64(Box.take(b) + v.len());
}
```

```output
42
7
```

Element types are not inferred from later uses; annotate the binding or
write `Vec.new::<T>()`:

```kush reject
fn main() -> i64 ! {alloc, panic} {
    let v = Vec.new();
    0
}
// error: cannot infer the element type
```

A `Vec` cannot hold linear values. Other containers: `Arena`/`ArenaBox`
(region allocation), user allocators (`Allocator`, `AllocBox`, `AllocVec`),
see [memory-completion.md](../memory-completion.md).

## Unions and intersections

`A | B` is a normalized union: `i64 | i64` is `i64`, order does not matter,
and a value of `A` is accepted where `A | B` is expected. A union is consumed
by matching with type patterns `T @name`. `A & B` is an intersection, mainly
used for function types.

```kush eval
fn describe(x: i64 | Bool) -> i64 ! {} {
    match x {
        i64 @n => n,
        Bool @b => if b { 1 } else { 0 },
    }
}

fn main() -> Unit ! {io, panic} {
    print_i64(describe(41) + describe(true));
}
```

```output
42
```

Subtyping is otherwise structural only for function types
([chapter 4](04-functions.md)); integer widths never subtype each other.

## Aliases and constants

```kush eval
type Pair<T> = (T, T);
const LIMIT: i64 = 40;
const DOUBLE: i64 = LIMIT + 2;

fn first<T>(p: Pair<T>) -> T ! {} { p.0 }

fn main() -> Unit ! {io, panic} {
    print_i64(first((DOUBLE, 0)));
}
```

```output
42
```

Aliases are transparent. A constant's value expression is substituted and
checked at each use, so its effects are those of the using function.

## Generic parameters

A generic binder is one of:

| Binder | Ranges over |
| --- | --- |
| `T` or `T: Type` | types |
| `T: Trait` | types implementing a trait ([chapter 5](05-traits.md)) |
| `N: Nat` | compile-time naturals (array lengths) |
| `e: Effects`, `e: Effects - alloc` | effect rows ([chapter 7](07-effects.md)) |
| `G: Grade` | usage grades ([chapter 10](10-grades.md)) |
| `'a`, `'a: 'b` | lifetimes ([chapter 6](06-ownership.md)) |

Generic code is monomorphized. Type arguments are inferred from arguments
whose types mention them directly, otherwise given with `::<...>`.
