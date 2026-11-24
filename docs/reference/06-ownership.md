# 6. Ownership and borrowing

Kush has no garbage collector and no reference counting in safe code. Every
value has one owner; memory is released when its owner goes out of scope.

## Copy, move, linear

| Class | Types | Using the value |
| --- | --- | --- |
| copyable | scalars, function pointers, tuples/records/enums of copyable parts | copies it |
| owning (affine) | `Box`, `Vec`, `Bytes`, `String`, `once fn`, and data containing them | moves it; dropped automatically if unused |
| linear | `#[linear]` records/enums, `linear once fn`, data containing them, values graded `@[1]` | moves it; must be consumed on every path |

```kush reject
fn main() -> i64 ! {alloc} {
    let a = Box.new(1);
    let b = a;
    Box.take(a)
}
// error: moved
```

Owned locals are dropped at scope exit in reverse binding order, record
fields in reverse declaration order, unless moved. `drop(x)` drops early.
Automatic cleanup never allocates, suspends or fails.

```kush eval
#[linear]
struct Token { id: i64 }

fn redeem(t: Token) -> i64 ! {} {
    let Token { id } = t;
    id
}

fn main() -> Unit ! {io} {
    let t = Token { id: 4 };
    print_i64(redeem(t));
}
```

```output
4
```

```kush reject
#[linear]
struct Token { id: i64 }
fn main() -> Unit ! {} { let t = Token { id: 4 }; }
// error: linear value is not consumed
```

A linear value must also be consumed on early exits (`return`, `?`,
`break`). A `Vec` cannot hold linear values.

## Boxes and recursive data

```kush eval
enum List { Nil, Cons(i64, Box<List>) }

fn sum(list: List) -> i64 ! {} {
    match list {
        List.Nil => 0,
        List.Cons(head, tail) => head + sum(Box.take(tail)),
    }
}

fn main() -> Unit ! {io, alloc} {
    let list = List.Cons(1, Box.new(List.Cons(2, Box.new(List.Nil))));
    print_i64(sum(list));
}
```

```output
3
```

`Box.new` allocates, `Box.take` moves the payload out and frees the box,
`Box.read` copies a copyable payload through a borrow, and `Box.reuse(b, f)`
updates the payload in the same allocation. `Vec.map_in_place` transforms a
vector without reallocating. These and the allocation reports are in
[reuse.md](../reuse.md) and [vector-reuse.md](../vector-reuse.md).

## Borrows

Today a borrow is one of these forms (planned: one `&'a T` type,
FND-REF-*):

| Form | Made by | Gives |
| --- | --- | --- |
| `&T`, `&mut T` | `&x`, `&mut x` on a local owner (record, `Box`, `Vec`, `Bytes`, `String`), or `&x.field` | shared or exclusive access to the owner |
| `&[T]`, `&mut [T]` | `&a[i..j]`, `&mut a[..]` on an array, `Vec` or `Bytes` | a slice view of elements |
| `&str`, `&mut str` | `s.as_str()`, `s.substr(i, j)`, `&t[i..j]` on a `&str` | a view of UTF-8 text |

```kush eval
struct Account { balance: i64 }

fn deposit(acct: &mut Account, amount: i64) -> Unit ! {} {
    acct.balance = acct.balance + amount;
}

fn balance(acct: &Account) -> i64 ! {} { acct.balance }

fn add(values: &mut Vec<i64>, x: i64) -> Unit ! {alloc} {
    Vec.push(values, x);
}

fn main() -> Unit ! {io, alloc} {
    let mut acct = Account { balance: 40 };
    deposit(&mut acct, 2);
    print_i64(balance(&acct));
    let mut v: Vec<i64> = Vec.new();
    add(&mut v, 7);
    print_i64(v.len());
}
```

```output
42
1
```

Rules:

- Any number of shared borrows, or one exclusive borrow, of the same storage
  at a time. A shared borrow cannot be upgraded to an exclusive one.
- An owner cannot be moved, replaced or dropped while borrowed.
- A borrow ends at its last use, not at the end of its block; loops and
  branches are handled by a fixed point.
- Disjoint record fields may be borrowed exclusively at the same time;
  index ranges are never assumed disjoint, except the two halves of
  `Slice.split_at_mut`.

```kush eval
fn main() -> Unit ! {io, alloc} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    let view = &v[..];
    print_i64(view.get(0));
    v = v.push(2);          // fine: `view` is no longer used
    print_i64(v.len());

    let mut a: [i64; 4] = [1, 2, 3, 4];
    let (left, right) = Slice.split_at_mut(&mut a[..], 2);
    Slice.set(left, 0, 10);
    Slice.set(right, 0, 30);
    print_i64(a[0] + a[2]);
}
```

```output
1
2
40
```

```kush reject
fn main() -> i64 ! {alloc} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    let view = &v[..];
    v = v.push(2);
    view.get(0)
}
// error: cannot replace an owner while a slice view or reference borrows it
```

```kush reject
fn both(a: &mut [i64], b: &mut [i64]) -> Unit ! {} { }
fn main() -> i64 ! {alloc} {
    let mut a: [i64; 2] = [1, 2];
    both(&mut a[..], &mut a[..]);
    0
}
// error: cannot create a view while an exclusive view
```

## Lifetimes

A function returning a borrow names which input it borrows from with a
lifetime parameter. With a single borrowed input, the lifetime may be
omitted. `<'long: 'short, 'short>` declares that one lifetime outlives
another.

```kush eval
fn tail(view: &[i64]) -> &[i64] ! {} { view[1..] }

fn pick<'a>(left: &'a [i64], right: &'a [i64], first: Bool) -> &'a [i64] ! {} {
    if first { left } else { right }
}

fn main() -> Unit ! {io} {
    let a: [i64; 3] = [1, 2, 3];
    let b: [i64; 1] = [9];
    print_i64(tail(&a[..]).len());
    print_i64(pick(&a[..], &b[..], false).get(0));
}
```

```output
2
9
```

```kush reject
fn local() -> &[i64] ! {alloc} {
    let v: Vec<i64> = Vec.new();
    &v[..]
}
fn main() -> i64 ! {} { 0 }
// error: no borrowed input
```

## Borrowed records

A record may declare lifetime parameters and store borrows in its fields.
Each field keeps its own provenance.

```kush eval
struct Window<'a> { view: &'a [i64], offset: i64 }

fn first<'a>(w: Window<'a>) -> i64 ! {} { w.view.get(0) + w.offset }

fn main() -> Unit ! {io} {
    let a: [i64; 3] = [5, 6, 7];
    let w = Window { view: &a[1..], offset: 100 };
    print_i64(first(w));
}
```

```output
106
```

```kush reject
struct Window<'a> { view: &'a [i64] }
fn make<'a>(x: &'a [i64]) -> Window<'a> ! {} { Window { view: x } }
fn main() -> i64 ! {alloc} {
    let w = { let v: Vec<i64> = Vec.new::<i64>(); make(&v[..]) };
    0
}
// error: would outlive the lexical scope of its owner
```

## Where borrows cannot go today

A borrow cannot be stored in a tuple ([chapter 3](03-types.md#tuples)),
an enum, or a `Box`; cannot pass through a generic type parameter
([chapter 5](05-traits.md#not-supported)); and a closure that captures one
is scoped ([chapter 4](04-functions.md#borrowing-closures)). A spawned task
may borrow only views that its scope captured from outside the scope. These
limits are what FND-REF-POSITIONS removes.

```kush reject
enum Holder<T> { Some(T), None }
fn main() -> i64 ! {alloc} {
    let a: [i64; 1] = [1];
    let h: Holder<&[i64]> = Holder.Some(&a[..]);
    0
}
// error: borrowed
```
