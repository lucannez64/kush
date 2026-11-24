# 4. Functions

## Declarations

```kush fragment
pub fn name<generics>(param: Type, erased proof: { ... }) -> Result ! {effects}
    ensures { ... }
{ body }
```

Parameter types and the result type are required on every function. A
private free function may omit its effect row: its row is inferred from its
body ([chapter 7](07-effects.md#inferred-rows)). Functions may be called
before their declaration and may recurse. `erased` parameters and `ensures`
clauses are proofs ([chapter 9](09-proofs.md)). A declaration ending in `;`
instead of a body is an interface (trait methods, foreign functions).

```kush eval
fn double(x: i64) -> i64 { x * 2 }
fn main() -> Unit ! {io} { print_i64(double(21)); }
```

```output
42
```

```kush reject
pub fn double(x: i64) -> i64 { x * 2 }
fn main() -> i64 ! {} { 0 }
// error: a public function declares its effect row
```

## Generic functions

```kush eval
fn pick<T>(flag: Bool, a: T, b: T) -> T ! {} {
    if flag { a } else { b }
}

fn main() -> Unit ! {io} {
    print_i64(pick(true, 1, 2));
    print_i64(pick::<i64>(false, 1, 2));
}
```

```output
1
2
```

Type arguments are inferred from arguments of matching shape; the expected
result type does not flow into arguments yet (planned: FND-INFER-*).

## Function values

`fn(A) -> B ! {e}` is the type of a copyable, non-capturing function: one
word, the code address. Named functions, explicitly specialized generics
(`id::<i64>`) and lambdas that capture nothing have such types.

```kush eval
fn inc(x: i64) -> i64 ! {} { x + 1 }

fn twice(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(f(x)) }

fn main() -> Unit ! {io} {
    print_i64(twice(inc, 40));
    print_i64(twice(fn(x: i64) -> i64 ! {} { x * 3 }, 1));
    print_i64(twice(fn(x) { x - 1 }, 10));
}
```

```output
42
9
8
```

A lambda is `fn(params) -> Result ! {effects} { body }`. When the expected
type is a function type, parameter and result annotations may be omitted.

### Subtyping of function types

A function type accepts a function with a wider parameter type, a narrower
result type and fewer effects:

```kush eval
fn classify(x: i64 | Bool) -> i64 ! {} {
    match x { i64 @n => n, Bool @b => if b { 1 } else { 0 } }
}

fn apply(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }

fn main() -> Unit ! {io} {
    print_i64(apply(classify, 42));
}
```

```output
42
```

## Closures

A lambda that captures a value is a **`once fn`**: it owns its environment
(one heap allocation, so creating it needs `alloc`) and is consumed by its
single call. It can be passed to a `once fn` parameter, returned and stored.

```kush eval
fn adder(n: i64) -> (once fn(i64) -> i64 ! {}) ! {alloc} {
    fn(x: i64) -> i64 ! {} { x + n }
}

fn main() -> Unit ! {io, alloc} {
    let add5 = adder(5);
    print_i64(add5(37));
}
```

```output
42
```

There is no closure kind that captures and can be called more than once
(planned: FND-CLOSURE-*). A capturing lambda is not a `fn(...)`, and a `once
fn` cannot be called twice:

```kush reject
fn map(v: i64, f: fn(i64) -> i64 ! {}) -> i64 ! {} { f(f(v)) }
fn main() -> i64 ! {alloc} {
    let k = 3;
    map(1, fn(x: i64) -> i64 ! {} { x + k })
}
// error: a capturing lambda has an owned environment and must be used as 'once fn(...)'
```

```kush reject
fn twice(f: once fn(i64) -> i64 ! {}) -> i64 ! {} { f(f(1)) }
fn main() -> i64 ! {} { 0 }
// error: moved
```

| Callable type | Captures | Calls | Representation |
| --- | --- | --- | --- |
| `fn(A) -> B ! {e}` | nothing | any number, copyable | code pointer |
| `once fn(A) -> B ! {e}` | owned values | at most once; dropped if uncalled | code + environment |
| `linear once fn(A) -> B ! {e}` | owned values | exactly once; cannot be dropped | code + environment |
| `multi fn(A) -> B ! {}` | continuation state | any number; only as a handler's resumption | code + environment |

`fn` converts to `once fn`; `once fn` does not convert to `fn`, and a
`linear once fn` does not convert to `once fn`.

### Borrowing closures

A lambda that captures a slice view, a reference or a mutable scalar local
borrows it instead of copying it. Such a closure is scoped: it must be bound
directly with `let` (or called at once), and it can only be called or dropped
in that scope. It cannot be returned, stored, passed to a function or
captured by a task. Mutable scalar locals are captured by reference, so the
closure can update them. Its environment (the borrowed addresses) is still
heap-allocated, so creating it needs `alloc`.

```kush eval
fn main() -> Unit ! {io, alloc} {
    let mut count = 0;
    let bump = fn(by: i64) -> Unit ! {} { count = count + by; };
    bump(40);
    print_i64(count + 2);
}
```

```output
42
```

## Callable unions

Function types with different signatures are distinct union alternatives
and are narrowed by matching:

```kush eval
fn inc(x: i64) -> i64 ! {} { x + 1 }
fn answer() -> i64 ! {} { 42 }

fn call(f: fn(i64) -> i64 ! {} | fn() -> i64 ! {}) -> i64 ! {} {
    match f {
        fn(i64) -> i64 ! {} @g => g(41),
        fn() -> i64 ! {} @g => g(),
    }
}

fn main() -> Unit ! {io} {
    print_i64(call(inc) + call(answer));
}
```

```output
84
```

Effect-polymorphic function types (`fn(i64) -> i64 ! {e}`) are in
[chapter 7](07-effects.md#effect-polymorphism).
