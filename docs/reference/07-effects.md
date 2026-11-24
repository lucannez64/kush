# 7. Effects

Planned changes (decided): handlers will move to one capability model and
tasks to a library on handlers (FND-HANDLERS-ONE, FND-TASKS-ON-HANDLERS).

## Effect rows

A function's row `! { ... }` lists what it may do. Built-in effects:

| Effect | Required by |
| --- | --- |
| `io` | input/output, foreign calls |
| `alloc` | acquiring heap memory (boxes, vectors, strings, closure environments, `dyn` payloads) |
| `suspend` | yielding to the task scheduler |

Panicking is not an effect: any function may panic ([below](#panics)).

Declared operations (below) are also row entries. Each operation in a body
must be allowed by the row, and a call requires the callee's row (written,
or [inferred](#inferred-rows) for a private function that omits it), not what
one call happens to do. A function with fewer effects can be used
where more are allowed.

```kush reject
fn noisy() -> Unit ! {io} { print_i64(1); }
fn quiet() -> Unit ! {} { noisy(); }
fn main() -> i64 ! {} { 0 }
// error: requires effects {io}
```

Releasing memory is not an effect, and a row without `alloc` is a guarantee
that no reachable path allocates (likewise `suspend`). For a row variable,
the guarantee is written as an exclusion, `e: Effects - alloc`. The former
`#[noalloc]` and `#[nosuspend]` attributes said nothing more and were
removed:

```kush reject
#[noalloc]
fn sum(values: &[i64]) -> i64 ! {} { values.len() }
fn main() -> i64 ! {} { 0 }
// error: #[noalloc] was removed: the effect row is the contract
```

## Inferred rows

A private free function may leave out `! { ... }`. Its row is then what its
body requires, through the rows of what it calls: the least fixed point over
the call graph, so recursion is fine. Callers, function values and handlers
see the inferred row exactly as if it were written.

```kush eval
fn show(x: i64) -> Unit { print_i64(x); }
fn even(n: i64) -> Bool { if n == 0 { true } else { odd(n - 1) } }
fn odd(n: i64) -> Bool { if n == 0 { false } else { show(n); even(n - 1) } }

fn main() -> Unit ! {io} {
    if even(2) { show(10) } else { show(20) }
}
```

```output
1
10
```

A declared row is still checked against the inferred rows it calls:

```kush reject
fn show(x: i64) -> Unit { print_i64(x); }
fn main() -> i64 ! {} { show(1); 0 }
// error: requires effects {io}
```

The row is the contract other code checks against, so it stays written on
public functions, methods (trait and inherent), foreign, exported and staged
functions, `#[gpu]` kernels, and functions with effect parameters. A
non-tail `perform` in an inferred function adds `alloc` to its row, since
whether its continuation allocates is only known after the row is settled.

```kush reject
struct P { x: i64 }
impl P { fn value(self: P) -> i64 { self.x } }
fn main() -> i64 ! {} { 0 }
// error: a method declares its effect row
```

## Effect polymorphism

A row variable `e: Effects` lets a higher-order function take the effects of
its argument. It is inferred from the argument or given explicitly.

```kush eval
fn inc(x: i64) -> i64 ! {} { x + 1 }
fn loud(x: i64) -> i64 ! {io} { print_i64(x); x }

fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {e} {
    f(x)
}

fn main() -> Unit ! {io} {
    print_i64(apply(inc, 1));
    print_i64(apply(loud, 7));
    print_i64(apply::<io>(loud, 8));
}
```

```output
2
7
7
8
8
```

`e: Effects - alloc` excludes effects from what `e` may be instantiated
with, so a polymorphic helper can still promise not to allocate. A row may
subtract: `! {e - io}`.

## Panics

Any function may panic: `panic()`, checked arithmetic, bounds checks, a
missing dynamic handler. A panic aborts the program with a message; by
default there is no unwinding and destructors do not run. A program that
uses `Task.catch` (see [chapter 8](08-concurrency.md)) unwinds panics to that
boundary instead, running cleanup. A panic inside an unwind cleanup
(`#[linear(unwind = f)]`) ends that cleanup and unwinding goes on; a panic
inside an allocator release callback or an arena strategy aborts the
process.

`panic` is not an effect name:

```kush reject
fn f(x: i64) -> i64 ! {panic} { x + 1 }
fn main() -> i64 ! {} { f(41) }
// error: 'panic' is not an effect: any function may panic
```

## Effect handlers

An operation is performed with `perform Op(payload)` and handled by the
innermost enclosing `handle Op: P -> R with handler { body }`. The handler is
an ordinary function value taking the payload and a resumption token; the
token continues the body from the perform point.

```kush eval
fn main() -> Unit ! {io} {
    let result = handle Ask: i64 -> i64 with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {} {
        let r = resume(x + 1);
        r * 2
    } {
        let a = perform Ask(20);
        a + 1
    };
    print_i64(result);
}
```

```output
44
```

The default token is `linear once`: the handler resumes exactly once on
every path. A handler that only ends with `resume(e)` runs in place without
allocation; one that does work after `resume` makes the body a resumable
state machine.

### Declared operations

`effect Op: P -> R;` declares an operation that called functions may
perform. It becomes a row entry; a `handle Op` discharges it. The handler
active at run time is found on a per-task handler stack; with none active,
the perform panics. A handler's own
effects are declared on the operation: `effect Log: i64 -> Unit ! {io};`.

```kush eval
effect Next: Unit -> i64 ! {};

fn sum_three() -> i64 ! {Next} {
    perform Next(()) + perform Next(()) + perform Next(())
}

fn main() -> Unit ! {io, alloc} {
    let mut counter = 0;
    let total = handle Next: Unit -> i64 with fn(
        u: Unit,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {} {
        counter = counter + 10;
        resume(counter)
    } {
        sum_three()
    };
    print_i64(total);
}
```

```output
60
```

### Other handler forms

| Form | Meaning |
| --- | --- |
| `resume: fn(R) -> R ! {}` | multishot: resume zero or more times; live values must be copyable |
| `resume: multi fn(R) -> R ! {}` | multishot token that may carry state across calls |
| `effect Fail: i64 -> Never;` | abortive: the handler takes no token and its result becomes the `handle`'s value; the code between the perform and the handle is discarded and its owned values dropped |
| `handle Op: P -> R as op with h { ... }` and `op: cap Op ! {e}` | a capability: pass `op` explicitly and `perform op(x)` calls exactly that handler, without a dynamic lookup |

```kush eval
effect Fail: i64 -> Never;
effect Ask: i64 -> i64;

fn parse(x: i64) -> i64 ! {Fail} {
    if x < 0 { perform Fail(x) }
    x * 2
}

fn step(op: cap Ask ! {}, x: i64) -> i64 ! {} { perform op(x) + 1 }

fn main() -> Unit ! {io} {
    let bad = handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {} { code } {
        parse(-5) + 1000
    };
    let good = handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {} { code } {
        parse(5) + 1000
    };
    let asked = handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {} { resume(x + 100) } {
        step(ask, 1)
    };
    print_i64(bad);
    print_i64(good);
    print_i64(asked);
}
```

```output
-5
1010
102
```

A capability is second-class: it can be passed and forwarded, not stored,
returned or captured by a task. A spawned task inherits only copyable
non-capturing handler frames.

Details and costs: [effect-handlers.md](../effect-handlers.md),
[effect-state-machines.md](../effect-state-machines.md),
[effect-capabilities.md](../effect-capabilities.md),
[multishot-capabilities.md](../multishot-capabilities.md),
[abortive-handlers.md](../abortive-handlers.md).
