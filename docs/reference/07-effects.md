# 7. Effects

Planned changes (decided): private functions will infer their rows
(FND-ROWS-INFER) and `panic` will stop being an effect (FND-ROWS-PANIC).
Handlers will move to one capability model
and tasks to a library on handlers (FND-HANDLERS-ONE,
FND-TASKS-ON-HANDLERS).

## Effect rows

A function's row `! { ... }` lists what it may do. Built-in effects:

| Effect | Required by |
| --- | --- |
| `io` | input/output, foreign calls |
| `alloc` | acquiring heap memory (boxes, vectors, strings, closure environments, `dyn` payloads) |
| `panic` | anything that can abort: checked arithmetic, bounds checks, `panic()`, a missing dynamic handler |
| `suspend` | yielding to the task scheduler |

Declared operations (below) are also row entries. Each operation in a body
must be allowed by the row, and a call requires the callee's **declared** row
(not what its body happens to do). A function with fewer effects can be used
where more are allowed.

```kush reject
fn noisy() -> Unit ! {io, panic} { print_i64(1); }
fn quiet() -> Unit ! {panic} { noisy(); }
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
fn sum(values: &[i64]) -> i64 ! {panic} { values.len() }
fn main() -> i64 ! {} { 0 }
// error: #[noalloc] was removed: the effect row is the contract
```

## Effect polymorphism

A row variable `e: Effects` lets a higher-order function take the effects of
its argument. It is inferred from the argument or given explicitly.

```kush eval
fn inc(x: i64) -> i64 ! {panic} { x + 1 }
fn loud(x: i64) -> i64 ! {io, panic} { print_i64(x); x }

fn apply<e: Effects>(f: fn(i64) -> i64 ! {e}, x: i64) -> i64 ! {panic, e} {
    f(x)
}

fn main() -> Unit ! {io, panic} {
    print_i64(apply(inc, 1));
    print_i64(apply(loud, 7));
    print_i64(apply::<io | panic>(loud, 8));
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

`panic()` aborts the program with a message, as do failed checks. By default
there is no unwinding and destructors do not run. A program that uses
`Task.catch` (see [chapter 8](08-concurrency.md)) unwinds panics to that
boundary instead, running cleanup.

## Effect handlers

An operation is performed with `perform Op(payload)` and handled by the
innermost enclosing `handle Op: P -> R with handler { body }`. The handler is
an ordinary function value taking the payload and a resumption token; the
token continues the body from the perform point.

```kush eval
fn main() -> Unit ! {io, panic} {
    let result = handle Ask: i64 -> i64 with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} {
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
the program aborts (so a dynamic perform also needs `panic`). A handler's own
effects are declared on the operation: `effect Log: i64 -> Unit ! {io};`.

```kush eval
effect Next: Unit -> i64 ! {panic};

fn sum_three() -> i64 ! {Next, panic} {
    perform Next(()) + perform Next(()) + perform Next(())
}

fn main() -> Unit ! {io, alloc, panic} {
    let mut counter = 0;
    let total = handle Next: Unit -> i64 with fn(
        u: Unit,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} {
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

fn parse(x: i64) -> i64 ! {Fail, panic} {
    if x < 0 { perform Fail(x) }
    x * 2
}

fn step(op: cap Ask ! {panic}, x: i64) -> i64 ! {panic} { perform op(x) + 1 }

fn main() -> Unit ! {io, panic} {
    let bad = handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {} { code } {
        parse(-5) + 1000
    };
    let good = handle Fail: i64 -> Never with fn(code: i64) -> i64 ! {} { code } {
        parse(5) + 1000
    };
    let asked = handle Ask: i64 -> i64 as ask with fn(
        x: i64,
        resume: linear once fn(i64) -> i64 ! {},
    ) -> i64 ! {panic} { resume(x + 100) } {
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
