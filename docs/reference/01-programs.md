# 1. Programs

## A first program

```kush eval
fn square(x: i64) -> i64 ! {} {
    x * x
}

fn main() -> Unit ! {io} {
    print_i64(square(7));
}
```

```output
49
```

Every function states its parameter types, its result type and its effect
row `! { ... }`. Here `square` has no effects and `main` does I/O. Any
function may panic (checked multiplication can overflow); panicking is not
an effect. Effects are described in [chapter 7](07-effects.md).

## `main`

A runnable file has a `fn main()` with no parameters returning `Unit` or
`i64`. A `Unit` result exits with status 0; an `i64` result exits with its low
eight bits.

```kush eval exit=42
fn main() -> i64 ! {} {
    42
}
```

```kush reject
fn main() -> Bool ! {} { true }
// error: main
```

## Printing

The bootstrap printing builtins write one value and a newline. They need
`io` (a failed write panics).

| Builtin | Prints |
| --- | --- |
| `print_i64(x)` | an `i64` |
| `print_int(x)` | any fixed-width integer |
| `print_float(x)` | an `f32` or `f64`, shortest round-trip decimal |

```kush eval
fn main() -> Unit ! {io} {
    let small: u8 = 200;
    print_int(small);
    print_float(1.5);
    print_float(1.0 / 0.0);
}
```

```output
200
1.5
inf
```

Text and bytes go through `std.io`:

```kush eval
use std.io;

fn main() -> Unit ! {io, alloc} {
    let line = Bytes.from("hello\n");
    let written = io.write(io.stdout(), &line);
}
```

```output
hello
```

## Commands

| Command | Does |
| --- | --- |
| `kush check file.kush` | parse, resolve and check |
| `kush eval file.kush` | run with the reference evaluator |
| `kush run file.kush [-- args]` | build natively and run |
| `kush build file.kush -o out` | build a native executable |
| `kush build … --release [--backend llvm]` | optimized build; LLVM needs `clang` |
| `kush new dir`, then `kush check/build/run/test/fmt` | the same on a project ([chapter 11](11-projects.md)) |
| `kush fuzz` | fuzz the checks the prover left in place ([chapter 9](09-proofs.md)) |
| `kush lsp` | language server |

`--stats` on `eval`, `run` and `build` prints one `allocation-stats:` line to
standard error with allocation, deallocation, peak, growth, reuse and fusion
counts.

Native code targets Linux x86-64. The reference evaluator and the native
backends must agree on output, exit status, evaluation order, checks and
cleanup; the test suite compares them.

## Files and modules

A file may start with `module a.b;` and import other modules with `use`.
Imported functions are called through the last path segment. Declarations are
private unless marked `pub`.

```kush eval
use std.option;
use std.option.Option;

fn main() -> Unit ! {io} {
    let missing: Option<i64> = Option.None;
    print_i64(option.unwrap_or(missing, 7));
}
```

```output
7
```

Modules, packages and the project layout are in [chapter 11](11-projects.md).
