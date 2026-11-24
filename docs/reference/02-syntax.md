# 2. Syntax and control flow

## Lexical rules

- Source is UTF-8. Identifiers are `[A-Za-z_][A-Za-z0-9_]*`.
- Reserved words: `fn`, `total`, `pub`, `let`, `mut`, `return`, `if`, `else`,
  `match`, `while`, `loop`, `break`, `continue`, `enum`, `struct`, `type`,
  `module`, `use`, `erased`, `perform`, `true`, `false`. `const`, `effect`,
  `handle`, `trait`, `impl`, `prop`, `as`, `cap`, `once`, `linear` and `multi`
  are contextual: they are keywords only where the grammar expects them and
  remain usable as names elsewhere.
- `//` starts a line comment; `/* ... */` comments nest. `///` doc comments
  are ordinary comments.
- Integer literals: decimal, `0x` hexadecimal, `0o` octal and `0b` binary,
  with single `_` separators between digits. There are no suffixes; the type
  comes from context and defaults to `i64`.
- Float literals have a fraction, an exponent, or both (`1.5`, `1e3`,
  `2.5e-3`) and default to `f64`.
- Character literals `'a'` hold one Unicode scalar; string literals `"..."`
  hold UTF-8 text. Escapes: `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\'`. There
  are no raw strings and no other escapes.
- `'a` (no closing quote) is a lifetime.

```kush eval
fn main() -> Unit ! {io} {
    print_i64(0xff + 0b1010 + 0o17 + 1_000);
    let c = '\n';
    print_int(c.code());
}
```

```output
1280
10
```

## Operators

From tightest to loosest:

| Operators | Association |
| --- | --- |
| calls `f(x)`, fields `.name`, `.0`, indexing `a[i]`, ranges `a[i..j]`, `?`, `::<T>` | left |
| unary `-`, `!`, `&`, `&mut` | prefix |
| `*`, `/`, `%` | left |
| `+`, `-` | left |
| `<<`, `>>` | left |
| `&` (bitwise) | left |
| `^` | left |
| `\|` (bitwise) | left |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | not chainable; looser than bitwise operators, unlike C |
| `&&` | left, short-circuit |
| `\|\|` | left, short-circuit |
| `=` | right |

`!` on an integer is bitwise not. Comparisons do not chain:

```kush reject
fn main() -> Bool ! {} { 1 < 2 < 3 }
// error: comparisons do not chain
```

Integer arithmetic is checked: overflow, division or remainder by zero,
`MIN / -1`, and shift amounts outside the width panic in every build. Both
operands of a binary operator have the same type; there are no implicit
numeric conversions ([chapter 3](03-types.md)).

## Blocks and bindings

A block `{ ... }` is a sequence of statements and an optional tail
expression, which is the block's value. `let` binds immutably; `let mut`
allows assignment. Names may be shadowed.

```kush eval
fn main() -> Unit ! {io} {
    let x = 1;
    let x = x + 1;          // shadows
    let mut total = x;
    total = total * 10;
    let y = { let t = total; t + 1 };
    print_i64(y);
}
```

```output
21
```

A statement that starts with a block-like expression (`if`, `match`,
`while`, `loop`, `handle`, a block) ends at its `}` when the next line starts
with `(`, `[`, `-` or `*`. Write `;` after such a block to end it explicitly
on the same line.

## Conditionals and matching

`if` is an expression; without `else` its value is `Unit`. `match` tries
arms in order; an arm may have a guard `if cond`. Matches must be exhaustive
and arms must be reachable. A guard never counts toward exhaustiveness, and
integer matches need a catch-all.

```kush eval
fn classify(n: i64) -> i64 ! {} {
    match n {
        0 => 0,
        1 | 2 | 3 => 1,
        k if k < 0 => -1,
        _ => 2,
    }
}

fn main() -> Unit ! {io} {
    print_i64(classify(2) + classify(-5) + classify(9));
    print_i64(if classify(0) == 0 { 10 } else { 20 });
}
```

```output
2
10
```

```kush reject
fn f(n: i64) -> i64 ! {} {
    match n { 0 => 0, 1 => 1 }
}
fn main() -> i64 ! {} { f(0) }
// error: catch-all
```

Arms are separated by commas, block-bodied arms included.

## Loops

`while cond { ... }` and `loop { ... }`. `break` leaves the innermost loop and
may carry a value out of a `loop`; `continue` starts the next iteration.
There is no `for` loop; iterate with an index.

```kush eval
fn main() -> Unit ! {io} {
    let mut i = 0;
    let mut sum = 0;
    while i < 10 {
        i = i + 1;
        if i % 2 == 0 { continue; }
        sum = sum + i;
    }
    let first_square_over_50 = loop {
        i = i + 1;
        if i * i > 50 { break i; }
    };
    print_i64(sum);
    print_i64(first_square_over_50);
}
```

```output
25
11
```

```kush reject
fn main() -> Unit ! {} { for i in 0..3 { } }
// error: expected
```

A `while` loop may carry an `invariant { ... }` used by the prover
([chapter 9](09-proofs.md)).

## Early exit

`return e` leaves the function. `e?` on a `Result` returns the error from a
function whose result is a `Result` with the identical error type, and
otherwise yields the success value ([chapter 3](03-types.md#result-and-option)).

## Patterns

Patterns appear in `match`, `let` and parameters of destructuring lets:

| Pattern | Matches |
| --- | --- |
| `_` | anything, binds nothing |
| `name` | anything, binds it |
| `0`, `-1`, `true`, `'a'` | a literal (no float literals) |
| `(p, q)` | a tuple |
| `Point { x, y: py }`, `Point { x, .. }` | a record |
| `Enum.Variant(p, q)`, `Enum.Unit` | an enum variant |
| `[a, b, c]` | an inline array, every element (exact length) |
| `[first, .., last]` | a `DynArray` |
| `p \| q` | either; both sides bind the same names and types |
| `i64 @n` | one alternative of a union type, bound to `n` |

```kush eval
struct Point { x: i64, y: i64 }

fn main() -> Unit ! {io} {
    let p = Point { x: 3, y: 4 };
    let Point { x, y } = p;
    let (a, b) = (x * 10, y);
    let edges: [i64; 3] = [1, 2, 9];
    let last = match edges { [_, _, z] => z };
    print_i64(a + b + last);
}
```

```output
43
```

Match bindings are immutable and local to their arm. A guard may not consume
an owned binding. An inline array pattern lists every element, and a slice or
`&str` view cannot be matched at all:

```kush reject
fn main() -> i64 ! {} {
    let a: [i64; 4] = [1, 2, 3, 9];
    match a { [x, .., z] => x + z }
}
// error: inline array patterns require an exact element count
```

```kush reject
fn first(v: &[i64]) -> i64 ! {} { match v { [a, ..] => a, _ => 0 } }
fn main() -> i64 ! {} { 0 }
// error: cannot match a divergent, borrowed-reference, or borrowed-view expression
```

## Attributes

`#[name]` or `#[name(arguments)]` before a declaration. Recognized:
`#[test]`, `#[fuzz]`, `#[linear]`, `#[foreign(...)]`, `#[stack_size(N)]`,
`#[gpu]`, `#[kernel_steps(N)]`, `#[staged]`. Each is
described with its feature. There are no macros.
