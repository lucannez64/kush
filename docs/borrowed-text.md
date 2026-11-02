# Borrowed text views and checked substrings

`&str` is an immutable, shared view of a contiguous range of a validated
`String`. It is a distinct static type: it is not `String`, not `Bytes`, not
`&[i64]`, and not a mutable alias. A text view never allocates and never
changes its owner. The executable representation is a private four-word
descriptor `(data pointer, byte length, stride, byte-elements flag)`, the same
shape used by slice views with a fixed byte stride of one, but the checker keeps
the text type separate so a `&str` can never be indexed or written as an
element slice.

```kush
use std.option.Option;

fn scalar_count(text: &str) -> i64 ! {} {
    Str.scalar_len(text)
}

fn initial(text: &str) -> &str ! {panic} {
    if Str.scalar_len(text) == 0 { text } else { text[0..1] }
}

fn main() -> i64 ! {io, alloc, panic} {
    let text = "héllo";
    let view: &str = text.as_str();   // no allocation
    print_i64(view.len());            // 6 UTF-8 bytes
    print_i64(view.scalar_len());     // 5 Unicode scalars

    let middle = view.substr(1, 3);   // "é"
    print_i64(middle.len());          // 2
    match middle.scalar_at(0) {
        Option.Some(c) => print_int(c.code()), // 233
        Option.None => print_i64(-1),
    }

    let tail = &view[3..6];           // "llo", a checked byte-range subview
    let owned: String = tail.to_string(); // explicit allocating copy
    print_i64(owned.len());           // 3
    0
}
```

Run `cargo run -p kush -- run examples/borrowed-text.kush`.

## Construction and checks

A view is created only from one of these forms:

| Form | Receiver | Effects | Meaning |
| --- | --- | --- | --- |
| `String.as_str(&s)` / `s.as_str()` | `&String` | none | Whole text. |
| `String.substr(&s, start, end)` / `s.substr(start, end)` | `&String` | `panic` | Checked byte range. |
| `Str.substr(v, start, end)` / `v.substr(start, end)` | `&str` | `panic` | Checked subview. |
| `&v[start..end]`, `&v[start..]`, `&v[..end]`, `&v[..]` | `&str` local | `panic` when a bound is present | Checked subview. |

The namespace and method spellings lower to exactly the same checked range
expression, evaluate the receiver once, and preserve evaluation order. Method
syntax auto-borrows a direct `String` local exactly as `&s`; a temporary String
receiver (`"abc".as_str()`) is rejected. `String.as_str` never panics;
`String.substr` and `Str.substr` require the `panic` effect because their
offsets are runtime values.

### Exact substring contract

`start` and `end` are **byte offsets**, `end` is exclusive, and the following
must hold at runtime:

1. `0 <= start <= end <= Str.len(v)`;
2. `start` and `end` are UTF-8 scalar boundaries (byte `i` is a boundary when
   `i == len` or the byte at `i` is not a continuation byte `10xxxxxx`).

Both conditions are checked at runtime in the reference evaluator and in native
code. A violation is a `panic:` diagnostic in the evaluator and an abort in
native code. This implementation intentionally chooses **panic** rather than a
recoverable `Option`/`Result` API; there is no fallible substring form yet.
Offsets are never Unicode scalar indices. Use `scalar_at`/`scalar_len` for
scalar access and `byte_at`/`len` for byte access.

`String` itself still has no slicing syntax: `&s[..]` on a `String` is rejected
with guidance to use `String.as_str`, `String.substr`, `byte_at`, or
`scalar_at`. Range syntax applies to `&str` views only, and its base must be a
local `&str` binding or a nested range expression, not an arbitrary call result.

## Reading a view

| Operation | Result | Effects | Meaning |
| --- | --- | --- | --- |
| `Str.len(v)` / `v.len()` | `i64` | none | UTF-8 byte length of the view. |
| `Str.scalar_len(v)` / `v.scalar_len()` | `i64` | none | Unicode scalar count of the view. |
| `Str.byte_at(v, i)` / `v.byte_at(i)` | `i64` | `panic` | Byte in `0..=255` at byte index `i`; continuation bytes are readable. |
| `Str.scalar_at(v, i)` / `v.scalar_at(i)` | `Option<Char>` | none | Scalar at scalar index `i`; negative or past the end is `None`. |
| `Str.to_string(v)` / `v.to_string()` | `String` | `alloc, panic` | Explicit independent copy of the view into an owned String. |

`Str.scalar_at` requires the conventional `Option<T> { None, Some(T) }` in
scope, like `String.scalar_at`. `Str.to_string` is the only conversion back to
an owning String; it allocates a fresh buffer and never transfers or aliases the
owner. There is deliberately no `Str.as_bytes`: a byte view would be a second
alias form over the same storage, and the owning `String.as_bytes` copy remains
the explicit byte route. Equality, ordering, printing, searching, trimming and
splitting are not implemented for text views.

## Lifetimes and loans

`&str` reuses the checked slice-view capability machinery:

- a view is tied to its `String` owner or parent view; creating it extends the
  owner's shared loan, released at the view's checked last use (loop- and
  branch-aware);
- while a view or any alias/subview can still be used, the owner cannot be
  moved, dropped, assigned over, or consumed by `String.bytes`/
  `String.from_utf8`; an exclusive `&mut String` borrow is checked like any
  other mutable owner reference and excludes shared aliases;
- a shared view may be copied to another binding, and nested shared subviews may
  coexist;
- a view of a local owner or temporary cannot escape: a returned view must be
  tied to a parameter carrying the declared result lifetime;
- named functions accept `&str` parameters and return `&str` with explicit
  lifetimes or conservative single-input elision, including helper chains.
  Explicit outlives shortening may also omit the bound
  (`fn f<'long, 'short>(s: &'long str) -> &'short str`), in which case
  `'long: 'short` is inferred and validated at each call site.
- call results and later arguments preserve the same loans: an earlier text
  argument keeps its owner loaned through later argument evaluation.

`&str` is immutable. `&mut str`, `&mut view[..]`, and mutating a text view are
rejected.

### Conservative boundaries

- A view derived from a `&String` parameter has no caller-named lifetime and
  cannot be returned, even though it may be used locally.
- Type aliases that hide `&str` in a function parameter or result do not supply
  a signature lifetime, so using them in borrowed signatures is rejected rather
  than inferred.
- Function arrow types, first-class function values, lambdas, closures, and
  tasks do not represent text borrows. A named function with a `&str` parameter
  or result cannot be converted to a value, a lambda cannot take or return
  `&str`, and a lambda cannot capture a text view.

## Rejected positions

A text view must stay in a lexical binding, be passed directly to a named
function, be stored in a declared-lifetime `&str` record field or a
`Box<&str>`/`Vec<&str>` reference container, or be copied by `Str.to_string`.
It cannot be stored in or escape through:

- a tuple, inline array, enum payload, union alternative, or generic type
  parameter;
- a closure capture, task body, function-arrow type, first-class function value,
  or match scrutinee/pattern;
- a `break` value, a block tail that borrows a local owner, or a returned view
  whose storage is a local or temporary;
- a single-index read (`view[i]`): use `byte_at`, `scalar_at`, or a byte-range
  subview;
- a `let mut` binding, a reassignment, or any mutable reinterpretation.

## Runtime and cleanup

The reference evaluator stores a view as the same shared view value used for
slices, flattened pointer/length intervals over an owner buffer; a subview
adjusts the start and length without copying. Native lowering computes the data
pointer and byte length directly from the String buffer and passes the four
words by value through the existing function ABI. View construction performs no
call into the C runtime and allocates no program memory. `Str.to_string`
allocates one new buffer in both backends. Existing `String` drops still free
the owner exactly once after its last use; a view itself owns no storage and is
never dropped.

## Remaining limits

This is borrowed, immutable text over validated `String` storage, not a string
library. There is no fallible substring, no `&mut str`, no text equality or
ordering, no char/byte iteration protocol, no slicing on a `String` value, no
`Str.as_bytes`, no `&String`-derived returned view, no text view in aggregates,
closures, tasks, unions, generics, or arrow types, and no general lifetime
inference beyond the documented slice rules. Arbitrary `Bytes` still cannot be
used as text without `String.from_utf8`.
