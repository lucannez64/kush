# Basic values: integers, Char, tuples, String, floats, and method syntax

This page records the implemented basic-value layer. It is deliberately
specific: a listed boundary is not available merely because a related type
name is reserved by the resolver.

```sh
cargo run -p kush -- run examples/tuples.kush
# 3, 9, 21, 12 on separate lines
cargo run -p kush -- run examples/strings.kush
# 6, 5, 195, 233, 6, 1 on separate lines
cargo run -p kush -- run examples/floats.kush
# 3.5, 0.1, 1.4142135623730951, inf, 3, 1, 3 on separate lines
```

Both examples execute in the reference evaluator and in the Cranelift native
backend. The automated suites also compare both backends.

## Fixed-width machine integers

The executable integer types are `i8`, `i16`, `i32`, `i64`, `u8`, `u16`,
`u32`, and `u64`. Every value occupies one 64-bit word. Signed values are
stored sign-extended, unsigned values zero-extended, and `u64` uses the raw
bit pattern. `i64` is the default type of an integer literal when no expected
type supplies a narrower or unsigned kind.

```kush
let small: u8 = 250;
let wide: u64 = 18446744073709551615;
let negative: i8 = -128;
```

An integer literal must fit its contextual type; decimal, hexadecimal, octal,
and binary literals are accepted. Two integer operands must have the same
type. Add, subtract, multiply, divide, remainder, and shifts are checked for
the operands' own width in every build, including native builds. A negative
shift amount or an amount at least the bit width is a panic. `/` and `%` by
zero panic; `MIN / -1` and `MIN % -1` panic. Unsigned negation is rejected.
Bitwise `&`, `|`, `^`, and `!` stay in the operand's width.

Explicit conversion forms are builtins, not implicit coercions:

| Form | Result | Rule |
| --- | --- | --- |
| `Int.convert(x)` | target integer | Statically lossless only; otherwise rejected. |
| `Int.try_convert(x)` | `Option<target>` | Range checked at runtime. |
| `Int.truncate(x)` | target integer | Two's-complement truncation. |
| `Int.wrapping_add/sub/mul` | target integer | Wrap in the target width. |
| `Int.saturating_add/sub/mul` | target integer | Clamp to the target range. |
| `Int.checked_add/sub/mul` | `Option<target>` | `None` on overflow. |

The target comes from the expected type or an explicit `::<T>`. The
Option-returning forms require the conventional `Option<T>` enum in scope.
`u64.MAX`, `i32.MIN`, and the corresponding constants for every width are
available. Integer arithmetic requires the `panic` effect; `print_int` (any
integer width) requires `io` and `panic`.

## Char

`Char` is a Unicode scalar value stored as its code point. Character literals
support the lexer's escapes. `Char` supports `==`, `!=`, `<`, `<=`, `>`, and
`>=`, and literal patterns in `match`.

```kush
let classify = match c {
    'a' => 1,
    'é' => 2,
    _ => if c >= '0' && c <= '9' { 3 } else { 0 },
};
```

`Char.code(c)` returns `u32`. `Char.from_code(code)` takes a `u32` and returns
`Option<Char>`; surrogate code points and values above `U+10FFFF` are `None`.
The method spellings `c.code()` and integer conversions such as `x.convert()`
are described below.

## Tuples

An anonymous tuple has 2 through 16 elements, stored inline as one tag word
followed by the elements in layout order, within the existing 32-word layout
budget. `()` is `Unit`; it is not a zero-element tuple value. A one-element
tuple is explicitly rejected:

```kush
let pair = (1, 2);
let nested = ((3, 4), 5);
let a = pair.0;          // positional projection, names are "0", "1", ...
let b = nested.0.1;      // nested positional projection
let (x, y) = pair;       // destructuring
```

Positional fields are `0` through `15`. Records may not use numeric field
names. A tuple field that owns resources cannot be moved out by projection;
destructure the tuple instead, as with records. Projecting copyable fields is
fine. Tuple patterns may nest and may be used in the ordinary exhaustive
`match` machinery.

Generic inference descends through tuple types:

```kush
fn swap<T, U>(p: (T, U)) -> (U, T) ! {} { (p.1, p.0) }
```

A tuple type and an actual tuple must have the same arity. Result-position
inference that first binds `T` can reject the call at the argument (`tuple
expression has 3 elements, but the expected tuple type has 2`); inference
without that binding rejects it during unification (`tuple type has 2
elements, but the value has 3`). Both are errors; neither pads or ignores
fields.

Tuple elements may be scalars, `Char`, `String`, owning records/enums,
`Box`, `Vec`, `Bytes`, unions, and callable values. Element types are widened
with the same explicit representation coercions as other inferred aggregates:
union injection and callable adapters are inserted for each field rather than
reinterpreting the tuple layout. Owning fields are dropped exactly once, and a
tuple carrying a linear obligation is linear as a whole.

Early exit is respected in tuple construction. Fields are checked and
evaluated left to right. If a field diverges with `return`, `panic`, `break`,
or `?`, later fields are unreachable and are not checked or emitted, so they
cannot create spurious obligations. An earlier field's owning result is still
cleaned up on the diverging path; an unconsumeable linear result remains an
error.

The following are rejected rather than stored:

- references, slice views, or records containing borrowed fields;
- task handles;
- `Never` elements;
- layouts wider than 32 words or more than 16 elements.

Borrowed data must stay in a lexical borrowed record or slice view. Tuple
provenance support is therefore intentionally deferred.

## String

`String` is a validated UTF-8 text type with the same one-word owning buffer
representation as `Bytes`. It is a distinct static type, not an alias:
arbitrary `Bytes` cannot be passed where a `String` is expected.

A string literal is a `String` value and allocates one buffer; it requires the
`alloc` and `panic` effects. `String.from("literal")` accepts exactly one
literal and has the same effect contract. It rejects a runtime value; use the
checked conversion instead.

`String.from_utf8(bytes)` consumes an owned `Bytes` and returns the
conventional `Result<String, Bytes>`:

```kush
use std.result.Result;

let bytes = Bytes.from("hé");
match String.from_utf8(bytes) {
    Result.Ok(text) => { /* text is validated UTF-8 */ },
    Result.Err(original) => { /* rejected bytes are preserved */ },
}
```

Validation rejects overlong encodings, surrogate code points, truncated
sequences, and values above `U+10FFFF`. The invalid path returns the original
allocation as `Err(Bytes)`; it does not copy or discard it. The valid path
moves the same allocation into the `String`. There is no unchecked
`Bytes -> String` conversion and no implicit memory alias. This is the only
runtime construction path.

Text operations make byte and scalar indexing explicit:

| Operation | Result | Effects | Meaning |
| --- | --- | --- | --- |
| `String.len(s: &String)` | `i64` | none | UTF-8 byte length. |
| `String.scalar_len(s: &String)` | `i64` | none | Unicode scalar count. |
| `String.byte_at(s: &String, i: i64)` | `i64` | `panic` | Byte in `0..=255` at a byte index. Continuation bytes are readable. |
| `String.scalar_at(s: &String, i: i64)` | `Option<Char>` | none | Scalar at a scalar index; negative or past-the-end is `None`. |
| `String.as_bytes(s: &String)` | `Bytes` | `alloc, panic` | Explicit independent copy of the UTF-8 bytes. |
| `String.bytes(s: String)` | `Bytes` | none | Move the same buffer to `Bytes`; no copy. |

`String.as_bytes` and `String.bytes` are the explicit byte conversions.
Returning bytes cannot become text again without `String.from_utf8`.
`&String` is an immutable owner borrow under the ordinary call-scoped borrow
rules. Mutable owner borrows are not supported.

`String` itself does not support byte slicing, traversal by implicit char
indexing, or equality. `&s[..]` on a `String` is rejected with a message
directing callers to `String.as_str`, `String.substr`, `byte_at`,
`scalar_at`, or `as_bytes`.

Borrowed UTF-8 text views are implemented as a distinct `&str` type. A view is
created from a validated `String` with `String.as_str` / `s.as_str()` or a
checked byte-offset substring (`String.substr`, `Str.substr`, and range syntax on
an existing `&str`); it allocates nothing, is immutable, keeps the owner loaned
until its checked last use, and can be copied into a `String` only by an
explicit `Str.to_string`. Both substring endpoints must be ordered, in bounds,
and on Unicode scalar boundaries, and violations panic in both backends. Text
views participate in the shared slice lifetime machinery (`&str` parameters and
returns with explicit or conservatively elided lifetimes and explicit outlives
bounds) but are deliberately excluded from records, tuples, arrays, `Vec`,
`Box`, enums, unions, generic type parameters, closures, tasks, and function
arrow types. See [borrowed text views](borrowed-text.md) for the exact surface,
runtime model, loan rules, and rejected positions. `String` is affine:
assignment, arguments, returns, tuples, and enum fields move it, and unused
values are freed exactly once.

## Receiver-style builtin calls

Method syntax is available for builtin operations that take a distinguished
receiver. A builtin method is a type-directed spelling of the existing
namespace call. User-defined inherent and trait methods use the same receiver
syntax but lower to ordinary checked function calls; they are described in
[static traits and user-defined methods](traits.md).

```kush
let text = "héllo";
print_i64(text.len());
print_i64(text.scalar_len());
print_i64(text.byte_at(1));

let mut buffer = Bytes.from("A");
buffer = buffer.push(66);
print_i64(buffer.len());

let mut values: Vec<i64> = Vec.new();
values = values.push(10);
print_i64(values.get(0));
```

Supported receiver methods are:

| Receiver | Methods |
| --- | --- |
| `Bytes` | `len`, `capacity`, `get`, `at`, `copy`, `push`, `push_reserved`, `clear`, `from_utf8` |
| `Vec<T>` | `len`, `get`, `at`, `push`, `set` |
| `&[T]` / `&mut [T]` | `len`, `get`, `try_get`, `at`, `set` |
| `String` | `len`, `scalar_len`, `byte_at`, `scalar_at`, `as_bytes`, `as_str`, `substr`, `bytes` |
| `&str` | `len`, `scalar_len`, `byte_at`, `scalar_at`, `to_string`, `substr` |
| `Box<T>` | `take`, `read` |
| `Char` | `code` |
| integers | `convert`, `try_convert`, `truncate`, `wrapping_*`, `saturating_*`, `checked_*` |
| `f32` / `f64` | `abs`, `sqrt`, `is_nan`, `is_infinite`, `is_finite`, `to_f64`, `try_to_f32`, `try_to_int` |

The method name is resolved from the checked receiver type. Read-only methods
auto-borrow a direct local owner exactly as `&name` would; a value already
borrowed is passed through. A temporary cannot be auto-borrowed. Consuming
methods (`Bytes.push`, `Vec.push`, `Vec.set`, `String.bytes`, `Box.take`, and
`Bytes.clear`) take the receiver by value. Method calls evaluate the receiver
once, before the remaining arguments, and lower to the same call node as the
namespace form.

Consequently method syntax preserves:

- effects and effect-row checking;
- proof arguments and erased evidence (`v.at(i, proof)`, `s.at(i, proof)`);
- bounds and `Option<T>`/`Result<T,E>` result shapes;
- left-to-right evaluation;
- receiver and argument loans for the duration of later arguments;
- ownership, linear obligations, and deterministic cleanup.

Static constructors and operations remain namespace calls: `Bytes.from`,
`Bytes.with_capacity`, `String.from`, `String.from_utf8`, `String.as_str`,
`String.substr`, `Str.len`, `Str.scalar_len`, `Str.byte_at`, `Str.scalar_at`,
`Str.to_string`, `Str.substr`, `Vec.new`, `Vec.with_capacity`, `Box.new`,
`Box.reuse`, `Vec.map_in_place`, `Task.*`, `IO.*`, and `print_int`. `Box.reuse`, `Vec.map_in_place`, and `Task.cancel`
currently have no method spelling.

User-defined methods and traits are implemented as static dispatch and are
documented in [traits.md](traits.md). Traits may take explicit type, `Nat`, and
`Grade` parameters, and methods may be generic; a generic trait call writes its
specialization in the selector, as in `point.Convert::<i64>.render()`.
Inherent and trait methods on nominal
records may additionally use the call-scoped borrowed receivers `&self` and
`&mut self` (or `self: &Self`/`self: &mut Self`); those follow the record
receiver rules in [traits.md](traits.md) and
[borrowed records](borrowed-records.md), not the builtin auto-borrow table.
They may not reuse the reserved builtin method names above. If a record has a callable field whose name is one of those
reserved builtin names, that field cannot be called with method syntax; the
checker reports that the receiver has no supported builtin method of that name.
Other callable field names still use the ordinary field-projection call path.
For non-reserved names, field projection takes precedence over an unqualified
method, and an impl method that would collide with a record field is rejected.

## Floats

`f32` and `f64` are IEEE-754 binary floating-point types. Every value occupies
one 64-bit word, bit for bit: `f64` stores its 64 IEEE bits and `f32` stores its
32 bits zero-extended in the low half. A float literal is decimal: it needs a
fraction, an exponent, or both.

```kush
let ratio = 7.0 / 2.0;      // f64 by default
let whole: f64 = 1e3;       // exponent form
let rounded: f32 = 0.1;     // contextual f32
let negative: f32 = -2.5;   // unary minus flips the IEEE sign bit
```

`1..2` remains a range and `pair.0` remains a tuple projection: a decimal point
is part of a float token only when a digit follows it. Integer suffixes remain
rejected. A literal that overflows its contextual kind is a compile error;
underflow to `0` or a subnormal is ordinary IEEE rounding and is accepted.

### Arithmetic and comparisons

The same float type must appear on both sides; there are no implicit
`f32`/`f64` or integer/float conversions. `+`, `-`, `*`, `/`, and `%` use the
IEEE operations in both backends; `%` is the C runtime's `fmod`/`fmodf`, and the
remaining arithmetic, comparisons, and unary negation are Cranelift
floating-point instructions. In particular:

- `1.0 / 0.0` is `inf`, `-1.0 / 0.0` is `-inf`, and `0.0 / 0.0` is `NaN`;
  float arithmetic has no `panic` effect and never traps on these inputs.
- Overflow yields an infinity; rounding is round-to-nearest, ties to even.
- `-` performs IEEE negation, so it preserves signed zero and flips the sign of
  a NaN. `-0.0 == 0.0` is true; printing distinguishes `-0` from `0`.
- `==`, `!=`, `<`, `<=`, `>`, and `>=` are the IEEE comparisons. Any comparison
  except `!=` with a `NaN` operand is `false`; `NaN != NaN` is `true`.
- `%` is the IEEE remainder (`fmod`): `5.0 % 2.0` is `1`, and a zero divisor
  produces `NaN` rather than a panic.
- Bitwise operators, shifts, and unary `!` are rejected for floats.

Float literal patterns are rejected rather than pretending that an unbounded
float domain can be matched exhaustively. Use `==` or an ordering comparison in
a match guard. A float value may still be matched by a wildcard, a binding, or
an enum/union pattern that contains it.

### Printing

`print_float(value)` requires `io` and `panic` like other printing. It writes
the shortest decimal that round-trips at the value's own width (`f32` output is
shortest-for-`f32`, not a widened `f64`), in plain notation with no exponent,
followed by a newline:

| Value | Output |
| --- | --- |
| `1.5` | `1.5` |
| `0.1` as `f32` | `0.1` |
| `1e20` | `100000000000000000000` |
| `1.0 / 0.0` | `inf` |
| `-1.0 / 0.0` | `-inf` |
| `0.0 / 0.0` | `NaN` |
| `-0.0` | `-0` |

The reference evaluator and the native C runtime independently generate this
spelling and the tests compare them. The native runtime pins numeric locale to
`C` before running the program, so neither `printf` nor parse-back can introduce
a locale-specific decimal separator. This is an implementation-owned format
contract, not a general-purpose localization facility.

### Explicit conversions

Conversions are builtins, never coercions. The target comes from the expected
type or an explicit `::<T>`.

| Form | Result | Rule |
| --- | --- | --- |
| `Float.from_int(x)` | target float | Allowed only when every value of the source integer kind is exactly representable: 8/16-bit kinds for `f32`; 8/16/32-bit kinds for `f64`. |
| `Float.from_int_rounded(x)` | target float | Rounds to nearest, ties to even; may lose precision for wide integers. |
| `Float.try_from_int(x)` | `Option<target>` | `Some` only when the integer is exactly representable. |
| `Float.try_to_int::<I>(x)` | `Option<I>` | Truncates toward zero. `None` for a non-finite value or a truncated value outside `I`'s range. |
| `Float.to_f64(x)` | `f64` | Exact widening from `f32`; identity for `f64`. |
| `Float.try_to_f32(x)` | `Option<f32>` | Rounds to nearest, ties to even; `None` only when a finite `f64` would overflow to `f32` infinity. Subnormal/zero underflow, NaN, and infinities are accepted. |

The integer bounds are checked in the floating-point domain, so the usual
64-bit edge cases are deliberate:

- `-9223372036854775808.0` converts to `i64.MIN`, because `-2^63` is exact.
- `9223372036854775808.0` is `2^63`; it is `None` for `i64` but `Some` for
  `u64`.
- `18446744073709549568.0` (`2^64 - 2048`) is the largest `f64` below `2^64`
  and converts to `u64`; `18446744073709551616.0` (`2^64`) is `None`.
- Truncation happens before range checking: `255.9` fits `u8` as `255`, while
  `256.0` does not. `-0.5` truncates to `0`, so it fits an unsigned target.

None of these forms widen or coerce integers silently. In particular
`Float.from_int` from `i64` to `f32` is rejected statically; use
`Float.try_from_int` or the explicitly lossy `Float.from_int_rounded`.

### Methods

Receiver syntax uses the existing builtin dispatch and preserves effects,
evaluation order, borrows, and Option shapes:

| Receiver | Methods |
| --- | --- |
| `f32` / `f64` | `abs`, `sqrt`, `is_nan`, `is_infinite`, `is_finite`, `to_f64`, `try_to_f32`, `try_to_int` |

```kush
let x = -3.5;
print_float(x.abs());          // 3.5
print_float(9.0.sqrt());       // 3
print_int(if x.is_finite() { 1 } else { 0 });
```

`Float.abs`, `Float.sqrt`, the predicates, and the conversion spellings are
also available as namespace calls. `sqrt` of a negative value is `NaN`;
`sqrt(-0.0)` is `-0.0`.

### Storage, aggregates, and proof boundaries

Floats are copyable, non-owning one-word scalars. They flow through tuples,
records, enums, `Vec`, unions, generic functions, and both copyable and
once-callable argument/result ABIs without truncation or an `as i64` conversion.
A float in a tuple/record/enum occupies exactly the same word as at top level.

Floats are **not** runtime indices for erased proofs. The kernel's symbolic
scalar carriers remain `i64`, `Bool`, and `Unit`; a float parameter or literal
cannot be used in `Eq<f64, ...>` or a `prop`/`total enum` index. Such a program
is rejected instead of being miselaborated as an integer bit pattern.

### Limits

This is floating-point support for the executable basic-value layer, not a
numerical standard library. There are no constants such as `f64.MAX`, no
transcendental functions beyond `sqrt`, no `min`/`max`/`round`/`floor`/`ceil`,
no `f128`, no decimal floating point, no numeric typeclass hierarchy, and no
user-defined operator overloading.
Float equality is available as a scalar operator, but float literal patterns are
intentionally unsupported. The compiler now implements one coherent supported
float layer without claiming that the rest of the language or a formal
soundness proof is complete.

## Verification boundaries

The integer, tuple, String, float, and method suites run every executable
example in the reference evaluator and, on Linux x86-64, in a compiled native
binary. Rejection tests cover range errors, width mismatches, tuple arity and
storage limits, one-tuples, borrowed/task tuple elements, invalid UTF-8,
arbitrary bytes used as text, slicing a String, use-after-move, temporary
receiver borrows, proof omission, method arity, float literal overflow, mixed
float widths, float bitwise operators, float literal patterns, and floats used
as erased machine indices. Borrowed-text coverage adds ASCII, multibyte and
empty views, nested subviews, negative/reversed/out-of-bounds and non-scalar
byte offsets, scalar indexing, zero program allocations for borrowed
operations, owner release after the last view use (including nested views),
loops and branches, elided/explicit/outlives helper returns, later-argument
owner loans, `#[noalloc]`/`#[nosuspend]` reads, and rejection of every
documented escape position. Native/reference differential tests cover finite
values, subnormals, signed zero, infinities, NaN, f32 rounding, aggregate and
callable storage, shortest round-trip printing, and integer conversion
boundaries around `i64::MIN`, `i64::MAX`, and `u64::MAX`. This is implementation
testing, not a formal soundness proof; the Rust compiler, Cranelift, its
floating-point instructions, and the C runtime remain trusted components.


## Linear conversion boundary and final validation

Ownership-moving `String.bytes` and `String.from_utf8` reject an owning
`@[1]` argument, including an obligation propagated through an alias. Their
ungraded result cannot silently erase that obligation. Borrowed reads and
explicit copies retain their ordinary existing usage rules. The general
`@[1]` owning result contract is implemented separately (see
[usage grades](grades.md#result-transfer-contracts)); this conversion boundary
stays deliberately conservative.

The final full Boat run passes 602 tests, formatting and Clippy with warnings
denied. The generic-trait/generic-method stage adds eighteen tests for
concrete specializations, trait-argument identity and arity, bounded helpers,
contract alpha-equivalence, generic nominal impl targets, borrowed-record
receivers, loan retention, cross-module visibility, owning cleanup, and
native/reference agreement; see [traits.md](traits.md). Root review added regression coverage for the String conversion
boundary after the initial 528-test implementation; the float stage added nine
tests, including native/reference differential printing, conversion boundaries,
aggregate/callable storage, lexer/projection regressions, and erased-index
rejections; the borrowed-text stage adds thirteen tests covering views,
substrings, boundaries, allocations, loans, helpers/outlives, loops/branches,
`#[noalloc]`/`#[nosuspend]`, later arguments, native agreement, and every
documented escape rejection. The static trait/method stage adds sixteen tests
covering inherent and trait dispatch, bounded generic helpers, receiver order,
owned moves and cleanup, erased evidence, lifetime returns, visibility,
duplicates/ambiguity, exact contracts, and rejected unsupported forms; see
[traits.md](traits.md). The borrowed-receiver stage adds seventeen tests for
shared inspection and exclusive updates in both backends, ordinary `&Record`
helpers, owning-record cleanup, nested records and arrays, linear/owning
borrows, trait contracts and disambiguation, bounded generic helpers,
`#[noalloc]`/`#[nosuspend]` contracts, and alias/move/field/escape rejections;
see [borrowed records](borrowed-records.md).
