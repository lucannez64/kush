# Enum niche encoding

The native backend can encode a two-variant enum in one word when one variant
is empty and the other contains exactly one supported payload. It stores the
empty variant in an otherwise-invalid payload value. Variant names and order
do not matter; source-level pattern matching and coverage still use logical
tags.

| Payload | Empty-variant encoding | Native enum storage on x86-64 |
|---|---|---:|
| `Box<T>` | null pointer (`0`) | 8 bytes |
| `&T` / `&mut T` | null pointer (`0`) | 8 bytes |
| `Bool` | `2` (valid values are `0` and `1`) | 8 bytes |
| `Char` | `0x110000` (outside Unicode's scalar range) | 8 bytes |

For example, `enum Maybe { None, Some(Box<i64>) }` now occupies 8 rather than
16 native bytes. A vector of these values uses an 8-byte element stride. The
box allocation itself and its private allocation header are unchanged. An
optional `Bool` or `Char` remains a whole 64-bit word; this change does not
introduce byte-packed scalar storage.

Construction, matching, field binding, native drop glue and builtin producers
share this layout decision. This includes `Char.from_code`, string/text scalar
lookup, `Slice.try_get`, and `Task.join`. A `TaskExit<Box<T>>`, for example,
uses null for `Cancelled` and the box pointer for `Completed`. Cancellation
still follows the existing affine/linear result-transfer rules. Source
ownership, effects, grades and borrow checks are unchanged by encoding.

The reference evaluator retains an abstract variant/tag plus payload. It
agrees on source behavior while native storage uses the encoded word. No
invalid payload is exposed as a `Bool`, `Char`, box or reference: the variant
check precedes binding or destruction of the payload.

## Optional references

Optional references are checked **lexical values**:

```kush
struct Point { x: i64 }
enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {} {
    let point = Point { x: 42 };
    let value: Maybe<&Point> = Maybe.Some(&point);
    match value { Maybe.Some(reference) => reference.x, Maybe.None => 0 }
}
```

The enum retains the reference's capability until its checked last use. Matching
the populated variant transfers that capability to the binding. Shared and
exclusive references are supported; exclusive values remain affine. Replacing,
dropping or escaping the referenced owner is rejected, including through
branches, loop results and closure capture.

A named function may take an optional reference as a parameter
(`fn queue(speaker: Option<&Audio>, ..)`): like any reference argument it lives
for the call, and the caller's loans stay in force while it runs. Results,
function-value signatures and declared record fields containing optional
references are still rejected. They require named enum lifetime contracts,
which are not currently part of the enum grammar. General borrowed enum
payloads, slices and borrowed-record payloads keep their existing restrictions;
the conventional borrowed `TaskExit<T>` remains its separate checked path.
Optional boxes, booleans and characters do cross ordinary function/callable
boundaries.

## Limits

- Only two variants, one empty and one single supported payload. There is no
  multi-variant niche packing or propagation through nested enums/records.
- Integer, floating-point, buffer/vector, function-pointer and foreign-resource
  payloads retain explicit tags in this milestone. Pointer-valued foreign
  resources have trusted host representations and are not assumed non-null.
- A unit-valued field is still a payload: `Err(Unit)` is not a fieldless
  variant. Conventional `Result<T,E>` retains its existing tag/ABI.
- Real union alternatives retain their union tag. An encoded enum can be a
  union member without losing its own encoding.
- Native layouts are compiler-private and may change between versions. This
  does not promise Rust aggregate ABI compatibility or alter the C bridge ABI.

`tests/niche_layout.rs` checks native/reference agreement under both default
and release code generation, both variant orders, owning cleanup, vectors,
outer enums/unions/records, callables, builtin producers, Unicode boundaries,
move/linear obligations, and hostile reference escapes. Internal layout tests
assert actual instantiated word counts and explicit-tag fallbacks. See
[the example](../examples/niches.kush).

## Validation checkpoint

The full Boat workspace gate passed **1,164 tests**, formatting, and strict
all-target Clippy. The sandbox was stopped afterwards. Local focused checks
also passed the two instantiated-layout assertions and ten integration tests;
each accepted integration program ran in the evaluator and native backend
with both default and release code generation. Existing integer, string,
slice, async and linear-task regressions passed locally during development.
The example prints `42`, `42`, `65` in evaluator and native release execution.

Logs: `/tmp/kush-niche-layout-integration.log`,
`/tmp/kush-niche-layout-final.log`, `/tmp/kush-boat-niche-first.log`.
