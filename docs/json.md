# JSON parser and minifier

`std.json` is written entirely in Kush. It parses an owned tree from a borrowed
input slice and serializes that tree to compact UTF-8 JSON. It uses ordinary
enums, boxes, `Bytes`, explicit effects, `Result` propagation and deterministic
cleanup. It introduces no compiler builtin, tracing GC or reference counting.

The [example CLI](../examples/json.kush) reads stdin to EOF and emits compact JSON:

```sh
printf ' { "todo": ["Ship Kush"], "done": false } ' | ./target/kush-json
# {"todo":["Ship Kush"],"done":false}
```

The Linux x86-64 binary is built remotely on Boat. To build from source on a
machine where compilation is allowed:

```sh
cargo run -p kush -- build examples/json.kush -o target/kush-json
```

In this workspace, use Boat as directed by `AGENTS.md`.

## API

```rust
use std.result.Result;
use std.json;

// All three operations below require alloc + panic; none suspends.
json.parse(source: &[i64]) -> Result<json.Value, json.Error>
json.stringify(value: json.Value) -> Result<Bytes, json.Error>
json.message(error: json.Error) -> Bytes
// No effects:
json.position(error: json.Error) -> i64
```

For a `Bytes` input, call `json.parse(&source[..])`. Parsing borrows the input
only for the call. The resulting tree owns its decoded strings, number text and
child lists, so the input can be dropped immediately after parsing. Serialization
consumes the tree. Ignored trees and partially constructed trees on error are
freed by the ordinary ownership machinery.

The public data types are:

```rust
enum Value {
    Null, Bool(Bool), Number(Bytes), String(Bytes),
    Array(Box<Items>), Object(Box<Members>),
}
enum Items { End, More(Value, Box<Items>) }
enum Members { End, More(Bytes, Value, Box<Members>) }
```

The lists retain element order, object member order and duplicate keys. There
is no implicit map conversion or duplicate-key overwrite policy. Destructure
values and use `Box.take` to consume child lists. This first representation uses
boxed lists rather than an arena or hash map, and is not a performance claim.

## Grammar and encoding

The implementation follows the JSON grammar in
[RFC 8259](https://www.rfc-editor.org/rfc/rfc8259), with the bounded Unicode-scalar
policy described below. It accepts top-level scalars as well as containers,
JSON's four whitespace bytes, empty arrays/objects, negative numbers, fractions
and signed exponents. It rejects comments, trailing commas, extra values,
leading-zero numbers, missing fraction/exponent digits, `NaN` and `Infinity`.

Numbers retain their exact validated source text as `Bytes`. There is no float
conversion, overflow from numeric magnitude, rounding or loss of exponent
precision. `-0`, `1.2300` and `1e9999` keep those spellings on serialization.
Numeric arithmetic and conversion are not part of this API.

Strings decode all JSON escapes, including `\uXXXX` and paired UTF-16 surrogate
escapes, into UTF-8. Raw UTF-8 is validated, rejecting truncated sequences,
overlong encodings, encoded surrogates and scalars above U+10FFFF. Lone surrogate
escapes are rejected deliberately; this is a Unicode interoperability policy
stricter than the RFC's escape ABNF. Raw control bytes in strings are rejected;
escaped controls and NUL are supported. A leading UTF-8 BOM is rejected.

Serialization escapes quotes, backslashes and control bytes, while emitting
other Unicode scalars as UTF-8. It also validates strings and number tokens in
manually constructed trees. Output is compact JSON, not canonical JSON:
member order and number spellings are preserved and keys are not sorted.

## Errors and limits

`Error` distinguishes `Unexpected`, `InvalidNumber`, `InvalidEscape`,
`InvalidUnicode`, `Trailing` and `Limit`. Each variant contains a zero-based
byte offset. For parser errors this is in the input, potentially its end; for
serializer leaf errors it is local to that string or number, and structural
serializer limits use offset zero. The CLI reports a message and offset on
stdout and exits 1 for a JSON error, or 2 for an I/O/input-capacity failure.

Parsing is bounded to 65,536 input bytes, eight nested containers and 256 members
or elements per container. Serialization applies the same nesting/container
limits. These bounds keep recursive processing within the current evaluator's
nesting budget; it also has a separate total computation budget, so sufficiently
large valid documents may exceed that budget in `eval`. Native execution has
no evaluator computation budget. Allocation failure retains the language's
normal panic behavior.

This is a whole-document parser, not a streaming parser. There is no JSON
Pointer, schema validation, object lookup API, numeric conversion or pretty
printing yet. Parsing and serialization allocate; lexical helpers use checked
`#[noalloc]` contracts, but the complete parser is not allocation-free.


## Validation

The full Boat workspace suite passes 474 tests, formatting and Clippy. JSON
regressions cover exact number text, decoded Unicode and controls, malformed
UTF-8 and escapes, duplicate keys, error positions, partial-tree cleanup,
container/depth boundaries and native/reference agreement. Allocations and frees
balance in reference runs; native normal-exit ownership checks remain enabled.
A separate seeded native check matched Python JSON semantics on 100 generated
documents and rejected 20 documents with trailing input. These checks are not
a formal conformance or memory-safety proof.
