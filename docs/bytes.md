# Owning byte buffers and a text parser

`Bytes` is an affine, growable byte buffer in the reference evaluator and the
Cranelift backend. Assignment, function arguments, returns, and enum fields move
ownership. Unused buffers are freed automatically, including on `return` and `?`.
There is no tracing GC or implicit reference counting. These operations extend
the [restricted ownership model](ownership.md); general grades and proof-driven
allocation remain future work.

```sh
cargo run -p kush -- run examples/bytes.kush
cargo run -p kush -- run examples/expression-parser.kush
cargo run -p kush -- build examples/expression-parser.kush -o target/expression-parser
./target/expression-parser
```

The parser example prints `42` for `12 + 3 * 10`.

## Operations

The following signatures describe builtins; they are not declarations to copy
into a source file. `Bytes.from` accepts exactly one string literal.

| Operation | Result | Effects | Behavior |
| --- | --- | --- | --- |
| `Bytes.from("text")` | `Bytes` | `alloc, panic` | Copy the literal's UTF-8 bytes into a new buffer. |
| `Bytes.with_capacity(n: i64)` | `Bytes` | `alloc, panic` | Empty buffer with capacity `n`. |
| `Bytes.len(b: &Bytes)` | `i64` | none | Number of initialized bytes. |
| `Bytes.capacity(b: &Bytes)` | `i64` | none | Number of bytes that fit without growth. |
| `Bytes.get(b: &Bytes, index: i64)` | `i64` | `panic` | Bounds-checked byte, in `0..255` inclusive. |
| `Bytes.copy(b: &Bytes)` | `Bytes` | `alloc, panic` | Explicit independent copy with capacity equal to length. |
| `Bytes.push(b: Bytes, byte: i64)` | `Bytes` | `alloc, panic` | Consume the buffer, append a byte, and return ownership. Grow if full. |
| `Bytes.push_reserved(b: Bytes, byte: i64)` | `Bytes` | `panic` | Same transfer, but abort if capacity is exhausted. Never grow. |
| `drop(b)` | `Unit` | none | Consume and free the buffer now. |

Literal construction gives capacity equal to byte length, including zero for an
empty literal. Embedded `\0` is an ordinary byte; no operation depends on C string
termination. For example, `Bytes.from("é\0")` contains three bytes: 195, 169, 0.
Byte indexes are not Unicode character indexes. Appending arbitrary bytes can
produce invalid UTF-8; `Bytes` is not a validated Unicode string type.

A push validates that the supplied value is in `0..255` inclusive. Reads reject
negative indexes and indexes at or beyond length. Capacity construction rejects
negative or unrepresentable capacities. Allocation failure aborts. Growing an
empty full buffer chooses capacity 8; subsequent full buffers double capacity,
saturating at the native representable limit. Existing bytes are preserved.
These checks remain enabled in native builds.

```rust
#[noalloc]
fn append(buffer: Bytes, byte: i64) -> Bytes ! {panic} {
    Bytes.push_reserved(buffer, byte)
}

fn main() -> Unit ! {alloc, panic, io} {
    let mut buffer = Bytes.with_capacity(2);
    buffer = append(buffer, 52);
    buffer = append(buffer, 50);
    print_i64(Bytes.get(&buffer, 0)); // 52
    let copy = Bytes.copy(&buffer);
    drop(buffer);
    print_i64(Bytes.len(&copy));    // 2
}
```

`push_reserved` is permitted inside `#[noalloc]`; `push` conservatively requires
`alloc` even when the caller has enough capacity. Capacity proofs and bounds-check
elimination are not implemented. Destruction and borrowing do not allocate or
suspend. These contracts cover the closed executable operation set, not arbitrary
allocator internals or real-time latency guarantees.

Immutable `&Bytes` parameters follow the same call-scoped rules as `&Box<T>`:
borrow an owned local with `&name`, forward borrowed parameters, and finish the
call before moving, replacing, or dropping the owner. Borrowed owner references
cannot be returned or stored. No buffer mutation is possible through an immutable
borrow. `&mut bytes[..]` creates an exclusive `&mut [i64]` byte view; writes use
`Slice.set` and values outside `0..=255` panic. The mutable view is a move-only
capability; it cannot be copied or stored. It can be narrowed to a child view
and returned from a helper when the result is tied to an exclusive parameter
lifetime. A checked `Slice.split_at_mut` may divide it into disjoint mutable
byte siblings, with no buffer copy. A borrowed byte view may be captured only by
a scoped, nonescaping `once fn` or used across same-task suspension; it cannot be
captured by a spawned task. See [lifetimes.md](lifetimes.md). Ordinary mutation can also consume and return the
unique owner.
A buffer can live inside enums or boxes, which then inherit its owning behavior.
`Box.read` cannot copy a boxed buffer; use `Box.take` to transfer it out.
Buffers have no implicit equality or address conversion operation.

## Parser example

[expression-parser.kush](../examples/expression-parser.kush) implements a small
recursive descent parser in Kush. It reads actual bytes from a literal-created
buffer, handles ASCII whitespace, recognizes nonnegative decimal `i64` numbers,
and gives multiplication precedence over addition. Number overflow and malformed
input return an enum error through `Result` and `?`. Parentheses, unary operators,
file input, and command-line input are not part of this literal-based example.
A [standard-stream variant](stdio.md) now reads bounded input from stdin.

The result is an owning `Expr` enum with boxed child nodes. Parsing borrows the
source; its output stores no references into that source. The example explicitly
drops the source before consuming/evaluating the AST. Failed parses also reclaim
any partially built tree. The example prints the value on success, a byte offset
on syntax failure, or `-1` on number overflow. Evaluation arithmetic remains
checked and can abort on overflow.

This is an application-level parser example. Kush's own parser remains the Rust
frontend. Native recursion and recursive AST destruction can exhaust the stack;
no tail-call or stack-bounded parsing guarantee is claimed.

## Representation and verification

A native buffer handle occupies one word. A single allocation contains its length,
capacity, and contiguous byte storage. Growth uses checked `realloc`; the returned
handle may change, so the compiler transfers ownership to the result. Compiled
literal data resides in read-only object data and is copied on construction.
The fixed C runtime implements these primitives; user functions, including the
example's parser and evaluator, are compiled by Cranelift.

The reference evaluator models buffer identities independently and limits each
buffer's capacity to 16 MiB to bound host storage. This is an evaluator budget,
not a native language limit. `evaluate_with_stats` counts buffer lifetimes as
allocations/deallocations, and reports logical capacity growth in `buffer_growths`.
Growth does not create a second owning allocation in those statistics. Native
normal-exit checks also require all owning allocations to have been released.
Panic aborts without a cleanup guarantee.

Tests compare native and reference execution for literal encodings, explicit
copies, growth, reserved appends, nested owners, early exits, and the parser's
success/error paths. Rejection tests cover use after move, invalidated borrows,
type/effect errors, and unsupported literal construction. Native bounds, byte
range, and capacity failures are checked to abort.

General strings/slices, other container types, filesystem I/O beyond standard streams, fallible allocation,
mutable owner borrows, allocator selection, and dependent length/capacity proofs remain
deferred. Validated text is a separate `String` type: it is created only from a
literal or `String.from_utf8(Bytes)`, and byte conversion is explicit. See
[basic values](basic-values.md) for UTF-8 validation, byte-vs-scalar indexing,
and receiver-style byte methods such as `buffer.len()`.

## Reusing initialized storage

`Bytes.clear(buffer: Bytes) -> Bytes ! {}` consumes and returns the same owner,
setting its initialized length to zero without changing capacity or allocating.
Old bytes are no longer accessible through the safe API; this is not a secure
memory wipe. Moves while a slice aliases the buffer remain rejected. A
binding-based owning `@[1]` argument is currently rejected, as with other
ungraded value-carrying byte builtins. See [chunked I/O](stdio.md) for a
one-allocation streaming copy that reuses its buffer after every write.
