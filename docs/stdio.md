# Bounded synchronous standard-stream I/O

Kush programs can read stdin and write raw bytes to stdout in both the Cranelift
backend and reference evaluator. Operations take explicit standard-stream values,
require the `io` effect, and return recoverable failures through the ordinary
`Result` enum. They use existing byte-buffer capacity without growing storage.
This is a synchronous bootstrap interface; async and general file handles remain
future work.

```sh
printf '12 + 3 * 10\n' | cargo run -p kush -- run examples/expression-stdin.kush
# 42
printf '12 + 3 * 10\n' | cargo run -p kush -- eval examples/expression-stdin.kush
# 42
cargo run -p kush -- build examples/expression-stdin.kush -o target/expression-stdin
printf '2 * 3 + 4\n' | ./target/expression-stdin
# 10
printf 'hello\n' | cargo run -p kush -- run examples/stdio.kush
# hello
```

## Values, types, and effects

The signatures below describe compiler builtins, not declarations to add to a
source file:

```rust
IO.stdin() -> Stdin ! {io}
IO.stdout() -> Stdout ! {io}
IO.read_all(input: Stdin, buffer: Bytes) -> Result<Bytes, i64> ! {io}
IO.read_line(input: Stdin, buffer: Bytes) -> Result<Bytes, i64> ! {io}
IO.write(output: Stdout, bytes: &Bytes) -> Result<Unit, i64> ! {io}
```

A file using `read_all` or `write` must declare the conventional
`enum Result<T,E> { Ok(T), Err(E) }`. Reversing variant order also works. The
compiler instantiates the relevant result type, validates its declaration, and
uses its actual variant tags. There is no implicit standard-library prelude yet.
`?` propagation requires matching error types as usual.

`Stdin` and `Stdout` are opaque, copyable views of the process's inherited standard
streams. They can be passed, returned, or stored in ordinary enums/boxes. Safe
code cannot construct them from integers, compare addresses, or convert one
stream direction into the other. They do not own or close descriptors on drop.
Copies share the same external stream state. These explicit arguments make a
function's stream dependency visible; the globally accessible factories are a
bootstrap convenience, not a complete authority-isolation mechanism.

```rust
enum Result<T,E> { Ok(T), Err(E) }

#[noalloc]
#[nosuspend]
fn copy(input: Stdin, output: Stdout, buffer: Bytes) -> Result<Unit,i64> ! {io} {
    let bytes = IO.read_all(input, buffer)?;
    IO.write(output, &bytes)
}

fn main() -> i64 ! {io, alloc, panic} {
    match copy(IO.stdin(), IO.stdout(), Bytes.with_capacity(4096)) {
        Ok(_) => 0,
        Err(_) => 1,
    }
}
```

The caller allocates storage before calling `copy`. Neither I/O operation adds
`alloc`, `panic`, or `suspend` to its declared effects. `noalloc` covers acquiring
or growing program-owned storage; trusted allocator/libc internals are outside
that guarantee. `nosuspend` means these operations do not yield to a scheduler.
They **can block**, including while waiting for EOF. It is not a nonblocking or
bounded-latency guarantee. There is no mandatory `async fn`/`await` syntax here;
[structured async and cooperative cancellation](async.md) adds explicit task
scopes and suspension but keeps these blocking stream operations separate.

## Reading, bounds, and ownership

`read_all` consumes the buffer and appends bytes until EOF. Its initialized prefix
is preserved. On success it returns the unique buffer with its original capacity.
It does not reserve, grow, or relocate storage. The caller may pass an empty
buffer or one with an initialized prefix created through `Bytes.push_reserved`.

When capacity is full, the operation attempts a one-byte read to distinguish EOF
from excess input. EOF succeeds even for a zero-capacity buffer. An excess byte
returns `Err(27)` (`EFBIG` on the current Linux target). **That byte is consumed.**
This operation is a bounded read-to-EOF API, not a chunk-reading API. On a terminal,
finish input with EOF; a newline alone does not complete the read.

Any failure destroys the consumed buffer before returning `Err(code)`. Partially
read bytes are discarded. Input already consumed from the external stream cannot
be rolled back. This includes the one-byte capacity probe. Cleanup of other
owners on subsequent `?`, `return`, or scope exit follows the normal affine rules.

## Writing and errors

`write` borrows the buffer and attempts to write all initialized bytes, including
NUL and non-UTF-8 bytes. It retries interrupted system calls and continues after
short writes. Empty buffers succeed without an OS write. It does not destroy or
modify the buffer, even on error. A failed call may have written a prefix; retrying
the whole buffer can repeat that prefix. Success does not promise durable storage,
a file synchronization operation, or application-level acknowledgement.

For this Linux x86-64 interface, positive `i64` error values are Linux errno codes.
Notable examples are `9` (`EBADF`), `27` (`EFBIG`, including the capacity check),
and `32` (`EPIPE`). An unsuccessful zero-byte write maps to `5` (`EIO`). Errors
such as `EAGAIN` on inherited nonblocking streams are returned, not busy-retried;
only `EINTR` is retried. A portable typed `IoError` abstraction is deferred.

Native process startup ignores `SIGPIPE`, allowing broken stdout pipes to produce
`Err(EPIPE)` instead of terminating the process. This is a process-wide runtime
policy. The existing `print_i64` helper still aborts on output failure. Arbitrary
signal configuration, descriptor closing, and FFI are not exposed to Kush source.

## Examples and reference evaluation

[expression-stdin.kush](../examples/expression-stdin.kush) reads at most 4096 bytes
and runs the same decimal/addition/multiplication parser as the
[literal-input example](bytes.md). It frees its source buffer before evaluating
the owning AST. Syntax errors print a byte offset; number overflow prints `-1`.
An I/O error prints the negative errno and exits with status 1. The parser remains
recursive and does not promise bounded stack usage. Parsing functions are repeated
in the two example files while cross-file module loading is deferred.

[stdio.kush](../examples/stdio.kush) copies at most 4096 bytes unchanged and exits
with status 1 on a recoverable I/O error.

The Rust host API provides `evaluate_with_io(input, output)` and
`evaluate_with_io_and_stats(input, output)` using injected `Read`/`Write` values.
`evaluate` and `evaluate_with_stats` retain deterministic empty input. The CLI's
`eval` command explicitly supplies stdin; `run` and standalone binaries inherit
the process streams. Host readers/writers without an errno map failures to `EIO`.
They must obey Rust's `Read`/`Write` contracts. Reference evaluation spends one
computation-budget unit per read/write attempt so endless interruptions produce
a diagnostic. A blocking host read itself is not interruptible by that budget.

Tests cover native/reference agreement, raw bytes, exact and exceeded capacity,
zero capacity, initialized prefixes, reversed Result tags, descriptor failures,
broken pipes, CLI stdin forwarding, and resource cleanup. Injected reference
streams additionally exercise interrupted/short transfers and failures after
partial progress. Native normal-exit allocation checks remain enabled.

General filesystem access, stderr capabilities, polling, seek,
fallible buffer allocation, stream ownership/close protocols, portable error
enums, async, and proof-driven capacity checks are deferred.


## Interactive line input

`IO.read_line(input, buffer)` consumes an existing bounded byte buffer and
appends through the next newline (including that newline) or EOF. It never
reads beyond the newline. An empty successful buffer means EOF when the input
buffer was initially empty; an empty line contains one newline byte. A final
line without a newline succeeds. CRLF is preserved for the caller to trim.

Like `read_all`, this operation does not allocate, grow, or suspend. It retries
interrupted reads and frees the consumed buffer on failure. A line exceeding
capacity returns `Err(27)` after consuming one excess byte; callers must not
assume the rest of that line has been drained. A newline needs a byte of capacity
too. Native and reference implementations read one byte at a time to avoid
consuming another command. This is blocking canonical terminal input, not raw
key handling or scheduler-aware I/O.

The [todo terminal app](../examples/todo.kush) uses it to process commands on
Enter without waiting for EOF. See [todo usage](todo.md).

## Reusable chunked input

`IO.read_chunk(input: Stdin, buffer: Bytes) -> Result<Bytes, i64> ! {io}`
appends the result of one successful read to the buffer's initialized prefix.
It retries `EINTR`, but a successful short read returns immediately. It never
reads beyond available capacity and never performs an excess-byte probe. A full
buffer (including zero capacity) returns `Err(27)` without reading input.
Failures consume and free the buffer. Neither growth nor allocation nor task
suspension is added; the operation can still block on the OS stream.

A short read is not EOF. With an initially empty buffer, an empty successful
result indicates EOF. If a prefix is supplied, compare lengths instead.
`Bytes.clear(buffer)` resets initialized length to zero while preserving the
same allocation and capacity, enabling repeated reads without reallocating.
Clear moves the owner, so live slice aliases prevent it. It does not securely
wipe memory. Binding-based linear `@[1]` arguments are conservatively rejected
by this operation rather than losing their consumption obligation.

[stream-copy.kush](../examples/stream-copy.kush) copies stdin to stdout with a
single 4096-byte allocation, irrespective of total input size. Its copy loop is
checked `#[noalloc]` and `#[nosuspend]`. This is a foundation for incremental
parsers and future file/stream abstractions; it does not implement nonblocking
I/O or a streaming JSON parser.
