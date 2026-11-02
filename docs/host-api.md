# Checked host APIs

Kush now exposes a small synchronous host surface for real applications. Every
operation declares the `io` effect, returns the conventional `Result` enum, and
uses positive Linux errno values as errors. No operation constructs an owning
value behind a raw address or pretends that blocking host calls are
scheduler-aware.

The APIs are compiler builtins, not source declarations. A file using them must
declare the conventional result enum, for example with
`use std.result.Result;`. Error payloads are `i64` errno codes; `OS.strerror`
turns a code into host text and `std.text.parse_i64` rejects malformed numbers
instead of guessing.

```text
FS.read(path: &Bytes, buffer: Bytes) -> Result<Bytes, i64> ! {io}
FS.write(path: &Bytes, data: &Bytes) -> Result<i64, i64> ! {io}
FS.append(path: &Bytes, data: &Bytes) -> Result<i64, i64> ! {io}
FS.remove(path: &Bytes) -> Result<Unit, i64> ! {io}
FS.rename(from: &Bytes, to: &Bytes) -> Result<Unit, i64> ! {io}
FS.mkdir(path: &Bytes) -> Result<Unit, i64> ! {io}
FS.remove_dir(path: &Bytes) -> Result<Unit, i64> ! {io}
FS.list(path: &Bytes, buffer: Bytes) -> Result<Bytes, i64> ! {io}
FS.is_file(path: &Bytes) -> Result<Bool, i64> ! {io}
FS.is_dir(path: &Bytes) -> Result<Bool, i64> ! {io}
FS.size(path: &Bytes) -> Result<i64, i64> ! {io}
FS.exists(path: &Bytes) -> Result<Bool, i64> ! {io}

ENV.arg_count() -> Result<i64, i64> ! {io}
ENV.arg(index: i64, buffer: Bytes) -> Result<Bytes, i64> ! {io}
ENV.var_count() -> Result<i64, i64> ! {io}
ENV.var(name: &Bytes, buffer: Bytes) -> Result<Bytes, i64> ! {io}

TIME.unix_seconds() -> Result<i64, i64> ! {io}
TIME.monotonic_ns() -> Result<i64, i64> ! {io}
TIME.sleep_ms(milliseconds: i64) -> Result<Unit, i64> ! {io}

PROC.run(program: &Bytes, arguments: &Bytes, output: &mut Bytes,
         timeout_ms: i64) -> Result<i64, i64> ! {io}
NET.tcp_exchange(host: &Bytes, port: i64, request: &Bytes,
                 response: &mut Bytes, timeout_ms: i64) -> Result<i64, i64> ! {io}

OS.strerror(code: i64, buffer: Bytes) -> Result<Bytes, i64> ! {io}
```

## Filesystems, paths, and ownership

Paths and data are byte strings. Embedded NUL bytes are rejected with `EINVAL`
instead of being silently truncated at the C interface. `FS.write` creates or
truncates with mode `0666` subject to the process umask; `FS.append` creates or
appends. `FS.read` appends to the initialized prefix of the supplied buffer and
never grows storage. A file larger than the remaining capacity reports `EFBIG`
(27) and frees the consumed buffer. `FS.list` writes one entry name per line,
excluding `.` and `..`; directory order is not specified. `FS.mkdir` is one
level, not recursive.

Reads and listings consume the buffer and return it on success, so failure
destroys the buffer exactly as `IO.read_all` does. Writes only borrow their
data. Metadata calls follow symlinks. Missing entries produce `Ok(false)` for
`is_file`, `is_dir`, and `exists`; `size` returns the errno. Runtime errors are
the host's Linux errno values, for example `2` (`ENOENT`), `13` (`EACCES`), `17`
(`EEXIST`), `20` (`ENOTDIR`), `21` (`EISDIR`), and `27` (`EFBIG`).

Byte-level helpers for building and inspecting paths live in
[`std.path`](../crates/kush/std/path.kush): `basename`, `dirname`, `extension`,
`is_absolute`, and `join`. They operate on bytes and do not canonicalize,
resolve symlinks, or collapse `..`.

## Arguments and environment

Native executables read the real process arguments and environment. `argv[0]`
is the executable path, so application arguments conventionally start at index
1. The project workflow already forwards arguments after `--` unchanged through
`ProgramInvocation` (see `crates/kush/src/project/runtime.rs`); no CLI text
rewrite is needed before the native program sees them. The reference evaluator
uses an injected `Host` value:

```rust
use kush::Host;

let host = Host::process();                 // current process
// or deterministic inputs for tests/tooling:
let host = Host::new(
    vec![b"todo".to_vec(), b"list".to_vec()],
    vec![(b"KUSH_TODO_FILE".to_vec(), b"/tmp/tasks.txt".to_vec())],
);
program.evaluate_with_host(&mut input, &mut output, &host)?;
```

`evaluate`, `evaluate_with_io`, and their `_stats` forms keep using an empty
host for deterministic existing tests. A CLI that runs the interpreter should
use `Host::process()` if source code may call these builtins. Native project and
single-file `run` commands already reach the same process argv through the
generated `main(argc, argv)`.

`ENV.arg` and `ENV.var` consume a bounded output buffer and append the raw
bytes. A missing argument or variable is `ENOENT` (2); overflow is `EFBIG` (27).
Environment values are inherited; there is no API yet for setting or enumerating
individual names. `ENV.var_count` and `ENV.arg_count` are counts, not iterators.

## Clocks and timeouts

`TIME.unix_seconds` is wall-clock time and may jump. `TIME.monotonic_ns` is the
host monotonic clock and is suitable for elapsed-time checks. `TIME.sleep_ms`
blocks the calling OS thread and retries interrupted sleeps; negative durations
are `EINVAL`. Timeouts in `PROC.run` and `NET.tcp_exchange` are explicit
milliseconds; `0` means no timeout. A timed-out operation returns `ETIMEDOUT`
(110) after terminating or closing the resource it owns.

## Subprocesses

`PROC.run` starts `program` directly through `execvp` without a shell.
`arguments` is a NUL-separated byte string; empty segments and a trailing NUL
are ignored, so `/bin/echo` with `hello\0world` receives two arguments.
Arguments are passed as separate C strings; embedded NUL is the separator.
Child stdin is `/dev/null`, stderr is discarded, and stdout is appended to the
caller-owned `output` buffer up to its capacity.

On success the return value is the child exit status, or `128 + signal` when
the child was terminated by a signal. `exec` failures are reported as the
underlying errno (for example `ENOENT`) instead of being collapsed into exit
127. If output exceeds capacity, the child is killed and reaped, the buffer is
left with its filled prefix, and `EFBIG` (27) is returned. On timeout the child
is killed and reaped and the partial prefix is retained. There is no stdin
plumbing, stderr capture, process group/job control, or environment override.
Callers that need a shell must invoke one explicitly and accept its quoting
rules.

## Plain TCP and HTTP

`NET.tcp_exchange` resolves `host` with `getaddrinfo`, connects to `port`
(1-65535), sends the complete request, performs `shutdown(SHUT_WR)`, and reads
until EOF or capacity. It appends response bytes to the caller-owned `response`
buffer and returns the number of bytes received from the socket, excluding any
preexisting prefix and excluding the excess probe byte. On timeout or overflow
the filled prefix remains in the caller-owned buffer. TCP is a byte stream: one
call is not one message. The timeout applies to connect/send/receive after DNS
resolution; DNS resolution itself is blocking and not timed.

The API is explicitly blocking and one-shot. It does not expose sockets,
nonblocking mode, polling, TLS, HTTP/2, redirects, proxies, or connection reuse.
`std.http` builds a minimal HTTP/1.1 request on top of this operation and parses
the status line and header/body boundary. It has a 64 KiB response bound and
does **not** decode chunked transfer encoding or content encodings. TLS is not
implemented, so it is suitable for plain loopback/private HTTP endpoints and
test servers, not arbitrary public HTTPS.

## Standard helpers and limits

`std.text` provides byte search/count/replace/split, whitespace trimming, strict
`i64` parsing, and decimal formatting. `std.sort` provides in-place `i64`
insertion sort and binary search. `std.collections` provides fixed-capacity
integer set/map helpers over caller-owned arrays and mutable slices; capacity is
the slice length and lookup is linear. These helpers intentionally avoid hidden
allocation and do not claim hash-map performance.

The standard library currently has a frontend limitation: an `i64`-returning
function cannot use `return value;` inside a `while` loop. Returning `Bool`,
`Unit`, `Bytes`, or `Result` from those positions works. The helper modules use
explicit found/break flags instead. This is a compiler limitation, not an API
property, and is recorded here rather than hidden.

Not implemented in this pass: recursive directory trees, globbing, symlink
inspection, file descriptors or seek, append-and-sync durability, stderr
source-level access, environment mutation, socket handles, TLS, DNS timeouts,
and a nonblocking scheduler. None of the blocking calls pretend to be
cancellable by the cooperative task scheduler.

[`examples/todo-cli`](../examples/todo-cli) exercises the filesystem,
argument, environment, formatting, and project-shaped module workflow end to
end. See [the todo CLI notes](todo-cli.md).
