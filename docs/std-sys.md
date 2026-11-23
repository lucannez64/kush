# `std.sys`: host calls as library code

IO is moving out of the compiler and into std, the way Rust's `std::sys` or
OCaml's `external` primitives work (plan nodes STD-SYS-FOREIGN through
HOST-BUILTINS-REMOVE). The compiler keeps one mechanism, foreign calls; std
builds files, streams and the environment on top of it in Kush.

[`std.sys`](../crates/kush/std/sys.kush) declares the runtime's `kush_sys_*`
stubs as ordinary `foreign` functions. Each stub makes one system call and
returns the positive errno as `Err`, including `EINTR`, so retries, write
loops and path policy are Kush code in the modules above it. Paths are passed
as `&Bytes` and copied into a C string by the stub (a path containing a NUL
byte is `EINVAL`).

Kush has no raw pointers and cannot read `errno`, so std cannot call libc's
`read`/`open` directly; the stubs are the smallest layer that turns the C
convention (return -1, set `errno`) into the bridge ABI (status plus out slot).

## Access rules

- Every stub needs the `io` effect except `kush_sys_cpu_features`
  (`std.cpu`), whose answer is fixed for the whole run.

- Only a std module may declare a `foreign "kush_sys_..."` function. A root
  file cannot be named under `std` at all (the loader rejects it), and the
  checker never counts the root unit as std either.
- Only std may call one. A program can `use std.sys` for its constants but a
  call to `sys.close(...)` is rejected; programs use `std.file` and the other
  safe modules.
- `kush build --lib` accepts `kush_sys_*` imports, since the runtime ships in
  the archive.

## Reading into a buffer (FOREIGN-BYTES-FILL)

A `kush_sys_*` import may take an owned `Bytes` (user foreign functions still
cannot). `sys.read(fd, buffer, length, offset)` makes one `read`/`pread` into
the buffer's spare capacity and returns it through `Result<Bytes, i64>` with
its length advanced, or frees it on failure, like the `FS.read_at` builtin.
Because a failed call loses the buffer, this stub retries `EINTR` itself.

## Reference evaluator (EVAL-FOREIGN-SHIMS)

`kush eval` runs `kush_sys_*` calls through a shim table in `eval.rs`, keyed
by symbol like Miri's foreign-function shims. Descriptors share the
evaluator's never-reused file table with `FS.open`, so a stale descriptor is
`EBADF`. Any other foreign call is still rejected there.

## Status

Declared: `openat`, `close`, `fsync`, `ftruncate`, `fstat_size`, `read`
(`pread` when `offset >= 0`), `probe` (read and discard one byte), `write`
(`pwrite` when `offset >= 0`), `unlink`, `mkdir`, `rmdir`, `rename`, `stat`
(mode or size), `opendir`/`readdir`/`closedir`, plus open flags and
`st_mode` constants; `argc`/`argv`, `environ_count`/`getenv`,
`clock_gettime` (realtime or monotonic, seconds or nanoseconds),
`nanosleep` (resumes after EINTR with the time left) and `strerror`.
`readdir` skips `.` and `..` and appends `name\n`, so a
listing needs no allocation or panic effect.

[`std.file`](../crates/kush/std/file.kush) is written over these calls: its
EINTR retries, full-length read and write loops and the `sync_dir` open,
fsync, close sequence are Kush code, and its arithmetic wraps only behind
guards, so the public signatures still need only `io`.

[`std.fs`](../crates/kush/std/fs.kush) has every path-based `FS.*` call
(`read`, `write`, `write_exclusive`, `append`, `remove`, `mkdir`,
`remove_dir`, `rename`, `list`, `is_file`, `is_dir`, `exists`, `size`,
`sync_dir`) with the same signatures and errno results, as Kush code. Tests
run the `FS.*` test programs with `FS.` replaced by `fs.` and require the
same output as the builtins in both backends.

[`std.env`](../crates/kush/std/env.kush) (`arg_count`, `arg`, `var_count`,
`var`), [`std.time`](../crates/kush/std/time.kush) (`unix_seconds`,
`monotonic_ns`, `sleep_ms`) and [`std.os`](../crates/kush/std/os.kush)
(`strerror`) replace `ENV.*`, `TIME.*` and `OS.*` the same way. These were
already thin, so they are mostly one call each; what changes is that they
go through the foreign mechanism instead of compiler special cases. The
reference evaluator's shims read the injected `Host` arguments, environment
and clock origin, so `Host::new` tests stay deterministic.

[`std.io`](../crates/kush/std/io.kush) replaces `IO.*`: `io.stdin()`,
`io.stdout()`, `read_all`, `read_line` (one byte per read, so the next line
stays unread), `read_chunk` and `write`, as loops over `sys.read`,
`sys.probe` and `sys.write`. Its handle types are `io.Input` and
`io.Output`, because `Stdin`/`Stdout` are still reserved builtin type
names. Unlike the builtins, which accept any conventional `Result`
declaration, `std.io` returns `std.result.Result`. In the reference
evaluator descriptor 0 reads the injected input and 1 writes the output;
`io.stdin()` goes through a `kush_sys_stdin` call so the evaluator still
buffers standard input only for programs that can read it.

[`std.proc`](../crates/kush/std/proc.kush) and
[`std.net`](../crates/kush/std/net.kush) replace `PROC.run` and
`NET.tcp_exchange` (STD-PROC-NET-IN-KUSH). The stubs below each do one
thing; the poll loops, the shared timeout budget (`time.deadline_ms` and
`time.remaining_ms`, over a millisecond `clock_gettime` field), partial
sends, the bounded capture with its one-byte overflow probe, and the
kill-and-reap cleanup are Kush code:

- `pipe` (both ends packed in one `i64`), `spawn` (fork and `execvp`,
  stdout on a given descriptor; it waits for the exec on a close-on-exec
  report pipe, so a missing program is `Err(ENOENT)` from the call itself),
  `wait` (blocking or not, decoded to the exit status or 128 + signal) and
  `kill`;
- `poll` on one descriptor, `resolve`/`resolve_free` (a `getaddrinfo` list as
  a handle), `connect` (one address of the list, with its own timeout,
  leaving the socket in blocking mode), `send` (never blocks, no `SIGPIPE`)
  and `shutdown`. Reads go through the existing `read` and `probe`.

Since the std versions take the buffer by value instead of `&mut Bytes`,
they return an `Outcome`: `Exited(output, status)` or `Received(response,
count)`; `Stopped(buffer, errno)` for a timeout, an overflow or another
failure after the start, with the filled prefix kept; `Failed(errno)` when
nothing was started, or a read failed and freed the buffer. `std.http` now
uses `std.net`. In the evaluator a pipe is a buffer filled by a thread that
copies the child's stdout, so `poll` can wait on it with a timeout without
any unsafe code; a socket's readability is a `peek` under a read timeout,
and its writes block.

### Server sockets (WEB-NET)

`std.net` also has the server side: a linear `Listener` from `listen(host,
port, backlog, reuse_port)` (SO_REUSEADDR always, SO_REUSEPORT on request;
port 0 picks one, `local_port` tells which), `accept` with a timeout, and a
linear `Conn` from `accept` or `connect`, with `read` (one read of what is
there, after a wait with the timeout), `write` (all of it, waiting on
EAGAIN), `shutdown`, `set_nodelay` and `close`. Their waits go through the
task reactor (WEB-REACTOR, [async.md](async.md)): `wait_ready`,
`connect_start`/`connect_finish`, and a nonblocking listener. The new stubs are
`socket` (for one address of a resolved list), `setsockopt` (int values),
`bind`, `listen`, `accept` (accept4, close-on-exec) and `local_port`
(getsockname). Timeouts are waits with deadlines, not
SO_RCVTIMEO/SO_SNDTIMEO.

In the evaluator, Rust's std has no unbound socket, so `socket` and `bind`
only record the address and `listen` binds and listens at once; SO_REUSEPORT
is ignored (a second listener on a port is EADDRINUSE there); `poll` on a
listener tries a nonblocking accept every 2 ms and keeps what it accepts for
the next `accept`. Tests: `crates/kush/tests/web_net.rs` (a server and a
client in one program on both backends, a native server answering a Rust
client, SO_REUSEPORT natively, linearity).

### UDP

`net.udp_send(host, port, data)` sends `data` as one datagram from a fresh
socket to the first address of `host` that takes it, and returns the byte
count or the errno (EMSGSIZE for a datagram too large). Its stubs are
`resolve_udp` (getaddrinfo with SOCK_DGRAM; `socket` takes the type from the
list, so the same stub makes the datagram socket) and `sendto` (one
nonblocking sendto to an address of the list). The EINTR retry, the wait on
EAGAIN, the address loop and the close are Kush code. In the evaluator,
`socket` on a `resolve_udp` list binds a Rust `UdpSocket` to an ephemeral
port of the address's family. `net.udp_broadcast` is the same with
SO_BROADCAST set on the socket first (`setsockopt`; the evaluator maps it to
`UdpSocket::set_broadcast`), which Linux requires before sending to a
broadcast address such as 192.168.1.255; `udp_send` gets EACCES there.
`net.udp_send6(host, port, data, address)` sends over IPv6 only and appends
the address it used, as text, to the `address` buffer. Its stubs are
`resolve_udp6` (getaddrinfo with AF_INET6 and no AI_V4MAPPED, so a name
without an AAAA record or an IPv4 literal is EINVAL; the evaluator filters
Rust's results to IPv6) and `address_text` (inet_ntop into an owned buffer,
freed on failure, like `strerror`). `net.udp_route_source(host, port,
address)` sends nothing: it connects a UDP socket (with SO_BROADCAST, which
Linux requires to connect to a broadcast address) and appends the local
address the route leaves from, so a program can tell which network it is
on. Its stubs are `connect_to` (one connect(2) of an existing socket) and
`local_address` (getsockname and inet_ntop into an owned buffer). In the
evaluator `connect_to` works on UDP sockets only (EOPNOTSUPP on an unbound
TCP socket, which Rust's std cannot connect). There is no receive side yet. Tests:
`crates/kush/tests/std_net_udp.rs` (IPv4 and IPv6 loopback and the error
cases, both backends).

Not yet: the `IO.*`, `FS.*`, `ENV.*`, `TIME.*`, `OS.*`, `PROC.*` and `NET.*`
builtins still exist next to their std modules; removal is
HOST-BUILTINS-REMOVE. Tests: `crates/kush/tests/std_proc_net.rs` (each
scenario through the builtin and std, both backends),
`crates/kush/tests/std_sys.rs`, `crates/kush/tests/std_file.rs`,
`crates/kush/tests/host_api.rs` (`std_fs_*`, `std_env_*`, `std_time_*`),
`crates/kush/tests/native_stdio.rs` (every program also runs through
`std.io`).
