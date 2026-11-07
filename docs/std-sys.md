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

- Only a std module may declare a `foreign "kush_sys_..."` function. The root
  file never counts as std, even if it is named `std.x`.
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

Not yet: the `IO.*`, `FS.*`, `ENV.*`, `TIME.*` and `OS.*` builtins still
exist next to their std modules; `PROC.*` and `NET.*` are still compiler
builtins only (STD-PROC-NET-IN-KUSH); removal is HOST-BUILTINS-REMOVE. Tests:
`crates/kush/tests/std_sys.rs`, `crates/kush/tests/std_file.rs`,
`crates/kush/tests/host_api.rs` (`std_fs_*`, `std_env_*`, `std_time_*`),
`crates/kush/tests/native_stdio.rs` (every program also runs through
`std.io`).
