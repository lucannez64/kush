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
(`pread` when `offset >= 0`), `write` (`pwrite` when `offset >= 0`),
`unlink`, `mkdir`, `rmdir`, `rename`, `stat` (mode or size), plus open flags
and `st_mode` constants.

[`std.file`](../crates/kush/std/file.kush) is written over these calls: its
EINTR retries, full-length read and write loops and the `sync_dir` open,
fsync, close sequence are Kush code, and its arithmetic wraps only behind
guards, so the public signatures still need only `io`.

Not yet: `IO.*`, `FS.*` (path operations, listing), `ENV.*`, `TIME.*`,
`PROC.*`, `NET.*` and `OS.*` are still compiler builtins (STD-IO-IN-KUSH,
STD-FS-IN-KUSH, STD-ENV-IN-KUSH, HOST-BUILTINS-REMOVE). Tests:
`crates/kush/tests/std_sys.rs`, `crates/kush/tests/std_file.rs`.
