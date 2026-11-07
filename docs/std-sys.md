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

## Status

Declared: `openat`, `close`, `fsync`, `ftruncate`, `fstat_size`, `write`
(`pwrite` when `offset >= 0`), `unlink`, `mkdir`, `rmdir`, `rename`, `stat`
(mode or size), plus open flags and `st_mode` constants.

Not yet: reads into a buffer's spare capacity (FOREIGN-BYTES-FILL), the
reference evaluator still rejects foreign calls (EVAL-FOREIGN-SHIMS), and the
`IO.*`/`FS.*`/`ENV.*` builtins are still compiler builtins until std is
rewritten over these calls. Tests: `crates/kush/tests/std_sys.rs`.
