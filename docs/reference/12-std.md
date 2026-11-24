# 12. Standard library

The standard library is written in Kush (`crates/kush/std/`) and embedded in
the compiler; import modules with `use std.name;`. There is no prelude:
`Option` and `Result` are imported too. Builtins that are not modules
(`Vec`, `Box`, `Bytes`, `String`, `Slice`, `Str`, `Int`, `Float`, `Char`,
`Task`, `Thread`, `Atomic`, `Channel`, `Arena`, `DynArray`, the `print_*`
functions) are described in the chapters above.

Planned (FND-STD-*): mutating `&mut` methods as the default for collections,
a text API on `&str` with string equality, and typed errors instead of `i64`
codes.

| Module | Contents |
| --- | --- |
| `std.option`, `std.result` | `Option<T>`, `Result<T, E>`, `unwrap_or` |
| `std.io` | standard input and output: `stdin`, `stdout`, `read_all`, `read_line`, `read_chunk`, `write` |
| `std.fs`, `std.file`, `std.path` | path-based filesystem calls, open files with positioned I/O, byte-path helpers |
| `std.env`, `std.os`, `std.proc`, `std.time` | arguments and environment, OS error messages, subprocesses, clocks and sleeping |
| `std.net`, `std.http`, `std.http1`, `std.url`, `std.web` | TCP (`Listener`, `Conn`), a minimal HTTP client, HTTP/1.1 parsing, URL decoding, the web server core |
| `std.sys` | thin Linux system calls used by the modules above |
| `std.task` | `TaskExit<T>`, `Panic` |
| `std.text`, `std.ascii` | byte-string helpers (`eq`, `find`, `split_part`, `trim`, `parse_i64`, `format_i64`, …) and ASCII classes |
| `std.json` | owned JSON values, parser and writer |
| `std.bytemap`, `std.collections`, `std.sort` | a hash map from byte keys, fixed-capacity sets/maps over arrays, sorting and binary search |
| `std.math`, `std.natural`, `std.random` | `min`/`max`/`abs`, arbitrary-precision naturals, OS random bytes |
| `std.sha1`, `std.sha256`, `std.hmac`, `std.base64`, `std.crc32`, `std.ct` | hashing, MACs, encodings, checksums, constant-time comparison |
| `std.simd`, `std.x86`, `std.cpu` | vector types and operations, x86 SHA intrinsics, CPU feature tokens |
| `std.test` | `is_true`, `is_false`, `equal_i64`, `fail` |

Errors in std are mostly `Result<T, i64>` with an errno-style code.

```kush eval
use std.text;
use std.result.Result;

fn main() -> Unit ! {io, alloc} {
    let input = Bytes.from("  42 ");
    let trimmed = text.trim(&input);
    match text.parse_i64(&trimmed) {
        Result.Ok(n) => print_i64(n),
        Result.Err(code) => print_i64(-code),
    }
}
```

```output
42
```
