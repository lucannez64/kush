# What proofs buy

Kush removes a runtime check when the checker proves it can never fail:
indexing and `Slice.at` / `Vec.at` / `Bytes.at` reads proved in bounds, and
`+`, `-`, `*`, `<<`, `>>` proved to stay in range. This benchmark measures
what that is worth, against the same kernels in Rust, C and Zig.

```sh
python3 benchmarks/proofs/run.py --kush /path/to/kush --zig /path/to/zig --cpu 5
```

`KUSH_KEEP_PROVED_CHECKS=1` builds any Kush program as if its proofs
removed nothing: every proof is still checked, then each operation a proof
made unchecked gets its runtime check back (`kush mir` shows the
difference). Build a program both ways to see what its proofs buy.

## Kernels

| Kernel | Size | What Kush proves |
| --- | --- | --- |
| sum | 4,096 `i64` × 200,001 | each `Slice.at` read is in bounds (loop guard) |
| stencil | 65,536 bytes × 20,001 | three `Bytes.at` reads in bounds, and `a + 2*b + c` of three `u8` values fits |
| crc32 | 65,536 bytes × 4,001 | `std.crc32`: byte reads in bounds, table index `x & 255` in bounds |
| lookup | 65,536 bytes × 20,001 | a table field typed `Vec<i64> where len >= 256`, indexed by each byte, in a function that never sees it built |
| follow | 4,096 `i64` × 200,001 | `values[j]` for a trailing index `j` that moves only past positive elements, from the invariant `j <= i` |

In every language the accumulators and the loop counter stay checked for
overflow, as Kush checks them.

| Variant | Build |
| --- | --- |
| Kush, proofs | `kush build --release --backend llvm` |
| Kush, checks kept | the same with `KUSH_KEEP_PROVED_CHECKS=1` |
| Rust, safe | `rustc -C opt-level=3 -C overflow-checks=yes`, checked indexing |
| Rust, unsafe | the same binary, `get_unchecked` / `unchecked_*` exactly where Kush proves |
| C | `clang -O2`: no bounds checks, `__builtin_add_overflow` on the accumulators |
| Zig, safe | ReleaseSafe |
| Zig, unchecked | ReleaseSafe, many-pointer reads and wrapping arithmetic where Kush proves |

All target baseline x86-64. Timing as in [../languages](../languages/README.md):
fresh processes pinned to one CPU, shuffled, two warm-ups, median of 15.

## Results

2026-11-27, Kush at 5e24b3b, tsar-bomba-2 (Ryzen 5 5500, clang 23.1.5,
rustc 1.101.0-nightly, Zig 0.17.1), median ms:

| Kernel | Kush, proofs | Kush, checks kept | Rust, safe | Rust, unsafe | C | Zig, safe | Zig, unchecked |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | **112** | 121 | 234 | 234 | 237 | 234 | 237 |
| stencil | 696 | 757 | 753 | 754 | 764 | 1069 | 692 |
| crc32 | 516 | 518 | 518 | 515 | 517 | 515 | 515 |
| lookup | 757 | 444 | 394 | 389 | 390 | 391 | 393 |
| follow | **402** | 448 | 450 | 443 | 403 | 472 | 396 |

- **follow is where a proof pays.** LLVM cannot bound the trailing index,
  so safe Rust and Zig check every `values[j]`. Kush proves it from the
  loop invariant and runs as fast as C and unchecked Zig, 10% ahead of its
  own checked build.
- **sum** no longer pays for its proof. A loop with a proved `Slice.at` is
  now given deferred overflow checks (FND-DEFER-PROVED-READS); before, it
  ran at 244 ms against 147 ms with the checks kept. Both Kush builds are
  2× ahead of every other checked build.
- **lookup** does not show what it was meant to. LLVM removes the table
  check in every checked build (safe and unsafe Rust are within 1%). Kush's
  proved and checked builds run the same seven instructions per byte. The
  1.7× gap between them is where the loop lands: in the slower binary its
  overflow branch straddles a 32-byte boundary.
- stencil: Kush with its proofs matches unchecked Zig; its loop bound and
  `i + 1` stay checked. crc32 takes the same time in every variant. Zig's
  ReleaseSafe stencil is 1.5× slower than its unchecked form.

Earlier run (Kush at 4c8fc95, before proved reads were deferred): sum 244 /
147, stencil 726 / 727, crc32 512 / 512 (proofs / checks kept).
