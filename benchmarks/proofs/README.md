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

2026-11-27, Kush at 4c8fc95 plus the switch, tsar-bomba-2 (Ryzen 5 5500,
clang 23.1.5, rustc 1.101.0-nightly, Zig 0.17.1), median ms:

| Kernel | Kush, proofs | Kush, checks kept | Rust, safe | Rust, unsafe | C | Zig, safe | Zig, unchecked |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | 244 | **147** | 247 | 240 | 239 | 246 | 236 |
| stencil | 726 | 727 | 761 | 685 | 719 | 1045 | 684 |
| crc32 | 512 | 512 | 511 | 510 | 512 | 511 | 510 |

- **The proof in `sum` makes it 1.66× slower.** A loop with a proved
  unchecked read is never given deferred overflow checks
  ([deferred-overflow.md](../../docs/deferred-overflow.md), rule 2), so the
  accumulator is checked on every element and the loop stays scalar. With
  the checks kept, the read is an ordinary checked `get`, the loop is
  deferred and vectorized, and it beats every other checked build by 1.6×.
- Elsewhere the proofs change nothing measurable: LLVM already removes these
  bounds checks from the checked code (safe and unsafe Rust differ by 1% on
  sum and crc32). On stencil Kush sits between safe and unsafe Rust (6%
  behind unsafe); its loop bound and `i + 1` stay checked, which the unsafe
  Rust and unchecked Zig forms skip.
- crc32 takes the same time in every variant.
- Zig's ReleaseSafe stencil is 1.4× slower than its unchecked form.

These kernels use the bounds facts LLVM can find for itself. Proofs should
pay where it cannot: indices read from data, or bounds carried by an
invariant across calls.
