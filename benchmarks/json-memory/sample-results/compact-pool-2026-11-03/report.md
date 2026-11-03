# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 50.338 | 2572 | 1552 | 0 | 0.635 | 0.280 |
| 256 × 31 | Kush / previous reuse | 47.845 | 2556 | 1546 | 0 | 0.634 | 0.279 |
| 256 × 31 | Kush / rebuild | 53.689 | 2660 | 13102 | 0 | 3.294 | 0.237 |
| 256 × 31 | Kush / reuse | 47.625 | 2588 | 1546 | 0 | 0.611 | 0.236 |
| 256 × 31 | Rust CLIF / rebuild | 69.354 | 2900 | 24906 | 32768 | 6.485 | 0.207 |
| 256 × 31 | Rust CLIF / deliberate reuse | 58.079 | 2912 | 1098 | 512 | 0.564 | 0.207 |
| 4096 × 31 | Kush / previous rebuild | 721.474 | 7156 | 104513 | 0 | 46.712 | 4.440 |
| 4096 × 31 | Kush / previous reuse | 574.927 | 7028 | 24587 | 0 | 10.127 | 4.440 |
| 4096 × 31 | Kush / rebuild | 763.375 | 6660 | 266542 | 0 | 66.048 | 3.635 |
| 4096 × 31 | Kush / reuse | 572.668 | 6644 | 24586 | 0 | 9.751 | 3.635 |
| 4096 × 31 | Rust CLIF / rebuild | 994.433 | 6456 | 397386 | 524288 | 103.678 | 3.283 |
| 4096 × 31 | Rust CLIF / deliberate reuse | 729.702 | 6456 | 16458 | 8192 | 8.928 | 3.283 |
| 16384 × 31 | Kush / previous rebuild | 3033.885 | 21808 | 835946 | 0 | 254.296 | 16.252 |
| 16384 × 31 | Kush / previous reuse | 2318.525 | 21580 | 98315 | 0 | 40.502 | 16.252 |
| 16384 × 31 | Kush / rebuild | 3052.115 | 20372 | 1077550 | 0 | 266.860 | 14.510 |
| 16384 × 31 | Kush / reuse | 2284.350 | 20296 | 98314 | 0 | 39.001 | 14.510 |
| 16384 × 31 | Rust CLIF / rebuild | 4048.240 | 18076 | 1589322 | 2097152 | 414.693 | 13.127 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 2905.153 | 18068 | 65610 | 32768 | 35.693 | 13.127 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2276 | 2672 | 2900 | 2900 | 2900 | 2900 |
| 256 | Kush / previous reuse | 2276 | 2672 | 2900 | 2900 | 2900 | 2900 |
| 256 | Kush / rebuild | 2276 | 2660 | 2880 | 2856 | 2856 | 2856 |
| 256 | Kush / reuse | 2192 | 2576 | 2796 | 2772 | 2772 | 2772 |
| 256 | Rust CLIF / rebuild | 2668 | 2776 | 2992 | 2920 | 2920 | 2920 |
| 256 | Rust CLIF / deliberate reuse | 2584 | 2692 | 2892 | 2832 | 2832 | 2832 |
| 4096 | Kush / previous rebuild | 2268 | 3804 | 7532 | 7532 | 7532 | 7532 |
| 4096 | Kush / previous reuse | 2276 | 3812 | 7460 | 7460 | 7460 | 7460 |
| 4096 | Kush / rebuild | 2272 | 3616 | 7136 | 3812 | 3812 | 3812 |
| 4096 | Kush / reuse | 2192 | 3536 | 7056 | 3732 | 3732 | 3732 |
| 4096 | Rust CLIF / rebuild | 2668 | 3412 | 6628 | 3332 | 3332 | 3332 |
| 4096 | Rust CLIF / deliberate reuse | 2608 | 3396 | 6596 | 3308 | 3308 | 3308 |
| 16384 | Kush / previous rebuild | 2280 | 7468 | 22188 | 12908 | 12908 | 12908 |
| 16384 | Kush / previous reuse | 2272 | 7460 | 22052 | 12908 | 12908 | 12908 |
| 16384 | Kush / rebuild | 2276 | 6696 | 20776 | 6376 | 6376 | 6376 |
| 16384 | Kush / reuse | 2188 | 6608 | 20688 | 6288 | 6288 | 6288 |
| 16384 | Rust CLIF / rebuild | 2608 | 5368 | 18184 | 4612 | 4612 | 4612 |
| 16384 | Rust CLIF / deliberate reuse | 2608 | 5368 | 18168 | 4608 | 4608 | 4608 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
