# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / rebuild | 13.208 | 2576 | 1552 | 0 | 0.635 | 0.280 |
| 256 × 31 | Kush / reuse | 12.858 | 2548 | 1546 | 0 | 0.634 | 0.279 |
| 256 × 31 | Rust CLIF / rebuild | 18.201 | 2948 | 24906 | 32768 | 6.485 | 0.207 |
| 256 × 31 | Rust CLIF / deliberate reuse | 15.557 | 2900 | 1098 | 512 | 0.564 | 0.207 |
| 4096 × 31 | Kush / rebuild | 168.442 | 7272 | 104513 | 0 | 46.712 | 4.440 |
| 4096 × 31 | Kush / reuse | 152.065 | 7068 | 24587 | 0 | 10.127 | 4.440 |
| 4096 × 31 | Rust CLIF / rebuild | 251.830 | 6440 | 397386 | 524288 | 103.678 | 3.283 |
| 4096 × 31 | Rust CLIF / deliberate reuse | 193.525 | 6456 | 16458 | 8192 | 8.928 | 3.283 |
| 16384 × 31 | Kush / rebuild | 811.408 | 21824 | 835946 | 0 | 254.296 | 16.252 |
| 16384 × 31 | Kush / reuse | 636.375 | 21484 | 98315 | 0 | 40.502 | 16.252 |
| 16384 × 31 | Rust CLIF / rebuild | 1101.439 | 18176 | 1589322 | 2097152 | 414.693 | 13.127 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 808.492 | 18020 | 65610 | 32768 | 35.693 | 13.127 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / rebuild | 2276 | 2672 | 2900 | 2900 | 2900 | 2900 |
| 256 | Kush / reuse | 2304 | 2700 | 2928 | 2928 | 2928 | 2928 |
| 256 | Rust CLIF / rebuild | 2548 | 2656 | 2912 | 2840 | 2840 | 2840 |
| 256 | Rust CLIF / deliberate reuse | 2604 | 2712 | 2912 | 2852 | 2852 | 2852 |
| 4096 | Kush / rebuild | 2288 | 3824 | 7552 | 7552 | 7552 | 7552 |
| 4096 | Kush / reuse | 2280 | 3816 | 7464 | 7464 | 7464 | 7464 |
| 4096 | Rust CLIF / rebuild | 2608 | 3352 | 6568 | 3272 | 3272 | 3272 |
| 4096 | Rust CLIF / deliberate reuse | 2636 | 3380 | 6580 | 3292 | 3292 | 3292 |
| 16384 | Kush / rebuild | 2260 | 7448 | 22168 | 12888 | 12888 | 12888 |
| 16384 | Kush / reuse | 2280 | 7468 | 22060 | 12916 | 12916 | 12916 |
| 16384 | Rust CLIF / rebuild | 2668 | 5432 | 18248 | 4676 | 4676 | 4676 |
| 16384 | Rust CLIF / deliberate reuse | 2656 | 5416 | 18216 | 4656 | 4656 | 4656 |

Phase RSS values are single diagnostic snapshots, not medians. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
