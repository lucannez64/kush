# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 40.102 | 2552 | 13095 | 0 | 3.191 | 0.225 |
| 256 × 31 | Kush / previous reuse | 31.270 | 2560 | 1541 | 0 | 0.597 | 0.225 |
| 256 × 31 | Kush / rebuild | 38.158 | 2536 | 13241 | 0 | 3.005 | 0.216 |
| 256 × 31 | Kush / reuse | 31.531 | 2400 | 1552 | 0 | 0.581 | 0.216 |
| 256 × 31 | Rust CLIF / rebuild | 49.231 | 2964 | 24906 | 32768 | 6.485 | 0.207 |
| 256 × 31 | Rust CLIF / deliberate reuse | 41.859 | 2972 | 1098 | 512 | 0.564 | 0.207 |
| 4096 × 31 | Kush / previous rebuild | 580.715 | 6408 | 266535 | 0 | 63.982 | 3.477 |
| 4096 × 31 | Kush / previous reuse | 413.881 | 6476 | 24581 | 0 | 9.532 | 3.477 |
| 4096 × 31 | Kush / rebuild | 515.472 | 6240 | 266681 | 0 | 60.046 | 3.351 |
| 4096 × 31 | Kush / reuse | 370.839 | 6216 | 24592 | 0 | 9.283 | 3.350 |
| 4096 × 31 | Rust CLIF / rebuild | 777.445 | 6516 | 397386 | 524288 | 103.678 | 3.283 |
| 4096 × 31 | Rust CLIF / deliberate reuse | 506.137 | 6356 | 16458 | 8192 | 8.928 | 3.283 |
| 16384 × 31 | Kush / previous rebuild | 1200.692 | 19460 | 1077543 | 0 | 258.513 | 13.884 |
| 16384 × 31 | Kush / previous reuse | 956.773 | 19308 | 98309 | 0 | 38.126 | 13.883 |
| 16384 × 31 | Kush / rebuild | 1140.114 | 18460 | 1077689 | 0 | 242.577 | 13.382 |
| 16384 × 31 | Kush / reuse | 788.115 | 18424 | 98320 | 0 | 37.126 | 13.382 |
| 16384 × 31 | Rust CLIF / rebuild | 1819.956 | 18160 | 1589322 | 2097152 | 414.693 | 13.127 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 1149.471 | 18016 | 65610 | 32768 | 35.693 | 13.127 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2256 | 2628 | 2844 | 2824 | 2824 | 2824 |
| 256 | Kush / previous reuse | 2260 | 2632 | 2848 | 2828 | 2828 | 2828 |
| 256 | Kush / rebuild | 2296 | 2660 | 2872 | 2856 | 2856 | 2856 |
| 256 | Kush / reuse | 2276 | 2648 | 2856 | 2844 | 2844 | 2844 |
| 256 | Rust CLIF / rebuild | 2652 | 2760 | 2976 | 2904 | 2904 | 2904 |
| 256 | Rust CLIF / deliberate reuse | 2604 | 2712 | 2912 | 2852 | 2852 | 2852 |
| 4096 | Kush / previous rebuild | 2260 | 3444 | 6900 | 3640 | 3640 | 3640 |
| 4096 | Kush / previous reuse | 2296 | 3480 | 6936 | 3676 | 3676 | 3676 |
| 4096 | Kush / rebuild | 2248 | 3340 | 6668 | 3532 | 3532 | 3532 |
| 4096 | Kush / reuse | 2276 | 3332 | 6660 | 3524 | 3524 | 3524 |
| 4096 | Rust CLIF / rebuild | 2604 | 3348 | 6564 | 3268 | 3268 | 3268 |
| 4096 | Rust CLIF / deliberate reuse | 2604 | 3348 | 6548 | 3260 | 3260 | 3260 |
| 16384 | Kush / previous rebuild | 2184 | 5964 | 19788 | 5772 | 5772 | 5772 |
| 16384 | Kush / previous reuse | 2260 | 6040 | 19864 | 5848 | 5848 | 5848 |
| 16384 | Kush / rebuild | 2288 | 5556 | 18868 | 5360 | 5360 | 5360 |
| 16384 | Kush / reuse | 2288 | 5556 | 18868 | 5360 | 5360 | 5360 |
| 16384 | Rust CLIF / rebuild | 2564 | 5324 | 18184 | 4612 | 4612 | 4612 |
| 16384 | Rust CLIF / deliberate reuse | 2604 | 5368 | 18168 | 4608 | 4608 | 4608 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
