# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 53.882 | 2588 | 13102 | 0 | 3.294 | 0.237 |
| 256 × 31 | Kush / previous reuse | 48.379 | 2536 | 1546 | 0 | 0.611 | 0.236 |
| 256 × 31 | Kush / rebuild | 53.386 | 2584 | 13095 | 0 | 3.191 | 0.225 |
| 256 × 31 | Kush / reuse | 47.234 | 2568 | 1541 | 0 | 0.597 | 0.225 |
| 256 × 31 | Rust CLIF / rebuild | 69.014 | 2964 | 24906 | 32768 | 6.485 | 0.207 |
| 256 × 31 | Rust CLIF / deliberate reuse | 58.312 | 2900 | 1098 | 512 | 0.564 | 0.207 |
| 16384 × 31 | Kush / previous rebuild | 3070.916 | 20276 | 1077550 | 0 | 266.860 | 14.510 |
| 16384 × 31 | Kush / previous reuse | 2294.230 | 20304 | 98314 | 0 | 39.001 | 14.510 |
| 16384 × 31 | Kush / rebuild | 3070.400 | 19392 | 1077543 | 0 | 258.513 | 13.884 |
| 16384 × 31 | Kush / reuse | 2265.701 | 19392 | 98309 | 0 | 38.126 | 13.883 |
| 16384 × 31 | Rust CLIF / rebuild | 4143.890 | 18048 | 1589322 | 2097152 | 414.693 | 13.127 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 2912.714 | 18004 | 65610 | 32768 | 35.693 | 13.127 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2196 | 2580 | 2800 | 2776 | 2776 | 2776 |
| 256 | Kush / previous reuse | 2260 | 2644 | 2864 | 2840 | 2840 | 2840 |
| 256 | Kush / rebuild | 2240 | 2628 | 2844 | 2824 | 2824 | 2824 |
| 256 | Kush / reuse | 2276 | 2648 | 2864 | 2844 | 2844 | 2844 |
| 256 | Rust CLIF / rebuild | 2668 | 2776 | 2992 | 2920 | 2920 | 2920 |
| 256 | Rust CLIF / deliberate reuse | 2608 | 2736 | 2936 | 2876 | 2876 | 2876 |
| 16384 | Kush / previous rebuild | 2276 | 6696 | 20776 | 6376 | 6376 | 6376 |
| 16384 | Kush / previous reuse | 2272 | 6692 | 20772 | 6372 | 6372 | 6372 |
| 16384 | Kush / rebuild | 2272 | 6052 | 19876 | 5860 | 5860 | 5860 |
| 16384 | Kush / reuse | 2272 | 6052 | 19876 | 5860 | 5860 | 5860 |
| 16384 | Rust CLIF / rebuild | 2608 | 5368 | 18184 | 4612 | 4612 | 4612 |
| 16384 | Rust CLIF / deliberate reuse | 2604 | 5364 | 18164 | 4604 | 4604 | 4604 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
