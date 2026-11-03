# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 20.173 | 2456 | 12839 | 0 | 3.185 | 0.220 |
| 256 × 31 | Kush / previous reuse | 17.651 | 2424 | 1286 | 0 | 0.590 | 0.219 |
| 256 × 31 | Kush / rebuild | 21.206 | 2420 | 12983 | 0 | 2.998 | 0.210 |
| 256 × 31 | Kush / reuse | 19.853 | 2436 | 1295 | 0 | 0.575 | 0.210 |
| 256 × 31 | Rust CLIF / rebuild | 25.374 | 2904 | 16698 | 32768 | 6.362 | 0.205 |
| 256 × 31 | Rust CLIF / deliberate reuse | 23.282 | 2788 | 826 | 512 | 0.561 | 0.205 |
| 4096 × 31 | Kush / previous rebuild | 287.918 | 5772 | 262439 | 0 | 63.888 | 3.384 |
| 4096 × 31 | Kush / previous reuse | 220.259 | 5836 | 20486 | 0 | 9.438 | 3.383 |
| 4096 × 31 | Kush / rebuild | 316.838 | 5708 | 262583 | 0 | 59.952 | 3.257 |
| 4096 × 31 | Kush / reuse | 242.668 | 5624 | 20495 | 0 | 9.188 | 3.257 |
| 4096 × 31 | Rust CLIF / rebuild | 340.162 | 5984 | 266298 | 524288 | 101.709 | 3.252 |
| 4096 × 31 | Rust CLIF / deliberate reuse | 282.005 | 5972 | 12346 | 8192 | 8.896 | 3.252 |
| 16384 × 31 | Kush / previous rebuild | 1101.026 | 16588 | 1061159 | 0 | 258.138 | 13.509 |
| 16384 × 31 | Kush / previous reuse | 866.743 | 16500 | 81926 | 0 | 37.750 | 13.508 |
| 16384 × 31 | Kush / rebuild | 1192.371 | 15988 | 1061303 | 0 | 242.202 | 13.007 |
| 16384 × 31 | Kush / reuse | 956.916 | 15988 | 81935 | 0 | 36.751 | 13.007 |
| 16384 × 31 | Rust CLIF / rebuild | 1314.885 | 16360 | 1065018 | 2097152 | 406.818 | 13.002 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 1101.496 | 16352 | 49210 | 32768 | 35.568 | 13.002 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2296 | 2660 | 2864 | 2864 | 2864 | 2864 |
| 256 | Kush / previous reuse | 2260 | 2624 | 2816 | 2816 | 2816 | 2816 |
| 256 | Kush / rebuild | 2284 | 2640 | 2840 | 2840 | 2840 | 2840 |
| 256 | Kush / reuse | 2272 | 2628 | 2816 | 2816 | 2816 | 2816 |
| 256 | Rust CLIF / rebuild | 2560 | 2704 | 2912 | 2856 | 2856 | 2856 |
| 256 | Rust CLIF / deliberate reuse | 2604 | 2708 | 2888 | 2848 | 2848 | 2848 |
| 4096 | Kush / previous rebuild | 2268 | 3292 | 6200 | 3488 | 3488 | 3488 |
| 4096 | Kush / previous reuse | 2272 | 3296 | 6192 | 3492 | 3492 | 3492 |
| 4096 | Kush / rebuild | 2272 | 3168 | 6072 | 3368 | 3368 | 3368 |
| 4096 | Kush / reuse | 2312 | 3208 | 6100 | 3400 | 3400 | 3400 |
| 4096 | Rust CLIF / rebuild | 2604 | 3252 | 6176 | 3152 | 3152 | 3152 |
| 4096 | Rust CLIF / deliberate reuse | 2652 | 3300 | 6188 | 3180 | 3180 | 3180 |
| 16384 | Kush / previous rebuild | 2268 | 5408 | 16964 | 5088 | 5088 | 5088 |
| 16384 | Kush / previous reuse | 2268 | 5408 | 16952 | 5088 | 5088 | 5088 |
| 16384 | Kush / rebuild | 2296 | 4924 | 16484 | 4608 | 4608 | 4608 |
| 16384 | Kush / reuse | 2192 | 4820 | 16368 | 4496 | 4496 | 4496 |
| 16384 | Rust CLIF / rebuild | 2604 | 4980 | 16572 | 15544 | 15544 | 15544 |
| 16384 | Rust CLIF / deliberate reuse | 2600 | 4976 | 16532 | 4088 | 4088 | 4088 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
