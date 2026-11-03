# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 42.248 | 2440 | 12839 | 0 | 3.185 | 0.220 |
| 256 × 31 | Kush / previous reuse | 40.047 | 2392 | 1286 | 0 | 0.590 | 0.219 |
| 256 × 31 | Kush / rebuild | 46.572 | 2456 | 12983 | 0 | 2.998 | 0.210 |
| 256 × 31 | Kush / reuse | 38.997 | 2408 | 1295 | 0 | 0.575 | 0.210 |
| 256 × 31 | Rust CLIF / rebuild | 61.946 | 2928 | 16698 | 32768 | 6.362 | 0.205 |
| 256 × 31 | Rust CLIF / deliberate reuse | 44.164 | 2776 | 826 | 512 | 0.561 | 0.205 |
| 4096 × 31 | Kush / previous rebuild | 538.230 | 5868 | 262439 | 0 | 63.888 | 3.384 |
| 4096 × 31 | Kush / previous reuse | 374.392 | 5764 | 20486 | 0 | 9.438 | 3.383 |
| 4096 × 31 | Kush / rebuild | 507.597 | 5708 | 262583 | 0 | 59.952 | 3.257 |
| 4096 × 31 | Kush / reuse | 395.968 | 5704 | 20495 | 0 | 9.188 | 3.257 |
| 4096 × 31 | Rust CLIF / rebuild | 714.188 | 6000 | 266298 | 524288 | 101.709 | 3.252 |
| 4096 × 31 | Rust CLIF / deliberate reuse | 509.162 | 6000 | 12346 | 8192 | 8.896 | 3.252 |
| 16384 × 31 | Kush / previous rebuild | 2019.638 | 16500 | 1061159 | 0 | 258.138 | 13.509 |
| 16384 × 31 | Kush / previous reuse | 1333.497 | 16500 | 81926 | 0 | 37.750 | 13.508 |
| 16384 × 31 | Kush / rebuild | 1929.043 | 16064 | 1061303 | 0 | 242.202 | 13.007 |
| 16384 × 31 | Kush / reuse | 1316.106 | 16076 | 81935 | 0 | 36.751 | 13.007 |
| 16384 × 31 | Rust CLIF / rebuild | 2490.582 | 16344 | 1065018 | 2097152 | 406.818 | 13.002 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 1806.294 | 16372 | 49210 | 32768 | 35.568 | 13.002 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2276 | 2640 | 2844 | 2844 | 2844 | 2844 |
| 256 | Kush / previous reuse | 2272 | 2636 | 2828 | 2828 | 2828 | 2828 |
| 256 | Kush / rebuild | 2284 | 2640 | 2840 | 2840 | 2840 | 2840 |
| 256 | Kush / reuse | 2296 | 2652 | 2840 | 2840 | 2840 | 2840 |
| 256 | Rust CLIF / rebuild | 2592 | 2696 | 2908 | 2852 | 2852 | 2852 |
| 256 | Rust CLIF / deliberate reuse | 2600 | 2704 | 2884 | 2844 | 2844 | 2844 |
| 4096 | Kush / previous rebuild | 2272 | 3296 | 6204 | 3492 | 3492 | 3492 |
| 4096 | Kush / previous reuse | 2272 | 3296 | 6192 | 3492 | 3492 | 3492 |
| 4096 | Kush / rebuild | 2296 | 3192 | 6096 | 3392 | 3392 | 3392 |
| 4096 | Kush / reuse | 2200 | 3096 | 5988 | 3288 | 3288 | 3288 |
| 4096 | Rust CLIF / rebuild | 2604 | 3304 | 6228 | 3204 | 3204 | 3204 |
| 4096 | Rust CLIF / deliberate reuse | 2604 | 3252 | 6140 | 3132 | 3132 | 3132 |
| 16384 | Kush / previous rebuild | 2180 | 5320 | 16876 | 5000 | 5000 | 5000 |
| 16384 | Kush / previous reuse | 2192 | 5332 | 16876 | 5012 | 5012 | 5012 |
| 16384 | Kush / rebuild | 2296 | 4924 | 16484 | 4608 | 4608 | 4608 |
| 16384 | Kush / reuse | 2276 | 4904 | 16452 | 4580 | 4580 | 4580 |
| 16384 | Rust CLIF / rebuild | 2564 | 4944 | 16568 | 15540 | 15540 | 15540 |
| 16384 | Rust CLIF / deliberate reuse | 2600 | 4980 | 16536 | 4092 | 4092 | 4092 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
