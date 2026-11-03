# JSON document editor: memory and allocation benchmark

Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.

| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 × 31 | Kush / previous rebuild | 51.611 | 2452 | 12846 | 0 | 3.286 | 0.229 |
| 256 × 31 | Kush / previous reuse | 48.216 | 2400 | 1290 | 0 | 0.603 | 0.228 |
| 256 × 31 | Kush / rebuild | 51.509 | 2416 | 12839 | 0 | 3.185 | 0.220 |
| 256 × 31 | Kush / reuse | 47.551 | 2456 | 1286 | 0 | 0.590 | 0.219 |
| 256 × 31 | Rust CLIF / rebuild | 69.906 | 2968 | 16698 | 32768 | 6.362 | 0.205 |
| 256 × 31 | Rust CLIF / deliberate reuse | 60.133 | 2840 | 826 | 512 | 0.561 | 0.205 |
| 16384 × 31 | Kush / previous rebuild | 2985.423 | 17016 | 1061166 | 0 | 266.361 | 14.010 |
| 16384 × 31 | Kush / previous reuse | 2315.278 | 17100 | 81930 | 0 | 38.502 | 14.010 |
| 16384 × 31 | Kush / rebuild | 2991.384 | 16520 | 1061159 | 0 | 258.138 | 13.509 |
| 16384 × 31 | Kush / reuse | 2307.707 | 16584 | 81926 | 0 | 37.750 | 13.508 |
| 16384 × 31 | Rust CLIF / rebuild | 3597.098 | 16372 | 1065018 | 2097152 | 406.818 | 13.002 |
| 16384 × 31 | Rust CLIF / deliberate reuse | 3077.651 | 16344 | 49210 | 32768 | 35.568 | 13.002 |

Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.

## Phase RSS (separate uninstrumented phase probe)

| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 256 | Kush / previous rebuild | 2292 | 2664 | 2860 | 2860 | 2860 | 2860 |
| 256 | Kush / previous reuse | 2264 | 2636 | 2828 | 2828 | 2828 | 2828 |
| 256 | Kush / rebuild | 2296 | 2660 | 2864 | 2864 | 2864 | 2864 |
| 256 | Kush / reuse | 2276 | 2640 | 2832 | 2832 | 2832 | 2832 |
| 256 | Rust CLIF / rebuild | 2576 | 2704 | 2908 | 2852 | 2852 | 2852 |
| 256 | Rust CLIF / deliberate reuse | 2556 | 2664 | 2844 | 2804 | 2804 | 2804 |
| 16384 | Kush / previous rebuild | 2196 | 5848 | 17384 | 5276 | 5276 | 5276 |
| 16384 | Kush / previous reuse | 2292 | 5944 | 17476 | 5368 | 5368 | 5368 |
| 16384 | Kush / rebuild | 2272 | 5412 | 16968 | 5092 | 5092 | 5092 |
| 16384 | Kush / reuse | 2272 | 5412 | 16956 | 5092 | 5092 | 5092 |
| 16384 | Rust CLIF / rebuild | 2604 | 4980 | 16572 | 15544 | 15544 | 15544 |
| 16384 | Rust CLIF / deliberate reuse | 2604 | 4980 | 16536 | 4092 | 4092 | 4092 |

Phase RSS values are medians of three independent diagnostic runs; every raw phase frame is retained. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction.
