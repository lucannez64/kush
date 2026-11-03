# Feature pipeline — measured results

Host: AMD Ryzen 5 PRO 5675U with Radeon Graphics

| Case | Implementation | Median wall ms | Peak RSS KiB (median) |
|---|---|---:|---:|
| n=262144, rounds=8 | Kush / automatic fusion | 43.467 | 4308 |
| n=262144, rounds=8 | Kush / fusion, contracts removed | 44.713 | 4348 |
| n=262144, rounds=8 | Kush / two passes | 45.641 | 4300 |
| n=262144, rounds=8 | Rust CLIF O3 / manual fusion | 18.139 | 4464 |
| n=262144, rounds=8 | Rust CLIF O3 / iterator chain | 51.478 | 4464 |
| n=262144, rounds=8 | Rust CLIF O3 / two passes | 21.167 | 4520 |
| n=262144, rounds=8 | Rust CLIF O0 / manual fusion | 55.894 | 4448 |
| n=2097152, rounds=4 | Kush / automatic fusion | 161.132 | 18520 |
| n=2097152, rounds=4 | Kush / fusion, contracts removed | 160.972 | 18552 |
| n=2097152, rounds=4 | Kush / two passes | 171.103 | 18628 |
| n=2097152, rounds=4 | Rust CLIF O3 / manual fusion | 60.918 | 18796 |
| n=2097152, rounds=4 | Rust CLIF O3 / iterator chain | 192.795 | 18800 |
| n=2097152, rounds=4 | Rust CLIF O3 / two passes | 73.317 | 18816 |
| n=2097152, rounds=4 | Rust CLIF O0 / manual fusion | 214.514 | 18784 |

Measurements include startup/output, use fresh processes and a pinned CPU, and exclude allocation instrumentation.
RSS is process peak residency, not live payload bytes. These results describe this workload, machine and compiler configuration only.

## Safety probes

| Case | Kush compilation | Rust compilation | Rust runtime note |
|---|---|---|---|
| use_after_move | rejected | rejected |  |
| borrow_invalidation | rejected | rejected |  |
| exclusive_alias | rejected | rejected |  |
| exact_use_grade | rejected | accepted |  |
| linear_discard | rejected | accepted | drop guard aborts |
| unauthorized_key | rejected | rejected |  |
| noalloc_violation | rejected | accepted |  |
| erased_observation | rejected | rejected |  |
| forget_ticket | no corresponding safe forget builtin in this API | accepted | exits normally; bypasses Drop guard |

## Source size (not a quality score)

{
  "Kush production": {
    "files": [
      "kush/main.kush",
      "kush/src/pipeline.kush"
    ],
    "nonblank_noncomment_lines": 76
  },
  "Rust production": {
    "files": [
      "rust/main.rs",
      "rust/pipeline.rs"
    ],
    "nonblank_noncomment_lines": 107
  },
  "Rust allocation instrumentation (excluded)": {
    "files": [
      "rust/allocation.rs"
    ],
    "nonblank_noncomment_lines": 70
  }
}

## Annotation erasure experiment

{
  "available": true,
  "hashes": {
    "kush-fused": "0d38015e010b1501c0112aa40217ca65a6f76562486cc41dbf26be2bf4bbcfee",
    "kush-plain": "0d38015e010b1501c0112aa40217ca65a6f76562486cc41dbf26be2bf4bbcfee"
  },
  "identical_text": true
}

See the project README for the fairness limits and the exact meaning of each feature.
