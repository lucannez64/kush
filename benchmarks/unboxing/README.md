# Unboxing extension measurements (UNBOX-MULTI-NICHE, UNBOX-TAG-NICHE)

Best-case programs: a 4,000,000-element `Vec` scanned 20 times, built with
`kush build <file> -o <out> --release` and timed with
`/usr/bin/time -f "%e s %M KB"` (5 interleaved runs each, x86-64 Linux,
2026-11-05). Each pair computes the same result (exit codes 6 and 221).

| Program | Layout | Time | Peak RSS |
| --- | --- | --- | --- |
| `multi-niche-tagged.kush` (`enum E { A, B, Some(Bool) }`) | 2 words today | 0.37 s | 64.5 MB |
| `multi-niche-one-word.kush` (same values as one `i64` code) | 1 word, what the extension would give | 0.34 s | 33.4 MB |
| `tag-niche-three-words.kush` (`Opt { None, Some(Inner) }`, `Inner { X(i64), Y(i64) }`) | 3 words today | 0.34 s | 95.8 MB |
| `tag-niche-two-words.kush` (the same values as one 3-variant enum) | 2 words, what the extension would give | 0.32 s | 64.5 MB |

The census over the repository's Kush programs is the ignored unit test
`layout_cert::census::census_of_extension_candidates`
(`mbx test -p kush --lib layout_cert::census -- --ignored --nocapture`).
