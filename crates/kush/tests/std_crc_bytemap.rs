//! STD-CRC32 and STD-BYTEMAP: `std.crc32` against known check values, and
//! `std.bytemap` against `std::collections::HashMap` on a pseudo-random
//! sequence of inserts, replacements and removals. Both backends must agree
//! and the evaluator must free every allocation.
use kush::executable::check;
use std::collections::HashMap;

fn agrees(source: &str) -> String {
    let output = reference(source);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(native(source), output);
    output
}

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("maps");
    kush::native::build(&program, &binary).unwrap();
    let native = std::process::Command::new(&binary).output().unwrap();
    assert_eq!(native.status.code(), Some(0));
    String::from_utf8(native.stdout).unwrap()
}

/// The reference evaluator has a step budget (10M by default) and is slower,
/// so it runs a smaller workload; native builds run a large one. Each must
/// match `expected`.
fn agrees_scaled(source: &str, small: i64, large: i64, expected: impl Fn(i64) -> String) {
    assert_eq!(
        reference(&source.replace("@N@", &small.to_string())),
        expected(small)
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(
        native(&source.replace("@N@", &large.to_string())),
        expected(large)
    );
    let _ = large;
}

#[test]
fn crc32_matches_known_values() {
    let output = agrees(
        "use std.crc32;
         fn main() -> i64 ! {io, alloc, panic} {
             let t = crc32.table();
             let d = Bytes.from(\"123456789\");
             print_int(crc32.of(&t, &d, 0, Bytes.len(&d), _));
             let e = Bytes.from(\"\");
             print_int(crc32.of(&t, &e, 0, 0, _));
             let q = Bytes.from(\"The quick brown fox jumps over the lazy dog\");
             print_int(crc32.of(&t, &q, 0, Bytes.len(&q), _));
             // In two parts, and a sub-range: constant bounds need the length.
             if Bytes.len(&d) != 9 { return 1; }
             let first = crc32.update(&t, 0, &d, 0, 4, _);
             print_int(crc32.update(&t, first, &d, 4, 9, _));
             print_int(crc32.of(&t, &d, 2, 5, _));
             0
         }",
    );
    let expected = [
        0xCBF4_3926u32,
        0,
        0x414F_A339,
        0xCBF4_3926,
        crc32_reference(b"345"),
    ];
    let expected: String = expected.iter().map(|v| format!("{v}\n")).collect();
    assert_eq!(output, expected);
}

fn crc32_reference(data: &[u8]) -> u32 {
    let mut c = !0u32;
    for &b in data {
        c ^= u32::from(b);
        for _ in 0..8 {
            c = if c & 1 == 1 {
                0xEDB8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
    }
    !c
}

#[test]
fn crc32_ranges_must_be_proved() {
    for call in [
        "crc32.of(&t, &d, 0, 10, _)",
        "crc32.of(&t, &d, 3, 2, _)",
        "crc32.of(&t, &d, -1, 2, _)",
    ] {
        let source = format!(
            "use std.crc32;
             fn main() -> i64 ! {{io, alloc, panic}} {{
                 let t = crc32.table(); let d = Bytes.from(\"123456789\");
                 print_int({call}); 0
             }}"
        );
        let error = check(&source)
            .err()
            .unwrap_or_else(|| panic!("accepted {call}"));
        assert!(error.message.contains("cannot prove"), "{error:?}");
    }
}

/// The operation sequence both sides run: a 64-bit LCG picks an operation
/// and a key among 300 (so keys repeat, are replaced and removed).
fn model(steps: i64) -> String {
    let mut map: HashMap<Vec<u8>, i64> = HashMap::new();
    let mut state: u64 = 12345;
    let mut out = String::new();
    for step in 0..steps {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = (state >> 33) as i64;
        let key = format!("k{}", r % 120).into_bytes();
        match r % 5 {
            0..=2 => {
                map.insert(key, step);
            }
            3 => {
                map.remove(&key);
            }
            _ => {
                let v = map.get(&key).copied().unwrap_or(-1);
                out.push_str(&format!("{v}\n"));
            }
        }
    }
    let total: i64 = map.values().sum();
    let key_bytes: usize = map.keys().map(Vec::len).sum();
    out.push_str(&format!("{}\n{total}\n{key_bytes}\n", map.len()));
    out
}

#[test]
fn bytemap_agrees_with_a_hash_map() {
    agrees_scaled(
        "use std.option.Option;
         use std.bytemap;
         use std.text;
         fn main() -> i64 ! {io, alloc, panic} {
             let mut map: bytemap.Map<i64> = bytemap.new(0);
             let mut state: u64 = 12345;
             let mut step = 0;
             while step < @N@ {
                 state = Int.wrapping_add(Int.wrapping_mul(state, 6364136223846793005), 1442695040888963407);
                 let r: i64 = Int.truncate(state >> 33);
                 let key = text.format_i64_into(Bytes.from(\"k\"), r % 120);
                 let op = r % 5;
                 if op <= 2 {
                     map = bytemap.insert(map, &key, step);
                 } else if op == 3 {
                     map = bytemap.remove(map, &key);
                 } else {
                     print_i64(match bytemap.get(&map, &key) { Option.Some(v) => v, Option.None => -1 });
                 }
                 drop(key);
                 step = step + 1;
             }
             // Iterate: every live entry exactly once.
             let mut values_sum = 0;
             let mut key_bytes = 0;
             let mut seen = 0;
             let mut slot = bytemap.next_slot(&map, 0);
             while slot >= 0 {
                 values_sum = values_sum + bytemap.value_at(&map, slot);
                 let k = bytemap.key_into(&map, slot, Bytes.with_capacity(8));
                 key_bytes = key_bytes + Bytes.len(&k);
                 drop(k);
                 seen = seen + 1;
                 slot = bytemap.next_slot(&map, slot + 1);
             }
             print_i64(seen);
             print_i64(values_sum);
             print_i64(key_bytes);
             drop(map);
             0
         }",
        3000,
        20000,
        model,
    );
}

#[test]
fn bytemap_holds_records_and_reclaims_removed_keys() {
    agrees_scaled(
        "use std.option.Option;
         use std.bytemap;
         use std.text;
         struct Loc { seg: i64, off: i64, len: i64 }
         fn key(i: i64) -> Bytes ! {alloc, panic} {
             // Long keys, so removals produce enough garbage to rebuild.
             text.format_i64_into(Bytes.from(\"a-long-key-prefix-so-that-removed-keys-make-enough-arena-garbage-\"), i)
         }
         fn main() -> i64 ! {io, alloc, panic} {
             let mut m: bytemap.Map<Loc> = bytemap.new(Loc { seg: 0, off: 0, len: 0 });
             let mut round = 0;
             while round < 2 {
                 let mut i = 0;
                 while i < @N@ {
                     let k = key(i);
                     m = bytemap.insert(m, &k, Loc { seg: round, off: i, len: i * 2 });
                     drop(k);
                     i = i + 1;
                 }
                 i = 0;
                 while i < @N@ {
                     if i % 5 != 0 { let k = key(i); m = bytemap.remove(m, &k); drop(k); }
                     i = i + 1;
                 }
                 round = round + 1;
             }
             let mut sum = 0;
             let mut i = 0;
             while i < @N@ {
                 let k = key(i);
                 match bytemap.get(&m, &k) {
                     Option.Some(l) => { sum = sum + l.seg * 1000000 + l.off + l.len; },
                     Option.None => {},
                 }
                 drop(k);
                 i = i + 1;
             }
             print_i64(bytemap.len(&m));
             print_i64(sum);
             print_int(bytemap.hash(&Bytes.from(\"\")));
             drop(m);
             0
         }",
        6,
        2000,
        |n| {
            // Survivors are the multiples of 5, all from the second round.
            let survivors = (0..n).filter(|i| i % 5 == 0);
            let sum: i64 = survivors.clone().map(|i| 1_000_000 + 3 * i).sum();
            format!("{}\n{sum}\n14695981039346656037\n", survivors.count())
        },
    );
}

/// EVAL-VEC-COST: element reads and writes do not copy the vector or byte
/// buffer, so the evaluator's cost per step does not grow with the length.
/// The budget is configurable and reported when exhausted.
#[test]
fn evaluator_vector_steps_do_not_scale_with_length() {
    let source = |length: i64| {
        format!(
            "fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut v: Vec<i64> = Vec.with_capacity({length});
                let mut b = Bytes.with_capacity({length});
                let mut i = 0;
                while i < {length} {{ v = Vec.push(v, i); b = Bytes.push(b, i % 256); i = i + 1; }}
                let mut sum = 0;
                let mut k = 0;
                while k < 20000 {{
                    let j = k % {length};
                    let old = Vec.get(&v, j);
                    v = Vec.set(v, j, old + 1);
                    sum = sum + Vec.len(&v) + Bytes.get(&b, j) + Bytes.len(&b);
                    k = k + 1;
                }}
                print_i64(sum % 1000003);
                print_i64(Vec.get(&v, 0));
                drop(v);
                drop(b);
                0
            }}"
        )
    };
    let expected = |length: i64| {
        let mut sum: i64 = 0;
        for k in 0..20000i64 {
            let j = k % length;
            sum += length + (j % 256) + length;
        }
        let first = 20000 / length + i64::from(20000 % length > 0);
        format!("{}\n{first}\n", sum % 1000003)
    };
    let short = std::time::Instant::now();
    assert_eq!(agrees(&source(10)), expected(10));
    let short = short.elapsed();
    let long = std::time::Instant::now();
    assert_eq!(agrees(&source(20000)), expected(20000));
    let long = long.elapsed();
    // Copying a 20000-element vector per read would take hundreds of times
    // longer; allow wide noise (native build time dominates both runs).
    assert!(
        long < short * 20 + std::time::Duration::from_secs(5),
        "{short:?} vs {long:?}"
    );

    // A small budget is exhausted with a clear error; a larger one runs.
    let mut program = check(&source(10)).unwrap();
    program.set_eval_fuel(1000);
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("budget exhausted"), "{error:?}");
    program.set_eval_fuel(kush::DEFAULT_EVAL_FUEL);
    assert_eq!(program.eval_fuel(), 10_000_000);
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
}
