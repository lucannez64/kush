//! Length-refined fields (`name: Vec<T> where len >= N`): the bound is
//! checked once when the record is built, never broken afterwards, and lets
//! the prover compile element accesses whose index it can bound as plain
//! loads and stores. Every program runs on the reference evaluator and
//! natively (replay on LLVM with `KUSH_BACKEND=llvm`).

use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn native(program: &kush::executable::Executable, name: &str) -> std::process::Output {
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join(name);
    kush::native::build(program, &binary).unwrap();
    std::process::Command::new(&binary).output().unwrap()
}

/// Runs `source` both ways and returns `(proved, checked)` accesses.
fn agrees(source: &str, expected_status: i64, expected_output: &str) -> (usize, usize) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let output = native(&program, "length-refined-test");
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
    program.bounds_report()
}

const MEMORY: &str = r#"
    const SIZE: i64 = 0x2000;
    struct Memory { tag: u8, ram: Vec<u8> where len >= SIZE, log: Vec<u8> }
    fn zeroed(n: i64) -> Vec<u8> ! {alloc, panic} {
        let mut v: Vec<u8> = Vec.with_capacity(n);
        let mut i = 0;
        while i < n { v = v.push(0); i = i + 1; }
        v
    }
"#;

#[test]
fn guarded_accesses_are_proved_and_others_stay_checked() {
    let source = format!(
        "{MEMORY}
        fn read(m: &Memory, address: u16) -> u8 ! {{panic}} {{
            let at: i64 = Int.convert(address);
            if address < 0x8000 {{ return 0xFF; }}
            if address < 0xA000 {{ return m.ram[at - 0x8000]; }}
            0xFF
        }}
        fn write(m: &mut Memory, address: u16, value: u8) -> Unit ! {{alloc, panic}} {{
            let at: i64 = Int.convert(address);
            if address < 0x8000 {{ m.log.push(value); return; }}
            if address < 0xA000 {{ m.ram[at - 0x8000] = value; return; }}
        }}
        fn masked(m: &Memory, i: i64) -> u8 ! {{panic}} {{ m.ram[i & 0x1FFF] }}
        fn unknown(m: &Memory, i: i64) -> u8 ! {{panic}} {{ m.ram[i] }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            write(&mut m, 0x8005, 42);
            write(&mut m, 0x9FFF, 9);
            write(&mut m, 0x0100, 3);
            m.ram.push(7);
            print_i64(Int.convert(read(&m, 0x8005)));
            print_i64(Int.convert(masked(&m, 0x3FFF)));
            print_i64(Int.convert(unknown(&m, SIZE)));
            print_i64(Vec.len(&m.log));
            0
        }}"
    );
    let (proved, checked) = agrees(&source, 0, "42\n9\n7\n1\n");
    // read, write and masked are proved; `unknown` and the unrefined
    // helpers keep their checks.
    assert_eq!(proved, 3, "{source}");
    assert!(checked >= 1);
}

#[test]
fn an_out_of_range_access_still_panics() {
    let source = format!(
        "{MEMORY}
        fn unknown(m: &Memory, i: i64) -> u8 ! {{panic}} {{ m.ram[i] }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            print_i64(1);
            Int.convert(unknown(&m, SIZE))
        }}"
    );
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let error = program.evaluate(&mut output).unwrap_err();
    assert!(error.message.contains("panic"), "{error:?}");
    assert_eq!(String::from_utf8(output).unwrap(), "1\n");
}

#[test]
fn building_a_record_with_a_short_vector_panics() {
    let source = format!(
        "{MEMORY}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            print_i64(1);
            let m = Memory {{ tag: 1, ram: zeroed(SIZE - 1), log: Vec.new() }};
            print_i64(2);
            Int.convert(m.tag)
        }}"
    );
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let error = program.evaluate(&mut output).unwrap_err();
    assert!(error.message.contains("panic"), "{error:?}");
    assert_eq!(String::from_utf8(output).unwrap(), "1\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let output = native(&program, "length-refined-short");
        assert_ne!(output.status.code(), Some(0));
        assert_eq!(String::from_utf8(output.stdout).unwrap(), "1\n");
    }
}

#[test]
fn contracts_carry_ranges_into_callers() {
    // `ensures` on a helper and an erased range on a parameter let the
    // prover see through calls; a loop without `break` exits with its
    // condition false.
    let source = format!(
        "{MEMORY}
        fn wide(value: u8) -> i64 ! {{}} ensures {{ result == value }} {{ Int.convert(value) }}
        fn tile(entry: u8) -> i64 ! {{}} ensures {{ 0 <= result && result <= 0x0FF0 }} {{
            wide(entry) * 16
        }}
        fn pair(m: &Memory, at: i64, erased inside: {{ 0 <= at && at < 0x1FFF }}) -> i64 ! {{panic}} {{
            wide(m.ram[at]) + wide(m.ram[at + 1])
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            let mut i = 0;
            while i < 16 {{ m.ram[i] = Int.truncate(i); i = i + 1; }}
            print_i64(pair(&m, tile(0) + 3, _));
            print_i64(wide(m.ram[i]));
            0
        }}"
    );
    let (proved, _) = agrees(&source, 0, "7\n0\n");
    // Both reads in `pair` and the loop store. After the loop only
    // `i >= 16` is known (no upper bound), so that read stays checked.
    assert_eq!(proved, 3, "{source}");
}

#[test]
fn a_diverging_branch_does_not_hide_facts_after_it() {
    let source = format!(
        "{MEMORY}
        fn touch(m: &mut Memory) -> Unit ! {{panic}} {{ m.tag = m.tag + 1; }}
        fn store(m: &mut Memory, a: u16) -> Unit ! {{panic}} {{
            let at: i64 = Int.convert(a);
            if a < 8 {{ touch(m); return; }}
            if a < 0x2000 {{ m.ram[at] = 5; return; }}
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            store(&mut m, 3);
            store(&mut m, 9);
            print_i64(Int.convert(m.tag));
            print_i64(Int.convert(m.ram[9]));
            0
        }}"
    );
    let (proved, _) = agrees(&source, 0, "2\n5\n");
    assert_eq!(proved, 2, "{source}");
}

#[test]
fn loop_exits_keep_only_sound_facts() {
    // With a `break`, the loop may exit early: nothing about `i` is known.
    rejects(
        "fn a(n: i64) -> i64 ! {panic} ensures { result >= 10 } {
            let mut i = 0;
            while i < 10 { if i == n { break; } i = i + 1; }
            i
        }",
        "cannot prove",
    );
    // A value rewritten in a `continue` branch is not trusted afterwards.
    let source = format!(
        "{MEMORY}
        fn f(m: &Memory, c: Bool) -> i64 ! {{panic}} {{
            let mut i = 3;
            let mut n = 0;
            let mut t = 0;
            while n < 4 {{
                n = n + 1;
                if c {{ i = 0x4000; continue; }}
                t = t + Int.convert(m.ram[i]);
            }}
            t
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            f(&m, false)
        }}"
    );
    let (proved, _) = agrees(&source, 0, "");
    assert_eq!(proved, 0, "{source}");
}

#[test]
fn the_bound_cannot_be_broken() {
    let base = MEMORY;
    rejects(
        &format!(
            "{base}
            fn f(m: &mut Memory) -> Unit ! {{alloc, panic}} {{ m.ram.clear(); }}"
        ),
        "clearing it would break that",
    );
    rejects(
        &format!(
            "{base}
            fn shrink(v: &mut Vec<u8>) -> Unit ! {{}} {{ }}
            fn f(m: &mut Memory) -> Unit ! {{alloc, panic}} {{ shrink(&mut m.ram); }}"
        ),
        "cannot be borrowed with '&mut'",
    );
    rejects(
        "struct S { v: u8 where len >= 4 }
        fn main() -> i64 ! {alloc, panic} { let s = S { v: 1 }; 0 }",
        "Vec",
    );
}

const SMALL: &str = r#"
    const SIZE: i64 = 16;
    struct Memory { tag: u8, ram: Vec<u8> where len >= SIZE, log: Vec<u8> }
    fn zeroed(n: i64) -> Vec<u8> ! {alloc, panic} {
        let mut v: Vec<u8> = Vec.with_capacity(n);
        let mut i = 0;
        while i < n { v = v.push(0); i = i + 1; }
        v
    }
"#;

#[test]
fn replace_swaps_a_vector_out_of_a_place_without_copying() {
    let source = format!(
        "{SMALL}
        fn swap_in(m: &mut Memory, other: Vec<u8>) -> Vec<u8> ! {{alloc, panic}} {{
            m.ram.replace(other)
        }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            m.ram[5] = 42;
            let mut log: Vec<u8> = Vec.new();
            log = log.push(7);
            let empty = m.log.replace(log);
            let old = swap_in(&mut m, zeroed(SIZE + 1));
            print_i64(Int.convert(old[5]));
            print_i64(Vec.len(&m.ram));
            print_i64(Vec.len(&empty));
            let mut local: Vec<u8> = Vec.new();
            let previous = Vec.replace(&mut local, old);
            print_i64(Vec.len(&local) - SIZE);
            print_i64(Vec.len(&previous));
            Int.convert(m.log[0])
        }}"
    );
    agrees(&source, 7, "42\n17\n0\n0\n0\n");
    // Into a length-refined field, the incoming vector is checked.
    let short = format!(
        "{SMALL}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = Memory {{ tag: 1, ram: zeroed(SIZE), log: Vec.new() }};
            print_i64(1);
            let old = m.ram.replace(zeroed(SIZE - 1));
            print_i64(2);
            0
        }}"
    );
    let program = check(&short).unwrap();
    let mut output = Vec::new();
    let error = program.evaluate(&mut output).unwrap_err();
    assert!(error.message.contains("panic"), "{error:?}");
    assert_eq!(String::from_utf8(output).unwrap(), "1\n");
}
