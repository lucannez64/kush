//! Borrowed records: lifetime-parameterized records storing shared slice views.
//!
//! These tests exercise the complete shared-slice subset on both the reference
//! evaluator and Cranelift native execution. A borrowed record field keeps the
//! caller's storage alive through checked provenance; it never copies the
//! backing array/vector/byte buffer and never adds a runtime tag or allocation.
use kush::executable::{MemoryStats, check};

#[test]
fn owning_record_place_reads_never_create_duplicate_owners() {
    agrees(
        r#"struct P { token: Box<i64>, start: i64 }
        struct Outer { meta: P }
        fn pass(p: P) -> P ! {} { let observed = p.start; p }
        fn read(p: P) -> i64 ! {} { p.start }
        fn main() -> i64 ! {alloc, panic} {
            let p = pass(P { token: Box.new(7), start: 4 });
            let mark = p.start;
            let P { token, .. } = p;
            let first = Box.take(token) + mark;
            let outer = Outer { meta: P { token: Box.new(2), start: 3 } };
            let nested = outer.meta.start;
            let Outer { meta } = outer;
            let P { token, .. } = meta;
            let second = Box.take(token) + nested;
            let extra = P { token: Box.new(1), start: 4 };
            let temporary = extra.start;
            first + second + temporary + read(P { token: Box.new(1), start: 3 })
        }"#,
        23,
        "",
    );
}

#[test]
fn mixed_record_shared_projection_and_record_return_cleanup_agree() {
    agrees(
        r#"struct Mixed<'a> { view: &'a [i64], token: Box<i64>, start: i64 }
        fn view<'a>(m: Mixed<'a>) -> &'a [i64] ! {} { m.view }
        fn pass<'a>(m: Mixed<'a>) -> Mixed<'a> ! {} { let s = m.start; m }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [4, 5];
            let v = view(Mixed { view: &values[..], token: Box.new(1), start: 0 });
            let head = Slice.get(v, 1);
            let m = pass(Mixed { view: &values[..], token: Box.new(7), start: 3 });
            let mark = m.start;
            let observed = Slice.get(m.view, 0);
            let Mixed { token, .. } = m;
            head + mark + observed + Box.take(token)
        }"#,
        19,
        "",
    );
}

#[test]
fn exclusive_slice_returns_accept_mutable_record_field_parameters() {
    agrees(
        r#"struct Window<'a, T> { view: &'a mut [T], start: i64 }
        struct Outer<'a> { window: Window<'a, i64> }
        struct Mixed<'a> { view: &'a mut [i64], token: Box<i64> }
        fn first<'a>(window: Window<'a, i64>) -> &'a mut [i64] ! {} {
            let Window { view, .. } = window; view
        }
        fn nested<'a>(outer: Outer<'a>) -> &'a mut [i64] ! {} {
            let Outer { window } = outer; first(window)
        }
        fn mixed<'a>(m: Mixed<'a>) -> &'a mut [i64] ! {} {
            let Mixed { view, .. } = m; view
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let v = nested(Outer { window: Window { view: &mut a[..], start: 0 } });
            Slice.set(v, 0, 9);
            let v = mixed(Mixed { view: &mut a[..], token: Box.new(7) });
            Slice.set(v, 1, 8);
            a[0] + a[1]
        }"#,
        17,
        "",
    );
    assert!(
        check(
            r#"struct Window<'a, 'b> { shared: &'a [i64], other: &'b mut [i64] }
        fn wrong<'a, 'b>(w: Window<'a, 'b>) -> &'a mut [i64] ! {} {
            let Window { shared, .. } = w; shared
        }
        fn main() -> Unit ! {} {}"#
        )
        .is_err()
    );
}

#[test]
fn record_rest_pattern_must_be_final_and_preserves_ignored_field_cleanup() {
    agrees(
        r#"struct P { token: Box<i64>, value: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let p = P { token: Box.new(1), value: 4 };
            let P { value: n, .., } = p;
            let P { .. } = P { token: Box.new(2), value: 5 };
            n
        }"#,
        4,
        "",
    );
    for pattern in ["P { .., value }", "P { value, .., .. }"] {
        assert!(
            kush::parse(&format!(
                "fn main() -> Unit ! {{}} {{ let {pattern} = p; }}"
            ))
            .is_err()
        );
    }
}

#[test]
fn mixed_metadata_exclusions_apply_through_nested_records_and_owned_wrappers() {
    for (declarations, value) in [
        ("struct Meta { field: Stdin }", "Meta { field: IO.stdin() }"),
        ("struct Meta { field: i64 | Bool }", "Meta { field: 1 }"),
        (
            "struct Meta { field: fn() -> i64 ! {} }",
            "Meta { field: answer }",
        ),
        (
            "struct Inner { field: fn() -> i64 ! {} } struct Meta { inner: Box<Inner> }",
            "Meta { inner: Box.new(Inner { field: answer }) }",
        ),
    ] {
        let source = format!(
            "{declarations}
            struct Mixed<'a> {{ view: &'a [i64], meta: Meta }}
            fn answer() -> i64 ! {{}} {{ 1 }}
            fn main() -> Unit ! {{io, alloc, panic}} {{
                let a: [i64; 1] = [1];
                let mixed = Mixed {{ view: &a[..], meta: {value} }};
                drop(mixed);
            }}"
        );
        rejects(&source, "not streams, unions, callables or task handles");
    }
}

#[test]
fn nested_record_literals_infer_actual_lifetimes_including_alias_fields() {
    agrees(
        r#"struct Inner<'a, T> { view: &'a [T] }
        type Alias<'a, T> = Inner<'a, T>;
        struct Outer<'a, T> { inner: Alias<'a, T>, note: i64 }
        fn make<'a, 'b>(first: &'a [i64], second: &'b [i64]) -> Outer<'b, i64> ! {} {
            Outer::<'b, i64> { inner: Inner { view: second }, note: 1 }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [4, 5];
            let outer = Outer { inner: Inner { view: &values[..] }, note: 3 };
            let returned = make(&values[..], &values[..]);
            Slice.get(outer.inner.view, 1) + outer.note + returned.note
        }"#,
        9,
        "",
    );
    assert!(
        check(
            r#"struct Inner<'a> { view: &'a [i64] }
        struct Outer<'a> { inner: Inner<'a> }
        fn wrong<'a, 'b>(first: &'a [i64], second: &'b [i64]) -> Outer<'a> ! {} {
            Outer::<'a> { inner: Inner { view: second } }
        }
        fn main() -> Unit ! {} {}"#,
        )
        .is_err()
    );
}

#[test]
fn destructured_field_loans_release_at_last_use_and_keep_live_aliases() {
    for (owner, replacement, tail, expected) in [
        (
            "let mut values: Vec<i64> = Vec.new(); values = Vec.push(values, 1); values = Vec.push(values, 2);",
            "values = Vec.push(values, 3);",
            "Vec.len(&values)",
            9,
        ),
        (
            "let mut values = Bytes.from(\"AB\");",
            "values = Bytes.from(\"xy\");",
            "Bytes.get(&values, 1)",
            191,
        ),
    ] {
        let source = format!(
            "struct Window<'a> {{ view: &'a [i64], start: i64 }}
            fn main() -> i64 ! {{alloc, panic}} {{
                {owner}
                let window = Window {{ view: &values[..], start: 5 }};
                let Window {{ view, start }} = window;
                let head = Slice.get(view, 0);
                {replacement}
                head + start + {tail}
            }}"
        );
        agrees(&source, expected, "");
    }
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..], start: 5 };
            let Window { view, start } = window;
            let head = Slice.get(view, 0);
            values = [7, 8];
            head + start + values[1]
        }"#,
        14,
        "",
    );
    assert!(
        check(
            r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..], start: 5 };
            let Window { view, start } = window;
            values = [7, 8];
            Slice.get(view, 0) + start
        }"#,
        )
        .is_err()
    );
    // Destructuring in a later argument must retain the first argument's loan.
    rejects(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn consume<'a>(window: Window<'a>, n: i64) -> i64 ! {panic} {
            Slice.get(window.view, 0) + n
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..], start: 5 };
            consume(window, {
                let Window { view, start } = window;
                let head = Slice.get(view, 0);
                values = [7, 8];
                head + start
            })
        }"#,
        "borrow",
    );
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowed-records-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
        let stderr = String::from_utf8(output.stderr).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap_or_else(|| panic!("missing native allocation diagnostics: {stderr:?}"));
        assert_eq!(line, stats.report(), "{source}");
    }
    stats
}

#[test]
fn inferred_local_record_destructuring_and_owner_kinds() {
    agrees(
        r#"struct Window<'a, T> {
            view: &'a [T],
            start: i64
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 3] = [4, 5, 6];
            let window = Window { view: &values[..], start: 1 };
            let Window { view, start } = window;
            let mut vector: Vec<i64> = Vec.new();
            vector = Vec.push(vector, 9);
            let vector_window = Window { view: &vector[..], start: 2 };
            let bytes = Bytes.from("A");
            let byte_window = Window { view: &bytes[..], start: 3 };
            Slice.get(view, 1) + start
                + Slice.get(vector_window.view, 0) + vector_window.start
                + Slice.get(byte_window.view, 0) + byte_window.start
        }"#,
        5 + 1 + 9 + 2 + 65 + 3,
        "",
    );
    agrees(
        r#"struct Window<'a, T> {
            view: &'a [T],
            start: i64
        }
        #[noalloc]
        #[nosuspend]
        fn length<'a>(window: Window<'a, i64>) -> i64 ! {panic} {
            Slice.len(window.view) + window.start
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [1, 2];
            length(Window { view: &values[..], start: 2 })
        }"#,
        4,
        "",
    );
}

#[test]
fn multiple_lifetimes_keep_fields_distinct_and_swap_or_wrong_field_fails() {
    agrees(
        r#"struct Two<'a, 'b> {
            first: &'a [i64],
            second: &'b [i64],
            tag: i64
        }
        fn first<'a, 'b>(two: Two<'a, 'b>) -> &'a [i64] ! {} { two.first }
        fn second<'a, 'b>(two: Two<'a, 'b>) -> &'b [i64] ! {} { two.second }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [10, 11];
            let b: [i64; 2] = [20, 21];
            let two = Two { first: &a[..], second: &b[..], tag: 4 };
            Slice.get(first(two), 1) * 100
                + Slice.get(second(two), 0) + two.tag
        }"#,
        11 * 100 + 20 + 4,
        "",
    );
    rejects(
        r#"struct Two<'a, 'b> {
            first: &'a [i64],
            second: &'b [i64]
        }
        fn wrong<'a, 'b>(two: Two<'a, 'b>) -> &'a [i64] ! {} {
            two.second
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime",
    );
    rejects(
        r#"struct Two<'a, 'b> {
            first: &'a [i64],
            second: &'b [i64]
        }
        fn swapped<'a, 'b>(two: Two<'a, 'b>) -> Two<'a, 'b> ! {} {
            Two { first: two.second, second: two.first }
        }
        fn main() -> Unit ! {} {}"#,
        "must be borrowed for lifetime",
    );
    rejects(
        r#"struct Two<'a, 'b> {
            first: &'a [i64],
            second: &'b [i64]
        }
        fn first<'a, 'b>(two: Two<'a, 'b>) -> &'a [i64] ! {} { two.first }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [10, 11];
            let b: [i64; 2] = [20, 21];
            let two = Two { first: &a[..], second: &b[..] };
            let view = first(two);
            b = [30, 31];
            Slice.get(view, 0) + two.second[0]
        }"#,
        "",
    );
}

#[test]
fn nested_generic_and_alias_records_preserve_field_provenance() {
    agrees(
        r#"struct Inner<'a, T> {
            view: &'a [T]
        }
        struct Outer<'a> {
            inner: Inner<'a, i64>,
            note: i64
        }
        type OuterAlias<'a> = Outer<'a>;
        fn outer<'a>(view: &'a [i64]) -> Outer<'a> ! {} {
            Outer { inner: Inner { view: view }, note: 3 }
        }
        fn read<'a>(outer: OuterAlias<'a>) -> &'a [i64] ! {} {
            outer.inner.view
        }
        struct Holder<T> {
            item: T,
            tag: i64
        }
        fn read_holder<'a>(holder: Holder<Inner<'a, i64>>) -> &'a [i64] ! {} {
            holder.item.view
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [8, 9];
            let nested = outer(&values[..]);
            let holder = Holder { item: Inner { view: &values[..] }, tag: 1 };
            Slice.get(read(nested), 0) + nested.note + Slice.get(read_holder(holder), 1)
        }"#,
        8 + 3 + 9,
        "",
    );
    rejects(
        r#"struct Inner<'a> { view: &'a [i64] }
        struct Outer<'a> { inner: Inner<'a> }
        fn wrong<'a>(inner: Inner<'a>) -> Outer<'a> ! {} {
            Outer { inner: inner, inner: inner }
        }
        fn main() -> Unit ! {} {}"#,
        "duplicate record field",
    );
}

#[test]
fn local_construction_and_nested_records_must_not_escape() {
    agrees(
        r#"struct Inner<'a> { view: &'a [i64] }
        fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [1, 2, 3];
            let inner = Inner { view: &values[..] };
            let copied = inner;
            Slice.get(copied.view, 2)
        }"#,
        3,
        "",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn escape<'a>(view: &'a [i64]) -> Window<'a> ! {} {
            let local: [i64; 2] = [1, 2];
            Window { view: &local[..] }
        }
        fn main() -> Unit ! {} {}"#,
        "must be borrowed for lifetime",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn escape<'a>(view: &'a [i64]) -> &'a [i64] ! {} {
            let local: [i64; 2] = [1, 2];
            let window = Window { view: &local[..] };
            window.view
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
}

#[test]
fn owner_replacement_and_argument_order_are_checked_through_records() {
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..] };
            values = [3, 4];
            Slice.get(window.view, 0)
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn read<'a>(window: Window<'a>, n: i64) -> i64 ! {panic} {
            Slice.get(window.view, 0) + n
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            read(Window { view: &values[..] }, { values = [3, 4]; 0 })
        }"#,
        "borrows it",
    );
    rejects(
        r#"struct Late<'a> { start: i64, view: &'a [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let late = Late { view: &values[..], start: { values = [3, 4]; 0 } };
            Slice.get(late.view, 0)
        }"#,
        "borrows it",
    );
    agrees(
        r#"struct Late<'a> { start: i64, view: &'a [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let late = Late { start: { values = [3, 4]; 5 }, view: &values[..] };
            late.start + Slice.get(late.view, 0)
        }"#,
        8,
        "",
    );
}

#[test]
fn record_loans_follow_branches_loops_and_last_use() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn choose<'a>(flag: Bool, a: &'a [i64], b: &'a [i64]) -> Window<'a> ! {} {
            if flag { Window { view: a } } else { Window { view: b } }
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [1, 2];
            let b: [i64; 2] = [3, 4];
            let window = choose(true, &a[..], &b[..]);
            let mut index = 0;
            let mut sum = 0;
            while index < Slice.len(window.view) {
                sum = sum + Slice.get(window.view, index);
                index = index + 1;
            }
            sum
        }"#,
        3,
        "",
    );
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..], start: 0 };
            let first = Slice.get(window.view, 0);
            values = [7, 8];
            first + values[1]
        }"#,
        1 + 8,
        "",
    );
}

#[test]
fn borrowed_record_rejects_unsafe_storage_generic_and_callable_escapes() {
    rejects(
        r#"struct Mutable<'a> { view: &'a mut [i64] }
        fn main() -> Unit ! {} {
            let values: [i64; 1] = [1];
            let _ = Mutable { view: &values[..] };
        }"#,
        "type mismatch",
    );
    rejects(
        r#"#[linear] struct Mixed<'a> { view: &'a [i64], owner: Box<i64> }
        fn main() -> Unit ! {} {}"#,
        "linear",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn store<'a>(view: &'a [i64]) -> Unit ! {alloc, panic} {
            let vector: Vec<Window<'a>> = Vec.new();
            let _ = vector;
        }
        fn main() -> Unit ! {} {}"#,
        "containers cannot store",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn store<'a>(view: &'a [i64]) -> Unit ! {alloc, panic} {
            let slot: Box<Window<'a>> = Box.new(Window { view: view });
            drop(slot);
        }
        fn main() -> Unit ! {} {}"#,
        "containers cannot store",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn store<'a>(view: &'a [i64]) -> Unit ! {} {
            let array: [Window<'a>; 1] = [Window { view: view }];
            let _ = array;
        }
        fn main() -> Unit ! {} {}"#,
        "inline array",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn identity<T>(value: T) -> T ! {} { value }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            let window = Window { view: view };
            Slice.get(identity(window).view, 0)
        }
        fn main() -> Unit ! {} {}"#,
        "generic type parameter",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn run<'a>(view: &'a [i64]) -> Unit ! {alloc, panic} {
            let window = Window { view: view };
            let read = fn() -> i64 ! {panic} { Slice.get(window.view, 0) };
            let command: once fn() -> i64 ! {panic} = read;
            let _ = command;
        }
        fn main() -> Unit ! {} {}"#,
        "scoped",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn run<'a>(view: &'a [i64]) -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let local: [i64; 1] = [5];
                let window = Window { view: &local[..] };
                Task.spawn(fn() -> Unit ! {panic, suspend} {
                    Slice.get(window.view, 0); Task.yield();
                });
            });
        }
        fn main() -> Unit ! {} {}"#,
        "captured from outside",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn run<'a>(view: &'a [i64]) -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Window<'a> ! {panic} { Window { view: view } });
        }
        fn main() -> Unit ! {} {}"#,
        "not outlived by any borrowed parameter or captured record field",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn union<'a>(view: &'a [i64]) -> Unit ! {} {
            let value: Window<'a> | i64 = Window { view: view };
            let _ = value;
        }
        fn main() -> Unit ! {} {}"#,
        "unions cannot contain borrowed records",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn main() -> Unit ! {} {
            let value: Window<'static, i64> = Window { view: &[1, 2][..] };
            let _ = value;
        }"#,
        "",
    );
}

#[test]
fn generic_record_alias_and_helper_results_keep_provenance() {
    agrees(
        r#"struct Window<'a, T> {
            view: &'a [T],
            start: i64
        }
        type WindowAlias<'a, T> = Window<'a, T>;
        fn make<'a>(view: &'a [i64]) -> WindowAlias<'a, i64> ! {} {
            Window { view: view, start: 1 }
        }
        fn identity<'a>(window: Window<'a, i64>) -> Window<'a, i64> ! {} { window }
        fn first<'a>(window: Window<'a, i64>) -> &'a [i64] ! {} { window.view }
        fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [2, 4, 6];
            let window = make(&values[..]);
            let copied = identity(identity(window));
            Slice.get(first(copied), 2) + copied.start
        }"#,
        7,
        "",
    );
    rejects(
        r#"struct Window<'a, T> { view: &'a [T] }
        fn main() -> Unit ! {} {
            let values: [i64; 2] = [1, 2];
            let window = Window { view: &values[..] };
            let view = window.view;
            let mutable: &mut [i64] = &mut view[..];
            Slice.set(mutable, 0, 9);
        }"#,
        "cannot be upgraded",
    );
}

#[test]
fn split_siblings_in_one_record_keep_disjoint_labels() {
    agrees(
        r#"struct Pair<'a, 'b> {
            first: &'a [i64],
            second: &'b [i64]
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let pair = Pair { first: &left[..], second: &right[..] };
            Slice.get(pair.first, 0) + Slice.get(pair.second, 1)
        }"#,
        1 + 4,
        "",
    );
    rejects(
        r#"struct Pair<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let pair = Pair { first: &left[..], second: &right[..] };
            values = [5, 6, 7, 8];
            Slice.get(pair.first, 0) + Slice.get(pair.second, 0)
        }"#,
        "cannot replace an owner",
    );
}

#[test]
fn result_lifetime_selects_only_matching_parameter_records() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn second<'a, 'b>(first: Window<'a>, second: Window<'b>) -> &'b [i64] ! {} {
            second.view
        }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let b: [i64; 2] = [8, 9];
            let view = second(Window { view: &a[..] }, Window { view: &b[..] });
            a = [6, 7];
            Slice.get(view, 0) + a[1]
        }"#,
        8 + 7,
        "",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn second<'a, 'b>(first: Window<'a>, second: Window<'b>) -> &'b [i64] ! {} {
            first.view
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime",
    );
}

#[test]
fn borrowed_record_metadata_may_be_arrays_enums_and_nested_records() {
    agrees(
        r#"enum Kind { Plain, Fancy }
        struct Info {
            kind: Kind,
            values: [i64; 2],
            count: i64
        }
        struct Window<'a> {
            view: &'a [i64],
            info: Info
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [1, 2, 3];
            let window = Window {
                view: &values[..],
                info: Info { kind: Kind.Fancy, values: [4, 5], count: 6 }
            };
            let full = window.view;
            let sub = &full[0..2];
            let head = Slice.get(sub, 1);
            let Window { view, info } = window;
            match info.kind {
                Kind.Fancy => head + info.values[0] + info.count + Slice.get(view, 2),
                Kind.Plain => 0,
            }
        }"#,
        2 + 4 + 6 + 3,
        "",
    );
}

#[test]
fn dropping_an_owner_in_a_later_record_argument_is_rejected() {
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn read<'a>(window: Window<'a>, n: i64) -> i64 ! {panic} {
            Slice.get(window.view, 0) + n
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            read(Window { view: &values[..] }, { drop(values); 0 })
        }"#,
        "cannot move or drop",
    );
    rejects(
        r#"struct Late<'a> { start: i64, view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let late = Late { view: &values[..], start: { drop(values); 0 } };
            Slice.get(late.view, 0)
        }"#,
        "cannot move or drop",
    );
}

#[test]
fn early_fallible_exit_does_not_require_borrowed_record_cleanup() {
    agrees(
        r#"use std.result.Result;
        struct Window<'a> { view: &'a [i64] }
        fn run<'a>(view: &'a [i64]) -> Result<i64, i64> ! {alloc, panic} {
            let window = Window { view: view };
            let extra: Result<i64, i64> = Ok(1);
            let value = extra?;
            Ok(Slice.get(window.view, 0) + value)
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [40, 41];
            match run(&values[..]) {
                Ok(value) => value,
                Err(code) => code,
            }
        }"#,
        41,
        "",
    );
}

#[test]
fn borrowed_record_survives_same_task_suspension() {
    agrees_balanced(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let values: [i64; 2] = [12, 13];
                let window = Window { view: &values[..] };
                let child: Task<i64> = Task.spawn(fn() -> i64 ! {suspend} {
                    Task.yield();
                    5
                });
                let joined = match Task.join(child) {
                    TaskExit.Completed(value) => value,
                    TaskExit.Cancelled => 0,
                };
                Slice.get(window.view, 0) + joined
            })
        }"#,
        17,
        "",
    );
}

fn agrees_balanced(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowed-records-balanced-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

#[test]
fn borrowed_record_example_matches_documented_output() {
    agrees_balanced(
        include_str!("../../../examples/borrowed-records.kush"),
        0,
        "10\n20\n5\n",
    );
}

#[test]
fn shared_slice_record_is_constructed_passed_and_projected() {
    agrees(
        r#"struct Window<'a, T> {
            view: &'a [T],
            start: i64
        }
        fn window<'a>(view: &'a [i64]) -> Window<'a, i64> ! {} {
            Window { view: view, start: 0 }
        }
        fn first<'a>(window: Window<'a, i64>) -> &'a [i64] ! {} {
            window.view
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [7, 8, 9];
            let window = window(&values[..]);
            Slice.get(first(window), 0) + window.start
        }"#,
        7,
        "",
    );
}

#[test]
fn mutable_record_fields_are_affine_and_restore_the_owner_after_last_use() {
    agrees(
        r#"struct Window<'a, T> {
            view: &'a mut [T],
            start: i64
        }
        fn window<'a>(view: &'a mut [i64]) -> Window<'a, i64> ! {} {
            Window { view: view, start: 3 }
        }
        fn bump<'a>(window: Window<'a, i64>) -> i64 ! {panic} {
            let Window { view, start } = window;
            Slice.set(view, 0, Slice.get(view, 0) + 40);
            Slice.get(view, 0) + start
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 3] = [1, 2, 3];
            let window = window(&mut values[..]);
            let result = bump(window);
            let head = Slice.get(&values[..], 0);
            result * 10 + head
        }"#,
        481,
        "",
    );
    rejects(
        r#"struct Window<'a> { view: &'a mut [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &mut values[..], start: 0 };
            let view = window.view;
            Slice.set(view, 0, 9);
            view[0]
        }"#,
        "destructure",
    );
    rejects(
        r#"struct Window<'a> { view: &'a mut [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = Window { view: &mut values[..], start: 0 };
            let copy = window;
            window.start + copy.start
        }"#,
        "moved",
    );
}

#[test]
fn mutable_record_helper_returns_keep_the_exclusive_lifetime_and_owner_suspended() {
    agrees(
        r#"struct Window<'a> { view: &'a mut [i64], start: i64 }
        fn tail<'a>(window: Window<'a>) -> Window<'a> ! {panic} {
            let Window { view, start } = window;
            let child = &mut view[1..];
            Window { view: child, start: start + 1 }
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let window = tail(Window { view: &mut values[..], start: 0 });
            let Window { view, start } = window;
            Slice.set(view, 0, 7);
            let written = Slice.get(view, 0);
            written * 10 + start + values[1]
        }"#,
        7 * 10 + 1 + 7,
        "",
    );
    rejects(
        r#"struct S<'a, 'b> { shared: &'a [i64], write: &'b mut [i64] }
        fn wrong<'a, 'b>(s: S<'a, 'b>) -> &'a mut [i64] ! {} {
            let S { shared, write } = s;
            write
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime",
    );
    rejects(
        r#"struct S<'a> { shared: &'a [i64], write: &'a mut [i64] }
        fn wrong<'a>(s: S<'a>) -> &'a mut [i64] ! {} {
            s.shared
        }
        fn main() -> Unit ! {} {}"#,
        "",
    );
}

#[test]
fn mutable_record_destructuring_transfers_the_capability_transitively() {
    agrees(
        r#"struct Inner<'a> { view: &'a mut [i64] }
        struct Outer<'a> { inner: Inner<'a>, note: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let outer = Outer { inner: Inner { view: &mut values[..] }, note: 4 };
            let moved = outer;
            let Outer { inner, note } = moved;
            let Inner { view } = inner;
            Slice.set(view, 0, 5);
            Slice.get(view, 0) + note
        }"#,
        9,
        "",
    );
    rejects(
        r#"struct Inner<'a> { view: &'a mut [i64] }
        struct Outer<'a> { inner: Inner<'a>, note: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let outer = Outer { inner: Inner { view: &mut values[..] }, note: 4 };
            let moved = outer;
            let again = outer;
            again.note
        }"#,
        "use after move",
    );
}

#[test]
fn mutable_split_siblings_in_one_record_remain_disjoint_and_restore_the_owner() {
    agrees(
        r#"struct Pair<'a, 'b> {
            left: &'a mut [i64],
            right: &'b mut [i64]
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left_parent, right_parent) = Slice.split_at_mut(&mut values[..], 2);
            let pair = Pair { left: &mut left_parent[..], right: &mut right_parent[..] };
            let Pair { left, right } = pair;
            Slice.set(left, 0, 10);
            Slice.set(right, 1, 40);
            let whole = Slice.get(left, 0) + Slice.get(right, 1);
            whole + values[2]
        }"#,
        10 + 40 + 3,
        "",
    );
    rejects(
        r#"struct Pair<'a, 'b> { left: &'a mut [i64], right: &'b mut [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left_parent, right_parent) = Slice.split_at_mut(&mut values[..], 2);
            let pair = Pair { left: &mut left_parent[..], right: &mut right_parent[..] };
            let Pair { left, right } = pair;
            let observed = values[2];
            Slice.set(left, 0, observed);
            Slice.get(right, 0)
        }"#,
        "exclusive",
    );
}

#[test]
fn mixed_borrowed_owning_records_move_and_free_owned_parts_exactly_once() {
    let stats = agrees(
        r#"struct BufferView<'a> {
            view: &'a [i64],
            token: Box<i64>,
            start: i64
        }
        fn make<'a>(view: &'a [i64]) -> BufferView<'a> ! {alloc, panic} {
            BufferView { token: Box.new(5), start: 2, view: view }
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [8, 9];
            let record = make(&values[..]);
            let BufferView { view, token, start } = record;
            Slice.get(view, 1) + Box.take(token) + start
        }"#,
        9 + 5 + 2,
        "",
    );
    assert_eq!(stats.allocations, 1, "one owned token allocation");
    let stats = agrees(
        r#"struct Mixed<'a> {
            view: &'a mut [i64],
            token: Bytes,
            items: Vec<i64>,
            count: i64
        }
        fn make<'a>(view: &'a mut [i64]) -> Mixed<'a> ! {alloc, panic} {
            let token = Bytes.from("A");
            let items: Vec<i64> = [3];
            Mixed { view: view, token: token, items: items, count: 1 }
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: [i64; 2] = [1, 2];
            let record = make(&mut values[..]);
            let Mixed { view, token, items, count } = record;
            Slice.set(view, 1, 7);
            let whole = Slice.get(view, 1) + Bytes.get(&token, 0) + Vec.len(&items) + count;
            whole + values[1]
        }"#,
        7 + 65 + 1 + 1 + 7,
        "",
    );
    assert_eq!(
        stats.allocations, stats.deallocations,
        "owned fields balance"
    );
    let stats = agrees(
        r#"struct BufferView<'a> { view: &'a [i64], token: Box<i64> }
        fn main() -> Unit ! {alloc, panic} {
            let values: [i64; 1] = [1];
            {
                let record = BufferView { view: &values[..], token: Box.new(1) };
            }
        }"#,
        0,
        "",
    );
    assert_eq!(
        stats.allocations, 1,
        "an unused mixed record frees its token once"
    );
    assert_eq!(stats.deallocations, 1, "its borrowed field owns no storage");
}

#[test]
fn mixed_record_cleanup_balances_across_early_exits_loops_and_noalloc_helpers() {
    agrees(
        r#"use std.result.Result;
        struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        fn fail() -> Result<i64, i64> ! {} { Err(9) }
        fn run<'a>(view: &'a [i64]) -> Result<i64, i64> ! {alloc, panic} {
            let record = Mixed { view: view, token: Box.new(3) };
            let Mixed { view, token } = record;
            let value = fail()?;
            Ok(Slice.get(view, 0) + Box.take(token) + value)
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 1] = [40];
            match run(&values[..]) {
                Ok(value) => value,
                Err(code) => code,
            }
        }"#,
        9,
        "",
    );
    agrees(
        r#"struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        #[noalloc]
        #[nosuspend]
        fn payload<'a>(record: Mixed<'a>) -> i64 ! {panic} {
            let Mixed { view, token } = record;
            Slice.get(view, 0) + Box.take(token)
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 1] = [40];
            payload(Mixed { view: &values[..], token: Box.new(2) })
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 1] = [4];
            let mut index = 0;
            let mut sum = 0;
            loop {
                let record = Mixed { view: &values[..], token: Box.new(2) };
                let Mixed { view, token } = record;
                sum = sum + Slice.get(view, 0) + Box.take(token);
                index = index + 1;
                if index == 2 {
                    break sum;
                }
                continue;
            }
        }"#,
        12,
        "",
    );
    agrees(
        r#"struct BufferView<'a> { view: &'a [i64], token: Box<i64>, start: i64 }
        fn partial<'a>(view: &'a [i64]) -> i64 ! {alloc, panic} {
            let record = BufferView { token: Box.new(4), start: 0, view: { return 9; } };
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 1] = [1];
            partial(&values[..])
        }"#,
        9,
        "",
    );
}

#[test]
fn mixed_record_survives_same_task_suspension_with_balanced_ownership() {
    agrees_balanced(
        r#"use std.task.TaskExit;
        struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let values: [i64; 2] = [12, 13];
                let record = Mixed { token: Box.new(5), view: &values[..] };
                let child: Task<i64> = Task.spawn(fn() -> i64 ! {suspend} {
                    Task.yield();
                    4
                });
                let joined = match Task.join(child) {
                    TaskExit.Completed(value) => value,
                    TaskExit.Cancelled => 0,
                };
                let Mixed { view, token } = record;
                Slice.get(view, 0) + Box.take(token) + joined
            })
        }"#,
        21,
        "",
    );
}

#[test]
fn mixed_owning_records_reject_containers_self_reference_and_linear_fields() {
    rejects(
        r#"struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        fn store<'a>(view: &'a [i64]) -> Unit ! {alloc, panic} {
            let slot: Box<Mixed<'a>> = Box.new(Mixed { view: view, token: Box.new(1) });
            drop(slot);
        }
        fn main() -> Unit ! {} {}"#,
        "containers cannot store",
    );
    rejects(
        r#"struct Owner<'a> { owner: Vec<i64>, view: &'a [i64] }
        fn main() -> Unit ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let record = Owner { owner: values, view: &values[..] };
            drop(record);
        }"#,
        "moved",
    );
    rejects(
        r#"struct Owner<'a> { owner: Vec<i64>, view: &'a [i64] }
        fn main() -> Unit ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let record = Owner { view: &values[..], owner: values };
            drop(record);
        }"#,
        "borrowed",
    );
    rejects(
        r#"#[linear] struct Mixed<'a> { view: &'a [i64], token: Box<i64> }
        fn main() -> Unit ! {} {}"#,
        "linear",
    );
}

#[test]
fn mutable_record_example_matches_documented_output() {
    agrees_balanced(
        include_str!("../../../examples/mutable-borrowed-records.kush"),
        0,
        "10\n20\n10\n20\n3\n",
    );
}

#[test]
fn mixed_record_example_matches_documented_output() {
    agrees_balanced(
        include_str!("../../../examples/mixed-borrowed-records.kush"),
        0,
        "28\n74\n7\n",
    );
}

#[test]
fn mutable_record_arguments_keep_owners_borrowed_through_later_arguments() {
    rejects(
        r#"struct Window<'a> { view: &'a mut [i64], start: i64 }
        fn read<'a>(window: Window<'a>, n: i64) -> i64 ! {panic} {
            let Window { view, start } = window;
            Slice.get(view, 0) + start + n
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            read(Window { view: &mut values[..], start: 0 }, { values = [3, 4]; 0 })
        }"#,
        "borrow",
    );
    rejects(
        r#"struct Late<'a> { start: i64, view: &'a mut [i64] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let late = Late { view: &mut values[..], start: { values = [3, 4]; 0 } };
            let Late { view, start } = late;
            Slice.get(view, 0) + start
        }"#,
        "borrow",
    );
}

#[test]
fn mutable_record_field_reborrows_restore_the_parent_and_owner() {
    agrees(
        r#"struct Window<'a> { view: &'a mut [i64], start: i64 }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 3] = [1, 2, 3];
            let window = Window { view: &mut values[..], start: 0 };
            let Window { view, start } = window;
            let child = &mut view[1..];
            Slice.set(child, 0, 9);
            let parent_read = Slice.get(view, 1);
            parent_read + start + values[0]
        }"#,
        10,
        "",
    );
    agrees(
        r#"struct Inner<'a> { view: &'a mut [i64] }
        type Alias<'a> = Inner<'a>;
        struct Outer<'a> { inner: Alias<'a>, note: i64 }
        fn pass<'a>(outer: Outer<'a>) -> Outer<'a> ! {} { outer }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [4, 5];
            let outer = pass(Outer { inner: Inner { view: &mut values[..] }, note: 2 });
            let Outer { inner, note } = outer;
            let Inner { view } = inner;
            Slice.set(view, 1, 8);
            Slice.get(view, 1) + note + values[0]
        }"#,
        14,
        "",
    );
}
