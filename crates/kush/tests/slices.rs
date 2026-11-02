use kush::executable::{MemoryStats, check};

fn checked(source: &str) -> kush::executable::Executable {
    check(source).unwrap()
}
fn evaluate(source: &str) -> (i64, String) {
    let program = checked(source);
    let mut output = Vec::new();
    let value = program.evaluate(&mut output).unwrap();
    (value, String::from_utf8(output).unwrap())
}
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}
fn panics(source: &str) {
    let program = checked(source);
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("panic:"), "{error:?}");
}

#[test]
fn arrays_of_views_support_length_index_subslice_and_loops() {
    let (value, output) = evaluate(
        r#"
        fn sum(s: &[i64]) -> i64 ! {panic} {
            let mut acc = 0;
            let mut i = 0;
            while i < Slice.len(s) {
                acc = acc + Slice.get(s, i);
                i = i + 1;
            }
            acc
        }
        fn main() -> Unit ! {io, panic} {
            let values: [i64; 5] = [10, 20, 30, 40, 50];
            let all: &[i64] = &values[..];
            let middle = &values[1..4];
            let tail = middle[1..];
            print_i64(Slice.len(all));
            print_i64(middle[0]);
            print_i64(middle[2]);
            print_i64(Slice.len(tail));
            print_i64(tail[0]);
            print_i64(sum(middle));
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "5\n20\n40\n2\n30\n90\n");
}

#[test]
fn vectors_and_bytes_are_borrowed_without_copying_their_storage() {
    let program = checked(
        r#"
        fn head(s: &[i64], fallback: i64) -> i64 ! {panic} {
            if Slice.len(s) > 0 { Slice.get(s, 0) } else { fallback }
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 10); v = Vec.push(v, 20); v = Vec.push(v, 30);
            let view: &[i64] = &v[1..];
            print_i64(Slice.len(view));
            print_i64(view[0]);
            print_i64(head(view[1..], 0));

            let bytes = Bytes.from("ABCD");
            let raw: &[i64] = &bytes[1..3];
            print_i64(Slice.len(raw));
            print_i64(raw[0]);
            print_i64(head(raw, 0));
        }
        "#,
    );
    let mut output = Vec::new();
    let (value, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(value, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "2\n20\n30\n2\n66\n66\n");
    // One Vec, one byte buffer, no allocations for either view.
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
}

#[test]
fn slices_of_nested_and_non_i64_elements_keep_their_layout() {
    let (value, output) = evaluate(
        r#"
        fn main() -> Unit ! {io, panic} {
            let nested: [[i64; 2]; 3] = [[1, 2], [3, 4], [5, 6]];
            let rows: &[[i64; 2]] = &nested[1..];
            print_i64(Slice.len(rows));
            let row = rows[1];
            print_i64(row[0]);
            print_i64(row[1]);

            let flags: [Bool; 3] = [true, false, true];
            let bits: &[Bool] = &flags[..];
            print_i64(if bits[2] { 1 } else { 0 });
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "2\n5\n6\n1\n");
}

#[test]
fn dynamic_fixed_array_indexing_is_checked_and_copies_only_copyable_values() {
    let (value, output) = evaluate(
        r#"
        fn main() -> Unit ! {io, panic} {
            let values: [i64; 4] = [5, 6, 7, 8];
            let mut i = 0;
            while i < 4 { print_i64(values[i]); i = i + 1; }
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "5\n6\n7\n8\n");
    panics(
        r#"fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [1, 2];
            let i = 2;
            values[i]
        }"#,
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let a:[Box<i64>;2]=[Box.new(1),Box.new(2)]; let i=0; a[i]; }",
        "dynamic indexing copies the element",
    );
}

#[test]
fn checked_slice_ranges_and_element_access_panic_at_the_reference_boundary() {
    panics(
        r#"fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [1, 2];
            let i = 2;
            let view = &values[..];
            Slice.get(view, i)
        }"#,
    );
    panics(
        r#"fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [1, 2, 3];
            let start = 2;
            let view = &values[start..start + 2];
            Slice.len(view)
        }"#,
    );
    panics(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let end = 2;
            let view = &v[0..end];
            print_i64(Slice.len(view));
        }"#,
    );
    rejects(
        "fn main() -> i64 ! {} { let a:[i64;2]=[1,2]; let s=&a[0..3]; 0 }",
        "out of bounds",
    );
}

#[test]
fn proved_slice_bounds_erase_the_runtime_check_and_are_version_aware() {
    let (value, _) = evaluate(
        r#"
        fn read(s: &[i64], i: i64, erased ok: { 0 <= i && i < Slice.len(s) }) -> i64 ! {} {
            Slice.at(s, i, _)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [7, 8, 9];
            let s: &[i64] = &a[..];
            if 0 <= 1 && 1 < Slice.len(s) { read(s, 1, _) } else { 0 }
        }
        "#,
    );
    assert_eq!(value, 8);
    rejects(
        "fn f(s: &[i64], i: i64) -> i64 ! {} { Slice.at(s, i, _) } fn main() -> Unit ! {} {}",
        "cannot prove",
    );
    // A fresh `if` fact that mentions the owner's length rather than the
    // slice's length is not silently reused for a different index.
    rejects(
        r#"fn f(s: &[i64], i: i64, erased ok: { 0 <= i && i < Slice.len(s) }) -> i64 ! {} { Slice.at(s, i, _) }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            if 0 <= 1 && 1 < Slice.len(s) { f(s, 2, _) } else { 0 }
        }"#,
        "cannot prove",
    );
}

#[test]
fn views_do_not_allocate_and_allow_noalloc_call_scoped_reads() {
    let program = checked(
        r#"
        #[noalloc]
        fn first(s: &[i64]) -> i64 ! {panic} { Slice.get(s, 0) }
        #[noalloc]
        fn pair() -> [i64; 2] ! {} { [41, 1] }
        fn main() -> i64 ! {panic} {
            let a = pair();
            let s: &[i64] = &a[..];
            first(s) + Slice.get(s, 1)
        }
        "#,
    );
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats, MemoryStats::default());
}

#[test]
fn owners_cannot_move_drop_or_be_replaced_while_a_view_is_live() {
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let s: &[i64] = &v[..];
            v = Vec.push(v, 2);
            Slice.len(s);
        }"#,
        "slice view or reference borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let b = Bytes.from("x");
            let s: &[i64] = &b[..];
            drop(b);
            Slice.len(s);
        }"#,
        "move",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            a = [3, 4];
            Slice.len(s);
        }"#,
        "slice view or reference borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let b = Bytes.from("x");
            let s: &[i64] = &b[..];
            let moved = b;
            Slice.len(s);
        }"#,
        "move",
    );
}

#[test]
fn view_lifetimes_are_lexical_and_escapes_are_rejected_explicitly() {
    // Releasing the view at the end of its block permits a later owner move.
    let (value, output) = evaluate(
        r#"
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            { let s: &[i64] = &v[..]; print_i64(Slice.len(s)); }
            v = Vec.push(v, 2);
            print_i64(Vec.len(&v));
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "1\n2\n");
    // A view of an outer owner may leave an inner block; the outer binding
    // inherits the loan.
    let (value, _) = evaluate(
        r#"fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [4, 5, 6];
            let s = { let t: &[i64] = &a[..]; t };
            s[2]
        }"#,
    );
    assert_eq!(value, 6);
    rejects(
        "fn f() -> &[i64] ! {} { let a:[i64;2]=[1,2]; &a[..] } fn main() -> Unit ! {} {}",
        "cannot be returned",
    );
    rejects(
        r#"fn consume(s: &[i64]) -> i64 ! {panic} { Slice.len(s) }
        fn main() -> i64 ! {panic} { consume({ let a:[i64;2]=[1,2]; &a[..] }) }"#,
        "outlive",
    );
    rejects(
        r#"fn main() -> Unit ! {} {
            let a:[i64;2]=[1,2];
            let stored:[&[i64];1] = [&a[..]];
        }"#,
        "stores references",
    );
    rejects(
        r#"enum E { A(&[i64]) } fn main() -> Unit ! {} {}"#,
        "cannot store borrowed references or slice views",
    );
    rejects(
        r#"fn main() -> Unit ! {} {
            let v: Vec<&[i64]> = Vec.new();
        }"#,
        "containers cannot store borrowed references or slice views",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} { let s = &[1, 2][..]; }"#,
        "bind the owner to a local",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let a: [Box<i64>; 1] = [Box.new(1)];
            let s: &[Box<i64>] = &a[..];
        }"#,
        "owning or linear elements",
    );
}

#[test]
fn slice_and_dynamic_index_effects_are_declared_precisely() {
    rejects(
        r#"fn main() -> i64 ! {} {
            let a: [i64; 2] = [1, 2];
            let i = 1;
            a[i]
        }"#,
        "requires effects {panic}",
    );
    rejects(
        r#"fn main() -> i64 ! {} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            Slice.get(s, 1)
        }"#,
        "requires effects {panic}",
    );
    rejects(
        r#"fn main() -> i64 ! {} {
            let a: [i64; 3] = [1, 2, 3];
            let start = 1;
            let s = &a[start..2];
            Slice.len(s)
        }"#,
        "requires effects {panic}",
    );
    // Full-range and compile-time-valid array ranges need no panic effect.
    checked(
        r#"fn main() -> i64 ! {} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            let t: &[i64] = &a[1..2];
            Slice.len(s); Slice.len(t); 0
        }"#,
    );
}

#[test]
fn computed_constant_array_lengths_are_folded_at_compile_time() {
    let (value, output) = evaluate(
        r#"
        fn main() -> Unit ! {io, panic} {
            let a: [i64; (1 + 1) * 2 - 1] = [10, 20, 30];
            let s: &[i64] = &a[1..(1 + 1) * 2 - 1];
            print_i64(Slice.len(s)); print_i64(s[0]);
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "2\n20\n");
    rejects(
        "fn main() -> Unit ! {} { let a: [i64; 1 - 2] = []; }",
        "nonnegative",
    );
    rejects(
        "fn main() -> Unit ! {} { let a: [i64; 1 / 0] = []; }",
        "constant nonnegative",
    );
    rejects(
        "fn main() -> Unit ! {} { let a: [i64; 1 + nope] = []; }",
        "constant expression",
    );
}

#[test]
fn bundle_and_record_storage_of_views_stays_rejected() {
    rejects(
        "fn main() -> Unit ! {} { let a: [&[i64]; 1] = []; }",
        "stores references",
    );
    rejects(
        "struct X { s: &[i64] } fn main() -> Unit ! {} {}",
        "records cannot store borrowed references or slice views",
    );
    rejects(
        "fn f() -> &[i64] ! {} { panic() } fn main() -> Unit ! {} {}",
        "cannot be returned",
    );
}

#[test]
fn try_get_returns_option_without_panicking() {
    let (value, output) = evaluate(
        r#"
        enum Option<T> { None, Some(T) }
        fn show(x: Option<i64>) -> i64 ! {io} {
            match x { Option.Some(value) => value, Option.None => -1 }
        }
        fn index_twice(i: i64) -> i64 ! {io, panic} { print_i64(i); i }
        fn read(s: &[i64], index: i64) -> i64 ! {} {
            match Slice.try_get(s, index) { Option.Some(value) => value, Option.None => 0 }
        }
        fn main() -> Unit ! {io, panic} {
            let a: [i64; 3] = [10, 20, 30];
            let shared: &[i64] = &a[..];
            print_i64(show(Slice.try_get(shared, 0)));
            print_i64(show(Slice.try_get(shared, 2)));
            print_i64(show(Slice.try_get(shared, -1)));
            print_i64(show(Slice.try_get(shared, 3)));
            print_i64(show(Slice.try_get(shared, 9223372036854775807)));
            print_i64(show(Slice.try_get(shared, index_twice(1))));
            let empty: &[i64] = &a[0..0];
            print_i64(show(Slice.try_get(empty, 0)));
            print_i64(read(empty, 0));
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "10\n30\n-1\n-1\n-1\n1\n20\n-1\n0\n");
}

#[test]
fn try_get_accepts_reversed_option_tags_and_mutable_views() {
    let (value, output) = evaluate(
        r#"
        enum Option<T> { Some(T), None }
        fn show(x: Option<i64>) -> i64 ! {io} {
            match x { Option.Some(value) => value, Option.None => -1 }
        }
        fn main() -> Unit ! {io, panic} {
            let mut a: [i64; 2] = [7, 8];
            let view: &mut [i64] = &mut a[..];
            print_i64(show(Slice.try_get(view, 1)));
            print_i64(show(Slice.try_get(view, 2)));
            Slice.set(view, 0, 9);
            print_i64(show(Slice.try_get(view, 0)));
        }
        "#,
    );
    assert_eq!(value, 0);
    assert_eq!(output, "8\n-1\n9\n");
}

#[test]
fn try_get_rejects_malformed_option_and_rival_owner_access() {
    rejects(
        r#"
        enum Option<T> { None, Some(Bool), Extra }
        fn main() -> Unit ! {} {
            let a: [i64; 1] = [1];
            let view: &[i64] = &a[..];
            let x = Slice.try_get(view, 0);
        }
        "#,
        "requires the exact enum Option<T>",
    );
    rejects(
        r#"
        enum Option<T> { None, Some(T) }
        fn main() -> Unit ! {} {
            let mut a: [i64; 1] = [1];
            let view: &[i64] = &a[..];
            let x = Slice.try_get(view, { a = [2]; 0 });
        }
        "#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
}
