#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{executable, native::Scratch};
use std::process::Command;

fn compare(source: &str) {
    let program = executable::check(source).unwrap();
    let mut expected_output = Vec::new();
    let expected_exit = program.evaluate(&mut expected_output).unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("slices");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary)
        .current_dir(scratch.path())
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected_exit as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, expected_output);
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn array_views_sub_slices_and_dynamic_indexes_match_reference() {
    compare(
        r#"
        fn sum(s: &[i64]) -> i64 ! {panic} {
            let mut acc = 0;
            let mut i = 0;
            while i < Slice.len(s) { acc = acc + Slice.get(s, i); i = i + 1; }
            acc
        }
        fn main() -> Unit ! {io, panic} {
            let a: [i64; 5] = [10, 20, 30, 40, 50];
            let s: &[i64] = &a[1..4];
            print_i64(Slice.len(s)); print_i64(s[0]); print_i64(s[2]);
            print_i64(sum(s)); print_i64(sum(s[1..]));
            let mut i = 0;
            while i < 5 { print_i64(a[i]); i = i + 1; }
        }
        "#,
    );
}

#[test]
fn vec_bytes_nested_and_non_i64_views_match_reference() {
    compare(
        r#"
        fn head(s: &[i64], fallback: i64) -> i64 ! {panic} {
            if Slice.len(s) > 0 { Slice.get(s, 0) } else { fallback }
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 10); v = Vec.push(v, 20); v = Vec.push(v, 30);
            let view: &[i64] = &v[1..];
            print_i64(Slice.len(view)); print_i64(view[0]); print_i64(head(view[1..], 0));
            let b = Bytes.from("ABCD");
            let raw: &[i64] = &b[1..3];
            print_i64(Slice.len(raw)); print_i64(raw[0]); print_i64(head(raw, 0));
            let nested: [[i64; 2]; 3] = [[1, 2], [3, 4], [5, 6]];
            let rows: &[[i64; 2]] = &nested[1..];
            let row = rows[1];
            print_i64(Slice.len(rows)); print_i64(row[0]); print_i64(row[1]);
            let flags: [Bool; 3] = [true, false, true];
            let bits: &[Bool] = &flags[..];
            print_i64(if bits[2] { 1 } else { 0 });
        }
        "#,
    );
}

#[test]
fn proved_slice_access_matches_reference() {
    compare(
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
}

#[test]
fn lexical_view_release_allows_later_owner_moves_natively() {
    compare(
        r#"
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            { let s: &[i64] = &v[..]; print_i64(Slice.len(s)); }
            v = Vec.push(v, 2);
            print_i64(Vec.len(&v));
            let a: [i64; 3] = [4, 5, 6];
            let s = { let t: &[i64] = &a[..]; t };
            print_i64(s[2]);
            drop(s);
        }
        "#,
    );
}

#[test]
fn out_of_bounds_slice_access_and_ranges_abort_natively() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for body in [
        r#"let a:[i64;2]=[1,2]; let s:&[i64]=&a[..]; Slice.get(s,2);"#,
        r#"let a:[i64;2]=[1,2]; let i=2; let x=a[i];"#,
        r#"let a:[i64;3]=[1,2,3]; let start=2; let s=&a[start..start+2]; Slice.len(s);"#,
    ] {
        let program =
            executable::check(&format!("fn main() -> Unit ! {{io, panic}} {{{body}}}")).unwrap();
        let binary = scratch.path().join("slices_failure");
        kush::native::build(&program, &binary).unwrap();
        let result = Command::new(binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(!result.status.success(), "{body}");
        assert!(
            String::from_utf8_lossy(&result.stderr).contains("panic:"),
            "{body}"
        );
    }
}

#[test]
fn try_get_matches_reference_for_arrays_vecs_and_bytes() {
    compare(
        r#"
        enum Option<T> { None, Some(T) }
        struct Pair { left: i64, right: i64 }
        fn show(x: Option<i64>) -> i64 ! {io} {
            match x { Option.Some(value) => value, Option.None => -1 }
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let a: [i64; 3] = [10, 20, 30];
            let s: &[i64] = &a[..];
            print_i64(show(Slice.try_get(s, 0)));
            print_i64(show(Slice.try_get(s, 2)));
            print_i64(show(Slice.try_get(s, 3)));
            print_i64(show(Slice.try_get(s, -1)));
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 4); v = Vec.push(v, 5);
            let vs: &[i64] = &v[..];
            print_i64(show(Slice.try_get(vs, 1)));
            print_i64(show(Slice.try_get(vs, 2)));
            let bytes = Bytes.from("AB");
            let raw: &[i64] = &bytes[..];
            print_i64(show(Slice.try_get(raw, 0)));
            print_i64(show(Slice.try_get(raw, 1)));
            let pairs: [Pair; 2] = [Pair{left: 1, right: 2}, Pair{left: 3, right: 4}];
            let ps: &[Pair] = &pairs[..];
            match Slice.try_get(ps, 1) {
                Option.Some(pair) => print_i64(pair.left + pair.right),
                Option.None => print_i64(-1),
            }
            match Slice.try_get(ps, 2) {
                Option.Some(pair) => print_i64(pair.left),
                Option.None => print_i64(-1),
            }
        }
        "#,
    );
}

#[test]
fn inline_array_try_get_allocates_nothing() {
    let program = executable::check(
        r#"
        enum Option<T> { None, Some(T) }
        fn main() -> i64 ! {} {
            let a: [i64; 2] = [4, 5];
            let s: &[i64] = &a[..];
            match Slice.try_get(s, 1) { Option.Some(v) => v, Option.None => 0 }
        }
        "#,
    )
    .unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 5);
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);
}

#[test]
fn try_get_preserves_union_payload_layout_and_reversed_option_tags() {
    let source = r#"
        enum Option<T> { Some(T), None }
        #[noalloc]
        #[nosuspend]
        fn read(view: &[i64 | Bool], index: i64) -> i64 ! {} {
            match Slice.try_get(view, index) {
                Option.Some(value) => match value {
                    i64 @ n => n,
                    Bool @ b => if b { 7 } else { 0 },
                },
                Option.None => -1,
            }
        }
        fn main() -> Unit ! {io, panic} {
            let values: [i64 | Bool; 2] = [42, true];
            let view = &values[..];
            print_i64(read(view, 0));
            print_i64(read(view, 1));
            print_i64(read(view, 2));
            print_i64(read(view, -1));
        }
    "#;
    let program = executable::check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(output, b"42\n7\n-1\n-1\n");
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);
    compare(source);
}

#[test]
fn try_get_resolves_option_in_the_callers_module() {
    let sources = kush::program::Memory(vec![(
        "helper".into(),
        "module helper; enum Option<T> { Some(T), None } pub fn touch() -> Unit ! {} {}".into(),
    )]);
    for option in ["use std.option.Option;", "enum Option<T> { Some(T), None }"] {
        let source = format!(
            "use helper.touch;
            {option}
            fn main() -> i64 ! {{}} {{
                touch();
                let a: [i64; 2] = [7, 8];
                match Slice.try_get(&a[..], 0) {{
                    Option.Some(n) => n, Option.None => 0,
                }}
            }}"
        );
        let program = kush::program::load("main.kush", &source, &sources).unwrap();
        let checked = executable::check_program(&program).unwrap();
        assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 7);
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("option-scope");
        kush::native::build(&checked, &binary).unwrap();
        let output = Command::new(binary).output().unwrap();
        assert_eq!(output.status.code(), Some(7));
        assert!(output.stderr.is_empty());
    }
    let source = "use helper.touch;
        fn main() -> Unit ! {} {
            touch(); let a: [i64; 1] = [7];
            let _ = Slice.try_get(&a[..], 0);
        }";
    let program = kush::program::load("main.kush", source, &sources).unwrap();
    let error = executable::check_program(&program).unwrap_err();
    assert!(error.message.contains("in scope"), "{error:?}");
}
