//! Checked UTF-8 `String` values: literals, fallible conversion from owned
//! `Bytes`, byte-vs-scalar indexing, explicit byte conversions, and native
//! agreement. `String` is a distinct static type over the byte-buffer ABI; it
//! is never created from unvalidated bytes.
use kush::executable::check;

const PREFIX: &str = "use std.option.Option;\nuse std.result.Result;\n";

fn rejects(source: &str, fragment: &str) {
    let source = format!("{PREFIX}{source}");
    let error = check(&source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("strings-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = format!("{PREFIX}{source}");
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    if let Some(output) = native(&source) {
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

fn panics(source: &str) {
    let source = format!("{PREFIX}{source}");
    let program = check(&source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("panic:"), "{source}: {error:?}");
    if let Some(output) = native(&source) {
        assert!(!output.status.success(), "{source} should abort natively");
    }
}

#[test]
fn string_example_matches_documented_output() {
    let program = check(include_str!("../../../examples/strings.kush")).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "6\n5\n195\n233\n6\n1\n");
}

#[test]
fn literals_use_byte_and_scalar_indexing_explicitly() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"héllo\";
            print_i64(String.len(&text));
            print_i64(String.scalar_len(&text));
            print_i64(text.len());
            print_i64(text.scalar_len());
            print_i64(String.byte_at(&text, 0));
            print_i64(text.byte_at(1));
            match text.scalar_at(1) {
                Option.Some(c) => print_int(Char.code(c)),
                Option.None => print_i64(-1),
            }
            match String.scalar_at(&text, 5) {
                Option.Some(_) => print_i64(1),
                Option.None => print_i64(0),
            }
            match String.scalar_at(&text, -1) {
                Option.Some(_) => print_i64(1),
                Option.None => print_i64(0),
            }
            0
        }",
        0,
        "6\n5\n6\n5\n104\n195\n233\n0\n0\n",
    );
}

#[test]
fn bytes_and_string_round_trip_with_explicit_validation() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let bytes = Bytes.from(\"hé\");
            match String.from_utf8(bytes) {
                Result.Ok(text) => {
                    print_i64(text.len());
                    print_i64(text.scalar_len());
                    let raw = text.as_bytes();
                    print_i64(Bytes.len(&raw));
                    let out = text.bytes();
                    print_i64(Bytes.get(&out, 1));
                },
                Result.Err(_) => print_i64(-1),
            }
            let mut bad = Bytes.with_capacity(1);
            bad = Bytes.push(bad, 255);
            match String.from_utf8(bad) {
                Result.Ok(_) => print_i64(-1),
                Result.Err(b) => print_i64(Bytes.len(&b)),
            }
            0
        }",
        0,
        "3\n2\n3\n195\n1\n",
    );
}

#[test]
fn string_from_and_method_syntax_are_explicit() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let literal = String.from(\"abc\");
            print_i64(literal.len());
            let copied = literal.as_bytes();
            print_i64(Bytes.len(&copied));
            0
        }",
        0,
        "3\n3\n",
    );
}

#[test]
fn string_is_not_bytes_or_sliceable_without_conversion() {
    rejects(
        "fn take(s: String) -> Unit ! {} {}
        fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); take(b); }",
        "type mismatch",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); let s = String.from(b); }",
        "requires exactly one string literal",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let s = \"abc\"; let slice = &s[..]; }",
        "String does not support byte slicing",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let s = \"abc\"; s == s; }",
        "opaque-handle equality",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let s = \"abc\"; let b = s.bytes(); String.len(&s); }",
        "cannot borrow a moved owner",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let s: String = 1; }",
        "type mismatch",
    );
}

#[test]
fn string_cleanup_is_balanced_for_ok_and_invalid_conversions() {
    let source = format!(
        "{PREFIX}fn main() -> Unit ! {{io, alloc, panic}} {{
            let good = String.from_utf8(Bytes.from(\"ok\"));
            let bad = String.from_utf8(Bytes.push(Bytes.with_capacity(1), 255));
            drop(good);
            drop(bad);
        }}"
    );
    let program = check(&source).unwrap();
    let (status, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    // Two byte buffers: the valid one is moved into Result<String,Bytes> and
    // the invalid one stays in Result's Err(Bytes) payload.
    assert_eq!(stats.allocations, 2);
    if let Some(output) = native(&source) {
        assert!(output.status.success());
    }
}

#[test]
fn string_record_and_box_fields_cleanup_exactly_once() {
    let source = format!(
        "{PREFIX}struct Wrapped {{ text: String }}
        fn main() -> Unit ! {{io, alloc, panic}} {{
            let wrapped = Wrapped {{ text: \"abc\" }};
            let Wrapped {{ text }} = wrapped;
            print_i64(text.len());
            let boxed = Box.new(\"de\");
            let moved = Box.take(boxed);
            print_i64(moved.scalar_len());
        }}"
    );
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "3\n2\n");
    assert_eq!(stats.allocations, stats.deallocations);
    if let Some(output) = native(&source) {
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap(), "3\n2\n");
    }
}

#[test]
fn utf8_validation_rejects_overlong_surrogates_truncation_and_high_points() {
    agrees(
        "fn rejected(bytes: Bytes) -> i64 ! {alloc, panic} {
            match String.from_utf8(bytes) {
                Result.Ok(_) => 1,
                Result.Err(_) => 0,
            }
        }
        fn two(a: i64, b: i64) -> Bytes ! {alloc, panic} {
            let mut bytes = Bytes.with_capacity(2);
            bytes = Bytes.push(bytes, a);
            Bytes.push(bytes, b)
        }
        fn three(a: i64, b: i64, c: i64) -> Bytes ! {alloc, panic} {
            let mut bytes = Bytes.with_capacity(3);
            bytes = Bytes.push(bytes, a);
            bytes = Bytes.push(bytes, b);
            Bytes.push(bytes, c)
        }
        fn four(a: i64, b: i64, c: i64, d: i64) -> Bytes ! {alloc, panic} {
            let mut bytes = Bytes.with_capacity(4);
            bytes = Bytes.push(bytes, a);
            bytes = Bytes.push(bytes, b);
            bytes = Bytes.push(bytes, c);
            Bytes.push(bytes, d)
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut sum = 0;
            sum = sum + rejected(two(0xC0, 0x80));
            sum = sum + rejected(three(0xED, 0xA0, 0x80));
            sum = sum + rejected(four(0xF4, 0x90, 0x80, 0x80));
            sum = sum + rejected(two(0xE2, 0x82));
            sum = sum + rejected(two(0xFF, 0x80));
            sum = sum + rejected(three(0xE2, 0x82, 0xAC));
            print_i64(sum);
            let valid = \"𐍈\";
            print_i64(String.len(&valid));
            print_i64(String.scalar_len(&valid));
            0
        }",
        0,
        "1\n4\n1\n",
    );
}

#[test]
fn string_byte_indexes_are_checked() {
    panics("fn main() -> i64 ! {io, alloc, panic} { let s = \"abc\"; String.byte_at(&s, 3) }");
}

#[test]
fn owning_string_conversions_cannot_erase_linear_obligations() {
    for body in [
        r#"let s: String @[1] = "hi"; drop(String.bytes(s));"#,
        r#"let s: String @[1] = "hi"; let alias = s; drop(alias.bytes());"#,
        r#"let b: Bytes @[1] = Bytes.from("hi"); drop(String.from_utf8(b));"#,
        r#"let b: Bytes @[1] = Bytes.from("hi"); let alias = b; drop(String.from_utf8(alias));"#,
    ] {
        rejects(
            &format!("fn main() -> Unit ! {{alloc, panic}} {{ {body} }}"),
            "linear",
        );
    }
}

#[test]
fn borrowed_text_example_matches_documented_output() {
    let source = include_str!("../../../examples/borrowed-text.kush");
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, 0);
    let expected = "6\n5\n5\n2\n1\n233\n195\n169\n3\n3\n0\n1\n3\n3\n";
    assert_eq!(String::from_utf8(output).unwrap(), expected);
    if let Some(output) = native(source) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    }
}

#[test]
fn borrowed_text_views_read_ascii_multibyte_and_empty() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let ascii = \"abc\";
            let a = ascii.as_str();
            print_i64(Str.len(a));
            print_i64(Str.scalar_len(a));
            print_i64(Str.byte_at(a, 2));
            match Str.scalar_at(a, 1) {
                Option.Some(c) => print_int(c.code()),
                Option.None => print_i64(-1),
            }

            let text = \"héllo\";
            let view = text.as_str();
            let middle = view.substr(1, 3);
            print_i64(middle.len());
            print_i64(middle.scalar_len());
            match middle.scalar_at(0) {
                Option.Some(c) => print_int(c.code()),
                Option.None => print_i64(-1),
            }
            print_i64(middle.byte_at(1));

            let empty = String.from(\"\");
            let nothing = empty.as_str();
            print_i64(nothing.len());
            print_i64(nothing.scalar_len());
            print_i64(nothing[0..0].len());
            match nothing.scalar_at(0) {
                Option.Some(_) => print_i64(-1),
                Option.None => print_i64(0),
            }
            0
        }",
        0,
        "3\n3\n99\n98\n2\n1\n233\n169\n0\n0\n0\n0\n",
    );
}

#[test]
fn borrowed_text_views_allocate_nothing_and_release_the_owner() {
    let source = format!(
        "{PREFIX}fn main() -> i64 ! {{io, alloc, panic}} {{
            let text = \"héllo\";
            let view = text.as_str();
            let part = view[1..3];
            let nested = part[0..2];
            let owned: String = nested.to_string();
            print_i64(Str.len(nested));
            print_i64(String.len(&owned));
            0
        }}"
    );
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "2\n2\n");
    // One String literal plus the one explicit to_string copy; every view is a
    // borrowed descriptor and allocates nothing.
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.allocations, stats.deallocations);
    if let Some(output) = native(&source) {
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap(), "2\n2\n");
    }
}

#[test]
fn nested_text_substrings_agree_and_check_scalar_boundaries() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"αβγδ\";
            let view = text.as_str();
            let middle = view[2..6];
            let inner = middle[0..2];
            print_i64(Str.len(middle));
            print_i64(Str.scalar_len(middle));
            match Str.scalar_at(inner, 0) {
                Option.Some(c) => print_int(c.code()),
                Option.None => print_i64(-1),
            }
            print_i64(Str.len(inner));
            0
        }",
        0,
        "4\n2\n946\n2\n",
    );
    for bounds in [
        "(1, 3)",  // start inside the first two-byte scalar
        "(0, 7)",  // end inside the last two-byte scalar
        "(3, 3)",  // a zero-width range still needs a boundary start
        "(6, 2)",  // reversed
        "(-1, 2)", // negative
        "(0, 9)",  // past the end
    ] {
        panics(&format!(
            "fn main() -> i64 ! {{alloc, panic}} {{
                let text = \"αβγδ\";
                let view = text.as_str();
                view.substr{bounds}.len()
            }}"
        ));
    }
}

#[test]
fn borrowed_text_helpers_infer_elide_and_shorten_lifetimes() {
    agrees(
        "fn whole(text: &str) -> &str ! {} { text }
        fn tail<'a>(text: &'a str) -> &'a str ! {panic} { text[1..] }
        fn shorten<'long: 'short, 'short>(text: &'long str) -> &'short str ! {} { text }
        fn pick<'a>(first: &'a str, second: &str) -> &'a str ! {} { first }
        fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abcdef\";
            let all = whole(text.as_str());
            print_i64(all.len());
            let rest = tail(all);
            print_i64(rest.len());
            let shorter: &str = shorten(text.as_str());
            print_i64(shorter.scalar_len());
            let chosen = pick(text.as_str(), text.as_str());
            print_i64(chosen.len());
            0
        }",
        0,
        "6\n5\n6\n6\n",
    );
}

#[test]
fn borrowed_text_fields_and_record_references_keep_their_source_borrowed() {
    agrees(
        r#"struct Text<'a> { text: &'a str, note: i64 }
        fn make<'a>(text: &'a str, note: i64) -> Text<'a> ! {panic} {
            Text { text: text, note: note }
        }
        fn read<'a>(text: Text<'a>) -> i64 ! {panic} {
            Str.len(text.text) + text.note
        }
        fn read_ref<'a>(text: &'a Text<'a>) -> i64 ! {panic} {
            Str.len(text.text) + text.note
        }
        fn main() -> i64 ! {alloc, panic} {
            let source = "abcd";
            let text = make(source.as_str(), 2);
            read(text) + read_ref(&text) - 6
        }"#,
        6,
        "",
    );
    // Returning the text view keeps the original String borrowed.
    agrees(
        r#"struct Text<'a> { text: &'a str }
        fn get<'a>(text: &'a Text<'a>) -> &'a str ! {panic} { text.text }
        fn main() -> i64 ! {alloc, panic} {
            let source = "abcd";
            let text = Text { text: source.as_str() };
            Str.len(get(&text))
        }"#,
        4,
        "",
    );
}

#[test]
fn borrowed_text_containers_carry_element_lifetimes() {
    agrees(
        r#"fn read_box<'a>(text: &'a Box<&'a str>) -> i64 ! {panic} {
            Str.len(Box.read(text))
        }
        fn read_vec<'a>(text: &'a Vec<&'a str>) -> i64 ! {panic} {
            Str.len(Vec.get(text, 0)) + Str.len(Vec.get(text, 1))
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let a = "abcd";
            let b = "wxyz";
            let boxed: Box<&str> = Box.new(a.as_str());
            let values: Vec<&str> = [a.as_str(), b.as_str()];
            print_i64(read_box(&boxed));
            print_i64(read_vec(&values));
            0
        }"#,
        0,
        "4\n8\n",
    );
    // The element owner stays loaned while a read view is live.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a = "abcd";
            let boxed: Box<&str> = Box.new(a.as_str());
            let view = Box.read(&boxed);
            a = "wxyz";
            Str.len(view)
        }"#,
        "cannot replace an owner",
    );
}

#[test]
fn borrowed_text_escape_positions_are_rejected() {
    // `&"abc"` is an `&String` place reference; it does not implicitly become
    // a `&str` descriptor without `String.as_str`.
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let view: &str = &\"abc\"; }",
        "type mismatch",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let view = \"abc\".as_str(); }",
        "temporary borrows are not supported",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let view: &str = \"abc\"; }",
        "type mismatch",
    );
    rejects(
        "fn only() -> &str ! {} { \"abc\" }",
        "borrowed slice result",
    );
    rejects(
        "fn only(text: &str) -> &str ! {alloc, panic} {
            let owned = text.to_string();
            owned.as_str()
        }",
        "outlive",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            let pair = (1, view);
        }",
        "tuples cannot store references, slice views, or borrowed records",
    );
    // A temporary `String` borrowed for a call has hidden storage in the
    // enclosing block; the returned view is usable there and cannot escape.
    agrees(
        "fn main() -> i64 ! {alloc, panic} { let view = String.as_str(&\"abc\"); Str.len(view) }",
        3,
        "",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            let mixed = if true { 1 } else { view };
        }",
        "unions cannot contain borrowed references or slice views",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            let values: [&str; 1] = [view];
        }",
        "inline array exceeds the 32-word layout budget",
    );
    rejects(
        "enum Holder { Text(&str) }
        fn main() -> Unit ! {alloc, panic} { }",
        "enums cannot store borrowed references or slice views",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            let closure = fn() -> i64 ! {} { Str.len(view) };
            let _ = closure();
        }",
        "cannot capture a borrowed '&str' text view",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            let f: fn(&str) -> i64 ! {} = fn(text: &str) -> i64 ! {} { Str.len(text) };
        }",
        "function arrow types may borrow slice views",
    );
    rejects(
        "fn first(text: &str) -> i64 ! {panic} { Str.len(text) }
        fn main() -> Unit ! {} { let f = first; }",
        "a function value cannot carry an owner reference or &str text view",
    );
    agrees(
        "fn main() -> i64 ! {alloc, panic} { let view = String.as_str(&\"abc\"); Str.len(view) }",
        3,
        "",
    );
    rejects(
        "fn take(text: &mut str) -> Unit ! {} { }",
        "mutable borrowed text",
    );
    rejects("fn take(text: str) -> Unit ! {} { }", "'str' is unsized");
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let view = s.as_str();
            match view { _ => () }
        }",
        "cannot match a divergent",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let s = \"abc\";
            let mut view = s.as_str();
        }",
        "borrowed views are not mutable bindings",
    );
}

#[test]
fn borrowed_text_keeps_its_owner_until_the_last_view_use() {
    rejects(
        "fn main() -> Unit ! {io, alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            let raw = text.bytes();
            print_i64(Str.len(view));
        }",
        "cannot move an owner while it is borrowed",
    );
    rejects(
        "fn main() -> Unit ! {io, alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            drop(text);
            print_i64(Str.len(view));
        }",
        "cannot move or drop an owner or view while a slice view",
    );
    rejects(
        "fn main() -> Unit ! {io, alloc, panic} {
            let text = \"abcdef\";
            let view = text.as_str();
            let part = view[1..3];
            let raw = text.bytes();
            print_i64(Str.len(part));
        }",
        "cannot move an owner while it is borrowed",
    );
    rejects(
        "fn main() -> Unit ! {io, alloc, panic} {
            let mut text = \"abc\";
            let view = text.as_str();
            text = \"zyx\";
            print_i64(Str.len(view));
        }",
        "cannot replace an owner while a slice view or reference borrows it",
    );
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            print_i64(Str.len(view));
            let owned: String = text.as_str().to_string();
            print_i64(String.len(&owned));
            let raw = text.bytes();
            print_i64(Bytes.len(&raw));
            0
        }",
        0,
        "3\n3\n3\n",
    );
}

#[test]
fn borrowed_text_works_in_loops_branches_and_method_chains() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abcdef\";
            let whole = text.as_str();
            let mut i = 0;
            let mut count = 0;
            while i < 3 {
                let part = whole[i..i + 1];
                count = count + Str.len(part);
                i = i + 1;
            }
            print_i64(count);

            let choose = if count == 3 { whole[0..2] } else { whole[3..5] };
            print_i64(Str.len(choose));

            print_i64(text.as_str().len());
            print_i64(text.as_str().substr(1, 4).scalar_len());
            let owned: String = text.as_str().to_string();
            print_i64(String.len(&owned));
            0
        }",
        0,
        "3\n2\n6\n3\n6\n",
    );
}

#[test]
fn borrowed_text_reads_are_noalloc_and_nosuspend() {
    agrees(
        "#[noalloc]
        #[nosuspend]
        fn first(text: &str) -> &str ! {panic} {
            if Str.scalar_len(text) == 0 { text } else { text[0..1] }
        }
        #[noalloc]
        #[nosuspend]
        fn count(text: &str) -> i64 ! {} { Str.len(text) }
        fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abc\";
            print_i64(first(text.as_str()).len());
            print_i64(count(text.as_str()));
            0
        }",
        0,
        "1\n3\n",
    );
    rejects(
        "fn copy(text: &str) -> String ! {panic} { let owned = text.to_string(); owned }
        fn main() -> Unit ! {} { }",
        "requires effects {alloc",
    );
}

#[test]
fn borrowed_text_namespace_forms_and_scalar_bounds() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"héllo\";
            let view = String.as_str(&text);
            let part = String.substr(&text, 1, 3);
            let nested = Str.substr(view, 3, 6);
            print_i64(Str.len(view));
            print_i64(Str.len(part));
            print_i64(Str.len(nested));
            match Str.scalar_at(view, 9) {
                Option.Some(_) => print_i64(-1),
                Option.None => print_i64(0),
            }
            match Str.scalar_at(view, -1) {
                Option.Some(_) => print_i64(-1),
                Option.None => print_i64(0),
            }
            0
        }",
        0,
        "6\n2\n3\n0\n0\n",
    );
    panics(
        "fn main() -> i64 ! {alloc, panic} {
            let text = \"héllo\";
            let view = text.as_str();
            Str.byte_at(view, 6)
        }",
    );
    panics(
        "fn main() -> i64 ! {alloc, panic} {
            let text = \"héllo\";
            let view = text.as_str();
            Str.byte_at(view, -1)
        }",
    );
}

#[test]
fn borrowed_text_task_and_generic_positions_are_rejected() {
    rejects(
        "fn main() -> Unit ! {io, alloc, panic, suspend} {
            let text = \"abc\";
            let view = text.as_str();
            Task.scope(fn() -> Unit ! {io, panic, suspend} {
                Task.yield();
                print_i64(Str.len(view));
            });
        }",
        "cannot capture a borrowed '&str' text view",
    );
    rejects(
        "fn identity<T>(value: T) -> T ! {} { value }
        fn main() -> Unit ! {alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            let other = identity::<&str>(view);
        }",
        "borrowed record cannot be passed through an ordinary generic type parameter",
    );
    // An explicit shorter text result infers its outlives bound from the
    // returned text parameter.
    check("fn escape<'a, 'b>(text: &'a str) -> &'b str ! {} { text }").unwrap();
    // The summary exports 'a: 'b for both branch origins. A caller must
    // establish that bound; accepting the declaration does not erase it.
    check("fn ambiguous<'a, 'b>(first: &'a str, second: &'b str) -> &'b str ! {} { if true { first } else { second } }").unwrap();
    rejects(
        "fn caller<'a, 'b>(first: &'a str, second: &'b str) -> i64 ! {} { Str.len(ambiguous(first, second)) }
        fn ambiguous<'a, 'b>(first: &'a str, second: &'b str) -> &'b str ! {} { if true { first } else { second } }",
        "cannot establish the callee's outlives constraint 'a: 'b",
    );
    // An elided text result with several sources is an anonymous intersection
    // outlived by every source; it cannot be named as a caller lifetime.
    check("fn ambiguous(first: &str, second: &str) -> &str ! {} { if true { first } else { second } }").unwrap();
    rejects(
        "fn main() -> Unit ! {alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            let mut part = &mut view[0..1];
        }",
        "mutable borrowed text",
    );
}

#[test]
fn borrowed_text_loans_extend_through_later_arguments() {
    rejects(
        "fn combine(view: &str, b: i64) -> i64 ! {panic} { Str.len(view) + b }
        fn main() -> Unit ! {io, alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            let result = combine(view, { drop(text); 1 });
            print_i64(result);
        }",
        "cannot move or drop an owner or view while a slice view",
    );
    agrees(
        "fn combine(view: &str, b: i64) -> i64 ! {panic} { Str.len(view) + b }
        fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abc\";
            let view = text.as_str();
            let result = combine(view, Str.scalar_len(view));
            print_i64(result);
            0
        }",
        0,
        "6\n",
    );
}

#[test]
fn borrowed_text_subview_returns_are_tied_to_the_parameter() {
    agrees(
        "fn first<'a>(text: &'a str) -> &'a str ! {panic} { text[0..1] }
        fn itself(text: &str) -> &str ! {panic} { text[0..] }
        fn main() -> i64 ! {io, alloc, panic} {
            let text = \"abcdef\";
            print_i64(first(text.as_str()).len());
            print_i64(itself(text.as_str()).scalar_len());
            0
        }",
        0,
        "1\n6\n",
    );
}
