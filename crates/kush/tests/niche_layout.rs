//! Encoded enum values keep source-level tags, ownership and borrow contracts.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let checked = check(source).unwrap();
    let (value, stats) = checked.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    for options in [
        kush::native::CodegenOptions::default(),
        kush::native::CodegenOptions::release(),
    ] {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("niche-layout");
        kush::native::build_with_codegen(&checked, &binary, false, &Default::default(), options)
            .unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
fn rejects(source: &str, expected: &str) {
    let error = check(source).unwrap_err();
    assert!(error.message.contains(expected), "{error:?}");
}

#[test]
fn optional_boxes_match_in_both_declaration_orders_and_drop_once() {
    for declaration in [
        "enum Maybe { None, Some(Box<i64>) }",
        "enum Maybe { Some(Box<i64>), None }",
    ] {
        agrees(
            &format!(
                r#"{declaration}
fn make(yes: Bool) -> Maybe ! {{alloc, panic}} {{
    if yes {{ Maybe.Some(Box.new(41)) }} else {{ Maybe.None }}
}}
fn value(m: Maybe) -> i64 ! {{panic}} {{
    match m {{ Maybe.None => 1, Maybe.Some(b) => Box.take(b) }}
}}
fn main() -> i64 ! {{alloc, panic}} {{ value(make(true)) + value(make(false)) }}
"#
            ),
            42,
        );
    }
}
#[test]
fn optional_box_containers_replace_clear_and_destroy_only_present_payloads() {
    agrees(
        r#"
enum Maybe { None, Some(Box<i64>) }
fn main() -> i64 ! {alloc, panic} {
    let values: Vec<Maybe> = [Maybe.Some(Box.new(3)), Maybe.None, Maybe.Some(Box.new(4))];
    let values = Vec.set(values, 0, Maybe.None);
    let values = Vec.set(values, 1, Maybe.Some(Box.new(5)));
    let values = Vec.clear(values);
    let values = Vec.push(values, Maybe.Some(Box.new(42)));
    drop(values);
    42
}
"#,
        42,
    );
}
#[test]
fn optional_bool_maps_without_widening_and_keeps_false_distinct_from_none() {
    agrees(
        r#"
enum Option<T> { Some(T), None }
fn lift(x: Bool) -> Option<Bool> ! {} { Option.Some(x) }
fn read(x: Option<Bool>) -> i64 ! {} {
    match x { Option.Some(true) => 10, Option.Some(false) => 20, Option.None => 12 }
}
fn main() -> i64 ! {alloc, panic} {
    let values: Vec<Bool> = [true, false];
    let values = Vec.map_in_place(values, lift);
    let values = Vec.push(values, Option.None);
    read(Vec.get(&values, 0)) + read(Vec.get(&values, 1)) + read(Vec.get(&values, 2))
}
"#,
        42,
    );
}
#[test]
fn scalar_builtin_producers_encode_none_and_full_unicode_range() {
    agrees(
        r#"
enum Option<T> { None, Some(T) }
fn code(x: Option<Char>) -> i64 ! {} {
    match x { Option.Some(c) => Int.convert(Char.code(c)), Option.None => 1 }
}
fn main() -> i64 ! {alloc, panic} {
    let a: [Bool; 1] = [false];
    let found = match Slice.try_get(&a[..], 0) { Option.Some(false) => 20, _ => 0 };
    let missing = match Slice.try_get(&a[..], 1) { Option.None => 20, _ => 0 };
    let text = "A";
    let first = code(String.scalar_at(&text, 0));
    let last = code(Str.scalar_at(String.as_str(&text), 1));
    let invalid = code(Char.from_code(1114112));
    let surrogate = code(Char.from_code(55296));
    let zero = code(Char.from_code(0));
    let maximum = code(Char.from_code(1114111));
    found + missing + first + last + invalid + surrogate + zero + maximum - 1114177
}
"#,
        42,
    );
}
#[test]
fn niches_compose_with_outer_tagged_enums_unions_records_and_callables() {
    agrees(
        r#"
enum Maybe { None, Some(Box<i64>) }
enum Outer { Empty, Full(Maybe) }
struct Holder { item: Outer, count: i64 }
fn make(x: i64) -> Maybe ! {alloc, panic} { Maybe.Some(Box.new(x)) }
fn main() -> i64 ! {alloc, panic} {
    let f: fn(i64) -> Maybe ! {alloc, panic} = make;
    let h = Holder { item: Outer.Full(f(40)), count: 2 };
    let Holder { item, count } = h;
    let sum = match item { Outer.Full(m) => match m { Maybe.Some(b) => Box.take(b), Maybe.None => 0 }, Outer.Empty => 0 };
    let mixed: Maybe | i64 = Maybe.None;
    let extra = match mixed { Maybe.None => count, Maybe.Some(b) => Box.take(b), i64 @ n => n };
    sum + extra
}
"#,
        42,
    );
}
#[test]
fn optional_references_transfer_lexical_shared_and_exclusive_capabilities() {
    agrees(
        r#"
struct Point { x: i64 }
enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {panic} {
    let mut p = Point { x: 20 };
    let shared: Maybe<&Point> = Maybe.Some(&p);
    let first = match shared { Maybe.Some(q) => q.x, Maybe.None => 0 };
    let exclusive: Maybe<&mut Point> = Maybe.Some(&mut p);
    let second = match exclusive { Maybe.Some(q) => { q.x = q.x + 2; q.x }, Maybe.None => 0 };
    first + second
}
"#,
        42,
    );
}
#[test]
fn optional_references_reject_invalidation_escape_and_unrepresented_boundaries() {
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {} { let mut p = P { x: 1 }; let r: Maybe<&P> = Maybe.Some(&p); p = P { x: 9 }; match r { Maybe.Some(q) => q.x, Maybe.None => 0 } }"#,
        "borrows",
    );
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {} { let r: Maybe<&P> = { let p = P { x: 1 }; Maybe.Some(&p) }; match r { Maybe.Some(q) => q.x, Maybe.None => 0 } }"#,
        "outlive",
    );
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn use_ref(p: Maybe<&P>) -> i64 ! {} { match p { Maybe.Some(q) => q.x, Maybe.None => 0 } }
fn main() -> i64 ! {} { let p = P { x: 42 }; use_ref(Maybe.Some(&p)) }"#,
        "lexical values",
    );
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
struct Holder { reference: Maybe<&P> } fn main() -> i64 ! {} { 0 }"#,
        "lexical values",
    );
}
#[test]
fn optional_box_moves_and_linear_payload_obligations_are_preserved() {
    rejects(
        r#"enum Maybe { None, Some(Box<i64>) }
fn consume(m: Maybe) -> Unit ! {} { drop(m) }
fn main() -> Unit ! {alloc, panic} { let m: Maybe = Maybe.Some(Box.new(42)); consume(m); consume(m); }"#,
        "move",
    );
    rejects(
        r#"#[linear] struct Token { value: i64 } enum Maybe { None, Some(Box<Token>) }
fn main() -> Unit ! {alloc, panic} { let m: Maybe = Maybe.Some(Box.new(Token { value: 42 })); drop(m); }"#,
        "linear",
    );
}

#[test]
fn optional_references_keep_merged_loop_and_stored_owner_loans() {
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {} { let mut p = P { x: 1 }; let r: Maybe<&P> = loop { break Maybe.Some(&p); }; p = P { x: 9 }; match r { Maybe.Some(q) => q.x, Maybe.None => 0 } }"#,
        "borrows",
    );
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {} { let mut p = P { x: 1 }; let r: Maybe<&mut P> = Maybe.Some(&mut p); let second = &mut p; match r { Maybe.Some(q) => q.x, Maybe.None => second.x } }"#,
        "exclusive",
    );
    agrees(
        r#"struct P { x: i64 } enum Maybe<T> { Some(T), None }
fn main() -> i64 ! {} { let p = P { x: 42 }; let reference = &p; let r: Maybe<&P> = if true { Maybe.Some(reference) } else { Maybe.None }; match r { Maybe.Some(q) => q.x, Maybe.None => 0 } }"#,
        42,
    );
}
#[test]
fn optional_reference_closures_cannot_escape_their_captured_owner() {
    rejects(
        r#"struct P { x: i64 } enum Maybe<T> { None, Some(T) }
fn main() -> i64 ! {alloc, panic} {
    let f = { let p = P { x: 42 }; let r: Maybe<&P> = Maybe.Some(&p); fn() -> i64 ! {} { match r { Maybe.Some(q) => q.x, Maybe.None => 0 } } };
    f()
}"#,
        "escape",
    );
}

/// UNBOX-CERT-CHECKER: the certificate decoders agree with the evaluator at
/// every value-set boundary, in both variant orders, and drop owners once.
#[test]
fn certificate_decoders_agree_at_every_value_set_boundary() {
    agrees(
        r#"
enum Option<T> { None, Some(T) }
enum Rev<T> { Some(T), None }
fn some(code: u32) -> i64 ! {} {
    match Char.from_code(code) { Option.Some(c) => 1, Option.None => 0 }
}
fn flip(x: Option<Bool>) -> Rev<Bool> ! {} {
    match x { Option.Some(b) => Rev.Some(b), Option.None => Rev.None }
}
fn score(x: Rev<Bool>) -> i64 ! {} {
    match x { Rev.Some(true) => 4, Rev.Some(false) => 2, Rev.None => 1 }
}
fn main() -> i64 ! {alloc, panic} {
    // Inside: 0xD7FF, 0xE000, 0x10FFFF, 0; outside: 0xD800, 0xDFFF, 0x110000.
    let chars = some(55295) + some(57344) + some(1114111) + some(0)
        + some(55296) + some(57343) + some(1114112);
    let n = 3;
    let bools = score(flip(Option.Some(n < 4))) + score(flip(Option.Some(n > 4)))
        + score(flip(Option.None));
    let boxed: Rev<Box<i64>> = Rev.Some(Box.new(30));
    let empty: Rev<Box<i64>> = Rev.None;
    let boxes = match boxed { Rev.Some(b) => Box.take(b), Rev.None => 0 }
        + match empty { Rev.Some(b) => Box.take(b), Rev.None => 1 };
    chars + bools + boxes
}
"#,
        4 + 7 + 31,
    );
}
