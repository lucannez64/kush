//! Whole mutation of records with borrowed fields through `&mut Holder<'a>`.
//! `*h = value` replaces every leaf at once: each written leaf must outlive
//! the record's lifetime (invariant under `&mut`), and the owner behind the
//! reference then holds the new leaves, so a caller keeps the written source
//! borrowed. Positive cases run in both backends with balanced allocations.
use kush::executable::{MemoryStats, check};

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

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowed-record-mutation-test");
        kush::native::build(&program, &binary).unwrap();
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

const RECORDS: &str = r#"
    struct Point { x: i64, y: i64 }
    struct Holder<'a> { point: &'a Point, note: i64 }
    struct Window<'a> { view: &'a mut [i64], note: i64 }
    struct Named<'a> { point: &'a Point, name: String }
"#;

fn with_records(body: &str) -> String {
    format!("{RECORDS}\n{body}")
}

#[test]
fn whole_records_are_replaced_through_exclusive_references() {
    agrees(
        &with_records(
            r#"
            fn reset<'a>(h: &mut Holder<'a>, p: &'a Point) -> Unit ! {} {
                *h = Holder { point: p, note: 7 };
            }
            fn bump<'a>(h: &mut Holder<'a>) -> Unit ! {panic} { h.note = h.note + 1; }
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let b = Point { x: 30, y: 40 };
                let mut h = Holder { point: &a, note: 1 };
                reset(&mut h, &b);
                bump(&mut h);
                h.point.x + h.note
            }"#,
        ),
        38,
        "",
    );
    // A local reference, a branch-selected owner, and a loop.
    agrees(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let p0 = Point { x: 1, y: 2 };
                let p1 = Point { x: 10, y: 20 };
                let mut h = Holder { point: &p0, note: 0 };
                let mut g = Holder { point: &p0, note: 0 };
                let mut i = 0;
                while i < 3 {
                    let r = if i == 2 { &mut g } else { &mut h };
                    if i == 1 { *r = Holder { point: &p1, note: i }; } else { *r = Holder { point: &p0, note: i }; }
                    i = i + 1;
                }
                h.point.x * 100 + h.note * 10 + g.note
            }"#,
        ),
        1012,
        "",
    );
    // An exclusive slice field moves to the new source; owned metadata of the
    // old record is dropped exactly once.
    agrees(
        &with_records(
            r#"
            fn swap_in<'a>(h: &mut Window<'a>, v: &'a mut [i64]) -> Unit ! {} {
                *h = Window { view: v, note: 2 };
            }
            fn rename<'a>(h: &mut Named<'a>, p: &'a Point) -> Unit ! {alloc, panic} {
                *h = Named { point: p, name: String.from("second") };
            }
            fn main() -> i64 ! {alloc, panic} {
                let mut a: [i64; 2] = [1, 2];
                let mut b: [i64; 2] = [3, 4];
                {
                    let mut h = Window { view: &mut a[..], note: 1 };
                    swap_in(&mut h, &mut b[..]);
                    let Window { view, note } = h;
                    Slice.set(view, 0, 30);
                }
                let p = Point { x: 5, y: 6 };
                let q = Point { x: 7, y: 8 };
                let mut n = Named { point: &p, name: String.from("first") };
                rename(&mut n, &q);
                let Named { point, name } = n;
                b[0] + a[0] + point.x + String.len(&name)
            }"#,
        ),
        30 + 1 + 7 + 6,
        "",
    );
}

#[test]
fn a_shorter_lived_reference_cannot_be_written_through_a_longer_record() {
    rejects(
        &with_records(
            r#"
            fn bad<'long, 'short>(h: &mut Holder<'long>, p: &'short Point) -> Unit ! {} {
                *h = Holder { point: p, note: 7 };
            }
            fn main() -> i64 ! {} { 0 }"#,
        ),
        "must be borrowed for lifetime 'long'",
    );
    rejects(
        &with_records(
            r#"
            fn bad<'a, 'b>(h: &mut Holder<'a>, other: Holder<'b>) -> Unit ! {} { *h = other; }
            fn main() -> i64 ! {} { 0 }"#,
        ),
        "lifetime mismatch",
    );
    // With an outlives bound the write is accepted, and the caller must
    // prove the bound.
    check(&with_records(
        r#"
        fn copy_into<'a, 'b: 'a>(h: &mut Holder<'a>, other: Holder<'b>) -> Unit ! {} { *h = other; }
        fn main() -> i64 ! {} { 0 }"#,
    ))
    .unwrap();
    // A caller cannot write a block-local owner into an outer record.
    rejects(
        &with_records(
            r#"
            fn reset<'a>(h: &mut Holder<'a>, p: &'a Point) -> Unit ! {} {
                *h = Holder { point: p, note: 7 };
            }
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let mut h = Holder { point: &a, note: 1 };
                {
                    let b = Point { x: 30, y: 40 };
                    reset(&mut h, &b);
                }
                h.point.x
            }"#,
        ),
        "an outer container was updated with a reference to this block-local value",
    );
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let mut h = Holder { point: &a, note: 1 };
                {
                    let b = Point { x: 30, y: 40 };
                    let r = &mut h;
                    *r = Holder { point: &b, note: 2 };
                }
                h.point.x
            }"#,
        ),
        "",
    );
}

#[test]
fn written_sources_stay_borrowed_by_the_record() {
    // Through a call, a local reference, and a branch-selected reference.
    rejects(
        &with_records(
            r#"
            fn reset<'a>(h: &mut Holder<'a>, p: &'a Point) -> Unit ! {} {
                *h = Holder { point: p, note: 7 };
            }
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let mut b = Point { x: 30, y: 40 };
                let mut h = Holder { point: &a, note: 1 };
                reset(&mut h, &b);
                b = Point { x: 0, y: 0 };
                h.point.x
            }"#,
        ),
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let mut b = Point { x: 30, y: 40 };
                let mut h = Holder { point: &a, note: 1 };
                {
                    let r = &mut h;
                    *r = Holder { point: &b, note: 2 };
                }
                b = Point { x: 0, y: 0 };
                h.point.x
            }"#,
        ),
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let mut b = Point { x: 30, y: 40 };
                let mut h1 = Holder { point: &a, note: 1 };
                let mut h2 = Holder { point: &a, note: 1 };
                let flag = true;
                {
                    let r = if flag { &mut h1 } else { &mut h2 };
                    *r = Holder { point: &b, note: 2 };
                }
                b = Point { x: 0, y: 0 };
                h2.point.x
            }"#,
        ),
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // An exclusive slice field written by a callee keeps its source
    // exclusively borrowed.
    rejects(
        &with_records(
            r#"
            fn swap_in<'a>(h: &mut Window<'a>, v: &'a mut [i64]) -> Unit ! {} {
                *h = Window { view: v, note: 2 };
            }
            fn main() -> i64 ! {panic} {
                let mut a: [i64; 2] = [1, 2];
                let mut b: [i64; 2] = [3, 4];
                let mut h = Window { view: &mut a[..], note: 1 };
                swap_in(&mut h, &mut b[..]);
                let n = b[0];
                let Window { view, note } = h;
                Slice.get(view, 0) + n
            }"#,
        ),
        "cannot read an owner while an exclusive '&mut [T]' view of it is live",
    );
}

#[test]
fn exclusive_record_references_exclude_aliases() {
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let b = Point { x: 30, y: 40 };
                let mut h = Holder { point: &a, note: 1 };
                let s = &h;
                let r = &mut h;
                *r = Holder { point: &b, note: 2 };
                s.note
            }"#,
        ),
        "cannot create an exclusive '&mut Record'",
    );
    // A shared borrow cannot replace an exclusive field.
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let mut a: [i64; 2] = [1, 2];
                let b: [i64; 2] = [3, 4];
                let mut h = Window { view: &mut a[..], note: 1 };
                let r = &mut h;
                *r = Window { view: &b[..], note: 2 };
                0
            }"#,
        ),
        "type mismatch",
    );
    rejects(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let h = Holder { point: &a, note: 1 };
                let r = &mut h;
                0
            }"#,
        ),
        "cannot mutably borrow an immutable binding",
    );
    // A value read before the write is unaffected by it. (A projected field
    // reference would keep the whole record loaned, so read a scalar.)
    agrees(
        &with_records(
            r#"
            fn main() -> i64 ! {panic} {
                let a = Point { x: 1, y: 2 };
                let b = Point { x: 30, y: 40 };
                let mut h = Holder { point: &a, note: 1 };
                let old = h.point.x;
                {
                    let r = &mut h;
                    *r = Holder { point: &b, note: 2 };
                }
                old + h.point.x
            }"#,
        ),
        31,
        "",
    );
}
