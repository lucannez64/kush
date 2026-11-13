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

// Independent review (R-REVIEW) regressions.
#[test]
fn review_partial_writes_keep_the_other_leaves_loaned() {
    // Writing one field of an owner keeps the other fields' loans.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Outer<'a> { h: Holder<'a>, other: &'a [i64] }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut c: Vec<i64> = [5, 6, 7, 8];
    let mut o = Outer { h: Holder { point: &a, note: 0 }, other: &c[..] };
    {
        let r = &mut o.h;
        *r = Holder { point: &a, note: 1 };
    }
    c = [1];
    let mut junk: Vec<i64> = [41, 42, 43, 44];
    Slice.get(o.other, 3)
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Pair<'a> { l: Holder<'a>, r: Holder<'a> }
fn main() -> i64 ! {panic} {
    let a = Point { x: 1, y: 2 };
    let mut b = Point { x: 77, y: 0 };
    let mut p = Pair { l: Holder { point: &a, note: 0 }, r: Holder { point: &b, note: 0 } };
    {
        let w = &mut p.l;
        *w = Holder { point: &a, note: 1 };
    }
    b = Point { x: 3, y: 3 };
    p.r.point.x
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Writing one container element keeps the other elements' loans.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut b = Point { x: 77, y: 0 };
    let c = Point { x: 8, y: 0 };
    let mut v = [Holder { point: &c, note: 0 }, Holder { point: &b, note: 0 }];
    {
        let r = &mut v[0];
        *r = Holder { point: &a, note: 1 };
    }
    b = Point { x: 3, y: 3 };
    Vec.get(&v, 1).point.x
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // A write through an unbound place reference is tracked.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { h: Win<'a>, other: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: [i64; 4] = [1, 2, 3, 4];
    let mut o = Outer { h: Win { view: &a[..], note: 0 }, other: 0 };
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        *(&mut o.h) = Win { view: &b[..], note: 1 };
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.h.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: [i64; 4] = [1, 2, 3, 4];
    let mut v = [Win { view: &a[..], note: 0 }];
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        *(&mut v[0]) = Win { view: &b[..], note: 1 };
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(Vec.get(&v, 0).view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // A leaf copied from another record argument flows into the caller's record.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn steal<'a>(h: &mut Win<'a>, g: &Win<'a>) -> Unit ! {} {
    *h = Win { view: g.view, note: 1 };
}
fn main() -> i64 ! {alloc, panic} {
    let a: [i64; 4] = [1, 2, 3, 4];
    let mut h1 = Win { view: &a[..], note: 0 };
    let mut b: Vec<i64> = [70, 71, 72, 73];
    {
        let h2 = Win { view: &b[..], note: 0 };
        steal(&mut h1, &h2);
    }
    b = [5];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(h1.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
fn steal<'a>(h: &mut Holder<'a>, g: &Holder<'a>) -> Unit ! {} {
    *h = Holder { point: g.point, note: 1 };
}
fn main() -> i64 ! {panic} {
    let a = Point { x: 1, y: 2 };
    let mut h1 = Holder { point: &a, note: 0 };
    let mut b = Point { x: 77, y: 0 };
    {
        let h2 = Holder { point: &b, note: 0 };
        steal(&mut h1, &h2);
    }
    b = Point { x: 123, y: 0 };
    h1.point.x
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
fn steal<'a>(h: &mut Holder<'a>, g: &mut Holder<'a>) -> Unit ! {} {
    *h = Holder { point: g.point, note: 1 };
}
fn main() -> i64 ! {panic} {
    let a = Point { x: 1, y: 2 };
    let mut h1 = Holder { point: &a, note: 0 };
    {
        let b = Point { x: 77, y: 0 };
        let mut h2 = Holder { point: &b, note: 0 };
        steal(&mut h1, &mut h2);
    }
    let z = Point { x: 123, y: 0 };
    h1.point.x
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // A field read through the reference after the write keeps the new
    // source loaned.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
fn main() -> i64 ! {panic} {
    let a = Point { x: 1, y: 2 };
    let mut b = Point { x: 30, y: 40 };
    let mut h = Holder { point: &a, note: 1 };
    let r = &mut h;
    *r = Holder { point: &b, note: 2 };
    let p = r.point;
    b = Point { x: 0, y: 0 };
    p.x
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Field, element, and argument writes that stay within their storage.
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Outer<'a> { h: Holder<'a>, other: &'a Point }
fn set_inner<'a>(o: &mut Outer<'a>, p: &'a Point) -> Unit ! {} {
    *(&mut o.h) = Holder { point: p, note: 9 };
}
fn steal<'a>(h: &mut Holder<'a>, g: &Holder<'a>) -> Unit ! {} { *h = Holder { point: g.point, note: 1 }; }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 30, y: 40 };
    let mut o = Outer { h: Holder { point: &a, note: 0 }, other: &a };
    set_inner(&mut o, &b);
    let g = Holder { point: &b, note: 0 };
    let mut h = Holder { point: &a, note: 0 };
    steal(&mut h, &g);
    o.h.point.x + o.h.note + h.point.x
}"#,
        69,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Outer<'a> { h: Holder<'a>, other: &'a Point }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 30, y: 40 };
    let mut o = Outer { h: Holder { point: &a, note: 0 }, other: &a };
    {
        let r = &mut o.h;
        *r = Holder { point: &b, note: 1 };
    }
    o.h.point.x + o.h.note + o.other.x
}"#,
        32,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 30, y: 40 };
    let mut v = [Holder { point: &a, note: 1 }, Holder { point: &a, note: 2 }];
    {
        let r = &mut v[1];
        *r = Holder { point: &b, note: 3 };
    }
    let w = 0;
    *(&mut v[w]) = Holder { point: &b, note: 5 };
    Vec.get(&v, 1).point.x + Vec.get(&v, 0).note * 1000
}"#,
        5030,
        "",
    );
}

#[test]
fn review_container_arguments_are_write_sources() {
    // A callee may copy an element from a shared container argument into a
    // written container; the caller keeps the copied element's owner loaned.
    rejects(
        r#"
        struct Point { x: i64, y: i64 }
        fn copy_first<'a>(dst: &mut Vec<&'a Point>, src: &Vec<&'a Point>) -> Unit ! {alloc, panic} {
            Vec.push(dst, Vec.get(src, 0));
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 1, y: 2 };
            let mut dst: Vec<&Point> = [&a];
            {
                let b = Point { x: 77, y: 0 };
                let src: Vec<&Point> = [&b];
                copy_first(&mut dst, &src);
            }
            Vec.get(&dst, 1).x
        }"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // A reference produced by a `break` value is rejected with a real
    // diagnostic, not an internal error.
    rejects(
        r#"fn main() -> i64 ! {panic} {
    let mut xs: [i64; 4] = [1, 2, 3, 4];
    let mut i = 0;
    let p = loop {
        i = 1;
        break &mut xs[i];
    };
    let q = &mut xs[2];
    *p = 10;
    *q = 20;
    *p
}"#,
        "cannot bind this reference: the storage it borrows cannot be tracked",
    );
}

#[test]
fn review_recheck_call_site_writes_resolve_the_written_field() {
    // A field place passed straight to a writing callee is tracked.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        set(&mut o.h, &b[..]);
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.h.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // So is a container element place.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
struct Pair<'a> { l: Win<'a>, r: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut v = [Win { view: &a[..], note: 0 }];
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        set(&mut v[0], &b[..]);
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(Vec.get(&v, 0).view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // The written field keeps the source loaned after the call.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut v = [Outer { other: &a[..], h: Win { view: &a[..], note: 0 } }];
    {
        let r = &mut v[0];
        let _x = 0;
    }
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    set(&mut o.h, &b[..]);
    let w = o.h.view;
    b = [2];
    Slice.get(w, 3)
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // A field place of a parameter is checked against the declared lifetime.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn inner<'a>(o: &mut Outer<'a>) -> i64 ! {alloc, panic} {
    let b: Vec<i64> = [70, 71, 72, 73];
    set(&mut o.h, &b[..]);
    0
}
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    inner(&mut o);
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.h.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "this call would write a borrow of a local owner into a container whose declared element lifetime is lifetime 'a'",
    );
    // A stored field reference passed to a callee merges under the field path.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    {
        let r = &mut o.h;
        set(r, &b[..]);
    }
    let v = o.h.view;
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(v, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn f<'a>(o: &mut Outer<'a>) -> Unit ! {alloc, panic} {
    let b: Vec<i64> = [70, 71, 72, 73];
    let r = &mut o.h;
    set(r, &b[..]);
}
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    f(&mut o);
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.h.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "this call would write a borrow of a local owner into a container whose declared element lifetime is lifetime 'a'",
    );
    // A generic record nested in itself is not mistaken for its whole owner.
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
struct Wrap<'a, T> { view: &'a [i64], inner: T }
fn inner<'a, 'b>(w: &'b mut Wrap<'a, Wrap<'a, i64>>) -> &'b mut Wrap<'a, i64> ! {} { &mut w.inner }
fn main() -> i64 ! {alloc, panic} {
    let mut a: Vec<i64> = [1, 2, 3, 4];
    let b: Vec<i64> = [70, 71, 72, 73];
    let mut w = Wrap { view: &a[..], inner: Wrap { view: &a[..], inner: 0 } };
    {
        let r = inner(&mut w);
        *r = Wrap { view: &b[..], inner: 5 };
    }
    a = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(w.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which part of its owner this '&mut' reference replaces",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn via<'a>(o: &mut Outer<'a>, v: &'a [i64]) -> Unit ! {} { set(&mut o.h, v); }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let b: Vec<i64> = [70, 71, 72, 73];
    let mut o = Outer { other: &a[..], h: Win { view: &a[..], note: 0 } };
    via(&mut o, &b[..]);
    Slice.get(o.h.view, 3) + o.h.note
}"#,
        80,
        "",
    );
}

#[test]
fn review_recheck_indirect_calls_and_container_field_places_merge_writes() {
    // A write through a function value is merged like a direct call.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut w = Win { view: &a[..], note: 0 };
    let f = set;
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        f(&mut w, &b[..]);
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(w.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // So is one through an annotated arrow binding.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut w = Win { view: &a[..], note: 0 };
    let f: fn<'a>(&mut Win<'a>, &'a [i64]) -> Unit ! {} = set;
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        f(&mut w, &b[..]);
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(w.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // And a container parameter through a function value.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
struct Point { x: i64, y: i64 }
fn addw<'a>(v: &mut Vec<Win<'a>>, s: &'a [i64]) -> Unit ! {alloc, panic} { Vec.push(v, Win { view: s, note: 0 }); }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut v = [Win { view: &a[..], note: 0 }];
    let f = addw;
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        f(&mut v, &b[..]);
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(Vec.get(&v, 1).view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // Pre-existing: a reference container written through a function value.
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn addv<'a>(v: &mut Vec<&'a Point>, s: &'a Point) -> Unit ! {alloc, panic} { Vec.push(v, s); }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    let f = addv;
    {
        let b = Point { x: 70, y: 71 };
        f(&mut v, &b);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
struct Point { x: i64, y: i64 }
fn apply<'x>(f: fn<'a>(&mut Win<'a>, &'a [i64]) -> Unit ! {}, w: &mut Win<'x>) -> Unit ! {alloc, panic} {
    let b: Vec<i64> = [70, 71, 72, 73];
    f(w, &b[..]);
}
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut w = Win { view: &a[..], note: 0 };
    apply(set, &mut w);
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(w.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "this call would write a borrow of a local owner into a container whose declared element lifetime is lifetime 'x'",
    );
    // A function value passed to a helper.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn apply<'x>(f: fn<'a>(&mut Win<'a>, &'a [i64]) -> Unit ! {}, w: &mut Win<'x>, v: &'x [i64]) -> Unit ! {} { f(w, v); }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut w = Win { view: &a[..], note: 0 };
    apply(set, &mut w, &b[..]);
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(w.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Pre-existing: Box.set through a field place of a record.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { b: Box<Win<'a>>, n: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { b: Box.new(Win { view: &a[..], note: 0 }), n: 0 };
    Box.set(&mut o.b, Win { view: &b[..], note: 1 });
    b = [1];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3)
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct Point { x: i64, y: i64 }
struct O<'a> { b: Box<Win<'a>>, n: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut o = O { b: Box.new(Win { view: &a[..], note: 0 }), n: 0 };
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        Box.set(&mut o.b, Win { view: &b[..], note: 1 });
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    // A callee writing through a field place of a container.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
fn setb<'a>(h: &mut Box<Win<'a>>, v: &'a [i64]) -> Unit ! {alloc, panic} { Box.set(h, Win { view: v, note: 7 }); }
struct Outer<'a> { b: Box<Win<'a>>, n: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = Outer { b: Box.new(Win { view: &a[..], note: 0 }), n: 0 };
    setb(&mut o.b, &b[..]);
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Vec.push through a field place.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { v: Vec<Win<'a>>, n: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut o = O { v: [Win { view: &a[..], note: 0 }], n: 0 };
    {
        let b: Vec<i64> = [70, 71, 72, 73];
        Vec.push(&mut o.v, Win { view: &b[..], note: 1 });
    }
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Vec.get(&o.v, 1);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "an outer container was updated with a reference to this block-local value",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { v: Vec<Win<'a>>, n: i64 }
fn addw<'a>(v: &mut Vec<Win<'a>>, s: &'a [i64]) -> Unit ! {alloc, panic} { Vec.push(v, Win { view: s, note: 0 }); }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { v: [Win { view: &a[..], note: 0 }], n: 0 };
    addw(&mut o.v, &b[..]);
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Vec.get(&o.v, 1);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Positive: the same writes are accepted while every source stays live.
    agrees(
        r#"
        struct Win<'a> { view: &'a [i64], note: i64 }
        struct O<'a> { b: Box<Win<'a>>, n: i64 }
        fn set<'a>(h: &mut Win<'a>, v: &'a [i64]) -> Unit ! {} { *h = Win { view: v, note: 7 }; }
        fn main() -> i64 ! {alloc, panic} {
            let a: Vec<i64> = [1, 2, 3, 4];
            let b: Vec<i64> = [70, 71, 72, 73];
            let mut w = Win { view: &a[..], note: 0 };
            let f = set;
            f(&mut w, &b[..]);
            let g: fn<'x>(&mut Win<'x>, &'x [i64]) -> Unit ! {} = set;
            g(&mut w, &b[..]);
            let mut o = O { b: Box.new(Win { view: &a[..], note: 0 }), n: 0 };
            Box.set(&mut o.b, Win { view: &b[..], note: 1 });
            let w2 = Box.read(&o.b);
            Slice.get(w.view, 3) + Slice.get(w2.view, 2) + w.note
        }"#,
        73 + 72 + 7,
        "",
    );
}

#[test]
fn review_a_mutable_record_argument_shares_its_shared_leaf_sources() {
    // `&mut h1` is exclusive over h1 but only shared over the storage behind
    // its shared leaves, so another argument may share that storage.
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn steal<'a>(h: &mut Win<'a>, g: &Win<'a>) -> Unit ! {panic} { *h = Win { view: g.view, note: 1 }; }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut h1 = Win { view: &a[..], note: 0 };
    let g = Win { view: &a[..], note: 5 };
    steal(&mut h1, &g);
    Slice.get(h1.view, 3) + g.note
}"#,
        9,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Holder<'a> { point: &'a Point, note: i64 }
struct Win<'a> { view: &'a [i64], note: i64 }
struct Outer<'a> { other: &'a [i64], h: Win<'a> }
fn steal<'a>(h: &mut Holder<'a>, g: &Holder<'a>) -> Unit ! {panic} { *h = Holder { point: g.point, note: 1 }; }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut h1 = Holder { point: &a, note: 0 };
    let g = Holder { point: &a, note: 5 };
    steal(&mut h1, &g);
    h1.point.x + g.note
}"#,
        6,
        "",
    );
    // An exclusive leaf keeps its source exclusive, and a shared leaf's
    // source cannot be lent exclusively to the same call.
    rejects(
        r#"
        struct Window<'a> { view: &'a mut [i64], note: i64 }
        fn peek<'a>(h: &mut Window<'a>, other: &[i64]) -> Unit ! {} { }
        fn main() -> i64 ! {alloc, panic} {
            let mut b: Vec<i64> = [1, 2];
            let mut h = Window { view: &mut b[..], note: 0 };
            peek(&mut h, &b[..]);
            0
        }"#,
        "",
    );
    rejects(
        r#"
        struct Win<'a> { view: &'a [i64], note: i64 }
        fn poke<'a>(h: &mut Win<'a>, other: &mut [i64]) -> Unit ! {} { }
        fn main() -> i64 ! {alloc, panic} {
            let mut b: Vec<i64> = [1, 2];
            let mut h = Win { view: &b[..], note: 0 };
            poke(&mut h, &mut b[..]);
            Slice.get(h.view, 0)
        }"#,
        "",
    );
}

#[test]
fn review_third_recheck_container_writes_and_reference_arguments() {
    // An elided element lifetime of a parameter container is not a write destination.
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn addv(v: &mut Vec<&Point>, s: &Point) -> Unit ! {alloc, panic} { Vec.push(v, s); }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    {
        let p2 = Point { x: 70, y: 71 };
        addv(&mut v, &p2);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "cannot write a reference into a parameter's container whose element lifetime is elided",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn addv(v: &mut Vec<&Point>, s: &Point) -> Unit ! {alloc, panic} { Vec.push(v, s); }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    let f = addv;
    {
        let p2 = Point { x: 70, y: 71 };
        f(&mut v, &p2);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "cannot write a reference into a parameter's container whose element lifetime is elided",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    let g = fn(v: &mut Vec<&Point>, s: &Point) -> Unit ! {alloc, panic} { Vec.push(v, s); };
    {
        let p2 = Point { x: 70, y: 71 };
        g(&mut v, &p2);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "cannot write a reference into a parameter's container whose element lifetime is elided",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    let g = fn(v: &mut Vec<&Point>, s: &Point) -> Unit ! {alloc, panic} { Vec.push(v, s); };
    let mut b = Point { x: 3, y: 4 };
    g(&mut v, &b);
    b = Point { x: 50, y: 50 };
    Vec.get(&v, 1).x
}"#,
        "cannot write a reference into a parameter's container whose element lifetime is elided",
    );
    // A container write through a block, call result, or branch receiver is rejected.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { n: i64, b: Box<Win<'a>> }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { n: 0, b: Box.new(Win { view: &a[..], note: 0 }) };
    Box.set({ &mut o.b }, Win { view: &b[..], note: 1 });
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { n: i64, b: Box<Win<'a>> }
fn pick<'a, 'b>(o: &'b mut O<'a>) -> &'b mut Box<Win<'a>> ! {} { &mut o.b }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { n: 0, b: Box.new(Win { view: &a[..], note: 0 }) };
    Box.set(pick(&mut o), Win { view: &b[..], note: 1 });
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { n: i64, v: Vec<Win<'a>> }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { n: 0, v: [Win { view: &a[..], note: 0 }] };
    Vec.push({ &mut o.v }, Win { view: &b[..], note: 1 });
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Vec.get(&o.v, 1);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { n: i64, b: Box<Win<'a>> }
fn setb<'a>(h: &mut Box<Win<'a>>, v: &'a [i64]) -> Unit ! {alloc, panic} { Box.set(h, Win { view: v, note: 7 }); }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut o = O { n: 0, b: Box.new(Win { view: &a[..], note: 0 }) };
    setb({ &mut o.b }, &b[..]);
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Box.read(&o.b);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut v = [Win { view: &a[..], note: 0 }];
    Vec.push(if Vec.len(&a) > 0 { &mut v } else { &mut v }, Win { view: &b[..], note: 1 });
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    let w2 = Vec.get(&v, 1);
    Slice.get(w2.view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    {
        let p2 = Point { x: 70, y: 71 };
        Vec.push({ &mut v }, &p2);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn id<'b, 'a>(v: &'b mut Vec<&'a Point>) -> &'b mut Vec<&'a Point> ! {} { v }
fn main() -> i64 ! {alloc, panic} {
    let a = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&a];
    {
        let p2 = Point { x: 70, y: 71 };
        Vec.push(id(&mut v), &p2);
    }
    let junk = Point { x: 9, y: 9 };
    Vec.get(&v, 1).x + junk.x * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut b: Vec<i64> = [70, 71, 72, 73];
    let mut bx = Box.new(Win { view: &a[..], note: 0 });
    Box.set({ &mut bx }, Win { view: &b[..], note: 1 });
    b = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(Box.read(&bx).view, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot track which owner this write through a place reference updates",
    );
    // A stored `&mut` record reference lends its leaves for the call.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn f<'a>(h: &mut Win<'a>, s: &mut [i64]) -> i64 ! {panic} { Slice.set(s, 0, 99); Slice.get(h.view, 0) }
fn main() -> i64 ! {alloc, panic} {
    let mut b: Vec<i64> = [1, 2, 3, 4];
    let mut h = Win { view: &b[..], note: 0 };
    let r = &mut h;
    f(r, &mut b[..])
}"#,
        "cannot create an exclusive view while a shared view retained by this expression",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
fn f<'a>(h: &mut Win<'a>, s: &mut Vec<i64>) -> i64 ! {alloc, panic} { Vec.push(s, 5); Vec.push(s, 6); Vec.push(s, 7); Vec.push(s, 8); Vec.push(s, 9); let junk: Vec<i64> = [100, 100, 100, 100, 100, 100, 100, 100]; Slice.get(h.view, 0) + Vec.get(&junk, 0) * 0 }
fn main() -> i64 ! {alloc, panic} {
    let mut b: Vec<i64> = [1, 2, 3, 4];
    let mut h = Win { view: &b[..], note: 0 };
    let r = &mut h;
    f(r, &mut b)
}"#,
        "",
    );
    rejects(
        r#"struct Window<'a> { view: &'a mut [i64], note: i64 }
fn f<'a>(h: &mut Window<'a>, s: &mut [i64]) -> i64 ! {panic} { Slice.get(s, 0) }
fn main() -> i64 ! {alloc, panic} {
    let mut b: Vec<i64> = [1, 2, 3, 4];
    let mut h = Window { view: &mut b[..], note: 0 };
    let r = &mut h;
    f(r, &mut b[..])
}"#,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
fn f<'a>(v: &mut Vec<&'a Point>, s: &mut Point) -> i64 ! {panic} { s.x = 99; Vec.get(v, 0).x }
fn main() -> i64 ! {alloc, panic} {
    let mut p = Point { x: 1, y: 2 };
    let mut v: Vec<&Point> = [&p];
    let r = &mut v;
    f(r, &mut p)
}"#,
        "",
    );
    // Box.set through a stored field reference merges under that field.
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { other: &'a [i64], b: Box<Win<'a>> }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut c: Vec<i64> = [5, 6, 7, 8];
    let mut o = O { other: &c[..], b: Box.new(Win { view: &a[..], note: 0 }) };
    let r = &mut o.b;
    Box.set(r, Win { view: &a[..], note: 1 });
    c = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.other, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Win<'a> { view: &'a [i64], note: i64 }
struct O<'a> { other: &'a [i64], b: Box<Win<'a>> }
fn main() -> i64 ! {alloc, panic} {
    let a: Vec<i64> = [1, 2, 3, 4];
    let mut c: Vec<i64> = [5, 6, 7, 8];
    let mut o = O { other: &c[..], b: Box.new(Win { view: &a[..], note: 0 }) };
    {
        let r = &mut o.b;
        Box.set(r, Win { view: &a[..], note: 1 });
    }
    c = [1];
    let junk: Vec<i64> = [9, 9, 9, 9];
    Slice.get(o.other, 3) + Vec.get(&junk, 0) * 0
}"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // The named-lifetime form of the elided helper is accepted.
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn addv<'a>(v: &mut Vec<&'a Point>, s: &'a Point) -> Unit ! {alloc, panic} { Vec.push(v, s); }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 1, y: 2 };
            let b = Point { x: 70, y: 71 };
            let mut v: Vec<&Point> = [&a];
            addv(&mut v, &b);
            let f = addv;
            f(&mut v, &a);
            Vec.get(&v, 1).x + Vec.len(&v)
        }"#,
        73,
        "",
    );
}

/// A call-scoped `&mut` record loan taken in one branch of an `if` or a
/// `match` does not exist on the other path, so each branch may lend the
/// same owner again. After the branches, the loans of all of them last until
/// the enclosing full expression ends, so a later alias is still rejected.
#[test]
fn each_branch_lends_the_owner_independently() {
    let common = "
struct Kernel { n: i64 }
enum Item { A(i64), B(i64, i64) }
fn f(k: &mut Kernel, x: i64) -> i64 ! {panic} { k.n = k.n + x; k.n }
fn both(a: i64, b: &Kernel) -> i64 ! {panic} { a + b.n }
";
    agrees(
        &format!(
            "{common}
fn main() -> i64 ! {{alloc, panic}} {{
    let mut k = Kernel {{ n: 0 }};
    let x = 3;
    if x > 1 {{ let _ = f(&mut k, x); }} else {{ let _ = f(&mut k, 1); }}
    if x > 5 {{ let _ = f(&mut k, 100); }} else {{ k.n = k.n + 1; }}
    let mut items: Vec<Item> = Vec.new();
    items = items.push(Item.A(10));
    items = items.push(Item.B(20, 5));
    let mut i = 0;
    while i < items.len() {{
        match items[i] {{
            Item.A(a) => {{ match f(&mut k, a) {{ 0 => {{}}, _ => {{}} }} }},
            Item.B(a, b) => {{ match f(&mut k, a + b) {{ 0 => {{}}, _ => {{}} }} }},
        }}
        i = i + 1;
    }}
    k.n
}}"
        ),
        39,
        "",
    );
    rejects(
        &format!(
            "{common}
fn main() -> i64 ! {{panic}} {{
    let mut k = Kernel {{ n: 0 }};
    both(if k.n > 0 {{ f(&mut k, 1) }} else {{ 0 }}, &k)
}}"
        ),
        "an exclusive '&mut [T]' view of it is live",
    );
}
