//! Regressions for the independent borrowing review's three confirmed holes.
use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(error.message.contains(fragment), "{error:?}");
}

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap();
    let (status, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(status, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowing-safety");
        kush::native::build(&program, &binary).unwrap();
        assert_eq!(
            std::process::Command::new(binary).status().unwrap().code(),
            Some(expected as i32)
        );
    }
}

#[test]
fn joined_borrow_cannot_escape_in_a_closure_environment() {
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn make<'a>(window: Window<'a>) -> once fn() -> i64 ! {panic} ! {alloc, panic, suspend} {
            Task.scope(fn() -> once fn() -> i64 ! {panic} ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} { window });
                let exit = Task.join(t);
                fn() -> i64 ! {panic} {
                    match exit {
                        TaskExit.Completed(w) => Slice.get(w.view, w.start),
                        TaskExit.Cancelled => 0,
                    }
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 3] = [1, 40, 2];
            let f = make(Window { view: &data[..], start: 1 });
            data = [9, 9, 9];
            f()
        }"#,
        "cannot capture TaskExit",
    );
}

#[test]
fn scope_slice_results_keep_their_original_owner_loaned() {
    agrees(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 2] = [40, 2];
            let view = &data[..];
            let out = Task.scope(fn() -> &[i64] ! {alloc, panic, suspend} { view });
            Slice.get(out, 0) + Slice.get(out, 1)
        }"#,
        42,
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 3] = [1, 40, 2];
            let view = &data[..];
            let out = Task.scope(fn() -> &[i64] ! {alloc, panic, suspend} { view });
            data = [9, 9, 9];
            Slice.get(out, 1)
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            let out = {
                let data: [i64; 2] = [40, 2];
                let view = &data[..];
                Task.scope(fn() -> &[i64] ! {alloc, panic, suspend} { view })
            };
            Slice.get(out, 0)
        }"#,
        "outlive",
    );
}

#[test]
fn exclusive_reference_arguments_cannot_alias_but_shared_ones_can() {
    let prefix = r#"struct Point { x: i64, y: i64 }
        fn swap(a: &mut Point, b: &mut Point) -> i64 ! {panic} {
            a.x = a.x + b.x;
            b.x = a.x + b.x;
            a.x
        }"#;
    for (arguments, diagnostic) in [
        ("r, r", "while a child view derived from it is live"),
        (
            "&mut *r, &mut *r",
            "while a child view derived from it is live",
        ),
        (
            "&mut p, &mut p",
            "cannot borrow an owner while an exclusive",
        ),
    ] {
        let source = format!(
            "{prefix} fn main() -> i64 ! {{panic}} {{
                let mut p = Point {{ x: 1, y: 2 }};
                let r = &mut p;
                swap({arguments})
            }}"
        );
        rejects(&source, diagnostic);
    }
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn read(a: &Point, b: &Point) -> i64 ! {panic} { a.x + b.y }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let r = &p;
            read(r, r)
        }"#,
        42,
    );
}

#[test]
fn scope_returned_split_half_keeps_its_disjoint_identity() {
    agrees(
        r#"fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 2] = [40, 2];
            let (left, right) = Slice.split_at_mut(&mut data[..], 1);
            let out = Task.scope(fn() -> &mut [i64] ! {alloc, panic, suspend} { left });
            let right_child = &mut right[..];
            Slice.get(out, 0) + Slice.get(right_child, 0)
        }"#,
        42,
    );
}

#[test]
fn reference_assignment_reserves_its_owner_through_the_right_hand_side() {
    rejects(
        r#"struct Point { x: i64, keep: Box<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point { x: 1, keep: Box.new(2) };
            let reference = &mut p;
            reference.x = { drop(p); 42 };
            0
        }"#,
        "cannot move or drop an owner or view",
    );
}

#[test]
fn loop_results_retain_borrowed_records_and_containers() {
    let declarations = "struct P { x: i64 } struct H<'a> { p: &'a P }";
    for value in ["H { p: &a }", "[H { p: &a }]", "Box.new(H { p: &a })"] {
        let read = if value.starts_with('[') {
            "Vec.get(&r, 0).p.x"
        } else if value.starts_with("Box") {
            "Box.read(&r).p.x"
        } else {
            "r.p.x"
        };
        agrees(
            &format!(
                "{declarations} fn main() -> i64 ! {{alloc, panic}} {{
            let a = P {{ x: 40 }};
            let r = loop {{ break {value}; }};
            {read} + 2
        }}"
            ),
            42,
        );
        rejects(
            &format!(
                "{declarations} fn main() -> i64 ! {{alloc, panic}} {{
            let mut a = P {{ x: 40 }};
            let r = loop {{ break {value}; }};
            a = P {{ x: 9 }};
            {read}
        }}"
            ),
            "cannot replace an owner",
        );
        rejects(
            &format!(
                "{declarations} fn main() -> i64 ! {{alloc, panic}} {{
            let r = loop {{ let a = P {{ x: 40 }}; break {value}; }};
            {read}
        }}"
            ),
            "loop result would outlive",
        );
    }
    rejects(
        r#"struct H<'a> { s: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let a: Vec<i64> = [40, 1];
            let h = H { s: &a[..] };
            let r = loop { break h; };
            drop(a);
            Slice.get(r.s, 0)
        }"#,
        "cannot move",
    );
}

#[test]
fn loop_result_assignment_and_all_break_branches_keep_sources() {
    rejects(
        r#"struct P { x: i64 } struct H<'a> { p: &'a P }
        fn main() -> i64 ! {panic} {
            let mut a = P { x: 40 }; let b = P { x: 2 };
            let mut r = H { p: &b };
            r = loop { break H { p: &a }; };
            a = P { x: 9 }; r.p.x
        }"#,
        "cannot replace an owner",
    );
    for owner in ["a", "b"] {
        rejects(
            &format!(
                r#"struct P {{ x: i64 }} struct H<'a> {{ p: &'a P }}
            fn main() -> i64 ! {{panic}} {{
                let mut a = P {{ x: 40 }}; let mut b = P {{ x: 2 }};
                let r = loop {{
                    if true {{ break H {{ p: &a }}; }}
                    break H {{ p: &b }};
                }};
                {owner} = P {{ x: 9 }}; r.p.x
            }}"#
            ),
            "cannot replace an owner",
        );
    }
    agrees(
        r#"struct P { x: i64 } struct H<'a> { p: &'a P }
        fn main() -> i64 ! {panic} {
            let a = P { x: 40 };
            let r = loop { break loop { break H { p: &a }; }; };
            r.p.x + 2
        }"#,
        42,
    );
}

#[test]
fn replacing_box_element_releases_only_its_previous_loan() {
    agrees(
        r#"struct P { x: i64 } struct H<'a> { p: &'a P }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = P { x: 40 }; let b = P { x: 2 };
            let mut boxed = Box.new(H { p: &a });
            Box.set(&mut boxed, H { p: &b });
            a = P { x: 9 };
            Box.read(&boxed).p.x + a.x + b.x
        }"#,
        13,
    );
    for (read, owner, tail) in [
        ("", "b", "Box.read(&boxed).p.x"),
        (
            "let old = Box.read(&boxed);",
            "a",
            "old.p.x + Box.read(&boxed).p.x",
        ),
    ] {
        rejects(
            &format!(
                r#"struct P {{ x: i64 }} struct H<'a> {{ p: &'a P }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let mut a = P {{ x: 40 }}; let mut b = P {{ x: 2 }};
                let mut boxed = Box.new(H {{ p: &a }});
                {read}
                Box.set(&mut boxed, H {{ p: &b }});
                {owner} = P {{ x: 9 }};
                {tail}
            }}"#
            ),
            "cannot replace an owner",
        );
    }
}
