//! Expanded borrowing contracts: borrowed records in callable signatures and
//! scoped captures, capture-returning lambdas, borrowed records in structured
//! tasks, nested record-field subviews, disjoint-field loans, and nominal-record
//! reference escape/reborrow. Every positive case runs in the reference
//! evaluator and, on Linux x86-64, in the Cranelift backend.
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
        let binary = scratch.path().join("borrowing-extensions-test");
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

#[test]
fn borrowed_record_parameters_and_results_travel_through_function_values() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn len<'a>(window: Window<'a>) -> i64 ! {panic} { Slice.len(window.view) - window.start }
        fn advance<'a>(window: Window<'a>) -> Window<'a> ! {} { window }
        fn apply<'a>(f: fn<'b>(Window<'b>) -> i64 ! {panic}, w: Window<'a>) -> i64 ! {panic} {
            f(w)
        }
        fn main() -> i64 ! {panic} {
            let data: [i64; 4] = [1, 2, 3, 4];
            let f: fn<'x>(Window<'x>) -> i64 ! {panic} = len;
            let view = advance(Window { view: &data[..], start: 2 });
            apply(f, view)
        }"#,
        2,
        "",
    );
    // The named function value remains alpha-equivalent when the arrow spells
    // the record lifetime differently.
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn tail<'a>(window: Window<'a>) -> Window<'a> ! {} { window }
        fn main() -> i64 ! {panic} {
            let data: [i64; 3] = [1, 40, 2];
            let f: fn<'y>(Window<'y>) -> Window<'y> ! {} = tail;
            let out = f(Window { view: &data[..] });
            Slice.get(out.view, 1)
        }"#,
        40,
        "",
    );
}

#[test]
fn scoped_closures_capture_borrowed_records_and_return_fields() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let data: [i64; 4] = [1, 2, 40, 4];
            let window = Window { view: &data[..], start: 1 };
            let read = fn(index: i64) -> i64 ! {panic} {
                Slice.get(window.view, index + window.start)
            };
            read(1)
        }"#,
        40,
        "",
    );
    // A capture-returning lambda keeps the captured owner loaned until the
    // returned view's checked last use.
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Vec<i64> = [7, 35];
            let window = Window { view: &owner[..] };
            let tail = fn() -> &[i64] ! {panic} { window.view[1..] };
            let rest = tail();
            Slice.get(rest, 0)
        }"#,
        35,
        "",
    );
    // A capture-derived record result keeps every per-field origin.
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn read<'a>(window: Window<'a>) -> i64 ! {alloc, panic} {
            let clone_window = fn() -> Window<'a> ! {panic} { window };
            let out = clone_window();
            Slice.get(out.view, out.start)
        }
        fn main() -> i64 ! {alloc, panic} {
            let data: [i64; 3] = [1, 40, 2];
            read(Window { view: &data[..], start: 1 })
        }"#,
        40,
        "",
    );
    // The same form through a captured slice rather than a record.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let data: [i64; 3] = [1, 40, 2];
            let view: &[i64] = &data[..];
            let tail = fn() -> &[i64] ! {panic} { view[1..] };
            let rest = tail();
            Slice.get(rest, 0) + Slice.get(rest, 1)
        }"#,
        42,
        "",
    );
}

#[test]
fn capture_returning_lambdas_reject_ambiguous_or_dangling_origins() {
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let data: [i64; 2] = [1, 2];
            let window = Window { view: &data[..] };
            let f = fn(extra: &[i64]) -> &[i64] ! {panic} { window.view };
            0
        }"#,
        "borrowed parameters or captures",
    );
    rejects(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 1] = [1];
            let b: [i64; 1] = [2];
            let two = Two { first: &a[..], second: &b[..] };
            let f = fn() -> &[i64] ! {panic} { two.first };
            0
        }"#,
        "cannot infer this lambda result's lifetime",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let data: [i64; 1] = [42];
            let f = fn() -> &[i64] ! {panic} {
                let local: [i64; 1] = [1];
                &local[..]
            };
            0
        }"#,
        "slice-returning lambda needs exactly one borrowed",
    );
}

#[test]
fn borrowed_records_are_lent_to_scope_bodies_and_child_tasks() {
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 4] = [1, 2, 3, 40];
            let window = Window { view: &data[..], start: 1 };
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} {
                    Task.yield();
                    Slice.get(window.view, window.start + 2)
                });
                match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
            })
        }"#,
        40,
        "",
    );
    // A record field may be read after the child task was spawned while the
    // record remains an aggregate capability.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [40, 1, 1];
            let window = Window { view: &data[..], start: 0 };
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} {
                    Task.yield(); window.start
                });
                let first = Slice.get(window.view, 0);
                match Task.join(t) { TaskExit.Completed(offset) => first + offset, TaskExit.Cancelled => 0 }
            })
        }"#,
        40,
        "",
    );
}

#[test]
fn child_tasks_cannot_borrow_record_storage_owned_by_the_scope_body() {
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let local: [i64; 1] = [5];
                let window = Window { view: &local[..] };
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic} {
                    Slice.get(window.view, 0)
                });
                match Task.join(t) { TaskExit.Completed(v) => v, TaskExit.Cancelled => 0 }
            })
        }"#,
        "captured from outside the scope",
    );
}

#[test]
fn nested_record_fields_can_be_sub_sliced_and_loaned_disjointly() {
    agrees(
        r#"struct Inner<'a> { view: &'a [i64] }
        struct Outer<'a> { inner: Inner<'a>, note: i64 }
        fn main() -> i64 ! {panic} {
            let data: [i64; 4] = [1, 2, 40, 4];
            let outer = Outer { inner: Inner { view: &data[..] }, note: 1 };
            let view = outer.inner.view[2..];
            Slice.get(view, 0) + outer.inner.view[0] + outer.note
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Pair<'a> { left: &'a mut [i64], right: &'a mut [i64] }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let mut b: [i64; 2] = [3, 4];
            let pair = Pair { left: &mut a[..], right: &mut b[..] };
            let left = &mut pair.left[..];
            let right = &mut pair.right[..];
            Slice.set(left, 0, 10);
            Slice.set(right, 0, 30);
            a[0] + b[0]
        }"#,
        40,
        "",
    );
}

#[test]
fn disjoint_field_loans_do_not_launder_aliases_or_whole_record_moves() {
    rejects(
        r#"struct Pair<'a> { left: &'a mut [i64], right: &'a mut [i64] }
        fn main() -> i64 ! {panic} {
            let mut data: [i64; 2] = [1, 2];
            let pair = Pair { left: &mut data[..], right: &mut data[..] };
            let left = &mut pair.left[..];
            Slice.get(left, 0)
        }"#,
        "exclusive",
    );
    rejects(
        r#"struct Pair<'a> { left: &'a mut [i64], right: &'a mut [i64] }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let mut b: [i64; 2] = [3, 4];
            let pair = Pair { left: &mut a[..], right: &mut b[..] };
            let left = &mut pair.left[..];
            drop(pair);
            Slice.set(left, 0, 9);
        }"#,
        "slice view derived from it is live",
    );
    rejects(
        r#"struct Pair<'a> { left: &'a mut [i64], right: &'a mut [i64] }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let mut b: [i64; 2] = [3, 4];
            let pair = Pair { left: &mut a[..], right: &mut b[..] };
            let first = &mut pair.left[..];
            let second = &mut pair.left[..];
            Slice.set(first, 0, 9);
            Slice.set(second, 0, 8);
        }"#,
        "exclusive '&mut [T]' view while another view of the same owner is live",
    );
}

#[test]
fn nominal_record_reference_escape_and_reborrow_contracts() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn identity<'a>(p: &'a Point) -> &'a Point ! {panic} { p }
        fn relay<'a>(p: &'a Point) -> &'a Point ! {panic} { identity(p) }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            relay(&p).x + relay(&p).y
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn bump<'a>(p: &'a mut Point) -> &'a mut Point ! {panic} {
            p.x = p.x + 1;
            p
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let x = bump(&mut p).x;
            x + p.y
        }"#,
        43,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>(p: &'a Point) -> &'a Point ! {panic} {
            let local = Point { x: 1, y: 2 };
            &local
        }
        fn main() -> Unit ! {panic} {}"#,
        "escapes",
    );
    rejects(
        r#"fn leak() -> &Bytes ! {panic} { Bytes.from("x") }
        fn main() -> Unit ! {} {}"#,
        "cannot be returned",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn peek(p: &Point) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 1, y: 2 };
            let r = &p;
            peek(r)
        }"#,
        "stored in local bindings",
    );
}

#[test]
fn result_lifetime_elision_counts_a_single_record_field_source() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn tail<'a>(window: Window<'a>) -> &[i64] ! {panic} { window.view[window.start..] }
        fn main() -> i64 ! {panic} {
            let data: [i64; 3] = [1, 40, 2];
            let view = tail(Window { view: &data[..], start: 1 });
            Slice.get(view, 0) + Slice.get(view, 1)
        }"#,
        42,
        "",
    );
    rejects(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn pick<'a, 'b>(two: Two<'a, 'b>) -> &[i64] ! {panic} { two.first }
        fn main() -> Unit ! {} {}"#,
        "distinct input borrow lifetimes",
    );
}
