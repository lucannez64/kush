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
fn borrowed_records_are_task_results_through_join_and_cancellation() {
    // The child returns the captured record. Task.join carries its per-field
    // provenance into the matched binding, and the scope's final join keeps the
    // external storage loaned through the read.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} {
                    Task.yield();
                    window
                });
                match Task.join(t) {
                    TaskExit.Completed(w) => Slice.get(w.view, w.start),
                    TaskExit.Cancelled => 0,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            run(Window { view: &data[..], start: 1 })
        }"#,
        40,
        "",
    );
    // Directly joining and matching is the same contract without an
    // intermediate TaskExit binding.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                match Task.join(Task.spawn(fn() -> Window<'a> ! {panic, suspend} {
                    Task.yield();
                    window
                })) {
                    TaskExit.Completed(w) => Slice.get(w.view, w.start),
                    TaskExit.Cancelled => 0,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            run(Window { view: &data[..], start: 1 })
        }"#,
        40,
        "",
    );
    // Cancellation drops the completed result value in the child: its owned
    // metadata is released exactly once, while the borrowed slice descriptor is
    // inert and never frees the caller's storage.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], owner: Vec<i64>, start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {alloc, panic, suspend} {
                    Task.yield();
                    Window { view: window.view, owner: [9, 8, 7], start: window.start }
                });
                Task.cancel(&t);
                match Task.join(t) {
                    TaskExit.Completed(w) => Slice.get(w.view, w.start),
                    TaskExit.Cancelled => 42,
                }
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            run(Window { view: &data[..], owner: [5], start: 1 }) + Slice.get(&data[..], 0)
        }"#,
        43,
        "",
    );
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64] }
        fn forge<'a>(view: &'a [i64]) -> i64 ! {} {
            let forged: TaskExit<Window<'a>> = TaskExit.Completed(Window { view: view });
            0
        }
        fn main() -> i64 ! {} { 0 }"#,
        "produced only by Task.join",
    );
    // A joined borrowed result may cross a function boundary when its
    // declared element lifetime is supplied by the caller.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64] }
        fn forward<'a>(exit: TaskExit<Window<'a>>) -> i64 ! {panic} {
            match exit {
                TaskExit.Completed(w) => Slice.get(w.view, 0),
                TaskExit.Cancelled => 0,
            }
        }
        fn make<'a>(view: &'a [i64]) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} {
                    Task.yield();
                    Window { view: view }
                });
                Task.join(t)
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 2] = [40, 2];
            forward(make(&data[..]))
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
    // A stored reference is a lexical capability, not a copy of the owner.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn peek(p: &Point) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let r = &p;
            peek(r) + r.y
        }"#,
        42,
        "",
    );
    // Returning a reference parameter through a stored local keeps its
    // caller lifetime.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn identity<'a>(p: &'a Point) -> &'a Point ! {panic} {
            let stored = p;
            stored
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let r = identity(&p);
            r.x + r.y
        }"#,
        42,
        "",
    );
    // Exclusive references are reborrowed on each use instead of moved, and an
    // explicit reborrow narrows the stored capability.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn bump<'a>(p: &'a mut Point) -> &'a mut Point ! {panic} {
            p.x = p.x + 1;
            p
        }
        fn read(p: &Point) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let r = &mut p;
            let a = read(&*r);
            let x = bump(&mut *r).x;
            let y = bump(r).y;
            x + y + a
        }"#,
        83,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>(p: &'a Point) -> &'a Point ! {panic} {
            let local = Point { x: 1, y: 2 };
            let stored = &local;
            stored
        }
        fn main() -> Unit ! {panic} {}"#,
        "escapes",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>(p: &'a Point) -> &'a Point ! {panic} {
            let stored = &*p;
            let local = Point { x: 1, y: 2 };
            let other = &local;
            other
        }
        fn main() -> Unit ! {panic} {}"#,
        "escapes",
    );
    // Owner references have valid escape contracts too: the caller-owned
    // Box/Vec/Bytes/String stays loaned for the returned reference's use.
    agrees(
        r#"fn box_value<'a>(b: &'a Box<i64>) -> &'a Box<i64> ! {panic} { b }
        fn vec_value<'a>(v: &'a Vec<i64>) -> &'a Vec<i64> ! {panic} { v }
        fn bytes_value<'a>(b: &'a Bytes) -> &'a Bytes ! {panic} { b }
        fn text_value<'a>(s: &'a String) -> &'a String ! {panic} { s }
        fn main() -> i64 ! {alloc, panic} {
            let boxed: Box<i64> = Box.new(40);
            let values: Vec<i64> = [2];
            let bytes: Bytes = Bytes.from("x");
            let text = String.from("y");
            let b = box_value(&boxed);
            let v = vec_value(&values);
            let by = bytes_value(&bytes);
            let t = text_value(&text);
            Box.read(b) + Vec.len(v) + Bytes.len(by) + String.len(t)
        }"#,
        43,
        "",
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
    // A per-field body origin selects the returned field's lifetime even when
    // the record type carries several distinct field lifetimes.
    agrees(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn pick<'a, 'b>(two: Two<'a, 'b>) -> &[i64] ! {panic} { two.first }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 2];
            let b: [i64; 2] = [9, 9];
            let view = pick(Two { first: &a[..], second: &b[..] });
            Slice.get(view, 0) + Slice.get(view, 1)
        }"#,
        42,
        "",
    );
    // Returning both fields from one result is an inferred anonymous
    // intersection: the result is outlived by both field lifetimes, so both
    // owners stay loaned through its last use.
    agrees(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn pick<'a, 'b>(two: Two<'a, 'b>, flag: Bool) -> &[i64] ! {panic} {
            if flag { two.first } else { two.second }
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 2];
            let b: [i64; 2] = [9, 9];
            let view = pick(Two { first: &a[..], second: &b[..] }, true);
            Slice.get(view, 0) + Slice.get(view, 1)
        }"#,
        42,
        "",
    );
}

// ---------------------------------------------------------------------------
// Place references into slice-view elements: `&s[i]` and `&mut s[i]`
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native_aborts(source: &str) {
    let program = check(source).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("slice-place-abort");
    kush::native::build(&program, &binary).unwrap();
    let output = std::process::Command::new(&binary).output().unwrap();
    assert!(!output.status.success(), "native code must abort: {source}");
}

#[test]
fn slice_element_places_read_and_write_the_viewed_storage() {
    // Array, DynArray, and Vec storage behind shared and exclusive views.
    agrees(
        r#"
        fn bump(p: &mut i64) -> Unit ! {panic} { *p = *p + 10; }
        fn main() -> i64 ! {alloc, panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            {
                let view: &mut [i64] = &mut xs[..];
                let p = &mut view[1];
                bump(p);
                *p = *p + 1;
            }
            let mut d: DynArray<i64, 4> = [4, 5];
            {
                let view: &mut [i64] = &mut d[1..];
                let p = &mut view[0];
                *p = 50;
            }
            let mut v: Vec<i64> = [7, 8, 9];
            {
                let view: &mut [i64] = &mut v[..];
                let p = &mut view[2];
                *p = 90;
            }
            let shared: &[i64] = &xs[..];
            let q = &shared[2];
            xs[1] + *q + DynArray.get(&d, 1) + Vec.get(&v, 2)
        }"#,
        13 + 3 + 50 + 90,
        "",
    );
    // Record elements: field reads and writes through the element reference.
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<Point> = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
            {
                let view: &mut [Point] = &mut v[..];
                let p = &mut view[1];
                p.x = 30;
            }
            let mut ps: [Point; 2] = [Point { x: 5, y: 6 }, Point { x: 7, y: 8 }];
            {
                let view: &mut [Point] = &mut ps[..];
                let y = &mut view[0].y;
                *y = 60;
            }
            let s = &v[..];
            let r = &s[1];
            r.x + r.y + ps[0].y
        }"#,
        94,
        "",
    );
}

#[test]
fn slice_element_references_return_through_slice_parameters() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn first<'a>(s: &'a [i64]) -> &'a i64 ! {panic} { &s[0] }
        fn last_mut<'a>(s: &'a mut [i64]) -> &'a mut i64 ! {panic} {
            let n = Slice.len(s);
            &mut s[n - 1]
        }
        fn grow(s: &mut [Point]) -> Unit ! {panic} { let p = &mut s[1]; p.y = p.y + 30; }
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            {
                let r = last_mut(&mut xs[..]);
                *r = 40;
            }
            let r = first(&xs[..]);
            let mut ps: [Point; 2] = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
            grow(&mut ps[..]);
            *r + xs[2] + ps[1].y
        }"#,
        1 + 40 + 34,
        "",
    );
    // A shared view cannot back an exclusive result.
    rejects(
        "fn bad<'a>(s: &'a [i64]) -> &'a mut i64 ! {panic} { &mut s[0] } fn main() -> i64 ! {} { 0 }",
        "does not appear on any reference parameter",
    );
    // A local view's element cannot escape the frame.
    rejects(
        r#"
        fn leak<'a>(s: &'a [i64]) -> &'a i64 ! {panic} {
            let xs: [i64; 2] = [1, 2];
            let local = &xs[..];
            &local[0]
        }
        fn main() -> i64 ! {} { 0 }"#,
        "reference escapes the lexical scope of the storage it borrows",
    );
    // The caller keeps the owner loaned while the returned element is live.
    rejects(
        r#"
        fn first<'a>(s: &'a [i64]) -> &'a i64 ! {panic} { &s[0] }
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let r = first(&xs[..]);
            xs = [7, 8, 9];
            *r
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
}

#[test]
fn slice_element_loans_root_at_the_views_owners() {
    // The element reference outlives the view binding's last use, so the
    // owner must stay loaned through the element itself.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let view: &mut [i64] = &mut xs[..];
            let p = &mut view[1];
            xs = [4, 5, 6];
            *p
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let p = {
                let view: &mut [i64] = &mut xs[..];
                &mut view[1]
            };
            xs = [4, 5, 6];
            *p
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let v: Vec<i64> = [1, 2, 3];
            let view: &[i64] = &v[..];
            let p = &view[0];
            let moved = v;
            *p + Vec.len(&moved)
        }"#,
        "cannot move an owner while it is borrowed",
    );
    // Two exclusive references to one view, or using the view while an
    // exclusive element reference is live, are aliasing errors.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let view: &mut [i64] = &mut xs[..];
            let p = &mut view[1];
            let q = &mut view[2];
            *p + *q
        }"#,
        "child view derived from it is live",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let view: &mut [i64] = &mut xs[..];
            let p = &view[1];
            Slice.set(view, 1, 9);
            *p
        }"#,
        "child view derived from it is live",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let xs: [i64; 3] = [1, 2, 3];
            let view: &[i64] = &xs[..];
            let p = &mut view[1];
            0
        }"#,
        "cannot create an exclusive element reference from a shared '&[T]' view",
    );
    // Owning elements are never aliased by an element reference.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<Box<i64>> = [Box.new(1)];
            let view: &mut [Box<i64>] = &mut v[..];
            let p = &mut view[0];
            0
        }"#,
        "cannot",
    );
}

#[test]
fn slice_element_references_into_split_sides_stay_disjoint() {
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [5, 6, 7];
            {
                let view: &mut [i64] = &mut a[..];
                let (left, right) = Slice.split_at_mut(view, 1);
                let p = &mut left[0];
                let q = &mut right[1];
                *p = *p + *q;
                *q = 70;
            }
            DynArray.get(&a, 0) + DynArray.get(&a, 2)
        }"#,
        12 + 70,
        "",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [5, 6, 7];
            let view: &mut [i64] = &mut a[..];
            let (left, right) = Slice.split_at_mut(view, 1);
            let p = &mut left[0];
            let q = &mut left[0];
            *p + *q
        }"#,
        "child view derived from it is live",
    );
}

#[test]
fn slice_element_places_check_the_bound_and_byte_backing_at_runtime() {
    let out_of_bounds = r#"
        fn main() -> i64 ! {panic} {
            let xs: [i64; 3] = [1, 2, 3];
            let view: &[i64] = &xs[..];
            let i = 3;
            let p = &view[i];
            *p
        }"#;
    let program = check(out_of_bounds).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("slice index out of bounds"),
        "{error:?}"
    );
    // A `&[i64]` over Bytes has byte-sized elements, so it has no word-sized
    // element address.
    let bytes = r#"
        fn peek<'a>(s: &'a [i64]) -> &'a i64 ! {panic} { &s[0] }
        fn main() -> i64 ! {alloc, panic} {
            let bytes = Bytes.from("abc");
            let raw: &[i64] = &bytes[..];
            let p = peek(raw);
            *p
        }"#;
    let program = check(bytes).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains("byte-backed slice element"),
        "{error:?}"
    );
    // The element reference needs `panic` because its bound is checked.
    rejects(
        r#"
        fn main() -> i64 ! {} {
            let xs: [i64; 3] = [1, 2, 3];
            let view: &[i64] = &xs[..];
            let p = &view[0];
            0
        }"#,
        "operation requires effects {panic}",
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        native_aborts(out_of_bounds);
        native_aborts(bytes);
    }
}
