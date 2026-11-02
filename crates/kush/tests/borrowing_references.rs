//! Reference-valued fields, reference element containers, and reference-valued
//! callables. Every positive case runs in the reference evaluator and, on Linux
//! x86-64, in the Cranelift backend. Hostile aliasing/escape cases remain
//! checked rejections.
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
        let binary = scratch.path().join("borrowing-references-test");
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
fn reference_fields_carry_declared_lifetimes_and_read() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn wrap<'a>(p: &'a Point, note: i64) -> Holder<'a> ! {panic} {
            Holder { point: p, note: note }
        }
        fn read<'a>(holder: Holder<'a>) -> i64 ! {panic} {
            holder.point.x + holder.note
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let holder = wrap(&p, 2);
            read(holder) + p.y
        }"#,
        44,
        "",
    );
    // An owner reference is a legal field when the declared lifetime is
    // supplied by a caller-owned value.
    agrees(
        r#"struct Holder<'a> { owner: &'a Box<i64>, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> = Box.new(40);
            let holder = Holder { owner: &value, note: 2 };
            Box.read(holder.owner) + holder.note
        }"#,
        42,
        "",
    );
    // Nested records keep each field's reference leaf.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Inner<'a> { point: &'a Point }
        struct Outer<'a> { inner: Inner<'a>, note: i64 }
        fn read<'a>(outer: Outer<'a>) -> i64 ! {panic} {
            outer.inner.point.x + outer.note
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 0 };
            read(Outer { inner: Inner { point: &p }, note: 2 }) + p.y
        }"#,
        42,
        "",
    );
}

#[test]
fn exclusive_reference_fields_require_destructuring_but_remain_checked() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a mut Point, note: i64 }
        fn bump<'a>(holder: Holder<'a>) -> i64 ! {panic} {
            let Holder { point, note } = holder;
            point.x = point.x + note;
            point.x
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let holder = Holder { point: &mut p, note: 2 };
            bump(holder) + p.y
        }"#,
        44,
        "",
    );
    // A shared reference cannot be stored in an exclusive field.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a mut Point }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let shared = &p;
            let holder = Holder { point: shared };
            0
        }"#,
        "type mismatch",
    );
    // Reading the exclusive field as a value would duplicate the exclusive
    // capability without a place check.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a mut Point }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let holder = Holder { point: &mut p };
            let moved = holder.point;
            0
        }"#,
        "cannot project exclusive reference field",
    );
}

#[test]
fn reference_field_escapes_and_owner_moves_are_rejected() {
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn leak<'a>() -> Holder<'a> ! {panic} {
            let p = Point { x: 1, y: 2 };
            Holder { point: &p }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "borrowed record result lifetime",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let holder = Holder { point: &p };
            p = Point { x: 1, y: 2 };
            holder.point.x
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Holder<'a> { owner: &'a Box<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> = Box.new(40);
            let holder = Holder { owner: &value };
            drop(value);
            Box.read(holder.owner)
        }"#,
        "cannot move or drop an owner or view",
    );
    // A reference field reached through a record reference is deliberately
    // outside the lexical field-read subset.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn read<'a>(holder: &'a Holder<'a>) -> i64 ! {panic} {
            holder.point.x
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot be read through a record reference",
    );
}

#[test]
fn reference_element_containers_preserve_owner_loans() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let boxed: Box<&Point> = Box.new(&p);
            let r = Box.read(&boxed);
            r.x + r.y + p.x
        }"#,
        82,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn first<'a>(values: Vec<&'a Point>) -> &'a Point ! {panic} {
            Vec.get(&values, 0)
        }
        fn apply<'a>(f: fn<'b>(Vec<&'b Point>) -> &'b Point ! {panic}, values: Vec<&'a Point>) -> &'a Point ! {panic} {
            f(values)
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 40, y: 2 };
            let values: Vec<&Point> = [&a];
            let f: fn<'x>(Vec<&'x Point>) -> &'x Point ! {panic} = first;
            let r = apply(f, values);
            r.x + r.y
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Bundle<'a> { points: Vec<&'a Point>, note: i64 }
        fn read<'a>(bundle: Bundle<'a>) -> i64 ! {panic} {
            let Bundle { points, note } = bundle;
            Vec.get(&points, 0).x + note
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 40, y: 2 };
            let bundle = Bundle { points: [&a], note: 2 };
            read(bundle) + a.y
        }"#,
        44,
        "",
    );
    // An unannotated container still tracks its element's actual loan.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 40, y: 0 };
            let b = Point { x: 1, y: 2 };
            let values = [&a, &b];
            Vec.get(&values, 0).x + Vec.get(&values, 1).y
        }"#,
        42,
        "",
    );
    // An exclusive box element is moved out, never copied by Box.read.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn bump(p: &mut Point) -> i64 ! {panic} { p.x = p.x + 1; p.x }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 40, y: 2 };
            let boxed: Box<&mut Point> = Box.new(&mut a);
            let r = Box.take(boxed);
            let x = bump(r);
            x + a.y
        }"#,
        43,
        "",
    );
}

#[test]
fn reference_element_containers_reject_aliasing_and_escapes() {
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 40, y: 0 };
            let values: Vec<&Point> = [&a];
            a = Point { x: 1, y: 2 };
            Vec.get(&values, 0).x
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 40, y: 0 };
            let boxed: Box<&Point> = Box.new(&a);
            a = Point { x: 1, y: 2 };
            Box.read(&boxed).x
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>() -> Vec<&'a Point> ! {alloc, panic} {
            let local = Point { x: 1, y: 2 };
            [&local]
        }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "would outlive the lexical scope",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>() -> Box<&'a Point> ! {alloc, panic} {
            let local = Point { x: 1, y: 2 };
            Box.new(&local)
        }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "would outlive the lexical scope",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 1, y: 2 };
            let values: Vec<&mut Point> = [&mut a];
            0
        }"#,
        "vectors cannot store exclusive references",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 1, y: 2 };
            let boxed: Box<&mut Point> = Box.new(&mut a);
            Box.read(&boxed).x
        }"#,
        "Box.read cannot copy an exclusive reference element",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn read(p: &Point) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 1, y: 2 };
            let values: Vec<&Point> = [&a];
            let out = Vec.map_in_place(values, read);
            Vec.get(&out, 0)
        }"#,
        "Vec.map_in_place cannot transform a vector of borrowed reference elements",
    );
}

#[test]
fn borrowed_scope_records_and_task_exits_cross_boundaries() {
    // A borrowed record returned directly from Task.scope keeps its declared
    // per-field lifetime and owner loan.
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            let out = Task.scope(fn() -> Window<'a> ! {alloc, panic, suspend} { window });
            Slice.get(out.view, out.start)
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            run(Window { view: &data[..], start: 1 })
        }"#,
        40,
        "",
    );
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn read<'a>(exit: TaskExit<Window<'a>>) -> i64 ! {panic} {
            match exit {
                TaskExit.Completed(window) => Slice.get(window.view, window.start),
                TaskExit.Cancelled => 0,
            }
        }
        fn make<'a>(window: Window<'a>) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} {
                    Task.yield();
                    window
                });
                Task.join(t)
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            read(make(Window { view: &data[..], start: 1 }))
        }"#,
        40,
        "",
    );
    agrees(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn make<'a>(window: Window<'a>) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} { window });
                Task.join(t)
            })
        }
        fn apply<'a>(f: fn<'b>(Window<'b>) -> TaskExit<Window<'b>> ! {alloc, panic, suspend}, window: Window<'a>) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            f(window)
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let data: [i64; 3] = [1, 40, 2];
            let f: fn<'x>(Window<'x>) -> TaskExit<Window<'x>> ! {alloc, panic, suspend} = make;
            match apply(f, Window { view: &data[..], start: 1 }) {
                TaskExit.Completed(window) => Slice.get(window.view, window.start),
                TaskExit.Cancelled => 0,
            }
        }"#,
        40,
        "",
    );
}

#[test]
fn task_exit_boundaries_reject_dangling_and_replaced_owners() {
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn make<'a>(window: Window<'a>) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic, suspend} { window });
                Task.join(t)
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} {
            let mut data: [i64; 3] = [1, 40, 2];
            let exit = make(Window { view: &data[..], start: 1 });
            data = [9, 9, 9];
            match exit { TaskExit.Completed(w) => Slice.get(w.view, w.start), TaskExit.Cancelled => 0 }
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn leak<'a>() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
            Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
                let local: [i64; 2] = [1, 2];
                let t: Task<Window<'a>> = Task.spawn(fn() -> Window<'a> ! {panic} {
                    Window { view: &local[..], start: 0 }
                });
                Task.join(t)
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} { 0 }"#,
        "borrowed record result lifetime 'a' does not appear",
    );
}

#[test]
fn reference_valued_arrows_keep_sources_borrowed() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn identity<'a>(p: &'a Point) -> &'a Point ! {panic} { p }
        fn apply<'a>(f: fn<'b>(&'b Point) -> &'b Point ! {panic}, p: &'a Point) -> &'a Point ! {panic} {
            f(p)
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let f: fn<'x>(&'x Point) -> &'x Point ! {panic} = identity;
            let r = apply(f, &p);
            r.x + r.y
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
        fn apply<'a>(f: fn<'b>(&'b mut Point) -> &'b mut Point ! {panic}, p: &'a mut Point) -> &'a mut Point ! {panic} {
            f(p)
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let f: fn<'x>(&'x mut Point) -> &'x mut Point ! {panic} = bump;
            let r = apply(f, &mut p);
            r.x + r.y
        }"#,
        43,
        "",
    );
    // An arrow result with no reference source cannot name a lifetime.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {panic} {
            let f: fn<'a>() -> &'a Point ! {panic} = panic;
            0
        }"#,
        "not outlived by any reference parameter",
    );
    // A shared parameter cannot supply an exclusive arrow result.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {panic} {
            let f: fn<'a>(&'a Point) -> &'a mut Point ! {panic} = panic;
            0
        }"#,
        "exclusive '&mut T' arrow result",
    );
    // Replacing the owner while an indirect result is live is rejected.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn identity<'a>(p: &'a Point) -> &'a Point ! {panic} { p }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let f: fn<'x>(&'x Point) -> &'x Point ! {panic} = identity;
            let r = f(&p);
            p = Point { x: 1, y: 2 };
            r.x
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
}
