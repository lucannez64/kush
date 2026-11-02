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

/// A checked program whose runtime bounds check must fail in the reference
/// evaluator and in the native executable.
fn runtime_panic(source: &str) {
    let program = check(source).unwrap();
    assert!(
        program.evaluate(&mut Vec::new()).is_err(),
        "reference evaluator accepted an out-of-bounds place: {source}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowing-place-panic");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert!(
            !output.status.success(),
            "native program did not panic on an out-of-bounds place"
        );
    }
}

#[test]
fn reference_annotations_do_not_change_the_caller_visible_type() {
    // The callee spells the outer and element lifetime with one name; the
    // caller's container carries its own erased label. Annotation names are
    // not part of runtime or nominal identity, so the call must still type
    // check while the element lifetime contract stays enforced.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn read<'a>(b: &'a Box<&'a Point>) -> i64 ! {panic} {
            let r = Box.read(b);
            r.x + r.y
        }
        fn first<'a>(v: &'a Vec<&'a Point>) -> i64 ! {panic} {
            Vec.get(v, 0).x
        }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let boxed: Box<&Point> = Box.new(&p);
            let values: Vec<&Point> = [&p];
            read(&boxed) + first(&values) - 40
        }"#,
        42,
        "",
    );
}

#[test]
fn mutable_owner_references_update_the_callers_container() {
    agrees(
        r#"fn grow(values: &mut Vec<i64>, value: i64) -> i64 ! {alloc, panic} {
            Vec.push(values, value);
            Vec.len(values)
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = [1, 2];
            let length = grow(&mut values, 40);
            Vec.reserve(&mut values, 1);
            Vec.set(&mut values, 0, 40);
            let answer = Vec.get(&values, 0);
            Vec.clear(&mut values);
            answer + length + Vec.len(&values)
        }"#,
        43,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn replace<'a>(b: &mut Box<&'a Point>, p: &'a Point) -> i64 ! {panic} {
            Box.set(b, p);
            Box.read(b).x
        }
        fn main() -> i64 ! {alloc, panic} {
            let first = Point { x: 1, y: 1 };
            let second = Point { x: 40, y: 2 };
            let mut boxed: Box<&Point> = Box.new(&first);
            replace(&mut boxed, &second) + second.y
        }"#,
        42,
        "",
    );
    agrees(
        r#"fn read_bytes(bytes: &mut Bytes) -> i64 ! {panic} { Bytes.get(bytes, 0) }
        fn read_text(text: &mut String) -> i64 ! {panic} { String.len(text) }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut bytes = Bytes.from("abcd");
            let mut text = "wxyz";
            print_i64(read_bytes(&mut bytes));
            print_i64(read_text(&mut text));
            0
        }"#,
        0,
        "97\n4\n",
    );
}

#[test]
fn mutable_container_writes_keep_written_owners_loaned() {
    // A reference stored through `&mut Vec<&Point>` keeps its owner loaned
    // after the call returns.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn add<'a>(values: &mut Vec<&'a Point>, p: &'a Point) -> Unit ! {alloc, panic} {
            Vec.push(values, p);
        }
        fn main() -> i64 ! {alloc, panic} {
            let first = Point { x: 40, y: 2 };
            let mut second = Point { x: 1, y: 1 };
            let mut values: Vec<&Point> = [];
            add(&mut values, &second);
            second = Point { x: 9, y: 9 };
            Vec.get(&values, 0).x
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn replace<'a>(b: &mut Box<&'a Point>, p: &'a Point) -> Unit ! {panic} {
            Box.set(b, p);
        }
        fn main() -> i64 ! {alloc, panic} {
            let first = Point { x: 40, y: 2 };
            let mut second = Point { x: 1, y: 1 };
            let mut boxed: Box<&Point> = Box.new(&first);
            replace(&mut boxed, &second);
            second = Point { x: 9, y: 9 };
            Box.read(&boxed).x
        }"#,
        "cannot replace an owner",
    );
    // A block-local owner cannot be written into a longer-lived container.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn add<'a>(values: &mut Vec<&'a Point>, p: &'a Point) -> Unit ! {alloc, panic} {
            Vec.push(values, p);
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<&Point> = [];
            {
                let local = Point { x: 1, y: 1 };
                add(&mut values, &local);
            }
            Vec.get(&values, 0).x
        }"#,
        "borrow escapes the lexical scope",
    );
    // The written source must outlive the declared element lifetime.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn add<'a, 'b>(values: &mut Vec<&'a Point>, p: &'b Point) -> Unit ! {alloc, panic} {
            Vec.push(values, p);
        }
        fn main() -> Unit ! {alloc, panic} { }"#,
        "does not outlive its declared element lifetime",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn replace<'a, 'b>(b: &mut Box<&'a Point>, p: &'b Point) -> Unit ! {panic} {
            Box.set(b, p);
        }
        fn main() -> Unit ! {alloc, panic} { }"#,
        "does not outlive its declared element lifetime",
    );
    // An exclusive owner borrow still excludes shared aliases.
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut values: Vec<i64> = [1, 2];
            let alias = &values;
            Vec.push(&mut values, 3);
            Vec.len(alias);
        }"#,
        "borrow",
    );
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
    // A shared reference field can be read through a shared record
    // reference; the field's owner stays loaned through the projection.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn read<'a>(holder: &'a Holder<'a>) -> i64 ! {panic} {
            holder.point.x + holder.point.y
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let holder = Holder { point: &p };
            read(&holder)
        }"#,
        42,
        "",
    );
    // Returning the field through the record reference keeps the pointed-to
    // owner loaned after the call returns.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn get<'a>(holder: &'a Holder<'a>) -> &'a Point ! {panic} {
            holder.point
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let holder = Holder { point: &p };
            get(&holder).x + p.y
        }"#,
        42,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a mut Point }
        fn read<'a>(holder: &'a Holder<'a>) -> i64 ! {panic} {
            holder.point.x
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot be read through a record reference",
    );
    // The projected field keeps the pointed-to owner loaned after the call.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn get<'a>(holder: &'a Holder<'a>) -> &'a Point ! {panic} {
            holder.point
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 40, y: 2 };
            let holder = Holder { point: &p };
            let r = get(&holder);
            p = Point { x: 1, y: 1 };
            r.x
        }"#,
        "cannot replace an owner while a slice view or reference borrows it",
    );
    // Nor may the record itself be replaced while the projection is live.
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point }
        fn get<'a>(holder: &'a Holder<'a>) -> &'a Point ! {panic} {
            holder.point
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 40, y: 2 };
            let mut holder = Holder { point: &p };
            let r = get(&holder);
            holder = Holder { point: &p };
            r.x
        }"#,
        "cannot replace an owner",
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
        "does not appear on any parameter",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a>() -> Box<&'a Point> ! {alloc, panic} {
            let local = Point { x: 1, y: 2 };
            Box.new(&local)
        }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "does not appear on any parameter",
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
fn field_index_and_temporary_places_are_checked_references() {
    // Nested record fields, owning fields, inline-array elements, vector
    // elements, and a hidden temporary owner all share one checked reference
    // form. Disjoint fields and distinct constant indices may be loaned in the
    // same expression; scalar writes reach the original storage.
    agrees(
        r#"struct Inner { a: i64, b: i64 }
        struct Outer { inner: Inner, note: i64 }
        fn add(left: &mut i64, right: &mut i64) -> Unit ! {panic} {
            *left = *left + *right;
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut outer = Outer { inner: Inner { a: 3, b: 4 }, note: 10 };
            add(&mut outer.inner.a, &mut outer.inner.b);
            let note = &outer.note;
            let mut values: Vec<i64> = [1, 2, 3];
            let element = &mut values[1];
            *element = *element + 5;
            let mut array: [i64; 3] = [1, 2, 3];
            add(&mut array[0], &mut array[2]);
            let temp = &mut Box.new(7);
            Box.set(temp, 9);
            *note + outer.inner.a + Box.read(temp) + Vec.get(&values, 1) + array[0] + array[2]
        }"#,
        40,
        "",
    );
    // A field reference may be returned from a reference parameter, and an
    // exclusive field reference is reborrowable through a helper.
    agrees(
        r#"struct P { x: i64 }
        fn pick(p: &P) -> &i64 ! {panic} { &p.x }
        fn bump(p: &mut P) -> &mut i64 ! {panic} { &mut p.x }
        fn main() -> i64 ! {panic} {
            let mut p = P { x: 5 };
            *bump(&mut p) = 8;
            *pick(&p)
        }"#,
        8,
        "",
    );
    // A temporary aggregate or owning handle is hoisted into hidden storage;
    // its cleanup follows the reference's checked last use and releases every
    // allocation exactly once.
    agrees(
        r#"struct P { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let r = &mut (P { x: 2, y: 3 });
            r.x = r.x + 1;
            let b = &mut Box.new(4);
            Box.set(b, 9);
            r.x + r.y + Box.read(b)
        }"#,
        15,
        "",
    );
    // A branch may select different disjoint field places; the joined
    // reference keeps the live storage identity.
    agrees(
        r#"struct Pair { a: i64, b: i64 }
        fn main() -> i64 ! {panic} {
            let mut p = Pair { a: 1, b: 2 };
            let flag = p.a == 1;
            let r = if flag { &mut p.a } else { &mut p.b };
            *r = 7;
            p.a + p.b
        }"#,
        9,
        "",
    );
}

#[test]
fn affine_reference_replacement_destroys_the_old_payload_exactly_once() {
    agrees(
        r#"struct H { b: Box<i64>, n: i64 }
        fn replace(h: &mut H) -> Unit ! {alloc, panic} {
            *h = H { b: Box.new(9), n: 2 };
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut h = H { b: Box.new(1), n: 0 };
            replace(&mut h);
            replace(&mut h);
            Box.read(&h.b) + h.n
        }"#,
        11,
        "",
    );
}

#[test]
fn place_reference_hostile_forms_are_rejected() {
    // Two overlapping field references of the same owner, including the same
    // field through a stored reference, are rejected.
    rejects(
        r#"struct Pair { a: i64, b: i64 }
        fn add(l: &mut i64, r: &mut i64) -> Unit ! {panic} { *l = *l + *r; }
        fn main() -> i64 ! {panic} {
            let mut p = Pair { a: 3, b: 4 };
            add(&mut p.a, &mut p.a);
            0
        }"#,
        "cannot create an exclusive place borrow",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 1, y: 2 };
            let r = &mut p.x;
            let s = &mut p.x;
            *r = 1;
            0
        }"#,
        "cannot create an exclusive place borrow",
    );
    // A mutable element reference suspends vector growth and whole-owner
    // access until its checked last use.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = [1, 2];
            let r = &mut v[0];
            Vec.push(&mut v, 3);
            *r
        }"#,
        "cannot borrow an owner",
    );
    // A field reference cannot escape the function that owns the storage.
    rejects(
        r#"struct P { x: i64 }
        fn escape() -> &i64 ! {panic} {
            let p = P { x: 1 };
            &p.x
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot be returned",
    );
    // Reading through a typed reference never copies an owning payload.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let b = Box.new(4);
            let r = &b;
            *r
        }"#,
        "dereferencing would copy an owning or linear payload",
    );
    // Replacing an owning handle uses its own operation, not a place write.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut b = Box.new(1);
            let r = &mut b;
            *r = Box.new(2);
            Box.read(&b)
        }"#,
        "replace an owning handle through its own operation",
    );
    // Index references alias only non-owning elements.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<Box<i64>> = [Box.new(1)];
            let r = &mut v[0];
            0
        }"#,
        "an index reference would alias an owning or linear element",
    );
    // A linear referent is never silently dropped by reference replacement.
    rejects(
        r#"#[linear]
        struct L { x: i64 }
        fn replace(p: &mut L) -> Unit ! {panic} { *p = L { x: 1 }; }
        fn main() -> Unit ! {panic} {}"#,
        "cannot replace a linear payload",
    );
    // Text views are immutable; a `&mut str` parameter is rejected at its
    // declaration rather than pretending arbitrary byte mutation preserves
    // UTF-8. A sound `&mut str` needs a replacement operation that validates
    // every write as one Unicode scalar with an unchanged encoded length.
    rejects(
        r#"fn read(text: &mut str) -> i64 ! {panic} { Str.len(text) }
        fn main() -> i64 ! {panic} { 0 }"#,
        "mutable borrowed text '&mut str' is not supported",
    );
}

#[test]
fn out_of_bounds_place_indices_panic_in_both_backends() {
    runtime_panic(
        r#"fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let i = 5;
            let r = &mut a[i];
            *r = 9;
            0
        }"#,
    );
    runtime_panic(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = [1, 2];
            let i = 9;
            let r = &mut v[i];
            *r = 9;
            0
        }"#,
    );
}

#[test]
fn borrowed_task_exit_child_and_environment_boundaries_are_rejected() {
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> i64 ! {alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
                let t: Task<TaskExit<Window<'a>>> = Task.spawn(fn() -> TaskExit<Window<'a>> ! {panic, suspend} { panic() });
                Task.join(t);
                0
            })
        }
        fn main() -> i64 ! {alloc, panic, suspend} { 0 }"#,
        "a child task cannot return a borrowed TaskExit",
    );
    rejects(
        r#"use std.task.TaskExit;
        struct Window<'a> { view: &'a [i64], start: i64 }
        fn run<'a>(window: Window<'a>) -> once fn() -> i64 ! {panic} ! {alloc, panic, suspend} {
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
        fn main() -> i64 ! {alloc, panic, suspend} { 0 }"#,
        "cannot capture TaskExit",
    );
}

#[test]
fn borrowed_record_containers_preserve_per_field_element_provenance() {
    // A vector element that is itself a borrowed record keeps every field
    // leaf: construction, indexed reads, append, replacement, and clearing all
    // preserve the owners behind the record's reference fields.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let holders = [Holder { point: &p, note: 0 }];
            let h = Vec.get(&holders, 0);
            h.point.x + h.point.y
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn keep<'a>(values: Vec<Holder<'a>>) -> Vec<Holder<'a>> ! {alloc} { values }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 1, y: 0 };
            let b = Point { x: 40, y: 2 };
            let values = [Holder { point: &a, note: 0 }];
            let values = Vec.push(values, Holder { point: &b, note: 1 });
            let values = Vec.set(values, 0, Holder { point: &b, note: 0 });
            let values = keep(values);
            Vec.get(&values, 0).point.x + Vec.get(&values, 1).point.y
        }"#,
        42,
        "",
    );
    // A borrowed-record element inside a nominal record keeps its per-field
    // path through destructuring and a helper boundary.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        struct Bundle<'a> { holders: Vec<Holder<'a>>, note: i64 }
        fn read<'a>(bundle: Bundle<'a>) -> i64 ! {panic} {
            let Bundle { holders, note } = bundle;
            Vec.get(&holders, 0).point.x + note
        }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            read(Bundle { holders: [Holder { point: &p, note: 0 }], note: 2 }) + p.y
        }"#,
        44,
        "",
    );
    // Box<Holder> supports read and take with the same field leaves.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn wrap<'a>(holder: Holder<'a>) -> Box<Holder<'a>> ! {alloc, panic} { Box.new(holder) }
        fn read<'a>(holder: Holder<'a>) -> i64 ! {panic} { holder.point.x + holder.note }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let boxed = wrap(Holder { point: &p, note: 0 });
            let copied = Box.read(&boxed);
            read(Box.take(boxed)) + copied.point.y
        }"#,
        42,
        "",
    );
    // Writing a new borrowed record through `&mut Box<Holder>` replaces the
    // element loan only after the written record's own owners are checked.
    agrees(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn replace<'a>(boxed: &mut Box<Holder<'a>>, holder: Holder<'a>) -> i64 ! {panic} {
            Box.set(boxed, holder);
            Box.read(boxed).point.x
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point { x: 1, y: 0 };
            let b = Point { x: 40, y: 2 };
            let mut boxed = Box.new(Holder { point: &a, note: 0 });
            replace(&mut boxed, Holder { point: &b, note: 1 }) + b.y
        }"#,
        42,
        "",
    );
}

#[test]
fn borrowed_record_containers_reject_owner_moves_and_block_escapes() {
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point { x: 40, y: 2 };
            let holders = [Holder { point: &p, note: 0 }];
            let h = Vec.get(&holders, 0);
            p = Point { x: 1, y: 1 };
            h.point.x
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let q = Point { x: 0, y: 0 };
            let mut values = [Holder { point: &q, note: 0 }];
            {
                let p = Point { x: 40, y: 2 };
                values = Vec.push(values, Holder { point: &p, note: 0 });
            }
            Vec.get(&values, 1).point.x
        }"#,
        "borrow escapes the lexical scope",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn add<'a>(values: &mut Vec<Holder<'a>>, holder: Holder<'a>) -> Unit ! {alloc, panic} {
            Vec.push(values, holder);
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Holder<'_>> = [];
            {
                let p = Point { x: 40, y: 2 };
                add(&mut values, Holder { point: &p, note: 0 });
            }
            Vec.get(&values, 0).point.x
        }"#,
        "borrow escapes the lexical scope",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn leak<'a>() -> Vec<Holder<'a>> ! {alloc, panic} {
            let local = Point { x: 1, y: 2 };
            [Holder { point: &local, note: 0 }]
        }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "does not appear on any parameter",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point { x: 40, y: 2 };
            let boxed = Box.new(Holder { point: &p, note: 0 });
            let h = Box.read(&boxed);
            p = Point { x: 1, y: 1 };
            h.point.x
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Holder<'a> { point: &'a Point, note: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point { x: 40, y: 2 };
            let values = [Holder { point: &p, note: 0 }];
            let h = Vec.get(&values, 0);
            let values = Vec.clear(values);
            drop(values);
            p = Point { x: 1, y: 1 };
            h.point.x
        }"#,
        "cannot replace an owner",
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

#[test]
fn returned_reference_containers_keep_their_sources_borrowed() {
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn wrap<'a>(p: &'a Point) -> Box<&'a Point> ! {alloc, panic} { Box.new(p) }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point {x: 40, y: 2};
            let boxed = wrap(&p);
            p = Point {x: 0, y: 0};
            let reference = Box.take(boxed);
            reference.x
        }"#,
        "borrow",
    );
}

#[test]
fn every_reference_vector_element_remains_borrowed_after_append_and_replace() {
    for build in [
        "let values: Vec<&Point> = [&a, &b];",
        "let values: Vec<&Point> = [&a]; let values = Vec.push(values, &b);",
    ] {
        rejects(
            &format!(
                "struct Point {{ x: i64, y: i64 }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let mut a = Point {{x: 40, y: 2}};
                let b = Point {{x: 1, y: 0}};
                {build}
                a = Point {{x: 0, y: 0}};
                Vec.get(&values, 0).x
            }}"
            ),
            "borrow",
        );
    }
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let a = Point {x: 1, y: 0};
            let mut b = Point {x: 40, y: 2};
            let values: Vec<&Point> = [&a];
            let values = Vec.set(values, 0, &b);
            b = Point {x: 0, y: 0};
            Vec.get(&values, 0).x
        }"#,
        "borrow",
    );
}

#[test]
fn reference_container_results_work_through_named_and_indirect_calls() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn wrap<'a>(p: &'a Point) -> Box<&'a Point> ! {alloc, panic} { Box.new(p) }
        fn keep<'a>(values: Vec<&'a Point>) -> Vec<&'a Point> ! {} { values }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point {x: 40, y: 2};
            let boxed = wrap(&p);
            let reference = Box.take(boxed);
            let values: Vec<&Point> = [reference];
            let call: fn<'a>(Vec<&'a Point>) -> Vec<&'a Point> ! {} = keep;
            let values = call(values);
            Vec.get(&values, 0).x + p.y
        }"#,
        42,
        "",
    );
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn wrap<'a>(p: &'a mut Point) -> Box<&'a mut Point> ! {alloc, panic} { Box.new(p) }
        fn main() -> i64 ! {alloc, panic} {
            let mut p = Point {x: 40, y: 0};
            let boxed = wrap(&mut p);
            let reference = Box.take(boxed);
            reference.y = 2;
            p.x + p.y
        }"#,
        42,
        "",
    );
}

#[test]
fn shared_reference_vectors_can_replace_elements_and_clear_all_source_loans() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point {x: 1, y: 0};
            let mut b = Point {x: 40, y: 2};
            let values: Vec<&Point> = [&a];
            let values = Vec.push(values, &b);
            let values = Vec.set(values, 0, &b);
            let answer = Vec.get(&values, 0).x + Vec.get(&values, 1).y;
            let values = Vec.clear(values);
            a = Point {x: 3, y: 0};
            b = Point {x: 4, y: 0};
            drop(values);
            answer
        }"#,
        42,
        "",
    );
    rejects(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        struct Point { x: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point {x: 42};
            let values: Vec<&Point> = [&p];
            drop(Vec.try_reserve(values, 1));
            0
        }"#,
        "enums cannot store borrowed",
    );
}

#[test]
fn structural_record_coercion_keeps_per_field_borrows() {
    // The kept field moves from source index 1 to target index 0; its loan
    // must follow it through the conversion, both for slice views and
    // reference containers, and through destructuring or projection.
    rejects(
        r#"struct Window<'a> { start: i64, view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [40];
            let w = Window { start: 0, view: &data[..] };
            let narrow: struct { view: &[i64] } = w;
            match narrow { struct { view } => { data = [9]; Slice.get(view, 0) } }
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Window<'a> { start: i64, view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [40];
            let w = Window { start: 0, view: &data[..] };
            let narrow: struct { view: &[i64] } = w;
            let v = narrow.view;
            data = [9];
            Slice.get(v, 0)
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        struct Bundle { note: i64, points: Vec<&Point> }
        fn main() -> i64 ! {alloc, panic} {
            let mut a = Point { x: 40, y: 2 };
            let b = Bundle { note: 2, points: [&a] };
            let narrow: struct { points: Vec<&Point> } = b;
            match narrow { struct { points } => {
                a = Point { x: 1, y: 1 };
                Vec.get(&points, 0).x
            } }
        }"#,
        "cannot replace an owner",
    );
    rejects(
        r#"struct Pair<'a> { left: &'a [i64], right: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let a: Vec<i64> = [1];
            let mut b: Vec<i64> = [41];
            let p = Pair { left: &a[..], right: &b[..] };
            let narrow: struct { right: &[i64] } = p;
            match narrow { struct { right } => { b = [9]; Slice.get(right, 0) } }
        }"#,
        "cannot replace an owner",
    );
    // The dropped field's loan ends with the field.
    agrees(
        r#"struct Pair<'a> { left: &'a [i64], right: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: Vec<i64> = [1];
            let b: Vec<i64> = [41];
            let p = Pair { left: &a[..], right: &b[..] };
            let narrow: struct { right: &[i64] } = p;
            match narrow { struct { right } => { a = [9]; Slice.get(right, 0) + 1 } }
        }"#,
        42,
        "",
    );
}

#[test]
fn shared_reference_container_parameters_read_their_elements() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
        fn read<'a>(b: &'a Box<&Point>) -> i64 ! {panic} {
            let r = Box.read(b);
            r.x + r.y
        }
        fn first<'a>(v: &'a Vec<&Point>) -> i64 ! {panic} { Vec.get(v, 0).x }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let boxed: Box<&Point> = Box.new(&p);
            let v: Vec<&Point> = [&p];
            read(&boxed) + first(&v) - 40
        }"#,
        42,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn leak<'a, 'b>(b: &'a Box<&'b Point>) -> &'a Point ! {panic} { Box.read(b) }
        fn main() -> i64 ! {alloc, panic} {
            let p = Point { x: 40, y: 2 };
            let boxed: Box<&Point> = Box.new(&p);
            leak(&boxed).x
        }"#,
        "reference result lifetime",
    );
}

#[test]
fn writes_through_a_stored_mutable_reference_reach_the_owner_scope_check() {
    let escape = "borrow escapes the lexical scope";
    rejects(
        r#"fn add<'a>(v: &mut Vec<&'a str>, s: &'a str) -> Unit ! {alloc, panic} { Vec.push(v, s); }
        fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<&str> = [];
            {
                let r = &mut v;
                let s = "abcd";
                add(r, s.as_str());
            }
            Str.len(Vec.get(&v, 0))
        }"#,
        escape,
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
        fn add<'a>(v: &mut Vec<&'a Point>, p: &'a Point) -> Unit ! {alloc, panic} { Vec.push(v, p); }
        fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<&Point> = [];
            {
                let r = &mut v;
                let p = Point { x: 40, y: 2 };
                add(r, &p);
            }
            Vec.get(&v, 0).x
        }"#,
        escape,
    );
    rejects(
        r#"fn put<'a>(b: &mut Box<&'a str>, s: &'a str) -> Unit ! {alloc, panic} { Box.set(b, s); }
        fn main() -> i64 ! {alloc, panic} {
            let keep = "zz";
            let mut b: Box<&str> = Box.new(keep.as_str());
            {
                let r = &mut b;
                let s = "abcd";
                put(r, s.as_str());
            }
            Str.len(Box.read(&b))
        }"#,
        escape,
    );
    agrees(
        r#"fn add<'a>(v: &mut Vec<&'a str>, s: &'a str) -> Unit ! {alloc, panic} { Vec.push(v, s); }
        fn main() -> i64 ! {alloc, panic} {
            let s = "abcd";
            let mut v: Vec<&str> = [];
            {
                let r = &mut v;
                add(r, s.as_str());
            }
            Str.len(Vec.get(&v, 0))
        }"#,
        4,
        "",
    );
}
