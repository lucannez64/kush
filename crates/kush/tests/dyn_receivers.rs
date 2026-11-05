//! Trait-object receivers that are not a plain local: temporaries and other
//! owned object values kept in hidden statement storage, receiver-tied views
//! through them, and projected fields. Every accepted program runs in the
//! reference evaluator and the native backend with balanced allocations.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("dyn-receivers-test");
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
    stats
}

/// `Pick` has a view tied to the receiver lifetime (`pick`), an elided view
/// (`el`, which really borrows the receiver's inline storage), and a mutable
/// method. `Text` owns a `String`, so every object payload owns storage.
const PICK: &str = r#"
trait Pick {
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic};
    fn el(self: &Self) -> &[i64] ! {alloc, panic};
    fn bump(self: &mut Self) -> i64 ! {panic};
}
struct Text { tag: i64, name: String, arr: DynArray<i64, 3> }
struct Plain { tag: i64, arr: DynArray<i64, 3> }
impl Pick for Text {
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
    fn el(self: &Self) -> &[i64] ! {alloc, panic} { &self.arr[..] }
    fn bump(self: &mut Self) -> i64 ! {panic} { self.tag = self.tag + 1; self.tag }
}
impl Pick for Plain {
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
    fn el(self: &Self) -> &[i64] ! {alloc, panic} { &self.arr[..] }
    fn bump(self: &mut Self) -> i64 ! {panic} { self.tag = self.tag + 10; self.tag }
}
"#;

/// The same trait with a generic impl, so `dyn Pick` uses the open dynamic
/// fat-object representation instead of the closed-world union.
const OPEN: &str = r#"
struct Wrap<T> { value: T, arr: DynArray<i64, 3> }
impl<T> Pick for Wrap<T> {
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
    fn el(self: &Self) -> &[i64] ! {alloc, panic} { &self.arr[..] }
    fn bump(self: &mut Self) -> i64 ! {panic} { 70 }
}
fn wrap() -> dyn Pick ! {alloc, panic} {
    Wrap { value: Text { tag: 0, name: "w", arr: [0] }, arr: [4, 5, 6] }
}
"#;

const MAKE: &str = r#"
fn make() -> dyn Pick ! {alloc, panic} { Text { tag: 1, name: "t", arr: [8, 9, 10] } }
fn plain() -> dyn Pick ! {alloc, panic} { Plain { tag: 2, arr: [1, 2, 3] } }
"#;

fn program(open: bool, main: &str) -> String {
    format!(
        "{PICK}{}{MAKE}\nfn main() -> i64 ! {{io, alloc, panic}} {{\n{main}\n}}\n",
        if open { OPEN } else { "" }
    )
}

#[test]
fn temporary_receivers_dispatch_in_hidden_storage_in_both_representations() {
    let main = r#"
        let values = [5, 6, 7];
        print_i64(make().pick(&values[..])[1]);
        print_i64(make().bump());
        print_i64(plain().bump());
        let mut i = 0;
        while i < 2 && make().bump() == 2 { i = i + 1; }
        print_i64(i);
        0"#;
    let closed = agrees(&program(false, main), 0, "6\n2\n12\n2\n");
    let open = agrees(&program(true, main), 0, "6\n2\n12\n2\n");
    // make() runs four times (the third loop test short-circuits on `i < 2`)
    // and plain() once. The open representation adds exactly one payload per
    // object, and every allocation is released once (checked by `run`).
    assert_eq!(open.allocations, closed.allocations + 5);
}

#[test]
fn receiver_tied_views_through_temporaries_live_through_the_let() {
    for open in [false, true] {
        agrees(
            &program(
                open,
                r#"
                let values = [5, 6, 7];
                let tied = make().pick(&values[..]);
                let elided = make().el();
                print_i64(tied[2] + elided[0]);
                print_i64(make().el()[2]);
                print_i64(plain().el().len());
                0"#,
            ),
            0,
            "15\n10\n3\n",
        );
    }
    agrees(
        &program(
            true,
            r#"
            let view = wrap().el();
            print_i64(view[1]);
            0"#,
        ),
        0,
        "5\n",
    );
}

#[test]
fn owned_object_values_of_any_expression_form_back_their_views() {
    for open in [false, true] {
        let stats = agrees(
            &program(
                open,
                r#"
                let mut first = make();
                let second = plain();
                let boxed: Box<dyn Pick> = Box.new(make());
                let chosen = if first.bump() > 1 { first } else { second };
                let view = chosen.el();
                print_i64(view[0]);
                let moved = Box.take(boxed).el();
                print_i64(moved[1]);
                let block = { let inner = plain(); inner }.el();
                print_i64(block[2]);
                0"#,
            ),
            0,
            "8\n9\n3\n",
        );
        assert_eq!(stats.allocations, stats.deallocations);
    }
}

#[test]
fn views_of_hidden_receiver_storage_cannot_outlive_their_block() {
    for open in [false, true] {
        rejects(
            &program(
                open,
                r#"
                let view = { make().el() };
                print_i64(view[0]);
                0"#,
            ),
            "outlive",
        );
        rejects(
            &format!(
                "{PICK}{}{MAKE}
                fn leak<'a>(values: &'a [i64]) -> &'a [i64] ! {{alloc, panic}} {{
                    make().pick(values)
                }}
                fn main() -> i64 ! {{io, alloc, panic}} {{
                    let values = [1, 2];
                    print_i64(leak(&values[..])[0]);
                    0
                }}",
                if open { OPEN } else { "" }
            ),
            "outlive",
        );
    }
}

#[test]
fn linear_temporary_receivers_must_still_be_consumed() {
    let linear = r#"
        #[linear]
        struct Ticket { id: i64 }
        struct Wrap<T> { value: T }
        trait Look {
            fn look(self: &Self) -> i64 ! {panic};
            fn done(self: Self) -> i64 ! {panic};
        }
        impl Look for Ticket {
            fn look(self: &Self) -> i64 ! {panic} { self.id }
            fn done(self: Self) -> i64 ! {panic} { let Ticket { id } = self; id + 1 }
        }
        impl<T: Look> Look for Wrap<T> {
            fn look(self: &Self) -> i64 ! {panic} { 3 }
            fn done(self: Self) -> i64 ! {panic} { let Wrap { value } = self; value.done() }
        }
    "#;
    rejects(
        &format!(
            "{linear} fn main() -> i64 ! {{alloc, panic}} {{
            {{ let ticket: dyn Look = Ticket {{ id: 1 }}; ticket }}.look()
        }}"
        ),
        "linear value is not consumed",
    );
    agrees(
        &format!(
            "{linear} fn main() -> i64 ! {{alloc, panic}} {{
            {{ let ticket: dyn Look = Ticket {{ id: 1 }}; ticket }}.done()
        }}"
        ),
        2,
        "",
    );
}

/// `Bump` has exclusive, shared, and view-returning methods. `Text` owns a
/// `String`; `Other` is copyable. `OPEN_BUMP` adds a generic impl so the same
/// programs also run through the open dynamic representation.
const BUMP: &str = r#"
struct Text { name: String, count: i64 }
struct Other { count: i64 }
trait Bump {
    fn bump(self: &mut Self, by: i64) -> i64 ! {panic};
    fn look(self: &Self) -> i64 ! {panic};
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic};
}
impl Bump for Text {
    fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count }
    fn look(self: &Self) -> i64 ! {panic} { self.count }
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
}
impl Bump for Other {
    fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { self.count = self.count + by; self.count }
    fn look(self: &Self) -> i64 ! {panic} { self.count }
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
}
struct Holder<T> { inner: T, tag: i64 }
struct Outer<T> { holder: Holder<T>, extra: i64 }
fn poke(holder: &mut Holder<dyn Bump>, by: i64) -> i64 ! {panic} { holder.inner.bump(by) }
fn peek(holder: &Holder<dyn Bump>) -> i64 ! {panic} { holder.inner.look() }
"#;

const OPEN_BUMP: &str = r#"
struct Nominal { inner: dyn Bump, tag: i64 }
impl Nominal {
    fn poke(self: &mut Self, by: i64) -> i64 ! {panic} { self.inner.bump(by) }
    fn peek(self: &Self) -> i64 ! {panic} { self.inner.look() }
}
struct Wrap<T> { value: T }
impl<T> Bump for Wrap<T> {
    fn bump(self: &mut Self, by: i64) -> i64 ! {panic} { by }
    fn look(self: &Self) -> i64 ! {panic} { 0 }
    fn pick<'a>(self: &'a Self, values: &'a [i64]) -> &'a [i64] ! {panic} { values }
}
"#;

fn bump_program(open: bool, main: &str) -> String {
    format!(
        "{BUMP}{}\nfn main() -> i64 ! {{io, alloc, panic}} {{\n{main}\n}}\n",
        if open { OPEN_BUMP } else { "" }
    )
}

#[test]
fn mutable_dispatch_on_projected_fields_writes_in_place() {
    for open in [false, true] {
        agrees(
            &bump_program(
                open,
                r#"
                let mut pair: (dyn Bump, i64) = (Text { name: "x", count: 1 }, 9);
                print_i64(pair.0.bump(5));
                print_i64(pair.0.bump(pair.1));
                print_i64(pair.0.look());
                let mut outer: Outer<dyn Bump> = Outer {
                    holder: Holder { inner: Other { count: 3 }, tag: 0 },
                    extra: 1,
                };
                print_i64(outer.holder.inner.bump(4));
                print_i64(outer.holder.inner.look());
                let mut holder: Holder<dyn Bump> = Holder { inner: Text { name: "y", count: 20 }, tag: 1 };
                print_i64(poke(&mut holder, 10));
                print_i64(peek(&holder));
                print_i64(holder.inner.look());
                0"#,
            ),
            0,
            "6\n15\n15\n7\n7\n30\n30\n30\n",
        );
    }
    // A nominal field spelling `dyn Bump` is reached through `&mut self`.
    agrees(
        &bump_program(
            true,
            r#"
            let mut nominal = Nominal { inner: Text { name: "z", count: 1 }, tag: 0 };
            print_i64(nominal.poke(10));
            print_i64(nominal.peek());
            print_i64(nominal.inner.bump(1));
            0"#,
        ),
        0,
        "11\n11\n12\n",
    );
}

#[test]
fn projected_field_views_keep_their_owner_borrowed() {
    for open in [false, true] {
        agrees(
            &bump_program(
                open,
                r#"
                let values = [4, 5];
                let mut pair: (dyn Bump, i64) = (Text { name: "x", count: 1 }, 9);
                let view = pair.0.pick(&values[..]);
                print_i64(view[1]);
                pair = (Other { count: 2 }, 3);
                print_i64(pair.0.bump(1));
                0"#,
            ),
            0,
            "5\n3\n",
        );
        rejects(
            &bump_program(
                open,
                r#"
                let values = [4, 5];
                let mut pair: (dyn Bump, i64) = (Text { name: "x", count: 1 }, 9);
                let view = pair.0.pick(&values[..]);
                pair = (Other { count: 2 }, 3);
                print_i64(view[1]);
                0"#,
            ),
            "borrow",
        );
    }
}

#[test]
fn projected_mutable_dispatch_respects_owner_capabilities_and_loans() {
    for open in [false, true] {
        for (main, expected) in [
            (
                "let pair: (dyn Bump, i64) = (Other { count: 1 }, 9); pair.0.bump(1)",
                "needs a mutable owner",
            ),
            (
                "let mut pair: (dyn Bump, i64) = (Other { count: 1 }, 9); pair.0.bump(pair.0.look())",
                "exclusive borrow",
            ),
            (
                "let mut pair: (dyn Bump, i64) = (Other { count: 1 }, 9); pair.0.bump({ pair = (Other { count: 5 }, 1); 0 })",
                "borrows it",
            ),
            (
                "let mut pair: (dyn Bump, i64) = (Other { count: 1 }, 9); let r = &pair; pair.0.bump(1) + r.1",
                "overlapping borrow",
            ),
            (
                "let mut pair: (dyn Bump, i64) = (Other { count: 1 }, 9); let moved = pair; pair.0.bump(1)",
                "moved",
            ),
        ] {
            rejects(&bump_program(open, main), expected);
        }
        rejects(
            &format!(
                "{BUMP}{}
                fn bad(holder: &Holder<dyn Bump>) -> i64 ! {{panic}} {{ holder.inner.bump(1) }}
                fn main() -> i64 ! {{alloc, panic}} {{ 0 }}",
                if open { OPEN_BUMP } else { "" }
            ),
            "needs a mutable owner",
        );
    }
}

/// Consuming methods; `Ticket` is linear and must be consumed exactly once.
const EAT: &str = r#"
#[linear]
struct Ticket { id: i64 }
struct Text { name: String, count: i64 }
struct Other { count: i64 }
trait Eat { fn eat(self: Self, extra: i64) -> i64 ! {panic}; }
impl Eat for Text { fn eat(self: Self, extra: i64) -> i64 ! {panic} { self.count + extra } }
impl Eat for Other { fn eat(self: Self, extra: i64) -> i64 ! {panic} { self.count + extra } }
impl Eat for Ticket {
    fn eat(self: Self, extra: i64) -> i64 ! {panic} { let Ticket { id } = self; id + extra }
}
struct Holder<T> { inner: T, label: String }
struct Outer<T> { holder: Holder<T>, extra: Vec<i64> }
fn ticket() -> Ticket @[1] ! {} { Ticket { id: 40 } }
"#;

const OPEN_EAT: &str = r#"
struct Wrap<T> { value: T }
impl<T> Eat for Wrap<T> { fn eat(self: Self, extra: i64) -> i64 ! {panic} { 100 + extra } }
"#;

fn eat_program(open: bool, main: &str) -> String {
    format!(
        "{EAT}{}\nfn main() -> i64 ! {{io, alloc, panic}} {{\n{main}\n}}\n",
        if open { OPEN_EAT } else { "" }
    )
}

#[test]
fn consuming_dispatch_on_projected_fields_consumes_the_aggregate_once() {
    let main = r#"
        let pair: (dyn Eat, String) = (Text { name: "x", count: 1 }, "sibling");
        print_i64(pair.0.eat(0));
        let mut items: Vec<i64> = Vec.new();
        items = Vec.push(items, 3);
        let outer: Outer<dyn Eat> = Outer {
            holder: Holder { inner: Other { count: 7 }, label: "label" },
            extra: items,
        };
        print_i64(outer.holder.inner.eat(0));
        let mut again: (i64, dyn Eat) = (4, Text { name: "y", count: 9 });
        print_i64(again.1.eat(1));
        again = (5, Other { count: 2 });
        print_i64(again.1.eat(0));
        let linear: (dyn Eat, i64) = (ticket(), 9);
        print_i64(linear.0.eat(2));
        0"#;
    let output = "1\n7\n10\n2\n42\n";
    // Every sibling String/Vec is released exactly once (checked by `run`);
    // the open representation adds one payload for each of the five objects.
    let closed = agrees(&eat_program(false, main), 0, output);
    let open = agrees(&eat_program(true, main), 0, output);
    assert_eq!(open.allocations, closed.allocations + 5);
}

#[test]
fn consuming_projected_dispatch_follows_destructuring_rules() {
    for open in [false, true] {
        for (main, expected) in [
            // The aggregate is consumed by the receiver, before the arguments.
            (
                r#"let pair: (dyn Eat, i64) = (Other { count: 1 }, 9); print_i64(pair.0.eat(0)); print_i64(pair.1); 0"#,
                "moved",
            ),
            (
                r#"let pair: (dyn Eat, i64) = (Other { count: 1 }, 9); pair.0.eat(pair.1)"#,
                "moved",
            ),
            // A linear sibling cannot be released implicitly.
            (
                r#"let pair: (dyn Eat, Ticket) = (Other { count: 1 }, ticket()); pair.0.eat(0)"#,
                "is linear",
            ),
            // A borrowed or loop-carried owner cannot be consumed.
            (
                r#"let pair: (dyn Eat, i64) = (Other { count: 1 }, 9); let r = &pair; let a = pair.0.eat(0); a + r.1"#,
                "borrowed",
            ),
            (
                r#"let pair: (dyn Eat, i64) = (Other { count: 1 }, 9); let mut i = 0; while i < 2 { i = i + pair.0.eat(0); } i"#,
                "loop",
            ),
            // An unconsumed linear object field still has to be consumed.
            (
                r#"let pair: (dyn Eat, i64) = (ticket(), 9); print_i64(pair.1); 0"#,
                "linear value is not consumed",
            ),
        ] {
            rejects(&eat_program(open, main), expected);
        }
        rejects(
            &format!(
                "{EAT}{}
                fn bad(holder: &Holder<dyn Eat>) -> i64 ! {{panic}} {{ holder.inner.eat(0) }}
                fn main() -> i64 ! {{alloc, panic}} {{ 0 }}",
                if open { OPEN_EAT } else { "" }
            ),
            "behind a reference",
        );
    }
}

/// A closed object whose trait has exactly one impl keeps its object type in
/// a tuple (D-SINGLE-TUPLE): projected shared, mutable and consuming calls
/// dispatch on the object, and the member type is not recovered implicitly.
const SINGLE: &str = r#"
struct Text { tag: i64, name: String }
trait Show {
    fn show(self: &Self) -> i64 ! {panic};
    fn bump(self: &mut Self) -> i64 ! {panic};
    fn eat(self: Self) -> i64 ! {panic};
}
impl Show for Text {
    fn show(self: &Self) -> i64 ! {panic} { self.tag }
    fn bump(self: &mut Self) -> i64 ! {panic} { self.tag = self.tag + 1; self.tag }
    fn eat(self: Self) -> i64 ! {panic} { let Text { tag, name } = self; tag * 10 }
}
"#;

#[test]
fn single_impl_objects_keep_their_object_type_inside_tuples() {
    let stats = agrees(
        &format!(
            r#"{SINGLE}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut pair: (dyn Show, i64) = (Text {{ tag: 7, name: String.from("hello") }}, 1);
                print_i64(pair.0.show());
                print_i64(pair.0.bump());
                let mut other: (i64, dyn Show) = (3, Text {{ tag: 1, name: String.from("x") }});
                print_i64(other.1.bump());
                let (n, object) = other;
                print_i64(object.eat() + n);
                print_i64(pair.1);
                print_i64(pair.0.eat());
                0
            }}"#
        ),
        0,
        "7\n8\n2\n23\n1\n80\n",
    );
    // One `String` per object; both are released by the consuming calls.
    assert_eq!(stats.allocations, 2, "{stats:?}");
}

#[test]
fn single_impl_objects_are_not_their_member_type() {
    // Projected out of a tuple (previously accepted through the collapse).
    rejects(
        r#"struct Text { name: i64 }
        trait Show { fn show(self: &Self) -> i64 ! {panic}; }
        impl Show for Text { fn show(self: &Self) -> i64 ! {panic} { self.name } }
        fn main() -> i64 ! {alloc, panic} {
            let pair: (dyn Show, i64) = (Text { name: 7 }, 1);
            let t: Text = pair.0;
            t.show()
        }"#,
        "expected Text, found dyn Show",
    );
    // A plain local (previously an internal representation error).
    rejects(
        &format!(
            r#"{SINGLE}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Show = Text {{ tag: 7, name: String.from("a") }};
                let t: Text = object;
                t.eat()
            }}"#
        ),
        "expected Text, found dyn Show",
    );
}

#[test]
fn single_impl_objects_stay_objects_through_joins() {
    for join in ["if n == 5 { a } else { b }", "match n { 5 => a, _ => b }"] {
        let stats = agrees(
            &format!(
                r#"{SINGLE}
                fn main() -> i64 ! {{io, alloc, panic}} {{
                    let a: dyn Show = Text {{ tag: 1, name: String.from("a") }};
                    let b: dyn Show = Text {{ tag: 2, name: String.from("b") }};
                    let n = 7;
                    let mut q = {join};
                    print_i64(q.bump());
                    print_i64(q.eat());
                    0
                }}"#
            ),
            0,
            "3\n30\n",
        );
        assert_eq!(stats.allocations, 2, "{stats:?}");
    }
}

#[test]
fn objects_sharing_one_representation_name_every_trait() {
    rejects(
        r#"struct Text { tag: i64 }
        trait Show { fn show(self: &Self) -> i64 ! {panic}; }
        trait Other { fn other(self: &Self) -> i64 ! {panic}; }
        impl Show for Text { fn show(self: &Self) -> i64 ! {panic} { self.tag } }
        impl Other for Text { fn other(self: &Self) -> i64 ! {panic} { self.tag * 2 } }
        fn main() -> i64 ! {panic} {
            let b: dyn Other = Text { tag: 1 };
            let z: i64 = b;
            z
        }"#,
        "found dyn Other or dyn Show",
    );
}

// D-SINGLE-JOIN: a one-impl object is the union of its single member, so a
// join whose least upper bound is exactly that member set stays the object.

fn single_main(body: &str) -> String {
    format!(
        r#"{SINGLE}
        fn first<T>(a: T, b: T) -> T ! {{}} {{ let _ = b; a }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let a: dyn Show = Text {{ tag: 1, name: String.from("a") }};
            let n = 7;
            {body}
        }}"#
    )
}

#[test]
fn generic_inference_from_two_single_impl_objects_keeps_the_object() {
    let stats = agrees(
        &single_main(
            r#"let b: dyn Show = Text { tag: 2, name: String.from("b") };
            let mut q = first(a, b);
            print_i64(q.bump());
            print_i64(q.eat());
            0"#,
        ),
        0,
        "2\n20\n",
    );
    assert_eq!(stats.allocations, 2, "{stats:?}");
}

#[test]
fn joins_of_an_object_and_its_member_type_become_the_object() {
    let text = r#"Text { tag: 4, name: String.from("t") }"#;
    // `n` is 7: the member arm gives 5/50, the object arm 2/20.
    for (join, expected) in [
        (format!("match n {{ 5 => a, _ => {text} }}"), "5\n50\n"),
        (format!("match n {{ 5 => {text}, _ => a }}"), "2\n20\n"),
        (format!("if n == 5 {{ a }} else {{ {text} }}"), "5\n50\n"),
        (format!("if n == 7 {{ {text} }} else {{ a }}"), "5\n50\n"),
        (format!("if n == 7 {{ a }} else {{ {text} }}"), "2\n20\n"),
    ] {
        let stats = agrees(
            &single_main(&format!(
                "let mut q = {join};
                print_i64(q.bump());
                print_i64(q.eat());
                0"
            )),
            0,
            expected,
        );
        // `a` always allocates; the member arm allocates only when taken.
        let built = if expected.starts_with('5') { 2 } else { 1 };
        assert_eq!(stats.allocations, built, "{join}: {stats:?}");
    }
    // The selected arm is the object `a`, and it still dispatches.
    agrees(
        &single_main(
            r#"let q = match n { 7 => a, _ => Text { tag: 4, name: String.from("t") } };
            q.show()"#,
        ),
        1,
        "",
    );
}

#[test]
fn a_joined_object_is_still_not_its_member_type() {
    rejects(
        &single_main(
            r#"let q = if n == 5 { a } else { Text { tag: 4, name: String.from("t") } };
            let t: Text = q;
            t.tag"#,
        ),
        "expected Text, found dyn Show",
    );
    rejects(
        &single_main(
            r#"let b: dyn Show = Text { tag: 2, name: String.from("b") };
            let q = first(a, b);
            q.tag"#,
        ),
        "field access requires a record value, found dyn Show",
    );
    // As for any union, the first argument fixes `T`: a plain member first
    // makes `T = Text`, and the object is not a `Text`.
    rejects(
        &single_main(
            r#"let q = first(Text { tag: 2, name: String.from("b") }, a);
            0"#,
        ),
        "expected Text, found dyn Show",
    );
}

#[test]
fn joins_of_an_object_with_unrelated_types_still_flatten() {
    // Unchanged behaviour (narrow fix): `dyn Show | i64` flattens to
    // `Text | i64`, exactly as a multi-impl object flattens its members.
    agrees(
        &single_main(
            r#"let q = if n == 7 { a } else { 3 };
            match q { Text { tag, name } => tag + 40, _ => 9 }"#,
        ),
        41,
        "",
    );
}
