//! Trait-object types beyond one plain trait: explicit associated-type
//! bindings (`dyn Trait<Out = T>`) and multi-trait objects (`dyn A + B`).
//! Every accepted program runs in the reference evaluator and the native
//! backend with balanced allocations.
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
        let binary = scratch.path().join("dyn-objects-test");
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

/// `Conv`'s only impl is generic, so its projection is unknown until a member
/// is registered, unless a `dyn Conv<Out = T>` binding fixes it.
const CONV: &str = r#"
struct Label { text: String }
struct W<T> { value: T }
trait Conv {
    type Out;
    fn conv(self: &Self) -> Self.Out ! {alloc, panic};
    fn size(self: &Self) -> i64 ! {panic};
}
impl<T> Conv for W<T> {
    type Out = Label;
    fn conv(self: &Self) -> Label ! {alloc, panic} { Label { text: "made" } }
    fn size(self: &Self) -> i64 ! {panic} { 7 }
}
"#;

#[test]
fn an_explicit_binding_fixes_the_projection_before_any_member() {
    // `use_it` is checked before `main` registers the first member.
    let stats = agrees(
        &format!(
            "{CONV}
            fn use_it(object: &dyn Conv<Out = Label>) -> i64 ! {{alloc, panic}} {{
                let Label {{ text }} = object.conv();
                String.len(&text) + object.size()
            }}
            fn unused(object: &dyn Conv<Out = Label>) -> i64 ! {{alloc, panic}} {{ object.size() }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let object: dyn Conv = W {{ value: 1 }};
                print_i64(use_it(&object));
                let other: dyn Conv<Out = Label> = W {{ value: true }};
                print_i64(use_it(&other));
                0
            }}"
        ),
        0,
        "11\n11\n",
    );
    // Two payloads and two "made" strings, each released once.
    assert_eq!(stats.allocations, 4);
    rejects(
        &format!(
            "{CONV}
            fn use_it(object: &dyn Conv) -> i64 ! {{alloc, panic}} {{
                let Label {{ text }} = object.conv();
                String.len(&text)
            }}
            fn main() -> i64 ! {{alloc, panic}} {{ 0 }}"
        ),
        "associated type 'Out'",
    );
}

#[test]
fn a_binding_is_checked_against_members_impls_and_other_bindings() {
    // A later member projects a different type.
    rejects(
        &format!(
            "{CONV}
            fn size(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.size() }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Conv = W {{ value: 1 }};
                size(&object)
            }}"
        ),
        "already fixed it as i64",
    );
    // Two bindings disagree.
    rejects(
        &format!(
            "{CONV}
            fn a(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.size() }}
            fn b(object: &dyn Conv<Out = Bool>) -> i64 ! {{panic}} {{ object.size() }}
            fn main() -> i64 ! {{alloc, panic}} {{ 0 }}"
        ),
        "already fixed as",
    );
    // Concrete impls agree on a different type: closed-world object, and a
    // nominal field lowered before the impls are collected.
    let concrete = r#"
        struct A { x: i64 }
        struct B { y: i64 }
        trait Conv { type Out; fn conv(self: &Self) -> Self.Out ! {panic}; }
        impl Conv for A { type Out = i64; fn conv(self: &Self) -> i64 ! {panic} { self.x } }
        impl Conv for B { type Out = i64; fn conv(self: &Self) -> i64 ! {panic} { self.y } }
    "#;
    rejects(
        &format!(
            "{concrete}
            fn f(object: &dyn Conv<Out = Bool>) -> Bool ! {{panic}} {{ object.conv() }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "fixed as",
    );
    rejects(
        &format!(
            "{concrete}
            struct Holder {{ object: dyn Conv<Out = Bool> }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "fixes it as Bool",
    );
    // An agreeing binding on a closed-world object keeps the union (no
    // payload allocation).
    let stats = agrees(
        &format!(
            "{concrete}
            fn f(object: &dyn Conv<Out = i64>) -> i64 ! {{panic}} {{ object.conv() }}
            fn main() -> i64 ! {{io, panic}} {{
                let object: dyn Conv<Out = i64> = A {{ x: 5 }};
                print_i64(f(&object));
                0
            }}"
        ),
        0,
        "5\n",
    );
    assert_eq!(stats.allocations, 0);
}

#[test]
fn binding_syntax_is_validated() {
    for (binding, expected) in [
        ("dyn Conv<Nope = i64>", "declares no associated type 'Nope'"),
        ("dyn Conv<Out = i64, Out = i64>", "bound twice"),
    ] {
        rejects(
            &format!(
                "{CONV}
                fn f(object: &{binding}) -> i64 ! {{panic}} {{ object.size() }}
                fn main() -> i64 ! {{panic}} {{ 0 }}"
            ),
            expected,
        );
    }
    let generic = r#"
        struct W<T> { value: T }
        trait Into<X> { type Out; fn into(self: &Self, x: X) -> Self.Out ! {panic}; }
        impl<T> Into<i64> for W<T> { type Out = i64; fn into(self: &Self, x: i64) -> i64 ! {panic} { x + 1 } }
    "#;
    rejects(
        &format!(
            "{generic}
            fn f(object: &dyn Into<Out = i64, i64>) -> i64 ! {{panic}} {{ 0 }}
            fn main() -> i64 ! {{panic}} {{ 0 }}"
        ),
        "trait arguments must come before",
    );
    agrees(
        &format!(
            "{generic}
            fn f(object: &dyn Into<i64, Out = i64>) -> i64 ! {{panic}} {{ object.into(4) }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Into<i64> = W {{ value: 0 }};
                f(&object)
            }}"
        ),
        5,
        "",
    );
}

/// Two traits sharing the method name `tag`. `Text` owns a `String`.
const MULTI: &str = r#"
struct Text { name: String, count: i64 }
struct Point { x: i64 }
struct Only { v: i64 }
trait Show {
    fn show(self: &Self) -> i64 ! {panic};
    fn tag(self: &Self) -> i64 ! {panic};
}
trait Count {
    fn amount(self: &Self) -> i64 ! {panic};
    fn bump(self: &mut Self) -> Unit ! {panic};
    fn tag(self: &Self) -> i64 ! {panic};
    fn eat(self: Self) -> i64 ! {panic};
    fn pair<U>(self: &Self, value: U) -> (i64, U) ! {panic};
}
impl Show for Text {
    fn show(self: &Self) -> i64 ! {panic} { 100 + self.count }
    fn tag(self: &Self) -> i64 ! {panic} { 1 }
}
impl Count for Text {
    fn amount(self: &Self) -> i64 ! {panic} { self.count }
    fn bump(self: &mut Self) -> Unit ! {panic} { self.count = self.count + 1; }
    fn tag(self: &Self) -> i64 ! {panic} { 2 }
    fn eat(self: Self) -> i64 ! {panic} { self.count * 10 }
    fn pair<U>(self: &Self, value: U) -> (i64, U) ! {panic} { (self.count, value) }
}
impl Show for Point {
    fn show(self: &Self) -> i64 ! {panic} { 200 + self.x }
    fn tag(self: &Self) -> i64 ! {panic} { 3 }
}
impl Count for Point {
    fn amount(self: &Self) -> i64 ! {panic} { self.x }
    fn bump(self: &mut Self) -> Unit ! {panic} { self.x = self.x + 5; }
    fn tag(self: &Self) -> i64 ! {panic} { 4 }
    fn eat(self: Self) -> i64 ! {panic} { self.x * 10 }
    fn pair<U>(self: &Self, value: U) -> (i64, U) ! {panic} { (self.x, value) }
}
impl Show for Only {
    fn show(self: &Self) -> i64 ! {panic} { self.v }
    fn tag(self: &Self) -> i64 ! {panic} { 5 }
}
"#;

fn multi(main: &str) -> String {
    format!("{MULTI}\nfn main() -> i64 ! {{io, alloc, panic}} {{\n{main}\n}}\n")
}

#[test]
fn multi_trait_objects_dispatch_every_listed_trait() {
    let stats = agrees(
        &multi(
            r#"
            let mut a: dyn Show + Count = Text { name: "a", count: 1 };
            let b: dyn Count + Show = Point { x: 2 };
            print_i64(a.show());
            a.bump();
            print_i64(a.amount());
            print_i64(a.Show.tag());
            print_i64(a.Count.tag());
            print_i64(b.show() + b.amount());
            let pair = a.pair(true);
            if pair.1 { print_i64(pair.0); } else { print_i64(0); }
            print_i64(b.pair::<i64>(9).1);
            print_i64(a.eat());
            print_i64(b.eat());
            0"#,
        ),
        0,
        "101\n2\n1\n2\n204\n2\n9\n20\n20\n",
    );
    // Two payloads and one String, each released once.
    assert_eq!(stats.allocations, 3);
}

#[test]
fn multi_trait_objects_upcast_to_any_subset_of_their_traits() {
    agrees(
        &format!(
            "{MULTI}
            // Checked before any member exists: later members still reach the
            // upcast targets.
            fn as_count(object: dyn Show + Count) -> dyn Count ! {{}} {{ object }}
            fn shown(object: dyn Show) -> i64 ! {{panic}} {{ object.show() }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let a: dyn Show + Count = Text {{ name: \"q\", count: 3 }};
                let mut count = as_count(a);
                count.bump();
                print_i64(count.amount());
                print_i64(count.eat());
                let p: dyn Count + Show = Point {{ x: 7 }};
                print_i64(shown(p));
                let boxed: Box<dyn Show + Count> = Box.new(Point {{ x: 1 }});
                let unboxed: dyn Count = Box.take(boxed);
                print_i64(unboxed.amount());
                let only: dyn Show = Only {{ v: 6 }};
                print_i64(shown(only));
                0
            }}"
        ),
        0,
        "4\n40\n207\n1\n6\n",
    );
}

#[test]
fn multi_trait_objects_work_in_fields_containers_temporaries_and_projections() {
    agrees(
        &format!(
            "{MULTI}
            struct Holder {{ object: dyn Show + Count, tag: i64 }}
            fn make() -> dyn Show + Count ! {{alloc}} {{ Point {{ x: 9 }} }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut holder = Holder {{ object: Text {{ name: \"h\", count: 1 }}, tag: 0 }};
                holder.object.bump();
                print_i64(holder.object.amount() + holder.object.show());
                print_i64(holder.object.eat());
                print_i64(make().show());
                print_i64(make().eat());
                let mut items: Vec<dyn Count + Show> = Vec.new();
                items = Vec.push(items, Point {{ x: 1 }});
                items = Vec.push(items, Text {{ name: \"v\", count: 2 }});
                items = Vec.clear(items);
                0
            }}"
        ),
        0,
        "104\n20\n209\n90\n",
    );
}

#[test]
fn multi_trait_objects_have_explicit_boundaries() {
    for (main, expected) in [
        ("let a: dyn Show + Show = Point { x: 1 }; 0", "listed twice"),
        (
            "let a: dyn Show = Point { x: 1 }; let b: dyn Show + Count = a; 0",
            "subset of its traits",
        ),
        (
            "let a: dyn Show + Count = Point { x: 1 }; let r: &dyn Show = &a; r.show()",
            "type mismatch",
        ),
        (
            "let a: dyn Show + Count = Only { v: 1 }; 0",
            "does not implement trait 'Count'",
        ),
        (
            "let a: dyn Show + Count = Point { x: 1 }; a.tag()",
            "disambiguate",
        ),
        (
            "let a: dyn Show + Count = Point { x: 1 }; a.missing()",
            "declares method 'missing'",
        ),
    ] {
        rejects(&multi(main), expected);
    }
    rejects(
        &format!(
            "{MULTI} fn f(o: dyn Show + 'a) -> i64 ! {{}} {{ 0 }} fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "lifetime bounds",
    );
}

#[test]
fn multi_trait_objects_keep_linear_members_linear_and_bind_projections() {
    let source = r#"
        #[linear]
        struct Ticket { id: i64 }
        trait Look { fn look(self: &Self) -> i64 ! {panic}; }
        trait Done { fn done(self: Self) -> i64 ! {panic}; }
        impl Look for Ticket { fn look(self: &Self) -> i64 ! {panic} { self.id } }
        impl Done for Ticket { fn done(self: Self) -> i64 ! {panic} { let Ticket { id } = self; id } }
    "#;
    agrees(
        &format!(
            "{source}
            fn main() -> i64 ! {{alloc, panic}} {{
                let t: dyn Look + Done = Ticket {{ id: 4 }};
                let seen = t.look();
                seen + t.done()
            }}"
        ),
        8,
        "",
    );
    rejects(
        &format!(
            "{source}
            fn main() -> i64 ! {{alloc, panic}} {{
                let t: dyn Look + Done = Ticket {{ id: 4 }};
                t.look()
            }}"
        ),
        "linear value is not consumed",
    );
    agrees(
        &format!(
            "{CONV}
            trait Show {{ fn show(self: &Self) -> i64 ! {{panic}}; }}
            impl<T> Show for W<T> {{ fn show(self: &Self) -> i64 ! {{panic}} {{ 1 }} }}
            fn read(object: &(dyn Show + Conv<Out = Label>)) -> i64 ! {{alloc, panic}} {{
                let Label {{ text }} = object.conv();
                String.len(&text) + object.show()
            }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let object: dyn Conv + Show = W {{ value: 0 }};
                read(&object)
            }}"
        ),
        5,
        "",
    );
}

#[test]
fn generic_trait_components_are_qualified_with_their_arguments() {
    let stats = agrees(
        r#"
        struct W<T> { value: T }
        trait Into<X> { fn into(self: &Self, x: X) -> i64 ! {panic}; }
        impl<T> Into<i64> for W<T> { fn into(self: &Self, x: i64) -> i64 ! {panic} { x + 1 } }
        impl<T> Into<Bool> for W<T> {
            fn into(self: &Self, x: Bool) -> i64 ! {panic} { if x { 10 } else { 20 } }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let o: dyn Into<i64> + Into<Bool> = W { value: 0 };
            print_i64(o.Into::<i64>.into(4));
            print_i64(o.Into::<Bool>.into(true));
            let a: dyn Into<Bool> = o;
            print_i64(a.into(false));
            0
        }"#,
        0,
        "5\n10\n20\n",
    );
    assert_eq!(stats.allocations, 1);
    rejects(
        r#"
        struct W<T> { value: T }
        trait Into<X> { fn into(self: &Self, x: X) -> i64 ! {panic}; }
        impl<T> Into<i64> for W<T> { fn into(self: &Self, x: i64) -> i64 ! {panic} { x + 1 } }
        impl<T> Into<Bool> for W<T> { fn into(self: &Self, x: Bool) -> i64 ! {panic} { 1 } }
        fn main() -> i64 ! {alloc, panic} {
            let o: dyn Into<i64> + Into<Bool> = W { value: 0 };
            o.into(4)
        }"#,
        "disambiguate",
    );
}
