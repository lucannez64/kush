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
