//! Borrowing and lifetime milestone: explicit and conservatively elided
//! signature lifetimes, checked borrowed returns, last-use loan release, and
//! exclusive mutable slice views.
use kush::executable::{MemoryStats, check};

#[test]
fn early_exits_cannot_abandon_pending_linear_callees_or_arguments() {
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> @[1] = Box.new(40);
            let f: linear once fn(i64) -> i64 ! {panic} =
                fn(n: i64) -> i64 ! {panic} { Box.take(owner) + n };
            f(loop {
                let mut n = 0;
                while n < 2 { n = n + 1; continue; }
                break n;
            })
        }"#,
        42,
        "",
    );
    for exit in ["return 0;", "break 0;", "continue;"] {
        let source = format!(
            "fn main() -> i64 ! {{alloc, panic}} {{
                loop {{
                    let owner: Box<i64> @[1] = Box.new(40);
                    let f: linear once fn(i64) -> i64 ! {{panic}} =
                        fn(n: i64) -> i64 ! {{panic}} {{ Box.take(owner) + n }};
                    let result = f({{ if true {{ {exit} }} 2 }});
                    break result;
                }}
            }}"
        );
        rejects(&source, "pending linear value");
    }
    rejects(
        r#"fn consume(value: Box<i64> @[1], n: i64) -> i64 ! {panic} {
            Box.take(value) + n
        }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> @[1] = Box.new(40);
            consume(owner, { return 0; })
        }"#,
        "pending linear value",
    );
    rejects(
        r#"use std.result.Result;
        fn run() -> Result<i64, i64> ! {alloc, panic} {
            let owner: Box<i64> @[1] = Box.new(40);
            let f: linear once fn(i64) -> i64 ! {panic} =
                fn(n: i64) -> i64 ! {panic} { Box.take(owner) + n };
            let failure: Result<i64, i64> = Err(9);
            Ok(f(failure?))
        }
        fn main() -> Unit ! {alloc, panic} { let _ = run(); }"#,
        "pending linear value",
    );
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> @[1] = Box.new(40);
            let f: linear once fn(i64) -> i64 ! {panic} =
                fn(n: i64) -> i64 ! {panic} { Box.take(owner) + n };
            f(if true { 2 } else { 3 })
        }"#,
        42,
        "",
    );
}

#[test]
fn borrowed_pipeline_retains_split_callees_across_join_argument_suspension() {
    agrees_balanced(
        include_str!("../../../examples/borrowed-pipeline.kush"),
        0,
        "20\n120\n7\n",
    );
    rejects(
        r#"use std.task.TaskExit;
        fn main() -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let mut source = Bytes.from("abc");
                let view = &source[..];
                let read = fn(by: i64) -> i64 ! {panic} { Slice.get(view, 0) + by };
                let child: Task<i64> = Task.spawn(fn() -> i64 ! {suspend} {
                    Task.yield(); 1
                });
                read({
                    let _ = Task.join(child);
                    source = Bytes.from("replacement");
                    0
                });
            });
        }"#,
        "borrows it",
    );
}

#[test]
fn local_borrowed_callees_retain_captures_through_argument_evaluation() {
    for (setup, replacement) in [
        (
            "let mut v: Vec<i64> = Vec.new(); v = Vec.push(v, 5);",
            "v = Vec.push(v, 6);",
        ),
        (
            "let mut v = Bytes.from(\"abc\");",
            "v = Bytes.from(\"replacement\");",
        ),
        ("let mut v: [i64; 2] = [5, 6];", "v = [8, 9];"),
    ] {
        for mutable in ["", "mut "] {
            for mutation in [replacement, "drop(v);"] {
                let source = format!(
                    "fn main() -> i64 ! {{alloc, panic}} {{
                        {setup}
                        let view: &{mutable}[i64] = &{mutable}v[..];
                        let f = fn(n: i64) -> i64 ! {{panic}} {{ Slice.get(view, 0) + n }};
                        f({{ {{ {mutation} }} 0 }})
                    }}"
                );
                assert!(check(&source).is_err(), "{source}");
            }
        }
        for other in ["", "mut "] {
            let source = format!(
                "fn main() -> i64 ! {{alloc, panic}} {{
                    {setup}
                    let view: &mut [i64] = &mut v[..];
                    let f = fn(other: &{other}[i64]) -> i64 ! {{panic}} {{
                        Slice.set(view, 0, 9); Slice.get(other, 0)
                    }};
                    f(&{other}v[..])
                }}"
            );
            assert!(check(&source).is_err(), "{source}");
        }
    }
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [5, 6];
            let view = &mut a[..];
            let f = fn(n: i64) -> i64 ! {panic} {
                Slice.set(view, 0, Slice.get(view, 0) + n);
                Slice.get(view, 0)
            };
            let result = f(1);
            a = [8, 9];
            result + a[0]
        }"#,
        14,
        "",
    );
}

#[test]
fn mutable_views_can_read_their_own_length_in_subview_bounds() {
    agrees(
        r#"fn trim<'a>(v: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut v[0..Slice.len(v)]
        }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut a[..], 2);
            let shared = &left[0..Slice.len(left)];
            let old = Slice.get(shared, 0);
            let child = &mut left[0..Slice.len(left)];
            Slice.set(child, 0, old + 10);
            let other = trim(&mut right[..]);
            Slice.set(other, 0, 20);
            a[0] + a[2]
        }"#,
        31,
        "",
    );
    rejects(
        r#"fn consume(v: &mut [i64]) -> i64 ! {panic} { Slice.len(v) }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let view = &mut a[..];
            let child = &mut view[0..consume(view)];
            Slice.len(child);
        }"#,
        "borrowed",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let view = &mut a[..];
            let child = &mut view[0..{ Slice.set(view, 0, 9); 1 }];
            Slice.len(child);
        }"#,
        "child view derived from it",
    );
}

#[test]
fn borrowed_slice_captures_are_scoped_and_callable() {
    // Immutable view capture: the closure reads the original owner storage.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 5);
            v = Vec.push(v, 7);
            let view: &[i64] = &v[..];
            let sum = fn() -> i64 ! {panic} { Slice.get(view, 0) + Slice.get(view, 1) };
            sum()
        }"#,
        12,
        "",
    );
    // Mutable capture: calling the once closure releases the loan, so the
    // owner can be borrowed again afterwards. Native and reference agree on
    // both the write and the allocation balance.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let view: &mut [i64] = &mut v[..];
            let bump = fn(by: i64) -> Unit ! {panic} {
                Slice.set(view, 0, Slice.get(view, 0) + by);
            };
            bump(41);
            Slice.get(&v[..], 0)
        }"#,
        42,
        "",
    );
    // Byte-buffer views use the same capture rules and write the real buffer.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut b = Bytes.from("ab");
            let view: &mut [i64] = &mut b[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 1, 90); };
            f();
            Bytes.get(&b, 1)
        }"#,
        90,
        "",
    );
    // Split siblings keep opposite-side certificates while their closures are
    // live, so both can mutate without reopening the parent.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut a[..], 2);
            let l = fn() -> Unit ! {panic} { Slice.set(left, 0, Slice.get(left, 0) + 1); };
            let r = fn() -> Unit ! {panic} { Slice.set(right, 0, Slice.get(right, 0) + 10); };
            l();
            r();
            a[0] + a[2]
        }"#,
        15,
        "",
    );
    // A closure may be rebuilt and called on every loop iteration.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [0, 0];
            let mut i = 0;
            while i < 2 {
                let view: &mut [i64] = &mut a[..];
                let f = fn() -> Unit ! {panic} { Slice.set(view, i, Slice.get(view, i) + 1); };
                f();
                i = i + 1;
            }
            a[0] + a[1]
        }"#,
        2,
        "",
    );
    // Branch-local consumption releases the owner on both paths.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn(at: i64) -> Unit ! {panic} { Slice.set(view, at, 9); };
            if true { f(0); } else { f(1); }
            a[0]
        }"#,
        9,
        "",
    );
    // A nested closure captures the outer closure's borrow and parameter.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 2] = [3, 4];
            let s: &[i64] = &a[..];
            let outer = fn(x: i64) -> i64 ! {alloc, panic} {
                let inner = fn(y: i64) -> i64 ! {panic} { Slice.get(s, 0) + x + y };
                inner(1)
            };
            outer(10)
        }"#,
        14,
        "",
    );
    // An immediate callee is a valid scoped construction position, and an
    // exact same-layout `once fn` annotation keeps the same loan tracking.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            let first = (fn() -> i64 ! {panic} { Slice.get(s, 0) + 1 })();
            let g: once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} { Slice.get(s, 1) + 1 };
            first + g()
        }"#,
        5,
        "",
    );
    // A borrowed capture can also target a borrowed parameter; the closure
    // operates on the caller's storage, not a callee snapshot.
    agrees(
        r#"fn write_through(view: &mut [i64], value: i64) -> Unit ! {alloc, panic} {
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, value); };
            f()
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            write_through(&mut a[..], 7);
            a[0]
        }"#,
        7,
        "",
    );
    // Mixed ownership: an uncalled closure releases its affine Box exactly
    // once and never drops the borrowed owner. The call path consumes both.
    agrees(
        r#"fn choose(flag: Bool) -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let n = Box.new(41);
            let f = fn() -> i64 ! {panic} {
                Slice.set(view, 0, 0);
                Box.take(n) + 1
            };
            if flag { return 0; }
            f()
        }
        fn main() -> i64 ! {alloc, panic} { choose(true) + choose(false) }"#,
        42,
        "",
    );
    // An uncalled closure releases only its environment at scope end; the
    // owner remains unchanged and usable.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            {
                let view: &mut [i64] = &mut a[..];
                let unused = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            }
            a[0]
        }"#,
        1,
        "",
    );
    // Capturing a mutable view moves its capability: the old name is gone.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            Slice.len(view)
        }"#,
        "use after move",
    );
    // Early return and `?` release an uncalled closure environment exactly
    // once while never dropping the borrowed owner.
    agrees(
        r#"use std.result.Result;
        fn choose(flag: Bool) -> Result<i64, i64> ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let read = fn() -> Result<i64, i64> ! {panic} {
                Ok(Slice.get(view, 0))
            };
            if flag { return Err(9); }
            let base = read()?;
            Ok(base + 1)
        }
        fn main() -> i64 ! {alloc, panic} {
            let left = match choose(true) { Ok(n) => n, Err(e) => e };
            let right = match choose(false) { Ok(n) => n, Err(e) => e };
            left + right
        }"#,
        11,
        "",
    );
    // A borrowed capture composes with an existing linear capture: the
    // callable remains linear-once and must be consumed by its call.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let n: Box<i64> @[1] = Box.new(40);
            let f: linear once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} {
                    Slice.set(view, 0, 0);
                    Box.take(n) + Slice.get(view, 0) + 2
                };
            f()
        }"#,
        42,
        "",
    );
    // An early return while a later argument evaluates abandons the immediate
    // call: the environment is reclaimed and the borrowed owner is untouched.
    agrees(
        r#"fn partial(flag: Bool) -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            (fn(x: i64) -> i64 ! {panic} {
                Slice.set(view, 0, x);
                Slice.get(view, 0)
            })({ if flag { return 7; } 1 })
        }
        fn main() -> i64 ! {alloc, panic} { partial(true) + partial(false) }"#,
        8,
        "",
    );
    // Shared captures behave like ordinary shared views: the owner may still
    // be read while the closure is live.
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 3);
            v = Vec.push(v, 4);
            let view: &[i64] = &v[..];
            let f = fn() -> i64 ! {panic} { Slice.get(view, 1) };
            let direct = Slice.get(&v[..], 0);
            direct + f()
        }"#,
        7,
        "",
    );
    // But a shared closure still freezes the owner against moves and
    // exclusive borrows.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 3);
            let view: &[i64] = &v[..];
            let f = fn() -> i64 ! {panic} { Slice.get(view, 0) };
            v = Vec.push(v, 4);
            f()
        }"#,
        "borrows it",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &[i64] = &a[..];
            let f = fn() -> i64 ! {panic} { Slice.get(view, 0) };
            let wide: &mut [i64] = &mut a[..];
            f() + Slice.len(wide)
        }"#,
        "exclusive '&mut [T]' view while another view",
    );
    // The loan stays active across a same-task suspension point and is then
    // consumed by the call before the owner is read.
    agrees_balanced(
        r#"fn main() -> i64 ! {io, alloc, panic, suspend} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 1, 9); };
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} { Task.yield(); });
            f();
            a[1]
        }"#,
        9,
        "",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            (fn(x: i64) -> i64 ! {panic} { Slice.set(view, 0, x); Slice.get(view, 0) })(
                { a = [8, 8]; 5 }
            )
        }"#,
        "borrows it",
    );
    agrees_balanced(
        r#"use std.task.TaskExit;
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> i64 ! {panic} { Slice.set(view, 0, 9); Slice.get(view, 0) };
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let child: Task<i64> = Task.spawn(fn() -> i64 ! {panic} { 5 });
                match Task.join(child) {
                    TaskExit.Completed(value) => print_i64(value),
                    TaskExit.Cancelled => print_i64(-1),
                }
            });
            print_i64(f());
            print_i64(a[0]);
        }"#,
        0,
        "5\n9\n9\n",
    );
    // While a borrowing closure is live, its owner and ancestors stay
    // suspended, even though the capture is not an owning move.
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            let observed = a[0];
            f();
            observed
        }"#,
        "exclusive '&mut [T]' view",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let parent: &mut [i64] = &mut a[..];
            let child: &mut [i64] = &mut parent[..];
            let f = fn() -> Unit ! {panic} { Slice.set(child, 0, 9); };
            let n = Slice.len(parent);
            f();
            n
        }"#,
        "child view derived from it",
    );
    // Borrowed captures do not erase through escapes.
    rejects(
        r#"fn make(v: &mut [i64]) -> once fn() -> Unit ! {panic} ! {alloc, panic} {
            let f = fn() -> Unit ! {panic} { Slice.set(v, 0, 1); };
            f
        }
        fn main() -> Unit ! {} {}"#,
        "scoped",
    );
    rejects(
        r#"struct Holder { f: once fn() -> Unit ! {alloc, panic} }
        fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let h = Holder { f: fn() -> Unit ! {panic} { Slice.set(view, 0, 9); } };
        }"#,
        "must be called immediately",
    );
    rejects(
        r#"#[noalloc]
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            f()
        }"#,
        "requires effects {alloc}",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 2] = [1, 2];
            let view: &[i64] = &a[..];
            let u: i64 | once fn() -> i64 ! {panic} =
                fn() -> i64 ! {panic} { Slice.get(view, 0) };
            0
        }"#,
        "union",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let a: [i64; 2] = [1, 2];
            let view: &[i64] = &a[..];
            let wide: once fn(i64) -> i64 ! {panic} =
                fn(x: i64 | Bool) -> i64 ! {panic} { Slice.get(view, 0) };
        }"#,
        "must be called immediately",
    );
    rejects(
        r#"fn apply(f: once fn() -> Unit ! {panic}) -> Unit ! {alloc, panic} { f() }
        fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            apply(f);
        }"#,
        "scoped",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let f = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            let boxed = Box.new(f);
        }"#,
        "scoped",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let mut a: [i64; 2] = [1, 2];
                let view: &mut [i64] = &mut a[..];
                Task.spawn(fn() -> Unit ! {panic} { Slice.set(view, 0, 9); });
            });
        }"#,
        "captured from outside the scope",
    );
}

#[test]
fn borrowed_closure_example_agrees_natively() {
    agrees(
        include_str!("../../../examples/borrowed-closures.kush"),
        0,
        "5\n11\n12\n103\n3\n",
    );
}

#[test]
fn retained_call_arguments_keep_their_owner_borrowed() {
    for (setup, replacement) in [
        (
            "let mut v: Vec<i64> = Vec.new(); v = Vec.push(v, 1);",
            "v = Vec.push(v, 2);",
        ),
        (
            "let mut v = Bytes.from(\"abc\");",
            "v = Bytes.from(\"replacement\");",
        ),
        ("let mut v: [i64; 2] = [1, 2];", "v = [8, 8];"),
    ] {
        for mutable in ["", "mut "] {
            for receiver in ["view", "&mut v[..]"] {
                if mutable.is_empty() && receiver != "view" {
                    continue;
                }
                for indirect in [false, true] {
                    let alias = if indirect { "let call = consume;" } else { "" };
                    let call = if indirect { "call" } else { "consume" };
                    let source = format!(
                        "fn consume(s: &{mutable}[i64], n: i64) -> Unit ! {{panic}} {{ Slice.get(s, 0); }}
                        fn main() -> Unit ! {{alloc, panic}} {{
                            {setup}
                            let view: &{mutable}[i64] = &{mutable}v[..];
                            {alias}
                            {call}({receiver}, {{ {replacement} 0 }});
                        }}"
                    );
                    assert!(check(&source).is_err(), "{source}");
                }
            }
        }
    }
}

#[test]
fn builtin_reborrows_protect_all_later_arguments() {
    for later in [
        "{ v = Vec.push(v, 2); 0 }",
        "{ Slice.set(&mut v[..], 0, 3); 0 }",
    ] {
        let source = format!(
            "fn main() -> Unit ! {{alloc, panic}} {{
                let mut v: Vec<i64> = Vec.new(); v = Vec.push(v, 1);
                let view: &mut [i64] = &mut v[..];
                Slice.set(view, {later}, 9);
            }}"
        );
        assert!(check(&source).is_err(), "{source}");
    }
    let source = "fn main() -> Unit ! {alloc, panic} {
        let mut v = Bytes.from(\"abc\");
        let view: &mut [i64] = &mut v[..];
        Slice.set(view, 0, { v = Bytes.from(\"zzzz\"); 9 });
    }";
    assert!(check(source).is_err());
}

#[test]
fn temporary_views_obey_shared_and_exclusive_alias_rules() {
    for setup in [
        "let mut v: [i64; 2] = [1, 2];",
        "let mut v: Vec<i64> = Vec.new(); v = Vec.push(v, 1);",
        "let mut v = Bytes.from(\"ab\");",
    ] {
        for (left, right) in [("mut ", ""), ("", "mut "), ("mut ", "mut ")] {
            let source = format!(
                "fn both(a: &{left}[i64], b: &{right}[i64]) -> Unit ! {{panic}} {{
                    Slice.get(a, 0); Slice.get(b, 0);
                }}
                fn main() -> Unit ! {{alloc, panic}} {{
                    {setup}
                    both(&{left}v[..], &{right}v[..]);
                }}"
            );
            assert!(check(&source).is_err(), "{source}");
        }
    }
    for body in [
        "let view: &mut [i64] = &mut v[..]; both(view, &v[..]);",
        "both(&mut v[..], { let shared = &v[..]; shared });",
        "read(&v[..], write(&mut v[..]));",
    ] {
        let source = format!(
            "fn both(a: &mut [i64], b: &[i64]) -> Unit ! {{panic}} {{ Slice.set(a, 0, Slice.get(b, 0)); }}
            fn read(a: &[i64], n: i64) -> Unit ! {{panic}} {{ Slice.get(a, 0); }}
            fn write(a: &mut [i64]) -> i64 ! {{panic}} {{ Slice.set(a, 0, 9); 0 }}
            fn main() -> Unit ! {{panic}} {{ let mut v: [i64; 2] = [1, 2]; {body} }}"
        );
        assert!(check(&source).is_err(), "{source}");
    }
}

#[test]
fn call_loans_release_after_calls_and_preserve_disjoint_owners() {
    agrees(
        "fn fill(a: &mut [i64], b: &[i64]) -> Unit ! {panic} {
            Slice.set(a, 0, Slice.get(b, 0));
        }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let b: [i64; 2] = [9, 8];
            fill(&mut a[..], &b[..]);
            a = [4, 5];
            let copied = a;
            fill(&mut a[..], &b[..]);
            a[0] + copied[0]
        }",
        13,
        "",
    );
    agrees(
        "fn update(v: &mut [i64]) -> Unit ! {panic} {
            Slice.set(v, Slice.get(v, 1), Slice.get(v, 0) + 1);
        }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [4, 0];
            update(&mut a[..]);
            a[0]
        }",
        5,
        "",
    );
}

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

/// Compare native execution with the reference evaluator, including the stable
/// allocation diagnostics line, so mutable views cannot hide cleanup leaks.
fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifetimes-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
        let stderr = String::from_utf8(output.stderr).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap_or_else(|| panic!("missing native allocation diagnostics: {stderr:?}"));
        assert_eq!(line, stats.report(), "{source}");
    }
    stats
}

/// Task programs allocate scheduler environments in an implementation-defined
/// way, so compare native/reference status and output and require each backend
/// to balance its own allocations instead of requiring identical counts.
fn agrees_balanced(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifetimes-task-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
        let stderr = String::from_utf8(output.stderr).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap_or_else(|| panic!("missing native allocation diagnostics: {stderr:?}"));
        let field = |name: &str| -> usize {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix(name))
                .and_then(|value| value.strip_prefix('='))
                .and_then(|value| value.parse().ok())
                .unwrap_or_else(|| panic!("missing {name} in {line}"))
        };
        assert_eq!(
            field("allocations"),
            field("deallocations"),
            "native allocation imbalance: {line}"
        );
    }
}

#[test]
fn borrowed_return_helpers_keep_original_storage_and_release_on_last_use() {
    agrees(
        include_str!("../../../examples/lifetimes.kush"),
        0,
        "2\n20\n30\n30\n7\n7\n65\n150\n99\n2\n99\n7\n",
    );
    // A view returned from a helper is still tied to the caller's owner. The
    // owner may move only after the view's checked last use.
    agrees(
        r#"
        fn tail<'a>(s: &'a [i64]) -> &'a [i64] ! {panic} { s[1..] }
        fn sum(s: &[i64]) -> i64 ! {panic} {
            let mut acc = 0;
            let mut i = 0;
            while i < Slice.len(s) { acc = acc + Slice.get(s, i); i = i + 1; }
            acc
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            values = Vec.push(values, 3);
            let rest = tail(&values[..]);
            let value = sum(rest);
            values = Vec.push(values, 4);
            print_i64(value + Vec.len(&values));
        }
        "#,
        0,
        "9\n",
    );
}

#[test]
fn mutable_slice_views_over_arrays_vectors_and_bytes_agree() {
    agrees(
        include_str!("../../../examples/mutable-slices.kush"),
        0,
        "4\n4\n9\n9\n66\n66\n6\n6\n",
    );
    let stats = agrees(
        r#"
        fn fill<'a>(v: &'a mut [i64], x: i64) -> Unit ! {panic} {
            let mut i = 0;
            while i < Slice.len(v) { Slice.set(v, i, x); i = i + 1; }
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut a: [i64; 3] = [0, 0, 0];
            fill(&mut a[..], 5);
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            fill(&mut v[..], 6);
            let mut b = Bytes.from("xy");
            fill(&mut b[..], 67);
            print_i64(a[0] + Vec.get(&v, 0) + Bytes.get(&b, 1));
        }
        "#,
        0,
        "78\n",
    );
    // The byte vector and vector allocate; array views allocate nothing.
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stats.allocations <= 3, "{stats:?}");
}

#[test]
fn mutable_views_are_exclusive_and_shared_upgrades_are_rejected() {
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let shared: &[i64] = &v[..];
            let exclusive: &mut [i64] = &mut v[..];
            Slice.len(shared) + Slice.len(exclusive);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let exclusive: &mut [i64] = &mut v[..];
            v = Vec.push(v, 1);
            Slice.len(exclusive);
        }"#,
        "slice view",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let exclusive: &mut [i64] = &mut v[..];
            let n = Vec.len(&v);
            Slice.len(exclusive) + n;
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let first: &mut [i64] = &mut v[..];
            let second: &mut [i64] = &mut v[..];
            Slice.len(first) + Slice.len(second);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let exclusive: &mut [i64] = &mut v[..];
            let shared: &[i64] = &v[..];
            Slice.len(exclusive) + Slice.len(shared);
        }"#,
        "exclusive",
    );
    // Mutable sub-views and mutable borrowed returns are implemented in the
    // next milestone; positive coverage lives in the returned-subview tests.
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let v: Vec<i64> = Vec.new();
            let exclusive: &mut [i64] = &mut v[..];
            Slice.len(exclusive);
        }"#,
        "let mut",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let shared: &[i64] = &v[..];
            Slice.set(shared, 0, 9);
        }"#,
        "requires an exclusive mutable view",
    );
}

#[test]
fn elided_borrowed_returns_infer_only_unambiguous_input_lifetimes() {
    // A single elided input borrow is the only candidate, so both shared,
    // exclusive, and shared-from-exclusive results are inferred. Nested
    // helper calls, generic element types, and a Nat-generic non-borrowed
    // parameter preserve the same relationship. Native and reference backends
    // agree for inline arrays, Vec, and Bytes.
    let stats = agrees(
        r#"
        #[noalloc]
        #[nosuspend]
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        #[noalloc]
        fn tail_mut(view: &mut [i64]) -> &mut [i64] ! {panic} { &mut view[1..] }
        #[noalloc]
        fn reborrow(view: &mut [i64]) -> &[i64] ! {panic} { &view[1..] }
        #[noalloc]
        fn twice(view: &[i64]) -> &[i64] ! {panic} { tail(tail(view)) }
        #[noalloc]
        fn twice_mut(view: &mut [i64]) -> &mut [i64] ! {panic} {
            tail_mut(tail_mut(view))
        }
        #[noalloc]
        fn choose<'a>(left: &'a [i64], right: &'a [i64], flag: Bool) -> &[i64] ! {panic} {
            if flag { left } else { right }
        }
        #[noalloc]
        fn tail_generic<T>(view: &[T]) -> &[T] ! {panic} { view[1..] }
        #[noalloc]
        fn tail_after<N: Nat>(view: &[i64], padding: [i64; N]) -> &[i64] ! {panic} {
            padding[0];
            view[1..]
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let array: [i64; 4] = [1, 2, 3, 4];
            print_i64(Slice.get(tail(&array[..]), 0));
            print_i64(Slice.get(twice(&array[..]), 0));

            let mut numbers: [i64; 4] = [10, 20, 30, 40];
            let child = tail_mut(&mut numbers[..]);
            let grandchild = tail_mut(&mut child[..]);
            Slice.set(grandchild, 0, 99);
            print_i64(Slice.get(grandchild, 0));
            print_i64(child[0]);
            print_i64(numbers[2]);

            let mut extra: [i64; 4] = [1, 2, 3, 4];
            let far = twice_mut(&mut extra[..]);
            Slice.set(far, 0, 77);
            print_i64(extra[2]);

            let mut bytes = Bytes.from("abcd");
            let read = reborrow(&mut bytes[..]);
            print_i64(Slice.get(read, 0));
            print_i64(Bytes.get(&bytes, 1));

            print_i64(Slice.get(choose(&array[..], &array[..], false), 3));
            print_i64(Slice.get(tail_generic::<i64>(&array[..]), 0));
            print_i64(Slice.get(tail_after::<2>(&array[..], [0, 0]), 0));
        }
        "#,
        0,
        "2\n3\n99\n20\n99\n77\n98\n98\n4\n2\n2\n",
    );
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
}

#[test]
fn borrowed_closures_retain_elided_helper_result_loans() {
    // A scoped borrowed closure captures a view returned by an elided helper.
    // The loan survives until the call, then the owner is usable again.
    let stats = agrees(
        r#"
        #[noalloc]
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 10);
            values = Vec.push(values, 20);
            values = Vec.push(values, 30);
            let view = tail(&values[..]);
            let read = fn() -> i64 ! {panic} { Slice.get(view, 1) };
            let result = read();
            values = Vec.push(values, 40);
            result + Vec.len(&values)
        }
        "#,
        34,
        "",
    );
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    rejects(
        r#"
        #[noalloc]
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        fn main() -> Unit ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 10);
            values = Vec.push(values, 20);
            let view = tail(&values[..]);
            let read = fn() -> i64 ! {panic} { Slice.get(view, 0) };
            values = Vec.push(values, 30);
            Slice.len(view);
        }
        "#,
        "borrows it",
    );
    rejects(
        r#"
        #[noalloc]
        fn tail_mut(view: &mut [i64]) -> &mut [i64] ! {panic} { &mut view[1..] }
        fn main() -> Unit ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 10);
            values = Vec.push(values, 20);
            let view = tail_mut(&mut values[..]);
            let write = fn() -> Unit ! {panic} { Slice.set(view, 0, 9); };
            values = Vec.push(values, 30);
            write();
        }
        "#,
        "borrows it",
    );
}

#[test]
fn elided_result_lifetimes_use_body_origins_and_reject_ambiguity() {
    // Two independent anonymous inputs stay distinct, but a body that returns
    // one directly resolves the result soundly.
    agrees(
        "fn pick(a: &[i64], b: &[i64]) -> &[i64] ! {panic} { a }
         fn main() -> i64 ! {panic} {
            let x: [i64; 2] = [40, 1];
            let y: [i64; 1] = [2];
            Slice.get(pick(&x[..], &y[..]), 0)
         }",
        40,
        "",
    );
    // Two return positions keep both candidates ambiguous. The diagnostic
    // points at every candidate input.
    let error = check(
        "fn bad(a: &[i64], b: &[i64]) -> &[i64] ! {panic} { if true { a } else { b } }
         fn main() -> Unit ! {} {}",
    )
    .unwrap_err();
    assert!(
        error.message.contains("distinct parameter lifetimes"),
        "{error:?}"
    );
    assert_eq!(error.notes.len(), 2, "{error:?}");
    // An unrelated owner-reference input participates in the candidate list,
    // but a body returning only the slice input resolves to that slice.
    check(
        "fn take(owner: &Bytes, view: &[i64]) -> &[i64] ! {panic} { view }
         fn main() -> Unit ! {} {}",
    )
    .unwrap();
    // A borrowed slice result with no borrowed input has no source lifetime.
    rejects(
        "fn bad() -> &[i64] ! {panic} { panic() }
         fn main() -> Unit ! {} {}",
        "no borrowed input",
    );
    // One input is not provenance for a local owner.
    rejects(
        r#"fn bad(view: &[i64]) -> &[i64] ! {panic} {
            let local: [i64; 2] = [1, 2];
            &local[..]
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // An explicit output lifetime is related to the returned input's
    // lifetime by an inferred outlives bound.
    check(
        "fn bad<'a>(view: &[i64]) -> &'a [i64] ! {panic} { view }
         fn main() -> Unit ! {} {}",
    )
    .unwrap();
    check(
        "fn bad<'a, 'b>(view: &'a [i64]) -> &'b [i64] ! {panic} { view }
         fn main() -> Unit ! {} {}",
    )
    .unwrap();
    // A mutable result still requires an exclusive input.
    rejects(
        "fn bad(view: &[i64]) -> &mut [i64] ! {panic} { panic() }
         fn main() -> Unit ! {} {}",
        "exclusive '&mut [T]' parameter",
    );
    // Aliases do not silently supply or erase borrow provenance.
    rejects(
        "type Borrowed = &[i64];
         fn bad(view: Borrowed) -> &[i64] ! {panic} { view }
         fn main() -> Unit ! {} {}",
        "no borrowed input",
    );
    rejects(
        "type Borrowed = &[i64];
         fn bad(view: &[i64]) -> Borrowed ! {panic} { view }
         fn main() -> Unit ! {} {}",
        "cannot be returned without an explicit lifetime",
    );
}

#[test]
fn helper_calls_and_explicit_results_infer_lifetime_bounds() {
    // A body that delegates to a helper follows the helper's result source.
    let stats = agrees(
        r#"
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        fn alias(a: &[i64], b: &[i64]) -> &[i64] ! {panic} { tail(a) }
        fn main() -> i64 ! {io, panic} {
            let x: [i64; 3] = [40, 1, 2];
            let y: [i64; 2] = [7, 8];
            print_i64(Slice.get(alias(&x[..], &y[..]), 0));
            0
        }
        "#,
        0,
        "1\n",
    );
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    // An explicit result lifetime gets the missing outlives bound inferred
    // from the returned source.
    agrees(
        r#"
        fn shorten<'long, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 1];
            Slice.get(shorten(&values[..]), 0)
        }
        "#,
        40,
        "",
    );
    agrees(
        r#"
        fn shorten<'long, 'short>(view: &'long mut [i64]) -> &'short mut [i64] ! {panic} {
            &mut view[..]
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 40];
            Slice.set(shorten(&mut values[..]), 0, 9);
            values[0] * 4 + values[1]
        }
        "#,
        76,
        "",
    );
    // A result lifetime longer than the returned source cannot be inferred.
    rejects(
        r#"fn widen<'long: 'short, 'short>(view: &'short [i64]) -> &'long [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "cannot infer an outlives bound",
    );
    // The helper source follows the argument that supplies it, not merely the
    // first one.
    agrees(
        r#"
        fn tail<'a>(view: &'a [i64]) -> &'a [i64] ! {panic} { view[1..] }
        fn alias(a: &[i64], b: &[i64]) -> &[i64] ! {panic} { tail(b) }
        fn main() -> i64 ! {panic} {
            let x: [i64; 3] = [40, 1, 2];
            let y: [i64; 2] = [7, 8];
            Slice.get(alias(&x[..], &y[..]), 0)
        }
        "#,
        8,
        "",
    );
    rejects(
        r#"
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        fn alias(a: &[i64], b: &[i64]) -> &[i64] ! {panic} {
            if true { tail(a) } else { tail(b) }
        }
        fn main() -> Unit ! {} {}
        "#,
        "distinct parameter lifetimes",
    );
}

#[test]
fn elided_helper_results_keep_split_side_provenance() {
    // The returned view descends from the left split side. Using the opposite
    // sibling stays disjoint; collapsing labels would reject this valid use.
    agrees(
        r#"
        #[noalloc]
        fn tail_mut(view: &mut [i64]) -> &mut [i64] ! {panic} { &mut view[1..] }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let tail = tail_mut(left);
            Slice.set(right, 0, 9);
            Slice.set(tail, 0, 7);
            values[1] * 10 + values[2]
        }
        "#,
        79,
        "",
    );
}

#[test]
fn elided_results_work_across_modules_and_same_task_suspension() {
    let sources = kush::program::Memory(vec![(
        "helper".into(),
        "module helper;
         #[noalloc]
         pub fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }"
            .into(),
    )]);
    let program = kush::program::load(
        "app.kush",
        "module app;
         use helper;
         fn main() -> i64 ! {panic} {
             let values: [i64; 3] = [10, 20, 30];
             Slice.get(helper.tail(&values[..]), 0)
         }",
        &sources,
    )
    .unwrap();
    let checked = kush::executable::check_program(&program).unwrap();
    assert_eq!(checked.evaluate(&mut Vec::new()).unwrap(), 20);
    agrees(
        r#"
        #[noalloc]
        fn tail(view: &[i64]) -> &[i64] ! {panic} { view[1..] }
        fn main() -> Unit ! {io, panic, suspend} {
            let values: [i64; 4] = [10, 20, 30, 40];
            let rest = tail(&values[..]);
            let cancelled = Task.yield();
            print_i64(Slice.get(rest, 0));
            print_i64(if cancelled { 0 } else { Slice.len(rest) });
        }
        "#,
        0,
        "20\n3\n",
    );
}

#[test]
fn borrowed_returns_reject_dangling_storage_and_unrelated_lifetimes() {
    rejects(
        r#"fn f<'a>(v: &'a [i64]) -> &'a [i64] ! {panic} {
            let local: [i64; 2] = [1, 2];
            &local[..]
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    rejects(
        r#"fn f<'a>(v: &'a [i64]) -> &'a [i64] ! {panic} {
            if Slice.len(v) > 0 { return &v[..]; }
            let local: [i64; 2] = [1, 2];
            &local[..]
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // An explicit result lifetime that the body never directly names is
    // related to the returned source by an inferred outlives bound.
    check(
        r#"fn f<'a, 'b>(x: &'a [i64]) -> &'b [i64] ! {} { x }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    check(
        r#"fn f<'a, 'b>(x: &'a [i64], y: &'b [i64]) -> &'a [i64] ! {} { y }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    // Unused lifetimes are rejected as relationships that cannot be satisfied,
    // while the declared lifetime must still be syntactically present.
    rejects(
        r#"fn f(v: &'c [i64]) -> &'c [i64] ! {} { v }
        fn main() -> Unit ! {} {}"#,
        "undeclared lifetime",
    );
}

#[test]
fn lifetime_erasure_through_generics_unions_and_closures_stays_rejected() {
    rejects(
        r#"fn id<T>(value: T) -> T ! {} { value }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            Slice.len(id(s))
        }"#,
        "cannot infer",
    );
    rejects(
        r#"enum E<T> { A(T) }
        fn f(e: E<&[i64]>) -> Unit ! {} {}
        fn main() -> Unit ! {} {}"#,
        "cannot store borrowed",
    );
    rejects(
        r#"fn id<T>(value: T) -> T ! {} { value }
        fn main() -> i64 ! {alloc, panic} {
            let a: [i64; 2] = [1, 2];
            let s: &[i64] = &a[..];
            let read = fn() -> i64 ! {panic} { Slice.len(s) };
            let escaped = id(read);
            0
        }"#,
        "scoped",
    );
    rejects(
        r#"struct Holder { view: &mut [i64] }
        fn main() -> Unit ! {} {}"#,
        "records cannot store borrowed",
    );
    rejects(
        r#"enum E { A(&mut [i64]) }
        fn main() -> Unit ! {} {}"#,
        "enums cannot store borrowed",
    );
}

#[test]
fn loans_across_branches_loops_breaks_calls_and_suspension_are_checked() {
    // A view used on a later loop iteration is live across the owner move.
    rejects(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let s: &[i64] = &v[..];
            let mut i = 0;
            while i < 2 { print_i64(Slice.len(s)); v = Vec.push(v, 2); i = i + 1; }
        }"#,
        "slice view",
    );
    // A view that is not used after the loop no longer loans the owner.
    agrees(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let s: &[i64] = &v[..];
            let mut i = 0;
            while i < 3 { i = i + Slice.len(s); }
            v = Vec.push(v, 2);
            print_i64(Vec.len(&v));
        }"#,
        0,
        "2\n",
    );
    // Branch-created views join their loans; a move on one path is rejected.
    rejects(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let s: &[i64] = if true { &v[..] } else { &v[..] };
            if true { v = Vec.push(v, 2); }
            print_i64(Slice.len(s));
        }"#,
        "slice view",
    );
    // Short-circuit right operands are still under the loan if the view is
    // used afterwards, and early returns cannot release it unsafely.
    rejects(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let s: &[i64] = &v[..];
            true && { v = Vec.push(v, 2); true };
            print_i64(Slice.len(s));
        }"#,
        "slice view",
    );
    rejects(
        r#"fn f<'a>(s: &'a [i64], stop: Bool) -> &'a [i64] ! {} {
            if stop { return s; }
            let local: [i64; 2] = [1, 2];
            &local[..]
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // Views and borrowed returns survive a same-task suspension point.
    let (status, output, _) = run(
        r#"fn tail<'a>(s: &'a [i64]) -> &'a [i64] ! {panic} { s[1..] }
        fn main() -> Unit ! {io, panic, suspend} {
            let a: [i64; 4] = [10, 20, 30, 40];
            let rest = tail(&a[..]);
            let cancelled = Task.yield();
            print_i64(Slice.get(rest, 0));
            print_i64(if cancelled { 0 } else { Slice.len(rest) });
        }"#,
    );
    assert_eq!(status, 0);
    assert_eq!(output, "20\n3\n");
}

#[test]
fn aliases_cannot_launder_a_loan_after_the_owner_moves() {
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let first: &[i64] = &v[..];
            let second = first;
            v = Vec.push(v, 2);
            Slice.len(second);
        }"#,
        "slice view",
    );
    // Releasing one alias while another is still live keeps the owner loaned.
    agrees(
        r#"fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let first: &[i64] = &v[..];
            let second = first;
            let n = Slice.len(first);
            let m = Slice.len(second);
            v = Vec.push(v, 2);
            print_i64(n + m + Vec.len(&v));
        }"#,
        0,
        "4\n",
    );
}

#[test]
fn views_survive_task_join_and_views_do_not_allocate() {
    let (status, output, _) = run(r#"use std.task.TaskExit;
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            let a: [i64; 3] = [4, 5, 6];
            let view: &[i64] = &a[..];
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let t: Task<i64> = Task.spawn(fn() -> i64 ! {panic} { 7 });
                match Task.join(t) {
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }
            });
            print_i64(Slice.get(view, 2));
        }"#);
    assert_eq!(status, 0);
    assert_eq!(output, "7\n6\n");
    let (_, _, stats) = run(
        r#"fn tail<'a>(s: &'a [i64]) -> &'a [i64] ! {panic} { s[1..] }
        fn main() -> i64 ! {panic} {
            let a: [i64; 4] = [1, 2, 3, 4];
            let rest = tail(&a[..]);
            rest[0] + rest[2]
        }"#,
    );
    assert_eq!(stats.allocations, 0, "{stats:?}");
    assert_eq!(stats.deallocations, 0, "{stats:?}");
}

#[test]
fn mutable_borrowed_returns_and_nested_reborrow_chains_agree() {
    agrees(
        r#"
        fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut s[1..]
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            values = Vec.push(values, 3);
            values = Vec.push(values, 4);
            let child = tail_mut(&mut values[..]);
            let grand = tail_mut(&mut child[..]);
            Slice.set(grand, 0, 90);
            print_i64(Slice.get(grand, 0));
            print_i64(Slice.get(child, 1));
            Slice.set(child, 0, 70);
            print_i64(Slice.get(child, 0));
            values = Vec.push(values, 5);
            print_i64(Vec.get(&values, 1));
            print_i64(Vec.get(&values, 2));
            print_i64(Vec.len(&values));
        }
        "#,
        0,
        "90\n90\n70\n70\n90\n5\n",
    );
    // Array, vector, and byte-buffer children alias the original backing
    // storage, including the byte write/read rule for Bytes.
    agrees(
        r#"
        fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut s[1..]
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut array: [i64; 4] = [1, 2, 3, 4];
            let head = &mut array[1..];
            Slice.set(head, 0, 20);
            print_i64(Slice.get(head, 0));
            print_i64(array[1]);

            let mut vector: Vec<i64> = Vec.new();
            vector = Vec.push(vector, 5);
            vector = Vec.push(vector, 6);
            let tail = tail_mut(&mut vector[..]);
            Slice.set(tail, 0, 60);
            print_i64(Slice.get(tail, 0));
            print_i64(Vec.get(&vector, 1));

            let mut bytes = Bytes.from("abcd");
            let back = &mut bytes[2..];
            Slice.set(back, 0, 70);
            print_i64(Slice.get(back, 0));
            print_i64(Bytes.get(&bytes, 2));
        }
        "#,
        0,
        "20\n20\n60\n60\n70\n70\n",
    );
    // Views themselves allocate no program storage, even when returned and
    // nested through several helpers.
    let stats = agrees(
        r#"
        fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut s[1..]
        }
        fn main() -> i64 ! {panic} {
            let mut array: [i64; 5] = [1, 2, 3, 4, 5];
            let a = tail_mut(&mut array[..]);
            let b = tail_mut(&mut a[..]);
            Slice.set(b, 0, 9);
            let result = Slice.get(b, 0);
            result + array[3]
        }
        "#,
        13,
        "",
    );
    assert_eq!(stats.allocations, 0, "{stats:?}");
    assert_eq!(stats.deallocations, 0, "{stats:?}");
}

#[test]
fn mutable_views_release_parents_after_branches_loops_breaks_and_early_returns() {
    agrees(
        r#"
        fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut s[1..]
        }
        fn pick_mut<'a>(
            a: &'a mut [i64],
            b: &'a mut [i64],
            flag: Bool,
        ) -> &'a mut [i64] ! {panic} {
            if flag { a } else { b }
        }
        fn ret_mut<'a>(s: &'a mut [i64], stop: Bool) -> &'a mut [i64] ! {panic} {
            if stop { return &mut s[..]; }
            &mut s[1..]
        }
        fn main() -> Unit ! {io, panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let mut b: [i64; 3] = [4, 5, 6];
            let chosen = pick_mut(&mut a[..], &mut b[..], true);
            Slice.set(chosen, 0, 10);
            print_i64(Slice.get(chosen, 0));
            a = [7, 8, 9];
            print_i64(a[0]);

            let mut i = 0;
            while i < 3 {
                let cell = &mut a[i..(i + 1)];
                Slice.set(cell, 0, Slice.get(cell, 0) + 1);
                i = i + 1;
            }
            print_i64(a[0]);
            print_i64(a[2]);

            let mut j = 0;
            loop {
                let child = tail_mut(&mut a[..]);
                Slice.set(child, 0, j + 20);
                if j == 1 { break; }
                j = j + 1;
                continue;
            }
            print_i64(a[1]);
            print_i64(a[2]);

            let early = ret_mut(&mut a[..], true);
            Slice.set(early, 0, 8);
            print_i64(Slice.get(early, 0));
            print_i64(a[0]);
        }
        "#,
        0,
        "10\n7\n8\n10\n21\n10\n8\n8\n",
    );
}

#[test]
fn mutable_views_survive_same_task_yields_and_joins() {
    agrees_balanced(
        r#"
        use std.task.TaskExit;
        #[noalloc]
        fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut s[1..]
        }
        #[nosuspend]
        fn narrowed<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            tail_mut(s)
        }
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            let mut array: [i64; 3] = [1, 2, 3];
            let child = narrowed(&mut array[..]);
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(fn() -> i64 ! {panic} { 7 });
                match Task.join(task) {
                    TaskExit.Completed(value) => print_i64(value),
                    TaskExit.Cancelled => print_i64(-1),
                }
            });
            let cancelled = Task.yield();
            Slice.set(child, 0, 9);
            print_i64(Slice.get(child, 0));
            print_i64(array[1]);
            if cancelled { print_i64(-2); }
        }
        "#,
        0,
        "7\n9\n9\n",
    );
}

#[test]
fn shared_reborrows_coexist_and_temporarily_freeze_the_owner() {
    agrees(
        r#"fn update(parent: &mut [i64]) -> i64 ! {panic} {
            let child = &parent[..];
            let old = Slice.get(child, 0);
            Slice.set(parent, 0, old + 1);
            Slice.get(parent, 0)
        }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [4, 5];
            update(&mut a[..])
        }"#,
        5,
        "",
    );
    agrees(
        r#"
        fn main() -> Unit ! {io, panic} {
            let mut array: [i64; 4] = [1, 2, 3, 4];
            let first: &[i64] = &array[..];
            let second: &[i64] = &array[..];
            print_i64(Slice.get(first, 0) + Slice.get(second, 1));
            array = [5, 6, 7, 8];
            print_i64(array[0]);
        }
        "#,
        0,
        "3\n5\n",
    );
    // Multiple shared children of an exclusive parent coexist and suspend the
    // parent until both children are dead.
    agrees(
        r#"
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            let parent: &mut [i64] = &mut v[..];
            let first: &[i64] = &parent[..];
            let second: &[i64] = &parent[..];
            print_i64(Slice.get(first, 0) + Slice.get(second, 1));
            Slice.set(parent, 0, 5);
            print_i64(Slice.get(parent, 0));
        }
        "#,
        0,
        "3\n5\n",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            let first: &[i64] = &v[..];
            let second: &mut [i64] = &mut v[..];
            Slice.len(first) + Slice.len(second);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let parent: &mut [i64] = &mut v[..];
            let shared: &[i64] = &parent[..];
            Slice.set(parent, 0, 9);
            Slice.len(shared);
        }"#,
        "child view derived from it",
    );
}

#[test]
fn mutable_child_views_are_ancestry_checked_not_root_flattened() {
    // Parameters are capabilities too: a shared child freezes a mutable
    // parameter just as it freezes a mutable view bound inside the function.
    rejects(
        r#"fn invalid(parent: &mut [i64]) -> Unit ! {panic} {
            let child = &parent[..];
            Slice.set(parent, 0, 9);
            Slice.get(child, 0);
        }
        fn main() -> Unit ! {} {}"#,
        "child view derived from it",
    );
    // Using a suspended parent is rejected.
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            let parent: &mut [i64] = &mut v[..];
            let child = &mut parent[1..];
            Slice.set(parent, 0, 9);
            Slice.len(child);
        }"#,
        "child view derived from it",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let parent: &mut [i64] = &mut v[..];
            let child = &mut parent[1..];
            Slice.len(parent);
            Slice.len(child);
        }"#,
        "child view derived from it",
    );
    // Competing siblings and disjoint ranges remain conservative.
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            let parent: &mut [i64] = &mut v[..];
            let child = &mut parent[1..];
            let rival = &mut parent[..1];
            Slice.len(child) + Slice.len(rival);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let left = &mut a[0..1];
            let right = &mut a[1..2];
            Slice.len(left) + Slice.len(right);
        }"#,
        "split siblings",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let child = &mut a[1..];
            a = [4, 5, 6];
            Slice.len(child);
        }"#,
        "slice view or reference borrows it",
    );
    rejects(
        r#"fn consume(s: &mut [i64]) -> Unit ! {panic} { Slice.len(s); }
        fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            let parent: &mut [i64] = &mut v[..];
            let child = &mut parent[1..];
            consume(parent);
            Slice.len(child);
        }"#,
        "borrowed",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            let child = &mut v[1..];
            drop(v);
            Slice.len(child);
        }"#,
        "move or drop",
    );
    // A returned child cannot outlive its owner or a local block.
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let view = {
                let mut local: [i64; 2] = [1, 2];
                &mut local[..]
            };
            Slice.len(view);
        }"#,
        "outlive",
    );
    rejects(
        r#"fn bad<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            let mut local: [i64; 2] = [1, 2];
            &mut local[..]
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    check(
        r#"fn bad<'a, 'b>(s: &'a mut [i64]) -> &'b mut [i64] ! {} { s }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    rejects(
        r#"fn bad<'a, 'b>(
            a: &'a mut [i64],
            b: &'b mut [i64],
        ) -> &'a mut [i64] ! {panic} {
            let child = &mut b[1..];
            child
        }
        fn main() -> Unit ! {} {}"#,
        "not a slice parameter with the declared result lifetime",
    );
    // Mutable views stay move-only: there is no implicit alias duplication.
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let child = &mut a[1..];
            let alias = child;
            Slice.set(alias, 0, 2);
            Slice.set(child, 0, 3);
        }"#,
        "use after move",
    );
    // Ordinary passing consumes the mutable view; retaining the original
    // requires an explicit '&mut parent[..]' reborrow.
    rejects(
        r#"fn consume(s: &mut [i64]) -> Unit ! {panic} { Slice.len(s); }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let parent: &mut [i64] = &mut a[..];
            consume(parent);
            Slice.len(parent);
        }"#,
        "use after move",
    );
    // A sub-view reserves its parent while its bounds evaluate, so a nested
    // rival view cannot be derived from the same capability there.
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let parent = &mut a[..];
            let child = &mut parent[0..{
                let rival = &mut parent[0..1];
                Slice.len(rival)
            }];
            Slice.len(child);
        }"#,
        "retained by this expression",
    );
}

#[test]
fn mutable_borrow_aliases_cannot_launder_through_calls_generics_data_closures_or_tasks() {
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let shared: &[i64] = &v[..];
            let upgraded: &mut [i64] = &mut shared[..];
            Slice.set(upgraded, 0, 2);
        }"#,
        "cannot be upgraded",
    );
    rejects(
        r#"fn bad<'a>(s: &'a [i64]) -> &'a mut [i64] ! {} { s }
        fn main() -> Unit ! {} {}"#,
        "exclusive '&mut [T]' parameter",
    );
    rejects(
        r#"fn id<T>(value: T) -> T ! {} { value }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            Slice.len(id(view))
        }"#,
        "cannot infer",
    );
    rejects(
        r#"struct Holder { view: &mut [i64] }
        fn main() -> Unit ! {} {}"#,
        "records cannot store borrowed",
    );
    rejects(
        r#"enum E { A(&mut [i64]) }
        fn main() -> Unit ! {} {}"#,
        "enums cannot store borrowed",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            let read = fn() -> i64 ! {panic} { Slice.len(view) };
            let alias = read;
            alias();
        }"#,
        "scoped",
    );
    rejects(
        r#"use std.task.TaskExit;
        fn main() -> Unit ! {alloc, panic, suspend} {
            let mut a: [i64; 2] = [1, 2];
            let view: &mut [i64] = &mut a[..];
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let (left, right) = Slice.split_at_mut(view, 1);
                Task.spawn(fn() -> Unit ! {panic} { Slice.set(left, 0, 9); });
                Slice.set(view, 0, 7);
            });
        }"#,
        "lent to a spawned task",
    );
    // A later argument cannot replace storage retained by an earlier returned
    // child or by a nested builtin receiver.
    rejects(
        r#"fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} { &mut s[1..] }
        fn consume(s: &mut [i64], n: i64) -> Unit ! {panic} { Slice.len(s); }
        fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            v = Vec.push(v, 2);
            consume(tail_mut(&mut v[..]), { v = Vec.push(v, 3); 0 });
        }"#,
        "borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut v: Vec<i64> = Vec.new();
            v = Vec.push(v, 1);
            let parent: &mut [i64] = &mut v[..];
            Slice.set(parent, { v = Vec.push(v, 2); 0 }, 9);
        }"#,
        "borrows it",
    );
}

#[test]
fn returned_mutable_subviews_check_runtime_bounds() {
    for body in [
        r#"let mut a: [i64; 1] = [1]; let bad = tail_mut(&mut a[..]); Slice.len(bad);"#,
        r#"let mut b = Bytes.from("a"); let bad = tail_mut(&mut b[..]); Slice.len(bad);"#,
    ] {
        let source = format!(
            "fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {{panic}} {{ &mut s[2..] }}
            fn main() -> Unit ! {{alloc, panic}} {{ {body} }}"
        );
        let program = check(&source).unwrap();
        let error = program.evaluate(&mut Vec::new()).unwrap_err();
        assert!(error.message.contains("panic:"), "{error:?}");
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        {
            let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
            let binary = scratch.path().join("lifetimes-bounds");
            kush::native::build(&program, &binary).unwrap();
            let output = std::process::Command::new(&binary).output().unwrap();
            assert!(!output.status.success(), "{source}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("panic:"),
                "{source}"
            );
        }
    }
}

#[test]
fn view_locals_are_single_assignment() {
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let mut b: [i64; 2] = [3, 4];
            let mut view: &mut [i64] = &mut a[..];
            view = &mut b[..];
            Slice.set(view, 0, 5);
        }"#,
        "cannot be reassigned",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let mut b: [i64; 2] = [3, 4];
            let flag = true;
            let mut view: &mut [i64] = &mut a[..];
            if flag { view = &mut b[..]; }
            Slice.set(view, 0, 5);
        }"#,
        "cannot be reassigned",
    );
}

#[test]
fn checked_mutable_splits_allow_disjoint_siblings() {
    let stats = agrees(
        r#"
        fn bump(left: &mut [i64], right: &mut [i64]) -> Unit ! {panic} {
            Slice.set(left, 0, Slice.get(left, 0) + 1);
            Slice.set(right, 0, Slice.get(right, 0) + 10);
        }
        #[noalloc]
        fn fill<'a>(view: &'a mut [i64]) -> Unit ! {panic} {
            let (left, right) = Slice.split_at_mut(view, 2);
            bump(left, right);
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut array: [i64; 4] = [1, 2, 3, 4];
            let parent = &mut array[..];
            let (left, right) = Slice.split_at_mut(parent, 2);
            Slice.set(left, 0, 10);
            Slice.set(right, 0, 20);
            bump(&mut left[..], &mut right[..]);
            print_i64(Slice.get(left, 0));
            print_i64(Slice.get(right, 0));
            print_i64(Slice.get(parent, 1));
            print_i64(array[0]);
            print_i64(array[2]);
            array = [7, 8, 9, 10];
            print_i64(array[0]);
            fill(&mut array[..]);
            print_i64(array[0]);
            print_i64(array[2]);
        }
        "#,
        0,
        "11\n30\n2\n11\n30\n7\n8\n19\n",
    );
    assert_eq!(stats.allocations, 0, "{stats:?}");
    assert_eq!(stats.deallocations, 0, "{stats:?}");
}

#[test]
fn mutable_splits_alias_arrays_vectors_and_bytes_at_their_real_edges() {
    agrees(
        r#"
        fn main() -> Unit ! {io, alloc, panic} {
            let mut array: [i64; 3] = [1, 2, 3];
            let (empty, all) = Slice.split_at_mut(&mut array[..], 0);
            print_i64(Slice.len(empty));
            print_i64(Slice.len(all));
            Slice.set(all, 0, 9);
            print_i64(array[0]);
            let (all2, empty2) = Slice.split_at_mut(&mut array[..], 3);
            print_i64(Slice.len(all2));
            print_i64(Slice.len(empty2));

            let mut vector: Vec<i64> = Vec.new();
            vector = Vec.push(vector, 4);
            vector = Vec.push(vector, 5);
            vector = Vec.push(vector, 6);
            let (first, rest) = Slice.split_at_mut(&mut vector[..], 1);
            Slice.set(first, 0, 40);
            Slice.set(rest, 0, 50);
            print_i64(Vec.get(&vector, 0));
            print_i64(Vec.get(&vector, 1));

            let mut bytes = Bytes.from("abcd");
            let (head, tail) = Slice.split_at_mut(&mut bytes[..], 2);
            Slice.set(head, 1, 66);
            Slice.set(tail, 0, 67);
            print_i64(Bytes.get(&bytes, 1));
            print_i64(Bytes.get(&bytes, 2));

            let mut flags: [Bool; 2] = [true, false];
            let (left, right) = Slice.split_at_mut(&mut flags[..], 1);
            Slice.set(left, 0, false);
            Slice.set(right, 0, true);
            if flags[0] { print_i64(0); } else { print_i64(1); }
            if flags[1] { print_i64(1); } else { print_i64(0); }
        }
        "#,
        0,
        "0\n3\n9\n3\n0\n40\n50\n66\n67\n1\n1\n",
    );
    agrees(
        r#"
        struct Cell { a: i64, b: i64 }
        fn main() -> Unit ! {io, panic} {
            let mut cells: [Cell; 3] = [
                Cell { a: 1, b: 2 },
                Cell { a: 3, b: 4 },
                Cell { a: 5, b: 6 },
            ];
            let (left, right) = Slice.split_at_mut(&mut cells[..], 1);
            Slice.set(left, 0, Cell { a: 10, b: 20 });
            let right_cell = right[0];
            print_i64(right_cell.a);
            print_i64(right_cell.b);
            let left_cell = left[0];
            print_i64(left_cell.a);
            print_i64(left_cell.b);
            print_i64(cells[0].a);
        }
        "#,
        0,
        "3\n4\n10\n20\n10\n",
    );
    agrees(
        r#"
        fn main() -> Unit ! {io, panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let child = &mut left[0..Slice.len(right)];
            Slice.set(child, 0, 9);
            Slice.set(right, 0, 8);
            print_i64(values[0]);
            print_i64(values[1]);
            print_i64(values[2]);
        }
        "#,
        0,
        "9\n2\n8\n",
    );
}

#[test]
fn mutable_split_siblings_release_the_parent_only_after_both_last_uses() {
    agrees(
        r#"
        fn tail<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            &mut view[1..]
        }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut array: [i64; 6] = [1, 2, 3, 4, 5, 6];
            let parent = &mut array[..];
            let (left, right) = Slice.split_at_mut(parent, 3);
            let left_tail = tail(left);
            Slice.set(left_tail, 0, 20);
            Slice.set(right, 0, 40);
            print_i64(Slice.get(left_tail, 0));
            print_i64(Slice.get(right, 0));
            print_i64(Slice.get(parent, 0));
            array = [0, 0, 0, 0, 0, 0];
            print_i64(array[0]);
        }
        "#,
        0,
        "20\n40\n1\n0\n",
    );
    agrees(
        r#"
        fn main() -> Unit ! {io, alloc, panic} {
            let mut array: [i64; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
            let (left, right) = Slice.split_at_mut(&mut array[..], 4);
            let (ll, lr) = Slice.split_at_mut(left, 2);
            let (rl, rr) = Slice.split_at_mut(right, 1);
            Slice.set(ll, 0, 11);
            Slice.set(lr, 0, 22);
            Slice.set(rl, 0, 33);
            Slice.set(rr, 0, 44);
            Slice.set(lr, 1, 23);
            print_i64(array[0]);
            print_i64(array[2]);
            print_i64(array[4]);
            print_i64(array[5]);
            print_i64(array[3]);
        }
        "#,
        0,
        "11\n22\n33\n44\n23\n",
    );
    agrees(
        r#"
        fn choose<'a>(a: &'a mut [i64], b: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            Slice.len(b);
            a
        }
        fn main() -> Unit ! {io, panic} {
            let mut array: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut array[..], 2);
            let chosen = choose(&mut left[..], &mut right[..]);
            Slice.set(chosen, 0, 9);
            Slice.set(left, 1, 8);
            Slice.set(right, 0, 7);
            print_i64(array[0]);
            print_i64(array[1]);
            print_i64(array[2]);
        }
        "#,
        0,
        "9\n8\n7\n",
    );
    agrees(
        r#"
        fn main() -> Unit ! {io, panic} {
            let mut array: [i64; 4] = [1, 2, 3, 4];
            let parent = &mut array[..];
            let (left, right) = Slice.split_at_mut(&mut parent[..], 2);
            Slice.set(left, 0, 10);
            Slice.set(right, 0, 30);
            print_i64(Slice.get(parent, 1));
            print_i64(array[0]);
            print_i64(array[2]);
        }
        "#,
        0,
        "2\n10\n30\n",
    );
}

#[test]
fn split_children_can_be_returned_only_through_matching_parameter_lifetimes() {
    let stats = agrees(
        r#"
        #[noalloc]
        fn first_half<'a>(view: &'a mut [i64], mid: i64) -> &'a mut [i64] ! {panic} {
            let (left, right) = Slice.split_at_mut(view, mid);
            Slice.set(right, 0, Slice.get(right, 0) + 1);
            left
        }
        fn main() -> Unit ! {io, panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let half = first_half(&mut values[..], 2);
            Slice.set(half, 0, 9);
            print_i64(values[0]);
            print_i64(values[2]);
        }
        "#,
        0,
        "9\n4\n",
    );
    assert_eq!(stats.allocations, 0, "{stats:?}");
    agrees(
        r#"
        #[noalloc]
        fn right_half<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            let (left, right) = Slice.split_at_mut(view, 1);
            Slice.set(left, 0, Slice.get(left, 0) + 1);
            right
        }
        fn main() -> Unit ! {io, panic} {
            let mut values: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let chosen = right_half(left);
            Slice.set(chosen, 0, 9);
            Slice.set(right, 0, 8);
            print_i64(values[0]);
            print_i64(values[1]);
            print_i64(values[2]);
        }
        "#,
        0,
        "2\n9\n8\n",
    );
    agrees(
        r#"
        #[noalloc]
        fn shared<'a>(view: &'a mut [i64]) -> &'a [i64] ! {panic} {
            &view[..]
        }
        fn main() -> Unit ! {io, panic} {
            let mut values: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut values[..], 2);
            let read = shared(left);
            Slice.set(right, 0, 30);
            print_i64(Slice.get(read, 0));
            print_i64(Slice.get(read, 1));
            print_i64(Slice.get(right, 0));
        }
        "#,
        0,
        "1\n2\n30\n",
    );
    // The result is returned through a local destructuring binding rather
    // than directly from the parameter, so the body-origin inference cannot
    // relate it to `'a`; the explicit-bound requirement still applies.
    rejects(
        r#"fn bad<'a, 'b>(view: &'a mut [i64]) -> &'b mut [i64] ! {panic} {
            let (left, right) = Slice.split_at_mut(view, 1);
            Slice.len(right);
            left
        }
        fn main() -> Unit ! {} {}"#,
        "does not appear on any parameter",
    );
    rejects(
        r#"fn bad<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            let mut local: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut local[..], 1);
            Slice.len(right);
            left
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
}

#[test]
fn mutable_split_example_agrees_and_does_not_allocate() {
    let stats = agrees(
        include_str!("../../../examples/mutable-splits.kush"),
        0,
        "11\n30\n40\n30\n40\n50\n",
    );
    assert_eq!(stats.allocations, 0, "{stats:?}");
    assert_eq!(stats.deallocations, 0, "{stats:?}");
}

#[test]
fn mutable_split_midpoints_are_checked_and_side_effects_run_once() {
    for source in [
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let (l, r) = Slice.split_at_mut(&mut a[..], 3);
            Slice.set(l, 0, 9);
            Slice.len(r);
        }"#,
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let (l, r) = Slice.split_at_mut(&mut a[..], -1);
            Slice.len(l) + Slice.len(r);
        }"#,
    ] {
        let program = check(source).unwrap();
        let error = program.evaluate(&mut Vec::new()).unwrap_err();
        assert!(error.message.contains("panic:"), "{error:?}");
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        {
            let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
            let binary = scratch.path().join("lifetimes-split-bounds");
            kush::native::build(&program, &binary).unwrap();
            let output = std::process::Command::new(&binary).output().unwrap();
            assert!(!output.status.success(), "{source}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("panic:"),
                "{source}"
            );
        }
    }
    agrees(
        r#"
        fn midpoint(x: i64) -> i64 ! {io, panic} {
            print_i64(x);
            x + 1
        }
        fn main() -> Unit ! {io, panic} {
            let mut a: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut a[..], midpoint(1));
            Slice.set(left, 0, 8);
            Slice.set(right, 0, Slice.get(right, 0) + 5);
            print_i64(left[1]);
            print_i64(right[0]);
        }
        "#,
        0,
        "1\n2\n8\n",
    );
}

#[test]
fn mutable_split_siblings_remain_disjoint_through_calls_reborrows_and_suspension() {
    agrees_balanced(
        r#"
        use std.task.TaskExit;
        fn write_both(a: &mut [i64], b: &mut [i64], value: i64) -> Unit ! {panic} {
            Slice.set(a, 0, value);
            Slice.set(b, 0, value + 1);
        }
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            let mut array: [i64; 4] = [0, 1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut array[..], 2);
            write_both(&mut left[..], &mut right[..], 9);
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let task: Task<i64> = Task.spawn(fn() -> i64 ! {panic} { 7 });
                match Task.join(task) {
                    TaskExit.Completed(value) => print_i64(value),
                    TaskExit.Cancelled => print_i64(-1),
                }
            });
            let cancelled = Task.yield();
            Slice.set(left, 1, Slice.get(right, 1) + 10);
            print_i64(array[0]);
            print_i64(array[2]);
            print_i64(array[3]);
            if cancelled { print_i64(-2); }
        }
        "#,
        0,
        "7\n9\n10\n3\n",
    );
    agrees_balanced(
        r#"
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let mut local: [i64; 2] = [1, 2];
                let (left, right) = Slice.split_at_mut(&mut local[..], 1);
                Slice.set(left, 0, 3);
                Slice.set(right, 0, 4);
                let cancelled = Task.yield();
                print_i64(local[0]);
                print_i64(local[1]);
                if cancelled { print_i64(-1); }
            });
        }
        "#,
        0,
        "3\n4\n",
    );
}

#[test]
fn mutable_split_survives_loop_and_branch_last_use_joins() {
    agrees(
        r#"
        fn main() -> Unit ! {io, panic} {
            let mut array: [i64; 6] = [0, 0, 0, 0, 0, 0];
            let mut i = 0;
            while i < 3 {
                let (left, right) = Slice.split_at_mut(&mut array[..], 3);
                Slice.set(left, i, i + 1);
                Slice.set(right, i, i + 10);
                i = i + 1;
            }
            if true {
                let (left, right) = Slice.split_at_mut(&mut array[..], 2);
                Slice.set(left, 1, 40);
                Slice.set(right, 2, 50);
            } else {
                let (left, right) = Slice.split_at_mut(&mut array[..], 1);
                Slice.set(left, 0, 60);
                Slice.set(right, 0, 70);
            }
            let mut j = 0;
            while j < 6 { print_i64(array[j]); j = j + 1; }
        }
        "#,
        0,
        "1\n40\n3\n10\n50\n12\n",
    );
    agrees(
        r#"
        fn main() -> Unit ! {io, panic} {
            let mut array: [i64; 4] = [0, 0, 0, 0];
            let mut i = 0;
            loop {
                let (left, right) = Slice.split_at_mut(&mut array[..], 2);
                Slice.set(left, 0, i + 1);
                Slice.set(right, 0, i + 10);
                if i == 1 { break; }
                i = i + 1;
                continue;
            }
            print_i64(array[0]);
            print_i64(array[2]);
        }
        "#,
        0,
        "2\n11\n",
    );
}

#[test]
fn mutable_split_rejections_are_specific_and_conservative() {
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let left = &mut a[0..1];
            let right = &mut a[1..2];
            Slice.len(left) + Slice.len(right);
        }"#,
        "split siblings",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let pair = Slice.split_at_mut(&mut a[..], 1);
            Slice.len(pair);
        }"#,
        "nonescaping borrow pair",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let view: &[i64] = &a[..];
            let (left, right) = Slice.split_at_mut(view, 1);
            Slice.len(left) + Slice.len(right);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            a = [4, 5, 6];
            Slice.len(left) + Slice.len(right);
        }"#,
        "slice view or reference borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            let rival = &mut a[2..];
            Slice.len(left) + Slice.len(right) + Slice.len(rival);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            Slice.set(left, 0, 9);
            Slice.len(right);
            let shared = &a[..];
            Slice.len(left) + Slice.len(right) + Slice.len(shared);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            let (left2, right2) = Slice.split_at_mut(left, 1);
            Slice.set(left, 0, 9);
            Slice.len(right);
            Slice.len(left2) + Slice.len(right2);
        }"#,
        "child view derived from it",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let parent = &mut a[..];
            let (left, right) = Slice.split_at_mut(parent, 1);
            let moved = right;
            Slice.set(moved, 0, 9);
            Slice.set(right, 0, 8);
            Slice.len(left);
        }"#,
        "use after move",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            let rival = &mut left[..];
            let crossing = &mut right[..];
            Slice.len(left) + Slice.len(rival) + Slice.len(crossing) + Slice.len(right);
        }"#,
        "child view derived from it",
    );
    // A helper result whose declared lifetime can flow from both siblings is
    // conservatively tied to both, so using either parent while it lives fails.
    rejects(
        r#"fn choose<'a>(a: &'a mut [i64], b: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
            Slice.len(b);
            a
        }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 4] = [1, 2, 3, 4];
            let (left, right) = Slice.split_at_mut(&mut a[..], 2);
            let chosen = choose(&mut left[..], &mut right[..]);
            Slice.set(left, 1, 8);
            Slice.set(chosen, 0, 9);
            Slice.len(right);
        }"#,
        "child view derived from it",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let parent = &mut a[..];
            let (left, right) = Slice.split_at_mut(parent, 2);
            Slice.len(left);
            Slice.len(parent);
            Slice.len(right);
        }"#,
        "child view derived from it",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 4] = [1, 2, 3, 4];
            let parent = &mut a[..];
            let (left, right) = Slice.split_at_mut(parent, 2);
            let (second_left, second_right) = Slice.split_at_mut(parent, 2);
            Slice.len(left) + Slice.len(right);
            Slice.len(second_left) + Slice.len(second_right);
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let parent = &mut a[..];
            let (left, right) = Slice.split_at_mut(&mut parent[..], 1);
            Slice.len(parent);
            Slice.len(left) + Slice.len(right);
        }"#,
        "child view derived from it",
    );
    rejects(
        r#"fn consume(view: &mut [i64], n: i64) -> Unit ! {panic} { Slice.len(view); }
        fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            consume(left, { a = [4, 5, 6]; 0 });
            Slice.len(right);
        }"#,
        "borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            Slice.set(left, { a = [4, 5, 6]; 0 }, Slice.get(right, 0));
        }"#,
        "borrows it",
    );
    rejects(
        r#"fn main() -> Unit ! {alloc, panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            let read = fn() -> i64 ! {panic} { Slice.len(left) };
            let alias = read;
            alias() + Slice.len(right);
        }"#,
        "scoped",
    );
    rejects(
        r#"fn bad(view: &mut [Box<i64>]) -> Unit ! {panic} {
            let (left, right) = Slice.split_at_mut(view, 0);
            Slice.len(left) + Slice.len(right);
        }
        fn main() -> Unit ! {} {}"#,
        "owning or linear elements",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let mut (left, right) = Slice.split_at_mut(&mut a[..], 1);
            Slice.len(left) + Slice.len(right);
        }"#,
        "let mut",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, _) = Slice.split_at_mut(&mut a[..], 1);
            Slice.len(left);
        }"#,
        "exactly two simple local names",
    );
    rejects(
        r#"fn main() -> Unit ! {panic} {
            let mut a: [i64; 3] = [1, 2, 3];
            let (left, right): (&mut [i64], &mut [i64]) = Slice.split_at_mut(&mut a[..], 1);
            Slice.len(left) + Slice.len(right);
        }"#,
        "omit the binding annotation",
    );
}

// Explicit outlives bounds: `<'long: 'short, 'short>` declares that storage
// named by `'long` outlives storage named by `'short`. A borrowed result may
// name the shorter lifetime, but callers must still establish the relation and
// the returned provenance keeps every source owner borrowed.

#[test]
fn explicit_outlives_bounds_shorten_shared_mutable_and_transitive_views() {
    agrees(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn shorten_mut<'long: 'short, 'short>(view: &'long mut [i64]) -> &'short mut [i64] ! {panic} { view }
        fn transit<'long: 'middle, 'middle: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn relay<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} {
            shorten(view)
        }
        fn main() -> Unit ! {io, panic} {
            let mut values: [i64; 4] = [10, 20, 30, 40];
            let short = shorten(&values[..]);
            print_i64(Slice.get(short, 1));
            let deep = transit(&values[..]);
            print_i64(Slice.get(deep, 2));
            let relayed = relay(&values[..]);
            print_i64(Slice.get(relayed, 0));
            let mut numbers: [i64; 3] = [1, 2, 3];
            let writable = shorten_mut(&mut numbers[..]);
            Slice.set(writable, 0, 7);
            print_i64(numbers[0]);
        }"#,
        0,
        "20\n30\n10\n7\n",
    );
}

#[test]
fn outlives_bounds_instantiate_borrowed_record_returns_and_keep_owners() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn make<'long: 'short, 'short>(view: &'long [i64]) -> Window<'short> ! {} {
            Window { view: view, start: 1 }
        }
        fn narrow<'long: 'short, 'short>(window: Window<'long>) -> Window<'short> ! {} { window }
        fn first<'a>(window: Window<'a>) -> &'a [i64] ! {} {
            let Window { view, .. } = window;
            view
        }
        fn read<'long: 'short, 'short>(window: Window<'long>) -> i64 ! {panic} {
            let narrowed = narrow(window);
            let Window { view, start } = narrowed;
            Slice.get(view, 0) + start
        }
        fn main() -> Unit ! {io, panic} {
            let values: [i64; 3] = [4, 5, 6];
            let window = make(&values[..]);
            print_i64(Slice.get(first(window), 0));
            let direct = Window { view: &values[..], start: 2 };
            print_i64(read(direct));
        }"#,
        0,
        "4\n6\n",
    );
}

#[test]
fn call_sites_must_establish_declared_outlives_constraints() {
    agrees(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.get(long, 0) + Slice.get(short, 0)
        }
        fn caller<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            pair(long, short)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 0];
            caller(&a[..], &a[..])
        }"#,
        80,
        "",
    );
    // The same storage satisfies the constraint reflexively.
    agrees(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.get(long, 0) + Slice.get(short, 1)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 2];
            pair(&a[..], &a[..])
        }"#,
        42,
        "",
    );
    // The caller's declared relation points the other way.
    rejects(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.len(long) + Slice.len(short)
        }
        fn caller<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            pair(short, long)
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot establish",
    );
    // A local owner cannot outlive a caller parameter, and two distinct local
    // owners cannot establish a non-reflexive relation.
    rejects(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.len(long) + Slice.len(short)
        }
        fn caller<'short>(short: &'short [i64]) -> i64 ! {panic} {
            let local: [i64; 2] = [1, 2];
            pair(&local[..], short)
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot establish",
    );
    rejects(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.len(long) + Slice.len(short)
        }
        fn main() -> i64 ! {panic} {
            let first: [i64; 2] = [1, 2];
            let second: [i64; 2] = [3, 4];
            pair(&first[..], &second[..])
        }"#,
        "cannot establish",
    );
}

#[test]
fn caller_lifetimes_outlive_frame_owned_locals_only() {
    // A caller parameter's storage outlives every local owned by this frame.
    agrees(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.get(long, 0) + Slice.get(short, 1)
        }
        fn caller<'p>(outer: &'p [i64]) -> i64 ! {panic} {
            let local: [i64; 2] = [0, 2];
            pair(outer, &local[..])
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 1] = [40];
            caller(&a[..])
        }"#,
        42,
        "",
    );
    // A shortened result that mixes caller and local storage stays local.
    rejects(
        r#"fn keep<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> &'short [i64] ! {panic} {
            short
        }
        fn caller<'p>(outer: &'p [i64]) -> &'p [i64] ! {panic} {
            let local: [i64; 2] = [0, 2];
            keep(outer, &local[..])
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "outlive",
    );
    // A view merged from two caller parameters is not frame-owned storage.
    rejects(
        r#"fn pair<'long: 'short, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            Slice.len(long) + Slice.len(short)
        }
        fn caller<'a, 'b>(a: &'a [i64], b: &'b [i64], flag: Bool) -> i64 ! {panic} {
            let merged = if flag { a } else { b };
            pair(a, merged)
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot establish",
    );
}

#[test]
fn outlives_bounds_reject_wrong_way_shortening_and_mutability_upgrades() {
    rejects(
        r#"fn widen<'long: 'short, 'short>(view: &'short [i64]) -> &'long [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "cannot infer an outlives bound",
    );
    rejects(
        r#"fn widen_mut<'long: 'short, 'short>(view: &'short mut [i64]) -> &'long mut [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "cannot infer an outlives bound",
    );
    rejects(
        r#"fn upgrade<'long: 'short, 'short>(view: &'long [i64]) -> &'short mut [i64] ! {panic} { panic() }
        fn main() -> Unit ! {} {}"#,
        "exclusive '&mut [T]' result lifetime",
    );
    rejects(
        r#"struct Window<'a> { view: &'a mut [i64] }
        fn upgrade<'long: 'short, 'short>(view: &'long [i64]) -> Window<'short> ! {panic} { panic() }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
}

#[test]
fn outlives_binders_are_resolved_and_cycles_are_rejected() {
    // A self bound is satisfied by reflexivity.
    agrees(
        r#"fn same<'a: 'a>(view: &'a [i64]) -> &'a [i64] ! {panic} { view }
        fn main() -> Unit ! {io, panic} {
            let a: [i64; 1] = [5];
            print_i64(Slice.get(same(&a[..]), 0));
        }"#,
        0,
        "5\n",
    );
    rejects(
        r#"fn f<'a: 'missing>(view: &'a [i64]) -> &'a [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "outlives bound refers to undeclared lifetime",
    );
    rejects(
        r#"fn f<'a: 'b + 'b, 'b>(view: &'a [i64]) -> &'b [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "duplicate outlives bound",
    );
    rejects(
        r#"fn f<'a: 'b, 'b: 'a>(view: &'a [i64]) -> &'b [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "cyclic outlives bounds",
    );
    rejects(
        r#"fn f<'a, 'a>(view: &'a [i64]) -> &'a [i64] ! {panic} { view }
        fn main() -> Unit ! {} {}"#,
        "duplicate lifetime parameter",
    );
    rejects(
        r#"struct W<'a: 'b, 'b> { first: &'a [i64], second: &'b [i64] }
        fn main() -> Unit ! {} {}"#,
        "only supported on executable function signatures",
    );
    rejects(
        r#"type Pair<'a: 'b, 'b> = &'a [i64];
        fn main() -> Unit ! {} {}"#,
        "only supported on executable function signatures",
    );
}

#[test]
fn shortened_results_keep_every_source_owner_borrowed_and_cannot_escape() {
    rejects(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let view = shorten(&values[..]);
            let first = Slice.get(view, 0);
            values = [9, 9];
            first + Slice.get(view, 1)
        }"#,
        "replace",
    );
    agrees(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let view = shorten(&values[..]);
            let first = Slice.get(view, 0);
            values = [9, 9];
            first + values[1]
        }"#,
        10,
        "",
    );
    rejects(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn bad<'a>(input: &'a [i64]) -> &'a [i64] ! {panic} {
            let local: [i64; 2] = [1, 2];
            shorten(&local[..])
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    rejects(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn read(view: &[i64], n: i64) -> i64 ! {panic} { Slice.len(view) + n }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [1, 2];
            let view = shorten(&values[..]);
            read(view, { values = [3, 4]; 0 })
        }"#,
        "borrows it",
    );
    rejects(
        r#"fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} { view }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [1, 2];
            let view = shorten(&values[..]);
            drop(values);
            Slice.get(view, 0)
        }"#,
        "move or drop",
    );
}

#[test]
fn outlives_bounds_stay_directional_for_borrowed_record_fields() {
    rejects(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn bad<'long: 'short, 'short>(first: &'long [i64], second: &'short [i64]) -> Two<'short, 'long> ! {} {
            Two { first: first, second: second }
        }
        fn main() -> Unit ! {} {}"#,
        "must be borrowed",
    );
    agrees(
        r#"struct Two<'a, 'b> { first: &'a [i64], second: &'b [i64] }
        fn good<'long: 'short, 'short>(first: &'long [i64], second: &'short [i64]) -> Two<'long, 'short> ! {} {
            Two { first: first, second: second }
        }
        fn read<'long: 'short, 'short>(two: Two<'long, 'short>) -> i64 ! {panic} {
            let Two { first, second } = two;
            Slice.get(first, 0) + Slice.get(second, 1)
        }
        fn relay<'long: 'short, 'short>(a: &'long [i64], b: &'short [i64]) -> i64 ! {panic} {
            read(good(a, b))
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 2];
            relay(&a[..], &a[..])
        }"#,
        42,
        "",
    );
}

#[test]
fn result_lifetime_claims_the_shortest_provable_source() {
    agrees(
        r#"fn pick<'a>(left: &'a [i64], right: &'a [i64], flag: Bool) -> &'a [i64] ! {panic} {
            if flag { left } else { right }
        }
        fn narrow<'long: 'short, 'short>(left: &'long [i64], right: &'short [i64], flag: Bool) -> &'short [i64] ! {panic} {
            pick(left, right, flag)
        }
        fn relay<'long: 'short, 'short>(left: &'long [i64], right: &'short [i64], flag: Bool) -> &'short [i64] ! {panic} {
            narrow(left, right, flag)
        }
        fn main() -> Unit ! {io, panic} {
            let a: [i64; 2] = [1, 2];
            print_i64(Slice.get(relay(&a[..], &a[..], false), 0));
        }"#,
        0,
        "1\n",
    );
    rejects(
        r#"fn pick<'a>(left: &'a [i64], right: &'a [i64], flag: Bool) -> &'a [i64] ! {panic} {
            if flag { left } else { right }
        }
        fn widen<'long: 'short, 'short>(left: &'long [i64], right: &'short [i64], flag: Bool) -> &'long [i64] ! {panic} {
            pick(left, right, flag)
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
}

#[test]
fn lifetime_bounds_example_agrees_natively() {
    agrees(
        include_str!("../../../examples/lifetime-bounds.kush"),
        0,
        "20\n30\n10\n40\n30\n7\n",
    );
}
