//! Limits lifted while building the Game Boy example: contextual `total` and
//! `handle`, loop invariants, facts kept across blocks and branch joins,
//! scalar cells shared by closures, `Option<&T>` parameters, length-refined
//! parameters, and the scoping of closures that capture references. Programs
//! run on the reference evaluator and natively with balanced allocations.

use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}\n{source}"
    );
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> (usize, usize) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("language-limits-test");
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
    program.bounds_report()
}

fn panics(source: &str, expected_output: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let error = program.evaluate(&mut output).unwrap_err();
    assert!(error.message.contains("panic"), "{error:?}");
    assert_eq!(String::from_utf8(output).unwrap(), expected_output);
}

#[test]
fn total_and_handle_are_contextual_keywords() {
    agrees(
        r#"
        effect Op: i64 -> i64;
        struct Win { handle: i64, total: i64 }
        total fn same(x: Bool) -> Bool ! {} { x }
        fn core() -> i64 ! {Op, panic} { perform Op(1) }
        fn main() -> i64 ! {io, panic} {
            let handle = 3;
            let total = Win { handle: handle, total: 4 };
            let round = 2;
            let r = handle Op: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {} { resume(x) } { core() };
            print_i64(total.handle + total.total + round + r);
            0
        }"#,
        0,
        "10\n",
    );
}

#[test]
fn loop_invariants_are_proved_and_then_assumed() {
    agrees(
        r#"
        fn count(n: i64) -> i64 ! {panic} ensures { 0 <= result && result <= 10 } {
            let mut c = 0;
            let mut i = 0;
            while i < n && c < 10 invariant { 0 <= c && c <= 10 } {
                if i % 3 == 0 { c = c + 1; }
                i = i + 1;
            }
            c
        }
        fn exact() -> i64 ! {panic} ensures { result == 10 } {
            let mut i = 0;
            while i < 10 invariant { i <= 10 } { i = i + 1; }
            i
        }
        fn main() -> i64 ! {panic} { count(50) + exact() }"#,
        20,
        "",
    );
    rejects(
        "fn f() -> i64 ! {panic} {
            let mut i = 0;
            while i < 10 invariant { i <= 5 } { i = i + 1; }
            i
        }",
        "the loop invariant at the end of the body",
    );
    rejects(
        "fn f(n: i64) -> i64 ! {panic} {
            let mut i = 0;
            while i < n invariant { i <= 10 } { if i == 3 { i = 20; continue; } i = i + 1; }
            i
        }",
        "the loop invariant at this 'continue'",
    );
    rejects(
        "fn f(n: i64) -> i64 ! {panic} {
            let mut i = 11;
            while i < n invariant { i <= 10 } { i = i + 1; }
            i
        }",
        "the loop invariant on entry",
    );
    // With a break the loop may leave early: nothing about the exit holds.
    rejects(
        "fn f(n: i64) -> i64 ! {panic} ensures { result >= 10 } {
            let mut i = 0;
            while i < 10 invariant { i <= 10 } { if i == n { break; } i = i + 1; }
            i
        }",
        "cannot prove",
    );
}

#[test]
fn a_branch_join_keeps_what_each_path_knew() {
    agrees(
        r#"
        fn pick(flag: Bool, x: i64) -> i64 ! {panic} ensures { 1 <= result && result <= 2 } {
            let mut y = 0;
            if flag { y = 1; } else { y = 2; }
            if x > 100 { y = y + 0; }
            y
        }
        fn main() -> i64 ! {panic} { pick(true, 5) + pick(false, 500) }"#,
        3,
        "",
    );
}

#[test]
fn closures_share_scalar_cells() {
    agrees(
        r#"
        effect A: i64 -> i64 ! {panic};
        effect B: i64 -> i64 ! {panic};
        fn core() -> i64 ! {A, B, panic} { perform A(1) + perform B(2) + perform A(3) }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut shared = 0;
            let mut steps = 0;
            let inc = fn(x: i64) -> i64 ! {panic} { steps = steps + x; steps };
            let dbl = fn(x: i64) -> i64 ! {panic} { steps = steps * x; steps };
            print_i64(inc(2) + dbl(3));
            let r = handle A: i64 -> i64 with fn(
                x: i64,
                resume: linear once fn(i64) -> i64 ! {},
            ) -> i64 ! {panic} { shared = shared + x; resume(shared) } {
                handle B: i64 -> i64 with fn(
                    x: i64,
                    resume: linear once fn(i64) -> i64 ! {},
                ) -> i64 ! {panic} { shared = shared * 10 + x; resume(shared) } { core() }
            };
            print_i64(shared);
            print_i64(steps);
            r
        }"#,
        28,
        "8\n15\n6\n",
    );
    // The owner still cannot touch the cell while a closure holding it lives.
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut x = 0;
            let k = fn(v: i64) -> i64 ! {panic} { x = x + v; x };
            x = 5;
            k(1)
        }",
        "while a closure capturing it is live",
    );
}

#[test]
fn optional_references_can_be_parameters() {
    agrees(
        r#"
        use std.option.Option;
        struct Dev { n: i64 }
        fn read(d: Option<&Dev>, x: i64) -> i64 ! {panic} {
            match d { Option.Some(dev) => dev.n + x, Option.None => x }
        }
        fn bump(d: Option<&mut Dev>) -> i64 ! {panic} {
            match d { Option.Some(dev) => { dev.n = dev.n + 1; dev.n }, Option.None => 0 }
        }
        fn main() -> i64 ! {io, panic} {
            let mut dev = Dev { n: 40 };
            print_i64(read(Option.Some(&dev), 2));
            print_i64(read(Option.None, 2));
            print_i64(bump(Option.Some(&mut dev)) + bump(Option.None));
            dev.n
        }"#,
        41,
        "42\n2\n41\n",
    );
    rejects(
        r#"
        use std.option.Option;
        struct Dev { n: i64 }
        fn leak<'a>(d: Option<&'a Dev>, other: &'a Dev) -> &'a Dev ! {panic} {
            match d { Option.Some(dev) => dev, Option.None => other }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "returned reference would dangle",
    );
    rejects(
        r#"
        use std.option.Option;
        struct Dev { n: i64 }
        fn two(d: Option<&mut Dev>, e: &mut Dev) -> i64 ! {panic} { e.n }
        fn main() -> i64 ! {panic} {
            let mut dev = Dev { n: 40 };
            two(Option.Some(&mut dev), &mut dev)
        }"#,
        "",
    );
}

const REFINED: &str = r#"
    struct M { io: Vec<u8> where len >= 8, other: Vec<u8> }
    fn zeroed(n: i64) -> Vec<u8> ! {alloc, panic} {
        let mut v: Vec<u8> = Vec.with_capacity(n);
        let mut i = 0;
        while i < n { v = v.push(0); i = i + 1; }
        v
    }
"#;

#[test]
fn length_refined_parameters_are_proved_or_checked_at_the_call() {
    let source = format!(
        "{REFINED}
        fn poke(io: &mut Vec<u8> where len >= 8, at: i64, value: u8) -> Unit ! {{alloc, panic}} {{
            io[3] = value;
            if at >= 0 && at < 8 {{ io[at] = value; }}
            io.push(1);
            inner(io);
        }}
        fn inner(io: &mut Vec<u8> where len >= 4) -> Unit ! {{panic}} {{ io[2] = 9; }}
        fn peek(io: &Vec<u8> where len >= 8) -> u8 ! {{panic}} {{ io[7] }}
        fn main() -> i64 ! {{io, alloc, panic}} {{
            let mut m = M {{ io: zeroed(8), other: zeroed(9) }};
            poke(&mut m.io, 5, 4);
            poke(&mut m.other, 6, 2);
            print_i64(Int.convert(peek(&m.io)) + Int.convert(m.io[5]) + Int.convert(m.io[2]));
            print_i64(Int.convert(m.other[6]));
            0
        }}"
    );
    let (proved, _) = agrees(&source, 0, "13\n2\n");
    assert!(proved >= 6, "{proved}");
    panics(
        &format!(
            "{REFINED}
            fn poke(io: &mut Vec<u8> where len >= 8) -> Unit ! {{panic}} {{ io[7] = 1; }}
            fn main() -> i64 ! {{io, alloc, panic}} {{
                let mut short = zeroed(3);
                print_i64(1);
                poke(&mut short);
                0
            }}"
        ),
        "1\n",
    );
}

#[test]
fn a_length_refined_parameter_cannot_be_shortened() {
    let cases = [
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { io.clear(); }",
            "clearing it would break that",
        ),
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { Vec.clear(io); }",
            "clearing it would break that",
        ),
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { let o = io; o.clear(); }",
            "keeps 'len >= N'",
        ),
        (
            "fn g(v: &mut Vec<u8>) -> Unit ! {alloc, panic} { v.clear(); }
             fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { g(io); }",
            "keeps 'len >= N'",
        ),
        (
            "fn g(v: &mut Vec<u8>) -> Unit ! {alloc, panic} { v.clear(); }
             fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { g(&mut *io); }",
            "keeps 'len >= N'",
        ),
        (
            "fn f<'a>(io: &'a mut Vec<u8> where len >= 8) -> &'a mut Vec<u8> ! {alloc, panic} { io }",
            "keeps 'len >= N'",
        ),
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} {
                 let k = fn() -> Unit ! {alloc, panic} { io.clear(); };
                 k();
             }",
            "cannot capture a parameter that keeps",
        ),
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { }
             fn main() -> i64 ! {alloc, panic} { let h = f; 0 }",
            "can only be called directly",
        ),
        (
            "fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {alloc, panic} { let t = (io, 1); }",
            "keeps 'len >= N'",
        ),
    ];
    for (body, fragment) in cases {
        rejects(&format!("{REFINED}\n{body}"), fragment);
    }
    // Replacing the vector checks the new one's length.
    panics(
        &format!(
            "{REFINED}
            fn f(io: &mut Vec<u8> where len >= 8) -> Unit ! {{alloc, panic}} {{
                let e: Vec<u8> = Vec.new();
                let old = io.replace(e);
            }}
            fn main() -> i64 ! {{io, alloc, panic}} {{ let mut v = zeroed(8); print_i64(1); f(&mut v); 0 }}"
        ),
        "1\n",
    );
}

#[test]
fn closures_capturing_references_stay_scoped() {
    let cases = [
        // Two closures cannot both hold one exclusive reference.
        (
            "struct D { n: i64 }
             fn main() -> i64 ! {alloc, panic} {
                 let mut d = D { n: 1 };
                 let r = &mut d;
                 let a = fn() -> i64 ! {} { r.n = 5; 0 };
                 let b = fn() -> i64 ! {} { r.n = 7; 0 };
                 a() + b() + d.n
             }",
            "while another view of the same owner is live",
        ),
        (
            "struct D { n: i64 }
             fn main() -> i64 ! {alloc, panic} {
                 let mut d = D { n: 1 };
                 let r = &mut d;
                 let a = fn() -> i64 ! {} { r.n = 5; 0 };
                 r.n = 3;
                 a() + d.n
             }",
            "cannot write through a reference",
        ),
        (
            "struct D { n: i64 }
             fn main() -> i64 ! {alloc, panic} {
                 let k = { let x = D { n: 2 }; let r = &x; fn() -> i64 ! {} { r.n } };
                 k()
             }",
            "must be called immediately or bound directly to a local",
        ),
        (
            "struct D { n: i64 }
             fn main() -> i64 ! {alloc, panic} {
                 let mut x = D { n: 2 };
                 let r = &x;
                 let k = fn() -> i64 ! {} { r.n };
                 x = D { n: 9 };
                 k()
             }",
            "cannot replace an owner",
        ),
        (
            "struct D { n: i64 }
             fn call(f: once fn() -> i64 ! {}) -> i64 ! {} { f() }
             fn main() -> i64 ! {alloc, panic} {
                 let x = D { n: 2 };
                 let r = &x;
                 let k = fn() -> i64 ! {} { r.n };
                 call(k)
             }",
            "is scoped",
        ),
        (
            "fn main() -> i64 ! {alloc, panic} {
                 let mut v: Vec<i64> = Vec.new();
                 v = v.push(1);
                 let r = &v;
                 let k = fn() -> i64 ! {} { Vec.len(r) };
                 v.push(2);
                 k()
             }",
            "cannot move an owner while it is borrowed",
        ),
        (
            "struct D { n: i64 }
             fn main() -> i64 ! {alloc, panic} {
                 let mut d = D { n: 1 };
                 let r = &mut d;
                 let a = fn() -> i64 ! {} { r.n = 5; 0 };
                 let s = &d;
                 a() + s.n
             }",
            "while an exclusive",
        ),
    ];
    for (source, fragment) in cases {
        rejects(source, fragment);
    }
    // A capture moved inside its closure ends the loan at the call.
    agrees(
        "struct D { n: i64 }
         fn main() -> i64 ! {alloc, panic} {
             let mut d = D { n: 1 };
             let r = &mut d;
             let a = fn() -> i64 ! {} { let q = r; q.n = 2; 0 };
             a() + d.n
         }",
        2,
        "",
    );
}
