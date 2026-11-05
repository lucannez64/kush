//! Runtime-length array extensions: `[T; n <= C]` in generic functions, impl
//! methods, and trait items; binders nested inside signature types; and
//! exclusive borrowed `DynArray` patterns.
//!
//! Each feature has positive, rejection, cleanup (balanced allocations), and
//! reference-evaluator/native parity tests.

use kush::executable::{MemoryStats, check};

fn evaluate(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
    (result, stats)
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

/// The reference evaluator returns `expected` with balanced allocations, and
/// the native build exits with the same status.
fn agrees(source: &str, expected: i64) -> MemoryStats {
    let (reference, stats) = evaluate(source);
    assert_eq!(reference, expected, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("runtime-length-extensions");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
    }
    stats
}

// ---------------------------------------------------------------------------
// Generic functions, methods, and trait items
// ---------------------------------------------------------------------------

#[test]
fn generic_functions_take_and_return_runtime_length_arrays() {
    // `T` is inferred from the element, the capacity from an explicit `Nat`
    // argument, and the binder is replaced by the caller's on both sides.
    agrees(
        r#"
        fn first<T>(n: i64, a: [T; n <= 8], erased ok: { 0 < n && n <= 8 }) -> T ! {} {
            a[0]
        }
        fn make<C: Nat>(n: i64) -> [i64; n <= C] ! {panic} { Array.fill(n, 3) }
        fn count<T, C: Nat>(n: i64, a: &[T; n <= C]) -> i64 ! {} { DynArray.len(a) }
        fn main() -> i64 ! {panic} {
            let k: i64 = 3;
            let b: [i64; k <= 8] = make::<8>(k);
            let c: [i64; k <= 4] = make::<4>(k);
            first(k, b, _) * 10 + count(k, &c)
        }"#,
        33,
    );
    // A generic element that owns resources is dropped exactly once.
    let stats = agrees(
        r#"
        fn keep<T>(n: i64, a: [T; n <= 4]) -> [T; n <= 4] ! {} { a }
        fn main() -> i64 ! {panic, alloc} {
            let k: i64 = 2;
            let a: [Box<i64>; k <= 4] = [Box.new(20), Box.new(22)];
            let b: [Box<i64>; k <= 4] = keep(k, a);
            match &b {
                [x, y] => Box.read(x) + Box.read(y),
                _ => 0,
            }
        }"#,
        42,
    );
    assert_eq!(stats.allocations, 2);
}

#[test]
fn impl_methods_and_trait_items_substitute_the_callers_binder() {
    agrees(
        r#"
        trait Summer {
            fn sum_up(self: &Self, n: i64, a: &[i64; n <= 8]) -> i64 ! {panic};
        }
        struct Base { v: i64 }
        impl Summer for Base {
            fn sum_up(self: &Self, n: i64, a: &[i64; n <= 8]) -> i64 ! {panic} {
                let mut i = 0;
                let mut acc = self.v;
                while i < n { acc = acc + a[i]; i = i + 1; }
                acc
            }
        }
        impl Base {
            fn make(self: &Base, n: i64) -> [i64; n <= 8] ! {panic} { Array.fill(n, self.v) }
        }
        struct W<T> { x: T }
        impl<T> W<T> {
            fn pick<U>(self: &Self, n: i64, a: &[U; n <= 4], erased ok: { 0 < n && n <= 4 }) -> U ! {} {
                a[0]
            }
        }
        fn twice<T: Summer>(x: T, k: i64, b: &[i64; k <= 8]) -> i64 ! {panic} {
            x.sum_up(k, b) * 2
        }
        fn main() -> i64 ! {panic} {
            let k: i64 = 3;
            let h = Base { v: 1 };
            let b: [i64; k <= 8] = h.make(k);
            let j: i64 = 2;
            let a: [i64; j <= 4] = [10, 20];
            let w = W { x: true };
            // (1 + 3) + 2 * (1 + 3) + 10
            h.sum_up(k, &b) + twice(h, k, &b) + w.pick(j, &a, _)
        }"#,
        22,
    );
}

#[test]
fn generic_and_method_calls_reject_mismatched_binders() {
    let base = r#"
        struct Base { v: i64 }
        impl Base {
            fn sum_up(self: &Base, n: i64, a: &[i64; n <= 8]) -> i64 ! {panic} { self.v + a[0] }
            fn make(self: &Base, n: i64) -> [i64; n <= 8] ! {panic} { Array.fill(n, self.v) }
        }
        fn first<T>(n: i64, a: [T; n <= 8]) -> T ! {panic} { a[0] }
    "#;
    let program = |body: &str| format!("{base}\nfn main() -> i64 ! {{panic}} {{\n{body}\n}}");
    rejects(
        &program(
            "let k: i64 = 3; let j: i64 = 3; let h = Base { v: 1 };
             let c: [i64; j <= 8] = Array.fill(j, 1); h.sum_up(k, &c)",
        ),
        "expected &[i64; k <= 8], found &[i64; j <= 8]",
    );
    rejects(
        &program(
            "let k: i64 = 3; let j: i64 = 3; let h = Base { v: 1 };
             let c: [i64; j <= 8] = h.make(k); 0",
        ),
        "expected [i64; j <= 8], found [i64; k <= 8]",
    );
    rejects(
        &program(
            "let k: i64 = 3; let h = Base { v: 1 };
             let c: [i64; k <= 8] = Array.fill(k, 1); h.sum_up(3, &c)",
        ),
        "'n' sizes a runtime-length array in the signature of 'sum_up'",
    );
    rejects(
        &program(
            "let k: i64 = 3; let j: i64 = 3;
             let c: [i64; j <= 8] = Array.fill(j, 1); first(k, c)",
        ),
        "expected [i64; k <= 8], found [i64; j <= 8]",
    );
    rejects(
        &program("let mut k: i64 = 3; let h = Base { v: 1 }; let c = h.make(k); 0"),
        "must be an immutable i64 parameter or local in scope",
    );
    rejects(
        &program("let f = first::<i64>; 0"),
        "cannot be a first-class value",
    );
    // The receiver is never a length binder.
    rejects(
        r#"
        trait Len { fn f(self: Self, a: [i64; self <= 4]) -> i64 ! {}; }
        fn main() -> i64 ! {} { 0 }"#,
        "must be an earlier i64 parameter of the same function",
    );
    // A trait and its impl must spell the binder the same way.
    rejects(
        r#"
        trait Summer { fn s(self: Self, n: i64, a: [i64; n <= 8]) -> i64 ! {panic}; }
        struct Base { v: i64 }
        impl Summer for Base {
            fn s(self: Self, m: i64, a: [i64; m <= 8]) -> i64 ! {panic} { a[0] }
        }
        fn main() -> i64 ! {} { 0 }"#,
        "does not match the trait signature exactly",
    );
    rejects(
        r#"
        foreign "f" fn f(n: i64, a: [i64; n <= 4]) -> i64 ! {io};
        fn main() -> i64 ! {} { 0 }"#,
        "a foreign function signature cannot mention a runtime-length array",
    );
}

#[test]
fn trait_objects_cannot_carry_runtime_length_methods() {
    // A dynamic call has no static callee whose binders could be replaced.
    rejects(
        r#"
        trait Summer { fn s(self: Self, n: i64, a: [i64; n <= 8]) -> i64 ! {panic}; }
        struct Base { v: i64 }
        impl Summer for Base {
            fn s(self: Self, n: i64, a: [i64; n <= 8]) -> i64 ! {panic} { a[0] }
        }
        fn main() -> i64 ! {panic} { let h = Base { v: 1 }; let d: dyn Summer = h; 0 }"#,
        "mentions a runtime-length array [T; n <= C]; call it through a concrete receiver",
    );
}

#[test]
fn recursive_calls_cannot_capture_their_own_length_binder() {
    // Regression: the instance `go::<[i64; n <= 4]>` called from inside `go`
    // named `go`'s own `n`. In the new activation `n` holds another value, so
    // `y` (built with the outer `n == 0`) was typed with the inner `n == 1`
    // and the proved read `y[i]` went out of bounds.
    rejects(
        r#"
        fn go<T>(n: i64, x: T, depth: i64, erased ok: { 0 <= n && n <= 4 }) -> i64 ! {panic} {
            let a: [i64; n <= 4] = Array.fill(n, 5);
            if depth == 0 {
                go::<[i64; n <= 4]>(1, a, 1, _)
            } else {
                let u: T | [i64; n <= 4] | Bool = x;
                match u {
                    [i64; n <= 4] @ y => {
                        let mut i = 0;
                        let mut acc = 0;
                        while i < n { acc = acc + y[i]; i = i + 1; }
                        acc
                    },
                    _ => 0,
                }
            }
        }
        fn main() -> i64 ! {panic} { go::<i64>(0, 0, 0, _) }"#,
        "a type argument of 'go' mentions its own length binder 'n'",
    );
    // The same through a generic impl's arguments.
    rejects(
        r#"
        struct W<T> { x: T }
        impl<T> W<T> {
            fn go(self: W<T>, n: i64, depth: i64, erased ok: { 0 <= n && n <= 4 }) -> i64 ! {panic} {
                let a: [i64; n <= 4] = Array.fill(n, 5);
                if depth == 0 {
                    let w2 = W { x: a };
                    let one: i64 = 1;
                    w2.go(one, 1, _)
                } else { 0 }
            }
        }
        fn main() -> i64 ! {panic} { let w = W { x: 0 }; w.go(0, 0, _) }"#,
        "a type argument of 'go' mentions its own length binder 'n'",
    );
    // Review regression: the same through an inherited trait default, whose
    // per-impl copy has its own binding while `n` belongs to the trait method.
    rejects(
        r#"
        struct W<T> { x: T }
        trait Go {
            fn go(self: Self, n: i64, depth: i64, erased ok: { 0 <= n && n <= 4 }) -> i64 ! {} {
                let a: [i64; n <= 4] = Array.fill(n, 5);
                if depth == 0 {
                    let w2 = W { x: a };
                    let one: i64 = 1;
                    w2.go(one, 1, _)
                } else {
                    let u: W<[i64; n <= 4]> | Self | Bool = self;
                    match u {
                        W<[i64; n <= 4]> @ w => { let y = w.x; if 0 < n { y[0] } else { 66 } },
                        _ => 77,
                    }
                }
            }
        }
        impl<T> Go for W<T> {}
        fn main() -> i64 ! {} { let w = W { x: 0 }; w.go(0, 0, _) }"#,
        "a type argument of 'go' mentions its own length binder 'n'",
    );
    // A different function may still be instantiated with the caller's type.
    agrees(
        r#"
        fn id<T>(x: T) -> T ! {} { x }
        fn go(n: i64, erased ok: { 0 < n && n <= 4 }) -> i64 ! {} {
            let a: [i64; n <= 4] = Array.fill(n, 5);
            let b: [i64; n <= 4] = id::<[i64; n <= 4]>(a);
            b[0]
        }
        fn main() -> i64 ! {panic} { let k: i64 = 2; go(k, _) }"#,
        5,
    );
}

// ---------------------------------------------------------------------------
// Binders nested inside signature types
// ---------------------------------------------------------------------------

#[test]
fn signatures_rebind_lengths_inside_containers_tuples_records_and_unions() {
    let stats = agrees(
        r#"
        enum Maybe<T> { Some(T), None }
        struct Pair<T> { a: T, b: i64 }
        fn rows(n: i64, count: i64) -> Vec<[i64; n <= 4]> ! {panic, alloc} {
            let mut v: Vec<[i64; n <= 4]> = Vec.new();
            let mut i = 0;
            while i < count { v = Vec.push(v, Array.fill(n, i)); i = i + 1; }
            v
        }
        fn summed(n: i64, v: &Vec<[i64; n <= 4]>) -> i64 ! {panic} {
            let mut acc = 0;
            let mut i = 0;
            while i < Vec.len(v) {
                let row: [i64; n <= 4] = Vec.get(v, i);
                let mut j = 0;
                while j < n { acc = acc + row[j]; j = j + 1; }
                i = i + 1;
            }
            acc
        }
        fn split(n: i64, p: ([i64; n <= 4], Box<[i64; n <= 4]>)) -> Pair<[i64; n <= 4]> ! {alloc} {
            let (x, y) = p;
            Pair { a: Box.take(y), b: DynArray.len(&x) }
        }
        fn opt(n: i64, o: Maybe<[i64; n <= 4]>) -> i64 ! {panic} {
            match o { Maybe.Some(a) => DynArray.len(&a), Maybe.None => 0 }
        }
        fn either(n: i64, u: [i64; n <= 4] | Bool) -> i64 ! {} {
            match u { [i64; n <= 4] @ a => DynArray.len(&a), Bool @ b => 100 }
        }
        fn mk(n: i64) -> struct { xs: [i64; n <= 4], tag: i64 } ! {panic} {
            struct { xs: Array.fill(n, 4), tag: 1 }
        }
        fn main() -> i64 ! {panic, alloc} {
            let k: i64 = 3;
            let v: Vec<[i64; k <= 4]> = rows(k, 3);
            let t = summed(k, &v);                         // 0*3 + 1*3 + 2*3 = 9
            let a: [i64; k <= 4] = Array.fill(k, 1);
            let b: [i64; k <= 4] = Array.fill(k, 2);
            let p: Pair<[i64; k <= 4]> = split(k, (a, Box.new(b)));
            let c: [i64; k <= 4] = p.a;
            let r = mk(k);
            let d: [i64; k <= 4] = r.xs;
            t + p.b + opt(k, Maybe.Some(c)) + either(k, d) + either(k, true)
        }"#,
        118,
    );
    assert!(stats.allocations >= 2);
    // A generic element inside a nested position.
    agrees(
        r#"
        fn heads<T>(n: i64, v: &Vec<[T; n <= 4]>, erased ok: { 0 < n && n <= 4 }) -> T ! {panic} {
            let row: [T; n <= 4] = Vec.get(v, 0);
            row[0]
        }
        fn main() -> i64 ! {panic, alloc} {
            let k: i64 = 2;
            let mut v: Vec<[i64; k <= 4]> = Vec.new();
            v = Vec.push(v, [7, 8]);
            heads(k, &v, _)
        }"#,
        7,
    );
    // Owning elements inside a nested array drop exactly once.
    let stats = agrees(
        r#"
        fn wrap(n: i64, a: [Box<i64>; n <= 4]) -> Vec<[Box<i64>; n <= 4]> ! {alloc, panic} {
            let v: Vec<[Box<i64>; n <= 4]> = Vec.new();
            Vec.push(v, a)
        }
        fn main() -> i64 ! {panic, alloc} {
            let k: i64 = 2;
            let a: [Box<i64>; k <= 4] = [Box.new(1), Box.new(2)];
            let v: Vec<[Box<i64>; k <= 4]> = wrap(k, a);
            Vec.len(&v)
        }"#,
        1,
    );
    assert!(stats.allocations >= 3);
}

#[test]
fn nested_signature_binders_reject_mismatches_and_unsubstitutable_positions() {
    rejects(
        r#"
        fn s(n: i64, v: &Vec<[i64; n <= 4]>) -> i64 ! {} { 0 }
        fn main() -> i64 ! {alloc, panic} {
            let k: i64 = 2; let j: i64 = 2;
            let v: Vec<[i64; j <= 4]> = Vec.new();
            s(k, &v)
        }"#,
        "expected &Vec<[i64; k <= 4]>, found &Vec<[i64; j <= 4]>",
    );
    rejects(
        r#"
        fn s(n: i64) -> Vec<[i64; n <= 4]> ! {alloc} { Vec.new() }
        fn main() -> i64 ! {alloc} {
            let k: i64 = 2; let j: i64 = 2;
            let v: Vec<[i64; j <= 4]> = s(k);
            0
        }"#,
        "expected Vec<[i64; j <= 4]>, found Vec<[i64; k <= 4]>",
    );
    rejects(
        "fn s(n: i64, f: fn([i64; n <= 4]) -> i64 ! {}) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "a fn/once fn type cannot mention a runtime-length array",
    );
    rejects(
        r#"
        trait Tr<T> { fn m(self: Self) -> i64 ! {}; }
        fn s(n: i64, f: dyn Tr<[i64; n <= 4]>) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }"#,
        "a trait object type cannot mention a runtime-length array",
    );
    rejects(
        "fn s(v: Vec<[i64; n <= 4]>, n: i64) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "must be the name of an immutable i64 parameter or local",
    );
    rejects(
        "fn s(m: i64, v: Vec<[i64; m <= 4]>) -> (i64, [i64; q <= 4]) ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "must be the name of an immutable i64 parameter or local",
    );
}

// ---------------------------------------------------------------------------
// Exclusive borrowed DynArray patterns
// ---------------------------------------------------------------------------

#[test]
fn exclusive_patterns_bind_disjoint_element_references() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn bump(n: i64, a: &mut [i64; n <= 4]) -> Unit ! {panic} {
            match a {
                [x, ..rest] => { *x = *x + 100; Slice.set(rest, 0, 7); },
                _ => {},
            }
        }
        fn bump_points(a: &mut DynArray<Point, 4>) -> Unit ! {panic} {
            match a {
                [p, .., q] => { p.x = 50; q.y = 60; },
                _ => {},
            }
        }
        fn main() -> i64 ! {panic} {
            let k: i64 = 3;
            let mut a: [i64; k <= 4] = [1, 2, 3];
            bump(k, &mut a);
            let mut swap: DynArray<i64, 4> = [4, 9];
            match &mut swap {
                [x, y] => { let t = *x; *x = *y; *y = t; },
                _ => {},
            }
            // A literal sub-pattern tests a copy; the guard reads a binding.
            let mut i = 0;
            let mut hits = 0;
            while i < 3 {
                match &mut swap {
                    [9, y] if *y < 6 => { *y = *y + 1; hits = hits + 1; },
                    _ => {},
                }
                i = i + 1;
            }
            let mut ps: DynArray<Point, 4> = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
            bump_points(&mut ps);
            // (101 + 7 + 3) + (9 * 10 + 6) + 2 + (50 + 60) = 319
            a[0] + a[1] + a[2] + DynArray.get(&swap, 0) * 10 + DynArray.get(&swap, 1) + hits
                + DynArray.get(&ps, 0).x + DynArray.get(&ps, 1).y - 256
        }"#,
        63,
    );
    // Two bindings may be passed to one call, and a reference into the rest
    // view coexists with a prefix binding.
    agrees(
        r#"
        fn swap(p: &mut i64, q: &mut i64) -> Unit ! {} { let t = *p; *p = *q; *q = t; }
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [3, 4, 5, 6];
            match &mut a { [x, .., y] => swap(x, y), _ => {} };
            match &mut a {
                [x, ..rest] => {
                    let y: &mut i64 = &mut rest[0];
                    *y = 20;
                    *x = *x + 1;
                    Slice.set(rest, 1, 30);
                },
                _ => {},
            };
            // [7, 20, 30, 3]
            DynArray.get(&a, 0) + DynArray.get(&a, 1) + DynArray.get(&a, 2) + DynArray.get(&a, 3)
        }"#,
        60,
    );
    // Split sides of `Slice.split_at_mut` likewise pass element references
    // from both sides to one call.
    agrees(
        r#"
        fn swap(p: &mut i64, q: &mut i64) -> Unit ! {} { let t = *p; *p = *q; *q = t; }
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [3, 4, 5];
            {
                let v: &mut [i64] = &mut a[..];
                let (l, r) = Slice.split_at_mut(v, 1);
                let p = &mut l[0];
                let q = &mut r[1];
                swap(p, q);
            }
            DynArray.get(&a, 0) * 10 + DynArray.get(&a, 2)
        }"#,
        53,
    );
    // A binding may leave the match; the array is usable after its last use.
    // A `&mut` parameter scrutinee is reborrowed, not consumed.
    agrees(
        r#"
        fn first(a: &mut DynArray<i64, 4>) -> i64 ! {panic} {
            let r: &mut i64 = match a { [x, ..] => x, _ => return 0 };
            *r = 1;
            DynArray.get(a, 0) + DynArray.len(a)
        }
        fn main() -> i64 ! {panic} {
            let mut b: DynArray<i64, 4> = [5, 2];
            let u = first(&mut b);
            let mut c: DynArray<(i64, i64), 4> = [(1, 2), (3, 4)];
            match &mut c { [(1, _), p] => { *p = (7, 8); }, _ => {} };
            let (s, t) = DynArray.get(&c, 1);
            u + DynArray.get(&b, 0) * 10 + s + t
        }"#,
        28,
    );
}

#[test]
fn exclusive_pattern_bindings_suspend_the_array() {
    let program = |body: &str| {
        format!(
            "struct H {{ xs: DynArray<i64, 4>, n: i64 }}
            fn eat(a: DynArray<i64, 4>) -> i64 ! {{}} {{ 0 }}
            fn main() -> i64 ! {{panic}} {{
                let mut a: DynArray<i64, 4> = [1, 2, 3];
                let mut h = H {{ xs: [1, 2], n: 4 }};
                {body}
                0
            }}"
        )
    };
    for (body, fragment) in [
        (
            "match &mut a { [x, ..] => { let z = DynArray.get(&a, 1); *x = z; }, _ => {} };",
            "cannot borrow an owner while an exclusive '&mut [T]' view of it is live",
        ),
        (
            "match &mut a { [x, ..] => { let v: &[i64] = &a[..]; *x = Slice.get(v, 0); }, _ => {} };",
            "while an exclusive '&mut [T]' view of the same owner is live",
        ),
        (
            "match &mut a { [x, ..] => { let v: &mut [i64] = &mut a[..]; Slice.set(v, 0, 3); *x = 1; }, _ => {} };",
            "cannot create an exclusive '&mut [T]' view while another view",
        ),
        (
            "match &mut a { [x, ..] => { a = DynArray.push(a, 3); *x = 1; }, _ => {} };",
            "cannot replace an owner while a slice view or reference borrows it",
        ),
        (
            "match &mut a { [x, ..] => { let q = eat(a); *x = 1; }, _ => {} };",
            "cannot read an owner while an exclusive '&mut [T]' view of it is live",
        ),
        (
            "match &mut a { [x, ..] if DynArray.len(&a) > 1 => { *x = 1; }, _ => {} };",
            "cannot borrow an owner while an exclusive '&mut [T]' view of it is live",
        ),
        (
            "let r: &mut i64 = match &mut a { [x, ..] => x, _ => return 0 };
             let z = DynArray.get(&a, 0); *r = 5;",
            "cannot borrow an owner while an exclusive '&mut [T]' view of it is live",
        ),
        (
            "let r: &mut i64 = match &mut a { [x, ..] => x, _ => return 0 };
             match &mut a { [y, ..] => { *y = 3; }, _ => {} };
             *r = 5;",
            "cannot borrow an owner while an exclusive '&mut [T]' view of it is live",
        ),
        (
            "match &mut a { [x, ..rest] => { let y: &mut i64 = &mut rest[0]; Slice.set(rest, 0, 5); *y = 20; }, _ => {} };",
            "cannot use a slice view while a child view derived from it is live",
        ),
        (
            "match &mut h.xs { [x, y] => { let q = DynArray.get(&h.xs, 0); *x = q; }, _ => {} };",
            "cannot create a shared place borrow while an exclusive borrow",
        ),
        (
            "let r: &mut i64 = { let mut b: DynArray<i64, 4> = [1, 2]; match &mut b { [x, ..] => x, _ => return 0 } };
             *r = 5;",
            "reference escapes the lexical scope of the storage it borrows",
        ),
    ] {
        rejects(&program(body), fragment);
    }
    rejects(
        r#"
        fn upd(a: &mut DynArray<i64, 4>) -> i64 ! {panic} {
            match a { [x, ..] => { let n = DynArray.len(a); *x = n; }, _ => {} }
            0
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot use an owner while an exclusive '&mut [T]' view of it is live",
    );
    rejects(
        r#"
        struct H { xs: DynArray<i64, 4>, n: i64 }
        fn upd(h: &mut H) -> Unit ! {panic} {
            match &mut h.xs { [x, ..] => { *h = H { xs: [], n: 0 }; *x = 42; }, _ => {} }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot write through a reference while a view, element reference, or pattern binding derived from it is live",
    );
}

#[test]
fn exclusive_patterns_reject_owning_elements_and_shared_storage() {
    rejects(
        r#"
        fn main() -> i64 ! {panic, alloc} {
            let mut a: DynArray<Box<i64>, 4> = [Box.new(1)];
            match &mut a { [x, ..] => 0, _ => 1 }
        }"#,
        "a '&mut DynArray' pattern binds '&mut T' element references, which would alias an owning",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let a: DynArray<i64, 4> = [1, 2];
            match &mut a { [x, ..] => { *x = 3; }, _ => {} }
            0
        }"#,
        "cannot mutably borrow an immutable binding",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            match &mut a { [x, x] => { *x = 3; }, _ => {} }
            0
        }"#,
        "duplicate pattern binding 'x'",
    );
    rejects(
        r#"
        fn f(a: &DynArray<i64, 4>) -> Unit ! {} { match a { [x, ..] => { *x = 1; }, _ => {} } }
        fn main() -> i64 ! {} { 0 }"#,
        "cannot write through a shared reference",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut a: DynArray<i64, 4> = [1, 2];
            match &mut a { [x, ..] => 0, y => 1 }
        }"#,
        "supports slice patterns such as '[x, .., y]' and '_'",
    );
}

#[test]
fn exclusive_pattern_arms_release_owners_on_every_exit() {
    // Early return, loop exit, and normal arm completion with owning locals
    // live around the exclusive bindings: every box is released once.
    let stats = agrees(
        r#"
        fn pick(a: &mut DynArray<i64, 4>, b: Box<i64>) -> i64 ! {panic, alloc} {
            let keep = Box.new(5);
            match a {
                [x, ..] if *x > 10 => { *x = 0; return Box.read(&b) + Box.read(&keep); },
                [x, y, ..] => { *y = Box.read(&b); *x = *x + 1; },
                _ => {},
            }
            Box.read(&keep)
        }
        fn main() -> i64 ! {panic, alloc} {
            let mut a: DynArray<i64, 4> = [20, 2];
            let first = pick(&mut a, Box.new(7));     // 12, a = [0, 2]
            let second = pick(&mut a, Box.new(9));    // 5,  a = [1, 9]
            let mut i = 0;
            while i < 4 {
                let guard = Box.new(i);
                match &mut a {
                    [x, ..] if *x > 2 => { break; },
                    [x, ..] => { *x = *x + Box.read(&guard); },
                    _ => {},
                }
                i = i + 1;
            }
            // a[0]: 1 -> 1 -> 2 -> 4 -> break
            first + second + DynArray.get(&a, 0) + DynArray.get(&a, 1)
        }"#,
        30,
    );
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stats.allocations >= 6);
}

#[test]
fn rebinding_never_merges_union_members() {
    // Review regression: `f(k, k, ...)` made the callee's two union members
    // one type at the call site, so the caller read the union's words as a
    // plain array (a proved read trapped natively; the evaluator crashed).
    for program in [
        r#"
        fn f(n: i64, m: i64, a: [i64; n <= 4], b: [i64; m <= 4], pick: Bool) -> [i64; n <= 4] | [i64; m <= 4] ! {} {
            if pick { a } else { b }
        }
        fn main() -> i64 ! {} {
            let k: i64 = 4;
            let x: [i64; k <= 4] = Array.fill(k, 5);
            let y: [i64; k <= 4] = Array.fill(k, 7);
            let r = f(k, k, x, y, false);
            let z: [i64; k <= 4] = r;
            z[3]
        }"#,
        r#"
        fn f<T>(n: i64, x: T, a: [i64; n <= 4], pick: Bool) -> T | [i64; n <= 4] ! {} {
            if pick { x } else { a }
        }
        fn main() -> i64 ! {} {
            let k: i64 = 4;
            let x: [i64; k <= 4] = Array.fill(k, 5);
            let y: [i64; k <= 4] = Array.fill(k, 7);
            let r = f(k, x, y, false);
            let z: [i64; k <= 4] = r;
            z[3]
        }"#,
        r#"
        fn f(n: i64, m: i64, u: [i64; n <= 4] | [i64; m <= 4], erased ok: { n == 4 && m == 4 }) -> i64 ! {} {
            match u { [i64; n <= 4] @ a => a[3], [i64; m <= 4] @ b => b[2] }
        }
        fn main() -> i64 ! {} {
            let k: i64 = 4;
            let x: [i64; k <= 4] = Array.fill(k, 5);
            f(k, k, x, _)
        }"#,
    ] {
        rejects(
            program,
            "would change the layout of the callee's signature type",
        );
    }
    // Distinct caller binders keep the union and its members.
    agrees(
        r#"
        fn f(n: i64, m: i64, a: [i64; n <= 4], b: [i64; m <= 4], pick: Bool) -> [i64; n <= 4] | [i64; m <= 4] ! {} {
            if pick { a } else { b }
        }
        fn main() -> i64 ! {panic} {
            let k: i64 = 4;
            let j: i64 = 2;
            let x: [i64; k <= 4] = Array.fill(k, 5);
            let y: [i64; j <= 4] = Array.fill(j, 7);
            let r = f(k, j, x, y, false);
            match r {
                [i64; k <= 4] @ a => DynArray.len(&a),
                [i64; j <= 4] @ b => DynArray.len(&b) * 10 + DynArray.get(&b, 1),
            }
        }"#,
        27,
    );
}

#[test]
fn rebinding_never_changes_a_signature_layout() {
    // Review regressions (round 3): rebuilding a signature type with the
    // caller's binders re-normalizes unions. Members could swap positions
    // (r3, r4: union order follows interned type ids), a width subtype could
    // absorb another member (p5), or a union inside a generic definition
    // could merge (p1). Each made the caller read the callee's union tag
    // against the wrong member. Such calls are rejected.
    rejects(
        r#"
fn f(n: i64, m: i64, a: [i64; n <= 4], b: [i64; m <= 4], pick: Bool) -> [i64; n <= 4] | [i64; m <= 4] ! {} {
    if pick { a } else { b }
}
fn main() -> i64 ! {} {
    let k: i64 = 4;
    let j: i64 = 2;
    let y: [i64; k <= 4] = Array.fill(k, 5);
    let x: [i64; j <= 4] = Array.fill(j, 7);
    let r = f(j, k, x, y, true);
    match r {
        [i64; k <= 4] @ a => a[3],
        [i64; j <= 4] @ b => b[1],
    }
}"#,
        "would change the layout of the callee's signature type",
    );
    rejects(
        r#"
struct W<T> { v: T, w: T, z: T, q: T, r: T }
fn f(n: i64, u: [i64; n <= 4] | W<i64>, erased ok: { n == 4 }) -> i64 ! {} {
    match u { [i64; n <= 4] @ a => a[3], W<i64> @ b => b.v }
}
fn main() -> i64 ! {} {
    let k: i64 = 4;
    let x: [i64; k <= 4] = Array.fill(k, 5);
    let w = W { v: 1, w: 2, z: 3, q: 4, r: 6 };
    let p = f(k, x, _); let q = f(k, w, _); if p == 5 { if q == 1 { 51 } else { q } } else { p }
}"#,
        "would change the layout of the callee's signature type",
    );
    rejects(
        r#"
struct P<A, B> { u: A | B, tag: i64 }
fn f(n: i64, m: i64, a: [i64; n <= 4], b: [i64; m <= 4], pick: Bool) -> P<[i64; n <= 4], [i64; m <= 4]> ! {} {
    if pick { P { u: a, tag: 1 } } else { P { u: b, tag: 2 } }
}
fn main() -> i64 ! {} {
    let k: i64 = 4;
    let x: [i64; k <= 4] = Array.fill(k, 5);
    let y: [i64; k <= 4] = Array.fill(k, 7);
    let r = f(k, k, x, y, false);
    let z: [i64; k <= 4] = r.u;
    z[3]
}"#,
        "would change the layout of the callee's signature type",
    );
    rejects(
        r#"
fn f(n: i64, m: i64, u: struct { xs: [i64; n <= 4] } | struct { xs: [i64; m <= 4], tag: i64 }, erased ok: { n == 4 && m == 4 }) -> i64 ! {} {
    match u {
        struct { xs: [i64; n <= 4] } @ a => { let v = a.xs; v[3] },
        struct { xs: [i64; m <= 4], tag: i64 } @ b => { let w = b.xs; w[2] },
    }
}
fn main() -> i64 ! {} {
    let k: i64 = 4;
    let x: [i64; k <= 4] = Array.fill(k, 5);
    f(k, k, struct { xs: x, tag: 30 }, _)
}"#,
        "would change the layout of the callee's signature type",
    );
}
