//! Lifetime-aware callable types: arrow types may borrow slice views under
//! their own lifetime binders (`fn<'a>(&'a [T]) -> &'a [T]`). A function value
//! fits an arrow only when its borrow contract is implied by the arrow's, and
//! calls through a value get the same borrow checks as direct calls.
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

/// Reference evaluator and native code must agree.
fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let (status, output, _) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("callable-lifetimes-test");
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
fn higher_order_helpers_take_slice_callbacks() {
    // Named functions and lambdas with elided slice parameters.
    agrees(
        r#"fn sum(v: &[i64]) -> i64 ! {panic} {
            let mut i = 0;
            let mut acc = 0;
            while i < Slice.len(v) { acc = acc + Slice.get(v, i); i = i + 1; }
            acc
        }
        fn measure(xs: &[i64], f: fn(&[i64]) -> i64 ! {panic}) -> i64 ! {panic} {
            f(xs)
        }
        fn main() -> i64 ! {io, panic} {
            let a: [i64; 3] = [10, 20, 12];
            print_i64(measure(&a[..], sum));
            let length = fn(v: &[i64]) -> i64 ! {panic} { Slice.len(v) };
            measure(&a[..], length)
        }"#,
        3,
        "42\n",
    );
}

#[test]
fn slice_returning_function_values_keep_their_sources_borrowed() {
    agrees(
        r#"fn tail<'a>(v: &'a [i64]) -> &'a [i64] ! {panic} { &v[1..] }
        fn apply<'x>(f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic}, v: &'x [i64]) -> &'x [i64] ! {panic} {
            f(v)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [1, 40, 2];
            let rest = apply(tail, &a[..]);
            Slice.get(rest, 0) + Slice.get(rest, 1)
        }"#,
        42,
        "",
    );
    // A value with an outlives bound fits an arrow that instantiates both
    // lifetimes to the same one.
    agrees(
        r#"fn second<'l: 's, 's>(long: &'l [i64], short: &'s [i64]) -> &'s [i64] ! {panic} { long }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 2];
            let pick: fn<'a>(&'a [i64], &'a [i64]) -> &'a [i64] ! {panic} = second;
            let view = pick(&a[..], &a[..]);
            Slice.get(view, 0) + Slice.get(view, 1)
        }"#,
        42,
        "",
    );
    // Exclusive results through a value.
    agrees(
        r#"fn head<'a>(v: &'a mut [i64]) -> &'a mut [i64] ! {panic} { v }
        fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let f: fn<'a>(&'a mut [i64]) -> &'a mut [i64] ! {panic} = head;
            let view = f(&mut a[..]);
            Slice.set(view, 0, 40);
            a[0] + a[1]
        }"#,
        42,
        "",
    );
}

#[test]
fn indirect_results_cannot_outlive_or_invalidate_their_sources() {
    // The result of a call through a value borrows the argument's owner.
    rejects(
        r#"fn tail<'a>(v: &'a [i64]) -> &'a [i64] ! {panic} { &v[1..] }
        fn leak<'p>(f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic}, p: &'p [i64]) -> &'p [i64] ! {panic} {
            let local: [i64; 2] = [1, 2];
            f(&local[..])
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "outlive",
    );
    rejects(
        r#"fn tail<'a>(v: &'a [i64]) -> &'a [i64] ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Vec<i64> = [1, 2];
            let f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic} = tail;
            let view = f(&owner[..]);
            drop(owner);
            Slice.get(view, 0)
        }"#,
        "while a slice view derived from it is live",
    );
    // Call-site outlives constraints apply through values too.
    rejects(
        r#"fn both<'l: 's, 's>(l: &'l [i64], s: &'s [i64]) -> i64 ! {panic} { Slice.len(l) + Slice.len(s) }
        fn main() -> i64 ! {panic} {
            let first: [i64; 1] = [1];
            let second: [i64; 1] = [2];
            let f: fn<'l: 's, 's>(&'l [i64], &'s [i64]) -> i64 ! {panic} = both;
            f(&first[..], &second[..])
        }"#,
        "cannot establish the callee's outlives constraint 'a: 'b",
    );
}

#[test]
fn function_values_fit_arrows_only_when_their_contract_is_implied() {
    // The result comes from the second input, but the arrow promises the first.
    rejects(
        r#"fn second<'a, 'b>(x: &'a [i64], y: &'b [i64]) -> &'b [i64] ! {panic} { y }
        fn main() -> i64 ! {panic} {
            let f: fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'a [i64] ! {panic} = second;
            0
        }"#,
        "expected fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'a [i64] ! {panic}, found fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'b [i64]",
    );
    // The value requires 'l: 's, which the arrow does not promise.
    rejects(
        r#"fn both<'l: 's, 's>(l: &'l [i64], s: &'s [i64]) -> i64 ! {panic} { 0 }
        fn main() -> i64 ! {panic} {
            let f: fn<'a, 'b>(&'a [i64], &'b [i64]) -> i64 ! {panic} = both;
            0
        }"#,
        "found fn<'a: 'b, 'b>(&'a [i64], &'b [i64]) -> i64",
    );
}

#[test]
fn arrow_lifetimes_are_bound_and_results_must_have_a_source() {
    rejects(
        r#"fn g<'x>(f: fn(&'x [i64]) -> i64 ! {}, v: &'x [i64]) -> i64 ! {} { f(v) }
        fn main() -> i64 ! {} { 0 }"#,
        "bound by the arrow itself",
    );
    rejects(
        r#"fn g(f: fn<'a, 'b>(&'a [i64]) -> &'b [i64] ! {}) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }"#,
        "not outlived by any slice parameter",
    );
    rejects(
        r#"fn g(f: fn(&[i64], &[i64]) -> &[i64] ! {}) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }"#,
        "cannot infer this arrow result's lifetime",
    );
    rejects(
        r#"fn g(f: fn<'a>(&'a [i64]) -> &'a mut [i64] ! {}) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }"#,
        "exclusive",
    );
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let f = fn(v: &[i64], w: &[i64]) -> &[i64] ! {panic} { v };
            0
        }"#,
        "cannot infer this lambda result's lifetime",
    );
    rejects(
        r#"fn g(f: fn<T>(T) -> i64 ! {}) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }"#,
        "binds only lifetimes",
    );
}

#[test]
fn borrowed_callables_example_agrees_natively() {
    agrees(
        include_str!("../../../examples/borrowed-callables.kush"),
        0,
        "42\n2\n40\n",
    );
}

#[test]
fn slice_returning_lambdas_preserve_borrows_through_higher_order_calls() {
    agrees(
        r#"fn apply<'x>(f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic}, v: &'x [i64]) -> &'x [i64] ! {panic} {
            f(v)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 3] = [1, 40, 2];
            let tail = fn(v: &[i64]) -> &[i64] ! {panic} { &v[1..] };
            let rest = apply(tail, &a[..]);
            Slice.get(rest, 0) + Slice.get(rest, 1)
        }"#,
        42,
        "",
    );
    agrees(
        r#"fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let head: fn<'a>(&'a mut [i64]) -> &'a mut [i64] ! {panic} =
                fn(v: &mut [i64]) -> &mut [i64] ! {panic} { v };
            let view = head(&mut a[..]);
            Slice.set(view, 0, 40);
            a[0] + a[1]
        }"#,
        42,
        "",
    );
}

#[test]
fn slice_returning_lambdas_reject_dangling_and_invalidated_results() {
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let leak = fn(v: &[i64]) -> &[i64] ! {panic} {
                let local: [i64; 1] = [42];
                &local[..]
            };
            0
        }"#,
        "outlive",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let owner: Vec<i64> = [40, 2];
            let identity = fn(v: &[i64]) -> &[i64] ! {panic} { v };
            let view = identity(&owner[..]);
            drop(owner);
            Slice.get(view, 0)
        }"#,
        "while a slice view derived from it is live",
    );
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let invalid = fn(v: &[i64]) -> &mut [i64] ! {panic} { v };
            0
        }"#,
        "exclusive slice parameter",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let owner: Vec<i64> = [42];
            let captured = fn(v: &[i64]) -> &[i64] ! {panic} { &owner[..] };
            0
        }"#,
        "dangle",
    );
}

#[test]
fn indirect_slice_returns_preserve_split_siblings_and_reborrow_exclusivity() {
    agrees(
        r#"fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let (left, right) = Slice.split_at_mut(&mut a[..], 1);
            let identity = fn(v: &mut [i64]) -> &mut [i64] ! {} { v };
            let first = identity(left);
            let second = identity(right);
            Slice.set(first, 0, 40);
            Slice.get(first, 0) + Slice.get(second, 0)
        }"#,
        42,
        "",
    );
    rejects(
        r#"fn main() -> i64 ! {panic} {
            let mut a: [i64; 2] = [1, 2];
            let view = &mut a[..];
            let identity = fn(v: &mut [i64]) -> &mut [i64] ! {} { v };
            let first = identity(view);
            let second = identity(view);
            Slice.get(first, 0) + Slice.get(second, 0)
        }"#,
        "use after move",
    );
}
