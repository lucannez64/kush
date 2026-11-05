//! Runtime-index disjointness for place references. Two element references
//! into one array, vector, or slice view coexist only when the checker's
//! linear facts prove their indices distinct; an unproved or equal pair is an
//! aliasing error. Every positive case runs in the reference evaluator and,
//! on Linux x86-64, in the Cranelift backend, with balanced allocations.
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
        let binary = scratch.path().join("index-disjointness-test");
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

const OVERLAP: &str = "cannot create an exclusive place borrow while an overlapping borrow";

#[test]
fn a_constant_and_a_runtime_index_conflict_unless_proved_distinct() {
    // Regression: `&mut xs[1]` and `&mut xs[i]` with `i == 1` used to be
    // treated as disjoint, aliasing one element through two `&mut`.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let i = 1;
            let p = &mut xs[1];
            let q = &mut xs[i];
            *p = 10;
            *q = 20;
            *p
        }"#,
        OVERLAP,
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut v: Vec<i64> = [1, 2, 3];
            let i = 1;
            let p = &mut v[i];
            let q = &mut v[1];
            *p = 10;
            *q = 20;
            *p
        }"#,
        OVERLAP,
    );
    // Proved distinct from the constant: accepted.
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let i = 2;
            {
                let p = &mut xs[1];
                let q = &mut xs[i];
                *p = 10;
                *q = 20;
            }
            xs[1] + xs[2]
        }"#,
        30,
        "",
    );
}

#[test]
fn equal_or_unproved_runtime_indices_conflict() {
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let i = 0;
            let j = 0;
            let p = &mut xs[i];
            let q = &mut xs[j];
            *p + *q
        }"#,
        OVERLAP,
    );
    rejects(
        r#"
        fn f(v: &mut [i64], i: i64, j: i64) -> i64 ! {panic} {
            let p = &mut v[i];
            let q = &mut v[j];
            *p + *q
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        OVERLAP,
    );
    // The same expression after the index returns to its old value.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let mut i = 0;
            let p = &mut xs[i];
            i = i + 1;
            i = i - 1;
            let q = &mut xs[i];
            *p + *q
        }"#,
        OVERLAP,
    );
    // An index whose address was taken by `&mut` is opaque to the facts.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let mut i = 0;
            let r = &mut i;
            let p = &mut xs[0];
            *r = 0;
            let q = &mut xs[i];
            *p + *q
        }"#,
        OVERLAP,
    );
    // A disequality only holds inside its branch.
    rejects(
        r#"
        fn f(v: &mut [i64], i: i64, j: i64) -> i64 ! {panic} {
            if i != j { 0 } else {
                let p = &mut v[i];
                let q = &mut v[j];
                *p + *q
            }
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        OVERLAP,
    );
    // Shared element references never conflict with each other.
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let xs: [i64; 3] = [1, 2, 3];
            let i = 0;
            let p = &xs[i];
            let q = &xs[0];
            *p + *q
        }"#,
        2,
        "",
    );
}

#[test]
fn established_facts_prove_distinct_indices() {
    // `i != j`, an order, and a loop index with its successor.
    agrees(
        r#"
        fn swap(v: &mut [i64], i: i64, j: i64) -> Unit ! {panic} {
            if i != j {
                let p = &mut v[i];
                let q = &mut v[j];
                let t = *p;
                *p = *q;
                *q = t;
            }
        }
        fn ordered(v: &mut [i64], i: i64, j: i64) -> i64 ! {panic} {
            if i < j {
                let p = &mut v[i];
                let q = &mut v[j];
                *p = *p + *q;
                *p
            } else { 0 }
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut xs: Vec<i64> = [1, 2, 3, 4];
            swap(&mut xs[..], 0, 3);
            swap(&mut xs[..], 2, 2);
            let mut k = 0;
            while k + 1 < 4 {
                let a = &mut xs[k];
                let b = &mut xs[k + 1];
                *a = *a + *b;
                k = k + 1;
            }
            let o = ordered(&mut xs[..], 1, 2) + ordered(&mut xs[..], 2, 1);
            Vec.get(&xs, 0) * 1000 + Vec.get(&xs, 3) * 100 + o
        }"#,
        6000 + 100 + 9,
        "",
    );
    // A reassigned index: the new version differs from the old one.
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let mut i = 0;
            {
                let p = &mut xs[i];
                i = i + 1;
                let q = &mut xs[i];
                *p = 9;
                *q = 8;
            }
            xs[0] * 10 + xs[1]
        }"#,
        98,
        "",
    );
    // Rows of a nested array: the inner indices are distinct even though the
    // row index is unknown.
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut m: [[i64; 2]; 2] = [[1, 2], [3, 4]];
            let i = 1;
            {
                let p = &mut m[i][0];
                let q = &mut m[i][1];
                *p = *p + *q;
            }
            m[1][0]
        }"#,
        7,
        "",
    );
    // Two calls in one expression: arguments are retained together.
    agrees(
        r#"
        fn add(left: &mut i64, right: &mut i64) -> Unit ! {panic} { *left = *left + *right; }
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let i = 0;
            add(&mut xs[i], &mut xs[i + 2]);
            xs[0]
        }"#,
        4,
        "",
    );
    rejects(
        r#"
        fn add(left: &mut i64, right: &mut i64) -> Unit ! {panic} { *left = *left + *right; }
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 3] = [1, 2, 3];
            let i = 0;
            add(&mut xs[i], &mut xs[i * 1]);
            xs[0]
        }"#,
        "",
    );
}

#[test]
fn slice_view_element_references_use_index_facts() {
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            {
                let s: &mut [i64] = &mut xs[..];
                let p = &mut s[0];
                let q = &mut s[3];
                *p = *q;
                *q = 7;
                let n = Slice.len(s);
            }
            xs[0] * 10 + xs[3]
        }"#,
        47,
        "",
    );
    agrees(
        r#"
        fn rotate(s: &mut [i64]) -> Unit ! {panic} {
            let n = Slice.len(s);
            let mut i = 0;
            while i + 1 < n {
                let a = &mut s[i];
                let b = &mut s[i + 1];
                let t = *a;
                *a = *b;
                *b = t;
                i = i + 1;
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut d: DynArray<i64, 4> = [1, 2, 3];
            rotate(&mut d[..]);
            DynArray.get(&d, 0) * 100 + DynArray.get(&d, 1) * 10 + DynArray.get(&d, 2)
        }"#,
        231,
        "",
    );
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let s: &mut [i64] = &mut xs[..];
            let i = 2;
            let p = &mut s[i];
            let q = &mut s[2];
            *p + *q
        }"#,
        OVERLAP,
    );
}

#[test]
fn proofs_never_cross_a_loop_iteration_through_stored_loans() {
    // Iteration k stores `&mut xs[k + 1]` in an outer box; iteration k + 1
    // then borrows `xs[k + 1]` again. Within one iteration `i` and `i + 1`
    // are distinct, but the stored loan is from the previous iteration, so
    // it keeps no index identity and conflicts.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let mut b: Box<&mut i64> = Box.new(&mut xs[3]);
            let mut i = 0;
            while i < 2 {
                let q = &mut xs[i];
                *q = *q + 5;
                Box.set(&mut b, &mut xs[i + 1]);
                i = i + 1;
            }
            let r = Box.take(b);
            *r
        }"#,
        OVERLAP,
    );
    // Regression: a reference stored in a container keeps its owner
    // exclusively borrowed against a new reference to the same element.
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let mut b: Box<&mut i64> = Box.new(&mut xs[0]);
            let q = &mut xs[0];
            *q = 5;
            let r = Box.take(b);
            *r
        }"#,
        OVERLAP,
    );
}

#[test]
fn review_an_exclusive_view_is_not_read_inside_its_own_element_index() {
    // Reading the view inside the index of its own element place is
    // rejected (documented); computing the index first is accepted.
    rejects(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let s: &mut [i64] = &mut xs[..];
            let p = &mut s[Slice.get(s, 0)];
            *p
        }"#,
        "cannot use a slice view while a child view derived from it is live",
    );
    agrees(
        r#"
        fn main() -> i64 ! {panic} {
            let mut xs: [i64; 4] = [1, 2, 3, 4];
            let s: &mut [i64] = &mut xs[..];
            let i = Slice.get(s, 0);
            let p = &mut s[i];
            *p = *p * 10;
            *p
        }"#,
        20,
        "",
    );
}
