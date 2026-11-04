//! Borrowed residual fields in structural rows.
//!
//! The canonical row interning includes each field's erased outer borrow
//! label, and `..r` specialization carries those descriptors through residual
//! inference, callable construction, and impl-header matching. Borrowed
//! structural results remain the next node's boundary: this suite only checks
//! that labels travel through parameters and are not silently erased.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment)
            || error.notes.iter().any(|(_, note)| note.contains(fragment)),
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
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifetime-rowvars-test");
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
}

#[test]
fn direct_structural_annotations_keep_their_borrow_labels() {
    // Before labels were part of the canonical row, the parameter's `view`
    // leaf had no lifetime and the explicit result could not be tied to it.
    agrees(
        r#"fn first<'a>(v: struct { n: i64, view: &'a [i64] }) -> &'a [i64] ! {panic} {
            v.view
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            Slice.get(first(struct { n: 1, view: &values[..] }), 0) + 2
        }"#,
        42,
        "",
    );
    // Rows that differ only in the erased label are distinct checker rows.
    // Converting the shorter view to the longer annotation has no witness.
    rejects(
        r#"fn keep<'long: 'short, 'short>(
            v: struct { view: &'short [i64] }) -> struct { view: &'long [i64] } ! {panic} {
            v
        }
        fn main() -> Unit ! {} {}"#,
        "cannot carry a borrowed field without a declared lifetime",
    );
}

#[test]
fn structural_conversions_cannot_relabel_borrowed_fields() {
    // Retained borrowed fields stay exact: a concrete `'short` source may not
    // be rewritten as `'long` merely because the erased field types match.
    rejects(
        r#"fn keep<'long: 'short, 'short>(v: struct { view: &'short [i64] }) -> Unit ! {panic} {
            let longer: struct { view: &'long [i64] } = v;
            drop(longer);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn row_variable_carries_a_borrowed_residual_through_a_reader() {
    // `read`'s pattern names only `n`; `view` is a residual row field. The
    // residual descriptor keeps `'a`, so the helper can read it and the call
    // retains the owner loan until the row is consumed.
    agrees(
        r#"struct Wide<'a> { n: i64, view: &'a [i64], flag: Bool }
        fn read<r>(v: struct { n: i64, ..r }) -> i64 ! {panic} {
            let n = v.n;
            let value = Slice.get(v.view, 0);
            drop(v);
            n + value
        }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            read(Wide { n: 1, view: view, flag: true }) + 1
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            run(&values[..])
        }"#,
        42,
        "",
    );
}

#[test]
fn several_call_sites_keep_distinct_owner_labels() {
    // Two residual bindings with different labels produce two specializations.
    // Reusing the first call's binder environment for the second would make
    // the shorter `'b` view satisfy `'a`'s (longer) contract.
    agrees(
        r#"struct Wide<'a> { n: i64, view: &'a [i64] }
        fn read<r>(v: struct { n: i64, ..r }) -> i64 ! {panic} {
            v.n + Slice.get(v.view, 0)
        }
        fn run<'long, 'short>(long: &'long [i64], short: &'short [i64]) -> i64 ! {panic} {
            let a = read(Wide { n: 1, view: long });
            let b = read(Wide { n: 1, view: short });
            a + b
        }
        fn main() -> i64 ! {panic} {
            let long: [i64; 2] = [20, 2];
            let short: [i64; 2] = [20, 2];
            run(&long[..], &short[..])
        }"#,
        42,
        "",
    );
}

#[test]
fn repeated_row_variables_require_matching_labels() {
    // The same residual row from every parameter: equal labels bind, distinct
    // labels stay distinct even when the erased field types are identical.
    agrees(
        r#"fn pair<r>(a: struct { x: i64, ..r }, b: struct { x: i64, ..r }) -> i64 ! {panic} {
            a.x + b.x
        }
        fn run<'a>(a: &'a [i64], b: &'a [i64]) -> i64 ! {panic} {
            let first: struct { x: i64, view: &'a [i64] } =
                struct { x: 20, view: a };
            let second: struct { x: i64, view: &'a [i64] } =
                struct { x: 20, view: b };
            pair(first, second)
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 1] = [1];
            let b: [i64; 1] = [2];
            run(&a[..], &b[..]) + 2
        }"#,
        42,
        "",
    );
    rejects(
        r#"fn pair<r>(a: struct { x: i64, ..r }, b: struct { x: i64, ..r }) -> i64 ! {panic} {
            a.x + b.x
        }
        fn run<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
            let first: struct { x: i64, view: &'a [i64] } =
                struct { x: 20, view: a };
            let second: struct { x: i64, view: &'b [i64] } =
                struct { x: 20, view: b };
            pair(first, second)
        }
        fn main() -> Unit ! {} {}"#,
        "residual row",
    );
}

#[test]
fn impl_rows_keep_borrowed_residual_labels() {
    // The impl header names only `n`; `view` arrives through `..r`. The method
    // result's elided lifetime can only be inferred when the specialized
    // `Self` row retained the annotation label.
    agrees(
        r#"impl<r> struct { n: i64, ..r } {
            fn first(self: Self) -> &[i64] ! {panic} { self.view }
        }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            let v: struct { n: i64, view: &'a [i64] } = struct { n: 1, view: view };
            Slice.get(v.first(), 0)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            run(&values[..]) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn owner_mutation_and_drop_while_a_residual_borrow_is_live_are_rejected() {
    rejects(
        r#"struct Wide<'a> { n: i64, view: &'a [i64] }
        fn read<r>(v: struct { n: i64, ..r }, values: &mut Vec<i64>) -> i64 ! {alloc, panic} {
            Vec.clear(values);
            Slice.get(v.view, 0)
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [1, 2];
            read(Wide { n: 1, view: &data[..] }, &mut data)
        }"#,
        "exclusive",
    );
    rejects(
        r#"struct Wide<'a> { n: i64, view: &'a [i64] }
        fn read<r>(v: struct { n: i64, ..r }) -> i64 ! {panic} {
            Slice.get(v.view, 0)
        }
        fn main() -> i64 ! {alloc, panic} {
            let data: Vec<i64> = [1, 2];
            let row = Wide { n: 1, view: &data[..] };
            drop(data);
            read(row)
        }"#,
        "cannot move or drop",
    );
}

#[test]
fn residual_paths_are_rebased_for_reordered_sources() {
    // `view` is source field 3 and `n` is source field 2; the canonical
    // residual row reorders them with the owning `extra` and `flag` fields.
    // Reading the view must use the target mapping, not the source index.
    agrees(
        r#"struct Wide<'a> { extra: Box<i64>, flag: Bool, n: i64, view: &'a [i64] }
        fn read<r>(v: struct { n: i64, ..r }) -> i64 ! {panic} {
            let flag = v.flag;
            let n = v.n;
            let value = Slice.get(v.view, 3);
            drop(v);
            if flag { 0 } else { n + value }
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 4] = [0, 1, 2, 40];
            let row = Wide {
                extra: Box.new(1),
                flag: false,
                n: 1,
                view: &values[..],
            };
            read(row) + 1
        }"#,
        42,
        "",
    );
}

#[test]
fn borrowed_structural_results_remain_rejected() {
    // A direct structural result and a row-variable result both stay outside
    // the initial fragment even though the specialization now carries `'a`.
    rejects(
        r#"fn keep<'a>(v: struct { view: &'a [i64], n: i64 })
            -> struct { view: &'a [i64], n: i64 } ! {panic} { v }
        fn main() -> Unit ! {} {}"#,
        "cannot carry a borrowed field without a declared lifetime",
    );
    rejects(
        r#"struct Wide<'a> { n: i64, view: &'a [i64] }
        fn keep<r>(v: struct { n: i64, ..r })
            -> struct { n: i64, ..r } ! {panic} { v }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            let v: struct { n: i64, view: &'a [i64] } = struct { n: 1, view: view };
            let _ = keep(v);
            0
        }
        fn main() -> i64 ! {panic} { 0 }"#,
        "cannot carry a borrowed field without a declared lifetime",
    );
}

#[test]
fn structural_call_instantiates_callee_lifetime() {
    agrees(
        r#"fn read<'a>(v: struct { view: &'a [i64] }) -> i64 ! {panic} { Slice.get(v.view, 0) }
        fn caller<'b>(x: &'b [i64]) -> i64 ! {panic} {
            let row: struct { view: &'b [i64] } = struct { view: x };
            read(row)
        }
        fn main() -> i64 ! {panic} { let x: [i64; 1] = [42]; caller(&x[..]) }"#,
        42,
        "",
    );
}

#[test]
fn structural_calls_have_separate_lifetime_instantiations() {
    agrees(
        r#"fn read<'a>(v: struct { view: &'a [i64] }) -> i64 ! {panic} { Slice.get(v.view, 0) }
        fn caller<'b, 'c>(x: &'b [i64], y: &'c [i64]) -> i64 ! {panic} {
            let first: struct { view: &'b [i64] } = struct { view: x };
            let second: struct { view: &'c [i64] } = struct { view: y };
            read(first) + read(second)
        }
        fn main() -> i64 ! {panic} {
            let x: [i64; 1] = [20]; let y: [i64; 1] = [22]; caller(&x[..], &y[..])
        }"#,
        42,
        "",
    );
    rejects(
        r#"fn pair<'a>(x: struct { view: &'a [i64] }, y: struct { view: &'a [i64] }) -> Unit ! {panic} {}
        fn caller<'b, 'c>(x: struct { view: &'b [i64] }, y: struct { view: &'c [i64] }) -> Unit ! {panic} {
            pair(x, y)
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn unlabelled_annotation_preserves_retained_borrow_label() {
    rejects(
        r#"fn keep<'long: 'short, 'short>(v: struct { view: &'short [i64] }) -> Unit ! {panic} {
            let unlabeled: struct { view: &[i64] } = v;
            let longer: struct { view: &'long [i64] } = unlabeled;
            drop(longer);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn residual_caller_lifetime_does_not_capture_same_named_callee_binder() {
    agrees(
        r#"fn inspect<'a,r>(v: struct { x: &'a [i64], ..r }) -> i64 ! {panic} {
            Slice.get(v.x, 0) + Slice.get(v.y, 0)
        }
        fn caller<'a,'b>(v: struct { x: &'b [i64], y: &'a [i64] }) -> i64 ! {panic} {
            inspect(v)
        }
        fn main() -> i64 ! {panic} {
            let x: [i64; 1] = [20];
            let y: [i64; 1] = [22];
            caller(struct { x: &x[..], y: &y[..] })
        }"#,
        42,
        "",
    );
}

#[test]
fn same_named_callee_binder_still_requires_one_invariant_identity() {
    rejects(
        r#"fn inspect<'a,r>(v: struct { x: &'a [i64], z: &'a [i64], ..r }) -> i64 ! {panic} {
            Slice.get(v.x, 0) + Slice.get(v.y, 0) + Slice.get(v.z, 0)
        }
        fn caller<'a,'b>(v: struct { x: &'b [i64], y: &'a [i64], z: &'a [i64] }) -> i64 ! {panic} {
            inspect(v)
        }
        fn main() -> Unit ! {} {}"#,
        "invariantly from several argument lifetimes",
    );
}
