//! Borrowed fields in anonymous structural record results.
//!
//! A structural row now carries the declared (or checked inferred) label of
//! each direct borrowed field. A function may return such a row only when every
//! borrowed leaf names a lifetime carried by a caller-owned parameter, and the
//! ownership pass keeps every possible origin loaned until the result's last
//! use.
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
        use kush::native::{CodegenOptions, LinkSpec, Optimization};
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let modes = [
            (
                "default",
                CodegenOptions {
                    optimization: Optimization::None,
                    inline_scalar_callbacks: false,
                },
            ),
            ("release", CodegenOptions::release()),
        ];
        for (at, (mode, options)) in modes.into_iter().enumerate() {
            let binary = scratch.path().join(format!("lifetime-struct-results-{at}"));
            kush::native::build_with_codegen(
                &program,
                &binary,
                true,
                &LinkSpec::default(),
                options,
            )
            .unwrap();
            let output = std::process::Command::new(&binary).output().unwrap();
            assert_eq!(
                output.status.code(),
                Some((expected_status as u64 & 255) as i32),
                "{mode}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                expected_output,
                "{mode}: {source}"
            );
            let stderr = String::from_utf8(output.stderr).unwrap();
            let line = stderr
                .lines()
                .find(|line| line.starts_with("allocation-stats: "))
                .unwrap_or_else(|| {
                    panic!("{mode}: missing native allocation diagnostics: {stderr:?}")
                });
            assert_eq!(line, stats.report(), "{mode}: {source}");
        }
    }
}

#[test]
fn named_slice_parameter_returns_in_a_labelled_structural_field() {
    agrees(
        r#"fn first<'a>(v: &'a [i64]) -> struct { n: i64, view: &'a [i64] } ! {panic} {
            struct { n: 1, view: v }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = first(&values[..]);
            Slice.get(out.view, 0) + out.n + 1
        }"#,
        42,
        "",
    );
}

#[test]
fn nominal_borrowed_input_narrows_into_a_structural_result() {
    agrees(
        r#"struct Wide<'a> { n: i64, view: &'a [i64], flag: Bool }
        fn narrow<'a>(w: Wide<'a>) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: w.view }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = narrow(Wide { n: 1, view: &values[..], flag: true });
            Slice.get(out.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn nested_structural_fields_keep_distinct_input_lifetimes() {
    agrees(
        r#"fn pair<'a, 'b>(left: &'a [i64], right: &'b [i64])
            -> struct { inner: struct { left: &'a [i64], right: &'b [i64] } } ! {panic} {
            struct { inner: struct { left: left, right: right } }
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 1] = [40];
            let b: [i64; 1] = [2];
            let out = pair(&a[..], &b[..]);
            Slice.get(out.inner.left, 0) + Slice.get(out.inner.right, 0)
        }"#,
        42,
        "",
    );
}

#[test]
fn row_variable_identity_returns_the_same_borrowed_row() {
    agrees(
        r#"fn keep<r>(v: struct { n: i64, ..r }) -> struct { n: i64, ..r } ! {panic} { v }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            let row: struct { n: i64, view: &'a [i64] } = struct { n: 1, view: view };
            let out = keep(row);
            Slice.get(out.view, 0) + out.n + 1
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
fn row_variable_helper_keeps_each_call_sites_owner_labels() {
    // Two specializations of the same row-variable identity helper. The first
    // call's `'a` binder must not leak into the second call's `'b` result, and
    // each result keeps its own owner loaned until its last use.
    agrees(
        r#"struct Row<'a> { n: i64, view: &'a [i64] }
        fn keep<r>(v: struct { n: i64, ..r }) -> struct { n: i64, ..r } ! {panic} {
            let _ = v.n;
            v
        }
        fn run<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
            let first = keep(Row { n: 20, view: a });
            let second = keep(Row { n: 20, view: b });
            Slice.get(first.view, 0) + Slice.get(second.view, 0) + 2
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 1] = [20];
            let b: [i64; 1] = [20];
            run(&a[..], &b[..])
        }"#,
        42,
        "",
    );
}

#[test]
fn reordered_width_conversion_keeps_only_the_named_roots() {
    // `view` is source field 3 and `n` is source field 2. The result row is
    // canonical `n, view`; the coercion must map the surviving borrow to its
    // actual source owner while dropping `extra` (owning) and `flag`.
    agrees(
        r#"struct Wide<'a> { extra: Box<i64>, flag: Bool, n: i64, view: &'a [i64] }
        fn narrow<'a>(w: Wide<'a>) -> struct { view: &'a [i64], n: i64 } ! {alloc, panic} {
            struct { view: w.view, n: w.n }
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 4] = [0, 1, 2, 40];
            let w = Wide { extra: Box.new(1), flag: false, n: 1, view: &values[..] };
            let out = narrow(w);
            Slice.get(out.view, 3) + out.n + 1
        }"#,
        42,
        "",
    );
}

#[test]
fn branch_and_loop_selected_origins_are_all_retained() {
    agrees(
        r#"fn pick<'a>(flag: Bool, left: &'a [i64], right: &'a [i64])
            -> struct { view: &'a [i64] } ! {panic} {
            if flag { struct { view: left } } else { struct { view: right } }
        }
        fn spin<'a>(stop: Bool, view: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            loop {
                if stop { break struct { view: view } }
            }
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 1] = [40];
            let b: [i64; 1] = [2];
            let left = pick(true, &a[..], &b[..]);
            let right = pick(false, &a[..], &b[..]);
            let looped = spin(true, &a[..]);
            if Slice.get(left.view, 0) == 40 {
                Slice.get(right.view, 0) + Slice.get(looped.view, 0)
            } else {
                0
            }
        }"#,
        42,
        "",
    );
}

#[test]
fn helper_results_compose_through_structural_results() {
    agrees(
        r#"fn inner<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: v }
        }
        fn outer<'a>(v: &'a [i64]) -> struct { nested: struct { view: &'a [i64] } } ! {panic} {
            let row = inner(v);
            struct { nested: row }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = outer(&values[..]);
            Slice.get(out.nested.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn helper_structural_result_projection_follows_the_projected_source() {
    // `wrap(a).view` keeps only `'a` as a possible source. `'b`'s owner is
    // therefore free to be mutated while the projected result is still live.
    agrees(
        r#"fn wrap<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: v }
        }
        fn project<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &[i64] ! {panic} {
            wrap(a).view
        }
        fn main() -> i64 ! {alloc, panic} {
            let a: Vec<i64> = [40, 2];
            let mut b: Vec<i64> = [3, 4];
            let out = project(&a[..], &b[..]);
            Vec.clear(&mut b);
            Slice.get(out, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn a_projected_helper_source_keeps_its_own_owner_loaned() {
    rejects(
        r#"fn wrap<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: v }
        }
        fn project<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &[i64] ! {panic} {
            wrap(a).view
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: Vec<i64> = [40, 2];
            let b: Vec<i64> = [3, 4];
            let out = project(&a[..], &b[..]);
            Vec.clear(&mut a);
            Slice.get(out, 0)
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn wrap<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: v }
        }
        fn project<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &[i64] ! {panic} {
            wrap(a).view
        }
        fn main() -> i64 ! {alloc, panic} {
            let a: Vec<i64> = [40, 2];
            let b: Vec<i64> = [3, 4];
            let out = project(&a[..], &b[..]);
            drop(a);
            Slice.get(out, 0)
        }"#,
        "cannot move or drop",
    );
}

#[test]
fn nested_structural_row_arguments_instantiate_the_callee_label() {
    // The callee's `'a` is instantiated from the caller's `'b` even though the
    // borrowed view is one nested row below the parameter's direct fields.
    agrees(
        r#"fn inner<'a>(v: struct { w: struct { view: &'a [i64] } })
            -> struct { view: &'a [i64] } ! {panic} { v.w }
        fn relay<'b>(v: &'b [i64]) -> struct { view: &'b [i64] } ! {panic} {
            inner(struct { w: struct { view: v } })
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = relay(&values[..]);
            Slice.get(out.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn a_nested_row_argument_result_keeps_the_caller_owner_loaned() {
    rejects(
        r#"fn inner<'a>(v: struct { w: struct { view: &'a [i64] } })
            -> struct { view: &'a [i64] } ! {panic} { v.w }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [1, 2];
            let out = inner(struct { w: struct { view: &data[..] } });
            Vec.clear(&mut data);
            Slice.get(out.view, 0)
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn inner<'a>(v: struct { w: struct { view: &'a [i64] } })
            -> struct { view: &'a [i64] } ! {panic} { v.w }
        fn main() -> i64 ! {alloc, panic} {
            let data: Vec<i64> = [1, 2];
            let out = inner(struct { w: struct { view: &data[..] } });
            drop(data);
            Slice.get(out.view, 0)
        }"#,
        "cannot move or drop",
    );
}

#[test]
fn a_local_backed_nested_row_argument_cannot_escape() {
    rejects(
        r#"fn inner<'a>(v: struct { w: struct { view: &'a [i64] } })
            -> struct { view: &'a [i64] } ! {panic} { v.w }
        fn bad<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            let local: [i64; 1] = [1];
            inner(struct { w: struct { view: &local[..] } })
        }
        fn main() -> Unit ! {} {}"#,
        "outlive the lexical scope",
    );
}

#[test]
fn nested_structural_row_labels_stay_exact_at_call_sites() {
    rejects(
        r#"fn pair<'a>(
            x: struct { w: struct { view: &'a [i64] } },
            y: struct { w: struct { view: &'a [i64] } },
        ) -> Unit ! {panic} {}
        fn caller<'b, 'c>(x: &'b [i64], y: &'c [i64]) -> Unit ! {panic} {
            let first: struct { w: struct { view: &'b [i64] } } =
                struct { w: struct { view: x } };
            let second: struct { w: struct { view: &'c [i64] } } =
                struct { w: struct { view: y } };
            pair(first, second)
        }
        fn main() -> Unit ! {} {}"#,
        "invariantly from several argument lifetimes",
    );
    rejects(
        r#"fn inner<'a>(v: struct { w: struct { view: &'a [i64] } })
            -> struct { view: &'a [i64] } ! {panic} { v.w }
        fn bad<'b, 'c>(v: &'b [i64]) -> struct { view: &'c [i64] } ! {panic} {
            inner(struct { w: struct { view: v } })
        }
        fn main() -> Unit ! {} {}"#,
        "does not appear on any parameter that outlives it",
    );
}

#[test]
fn exclusive_structural_result_comes_from_an_exclusive_input() {
    agrees(
        r#"fn keep<'a>(v: &'a mut [i64]) -> struct { view: &'a mut [i64] } ! {panic} {
            struct { view: v }
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [40, 2];
            let out = keep(&mut values[..]);
            let struct { view } = out;
            Slice.get(view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn unlabelled_structural_result_field_uses_the_single_input_lifetime() {
    agrees(
        r#"fn first<'a>(v: &'a [i64]) -> struct { n: i64, view: &[i64] } ! {panic} {
            struct { n: 1, view: v }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = first(&values[..]);
            Slice.get(out.view, 0) + out.n + 1
        }"#,
        42,
        "",
    );
}

#[test]
fn caller_mutation_or_drop_while_the_result_is_live_is_rejected() {
    // The returned row's field keeps the caller's `data` loaned, exactly like a
    // directly returned slice.
    rejects(
        r#"fn keep<'a>(v: struct { n: i64, view: &'a [i64] })
            -> struct { n: i64, view: &'a [i64] } ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [1, 2];
            let out = keep(struct { n: 1, view: &data[..] });
            Vec.clear(&mut data);
            Slice.get(out.view, 0)
        }"#,
        "exclusive",
    );
    rejects(
        r#"fn keep<'a>(v: struct { n: i64, view: &'a [i64] })
            -> struct { n: i64, view: &'a [i64] } ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let data: Vec<i64> = [1, 2];
            let out = keep(struct { n: 1, view: &data[..] });
            drop(data);
            Slice.get(out.view, 0)
        }"#,
        "cannot move or drop",
    );
}

#[test]
fn local_storage_behind_a_result_field_annotation_is_rejected() {
    // The annotation names a caller lifetime, but the actual field is a stack
    // local; the annotation is not evidence of the value's origin.
    rejects(
        r#"fn bad<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            let local: [i64; 1] = [1];
            struct { view: &local[..] }
        }
        fn main() -> Unit ! {} {}"#,
        "outlive the lexical scope",
    );
}

#[test]
fn a_temporary_structural_field_cannot_escape() {
    rejects(
        r#"fn values() -> [i64; 1] ! {panic} { [1] }
        fn bad<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: &values()[..] }
        }
        fn main() -> Unit ! {} {}"#,
        "bind the owner to a local first",
    );
}

#[test]
fn a_block_local_structural_row_cannot_escape() {
    rejects(
        r#"fn bad<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            let row = {
                let local: [i64; 1] = [1];
                struct { view: &local[..] }
            };
            row
        }
        fn main() -> Unit ! {} {}"#,
        "outlive the lexical scope",
    );
}

#[test]
fn shared_storage_cannot_become_an_exclusive_structural_field() {
    rejects(
        r#"fn bad<'a>(v: &'a [i64]) -> struct { view: &'a mut [i64] } ! {panic} {
            struct { view: v }
        }
        fn main() -> Unit ! {} {}"#,
        "exclusive borrowed record result",
    );
}

#[test]
fn duplicate_mutable_structural_fields_are_rejected() {
    rejects(
        r#"fn dup<'a>(v: &'a mut [i64])
            -> struct { a: &'a mut [i64], b: &'a mut [i64] } ! {panic} {
            struct { a: v, b: v }
        }
        fn main() -> Unit ! {} {}"#,
        "move",
    );
    rejects(
        r#"fn dup<'a>(v: &'a mut [i64])
            -> struct { a: &'a mut [i64], b: &'a mut [i64] } ! {panic} {
            let a = &mut v[..];
            let b = &mut v[..];
            struct { a: a, b: b }
        }
        fn main() -> Unit ! {} {}"#,
        "exclusive",
    );
}

#[test]
fn a_shared_field_cannot_alias_a_returned_exclusive_field() {
    rejects(
        r#"fn dup<'a>(v: &'a mut [i64])
            -> struct { a: &'a mut [i64], b: &'a [i64] } ! {panic} {
            let a = &mut v[..];
            let b = &v[..];
            struct { a: a, b: b }
        }
        fn main() -> Unit ! {} {}"#,
        "exclusive",
    );
}

#[test]
fn unrecoverable_elision_is_an_explicit_rejection() {
    rejects(
        r#"fn bad<'a, 'b>(v: &'a [i64], w: &'b [i64]) -> struct { view: &[i64] } ! {panic} {
            struct { view: v }
        }
        fn main() -> Unit ! {} {}"#,
        "cannot recover the lifetime of an elided structural result field",
    );
    rejects(
        r#"fn bad() -> struct { view: &[i64] } ! {panic} {
            let values: [i64; 1] = [1];
            struct { view: &values[..] }
        }
        fn main() -> Unit ! {} {}"#,
        "no borrowed input to infer it from",
    );
}

#[test]
fn a_result_label_that_no_parameter_carries_is_rejected() {
    rejects(
        r#"fn bad<'a, 'b>(v: &'a [i64]) -> struct { view: &'b [i64] } ! {panic} {
            struct { view: v }
        }
        fn main() -> Unit ! {} {}"#,
        "does not appear on any parameter that outlives it",
    );
}

#[test]
fn direct_structural_owner_reference_results_stay_rejected() {
    rejects(
        r#"fn bad<'a>(v: &'a Vec<i64>) -> struct { owner: &'a Vec<i64> } ! {panic} {
            struct { owner: v }
        }
        fn main() -> Unit ! {} {}"#,
        "cannot store an owner reference",
    );
}

#[test]
fn a_longer_input_lifetime_shortens_into_the_result_label() {
    // The declared field label is an obligation: a caller-owned source whose
    // lifetime outlives it satisfies the result, exactly like a direct slice.
    agrees(
        r#"fn shorten<'long: 'short, 'short>(v: &'long [i64]) -> struct { view: &'short [i64] } ! {panic} {
            struct { view: v }
        }
        fn run<'a>(v: &'a [i64]) -> i64 ! {panic} {
            let out = shorten(v);
            Slice.get(out.view, 0) + 2
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
fn a_branch_that_returns_a_short_lifetime_is_rejected() {
    // Every alternative is checked: the second branch's `'b` owner cannot
    // satisfy the result field's `'a` obligation even when the first branch
    // would.
    rejects(
        r#"fn bad<'a, 'b>(flag: Bool, v: &'a [i64], w: &'b [i64])
            -> struct { view: &'a [i64] } ! {panic} {
            if flag { struct { view: v } } else { struct { view: w } }
        }
        fn main() -> Unit ! {} {}"#,
        "does not satisfy the declared result lifetime",
    );
}

#[test]
fn owner_mutation_is_rejected_when_any_branch_may_have_selected_it() {
    // Both owners are possible origins of the result. The checker must keep
    // both loaned, not only the branch selected at runtime.
    rejects(
        r#"fn pick<'a>(flag: Bool, left: &'a [i64], right: &'a [i64])
            -> struct { view: &'a [i64] } ! {panic} {
            if flag { struct { view: left } } else { struct { view: right } }
        }
        fn main() -> i64 ! {alloc, panic} {
            let mut a: Vec<i64> = [1, 2];
            let mut b: Vec<i64> = [3, 4];
            let out = pick(true, &a[..], &b[..]);
            Vec.clear(&mut b);
            Slice.get(out.view, 0)
        }"#,
        "exclusive",
    );
}

#[test]
fn nested_container_leaves_keep_their_owner_loan() {
    agrees(
        r#"struct Wide<'a> { n: i64, view: &'a [i64] }
        fn wrap<'a>(rows: Vec<Wide<'a>>) -> struct { rows: Vec<Wide<'a>> } ! {alloc, panic} {
            struct { rows: rows }
        }
        fn run<'a>(view: &'a [i64]) -> i64 ! {alloc, panic} {
            let rows: Vec<Wide<'a>> = [Wide { n: 1, view: view }];
            let out = wrap(rows);
            let first = Vec.get(&out.rows, 0);
            Slice.get(first.view, 0) + 2
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [40, 2];
            run(&values[..])
        }"#,
        42,
        "",
    );
}

#[test]
fn indirect_helper_composition_keeps_the_result_lifetime() {
    agrees(
        r#"fn identity<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            struct { view: v }
        }
        fn apply<'a>(f: fn<'a>(&'a [i64]) -> struct { view: &'a [i64] } ! {panic}, v: &'a [i64])
            -> struct { view: &'a [i64] } ! {panic} {
            f(v)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = apply(identity, &values[..]);
            Slice.get(out.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn a_structural_row_nested_in_a_nominal_result_keeps_its_loan() {
    // The old blanket gate also covered structural rows nested behind a
    // nominal record. Its field label is substituted from the nominal
    // lifetime argument and checked through the same leaf path.
    agrees(
        r#"struct Holder<'a> { inner: struct { view: &'a [i64] } }
        fn hold<'a>(v: &'a [i64]) -> Holder<'a> ! {panic} {
            Holder { inner: struct { view: v } }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = hold(&values[..]);
            Slice.get(out.inner.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn an_impl_row_method_returns_its_specialized_borrowed_row() {
    agrees(
        r#"impl<r> struct { n: i64, ..r } {
            fn keep(self: Self) -> struct { n: i64, ..r } ! {panic} {
                let _ = self.n;
                self
            }
        }
        fn run<'a>(view: &'a [i64]) -> i64 ! {panic} {
            let row: struct { n: i64, view: &'a [i64] } = struct { n: 1, view: view };
            let out = row.keep();
            Slice.get(out.view, 0) + out.n + 1
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
fn an_owner_is_released_after_the_results_last_use() {
    // The loan lasts until the result's checked last use, not to scope end.
    agrees(
        r#"fn keep<'a>(v: struct { n: i64, view: &'a [i64] })
            -> struct { n: i64, view: &'a [i64] } ! {panic} { v }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: Vec<i64> = [40, 2];
            let out = keep(struct { n: 1, view: &data[..] });
            let value = Slice.get(out.view, 0);
            Vec.clear(&mut data);
            value + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn elision_uses_an_elided_inputs_checked_identity() {
    // A single elided input borrow supplies the fresh checked identity for an
    // elided result field, exactly like a directly returned elided slice.
    agrees(
        r#"fn first(v: &[i64]) -> struct { n: i64, view: &[i64] } ! {panic} {
            struct { n: 1, view: v }
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = first(&values[..]);
            Slice.get(out.view, 0) + out.n + 1
        }"#,
        42,
        "",
    );
}

#[test]
fn an_elided_helper_result_reacquires_a_labelled_annotation() {
    agrees(
        r#"fn first<'a>(v: &'a [i64]) -> struct { view: &[i64] } ! {panic} {
            struct { view: v }
        }
        fn second<'a>(v: &'a [i64]) -> struct { view: &'a [i64] } ! {panic} {
            first(v)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let out = second(&values[..]);
            Slice.get(out.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn an_arrow_result_field_must_name_an_arrow_lifetime() {
    rejects(
        r#"fn bad(f: fn<'a>(&'a [i64]) -> struct { view: &[i64] } ! {panic}) -> Unit ! {panic} {}
        fn main() -> Unit ! {} {}"#,
        "must name a lifetime bound by the arrow itself",
    );
}

#[test]
fn a_structural_row_behind_an_owned_container_keeps_its_label() {
    agrees(
        r#"fn build<'a>(v: &'a [i64]) -> Box<struct { view: &'a [i64] }> ! {alloc, panic} {
            Box.new(struct { view: v })
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [40, 2];
            let out = build(&values[..]);
            let inner = Box.take(out);
            Slice.get(inner.view, 0) + 2
        }"#,
        42,
        "",
    );
}

#[test]
fn an_elided_helper_result_cannot_be_relabelled_to_another_input() {
    rejects(
        r#"fn first<'a>(v: &'a [i64]) -> struct { view: &[i64] } ! {panic} {
            struct { view: v }
        }
        fn leak<'x, 'y>(a: &'x [i64], b: &'y [i64]) -> struct { view: &'y [i64] } ! {panic} {
            first(a)
        }
        fn main() -> Unit ! {} {}"#,
        "does not satisfy the declared result lifetime",
    );
}

#[test]
fn owning_metadata_in_a_structural_result_is_cleaned_up() {
    agrees(
        r#"fn build<'a>(v: &'a [i64], extra: Box<i64>) -> struct { extra: Box<i64>, view: &'a [i64] } ! {alloc, panic} {
            struct { extra: extra, view: v }
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: [i64; 2] = [40, 2];
            let out = build(&values[..], Box.new(1));
            let struct { extra, view } = out;
            Slice.get(view, 0) + Box.take(extra) + 1
        }"#,
        42,
        "",
    );
}
