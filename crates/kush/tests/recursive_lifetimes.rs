//! Recursive lifetime summaries across direct-call SCCs.
//!
//! These tests exercise the finite may-origin fixed point, all-owner retention,
//! declaration-order and worklist independence, local escape, propagated
//! preconditions, and rigid arrow contracts. Unsupported boundaries and
//! unseeded cycles stay checked rejections.
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
        let binary = scratch.path().join("recursive-lifetime-test");
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

const MUTUAL: &str = r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { a } else { right(a, b, true) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { b } else { left(a, b, true) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(left(&a[..], &b[..], false), 0)
}
"#;

#[test]
fn mutual_recursion_keeps_every_result_owner_and_evaluates_consistently() {
    // `false` selects the recursive branch and then `b`; a path-insensitive
    // summary must still retain both owners.
    agrees(MUTUAL, 3, "");
}

#[test]
fn declaration_order_does_not_change_mutual_summaries() {
    let reversed = r#"
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { b } else { left(a, b, true) }
}
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { a } else { right(a, b, true) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(left(&a[..], &b[..], false), 0)
}
"#;
    agrees(reversed, 3, "");
}

#[test]
fn input_permutation_on_recursive_calls_keeps_all_sources() {
    agrees(
        r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { a } else { right(b, a, true) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { b } else { left(b, a, true) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(left(&a[..], &b[..], false), 0)
}
"#,
        1,
        "",
    );
}

#[test]
fn self_recursion_with_a_base_origin_unions_every_visit() {
    // One visit flips the arguments; the base returns the second lifetime.
    agrees(
        r#"
fn find<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    if n == 0 { a } else { find(b, a, n - 1) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(find(&a[..], &b[..], 1), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn helper_chains_compose_through_a_three_function_cycle() {
    agrees(
        r#"
fn first<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    if n == 0 { a } else { second(a, b, n - 1) }
}
fn second<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    third(a, b, n)
}
fn third<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    if n == 0 { b } else { first(a, b, n - 1) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(first(&a[..], &b[..], 1), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn recursive_record_field_parameters_keep_field_paths() {
    agrees(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn first<'a, 'b>(p: Pair<'a, 'b>, q: Pair<'a, 'b>, n: i64) -> &[i64] ! {panic} {
    if n == 0 { p.left } else { second(q, p, n - 1) }
}
fn second<'a, 'b>(p: Pair<'a, 'b>, q: Pair<'a, 'b>, n: i64) -> &[i64] ! {panic} {
    if n == 0 { q.right } else { first(p, q, n - 1) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    let p = Pair { left: &a[..], right: &b[..] };
    let q = Pair { left: &a[..], right: &b[..] };
    Slice.get(first(p, q, 1), 1)
}
"#,
        4,
        "",
    );
}

#[test]
fn a_local_escape_on_a_recursive_path_stays_rejected() {
    rejects(
        r#"
fn f<'a>(a: &'a [i64], n: i64) -> &[i64] ! {panic} {
    let local: [i64; 2] = [9, 9];
    if n == 0 { a } else { f(&local[..], n - 1) }
}
fn main() -> Unit ! {panic} { let a: [i64; 2] = [1, 2]; let _ = f(&a[..], 2); }
"#,
        "outlive the lexical scope",
    );
}

#[test]
fn a_no_seed_cycle_cannot_manufacture_an_origin_or_equality() {
    let error = check(
        r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    right(a, b, stop)
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    left(a, b, stop)
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("no independently justified result origin"),
        "{error:?}"
    );
    assert!(
        error
            .notes
            .iter()
            .any(|(_, note)| note.contains("recursive call edge 'left' -> 'right'")),
        "{error:?}"
    );
    assert!(
        error
            .notes
            .iter()
            .any(|(_, note)| note.contains("recursive call edge 'right' -> 'left'")),
        "{error:?}"
    );
}

#[test]
fn an_explicit_recursive_contract_is_parametric_forwarding_not_inferred_never() {
    check(
        r#"
fn f<'a>(a: &'a [i64], n: i64) -> &'a [i64] ! {panic} { f(a, n) }
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
    agrees(
        r#"
fn f<'a>(a: &'a [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { f(a, n - 1) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [7, 8];
    Slice.get(f(&a[..], 2), 0)
}
"#,
        7,
        "",
    );
}

#[test]
fn a_recursive_precondition_is_exported_and_checked_at_callers() {
    // `right` returns `b` through an explicit `'a` result, so the SCC exports
    // `b: a`. A caller without that relation is rejected even though the
    // declaration order could have checked the caller header first.
    rejects(
        r#"
fn caller<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
    Slice.get(left(a, b, 1), 0)
}
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { b } else { left(a, b, n - 1) }
}
fn main() -> Unit ! {} {}
"#,
        "cannot establish the callee's outlives constraint 'b: 'a",
    );
    // The same call is accepted when the caller declares the propagated
    // requirement. `caller` is checked eagerly even though `main` never calls
    // it, so this is not a dead-code exemption.
    check(
        r#"
fn caller<'a, 'b: 'a>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
    Slice.get(left(a, b, 1), 0)
}
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { b } else { left(a, b, n - 1) }
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
}

#[test]
fn a_frozen_recursive_contract_cannot_be_silently_strengthened_by_an_arrow() {
    // The recursive SCC infers `b: a`; an unconstrained arrow cannot erase it.
    rejects(
        r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { b } else { left(a, b, n - 1) }
}
fn main() -> Unit ! {panic} {
    let f: fn<'a, 'b>(&'a [i64], &'b [i64], i64) -> &'a [i64] ! {panic} = left;
    let _ = f;
}
"#,
        "type mismatch",
    );
    // Spelling the requirement keeps the exact arrow contract valid.
    check(
        r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { b } else { left(a, b, n - 1) }
}
fn main() -> Unit ! {panic} {
    let f: fn<'a, 'b: 'a>(&'a [i64], &'b [i64], i64) -> &'a [i64] ! {panic} = left;
    let _ = f;
}
"#,
    )
    .unwrap();
}

#[test]
fn an_explicit_boundary_can_seed_an_elided_recursive_cycle() {
    // The elided function has more than one input lifetime, but every result
    // comes from a call whose explicit contract names `'a`. That is a
    // parametric seed, not an unseeded cycle. `annotated` never returns, so
    // this also checks that no `Never` result is inferred.
    check(
        r#"
fn annotated<'a>(a: &'a [i64], n: i64) -> &'a [i64] ! {panic} {
    elided(a, a, n - 1)
}
fn elided<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    annotated(a, n)
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
}

#[test]
fn an_unsupported_recursive_boundary_asks_for_an_explicit_contract() {
    // A direct record-returning call is summarized per field. The same call
    // through an unconstrained function value is an indirect boundary and must
    // not be read as an empty field set.
    rejects(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn make<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn f<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    let g: fn<'a, 'b>(&'a [i64], &'b [i64]) -> Pair<'a, 'b> ! {panic} = make;
    if n == 0 { g(a, b).left } else { f(a, b, n - 1) }
}
fn main() -> Unit ! {} {}
"#,
        "cannot use this result origin",
    );
}

#[test]
fn every_recursive_result_owner_stays_loaned_until_the_last_use() {
    rejects(
        r#"
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { a } else { right(a, b, true) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { b } else { left(a, b, true) }
}
fn main() -> i64 ! {panic} {
    let mut a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    let view = left(&a[..], &b[..], false);
    a = [5, 6];
    Slice.get(view, 0)
}
"#,
        "cannot replace an owner",
    );
}

#[test]
fn mutually_recursive_exclusive_views_keep_their_capabilities() {
    // The result may alias either exclusive view, so both stay loaned and the
    // write through the returned view remains checked.
    agrees(
        r#"
fn left<'a, 'b>(a: &'a mut [i64], b: &'b mut [i64], n: i64) -> &mut [i64] ! {panic} {
    if n == 0 { a } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a mut [i64], b: &'b mut [i64], n: i64) -> &mut [i64] ! {panic} {
    if n == 0 { b } else { left(a, b, n - 1) }
}
fn main() -> i64 ! {panic} {
    let mut a: [i64; 2] = [1, 2];
    let mut b: [i64; 2] = [3, 4];
    let view = left(&mut a[..], &mut b[..], 1);
    Slice.set(view, 0, 9);
    a[1] + b[0]
}
"#,
        11,
        "",
    );
    // A shared view cannot become the exclusive recursive result, even when
    // the recursive branch only forwards the shared parameter.
    rejects(
        r#"
fn bad<'a>(a: &'a [i64], n: i64) -> &mut [i64] ! {panic} {
    if n == 0 { a } else { bad(a, n - 1) }
}
fn main() -> Unit ! {} {}
"#,
        "shared storage cannot be returned mutably",
    );
}

#[test]
fn erased_proof_parameters_do_not_shift_recursive_argument_mapping() {
    // The call keeps the erased proof hole in its AST argument list. A summary
    // origin names runtime parameter 1 (`y`), which must map to source argument
    // 2 (`y`), not to `x` at source position 1.
    agrees(
        r#"
fn second<'a, 'b>(erased p: { 0 == 0 }, x: &'a [i64], y: &'b [i64]) -> &'b [i64] ! {panic} { y }
fn forward<'a, 'b>(x: &'a [i64], y: &'b [i64]) -> &[i64] ! {panic} { second(_, x, y) }
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(forward(&a[..], &b[..]), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn erased_proof_parameters_in_the_middle_keep_source_argument_mapping() {
    agrees(
        r#"
fn second<'a, 'b>(x: &'a [i64], erased p: { 0 == 0 }, y: &'b [i64]) -> &'b [i64] ! {panic} { y }
fn forward<'a, 'b>(x: &'a [i64], y: &'b [i64]) -> &[i64] ! {panic} { second(x, _, y) }
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(forward(&a[..], &b[..]), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn an_acyclic_indirect_result_requires_an_explicit_contract() {
    rejects(
        r#"
fn helper<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} { a }
fn indirect<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    let f: fn<'a, 'b>(&'a [i64], &'b [i64], i64) -> &'a [i64] ! {panic} = helper;
    f(a, b, n)
}
fn main() -> Unit ! {} {}
"#,
        "cannot use this result origin",
    );
}

#[test]
fn an_acyclic_borrowed_record_channel_cannot_become_empty_provenance() {
    // A direct record call is now summarized per field, so its projection is
    // usable. An indirect call through an unconstrained arrow still cannot be
    // read as empty provenance.
    check(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn make<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn unsupported<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &'a [i64] ! {panic} {
    make(a, b).left
}
fn forward<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &[i64] ! {panic} {
    unsupported(a, b)
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
    rejects(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn make<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn unsupported<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &'a [i64] ! {panic} {
    let g: fn<'a, 'b>(&'a [i64], &'b [i64]) -> Pair<'a, 'b> ! {panic} = make;
    g(a, b).left
}
fn forward<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &[i64] ! {panic} {
    unsupported(a, b)
}
fn main() -> Unit ! {} {}
"#,
        "cannot use this result origin",
    );
    // The explicit contract makes the same acyclic boundary usable.
    check(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn make<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn unsupported<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &'a [i64] ! {panic} {
    make(a, b).left
}
fn forward<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> &'a [i64] ! {panic} {
    unsupported(a, b)
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
}

#[test]
fn an_unrelated_explicit_result_call_does_not_seed_a_no_origin_cycle() {
    rejects(
        r#"
fn annotated<'a>(a: &'a [i64]) -> &'a [i64] ! {panic} { a }
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    let local: [i64; 1] = [9];
    let _ = annotated(a);
    if n == 0 { &local[..] } else { right(a, b, n - 1) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
    left(a, b, n)
}
fn main() -> Unit ! {} {}
"#,
        "no independently justified result origin",
    );
}

#[test]
fn statically_resolved_recursive_method_calls_compose_origins() {
    // The receiver is an implicit source argument at position zero; the
    // recursive branch permutes the two slice parameters. Both owners stay in
    // the summary and the evaluator selects the permuted winner.
    agrees(
        r#"
struct Provider { tag: i64 }
impl Provider {
    fn pick<'a, 'b>(self: Provider, a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
        if n == 0 { a } else { self.pick(b, a, n - 1) }
    }
}
fn main() -> i64 ! {panic} {
    let provider = Provider { tag: 0 };
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(provider.pick(&a[..], &b[..], 1), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn a_recursive_method_with_erased_proof_positions_keeps_source_arguments() {
    // The receiver occupies source position zero, so the erased hole after the
    // first runtime argument must still map the selected parameter to `b`, not
    // to the erased position or the receiver.
    agrees(
        r#"
struct Provider { tag: i64 }
impl Provider {
    fn pick<'a, 'b>(
        self: Provider,
        a: &'a [i64],
        erased proof: { 0 == 0 },
        b: &'b [i64],
        n: i64,
    ) -> &'b [i64] ! {panic} {
        if n == 0 { b } else { self.pick(a, _, b, n - 1) }
    }
}
fn main() -> i64 ! {panic} {
    let provider = Provider { tag: 0 };
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(provider.pick(&a[..], _, &b[..], 1), 1)
}
"#,
        4,
        "",
    );
}

#[test]
fn a_static_trait_method_cycle_participates_and_keeps_its_contract() {
    agrees(
        r#"
struct Provider { tag: i64 }
trait Pick {
    fn pick<'a, 'b>(self: Self, a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic};
}
impl Pick for Provider {
    fn pick<'a, 'b>(self: Self, a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
        if n == 0 { b } else { self.pick(a, b, n - 1) }
    }
}
fn main() -> i64 ! {panic} {
    let provider = Provider { tag: 0 };
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(provider.pick(&a[..], &b[..], 1), 0)
}
"#,
        3,
        "",
    );
}

#[test]
fn a_recursive_method_cycle_without_a_base_origin_is_rejected() {
    rejects(
        r#"
struct Provider { tag: i64 }
impl Provider {
    fn chase<'a, 'b>(self: Provider, a: &'a [i64], b: &'b [i64], n: i64) -> &[i64] ! {panic} {
        self.chase(a, b, n)
    }
}
fn main() -> Unit ! {} {}
"#,
        "no independently justified result origin",
    );
}

#[test]
fn borrowed_record_results_keep_a_per_field_summary() {
    // A recursive relay returns a record with two independently borrowed
    // fields. Both field origins survive the call graph, and both owners stay
    // loaned through the record's last use.
    agrees(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn build<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> Pair<'a, 'b> ! {panic} {
    if n == 0 { build(a, b) } else { relay(a, b, n - 1) }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    let pair = relay(&a[..], &b[..], 2);
    Slice.get(pair.left, 1) + Slice.get(pair.right, 0)
}
"#,
        5,
        "",
    );
}

#[test]
fn a_recursive_record_result_keeps_every_owner_loaned() {
    // Reading only `left` must not release the owner of `right`.
    rejects(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn build<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> Pair<'a, 'b> ! {panic} {
    Pair { left: a, right: b }
}
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> Pair<'a, 'b> ! {panic} {
    if n == 0 { build(a, b) } else { relay(a, b, n - 1) }
}
fn main() -> i64 ! {panic} {
    let mut a: [i64; 2] = [1, 2];
    let mut b: [i64; 2] = [3, 4];
    let pair = relay(&a[..], &b[..], 1);
    a = [5, 6];
    b = [7, 8];
    Slice.get(pair.left, 0)
}
"#,
        "cannot replace an owner",
    );
}

#[test]
fn permuted_record_inputs_keep_all_owners_under_one_lifetime() {
    // Both parameters share one declared lifetime, so permuting them retains
    // both origins without inventing an equality. Replacing either owner while
    // the record is live must remain rejected.
    rejects(
        r#"
struct One<'a> { value: &'a [i64] }
fn left<'a>(a: &'a [i64], b: &'a [i64], n: i64) -> One<'a> ! {panic} {
    if n == 0 { One { value: a } } else { right(b, a, n - 1) }
}
fn right<'a>(a: &'a [i64], b: &'a [i64], n: i64) -> One<'a> ! {panic} {
    if n == 0 { One { value: a } } else { left(b, a, n - 1) }
}
fn main() -> i64 ! {panic} {
    let mut a: [i64; 2] = [1, 2];
    let mut b: [i64; 2] = [3, 4];
    let one = left(&a[..], &b[..], 1);
    b = [5, 6];
    Slice.get(one.value, 0)
}
"#,
        "cannot replace an owner",
    );
}

#[test]
fn a_local_record_field_on_a_recursive_path_stays_rejected() {
    rejects(
        r#"
struct Holder<'a> { value: &'a [i64] }
fn chase<'a>(a: &'a [i64], n: i64) -> Holder<'a> ! {panic} {
    let local: [i64; 2] = [9, 9];
    if n == 0 { Holder { value: a } } else { chase(&local[..], n - 1) }
}
fn main() -> Unit ! {} {}
"#,
        "outlive the lexical scope",
    );
}

#[test]
fn a_no_seed_record_cycle_cannot_manufacture_field_origins() {
    rejects(
        r#"
struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> Pair<'a, 'b> ! {panic} {
    right(a, b, stop)
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> Pair<'a, 'b> ! {panic} {
    left(a, b, stop)
}
fn main() -> Unit ! {} {}
"#,
        "no independently justified result origin",
    );
}

#[test]
fn a_recursive_container_write_exports_a_caller_precondition() {
    // `fill` writes `p` into `values` through `Vec.push`, so its body needs
    // `'b: 'a`. The requirement is independent of any returned origin and is
    // exported as R[fill]; the body itself is accepted. The accepted program
    // evaluates identically in the reference evaluator and native backend.
    agrees(
        r#"
struct Point { x: i64, y: i64 }
fn fill<'a, 'b>(values: Vec<&'a Point>, p: &'b Point, n: i64) -> Vec<&'a Point> ! {alloc, panic} {
    if n > 0 { fill(values, p, n - 1) } else { Vec.push(values, p) }
}
fn caller<'a, 'b: 'a>(values: Vec<&'a Point>, p: &'b Point) -> Vec<&'a Point> ! {alloc, panic} {
    fill(values, p, 1)
}
fn main() -> i64 ! {alloc, panic} {
    let p = Point { x: 7, y: 0 };
    let values: Vec<&Point> = [&p];
    let values = caller(values, &p);
    Vec.get(&values, 0).x + Vec.get(&values, 1).x
}
"#,
        14,
        "",
    );
    // A caller that cannot prove the newly inferred requirement is rejected,
    // even though its declaration appears before the recursive callee.
    rejects(
        r#"
struct Point { x: i64, y: i64 }
fn caller<'a, 'b>(values: Vec<&'a Point>, p: &'b Point) -> Vec<&'a Point> ! {alloc, panic} {
    fill(values, p, 1)
}
fn fill<'a, 'b>(values: Vec<&'a Point>, p: &'b Point, n: i64) -> Vec<&'a Point> ! {alloc, panic} {
    if n > 0 { fill(values, p, n - 1) } else { Vec.push(values, p) }
}
fn main() -> Unit ! {} {}
"#,
        "cannot establish the callee's outlives constraint 'b: 'a",
    );
}

#[test]
fn an_explicit_callee_bound_propagates_as_a_recursive_precondition() {
    // `relay` never returns a borrow, but it calls `left`, whose explicit
    // `'b: 'a` contract becomes relay's independent requirement.
    check(
        r#"
fn left<'a, 'b: 'a>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { b }
}
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> i64 ! {panic} {
    if n == 0 { 0 } else { let _ = left(a, b, n - 1); relay(a, b, n - 1) }
}
fn caller<'a, 'b: 'a>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
    relay(a, b, 1)
}
fn main() -> Unit ! {} {}
"#,
    )
    .unwrap();
    rejects(
        r#"
fn left<'a, 'b: 'a>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { b }
}
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> i64 ! {panic} {
    if n == 0 { 0 } else { let _ = left(a, b, n - 1); relay(a, b, n - 1) }
}
fn caller<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
    relay(a, b, 1)
}
fn main() -> Unit ! {} {}
"#,
        "cannot establish the callee's outlives constraint 'b: 'a",
    );
    // The same program with declarations permuted gives the same requirement.
    rejects(
        r#"
fn caller<'a, 'b>(a: &'a [i64], b: &'b [i64]) -> i64 ! {panic} {
    relay(a, b, 1)
}
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> i64 ! {panic} {
    if n == 0 { 0 } else { let _ = left(a, b, n - 1); relay(a, b, n - 1) }
}
fn left<'a, 'b: 'a>(a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
    if n == 0 { a } else { b }
}
fn main() -> Unit ! {} {}
"#,
        "cannot establish the callee's outlives constraint 'b: 'a",
    );
}

#[test]
fn a_frozen_arrow_cannot_erase_a_recursive_container_requirement() {
    rejects(
        r#"
struct Point { x: i64, y: i64 }
fn fill<'a, 'b>(values: Vec<&'a Point>, p: &'b Point, n: i64) -> Vec<&'a Point> ! {alloc, panic} {
    if n > 0 { fill(values, p, n - 1) } else { Vec.push(values, p) }
}
fn main() -> Unit ! {alloc, panic} {
    let f: fn<'a, 'b>(Vec<&'a Point>, &'b Point, i64) -> Vec<&'a Point> ! {alloc, panic} = fill;
    let _ = f;
}
"#,
        "type mismatch",
    );
}

// Regressions from the independent recursive-lifetime soundness review.

#[test]
fn unsupported_relays_converge_independent_of_branch_order() {
    // A recursive call relaying an unsupported channel used to wrap the
    // witness again on every pass, so the fixed point never converged.
    for source in [
        r#"struct H<'a> { view: &'a [i64] }
fn f<'a>(a: &'a [i64], g: fn<'a>(&'a [i64]) -> H<'a> ! {panic}, n: i64) -> H<'a> ! {panic} {
    if n == 0 { f(a, g, n - 1) } else { g(a) }
}
fn main() -> Unit ! {} {}
"#,
        r#"struct H<'a> { view: &'a [i64] }
fn f<'a>(a: &'a [i64], g: fn<'a>(&'a [i64]) -> H<'a> ! {panic}, n: i64) -> H<'a> ! {panic} {
    if n != 0 { g(a) } else { f(a, g, n - 1) }
}
fn main() -> Unit ! {} {}
"#,
    ] {
        rejects(
            source,
            "a call to a non-function or erased definition in result position",
        );
    }
}

#[test]
fn a_generic_receiver_does_not_select_an_unrelated_impl_method() {
    // `id(b).pick(..)` has a receiver typed by a generic binder `A`; it must
    // stay an explicit-contract boundary, never resolve to `A::pick`.
    rejects(
        r#"struct A { tag: i64 }
struct B { tag: i64 }
impl A {
    fn pick<'a, 'b>(self: A, a: &'a [i64], b: &'b [i64], n: i64) -> &'a [i64] ! {panic} {
        if n == 0 { a } else { self.pick(a, b, n - 1) }
    }
}
impl B {
    fn pick<'a, 'b>(self: B, a: &'a [i64], b: &'b [i64], n: i64) -> &'b [i64] ! {panic} {
        if n == 0 { b } else { self.pick(a, b, n - 1) }
    }
}
fn id<A>(x: A) -> A ! {} { x }
fn use_it<'a, 'b>(b: B, a: &'a [i64], bb: &'b [i64], n: i64) -> &[i64] ! {panic} {
    let r = id(b);
    r.pick(a, bb, n)
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    Slice.get(use_it(B { tag: 0 }, &a[..], &b[..], 0), 0)
}
"#,
        "unresolved call in result position",
    );
}

#[test]
fn whole_record_identity_helpers_keep_per_field_owners() {
    agrees(
        r#"struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn id<'a, 'b>(p: Pair<'a, 'b>) -> Pair<'a, 'b> ! {panic} { p }
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> Pair<'a, 'b> ! {panic} {
    if n == 0 {
        Pair { left: a, right: b }
    } else {
        let p = relay(a, b, n - 1);
        id(p)
    }
}
fn main() -> i64 ! {panic} {
    let a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    let pair = relay(&a[..], &b[..], 2);
    Slice.get(pair.left, 1) + Slice.get(pair.right, 0)
}
"#,
        5,
        "",
    );
    rejects(
        r#"struct Pair<'a, 'b> { left: &'a [i64], right: &'b [i64] }
fn id<'a, 'b>(p: Pair<'a, 'b>) -> Pair<'a, 'b> ! {panic} { p }
fn relay<'a, 'b>(a: &'a [i64], b: &'b [i64], n: i64) -> Pair<'a, 'b> ! {panic} {
    if n == 0 {
        Pair { left: a, right: b }
    } else {
        let p = relay(a, b, n - 1);
        id(p)
    }
}
fn main() -> i64 ! {panic} {
    let mut a: [i64; 2] = [1, 2];
    let b: [i64; 2] = [3, 4];
    let pair = relay(&a[..], &b[..], 2);
    a = [9, 9];
    Slice.get(pair.left, 1) + Slice.get(pair.right, 0)
}
"#,
        "cannot replace an owner",
    );
}

#[test]
fn inherent_methods_publish_inferred_container_write_requirements() {
    agrees(
        r#"struct Point { x: i64, y: i64 }
struct Provider { tag: i64 }
impl Provider {
    fn fill<'a, 'b>(self: Provider, values: Vec<&'a Point>, p: &'b Point, n: i64) -> Vec<&'a Point> ! {alloc, panic} {
        if n > 0 { self.fill(values, p, n - 1) } else { Vec.push(values, p) }
    }
}
fn caller<'a, 'b: 'a>(provider: Provider, values: Vec<&'a Point>, p: &'b Point) -> Vec<&'a Point> ! {alloc, panic} {
    provider.fill(values, p, 1)
}
fn main() -> i64 ! {alloc, panic} {
    let p = Point { x: 7, y: 0 };
    let values: Vec<&Point> = [&p];
    let values = caller(Provider { tag: 0 }, values, &p);
    Vec.get(&values, 0).x + Vec.get(&values, 1).x
}
"#,
        14,
        "",
    );
    rejects(
        r#"struct Point { x: i64, y: i64 }
struct Provider { tag: i64 }
impl Provider {
    fn fill<'a, 'b>(self: Provider, values: Vec<&'a Point>, p: &'b Point, n: i64) -> Vec<&'a Point> ! {alloc, panic} {
        if n > 0 { self.fill(values, p, n - 1) } else { Vec.push(values, p) }
    }
}
fn caller<'a, 'b>(provider: Provider, values: Vec<&'a Point>, p: &'b Point) -> Vec<&'a Point> ! {alloc, panic} {
    provider.fill(values, p, 1)
}
fn main() -> i64 ! {alloc, panic} {
    let p = Point { x: 7, y: 0 };
    let values: Vec<&Point> = [&p];
    let values = caller(Provider { tag: 0 }, values, &p);
    Vec.get(&values, 0).x + Vec.get(&values, 1).x
}
"#,
        "cannot establish the callee's outlives constraint 'b: 'a",
    );
}
