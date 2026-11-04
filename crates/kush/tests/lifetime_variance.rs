//! Lifetime-only variance: seeded declaration tables, contextual conversion,
//! invariant constructor positions, callable occurrence environments, and
//! owner-provenance preservation.
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

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifetime-variance-test");
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

#[test]
fn by_value_shortening_is_covariant_and_extension_needs_a_proof() {
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn shorten<'long: 'short, 'short>(window: Window<'long>) -> Window<'short> ! {panic} {
            window
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            let window = Window { view: &values[..], start: 0 };
            Slice.get(shorten(window).view, 0)
        }"#,
        40,
        "",
    );
    // The reverse direction has no established outlives edge. Erased shape is
    // not evidence, so the conversion must be rejected.
    rejects(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn extend<'long: 'short, 'short>(window: Window<'short>) -> Window<'long> ! {panic} {
            window
        }
        fn main() -> Unit ! {} {}"#,
        "does not appear on any parameter",
    );
}

#[test]
fn invariant_mutable_pointee_positions_require_identity() {
    // `&mut` makes its pointee invariant even when the inner record's lifetime
    // parameter is otherwise covariant. The table therefore reports the
    // `Holder` parameter invariant.
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        struct Holder<'a> { slot: &'a mut Box<Window<'a>> }
        fn identity<'a>(holder: Holder<'a>) -> Holder<'a> ! {panic} {
            holder
        }
        fn main() -> Unit ! {} {}"#,
        0,
        "",
    );
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        struct Holder<'a> { slot: &'a mut Box<Window<'a>> }
        fn shorten<'long: 'short, 'short>(holder: Holder<'long>) -> Holder<'short> ! {panic} {
            holder
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn callable_arrow_direction_and_alpha_equivalence_are_preserved() {
    // Alpha-equivalent arrow labels map positionally, including a many-to-one
    // source contract that the target can instantiate.
    agrees(
        r#"fn second<'long: 'short, 'short>(first: &'long [i64], second: &'short [i64]) -> &'short [i64] ! {panic} {
            second
        }
        fn apply(f: fn<'a>(&'a [i64], &'a [i64]) -> &'a [i64] ! {panic}, values: &[i64]) -> i64 ! {panic} {
            Slice.get(f(values, values), 0)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            apply(second, &values[..])
        }"#,
        40,
        "",
    );
    // A source contract that returns its second parameter does not fit an
    // arrow whose result is tied to the first parameter.
    rejects(
        r#"fn install(f: fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'a [i64] ! {panic}) -> Unit ! {} {
            let _ = f;
        }
        fn second<'a, 'b>(first: &'a [i64], second: &'b [i64]) -> &'b [i64] ! {panic} {
            second
        }
        fn main() -> Unit ! {} {
            install(second);
        }"#,
        "type mismatch",
    );
}

#[test]
fn anonymous_intersections_and_elision_still_work() {
    agrees(
        r#"fn pick<'a, 'b>(left: &'a [i64], right: &'b [i64], first: i64) -> &[i64] ! {panic} {
            if first == 0 { left } else { right }
        }
        fn main() -> i64 ! {panic} {
            let a: [i64; 2] = [40, 1];
            let b: [i64; 2] = [2, 3];
            Slice.get(pick(&a[..], &b[..], 0), 0)
        }"#,
        40,
        "",
    );
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn first<'a>(window: Window<'a>) -> &'a [i64] ! {panic} { window.view }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [9, 8];
            Slice.get(first(Window { view: &values[..] }), 0)
        }"#,
        9,
        "",
    );
}

#[test]
fn shortening_keeps_every_source_owner_loaned() {
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn shorten<'long: 'short, 'short>(window: Window<'long>) -> Window<'short> ! {panic} {
            window
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [40, 1];
            let window = shorten(Window { view: &values[..] });
            let first = Slice.get(window.view, 0);
            values = [9, 9];
            first + Slice.get(window.view, 1)
        }"#,
        "replace an owner",
    );
    agrees(
        r#"struct Window<'a> { view: &'a [i64] }
        fn shorten<'long: 'short, 'short>(window: Window<'long>) -> Window<'short> ! {panic} {
            window
        }
        fn main() -> i64 ! {panic} {
            let mut values: [i64; 2] = [40, 1];
            let window = shorten(Window { view: &values[..] });
            let first = Slice.get(window.view, 0);
            values = [9, 9];
            first + values[1]
        }"#,
        49,
        "",
    );
}

#[test]
fn destination_declared_mutable_labels_still_reject_short_writes() {
    rejects(
        r#"fn push<'a, 'b>(values: &mut Vec<&'a i64>, value: &'b i64) -> Unit ! {alloc, panic} {
            Vec.push(values, value);
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
}

#[test]
fn task_exit_and_structural_borrowed_leaves_stay_exact() {
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn narrow<'a>(window: Window<'a>) -> struct { view: &'a [i64] } ! {panic} {
            window
        }
        fn main() -> Unit ! {} {}"#,
        "returned record cannot carry a borrowed field",
    );
}

#[test]
fn distinct_source_occurrences_can_share_an_interned_arrow_contract() {
    // Both named functions have the same canonical callable contract. The
    // occurrence environment must be built per conversion, not attached once to
    // the interned function-type ID.
    agrees(
        r#"fn keep<'a>(value: &'a [i64]) -> &'a [i64] ! {panic} { value }
        fn same<'x>(value: &'x [i64]) -> &'x [i64] ! {panic} { value }
        fn apply(f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic}, values: &[i64]) -> i64 ! {panic} {
            Slice.get(f(values), 0)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [20, 2];
            apply(keep, &values[..]) + apply(same, &values[..])
        }"#,
        40,
        "",
    );
}

#[test]
fn recursive_borrowed_records_are_reported_instead_of_exhausting_the_stack() {
    // The leaf walk must terminate on a recursive borrowed record and report a
    // checked limitation. Expanding `next` without a visited set previously
    // overflowed the compiler stack.
    rejects(
        r#"struct Node<'a> { view: &'a [i64], next: Box<Node<'a>> }
        fn read<'a>(node: Node<'a>) -> i64 ! {panic} {
            Slice.get(node.view, 0)
        }
        fn main() -> Unit ! {} {}"#,
        "recursive borrowed type",
    );
}

#[test]
fn result_only_declared_labels_are_classified_by_the_contextual_witness() {
    // `'short` appears only in the by-value record result, so the old
    // direct-parameter environment left it unclassified and skipped the whole
    // conversion. Without `'long: 'short` the shortening has no proof.
    rejects(
        r#"struct Window<'a> { view: &'a [i64] }
        fn bad<'long, 'short>(window: Window<'long>) -> Window<'short> ! {panic} {
            window
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // With the declared edge the same result-only label is a proved covariant
    // shortening, not an erased comparison.
    check(
        r#"struct Window<'a> { view: &'a [i64] }
        fn ok<'long: 'short, 'short>(window: Window<'long>) -> Window<'short> ! {panic} {
            window
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
}

#[test]
fn nested_and_container_invariant_shortening_is_rejected() {
    // `'a` is nested under two mutable positions (`&'a mut Vec<&'a i64>` and
    // the outer `Box`), while no direct parameter or result borrow names it.
    // The declared-lifetime environment must still classify both labels.
    rejects(
        r#"struct Outer<'a> { cell: Box<&'a mut Vec<&'a i64>> }
        fn bad<'long: 'short, 'short>(x: Outer<'long>) -> Outer<'short> ! {panic} {
            x
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // A nested mutable box pointee is invariant even though the outer `&mut`
    // lifetime itself could otherwise shorten.
    rejects(
        r#"fn bad<'long: 'short + 'x, 'short, 'x>(b: &'x mut Box<&'long mut i64>) -> &'x mut Box<&'short mut i64> ! {panic} {
            b
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // Exact identity remains accepted for the same nested shape.
    check(
        r#"struct Outer<'a> { cell: Box<&'a mut Vec<&'a i64>> }
        fn same<'a>(x: Outer<'a>) -> Outer<'a> ! {panic} {
            x
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
}

#[test]
fn mutable_container_writes_use_the_static_destination_label() {
    // The local container has an explicit declared element lifetime but no
    // stored provenance leaf yet. The static type is the destination
    // authority, so a short write cannot be skipped.
    rejects(
        r#"fn attack<'long: 'short, 'short>(s: &'short i64) -> Unit ! {alloc, panic} {
            let mut values: Vec<&'long i64> = Vec.new();
            Vec.push(values, s);
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // The same rule applies through a `&mut Vec<&'a T>` parameter.
    rejects(
        r#"fn attack<'long: 'short, 'short>(values: &mut Vec<&'long i64>, s: &'short i64) -> Unit ! {alloc, panic} {
            Vec.push(values, s);
        }
        fn main() -> Unit ! {} {}"#,
        "outlive",
    );
    // A longer source written into a shorter declared element lifetime remains
    // valid.
    check(
        r#"fn ok<'long: 'short, 'short>(values: &mut Vec<&'short i64>, s: &'long i64) -> Unit ! {alloc, panic} {
            Vec.push(values, s);
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
}

#[test]
fn nested_record_leaves_inherit_enclosing_invariant_variance() {
    // `cell` is covariant on its own, but `Inner<'b>` is invariant in `'b`
    // through `keep`. A returned/constructed leaf must not be recorded as a
    // positive occurrence merely because the field is not a direct borrow.
    rejects(
        r#"struct Inner<'b> { keep: &'b mut Vec<&'b i64>, cell: Box<&'b i64> }
        fn make<'long: 'short, 'short>(long: &'long i64, keep: &'short mut Vec<&'short i64>) -> Inner<'short> ! {alloc, panic} {
            Inner { keep: keep, cell: Box.new(long) }
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence",
    );
}

#[test]
fn invariant_identity_through_calls_and_typed_locals_is_rejected() {
    // A callee binder is instantiated from the actual argument. Relabeling the
    // result with that caller provenance must make the same-scope invariant
    // check see `'long`, not an unclassified callee placeholder.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(i: Inv<'x>) -> Inv<'x> ! {panic} { i }
        fn bad<'long: 'short, 'short>(i: Inv<'long>) -> Unit ! {panic} {
            let a = make(i);
            let b: Inv<'short> = a;
            let _ = b;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // The reverse extension is equally unproved.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(i: Inv<'x>) -> Inv<'x> ! {panic} { i }
        fn bad<'long: 'short, 'short>(s: Inv<'short>) -> Unit ! {panic} {
            let a = make(s);
            let b: Inv<'long> = a;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // A borrowed-record result through one local keeps the same provenance;
    // removing only the direct `Call` case would leave this hole open.
    rejects(
        r#"struct Wrap<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn idr<'x>(w: &'x Wrap<'x>) -> &'x Wrap<'x> ! {panic} { w }
        fn bad<'long: 'short, 'short>(w: &'long Wrap<'long>) -> Unit ! {panic} {
            let e = idr(w);
            let y: &'short Wrap<'short> = e;
            let _ = y;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // Direct coercion of the call result, with no intervening local.
    rejects(
        r#"struct Wrap<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn idr<'x>(w: &'x Wrap<'x>) -> &'x Wrap<'x> ! {panic} { w }
        fn bad<'long: 'short, 'short>(w: &'long Wrap<'long>) -> Unit ! {panic} {
            let y: &'short Wrap<'short> = idr(w);
            let _ = y;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // A builtin container read carries the caller's element label; its result
    // must not be accepted as a different invariant element lifetime.
    rejects(
        r#"fn bad<'long: 'short, 'short>(v: &Vec<&'long mut Box<&'long i64>>) -> Unit ! {panic} {
            let x: &'short mut Box<&'short i64> = Vec.get(v, 0);
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn fresh_inferred_record_identity_must_not_launder_invariance() {
    // Destructuring and reconstructing a record gives the literal a fresh
    // inferred identity. Once field provenance resolves that identity to
    // `'long`, an unused typed binding to `Inv<'short>` is still an unproved
    // invariant conversion.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn bad<'long: 'short, 'short>(i: Inv<'long>) -> Unit ! {panic} {
            let Inv { cell } = i;
            let w = Inv { cell: cell };
            let x: Inv<'short> = w;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // The same fresh literal may not silently extend a short source either.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn bad<'long: 'short, 'short>(i: Inv<'short>) -> Unit ! {panic} {
            let Inv { cell } = i;
            let w = Inv { cell: cell };
            let x: Inv<'long> = w;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    // A field whose value carries a nested borrow label resolves the same way,
    // so the escape path is rejected at the binding, not by an internal
    // capability error later.
    rejects(
        r#"struct V<'a> { keep: &'a mut Vec<&'a i64> }
        fn make<'x>(v: V<'x>) -> V<'x> ! {panic} { v }
        fn bad<'long: 'short, 'short>(s: V<'short>, out: &mut Vec<&'long i64>) -> Unit ! {alloc, panic} {
            let a = make(s);
            let b: V<'long> = a;
            let V { keep } = b;
            let leaked = Vec.get(keep, 0);
            Vec.push(out, leaked);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn inferred_literal_identity_and_covariance_remain_accepted() {
    // Destructure/reconstruct is a legitimate identity transfer when the
    // inferred literal gets its actual field provenance label.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn keep<'a>(i: Inv<'a>) -> Inv<'a> ! {panic} {
            let Inv { cell } = i;
            let w = Inv { cell: cell };
            w
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    // An inferred covariant record literal may still shorten to a declared
    // parameter lifetime.
    check(
        r#"struct Window<'a> { view: &'a [i64] }
        fn first<'a>(window: Window<'a>) -> i64 ! {panic} { Slice.get(window.view, 0) }
        fn local<'short>(values: &'short [i64]) -> i64 ! {panic} {
            let w = Window { view: values };
            let x: Window<'short> = w;
            first(x)
        }
        fn main() -> i64 ! {panic} {
            let values: [i64; 2] = [40, 2];
            local(&values[..])
        }"#,
    )
    .unwrap();
}

#[test]
fn call_wide_lifetime_constraints_follow_parameter_variance() {
    // One invariant binder cannot be instantiated from two distinct actual
    // identities, even when the call result is unused Unit.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn take<'x>(p: Inv<'x>, q: Inv<'x>) -> Unit ! {panic} {
            let _ = p;
            let _ = q;
        }
        fn bad<'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            take(p, q);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn take<'x>(p: Inv<'x>, q: Inv<'x>) -> Unit ! {panic} {
            let _ = p;
            let _ = q;
        }
        fn ok<'short>(p: Inv<'short>, q: Inv<'short>) -> Unit ! {panic} {
            take(p, q);
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    // A covariant occurrence may use a longer actual lifetime once the
    // invariant occurrence has fixed the binder, but the reverse has no proof.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct View<'a> { r: &'a i64 }
        fn relax<'x>(p: Inv<'x>, v: View<'x>) -> Unit ! {panic} {
            let _ = p;
            let _ = v;
        }
        fn ok<'long: 'short, 'short>(p: Inv<'short>, v: View<'long>) -> Unit ! {panic} {
            relax(p, v);
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct View<'a> { r: &'a i64 }
        fn relax<'x>(p: Inv<'x>, v: View<'x>) -> Unit ! {panic} {
            let _ = p;
            let _ = v;
        }
        fn bad<'long: 'short, 'short>(p: Inv<'long>, v: View<'short>) -> Unit ! {panic} {
            relax(p, v);
        }
        fn main() -> Unit ! {} {}"#,
        "cannot use lifetime 'short' where 'x' is invariant 'long'",
    );
    // The same occurrence constraints apply to methods.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct Sink { n: i64 }
        impl Sink {
            fn absorb<'x>(self: &Self, p: Inv<'x>, q: Inv<'x>) -> Unit ! {panic} {
                let _ = self;
                let _ = p;
                let _ = q;
            }
        }
        fn ok<'short>(p: Inv<'short>, q: Inv<'short>) -> Unit ! {panic} {
            let sink = Sink { n: 0 };
            sink.absorb(p, q);
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct Sink { n: i64 }
        impl Sink {
            fn absorb<'x>(self: &Self, p: Inv<'x>, q: Inv<'x>) -> Unit ! {panic} {
                let _ = self;
                let _ = p;
                let _ = q;
            }
        }
        fn bad<'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            let sink = Sink { n: 0 };
            sink.absorb(p, q);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
}

#[test]
fn indirect_calls_instantiate_lifetimes_from_actual_arguments() {
    // A single actual identity instantiates the arrow binder; the call is
    // valid for unused Unit, observable results, and nested borrowed records.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn take<'x>(i: Inv<'x>) -> Unit ! {panic} { let _ = i; }
        fn ok<'long>(i: Inv<'long>) -> Unit ! {panic} {
            let f: fn<'x>(Inv<'x>) -> Unit ! {panic} = take;
            f(i);
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    agrees(
        r#"struct Window<'a> { view: &'a [i64], start: i64 }
        fn first<'x>(window: Window<'x>) -> i64 ! {panic} {
            Slice.get(window.view, window.start)
        }
        fn main() -> i64 ! {panic} {
            let f: fn<'x>(Window<'x>) -> i64 ! {panic} = first;
            let values: [i64; 2] = [40, 2];
            f(Window { view: &values[..], start: 0 })
        }"#,
        40,
        "",
    );
    // Two invariant occurrences still need one identity through the arrow.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn take<'x>(p: Inv<'x>, q: Inv<'x>) -> Unit ! {panic} {
            let _ = p;
            let _ = q;
        }
        fn bad<'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            let f: fn<'x>(Inv<'x>, Inv<'x>) -> Unit ! {panic} = take;
            f(p, q);
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
    // Returning the arrow's identity and then shortening it is still an
    // unproved invariant conversion.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(i: Inv<'x>) -> Inv<'x> ! {panic} { i }
        fn bad<'long: 'short, 'short>(i: Inv<'long>) -> Unit ! {panic} {
            let f: fn<'x>(Inv<'x>) -> Inv<'x> ! {panic} = make;
            let a = f(i);
            let b: Inv<'short> = a;
            let _ = b;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn nested_argument_blocks_and_lambdas_keep_their_lifetime_checks() {
    // The call boundary covers only the outer argument instantiation; a block
    // used as an argument still checks its own annotated conversion.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn sink(n: i64) -> Unit ! {panic} { let _ = n; }
        fn bad<'long: 'short, 'short>(i: Inv<'long>) -> Unit ! {panic} {
            sink({ let b: Inv<'short> = i; let _ = b; 0 });
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime mismatch",
    );
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn sink(n: i64) -> Unit ! {panic} { let _ = n; }
        fn ok<'long>(i: Inv<'long>) -> Unit ! {panic} {
            sink({ let b: Inv<'long> = i; let _ = b; 0 });
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn sink(n: i64) -> Unit ! {panic} { let _ = n; }
        fn bad<'long: 'short, 'short>(c: Bool, i: Inv<'long>) -> Unit ! {panic} {
            sink(if c { let b: Inv<'short> = i; let _ = b; 0 } else { 0 });
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime mismatch",
    );
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn sink(n: i64) -> Unit ! {panic} { let _ = n; }
        fn ok<'long>(c: Bool, i: Inv<'long>) -> Unit ! {panic} {
            sink(if c { let b: Inv<'long> = i; let _ = b; 0 } else { 0 });
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    // An immediately called lambda keeps its body obligations even when the
    // lambda itself is the callee of a call.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn bad<'long: 'short, 'short>(i: Inv<'long>) -> Unit ! {alloc, panic} {
            let _ = (fn() -> i64 ! {alloc, panic} {
                let b: Inv<'short> = i;
                let _ = b;
                0
            })();
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime mismatch",
    );
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn ok<'long>(i: Inv<'long>) -> Unit ! {alloc, panic} {
            let _ = (fn() -> i64 ! {alloc, panic} {
                let b: Inv<'long> = i;
                let _ = b;
                0
            })();
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
}

#[test]
fn unresolved_callee_result_labels_never_alias_caller_binders() {
    // The callee binder 'x is ambiguous, so it must not survive as the raw
    // name 'x and accidentally equal the caller's own 'x.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(p: Inv<'x>, q: Inv<'x>) -> Inv<'x> ! {panic} { p }
        fn bad<'x, 'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            let r = make(p, q);
            let x: Inv<'x> = r;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(p: Inv<'x>, q: Inv<'x>) -> Inv<'x> ! {panic} { p }
        fn control<'x, 'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            let r = make(p, q);
            let x: Inv<'short> = r;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(p: Inv<'x>) -> Inv<'x> ! {panic} { p }
        fn bad<'x, 'long>(p: Inv<'long>) -> Unit ! {panic} {
            let r = make(p);
            let x: Inv<'x> = r;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn make<'x>(p: Inv<'x>, q: Inv<'x>) -> Inv<'x> ! {panic} { p }
        fn bad<'x, 'long: 'short, 'short>(p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
            let f: fn<'x>(Inv<'x>, Inv<'x>) -> Inv<'x> ! {panic} = make;
            let r = f(p, q);
            let x: Inv<'x> = r;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant occurrence requires one actual lifetime identity",
    );
}

#[test]
fn record_literal_inference_uses_only_fields_that_mention_the_lifetime() {
    // `W<'a, T>` has one lifetime parameter used by `inv`. The unrelated
    // `extra: B<'long>` field must neither supply nor poison that identity.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct W<'a, T> { inv: Inv<'a>, extra: T }
        struct B<'b> { view: &'b i64 }
        fn ok<'long: 'short, 'short>(i: Inv<'short>, b: B<'long>) -> Unit ! {panic} {
            let w = W { inv: i, extra: b };
            let x: W<'short, B<'long>> = w;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
    // The unrelated field's longer lifetime cannot be taken as the identity
    // of the invariant field.
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct W<'a, T> { inv: Inv<'a>, extra: T }
        struct B<'b> { view: &'b i64 }
        fn loose<'a, T>(inv: Inv<'a>, extra: T) -> W<'a, T> ! {panic} {
            W { inv: inv, extra: extra }
        }
        fn bad<'long: 'short, 'short>(i: Inv<'short>, b: B<'long>) -> Unit ! {panic} {
            let w = W { inv: i, extra: b };
            let x: W<'long, B<'long>> = w;
            let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "invariant",
    );
}

#[test]
fn call_argument_if_joins_preserve_actual_lifetime_obligations() {
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
fn id<'x>(p: Inv<'x>) -> Inv<'x> ! {panic} { p }
fn bad<'long: 'short, 'short>(c: Bool, p: Inv<'long>, q: Inv<'short>) -> Unit ! {panic} {
    let r = id(if c { p } else { q });
    let x: Inv<'long> = r;
    let _ = x;
}
fn main() -> Unit ! {} {}
"#,
        "lifetime",
    );
    rejects(
        r#"struct View<'a> { r: &'a i64 }
fn take<'x>(v: View<'x>) -> Unit ! {panic} { let _ = v; }
fn bad<'long: 'short, 'short>(c: Bool, p: View<'long>, q: View<'short>) -> Unit ! {panic} {
    take(if c { p } else { q });
}
fn main() -> Unit ! {} {}
"#,
        "lifetime",
    );
}

#[test]
fn laundering_coverage_through_union_typed_arms() {
    // The arms' identities must survive the swap-in of either label flavor:
    // the second arm uses a structural union against the same definition.
    check(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        fn id<'x>(v: Inv<'x>) -> Unit ! {panic} { let _ = v; }
        fn ok<'x>(v: Inv<'x>) -> Unit ! {panic} { id(v) }
        fn main() -> Unit ! {} {}"#,
    )
    .unwrap();
}

#[test]
fn lifetimes_inside_record_type_arguments_are_invariant() {
    // A label that occurs only inside a type argument cannot be extended
    // (`Outer<W<'short>>` -> `Outer<W<'long>>`) or used to bypass an
    // invariant slot.
    rejects(
        r#"struct W<'a> { view: &'a [i64] }
        struct Outer<T> { inner: T }
        fn launder<'long: 'short, 'short>(o: Outer<W<'short>>, mark: &'long i64) -> i64 ! {panic} {
            let x: Outer<W<'long>> = o;
            let _ = mark;
            Slice.get(x.inner.view, 0)
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime mismatch",
    );
    rejects(
        r#"struct Inv<'a> { cell: Box<&'a mut Box<&'a i64>> }
        struct Wrap<T> { inner: T }
        fn launder<'long: 'short, 'short>(w: Wrap<Inv<'short>>, mark: &'long i64) -> Unit ! {panic} {
            let x: Wrap<Inv<'long>> = w;
            let _ = mark; let _ = x;
        }
        fn main() -> Unit ! {} {}"#,
        "lifetime mismatch",
    );
}
