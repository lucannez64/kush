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
