//! PROOF-FUZZ step 1: the checker records every run-time check it could not
//! discharge (an obligation), with its kind, span, function and goal. A
//! proved check records nothing. The span is the one the reference evaluator
//! reports when that check panics, so a failure can be attributed to exactly
//! one obligation. See docs/proof-fuzz.md.
use kush::executable::{Container, Executable, ObligationKind, check};

fn checked(source: &str) -> Executable {
    check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"))
}

/// `(kind label, function, goal, source text of the span)` for each obligation.
fn listed(source: &str) -> Vec<(String, String, String, String)> {
    let program = checked(source);
    program
        .obligations()
        .iter()
        .map(|o| {
            (
                o.kind.label().to_owned(),
                o.function_name.clone(),
                o.goal.clone(),
                source[o.span.start..o.span.end].to_owned(),
            )
        })
        .collect()
}

fn row(kind: &str, function: &str, goal: &str, text: &str) -> (String, String, String, String) {
    (kind.into(), function.into(), goal.into(), text.into())
}

#[test]
fn each_kind_of_unproved_check_is_recorded() {
    let source = "fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn neg(a: i64) -> i64 ! {panic} { -a }
fn div(a: i64, b: i64) -> i64 ! {panic} { a / b }
fn shift(a: u8, b: u8) -> u8 ! {panic} { a << b }
fn main() -> i64 ! {panic} { add(1, 2) + neg(1) + div(4, 2) + Int.convert(shift(1, 1)) }";
    let rows = listed(source);
    assert!(rows.contains(&row(
        "overflow",
        "add",
        "the result of + stays in i64",
        "a + b"
    )));
    assert!(rows.contains(&row("overflow", "neg", "the negation stays in i64", "-a")));
    assert!(rows.contains(&row(
        "division",
        "div",
        "the divisor is not zero and the quotient fits",
        "a / b"
    )));
    assert!(rows.contains(&row(
        "shift",
        "shift",
        "the shift amount is below the width of u8",
        "a << b"
    )));
}

#[test]
fn proved_checks_record_nothing() {
    let rows = listed(
        "fn next(c: i64, erased q: { c <= 100 }) -> i64 ! {} { c + 1 }
fn bump(x: u8) -> u8 ! {} { if x < 255 { x + 1 } else { x } }
fn main() -> i64 ! {panic} { next(1, _) + Int.convert(bump(3)) }",
    );
    assert!(
        rows.iter().all(|(_, function, _, _)| function == "main"),
        "{rows:?}"
    );
}

#[test]
fn vec_accesses_are_recorded_with_their_refinement() {
    let source = "struct Ram { cells: Vec<u8> where len >= 16 }
fn plain(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
fn refined(r: &Ram, i: i64) -> u8 ! {panic} { r.cells[i] }
fn proved(r: &Ram, i: i64) -> u8 ! {panic} { if i >= 0 && i < 16 { r.cells[i] } else { 0 } }
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    let mut cells: Vec<u8> = Vec.new();
    let mut k = 0;
    while k < 16 { cells = cells.push(0); k = k + 1; }
    let r = Ram { cells: cells };
    plain(&v, 0) + Int.convert(refined(&r, 1)) + Int.convert(proved(&r, 2))
}";
    let program = checked(source);
    let bounds: Vec<_> = program
        .obligations()
        .iter()
        .filter_map(|o| match o.kind {
            ObligationKind::Bounds {
                container,
                refined_length,
            } => Some((
                o.function_name.as_str(),
                container,
                refined_length,
                o.goal.as_str(),
            )),
            _ => None,
        })
        .collect();
    assert!(
        bounds.contains(&("plain", Container::Vec, None, "0 <= index && index < len")),
        "{bounds:?}"
    );
    assert!(
        bounds.contains(&("refined", Container::Vec, Some(16), "0 <= index && index < 16")),
        "{bounds:?}"
    );
    assert!(!bounds.iter().any(|(f, ..)| *f == "proved"), "{bounds:?}");
    // Vec obligations are exactly the accesses the report counts as checked.
    let (_, checked_count) = program.bounds_report();
    let vec_obligations = program
        .obligations()
        .iter()
        .filter(|o| {
            matches!(
                o.kind,
                ObligationKind::Bounds {
                    container: Container::Vec,
                    ..
                }
            )
        })
        .count();
    assert_eq!(vec_obligations, checked_count);
}

#[test]
fn slice_and_array_accesses_are_recorded() {
    let rows = listed(
        "fn first(s: &[i64], i: i64) -> i64 ! {panic} { s[i] }
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(7);
    first(&v[..], 0)
}",
    );
    assert!(
        rows.iter()
            .any(|(kind, function, _, text)| kind == "bounds"
                && function == "first"
                && text == "s[i]"),
        "{rows:?}"
    );
}

/// The span a failing check panics at, under the reference evaluator, is the
/// span of exactly one recorded obligation of the expected kind.
fn panics_at(source: &str, kind: &str, text: &str) {
    let program = checked(source);
    let error = program
        .evaluate(&mut Vec::new())
        .expect_err("the program should panic");
    assert!(error.message.starts_with("panic:"), "{error:?}");
    let matching: Vec<_> = program
        .obligations()
        .iter()
        .filter(|o| o.span == error.span)
        .collect();
    assert_eq!(matching.len(), 1, "{error:?} {:?}", program.obligations());
    assert_eq!(matching[0].kind.label(), kind);
    assert_eq!(&source[error.span.start..error.span.end], text);
}

#[test]
fn an_evaluator_panic_names_its_obligation() {
    panics_at(
        "fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn main() -> i64 ! {panic} { add(9223372036854775807, 1) }",
        "overflow",
        "a + b",
    );
    panics_at(
        "fn div(a: i64, b: i64) -> i64 ! {panic} { a / b }
fn main() -> i64 ! {panic} { div(1, 0) }",
        "division",
        "a / b",
    );
    panics_at(
        "fn at(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    at(&v, 3)
}",
        "bounds",
        "v[i]",
    );
}

#[test]
fn a_generic_check_is_one_obligation_per_instance() {
    let program = checked(
        "fn twice<T>(x: i64, t: T) -> i64 ! {panic} { x + x }
fn main() -> i64 ! {panic} { twice(1, 2) + twice(1, true) }",
    );
    let twice: Vec<_> = program
        .obligations()
        .iter()
        .filter(|o| o.function_name.starts_with("twice"))
        .collect();
    assert_eq!(twice.len(), 2, "{:?}", program.obligations());
    assert_eq!(twice[0].span, twice[1].span);
    assert_ne!(twice[0].function, twice[1].function);
}
