//! KERNEL-BUDGET-ATTR: the kernel's step budget is deterministic and large by
//! default, and a logical declaration can set its own with
//! `#[kernel_steps(N)]`; the budget travels with the declaration in the
//! exchange format.
use kush::{check, exchange, kernel};

const ADD: &str = "
total fn add(n: Nat, m: Nat) -> Nat ! {} {
    Nat.induct(fn(k) { Nat }, m, fn(k, acc) { Nat.succ(acc) }, n)
}
";

fn rejects(source: &str, expected: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected:?}, got {error:?}"
    );
}

#[test]
fn a_declaration_sets_its_own_step_budget() {
    let proof = "total fn sixty() -> Eq<Nat, add<30, 30>, 60> ! {} { refl::<Nat>(60) }";
    check(&format!("{ADD}{proof}")).unwrap();
    // A small budget is exhausted: an error, never a verdict.
    rejects(
        &format!("{ADD}#[kernel_steps(50)]\n{proof}"),
        "budget exhausted",
    );
    // A raised budget is accepted and recorded for export; other
    // declarations keep the default.
    let raised = check(&format!("{ADD}#[kernel_steps(200_000_000)]\n{proof}")).unwrap();
    assert_eq!(raised.kernel.admitted_steps("sixty"), Some(200_000_000));
    assert_eq!(raised.kernel.admitted_steps("add"), None);
    assert_eq!(raised.kernel.limits().steps, kernel::DEFAULT_STEPS);
    let dump = exchange::dump(&raised);
    assert!(dump.contains("(steps 200000000))"), "{dump}");
    // The Rust kernel replays the dump with the recorded budget.
    assert!(exchange::answer(&dump).unwrap().contains("ok sixty"));
    // The same budget on a data family.
    let data =
        check("#[kernel_steps(1000000)]\ntotal enum Even { EvenZero: Even, EvenSucc(Even): Even }")
            .unwrap();
    assert_eq!(data.kernel.admitted_steps("Even"), Some(1_000_000));
    assert!(exchange::dump(&data).contains("(steps 1000000)"));
}

#[test]
fn budgets_round_trip_in_the_exchange_format() {
    let text = "(def two 0 nat (succ (succ zero)) (steps 5))\n\
                (data Unit1 0 type () (steps 7) (ctor mk () () ()))\n";
    let items = exchange::parse(text).unwrap();
    match &items[0] {
        exchange::Item::Def { steps, .. } => assert_eq!(*steps, Some(5)),
        other => panic!("{other:?}"),
    }
    match &items[1] {
        exchange::Item::Data { steps, .. } => assert_eq!(*steps, Some(7)),
        other => panic!("{other:?}"),
    }
    // Five steps are not enough to check `two`; seven are enough for Unit1.
    assert_eq!(exchange::answer(text).unwrap(), "budget two\nok Unit1\n");
    for (bad, expected) in [
        ("(def x 0 nat zero (steps 0))", "positive"),
        ("(def x 0 nat zero (stops 5))", "(steps N)"),
        ("(def x 0 nat zero (steps))", "takes 1 arguments"),
    ] {
        let error = exchange::parse(bad).unwrap_err().to_string();
        assert!(error.contains(expected), "{bad}: {error}");
    }
}

#[test]
fn malformed_or_misplaced_budgets_are_rejected() {
    let proof = "total fn one() -> Nat ! {} { 1 }";
    for (attribute, expected) in [
        ("#[kernel_steps(0)]", "positive integer"),
        ("#[kernel_steps(\"many\")]", "positive integer"),
        ("#[kernel_steps]", "positive integer"),
        (
            "#[kernel_steps(5)]\n#[kernel_steps(6)]",
            "once per declaration",
        ),
        ("#[noalloc]", "only #[kernel_steps(N)]"),
    ] {
        rejects(&format!("{attribute}\n{proof}"), expected);
    }
    // In a program with executable code, it applies to logical declarations
    // only.
    let error =
        kush::executable::check("#[kernel_steps(5)]\nfn main() -> i64 ! {} { 0 }").unwrap_err();
    assert!(
        error.message.contains("logical declarations only"),
        "{error:?}"
    );
    kush::executable::check(
        "#[kernel_steps(1000000)]\ntotal fn one() -> Nat ! {} { 1 }\nfn main() -> i64 ! {} { 0 }",
    )
    .unwrap();
}

#[test]
fn the_defaults_are_large_and_deterministic() {
    let limits = kernel::Limits::default();
    assert_eq!(limits.steps, kernel::DEFAULT_STEPS);
    assert_eq!(limits.steps, 100_000_000);
    assert_eq!(limits.depth, 100_000);
}
