//! The RES-INFERENCE-PROTOTYPE corpus: each program's expected outcome.
//! See docs/inference-prototype.md for the evaluation.
use kush_infer_proto::{Failure, Fit, check};

const BUDGET: usize = 100_000;

fn inferred(source: &str, ty: &str, fit: Fit) {
    let report = check(source, BUDGET);
    match report.outcome {
        Ok((out, actual, _)) => {
            assert_eq!(out.to_string(), ty, "{source}");
            assert_eq!(actual, fit, "{source}");
        }
        Err(failure) => panic!("{source}: {failure:?}"),
    }
}

fn unrepresentable(source: &str, reason: &str) {
    match check(source, BUDGET).outcome {
        Ok((_, Fit::Unrepresentable(actual), _)) => {
            assert!(actual.contains(reason), "{source}: {actual}")
        }
        other => panic!("{source}: {other:?}"),
    }
}

fn type_error(source: &str, message: &str) {
    match check(source, BUDGET).outcome {
        Err(Failure::Type(actual)) => assert!(actual.contains(message), "{source}: {actual}"),
        other => panic!("{source}: {other:?}"),
    }
}

/// Programs Kush already expresses with explicit generics: inferred with no
/// annotation and a direct Kush type.
#[test]
fn rank_one_generic_programs_infer_without_annotations() {
    inferred("(lam x x)", "('a1 -> 'a1)", Fit::Direct);
    inferred(
        "(lam f (lam x (app f x)))",
        "(('a2 -> 'a3) -> ('a2 -> 'a3))",
        Fit::Direct,
    );
    inferred(
        "(lam f (lam g (lam x (app f (app g x)))))",
        "(('a4 -> 'a5) -> (('a3 -> 'a4) -> ('a3 -> 'a5)))",
        Fit::Direct,
    );
    // Let-polymorphism: one binding used at two types.
    inferred(
        "(let id (lam x x) (if (app id true) (app id 1) 2))",
        "int",
        Fit::Direct,
    );
    // Kush requires lambda parameter annotations today.
    inferred(
        "(let inc (lam x (app add x 1)) (app inc 41))",
        "int",
        Fit::Direct,
    );
    // Without variable merging, `f`'s bounds stay apart; every variable
    // could be unified to give Kush's `fn twice<T>(f: fn(T) -> T, x: T)`.
    inferred(
        "(lam f (lam x (app f (app f x))))",
        "((('a2 | 'a3) -> ('a3 & 'a4)) -> ('a2 -> 'a4))",
        Fit::Direct,
    );
}

/// Joins of distinct scalars become Kush unions, which change the value's
/// representation at every injection.
#[test]
fn joins_need_representation_changing_coercions() {
    inferred(
        "(lam c (if c 1 true))",
        "(bool -> (int | bool))",
        Fit::NeedsUnionCoercion,
    );
    // "Rank-2" use without annotation is typed at a union monotype: the
    // argument must accept `int | bool`, so an `int -> int` function is
    // rejected at the call and `id` is used through an adapter.
    inferred(
        "(lam f (if (app f true) (app f 1) 0))",
        "(((int | bool) -> (bool & 'a3)) -> int)",
        Fit::NeedsUnionCoercion,
    );
}

/// The annotation escape hatch: a `forall` parameter is instantiated at each
/// use and checked against rigid variables at each call.
#[test]
fn polymorphic_parameters_need_and_respect_annotations() {
    inferred(
        "(lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0))",
        "(<forall> -> int)",
        Fit::Direct,
    );
    inferred(
        "(app (lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0)) (lam x x))",
        "int",
        Fit::Direct,
    );
    type_error(
        "(app (lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0)) (lam x (app add x 1)))",
        "cannot use",
    );
}

/// Effect rows are a lattice: lower bounds flow through arrows and are
/// checked against annotated rows.
#[test]
fn effect_rows_flow_and_are_checked() {
    inferred("(lam x (app print x))", "(int ->{io} int)", Fit::Direct);
    inferred(
        "(ann (lam x (app print x)) (->! io int int))",
        "(int ->{io} int)",
        Fit::Direct,
    );
    type_error(
        "(ann (lam x (app print x)) (-> int int))",
        "exceed the annotated row",
    );
    inferred(
        "(lam f (lam x (app f (app print x))))",
        "((int -> 'a4) -> (int ->{io} 'a4))",
        Fit::Direct,
    );
    let report = check("(app (lam x (app print x)) 1)", BUDGET);
    assert_eq!(report.outcome.unwrap().2, kush_infer_proto::IO);
}

#[test]
fn ill_typed_programs_are_rejected() {
    type_error("(app 1 2)", "cannot use int as");
    type_error("(if 1 2 3)", "cannot use int as bool");
    type_error("(app nope 1)", "unbound variable");
}

/// Subtyping inference accepts self-application with an equirecursive type;
/// Kush has none, so every binding is checked, not just the result.
#[test]
fn recursive_types_are_not_kush_types() {
    unrepresentable("(lam x (app x x))", "recursive type");
    unrepresentable(
        "(let w (lam x (app x x)) (app w w))",
        "binding 'x': recursive type",
    );
}

fn pairs(n: usize) -> String {
    let mut s = String::from("(let p0 (lam x (lam g (app g x x))) ");
    for k in 1..=n {
        s.push_str(&format!(
            "(let p{k} (lam y (app p{p} (app p{p} y))) ",
            p = k - 1
        ));
    }
    s.push_str(&format!("p{n}"));
    s.push_str(&")".repeat(n + 1));
    s
}

/// Budgets are deterministic and exhaustion is never success.
#[test]
fn budgets_are_deterministic_and_never_accept() {
    let small = check(&pairs(2), 2_000_000);
    assert!(small.outcome.is_ok());
    assert_eq!(small.steps, check(&pairs(2), 2_000_000).steps);
    // Exponential bound growth: the step budget stops it.
    let big = check(&pairs(6), 2_000_000);
    assert_eq!(big.outcome.unwrap_err(), Failure::Budget);
    assert_eq!(big.steps, 2_000_001);
    // Deep nesting: the depth budget stops it before the native stack does.
    let deep = check(&pairs(40), 2_000_000);
    assert_eq!(deep.outcome.unwrap_err(), Failure::Budget);
    // A tiny budget rejects even a trivial program.
    assert_eq!(check("(lam x x)", 5).outcome.unwrap_err(), Failure::Budget);
}

// ---------------------------------------------------------------------------
// I-PROTO-SIMPLIFY: co-occurrence simplification and Kush signatures
// ---------------------------------------------------------------------------

fn signature_of(source: &str) -> kush_infer_proto::Signature {
    let (out, _, _) = check(source, BUDGET).outcome.unwrap();
    kush_infer_proto::signature(&out)
}

#[test]
fn simplification_preserves_already_simple_types() {
    for (source, expected) in [
        ("(lam x x)", "('a0 -> 'a0)"),
        (
            "(lam f (lam x (app f x)))",
            "(('a0 -> 'a1) -> ('a0 -> 'a1))",
        ),
        (
            "(lam f (lam g (lam x (app f (app g x)))))",
            "(('a0 -> 'a1) -> (('a2 -> 'a0) -> ('a2 -> 'a1)))",
        ),
        ("(lam x (app print x))", "(int ->{io} int)"),
        ("(lam c (if c 1 true))", "(bool -> (int | bool))"),
    ] {
        let signature = signature_of(source);
        assert_eq!(signature.simplified.to_string(), expected, "{source}");
        assert_eq!(signature.kush, signature.simplified, "{source}");
        assert!(!signature.instance, "{source}");
    }
}

#[test]
fn co_occurring_variables_merge_and_polar_variables_vanish() {
    // twice: 'a2 and 'a3 always occur together positively, so they merge;
    // the remaining intersection of variables is merged only for Kush.
    let twice = signature_of("(lam f (lam x (app f (app f x))))");
    assert_eq!(
        twice.simplified.to_string(),
        "(('a0 -> ('a0 & 'a1)) -> ('a0 -> 'a1))"
    );
    assert_eq!(twice.kush.to_string(), "(('a0 -> 'a0) -> ('a0 -> 'a0))");
    assert!(twice.instance);
    // A variable that only bounds a result from one side disappears.
    let rank2 = signature_of("(lam f (if (app f true) (app f 1) 0))");
    assert_eq!(
        rank2.simplified.to_string(),
        "(((int | bool) -> bool) -> int)"
    );
    // Two branches of variables: (x, y) -> x | y is x -> x -> x.
    let pick = signature_of("(lam c (lam x (lam y (if c x y))))");
    assert_eq!(
        pick.simplified.to_string(),
        "(bool -> ('a0 -> ('a0 -> 'a0)))"
    );
    assert!(!pick.instance);
}

/// Replace every type variable by `int` and print as an annotation.
fn at_int(out: &kush_infer_proto::Out) -> Option<String> {
    use kush_infer_proto::Out;
    Some(match out {
        Out::Int | Out::Param(_) => "int".into(),
        Out::Bool => "bool".into(),
        Out::Fun(a, b, 0) => format!("(-> {} {})", at_int(a)?, at_int(b)?),
        Out::Fun(a, b, bits) => {
            let mut names = Vec::new();
            for (bit, name) in [(kush_infer_proto::IO, "io"), (2, "alloc"), (4, "panic")] {
                if bits & bit != 0 {
                    names.push(name);
                }
            }
            format!("(->! {} {} {})", names.join(" "), at_int(a)?, at_int(b)?)
        }
        _ => return None,
    })
}

#[test]
fn every_kush_signature_still_types_its_program() {
    // Simplification and merging must yield a type the term really has:
    // re-check each corpus program annotated with its Kush signature at int.
    let mut checked = 0;
    for source in [
        "(lam x x)",
        "(lam f (lam x (app f x)))",
        "(lam f (lam g (lam x (app f (app g x)))))",
        "(lam f (lam x (app f (app f x))))",
        "(lam c (lam x (lam y (if c x y))))",
        "(lam x (app print x))",
        "(lam f (lam x (app f (app print x))))",
    ] {
        let signature = signature_of(source);
        let Some(annotation) = at_int(&signature.kush) else {
            continue;
        };
        let annotated = format!("(ann {source} {annotation})");
        assert!(
            check(&annotated, BUDGET).outcome.is_ok(),
            "{annotated}: {:?}",
            check(&annotated, BUDGET).outcome
        );
        checked += 1;
    }
    assert_eq!(checked, 7);
    // The re-check is not vacuous: a signature the term does not have is
    // rejected (twice feeds f's result back into f).
    assert!(
        check(
            "(ann (lam f (lam x (app f (app f x)))) (-> (-> int bool) (-> int bool)))",
            BUDGET
        )
        .outcome
        .is_err()
    );
}
