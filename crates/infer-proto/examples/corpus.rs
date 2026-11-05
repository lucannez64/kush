//! Print the prototype's result for each corpus program.
fn main() {
    for (name, source) in kush_infer_proto_corpus() {
        let report = kush_infer_proto::check(source, 100_000);
        match &report.outcome {
            Ok((out, fit, eff)) => {
                let signature = kush_infer_proto::signature(out);
                println!(
                    "{name}: {out}  fit={fit:?} eff={eff} steps={}\n    simplified: {}\n    kush: {}{}",
                    report.steps,
                    signature.simplified,
                    signature.kush,
                    if signature.instance {
                        " (instance)"
                    } else {
                        ""
                    }
                )
            }
            Err(failure) => println!("{name}: FAIL {failure:?} steps={}", report.steps),
        }
    }
}
fn kush_infer_proto_corpus() -> Vec<(&'static str, &'static str)> {
    vec![
        ("id", "(lam x x)"),
        ("apply", "(lam f (lam x (app f x)))"),
        ("compose", "(lam f (lam g (lam x (app f (app g x)))))"),
        (
            "let_poly",
            "(let id (lam x x) (if (app id true) (app id 1) 2))",
        ),
        (
            "unannotated_lambda",
            "(let inc (lam x (app add x 1)) (app inc 41))",
        ),
        ("join_union", "(lam c (if c 1 true))"),
        ("rank2_unannotated", "(lam f (if (app f true) (app f 1) 0))"),
        (
            "rank2_annotated",
            "(lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0))",
        ),
        (
            "rank2_use_ok",
            "(app (lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0)) (lam x x))",
        ),
        (
            "rank2_use_bad",
            "(app (lam (f : (forall (a) (-> a a))) (if (app f true) (app f 1) 0)) (lam x (app add x 1)))",
        ),
        ("effect_infer", "(lam x (app print x))"),
        (
            "effect_pure_ann_bad",
            "(ann (lam x (app print x)) (-> int int))",
        ),
        (
            "effect_ann_ok",
            "(ann (lam x (app print x)) (->! io int int))",
        ),
        ("effect_hof", "(lam f (lam x (app f (app print x))))"),
        ("effect_flow_top", "(app (lam x (app print x)) 1)"),
        ("bad_app", "(app 1 2)"),
        ("bad_if", "(if 1 2 3)"),
        ("self_app", "(lam x (app x x))"),
        ("omega_use", "(let w (lam x (app x x)) (app w w))"),
        ("church_two", "(lam f (lam x (app f (app f x))))"),
        ("pick", "(lam c (lam x (lam y (if c x y))))"),
        (
            "nested_lets",
            "(let a (lam x x) (let b (lam y (app a (app a y))) (let c (lam z (app b (app b z))) (let d (lam u (app c (app c u))) (app d 1)))))",
        ),
    ]
}
