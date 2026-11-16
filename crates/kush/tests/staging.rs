//! Staging syntax and stage-boundary regressions. Execution tests belong here
//! as the checker, generator evaluator and native support become available.
use kush::ast::{Expr, ExprKind, ItemKind, StagingForm, Statement};

fn tail(source: &str) -> Expr {
    let mut module = kush::parse(source).unwrap();
    let ItemKind::Function(function) = module.items.remove(0).item.kind else {
        panic!("expected a function")
    };
    *function.body.unwrap().tail.unwrap()
}

#[test]
fn quote_is_structured_and_retains_its_signature_and_spans() {
    let source = "fn make() -> Unit ! {} { quote fn(x: i64) -> i64 ! {panic} { x + 1 } }";
    let expr = tail(source);
    let (form, body) = expr.staging().unwrap();
    assert_eq!(form, StagingForm::Quote);
    assert_eq!(
        &source[expr.span.start..expr.span.end],
        "quote fn(x: i64) -> i64 ! {panic} { x + 1 }"
    );
    let ExprKind::Lambda(lambda) = &body.kind else {
        panic!()
    };
    assert_eq!(lambda.parameters[0].name, "x");
    assert_eq!(lambda.effects.len(), 1);
    assert!(matches!(
        lambda.body.tail.as_ref().unwrap().kind,
        ExprKind::Binary { .. }
    ));
}

#[test]
fn splice_is_a_callable_expression_and_lift_is_an_operand() {
    let quote = tail(
        "fn make() -> Unit ! {} { quote fn(x: i64) -> i64 ! {} { splice(fragment)(lift(n)) } }",
    );
    let (_, quoted) = quote.staging().unwrap();
    let ExprKind::Lambda(lambda) = &quoted.kind else {
        panic!()
    };
    let ExprKind::Call { callee, arguments } = &lambda.body.tail.as_ref().unwrap().kind else {
        panic!()
    };
    assert_eq!(callee.staging().unwrap().0, StagingForm::Splice);
    assert_eq!(arguments[0].staging().unwrap().0, StagingForm::Lift);
}

#[test]
fn nested_quotes_and_stage_escapes_restore_the_outer_stage() {
    let quote = tail(
        "fn make() -> Unit ! {} { quote fn() -> Unit ! {} { let inner = quote fn() -> i64 ! {} { lift(n) }; splice(quote fn() -> i64 ! {} { lift(m) })() } }",
    );
    let (_, quoted) = quote.staging().unwrap();
    let ExprKind::Lambda(lambda) = &quoted.kind else {
        panic!()
    };
    let Statement::Let { value: inner, .. } = &lambda.body.statements[0] else {
        panic!()
    };
    assert_eq!(inner.staging().unwrap().0, StagingForm::Quote);
    let ExprKind::Call { callee, .. } = &lambda.body.tail.as_ref().unwrap().kind else {
        panic!()
    };
    let (form, operand) = callee.staging().unwrap();
    assert_eq!(form, StagingForm::Splice);
    assert_eq!(operand.staging().unwrap().0, StagingForm::Quote);
}

#[test]
fn staged_definition_keeps_the_generator_separate_from_the_body_signature() {
    let module = kush::parse("#[staged] pub fn cube(x: i64) -> i64 ! {panic} = power(3);").unwrap();
    assert!(module.items[0].public);
    let ItemKind::Function(function) = &module.items[0].item.kind else {
        panic!()
    };
    assert_eq!(function.name, "cube");
    assert_eq!(function.parameters.len(), 1);
    assert_eq!(function.effects.len(), 1);
    let (form, generator) = function
        .body
        .as_ref()
        .unwrap()
        .tail
        .as_ref()
        .unwrap()
        .staging()
        .unwrap();
    assert_eq!(form, StagingForm::Definition);
    assert!(matches!(generator.kind, ExprKind::Call { .. }));
}

#[test]
fn staged_attribute_and_initializer_must_match() {
    for source in [
        "fn f() -> i64 ! {} = generator();",
        "#[staged] fn f() -> i64 ! {} { 1 }",
        "#[staged] fn f() -> i64 ! {};",
        "#[staged] struct Bad {}",
        "#[staged] const x: i64 = 1;",
        "#[staged(1)] fn f() -> i64 ! {} = generator();",
        "#[staged] total fn f() -> i64 = generator();",
    ] {
        assert!(kush::parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn contextual_words_and_literals_are_not_rewritten() {
    let expr = tail("fn f() -> i64 ! {} { quote(1) }");
    assert!(expr.staging().is_none());
    assert!(
        kush::parse("fn f() -> Unit ! {} { let quote = 1; let splice = 2; let lift = 3; }").is_ok()
    );
    let expr = tail("fn f() -> Unit ! {} { \"quote fn() { splice(x) }\" }");
    assert!(matches!(expr.kind, ExprKind::String(_)));
    assert!(kush::parse("fn f() -> Unit ! {} { $stage_quote(1) }").is_err());
}

#[test]
fn staging_operands_and_nested_quotes_obey_the_parser_budget() {
    for expression in [
        "quote fn() -> i64 ! {} { lift() }",
        "quote fn() -> i64 ! {} { splice(x, y) }",
    ] {
        assert!(kush::parse(&format!("fn f() -> Unit ! {{}} {{ {expression} }}")).is_err());
    }
    let source = format!(
        "fn f() -> Unit ! {{}} {{ {}0{} }}",
        "quote fn() -> Unit ! {} { ".repeat(150),
        " }".repeat(150)
    );
    assert!(kush::parse(&source).is_err());
}

#[test]
fn unelaborated_quotes_fail_closed_instead_of_executing_as_closures() {
    let program = kush::program::load_source(
        "staging.kush",
        "fn main() -> Unit ! {alloc} { quote fn() -> Unit ! {} {} }",
    )
    .unwrap();
    let error = kush::executable::check_program(&program).err().unwrap();
    assert!(
        error
            .message
            .contains("staging form has not been elaborated"),
        "{}",
        error.message
    );
}

fn resolve_stages(source: &str) -> Result<kush::resolve::Resolution, kush::Diagnostic> {
    let program = kush::program::load_source("stages.kush", source).unwrap();
    kush::resolve::resolve_staged_program(&program)
}

#[test]
fn stages_reject_implicit_local_capture_including_generic_templates() {
    for source in [
        "fn make(n: i64) -> Code<fn() -> i64 ! {}> ! {alloc} { quote fn() -> i64 ! {} { n } }",
        "fn make<T>(n: T) -> Code<fn() -> T ! {}> ! {alloc} { quote fn() -> T ! {} { n } }",
        "fn make(n: i64) -> Unit ! {} { quote fn() -> Unit ! {} { quote fn() -> i64 ! {} { lift(n) } } }",
        "#[staged] fn f(x: i64) -> i64 ! {} = x;",
        "fn make() -> Unit ! {} { quote fn(x: i64) -> i64 ! {} { lift(x) } }",
    ] {
        let error = resolve_stages(source)
            .err()
            .unwrap_or_else(|| panic!("accepted {source}"));
        assert!(
            error.message.contains("belongs to stage"),
            "{}",
            error.message
        );
    }
}

#[test]
fn explicit_cross_stage_operations_and_quoted_shadowing_resolve() {
    for source in [
        "fn make(n: i64) -> Code<fn() -> i64 ! {}> ! {alloc} { quote fn() -> i64 ! {} { lift(n) } }",
        "fn make(n: i64) -> Unit ! {} { quote fn(n: i64) -> i64 ! {} { n } }",
        "fn make(n: i64) -> Unit ! {} { quote fn() -> i64 ! {} { let n = 2; n } }",
        "fn make(code: Code<fn(i64) -> i64 ! {}>) -> Unit ! {} { quote fn(x: i64) -> i64 ! {} { splice(code)(x) } }",
        "fn global() -> i64 ! {} { 1 } fn make() -> Unit ! {} { quote fn() -> i64 ! {} { global() } }",
    ] {
        resolve_stages(source).unwrap_or_else(|e| panic!("{source}: {}", e.message));
    }
}

#[test]
fn stage_metadata_uses_distinct_binding_identities_for_shadowed_names() {
    let resolution =
        resolve_stages("fn make(x: i64) -> Unit ! {} { quote fn(x: i64) -> i64 ! {} { x } }")
            .unwrap();
    let stages: Vec<_> = resolution
        .bindings
        .iter()
        .enumerate()
        .filter(|(_, binding)| binding.name == "x")
        .map(|(id, _)| resolution.binding_stages[&id])
        .collect();
    assert_eq!(stages, [0, 1]);
}

#[test]
fn stage_resolution_preserves_private_module_references_and_import_visibility() {
    let modules = kush::program::Memory(vec![("generator".into(),
        "module generator; fn secret() -> i64 ! {} { 7 } pub fn make() -> Code<fn() -> i64 ! {}> ! {alloc} { quote fn() -> i64 ! {} { secret() } }".into())]);
    let program = kush::program::load(
        "app.kush",
        "module app; use generator; fn secret() -> i64 ! {} { 99 } fn main() -> Unit ! {} {}",
        &modules,
    )
    .unwrap();
    let resolution = kush::resolve::resolve_staged_program(&program).unwrap();
    let generator_unit = program
        .units
        .iter()
        .position(|u| u.path == ["generator"])
        .unwrap();
    let secret = resolution
        .bindings
        .iter()
        .enumerate()
        .find(|(id, binding)| {
            binding.name == "secret" && resolution.unit_of.get(id) == Some(&generator_unit)
        })
        .unwrap()
        .0;
    assert!(resolution.references.iter().any(|r| r.binding == secret));
    let private = kush::program::load(
        "app.kush",
        "module app; use generator; fn main() -> i64 ! {} { generator.secret() }",
        &modules,
    )
    .unwrap();
    assert!(
        kush::resolve::resolve_staged_program(&private)
            .unwrap_err()
            .message
            .contains("private")
    );
}

#[test]
fn quote_statement_ends_before_a_new_line_starting_with_parens() {
    let module = kush::parse("fn make() -> i64 ! {} { quote fn() -> Unit ! {} {}\n(1) }").unwrap();
    let ItemKind::Function(function) = &module.items[0].item.kind else {
        panic!()
    };
    let block = function.body.as_ref().unwrap();
    assert_eq!(block.statements.len(), 1);
    assert!(matches!(
        block.tail.as_ref().unwrap().kind,
        ExprKind::Integer(_)
    ));
}
