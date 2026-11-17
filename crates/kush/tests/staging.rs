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
    assert!(source[body.span.start..body.span.end].starts_with("fn("));
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
fn quote_construction_requires_its_generation_effects() {
    let program = kush::program::load_source(
        "staging.kush",
        "fn main() -> Unit ! {alloc} { quote fn() -> Unit ! {} {} }",
    )
    .unwrap();
    let error = kush::executable::check_program(&program).err().unwrap();
    assert!(
        error.message.contains("requires effects {panic}"),
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

fn checked(source: &str) -> Result<kush::executable::Executable, String> {
    let program =
        kush::program::load_source("code-types.kush", source).map_err(|(_, e)| e.message)?;
    kush::executable::check_program(&program).map_err(|e| program.sources.render(&e))
}

#[test]
fn code_types_are_opaque_affine_values_with_a_static_callable_signature() {
    checked("fn consume(code: Code<fn(i64) -> i64 ! {panic}>) -> Unit ! {} {} fn main() -> Unit ! {} {}")
        .unwrap();
    let error = checked("fn twice(code: Code<fn() -> Unit ! {}>) -> Unit ! {} { let first = code; let second = code; } fn main() -> Unit ! {} {}")
        .err().unwrap();
    assert!(error.contains("moved"), "{error}");
    assert!(checked("fn forge(bytes: Bytes) -> Code<fn() -> Unit ! {}> ! {} { bytes } fn main() -> Unit ! {} {}")
        .is_err());
    assert!(checked("fn forge(bytes: Bytes) -> Code<fn() -> Unit ! {}> ! {} { (bytes,) } fn main() -> Unit ! {} {}")
        .is_err());
}

#[test]
fn code_types_preserve_latent_effects_and_reject_non_reusable_signatures() {
    for signature in [
        "i64",
        "once fn() -> Unit ! {}",
        "linear once fn() -> Unit ! {}",
    ] {
        let source = format!(
            "fn bad(code: Code<{signature}>) -> Unit ! {{}} {{}} fn main() -> Unit ! {{}} {{}}"
        );
        let error = checked(&source).err().unwrap();
        assert!(error.contains("reusable fn"), "{error}");
    }
    let error = checked("fn strip(code: Code<fn() -> Unit ! {io}>) -> Code<fn() -> Unit ! {}> ! {} { code } fn main() -> Unit ! {} {}")
        .err().unwrap();
    assert!(error.contains("Code"), "{error}");
    assert!(checked("fn wrong(code: Code<fn(i64) -> i64 ! {}>) -> Code<fn(Bool) -> i64 ! {}> ! {} { code } fn main() -> Unit ! {} {}")
        .is_err());
}

#[test]
fn code_signature_arguments_infer_through_generic_helpers() {
    checked("fn identity<F>(code: Code<F>) -> Code<F> ! {} { code } fn relay(code: Code<fn(i64) -> i64 ! {panic}>) -> Code<fn(i64) -> i64 ! {panic}> ! {} { identity(code) } fn main() -> Unit ! {} {}")
        .unwrap();
}

#[test]
fn constructing_a_checked_quote_does_not_execute_its_body_and_releases_storage() {
    let program = checked("fn main() -> Unit ! {alloc, panic, io} { let code = quote fn() -> Unit ! {io, panic} { print_i64(99) }; let cloned = Code.clone(&code); print_i64(7) }")
        .unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(output, b"7\n");
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stats.allocations > 0);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("quote");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"7\n");
    }
}

#[test]
fn every_quotation_body_is_checked_before_it_can_execute() {
    assert!(checked("fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} { quote fn() -> i64 ! {} { true } } fn main() -> Unit ! {} {}")
        .is_err());
    assert!(checked("fn make() -> Code<fn() -> Unit ! {}> ! {alloc, panic} { quote fn() -> Unit ! {} { print_i64(1) } } fn main() -> Unit ! {} {}")
        .is_err());
    checked("fn make() -> Code<fn() -> Unit ! {io, panic}> ! {alloc, panic} { quote fn() -> Unit ! {io, panic} { print_i64(1) } } fn main() -> Unit ! {} {}")
        .unwrap();
}

#[test]
fn staged_declarations_run_checked_generators_and_publish_native_functions() {
    let program = checked(
        r#"
fn choose(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    let mut left = n;
    while left > 1 { left = left - 1; }
    if left == 1 { quote fn(x: i64) -> i64 ! {panic} { x + 1 } }
    else { quote fn(x: i64) -> i64 ! {panic} { x - 1 } }
}
#[staged] fn increment(x: i64) -> i64 ! {panic} = choose(3);
fn main() -> i64 ! {panic} { increment(41) }
"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("staged");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(output.status.code(), Some(42));
    }
}

#[test]
fn compile_time_generation_rejects_host_effects_and_dependency_cycles() {
    let error = checked("fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic, io} { print_i64(1); quote fn() -> i64 ! {} { 1 } } #[staged] fn value() -> i64 ! {} = make(); fn main() -> i64 ! {} { value() }").err().unwrap();
    assert!(error.contains("effects"), "{error}");
    let error = checked("fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} { value(); quote fn() -> i64 ! {} { 1 } } #[staged] fn value() -> i64 ! {} = make(); fn main() -> i64 ! {} { value() }").err().unwrap();
    assert!(error.contains("cyclic staged"), "{error}");
}

#[test]
fn lifted_scalars_specialize_a_template_independently_for_each_declaration() {
    let program = checked(
        r#"
fn add(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    quote fn(x: i64) -> i64 ! {panic} { x + lift(n * 2) }
}
#[staged] fn first(x: i64) -> i64 ! {panic} = add(3);
#[staged] fn second(x: i64) -> i64 ! {panic} = add(7);
fn main() -> i64 ! {panic} { first(10) + second(10) }
"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 40);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifted");
        kush::native::build(&program, &binary).unwrap();
        assert_eq!(
            std::process::Command::new(binary).status().unwrap().code(),
            Some(40)
        );
    }
}

#[test]
fn recursive_generators_compose_typed_fragments_hygienically() {
    let program = checked(
        r#"
fn power(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    if n == 0 { quote fn(x: i64) -> i64 ! {panic} { 1 } }
    else {
        let smaller = power(n - 1);
        quote fn(x: i64) -> i64 ! {panic} { x * splice(smaller)(x) }
    }
}
#[staged] fn cube(x: i64) -> i64 ! {panic} = power(3);
#[staged] fn square(x: i64) -> i64 ! {panic} = power(2);
fn main() -> i64 ! {panic} { cube(3) + square(4) }
"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 43);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("power");
        kush::native::build(&program, &binary).unwrap();
        assert_eq!(
            std::process::Command::new(binary).status().unwrap().code(),
            Some(43)
        );
    }
}

#[test]
fn owned_text_and_float_lifts_preserve_values_and_independent_storage() {
    let program = checked(r#"
fn blob(value: Bytes) -> Code<fn() -> Bytes ! {alloc, panic}> ! {alloc, panic} {
    quote fn() -> Bytes ! {alloc, panic} { lift(value) }
}
fn text(value: String) -> Code<fn() -> String ! {alloc, panic}> ! {alloc, panic} {
    quote fn() -> String ! {alloc, panic} { lift(value) }
}
fn number(value: f64) -> Code<fn() -> f64 ! {}> ! {alloc, panic} {
    quote fn() -> f64 ! {} { lift(value) }
}
#[staged] fn bytes() -> Bytes ! {alloc, panic} = blob(Bytes.from("abc"));
#[staged] fn string() -> String ! {alloc, panic} = text("héllo");
#[staged] fn floating() -> f64 ! {} = number(1.5);
fn main() -> i64 ! {alloc, panic} {
    let first = bytes();
    let second = bytes();
    let third = string();
    if Bytes.len(&first) + Bytes.len(&second) + String.len(&third) == 12 && floating() == 1.5 { 42 } else { 0 }
}
"#).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        for backend in [
            kush::native::Backend::Cranelift,
            kush::native::Backend::Llvm,
        ] {
            let binary = scratch.path().join(format!("lifted-{backend:?}"));
            let options = kush::native::CodegenOptions {
                backend,
                ..Default::default()
            };
            kush::native::build_with_codegen(
                &program,
                &binary,
                false,
                &Default::default(),
                options,
            )
            .unwrap();
            assert_eq!(
                std::process::Command::new(binary).status().unwrap().code(),
                Some(42)
            );
        }
    }
}

#[test]
fn nested_stages_lift_from_the_immediately_enclosing_level() {
    let program = checked(
        r#"
fn stage(n: i64) -> Code<fn(i64) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic}> ! {alloc, panic} {
    quote fn(x: i64) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic} {
        quote fn() -> i64 ! {panic} { lift(x) + lift(lift(n)) }
    }
}
#[staged] fn first(x: i64) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic} = stage(5);
#[staged] fn second() -> i64 ! {panic} = first(37);
fn main() -> i64 ! {panic} { second() }
"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("nested");
        kush::native::build(&program, &binary).unwrap();
        assert_eq!(
            std::process::Command::new(binary).status().unwrap().code(),
            Some(42)
        );
    }
}

#[test]
fn splice_types_ownership_and_owned_lift_effects_are_checked() {
    for source in [
        "fn bad(code: Code<fn() -> Bool ! {}>) -> Code<fn() -> i64 ! {}> ! {alloc, panic} { quote fn() -> i64 ! {} { splice(code)() } } fn main() -> Unit ! {} {}",
        "fn bad(code: Code<fn() -> i64 ! {}>) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic} { quote fn() -> i64 ! {panic} { splice(code)() + splice(code)() } } fn main() -> Unit ! {} {}",
        "fn bad(bytes: Bytes) -> Code<fn() -> Bytes ! {}> ! {alloc, panic} { quote fn() -> Bytes ! {} { lift(bytes) } } fn main() -> Unit ! {} {}",
        "fn bad(code: Code<fn() -> Unit ! {}>) -> i64 ! {} { code.unknown } fn main() -> Unit ! {} {}",
    ] {
        assert!(checked(source).is_err(), "accepted {source}");
    }
    checked("fn good(code: Code<fn() -> i64 ! {}>) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic} { quote fn() -> i64 ! {panic} { splice(Code.clone(&code))() + splice(Code.clone(&code))() } } fn main() -> Unit ! {} {}")
        .unwrap();
}

#[test]
fn generation_panics_and_resource_exhaustion_are_compile_diagnostics() {
    let error = checked("fn make() -> Code<fn() -> Unit ! {}> ! {alloc, panic} { panic() } #[staged] fn target() -> Unit ! {} = make(); fn main() -> Unit ! {} {}")
        .err().unwrap();
    assert!(error.contains("panic"), "{error}");
    let error = checked("fn make() -> Code<fn() -> Unit ! {}> ! {alloc, panic} { while true {} quote fn() -> Unit ! {} {} } #[staged] fn target() -> Unit ! {} = make(); fn main() -> Unit ! {} {}")
        .err().unwrap();
    assert!(error.contains("budget"), "{error}");
    let error = checked("fn make() -> Code<fn() -> Unit ! {}> ! {alloc, panic} { let a = Bytes.with_capacity(16777216); let b = Bytes.with_capacity(16777216); let c = Bytes.with_capacity(16777216); let d = Bytes.with_capacity(16777216); let e = Bytes.with_capacity(16777216); quote fn() -> Unit ! {} {} } #[staged] fn target() -> Unit ! {} = make(); fn main() -> Unit ! {} {}")
        .err().unwrap();
    assert!(error.contains("allocation budget"), "{error}");
}

#[test]
fn power_example_runs_without_a_runtime_generator_call() {
    let program = checked(include_str!("../../../examples/staging-power.kush")).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(output, b"27\n16\n");
}

#[test]
fn specialization_keeps_erased_parameter_contracts() {
    let program = checked(
        r#"
fn make(n: i64) -> Code<fn(i64 @[0]) -> i64 ! {}> ! {alloc, panic} {
    quote fn(x: i64 @[0]) -> i64 ! {} { lift(n) }
}
#[staged] fn value(x: i64 @[0]) -> i64 ! {} = make(42);
fn main() -> i64 ! {} { value(999) }
"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 42);
}
