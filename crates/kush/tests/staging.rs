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
        "export \"staged_f\" fn f() -> i64 ! {} = generator();",
        "#[staged] export \"staged_f\" fn f() -> i64 ! {} { 1 }",
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
        "module generator; fn secret() -> i64 ! {} { 7 } pub fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} { quote fn() -> i64 ! {} { secret() } }".into())]);
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
    let spliced = kush::program::load(
        "app.kush",
        r#"
module app;
use generator;
fn secret() -> i64 ! {} { 99 }
fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    let fragment = generator.make();
    quote fn() -> i64 ! {} { splice(fragment)() }
}
#[staged] fn compiled() -> i64 ! {} = make();
fn main() -> i64 ! {} { compiled() }
"#,
        &modules,
    )
    .unwrap();
    let spliced = kush::executable::check_program(&spliced).unwrap();
    assert_eq!(spliced.evaluate(&mut Vec::new()).unwrap(), 7);
    assert_native_result(&spliced, 7);
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
fn runtime_compilation_specializes_independent_owners_and_releases_them() {
    let source = r#"
use std.result.Result;
fn power(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    if n == 0 { quote fn(x: i64) -> i64 ! {panic} { 1 } }
    else {
        let smaller = power(n - 1);
        quote fn(x: i64) -> i64 ! {panic} { x * splice(smaller)(x) }
    }
}
fn main() -> i64 ! {alloc, panic} {
    let cube = match Code.compile(power(3)) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    let square = match Code.compile(power(2)) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    Code.call(&cube, 3) + Code.call(&square, 4) + Code.call(&cube, 2)
}
"#;
    let exe = checked(source).unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 51);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 51);
}

fn clang_available() -> bool {
    std::process::Command::new(std::env::var_os("KUSH_CLANG").unwrap_or_else(|| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

/// The native result under Cranelift and, when `clang` is installed, LLVM.
fn assert_native_result(exe: &kush::executable::Executable, expected: i32) {
    assert_native_result_with_budget(exe, expected, None);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    if clang_available() {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("runtime-staging-llvm");
        let options = kush::native::CodegenOptions {
            backend: kush::native::Backend::Llvm,
            ..Default::default()
        };
        kush::native::build_with_codegen(exe, &binary, false, &Default::default(), options)
            .unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(output.status.code(), Some(expected), "LLVM: {output:?}");
    }
}

fn assert_native_result_with_budget(
    exe: &kush::executable::Executable,
    expected: i32,
    budget: Option<&str>,
) {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("runtime-staging");
        kush::native::build(exe, &binary).unwrap();
        let mut command = std::process::Command::new(binary);
        command.env_remove("KUSH_ALLOC_FAIL_AFTER");
        if let Some(budget) = budget {
            command.env("KUSH_ALLOC_FAIL_AFTER", budget);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(expected), "{output:?}");
    }
}

#[test]
fn compiled_owner_is_borrowed_during_argument_evaluation() {
    let source = r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(quote fn(x: i64) -> i64 ! {} { x }) {
        Result.Ok(owner) => owner, Result.Err(e) => return e,
    };
    Code.call(&owner, { drop(owner); 4 })
}
"#;
    let error = checked(source).unwrap_err();
    assert!(error.contains("cannot move or drop an owner"), "{error}");
}

#[test]
fn runtime_compile_failure_consumes_its_graph() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    match Code.compile(quote fn() -> i64 ! {} { 42 }) {
        Result.Ok(owner) => Code.call(&owner), Result.Err(e) => e,
    }
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_alloc_budget(&mut Vec::new(), 0).unwrap();
    assert_eq!(result, 12);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result_with_budget(&exe, 12, Some("0"));
    assert_native_result(&exe, 42);
}

#[test]
fn runtime_compilation_copies_lifted_storage_and_returns_owned_results() {
    let exe = checked(
        r#"
use std.result.Result;
fn make(text: Bytes) -> Code<fn() -> Bytes ! {alloc, panic}> ! {alloc, panic} {
    quote fn() -> Bytes ! {alloc, panic} { lift(text) }
}

fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(make(Bytes.from("hello"))) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    let first = Code.call(&owner);
    let second = Code.call(&owner);
    drop(owner);
    Bytes.len(&first) + Bytes.len(&second)
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 10);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 10);
}

#[test]
fn runtime_compilation_relocates_static_data_and_loads_scalar_holes() {
    let exe = checked(
        r#"
use std.result.Result;
fn make(n: i64) -> Code<fn() -> i64 ! {alloc, panic}> ! {alloc, panic} {
    quote fn() -> i64 ! {alloc, panic} {
        let data = Bytes.from("static data");
        Bytes.len(&data) + lift(n)
    }
}
fn main() -> i64 ! {io, alloc, panic} {
    let input = match IO.read_line(IO.stdin(), Bytes.with_capacity(32)) {
        Result.Ok(bytes) => bytes, Result.Err(e) => return -e,
    };
    let owner = match Code.compile(make(Bytes.len(&input))) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    Code.call(&owner)
}
"#,
    )
    .unwrap();
    let input = b"runtime input";
    let expected = 11 + input.len() as i32;
    assert_eq!(
        exe.evaluate_with_io(&mut input.as_slice(), &mut Vec::new())
            .unwrap(),
        i64::from(expected),
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("runtime-input");
        let input_path = scratch.path().join("input");
        std::fs::write(&input_path, input).unwrap();
        kush::native::build(&exe, &binary).unwrap();
        let output = std::process::Command::new(binary)
            .stdin(std::fs::File::open(input_path).unwrap())
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(expected), "{output:?}");
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn runtime_publication_enforces_wx_and_releases_a_failed_mapping() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    match Code.compile(quote fn() -> i64 ! {} { 42 }) {
        Result.Ok(owner) => Code.call(&owner), Result.Err(e) => e,
    }
}
"#,
    )
    .unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("staged");
    let source = scratch.path().join("mapping-probe.c");
    let preload = scratch.path().join("mapping-probe.so");
    std::fs::write(
        &source,
        r#"
#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

static void *stage;
static int attempted, published, released;

void *mmap(void *address, size_t size, int prot, int flags, int fd, off_t offset) {
    assert((prot & (PROT_WRITE | PROT_EXEC)) != (PROT_WRITE | PROT_EXEC));
    if (size == 64u * 1024u * 1024u) {
        assert(!attempted && prot == (PROT_READ | PROT_WRITE));
        attempted = 1;
        if (getenv("KUSH_TEST_REJECT_MAPPING")) { errno = ENOMEM; return MAP_FAILED; }
    }
    void *result = (void *)syscall(SYS_mmap, address, size, prot, flags, fd, offset);
    if (size == 64u * 1024u * 1024u && result != MAP_FAILED) {
        stage = result;
    }
    return result;
}
int mprotect(void *address, size_t size, int prot) {
    assert((prot & (PROT_WRITE | PROT_EXEC)) != (PROT_WRITE | PROT_EXEC));
    if (address == stage) {
        assert(!published && !released && prot == (PROT_READ | PROT_EXEC));
        published = 1;
        if (getenv("KUSH_TEST_REJECT_PUBLICATION")) { errno = EACCES; return -1; }
    }
    return (int)syscall(SYS_mprotect, address, size, prot);
}
int munmap(void *address, size_t size) {
    if (address == stage) {
        assert(published && !released && size == 64u * 1024u * 1024u);
        released = 1;
    }
    return (int)syscall(SYS_munmap, address, size);
}
__attribute__((destructor)) static void verify_release(void) {
    assert(attempted == 1);
    if (getenv("KUSH_TEST_REJECT_MAPPING")) assert(!stage && !published && !released);
    else assert(stage && published == 1 && released == 1);
}
"#,
    )
    .unwrap();
    let compile = std::process::Command::new("cc")
        .args(["-shared", "-fPIC", "-o"])
        .arg(&preload)
        .arg(&source)
        .output()
        .unwrap();
    assert!(compile.status.success(), "{compile:?}");
    kush::native::build(&exe, &binary).unwrap();
    for (failure, expected) in [
        (None, 42),
        (Some("KUSH_TEST_REJECT_PUBLICATION"), 13),
        (Some("KUSH_TEST_REJECT_MAPPING"), 12),
    ] {
        let mut command = std::process::Command::new(&binary);
        command
            .env("LD_PRELOAD", &preload)
            .env_remove("KUSH_TEST_REJECT_PUBLICATION")
            .env_remove("KUSH_TEST_REJECT_MAPPING")
            .env_remove("KUSH_ALLOC_FAIL_AFTER");
        if let Some(failure) = failure {
            command.env(failure, "1");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(expected), "{output:?}");
    }
}

#[test]
fn compiled_calls_preserve_aggregate_and_erased_parameter_abis() {
    let exe = checked(
        r#"
use std.result.Result;
struct Pair { a: i64, b: i64 }
fn shifted(n: i64) -> Code<fn(Pair, i64 @[0]) -> Pair ! {panic}> ! {alloc, panic} {
    quote fn(p: Pair, unused: i64 @[0]) -> Pair ! {panic} {
        Pair { a: p.a + lift(n), b: p.b }
    }
}
fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(shifted(10)) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    let p = Code.call(&owner, Pair { a: 12, b: 20 }, 99);
    p.a + p.b
}
"#,
    )
    .unwrap();
    assert_eq!(exe.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&exe, 42);
}

#[test]
fn compiled_calls_preserve_exact_parameter_usage() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    let code = quote fn(x: i64 @[1]) -> i64 ! {} { x };
    match Code.compile(code) {
        Result.Ok(owner) => Code.call(&owner, 42),
        Result.Err(e) => e,
    }
}
"#,
    )
    .unwrap();
    assert_eq!(exe.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&exe, 42);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    if clang_available() {
        // An LLVM executable carries Cranelift recipes for its quotations.
        for options in [
            kush::native::CodegenOptions {
                backend: kush::native::Backend::Llvm,
                ..Default::default()
            },
            kush::native::CodegenOptions::release_llvm(),
        ] {
            let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
            let binary = scratch.path().join("llvm-runtime-recipes");
            kush::native::build_with_codegen(&exe, &binary, false, &Default::default(), options)
                .unwrap();
            let output = std::process::Command::new(binary).output().unwrap();
            assert_eq!(output.status.code(), Some(42), "{output:?}");
        }
    }
}

#[test]
fn repeated_runtime_stages_can_drop_the_previous_owner_before_compilation() {
    let exe = checked(
        r#"
use std.result.Result;
fn outer(n: i64) -> Code<fn(i64) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic}> ! {alloc, panic} {
    quote fn(x: i64) -> Code<fn() -> i64 ! {panic}> ! {alloc, panic} {
        quote fn() -> i64 ! {panic} { lift(x) + lift(lift(n)) }
    }
}
fn main() -> i64 ! {alloc, panic} {
    let mut sum = 0;
    let mut i = 0;
    while i < 7 {
        let first = match Code.compile(outer(i)) {
            Result.Ok(owner) => owner, Result.Err(e) => return -e,
        };
        let graph = Code.call(&first, 3);
        drop(first);
        let second = match Code.compile(graph) {
            Result.Ok(owner) => owner, Result.Err(e) => return -e,
        };
        sum = sum + Code.call(&second);
        i = i + 1;
    }
    sum
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn compiled_call_may_return_a_view_borrowed_from_its_argument() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(quote fn(xs: &[i64]) -> &[i64] ! {} { xs }) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    let xs: [i64; 1] = [42];
    let view = Code.call(&owner, &xs[..]);
    drop(owner);
    view[0]
}
"#,
    )
    .unwrap();
    assert_eq!(exe.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&exe, 42);
}

#[test]
fn independent_threads_compile_and_drop_the_same_template() {
    let exe = checked(
        r#"
use std.result.Result;
fn run(n: i64) -> i64 ! {alloc, panic} {
    let mut i = 0;
    while i < 64 {
        let owner = match Code.compile(quote fn() -> i64 ! {panic} { lift(n) + lift(i) }) {
            Result.Ok(owner) => owner, Result.Err(e) => return -e,
        };
        if Code.call(&owner) != n + i { return -1; }
        drop(owner);
        i = i + 1;
    }
    n
}
fn main() -> i64 ! {alloc, panic} {
    Thread.scope(fn() -> i64 ! {alloc, panic} {
        let a = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(10) });
        let b = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(12) });
        let c = Thread.spawn(fn() -> i64 ! {alloc, panic} { run(20) });
        Thread.join(a) + Thread.join(b) + Thread.join(c)
    })
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn compiled_calls_resume_after_yielding_to_another_task() {
    let exe = checked(
        r#"
use std.result.Result;
enum TaskExit<T> { Completed(T), Cancelled }
fn main() -> i64 ! {alloc, panic, suspend} {
    Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
        let child = Task.spawn(fn() -> i64 ! {alloc, panic, suspend} {
            let owner = match Code.compile(quote fn() -> i64 ! {suspend} {
                if Task.yield() { return -1; }
                20
            }) {
                Result.Ok(owner) => owner, Result.Err(e) => return -e,
            };
            Code.call(&owner)
        });
        Task.yield();
        let other = match Code.compile(quote fn() -> i64 ! {} { 22 }) {
            Result.Ok(owner) => owner, Result.Err(e) => return -e,
        };
        let value = Code.call(&other);
        drop(other);
        match Task.join(child) {
            TaskExit.Completed(result) => result + value,
            TaskExit.Cancelled => -2,
        }
    })
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn cancelling_a_suspended_compiled_call_releases_its_owner() {
    let exe = checked(
        r#"
use std.result.Result;
enum TaskExit<T> { Completed(T), Cancelled }
fn main() -> i64 ! {alloc, panic, suspend} {
    Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
        let child = Task.spawn(fn() -> i64 ! {alloc, panic, suspend} {
            let owner = match Code.compile(quote fn() -> i64 ! {suspend} {
                while !Task.yield() {}
                0
            }) {
                Result.Ok(owner) => owner, Result.Err(e) => return -e,
            };
            Code.call(&owner)
        });
        Task.yield();
        Task.cancel(&child);
        match Task.join(child) {
            TaskExit.Completed(result) => result,
            TaskExit.Cancelled => 42,
        }
    })
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn threads_can_call_the_same_compiled_owner_through_shared_borrows() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    let delta = 10;
    let owner = match Code.compile(quote fn(x: i64) -> i64 ! {panic} { x + lift(delta) }) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    let owners: Vec<CompiledCode<fn(i64) -> i64 ! {panic}>> = Vec.with_capacity(1);
    let owners = Vec.push(owners, owner);
    let view = &owners[..];
    let total = Thread.scope(fn() -> i64 ! {alloc, panic} {
        let first = Thread.spawn(fn() -> i64 ! {panic} { Code.call(&view[0], 7) });
        let second = Thread.spawn(fn() -> i64 ! {panic} { Code.call(&view[0], 15) });
        Thread.join(first) + Thread.join(second)
    });
    drop(owners);
    total
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn a_panic_during_compiled_execution_releases_its_owner() {
    let exe = checked(
        r#"
use std.result.Result;
use std.task.Panic;
fn main() -> i64 ! {alloc, panic, suspend} {
    match Task.catch(fn() -> i64 ! {alloc, panic} {
        let owner = match Code.compile(quote fn() -> i64 ! {panic} { panic() }) {
            Result.Ok(owner) => owner, Result.Err(e) => return -e,
        };
        Code.call(&owner)
    }) {
        Result.Ok(value) => value,
        Result.Err(_) => 42,
    }
}
"#,
    )
    .unwrap();
    let (result, stats) = exe.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&exe, 42);
}

#[test]
fn runtime_compilation_rejects_splice_addresses_that_can_outlive_the_owner() {
    let exe = checked(
        r#"
use std.result.Result;
fn main() -> i64 ! {alloc, panic} {
    let fragment = quote fn() -> i64 ! {} { 42 };
    let composed = quote fn() -> i64 ! {} {
        let f = splice(fragment);
        f()
    };
    match Code.compile(composed) {
        Result.Ok(owner) => Code.call(&owner), Result.Err(e) => e,
    }
}
"#,
    )
    .unwrap();
    assert_eq!(exe.evaluate(&mut Vec::new()).unwrap(), 95);
    assert_native_result(&exe, 95);
}

#[test]
fn compile_time_generators_cannot_invoke_the_runtime_compiler() {
    let error = checked(
        r#"
use std.result.Result;
fn generate() -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    let graph = quote fn() -> i64 ! {} { 41 };
    let owner = match Code.compile(graph) {
        Result.Ok(owner) => owner, Result.Err(_) => panic(),
    };
    let value = Code.call(&owner);
    quote fn() -> i64 ! {} { lift(value) }
}
#[staged] fn answer() -> i64 ! {} = generate();
fn main() -> i64 ! {} { answer() }
"#,
    )
    .unwrap_err();
    assert!(
        error.contains("runtime compilation is unavailable"),
        "{error}"
    );
}

#[test]
fn compile_time_templates_do_not_become_runtime_recipes() {
    let source = r#"
use std.result.Result;
fn offset(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    quote fn(x: i64) -> i64 ! {panic} { x + lift(n) }
}
fn scale(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    quote fn(x: i64) -> i64 ! {panic} { x * lift(n) }
}
#[staged] fn add_two(x: i64) -> i64 ! {panic} = offset(2);
fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(scale(4)) {
        Result.Ok(owner) => owner, Result.Err(e) => return -e,
    };
    Code.call(&owner, add_two(8))
}
"#;
    let program = checked(source).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 40);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("pruned-recipes");
        let ir = kush::native::build_with_clif(&program, &binary).unwrap();
        assert_eq!(ir.matches("; staging recipe ").count(), 1, "{ir}");
        assert!(!ir.contains("; offset\n"), "{ir}");
        let native = std::process::Command::new(binary).output().unwrap();
        assert_eq!(native.status.code(), Some(40), "{native:?}");
    }
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
fn unused_generic_declarations_still_check_type_independent_quotes() {
    let source = r#"
fn unused<T: Type>() -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    quote fn() -> i64 ! {} { true }
}
fn main() -> i64 ! {} { 42 }
"#;
    let error = checked(source).unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    let valid = checked(&source.replace("{ true }", "{ 1 }")).unwrap();
    assert_eq!(valid.evaluate(&mut Vec::new()).unwrap(), 42);
}

#[test]
fn unused_generic_quotes_check_rigid_return_types() {
    let source = r#"
fn unused<T: Type, U: Type>() -> Code<fn(T, U) -> T ! {}> ! {alloc, panic} {
    quote fn(x: T, y: U) -> T ! {} { x }
}
fn main() -> i64 ! {} { 42 }
"#;
    checked(source).unwrap();
    for wrong in ["y", "true", "if true { x } else { y }", "return y;"] {
        let error = checked(&source.replace("{ x }", &format!("{{ {wrong} }}"))).unwrap_err();
        assert!(error.contains("for every specialization"), "{error}");
    }
}

#[test]
fn unused_generic_quotes_check_inferred_types_and_moves() {
    let source = r#"
fn unused<T: Type, U: Type>() -> Code<fn(T, U) -> T ! {}> ! {alloc, panic} {
    quote fn(x: T, y: U) -> T ! {} { let result = x; result }
}
fn main() -> i64 ! {} { 42 }
"#;
    checked(source).unwrap();
    let wrong_type = source.replace("let result = x", "let result = y");
    let error = checked(&wrong_type).unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    let moved = source.replace("; result", "; x");
    let error = checked(&moved).unwrap_err();
    assert!(error.contains("moved"), "{error}");
}

#[test]
fn unused_generic_quotes_reject_fixed_result_mismatches() {
    let source = r#"
fn unused<N: Nat>() -> Code<fn([i64; N]) -> Bool ! {}> ! {alloc, panic} {
    quote fn(x: [i64; N]) -> Bool ! {} { 31 }
}
fn main() -> i64 ! {} { 42 }
"#;
    assert!(checked(source).unwrap_err().contains("cannot return an integer"));
    checked(&source.replace("{ 31 }", "{ true }")).unwrap();
}

#[test]
fn unused_generic_quote_rows_must_guarantee_direct_effects() {
    let source = r#"
fn unused<e: Effects>() -> Code<fn() -> Unit ! {e}> ! {alloc, panic} {
    quote fn() -> Unit ! {e} { print_i64(271) }
}
fn main() -> i64 ! {} { 42 }
"#;
    assert!(checked(source).unwrap_err().contains("does not guarantee {io, panic}"));
    let bounded = source.replace("e: Effects", "e: Effects + (io | panic)");
    checked(&bounded).unwrap();
    let subtract = bounded.replace("! {e}", "! {e - io}");
    assert!(checked(&subtract).unwrap_err().contains("does not guarantee {io}"));
}

#[test]
fn unused_generic_quotes_check_effects_of_called_functions() {
    let source = r#"
fn show() -> Unit ! {io, panic} { print_i64(271) }
fn unused<e: Effects>() -> Code<fn() -> Unit ! {e}> ! {alloc, panic} {
    quote fn() -> Unit ! {e} { show() }
}
fn main() -> i64 ! {} { 42 }
"#;
    assert!(checked(source).unwrap_err().contains("requires effects {io, panic}"));
    let bounded = source.replace("e: Effects", "e: Effects + (io | panic)");
    assert_eq!(checked(&bounded).unwrap().evaluate(&mut Vec::new()).unwrap(), 42);

    let different_rows = r#"
fn unused<e: Effects, f: Effects>(code: Code<fn() -> Unit ! {e}>)
    -> Code<fn() -> Unit ! {f}> ! {alloc, panic} {
    quote fn() -> Unit ! {f} { splice(code)() }
}
fn main() -> i64 ! {} { 42 }
"#;
    assert!(checked(different_rows).unwrap_err().contains("requires effects"));
}

#[test]
fn generic_quotation_aliases_are_checked_even_if_specializations_agree() {
    let source = r#"
fn make<T: Type, U: Type>() -> Code<fn(T, U) -> T ! {}> ! {alloc, panic} {
    quote fn(x: T, y: U) -> T ! {} { let result = y; result }
}
#[staged] fn choose(x: i64, y: i64) -> i64 ! {} = make::<i64, i64>();
fn main() -> i64 ! {} { choose(11, 31) }
"#;
    let error = checked(source).unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    let valid = checked(&source.replace("let result = y", "let result = x")).unwrap();
    assert_eq!(valid.evaluate(&mut Vec::new()).unwrap(), 11);
}

#[test]
fn generic_generators_can_lift_a_concrete_scalar_specialization() {
    let program = checked(r#"
fn specialize<T: Type>(value: T) -> Code<fn() -> T ! {}> ! {alloc, panic} {
    quote fn() -> T ! {} { lift(value) }
}
#[staged] fn first() -> i64 ! {} = specialize(42);
fn main() -> i64 ! {} { first() }
"#).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);
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
fn nested_closures_own_lifted_text_independently() {
    let program = checked(r#"
use std.result.Result;
fn specialize(text: Bytes) -> Code<fn() -> i64 ! {alloc, panic}> ! {alloc, panic} {
    quote fn() -> i64 ! {alloc, panic} {
        let read = fn() -> i64 ! {alloc, panic} {
            let copy = lift(text);
            Bytes.get(&copy, 0)
        };
        read()
    }
}
#[staged] fn aot() -> i64 ! {alloc, panic} = specialize(Bytes.from("*"));
fn main() -> i64 ! {alloc, panic} {
    let owner = match Code.compile(specialize(Bytes.from("*"))) {
        Result.Ok(owner) => owner, Result.Err(e) => return e,
    };
    if aot() == 42 && Code.call(&owner) == 42 { Code.call(&owner) } else { 1 }
}
"#).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&program, 42);
}

#[test]
fn aot_splices_are_specialized_inside_nested_closures() {
    let program = checked(r#"
fn specialize(fragment: Code<fn() -> i64 ! {}>) -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    quote fn() -> i64 ! {} {
        let inner = fn() -> i64 ! {} { splice(fragment)() };
        inner()
    }
}
#[staged] fn first() -> i64 ! {} = specialize(quote fn() -> i64 ! {} { 20 });
#[staged] fn second() -> i64 ! {} = specialize(quote fn() -> i64 ! {} { 22 });
fn main() -> i64 ! {panic} { first() + second() }
"#).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);
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
fn generators_may_use_arenas_within_the_generation_budget() {
    let source = r#"
fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    let arena = Arena.new();
    let first = Arena.alloc(&arena, 20);
    let second = Arena.alloc(&arena, Box.new(22));
    drop(arena);
    let n = ArenaBox.take(first) + Box.take(ArenaBox.take(second));
    quote fn() -> i64 ! {} { lift(n) }
}
#[staged] fn answer() -> i64 ! {} = make();
fn main() -> i64 ! {} { answer() }
"#;
    let program = checked(source).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);

    // Arena chunks live outside the heap; they still count against the budget.
    let huge = r#"
fn huge(need: i64, current: i64) -> i64 ! {} { 1099511627776 }
fn make() -> Code<fn() -> i64 ! {}> ! {alloc, panic} {
    let arena = Arena.with_strategy(huge);
    let filler = Arena.alloc(&arena, 1);
    drop(filler);
    drop(arena);
    quote fn() -> i64 ! {} { 42 }
}
#[staged] fn answer() -> i64 ! {} = make();
fn main() -> i64 ! {} { answer() }
"#;
    let error = checked(huge).err().unwrap();
    assert!(error.contains("allocation budget"), "{error}");
}

#[test]
fn power_example_runs_without_a_runtime_generator_call() {
    let program = checked(include_str!("../../../examples/staging-power.kush")).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(output, b"27\n16\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("staging-power");
        let ir = kush::native::build_with_clif(&program, &binary).unwrap();
        assert!(ir.contains("; cube\n") && ir.contains("; square\n"), "{ir}");
        assert!(!ir.contains("; power\n") && !ir.contains("$staging_init"), "{ir}");
        let executable = std::fs::read(&binary).unwrap();
        assert!(!executable.windows(8).any(|bytes| {
            matches!(bytes, b"KUSHCD01" | b"KUSHCD02" | b"KUSHCD03")
        }));
        let native = std::process::Command::new(binary).output().unwrap();
        assert!(native.status.success(), "{native:?}");
        assert_eq!(native.stdout, output);
    }
}

#[test]
fn specialized_bytecode_matches_the_interpreter() {
    let program = checked(include_str!("../../../examples/staging-interpreter.kush")).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(stats.allocations, stats.deallocations, "{stats:?}");
    assert_native_result(&program, 42);
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

#[test]
fn staged_mutable_refinement_checks_the_generated_body() {
    let source = r#"
fn write_value(v: &mut Vec<i64>) -> Unit ! {alloc, panic} {
    v.push(99);
    v[0] = 42;
}
#[staged] fn update(v: &mut Vec<i64> where len >= 1) -> Unit ! {alloc, panic} =
    quote fn(v: &mut Vec<i64>) -> Unit ! {alloc, panic} { write_value(v) };
fn main() -> i64 ! {alloc, panic} {
    let mut values: Vec<i64> = [1];
    update(&mut values);
    values[0]
}
"#;
    let program = checked(source).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);
    let shrinks = source.replace("v.push(99);", "v.clear();");
    assert!(checked(&shrinks).unwrap_err().contains("preserves the vector length"));
}

#[test]
fn staged_declarations_keep_call_site_proof_and_shared_length_contracts() {
    let source = r#"
#[staged]
fn positive(x: i64, erased evidence: { 0 < x }) -> i64 ! {} =
    quote fn(x: i64) -> i64 ! {} { x };
#[staged]
fn head(v: &Vec<i64> where len >= 1) -> i64 ! {panic} =
    quote fn(v: &Vec<i64>) -> i64 ! {panic} { v[0] };
fn main() -> i64 ! {alloc, panic} {
    let v: Vec<i64> = [42];
    positive(1, _) + head(&v) - 1
}
"#;
    let program = checked(source).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);
    let error = checked(&source.replace("positive(1, _)", "positive(0, _)")).unwrap_err();
    assert!(error.contains("cannot prove"), "{error}");
    let shorter = source.replace("[42]", "Vec.with_capacity(1)");
    let program = checked(&shorter).unwrap();
    assert!(program.evaluate(&mut Vec::new()).is_err());
}

#[test]
fn each_generic_staged_target_gets_its_own_initializer() {
    let program = checked(r#"
fn identity<T: Type>() -> Code<fn(T) -> T ! {}> ! {alloc, panic} {
    quote fn(x: T) -> T ! {} { x }
}

#[staged] fn first<T: Type>(x: T) -> T ! {} = identity::<T>();
fn select<N: Nat>() -> Code<fn([i64; N]) -> i64 ! {panic}> ! {alloc, panic} {
    let offset = first::<i64>(0);
    quote fn(xs: [i64; N]) -> i64 ! {panic} { xs[0] + lift(offset) }
}
#[staged] fn second<N: Nat>(xs: [i64; N]) -> i64 ! {panic} = select::<N>();
fn main() -> i64 ! {panic} {
    if first::<Bool>(true) { second::<1>([20]) + second::<2>([22, 99]) } else { 0 }
}
"#).unwrap();
    assert_eq!(program.evaluate(&mut Vec::new()).unwrap(), 42);
    assert_native_result(&program, 42);
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn staged_exports_link_as_ordinary_native_functions() {
    let program = checked(r#"
#[staged] export "staged_value" fn staged_value(x: i64) -> i64 ! {} =
    quote fn(x: i64) -> i64 ! {} { x ^ 3 };
"#).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let caller = scratch.path().join("caller.c");
    std::fs::write(&caller, r#"
#include <stdint.h>
extern int64_t staged_value(int64_t x);
int main(void) { return staged_value(41) != 42; }
"#).unwrap();
    for backend in [kush::native::Backend::Cranelift, kush::native::Backend::Llvm] {
        let library = scratch.path().join(format!("libstaged-{backend:?}.a"));
        let executable = scratch.path().join(format!("caller-{backend:?}"));
        kush::native::build_library(
            &program,
            &library,
            kush::native::CodegenOptions { backend, ..Default::default() },
        ).unwrap();
        let link = std::process::Command::new("cc")
            .arg(&caller)
            .arg(&library)
            .arg("-lm")
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(link.status.success(), "{link:?}");
        assert!(std::process::Command::new(executable).status().unwrap().success());
    }
}
