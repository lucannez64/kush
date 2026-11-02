use kush::{
    parse,
    resolve::{BindingKind, resolve},
};

fn valid(source: &str) -> kush::resolve::Resolution {
    resolve(&parse(source).unwrap()).unwrap()
}
fn invalid(source: &str, expected: &str) {
    let error = resolve(&parse(source).unwrap()).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

#[test]
fn forward_references_and_self_module_qualification() {
    let result = valid(
        "module proof.demo; fn first(n: Nat) -> Nat ! {} { proof.demo.second(n) } fn second(n: Nat) -> Nat ! {} { n }",
    );
    let first = result
        .bindings
        .iter()
        .position(|b| b.name == "first")
        .unwrap();
    let second = result
        .bindings
        .iter()
        .position(|b| b.name == "second")
        .unwrap();
    assert!(result.dependencies[&first].contains(&second));
    assert!(result.references.iter().any(|r| r.binding == second));
}
#[test]
fn initializer_uses_old_binding_then_new_binding_shadows_it() {
    let source = "fn f(x: Nat) -> Nat ! {} { let x = x; x }";
    let result = valid(source);
    let parameter = result
        .bindings
        .iter()
        .position(|b| b.name == "x" && b.kind == BindingKind::Parameter)
        .unwrap();
    let local = result
        .bindings
        .iter()
        .position(|b| b.name == "x" && b.kind == BindingKind::Local)
        .unwrap();
    let x_refs = result
        .references
        .iter()
        .filter(|r| result.bindings[r.binding].name == "x")
        .collect::<Vec<_>>();
    assert_eq!(x_refs[0].binding, parameter);
    assert_eq!(x_refs[1].binding, local);
    assert_ne!(parameter, local);
    invalid("fn f() -> Nat ! {} { let x = x; x }", "unknown name 'x'");
}
#[test]
fn types_can_reference_preceding_value_binders() {
    valid("fn f<T: Type>(x: T, p: Eq<T, x, x>) -> Eq<T, x, x> ! {} { p }");
    invalid("fn f(x: T) -> Nat ! {} { 0 }", "unknown name 'T'");
    invalid(
        "fn f<T: U, U: Type>() -> Nat ! {} { 0 }",
        "unknown name 'U'",
    );
    invalid(
        "fn f(x: Eq<Nat, y, y>, y: Nat) -> Nat ! {} { y }",
        "unknown name 'y'",
    );
}
#[test]
fn qualified_constructors_and_unique_short_names() {
    valid("enum E { A(Nat), B } fn f(x: E) -> Nat ! {} { match x { E.A(n) => n, B => 0 } }");
    invalid(
        "enum E { A } enum F { A } fn f(x: E) -> Nat ! {} { match x { A => 0 } }",
        "ambiguous constructor",
    );
    valid("enum E { A } enum F { A } fn f(x: E) -> Nat ! {} { match x { E.A => 0 } }");
    invalid(
        "enum E { A } fn f() -> E ! {} { E.Missing }",
        "unknown qualified name",
    );
    invalid(
        "fn f() -> Nat ! {} { Nat.missing }",
        "unknown qualified name",
    );
}
#[test]
fn fields_on_local_values_wait_for_type_checking() {
    let r = valid("struct R { value: Nat } fn f(x: R) -> Nat ! {} { x.missing }");
    assert!(
        r.references
            .iter()
            .any(|reference| r.bindings[reference.binding].name == "x")
    );
}
#[test]
fn duplicate_declarations_binders_and_fields() {
    for (source, expected) in [
        ("type A = Nat; type A = Nat;", "duplicate"),
        ("type Nat = Type;", "reserved"),
        ("fn f(x: Nat, x: Nat) -> Nat ! {} { x }", "duplicate binder"),
        (
            "fn f<T: Type, T: Type>() -> Nat ! {} { 0 }",
            "duplicate binder",
        ),
        ("struct R { x: Nat, x: Nat }", "duplicate field"),
        ("enum E { A, A }", "duplicate"),
        ("enum E { A { x: Nat, x: Nat } }", "duplicate field"),
        (
            "fn f() -> Nat ! {} { let (x, x) = (0, 0); x }",
            "duplicate pattern binding",
        ),
    ] {
        invalid(source, expected);
    }
}
#[test]
fn imports_headers_and_unknown_names_are_diagnosed() {
    invalid("use external.lib;", "imports need a loaded program");
    invalid(
        "type A = Nat; module late;",
        "module header must occur first",
    );
    invalid("module a; module b;", "module header must occur first");
    invalid("pub module a;", "module header must occur first");
    invalid("fn f() -> Missing ! {} { 0 }", "unknown name 'Missing'");
    invalid("fn f() -> Nat ! {missing} { 0 }", "unknown name 'missing'");
    invalid("fn f() -> Nat ! {} { not_here }", "unknown name 'not_here'");
}
#[test]
fn pattern_bindings_are_branch_local_and_alternatives_agree() {
    valid(
        "enum E { A(Nat), B(Nat) } fn f(x: E) -> Nat ! {} { match x { E.A(n) | E.B(n) if n > 0 => n, _ => 0 } }",
    );
    invalid(
        "enum E { A(Nat), B(Nat) } fn f(x: E) -> Nat ! {} { match x { E.A(a) | E.B(b) => a } }",
        "same names",
    );
    invalid(
        "enum E { A(Nat) } fn f(x: E) -> Nat ! {} { match x { E.A(n) => n, _ => n } }",
        "unknown name 'n'",
    );
    invalid(
        "fn f(x: Nat) -> Nat ! {} { { let hidden = x; hidden }; hidden }",
        "unknown name 'hidden'",
    );
    invalid(
        "fn f(x: Nat) -> Nat ! {} { if true { let hidden = x; hidden } else { hidden } }",
        "unknown name 'hidden'",
    );
}
#[test]
fn local_shadowing_does_not_resolve_as_a_global_constructor() {
    let result = valid("enum E { A } fn f(E: Nat) -> Nat ! {} { E.field }");
    let parameter = result
        .bindings
        .iter()
        .position(|b| b.name == "E" && b.kind == BindingKind::Parameter)
        .unwrap();
    assert!(result.references.iter().any(|r| r.binding == parameter));
}
