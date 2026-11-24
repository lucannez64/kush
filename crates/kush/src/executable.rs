//! Checked executable value subset: monomorphic functions, generic inline enums,
//! and normalized heterogeneous union/intersection value types. Logical proof terms never
//! enter this IR; only this module can construct a checked executable.
pub use crate::eval::MemoryStats;
use crate::{
    Diagnostic, Span, ast,
    coverage::Coverage,
    grades::{self, Grade},
    kernel::{Scalar, Term},
    lexer::Kind,
    resolve::{self, BindingId, BindingKind, Resolution},
    runtime_types::{Enum, FunctionType, ResultShape, Types},
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) mod anf;
mod array_expressions;
mod assignment_expressions;
mod ast_queries;
mod binary_expressions;
mod blocks;
mod builtin_calls;
mod call_expressions;
mod calls_records;
mod coercion;
mod collections;
mod concurrency;
mod conditionals;
mod construction_staging;
mod expressions;
mod fusion;
mod handlers;
mod impl_patterns;
mod index_expressions;
mod instances;
mod ir;
mod lambdas;
mod local_lifetimes;
mod memory_calls;
mod methods;
mod performs;
mod places;
mod postconditions;
mod program;
mod proof_scalars;
mod recursive_lifetimes;
mod signature_validation;
mod slices;
mod trait_collection;
mod unification;

pub(crate) use ast_queries::*;
use fusion::*;
use impl_patterns::*;
pub use ir::*;
pub(crate) use local_lifetimes::*;
pub(crate) use signature_validation::*;
use trait_collection::*;
type Result<T> = std::result::Result<T, Diagnostic>;
/// FND-ROWS-PANIC: `panic` is not an effect; any function may panic. The
/// constant is the empty set, so no row contains it and `require(PANIC)`
/// always holds. Code generation must not read "may not panic" from a row:
/// native tests the abort word after every call in unwinding programs.
/// (Bit 0 stays unused; declared operations start at `1 << 4`.)
pub(crate) const PANIC: u16 = 0;
/// CAP-CAPTURING-LEXICAL: operation ids above this name private frames of
/// capability-only capturing handlers; no declared operation reaches them.
pub(crate) const PRIVATE_OPERATION_BASE: usize = 1 << 20;
pub(crate) const IO: u16 = 2;
pub(crate) const ALLOC: u16 = 4;
pub(crate) const SUSPEND: u16 = 8;
pub(crate) const EFFECT_BITS: u16 = PANIC | IO | ALLOC | SUSPEND;
pub(crate) const MAX_EFFECT_ROW_VARIABLES: usize = 16;
/// Runtime host stubs whose answer is fixed for the process, so std may
/// declare them without the `io` effect (SIMD-CPU). Only std can import a
/// `kush_sys_*` symbol, so no program can add to this list.
const PURE_HOST_SYMBOLS: &[&str] = &["kush_sys_cpu_features"];
/// Allow only the stable C ABI bridge subset. Pointers, Rust enums with
/// payloads, owned text/buffers, and arbitrary aggregates are rejected here
/// rather than guessed at the backend.
fn foreign_value_supported(types: &Types<'_>, ty: Type) -> bool {
    match ty {
        Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) | Type::Str => true,
        Type::Enum(id) => types.enums[id].foreign.is_some(),
        Type::Ref(pointer) => match types.pointees[pointer] {
            Type::Enum(id) => types.enums[id].foreign.is_some(),
            Type::Bytes | Type::String => true,
            _ => false,
        },
        _ => false,
    }
}
fn foreign_result_supported(types: &Types<'_>, ty: Type, error: bool) -> bool {
    if error {
        return ty == Type::I64;
    }
    match ty {
        Type::Unit | Type::Bytes | Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) => true,
        Type::Enum(id) => types.enums[id].foreign.is_some(),
        _ => false,
    }
}
/// Validate the checked signature of a foreign declaration. The caller already
/// required a concrete, monomorphic, non-erased signature with `io` in its row.
///
/// `std_sys` marks a std-only `kush_sys_*` runtime stub, which may also take
/// an owned `Bytes` buffer (FOREIGN-BYTES-FILL): the stub appends into its
/// spare capacity and hands it back through a `Result<Bytes, i64>` out slot,
/// or frees it on failure, like the `FS.read_at` builtin.
#[allow(clippy::too_many_arguments)]
fn validate_foreign_function(
    types: &Types<'_>,
    std_sys: bool,
    parameters: &[Type],
    result: Type,
    result_shape: Option<ResultShape>,
    parameter_grades: &[Option<Grade>],
    result_grade: Option<Grade>,
    span: Span,
) -> Result<()> {
    if parameter_grades.iter().any(Option::is_some) || result_grade.is_some() {
        return Err(Diagnostic::new(
            span,
            "foreign functions cannot carry usage grades; use the owning result type for exactly-once transfer, or Result<T, i64> for checked failure",
        ));
    }
    for ty in parameters {
        if !foreign_value_supported(types, *ty) && !(std_sys && *ty == Type::Bytes) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "foreign parameter type {} is not part of the stable C bridge ABI; supported inputs are fixed-width integers, f32/f64, Bool, &str, &Bytes, &String, and declared foreign resources",
                    types.name(*ty)
                ),
            ));
        }
    }
    if let Some(shape) = result_shape {
        if !foreign_result_supported(types, shape.ok, false) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "foreign Result Ok type {} is not bridgeable; supported results are Unit, Bytes, fixed-width integers, f32/f64, Bool, and declared foreign resources",
                    types.name(shape.ok)
                ),
            ));
        }
        if !foreign_result_supported(types, shape.error, true) {
            return Err(Diagnostic::new(
                span,
                "a foreign Result must use i64 as its error type; the bridge returns a non-zero C status as Err(status)",
            ));
        }
    } else if !foreign_result_supported(types, result, false) {
        return Err(Diagnostic::new(
            span,
            format!(
                "foreign result type {} is not part of the stable C bridge ABI; return Unit, Bytes, a fixed-width integer, f32/f64, Bool, a declared foreign resource, or Result<T, i64>",
                types.name(result)
            ),
        ));
    }
    Ok(())
}
/// Split `T @[grade]` into the type and its grade expression.
pub(crate) fn split_grade(ty: &ast::Type) -> (&ast::Type, Option<&ast::Type>) {
    grades::split(ty)
}
/// Whether a name is a bare C symbol. Foreign declarations and resource release
/// hooks are passed to Cranelift and `cc` as arguments, never through a shell,
/// but restricting the spelling keeps diagnostics and generated C/Rust shims
/// predictable.
pub(crate) fn valid_c_symbol(name: &str) -> bool {
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && characters.all(|character| character == '_' || character.is_ascii_alphanumeric())
}
/// Expand an outer chain of transparent executable type aliases so a result
/// contract can be written through an alias:
///
/// ```kush
/// type Handle<T> = Box<T> @[1];
/// fn make() -> Handle<i64> ! { ... } { Box.new(0) }
/// ```
///
/// Only the outermost alias chain is expanded here; nested aliases still go
/// through normal checked type lowering. Grade/const/type arguments are
/// substituted structurally, while lifetime arguments stay erased. Grade
/// parameters are permitted only here, in a result-contract position: the
/// substituted grade is evaluated by [`result_contract`] afterwards, or
/// inferred from the expected arrow contract for a generic function value.
fn expand_result_aliases(
    resolution: &Resolution,
    types: &Types<'_>,
    ty: &ast::Type,
) -> Result<ast::Type> {
    let mut current = ty.clone();
    let mut active = BTreeSet::new();
    for _ in 0..64 {
        let ast::TypeKind::Named { arguments, .. } = &current.kind else {
            return Ok(current);
        };
        let Some(id) = resolution.reference(current.span) else {
            return Ok(current);
        };
        if resolution.bindings[id].kind != BindingKind::Alias {
            return Ok(current);
        }
        let Some((generics, rhs)) = types.alias_definition(id) else {
            return Ok(current);
        };
        let lifetime_arguments = arguments
            .iter()
            .filter(|argument| matches!(argument.kind, ast::TypeKind::Lifetime(_)))
            .count();
        if let Some(expected) = types.alias_lifetime_count(id)
            && lifetime_arguments != expected
        {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "type alias '{}' expects {expected} lifetime argument(s), found {lifetime_arguments}",
                    resolution.bindings[id].name
                ),
            ));
        }
        let runtime_arguments = arguments
            .iter()
            .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
            .collect::<Vec<_>>();
        if runtime_arguments.len() != generics.len() {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "type alias '{}' expects {} runtime argument(s), found {}",
                    resolution.bindings[id].name,
                    generics.len(),
                    runtime_arguments.len()
                ),
            ));
        }
        if !active.insert(id) {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "cyclic executable type alias '{}' is not allowed",
                    resolution.bindings[id].name
                ),
            ));
        }
        let mut map = BTreeMap::new();
        for (generic, argument) in generics.iter().zip(runtime_arguments) {
            // Grade arguments are substituted like any other structural
            // argument here. `expand_alias` still rejects them in every
            // non-result alias position, so a grade cannot enter a parameter
            // or stored type through this expansion.
            map.insert(resolution.binder(generic.span).unwrap(), argument);
        }
        current = substitute_alias_type(resolution, rhs, &map);
    }
    Err(Diagnostic::new(
        ty.span,
        "executable type alias expansion exceeds the 64-level budget",
    ))
}

/// Whether `ty` mentions the given binding anywhere, including nested grade
/// expressions and alias arguments.
pub(crate) fn type_mentions_binding(
    resolution: &Resolution,
    ty: &ast::Type,
    binder: BindingId,
) -> bool {
    use ast::TypeKind as K;
    match &ty.kind {
        K::Named { arguments, .. } => {
            resolution.reference(ty.span) == Some(binder)
                || arguments
                    .iter()
                    .any(|argument| type_mentions_binding(resolution, argument, binder))
        }
        K::Tuple(items) => items
            .iter()
            .any(|item| type_mentions_binding(resolution, item, binder)),
        K::Structural { fields, .. } => fields
            .iter()
            .any(|field| type_mentions_binding(resolution, &field.ty, binder)),
        K::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_mentions_binding(resolution, inner, binder))
        }
        K::Slice(inner) => type_mentions_binding(resolution, inner, binder),
        K::Array(element, length) => {
            type_mentions_binding(resolution, element, binder)
                || type_mentions_binding(resolution, length, binder)
        }
        K::Borrow { inner, .. } => type_mentions_binding(resolution, inner, binder),
        K::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_binding(resolution, &parameter.ty, binder))
                || type_mentions_binding(resolution, result, binder)
                || effects
                    .iter()
                    .any(|effect| type_mentions_binding(resolution, effect, binder))
        }
        K::Binary { left, right, .. } => {
            type_mentions_binding(resolution, left, binder)
                || type_mentions_binding(resolution, right, binder)
        }
        K::Graded { inner, grade } => {
            type_mentions_binding(resolution, inner, binder)
                || type_mentions_binding(resolution, grade, binder)
        }
        K::Capability { effects, .. } => effects
            .iter()
            .any(|effect| type_mentions_binding(resolution, effect, binder)),
        K::Integer(_) | K::Bool(_) | K::Lifetime(_) | K::SelfType | K::Infer | K::Predicate(_) => {
            false
        }
    }
}
/// The binder named by a bare grade expression, as in `@[G]`. Composite
/// expressions such as `@[G + 1]` and `@[G * 2]` are not inferable.
pub(crate) fn bare_grade_binder(resolution: &Resolution, grade: &ast::Type) -> Option<BindingId> {
    let ast::TypeKind::Named { arguments, .. } = &grade.kind else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    resolution.reference(grade.span)
}
/// Split a declared result type into the runtime result type and the evaluated
/// static result grade, expanding outer aliases first. Only `@[1]` on an owning
/// or intrinsically linear result is supported; other grades are rejected
/// explicitly instead of silently discarding the transfer obligation.
fn result_contract(
    resolution: &Resolution,
    types: &Types<'_>,
    grade_substitution: &BTreeMap<BindingId, Grade>,
    ty: &ast::Type,
) -> Result<(ast::Type, Option<Grade>)> {
    let expanded = expand_result_aliases(resolution, types, ty)?;
    let (inner, grade) = split_grade(&expanded);
    let grade = grade
        .map(|grade| grades::evaluate(resolution, grade_substitution, grade))
        .transpose()?;
    Ok((inner.clone(), grade))
}

/// Validate a static result-transfer contract.
///
/// Exactly `@[1]` is representable. On an owning or intrinsically linear
/// result it transfers an owning linear obligation. On a copyable result it
/// transfers a *must-use* obligation: the caller must observe the returned
/// value exactly once on every normal path. The two obligations are distinct
/// even though both use the same `@[1]` surface syntax; `result_grade` alone
/// never makes a copyable value move-owning.
fn validate_result_contract(
    grade: Option<Grade>,
    owning: bool,
    name: &str,
    span: Span,
) -> Result<()> {
    match grade {
        None => Ok(()),
        Some(grade) if grade.is_one() => Ok(()),
        Some(grade) if grade.is_zero() && !owning => Ok(()),
        Some(grade) if grade.is_zero() => Err(Diagnostic::new(
            span,
            format!(
                "a result graded @[0] would silently discard the owning/linear value {name}; use an owning @[1] result contract, consume it inside the function, or return Unit"
            ),
        )),
        Some(grade) if grade.is_many() => Err(Diagnostic::new(
            span,
            "a result graded 'many' could duplicate one owning resource; result contracts currently support exactly @[1] or a copyable @[0]",
        )),
        Some(grade) => Err(Diagnostic::new(
            span,
            format!(
                "a result graded @[{grade}] could duplicate one owning resource; result contracts currently support exactly @[1] or a copyable @[0]"
            ),
        )),
    }
}
/// The runtime type of a direct call expression. A `@[0]` result has no
/// observable payload, so callers see `Unit`.
fn call_result_type(signature: &Signature) -> Type {
    if crate::runtime_types::grade_erases(signature.result_grade) {
        Type::Unit
    } else {
        signature.result
    }
}
/// Outer lifetime annotation of a borrow type, if any.
/// Reflexive-transitive closure of declared or inferred outlives edges.
fn close_lifetime_bounds(bounds: BTreeSet<(String, String)>) -> BTreeSet<(String, String)> {
    crate::lifetimes::LifetimeGraph::new(&bounds)
        .solve()
        .closure
}
fn borrow_lifetime(ty: &ast::Type) -> Option<String> {
    match &ty.kind {
        ast::TypeKind::Borrow { lifetime, .. } => lifetime.clone(),
        _ => None,
    }
}
/// Every lifetime name mentioned by a type, including nested borrows.
/// The first lifetime nested in a parameter's written type. A container such
/// as `&mut Vec<&'a T>` has an elided outer borrow lifetime but a concrete
/// element lifetime `'a`; the requirement mapper must use the element one.
fn nested_borrow_lifetime(ty: &ast::Type) -> Option<String> {
    match &ty.kind {
        ast::TypeKind::Borrow {
            lifetime, inner, ..
        } => lifetime.clone().or_else(|| nested_borrow_lifetime(inner)),
        ast::TypeKind::Lifetime(name) => Some(name.clone()),
        ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Slice(inner)
        | ast::TypeKind::Array(inner, _) => nested_borrow_lifetime(inner),
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            arguments.iter().find_map(nested_borrow_lifetime)
        }
        _ => None,
    }
}
fn type_lifetimes(ty: &ast::Type, out: &mut BTreeSet<String>) {
    match &ty.kind {
        ast::TypeKind::Lifetime(name) => {
            out.insert(name.clone());
        }
        ast::TypeKind::Borrow {
            lifetime, inner, ..
        } => {
            if let Some(lifetime) = lifetime {
                out.insert(lifetime.clone());
            }
            type_lifetimes(inner, out);
        }
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_lifetimes(inner, out);
        }
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            for argument in arguments {
                type_lifetimes(argument, out);
            }
        }
        ast::TypeKind::Structural { fields, .. } => {
            for field in fields {
                type_lifetimes(&field.ty, out);
            }
        }
        ast::TypeKind::Array(inner, length) => {
            type_lifetimes(inner, out);
            type_lifetimes(length, out);
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_lifetimes(left, out);
            type_lifetimes(right, out);
        }
        ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            ..
        } => {
            // Lifetimes bound by the arrow itself are not free in the type.
            let mut inner = BTreeSet::new();
            for parameter in parameters {
                type_lifetimes(&parameter.ty, &mut inner);
            }
            type_lifetimes(result, &mut inner);
            for effect in effects {
                type_lifetimes(effect, &mut inner);
            }
            for lifetime in lifetimes {
                inner.remove(&lifetime.name);
            }
            out.extend(inner);
        }
        _ => {}
    }
}
/// Collect explicit `return value` expressions while ignoring nested lambdas,
/// whose returns belong to the callable rather than this function body.
fn collect_body_returns<'a>(expr: &'a ast::Expr, out: &mut Vec<&'a ast::Expr>) {
    match &expr.kind {
        ast::ExprKind::Return(Some(value)) => {
            out.push(value);
            collect_body_returns(value, out);
        }
        ast::ExprKind::Lambda(_) | ast::ExprKind::Return(None) | ast::ExprKind::Continue => {}
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_) => {}
        ast::ExprKind::Tuple(items) | ast::ExprKind::Array(items) => {
            for item in items {
                collect_body_returns(item, out);
            }
        }
        ast::ExprKind::StructuralLiteral(fields) => {
            for (_, value) in fields {
                collect_body_returns(value, out);
            }
        }
        ast::ExprKind::Block(block) => collect_block_returns(block, out),
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Field { value: operand, .. }
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. }
        | ast::ExprKind::Specialize {
            callee: operand, ..
        } => {
            collect_body_returns(operand, out);
        }
        ast::ExprKind::Slice { value, start, end } => {
            collect_body_returns(value, out);
            if let Some(start) = start {
                collect_body_returns(start, out);
            }
            if let Some(end) = end {
                collect_body_returns(end, out);
            }
        }
        ast::ExprKind::Binary { left, right, .. } => {
            collect_body_returns(left, out);
            collect_body_returns(right, out);
        }
        ast::ExprKind::Index { value, index } => {
            collect_body_returns(value, out);
            collect_body_returns(index, out);
        }
        ast::ExprKind::Call { callee, arguments } => {
            collect_body_returns(callee, out);
            for argument in arguments {
                collect_body_returns(argument, out);
            }
        }
        ast::ExprKind::Handle { handler, body, .. } => {
            collect_body_returns(handler, out);
            collect_block_returns(body, out);
        }
        ast::ExprKind::Perform { value, .. } => collect_body_returns(value, out),
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            collect_body_returns(condition, out);
            collect_block_returns(then, out);
            if let Some(otherwise) = otherwise {
                collect_body_returns(otherwise, out);
            }
        }
        ast::ExprKind::Match { value, arms } => {
            collect_body_returns(value, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_body_returns(guard, out);
                }
                collect_body_returns(&arm.body, out);
            }
        }
        ast::ExprKind::Record { ty, fields, base } => {
            collect_body_returns(ty, out);
            for (_, field) in fields {
                collect_body_returns(field, out);
            }
            if let Some(base) = base {
                collect_body_returns(base, out);
            }
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
            collect_body_returns(condition, out);
            collect_block_returns(body, out);
        }
        ast::ExprKind::Loop(body) => collect_block_returns(body, out),
        ast::ExprKind::Break(value) => {
            if let Some(value) = value {
                collect_body_returns(value, out);
            }
        }
    }
}
fn collect_block_returns<'a>(block: &'a ast::Block, out: &mut Vec<&'a ast::Expr>) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => collect_body_returns(value, out),
            ast::Statement::Expr(expr) => collect_body_returns(expr, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_body_returns(tail, out);
    }
}
/// A capability type `cap Op` is second-class: it is accepted only as the
/// whole type of a named function parameter. Anywhere else it is rejected.
fn reject_capability_type(ty: &ast::Type) -> Result<()> {
    let mut found = None;
    fn walk(ty: &ast::Type, found: &mut Option<Span>) {
        if found.is_some() {
            return;
        }
        match &ty.kind {
            ast::TypeKind::Capability { .. } => *found = Some(ty.span),
            ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
                arguments.iter().for_each(|argument| walk(argument, found));
            }
            ast::TypeKind::Slice(inner)
            | ast::TypeKind::Borrow { inner, .. }
            | ast::TypeKind::Graded { inner, .. } => walk(inner, found),
            ast::TypeKind::Array(inner, length) => {
                walk(inner, found);
                walk(length, found);
            }
            ast::TypeKind::Structural { fields, .. } => {
                fields.iter().for_each(|field| walk(&field.ty, found));
            }
            ast::TypeKind::Binary { left, right, .. } => {
                walk(left, found);
                walk(right, found);
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .for_each(|parameter| walk(&parameter.ty, found));
                walk(result, found);
            }
            ast::TypeKind::Dyn(bounds) => {
                crate::ast::dyn_types(bounds).for_each(|inner| walk(inner, found));
            }
            _ => {}
        }
    }
    walk(ty, &mut found);
    match found {
        Some(span) => Err(Diagnostic::new(
            span,
            "a capability type 'cap Op' is second-class: it is only allowed as the whole type of a named function parameter, never stored, returned, nested or used in a function value type",
        )),
        None => Ok(()),
    }
}
/// Reject capability types in declarations that store or name values.
/// FND-ROWS-INFER: only private free functions infer their row. A method's
/// row is part of its trait contract or of its type's interface.
fn reject_omitted_method_rows(module: &ast::Module) -> Result<()> {
    for declaration in &module.items {
        let (ast::ItemKind::Trait { methods, .. } | ast::ItemKind::Impl { methods, .. }) =
            &declaration.item.kind
        else {
            continue;
        };
        if let Some(method) = methods.iter().find(|method| method.function.row_omitted()) {
            return Err(Diagnostic::new(
                method.span,
                "a method declares its effect row; add '! {..}' after the result type",
            ));
        }
    }
    Ok(())
}
fn reject_stored_capabilities(module: &ast::Module) -> Result<()> {
    for declaration in &module.items {
        match &declaration.item.kind {
            ast::ItemKind::Struct { fields, .. } => {
                for field in fields {
                    reject_capability_type(&field.ty)?;
                }
            }
            ast::ItemKind::Enum { variants, .. } => {
                for variant in variants {
                    match &variant.payload {
                        ast::Payload::Unit => {}
                        ast::Payload::Tuple(types) => {
                            for ty in types {
                                reject_capability_type(ty)?;
                            }
                        }
                        ast::Payload::Fields(fields) | ast::Payload::Record(fields) => {
                            for field in fields {
                                reject_capability_type(&field.ty)?;
                            }
                        }
                    }
                }
            }
            ast::ItemKind::Alias { ty, .. } => reject_capability_type(ty)?,
            ast::ItemKind::Effect {
                parameter, result, ..
            } => {
                reject_capability_type(parameter)?;
                reject_capability_type(result)?;
            }
            ast::ItemKind::Function(function) => {
                reject_capability_type(&function.result)?;
                for effect in &function.effects {
                    reject_capability_type(effect)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}
/// Whether a lambda omits a parameter, result or effect annotation.
fn lambda_has_holes(lambda: &ast::Lambda) -> bool {
    matches!(lambda.result.kind, ast::TypeKind::Infer)
        || matches!(lambda.effects.as_slice(), [only] if matches!(only.kind, ast::TypeKind::Infer))
        || lambda
            .parameters
            .iter()
            .any(|parameter| matches!(parameter.ty.kind, ast::TypeKind::Infer))
}
/// Whether some expression of `block` (not inside a nested lambda) satisfies
/// `predicate`. Bounded by the AST size.
fn block_any(block: &ast::Block, predicate: &dyn Fn(&ast::ExprKind) -> bool) -> bool {
    let mut stack = Vec::new();
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => stack.push(value),
            ast::Statement::Expr(expr) => stack.push(expr),
        }
    }
    stack.extend(block.tail.as_deref());
    while let Some(expr) = stack.pop() {
        if predicate(&expr.kind) {
            return true;
        }
        if !matches!(expr.kind, ast::ExprKind::Lambda(_)) {
            ast_children(expr, &mut |child| stack.push(child));
        }
    }
    false
}
fn placeholder_expr(span: Span) -> Box<Expr> {
    Box::new(Expr {
        kind: ExprKind::Constant(0),
        ty: Type::Unit,
        span,
        resource: None,
    })
}

fn is_grade_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    generic.bound.as_ref().is_some_and(|bound| {
        resolution.reference(bound.span).is_some_and(|id| {
            resolution.bindings[id].kind == BindingKind::Builtin
                && resolution.bindings[id].name == "Grade"
        })
    })
}
/// Whether a generic binder is a compile-time natural `<N: Nat>`.
fn is_const_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    crate::runtime_types::is_const_generic(resolution, generic)
}
/// Render a concrete effect set for diagnostics, in canonical order with
/// declared operations after the built-in vocabulary.
fn effect_names(resolution: &Resolution, bits: u16) -> String {
    crate::runtime_types::effect_name_list(resolution, bits).join(", ")
}
/// An executable `fn` declaration before specialization.
#[derive(Clone, Copy)]
struct Declared<'a> {
    ast: &'a ast::Function,
    span: Span,
    /// Concrete `Self` target for an impl method. Ordinary functions are `None`
    /// and reject any stray `Self` during type lowering.
    self_ty: Option<Type>,
    /// Index into `Functions::default_specializations` for a trait default
    /// method materialized for one impl. The entry supplies the trait's
    /// concrete type/Nat/Grade/effect arguments, which are substituted into the
    /// default body's signature exactly like `Self`.
    default_specialization: Option<usize>,
    /// Associated values of the impl that owns this method. `Self::Item` and
    /// `Self::CONST` normalize through this entry.
    impl_associated: Option<usize>,
    /// Index into `Functions::impl_headers` when the method belongs to a
    /// generic impl. Its receiver type and impl generics are supplied per
    /// instance by `MethodDefinition::impl_arguments`.
    impl_template: Option<usize>,
}
/// One method declared by a trait: its declaration span and signature, with an
/// optional default body borrowed from the module AST.
#[derive(Clone, Copy)]
struct TraitMethod<'a> {
    span: Span,
    function: &'a ast::Function,
}
/// One associated item declared by a trait.
#[derive(Debug, Clone)]
enum TraitAssociated {
    /// An associated type declaration, optionally with a default type that an
    /// impl inherits when it omits `type Name = ...`.
    Type {
        /// A default type, substituted with the impl's trait arguments and
        /// materialized per impl. It may mention the trait's parameters but
        /// not `Self`; `Self::Other` is permitted and checked for cycles.
        default: Option<ast::Type>,
    },
    Const {
        ty: ast::Type,
        /// A default value inherited by impls that omit the constant.
        default: Option<ast::Expr>,
    },
}
/// One declared trait: its generic parameters, associated items, and method
/// declarations.
#[derive(Clone)]
struct TraitDefinition<'a> {
    generics: Vec<ast::Generic>,
    associated: BTreeMap<String, TraitAssociated>,
    /// Associated item names in declaration order. Constant defaults may
    /// reference earlier constants, so inheritance evaluates in this order.
    associated_order: Vec<String>,
    methods: BTreeMap<String, TraitMethod<'a>>,
}
/// A checked compile-time associated constant. Scalar values carry their bit
/// representation; tuples and inline arrays of constants carry recursively
/// checked element values. The value is substituted wherever the constant is
/// named, so it has no runtime storage, address, or accessor function.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstValue {
    ty: Type,
    /// Scalar bit representation. Aggregate values use `elements`.
    bits: i64,
    /// Element values for a tuple or inline-array constant; empty for scalars.
    elements: Vec<ConstValue>,
}
impl ConstValue {
    fn scalar(ty: Type, bits: i64) -> Self {
        Self {
            ty,
            bits,
            elements: Vec::new(),
        }
    }
    fn aggregate(ty: Type, elements: Vec<ConstValue>) -> Self {
        Self {
            ty,
            bits: 0,
            elements,
        }
    }
}
/// Associated values supplied by one impl, from which `Self::Item` projections
/// and `Self::CONST` references are normalized for that impl's methods and
/// inherited defaults.
#[derive(Debug, Clone, Default)]
struct ImplAssociated {
    types: BTreeMap<String, ast::Type>,
    consts: BTreeMap<String, ConstValue>,
}
/// Canonical, checked arguments that select one trait specialization. Each
/// vector is in declaration order among parameters of that category, exactly
/// like a function instance key.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TraitArguments {
    pub(crate) types: Vec<Type>,
    pub(crate) consts: Vec<usize>,
    pub(crate) grades: Vec<Grade>,
    pub(crate) effects: Vec<u16>,
}
/// Concrete arguments for the generic parameters of one impl header. Stored by
/// index so `MethodDefinition` stays `Copy`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct ImplArguments {
    types: Vec<Type>,
    consts: Vec<usize>,
    grades: Vec<Grade>,
    effects: Vec<u16>,
}
/// One generic or blanket impl header. The self type and trait arguments are
/// patterns over `generics`; concrete receivers are matched against them by
/// first-order unification, and the unique most-specific matching impl wins.
#[derive(Debug, Clone)]
struct ImplHeader {
    /// `None` for an inherent `impl<T> Type<T>` block.
    trait_id: Option<BindingId>,
    generics: Vec<ast::Generic>,
    self_ty: ast::Type,
    /// Raw trait argument patterns, aligned with the trait's generic
    /// parameters. Empty for inherent impls.
    trait_arguments: Vec<ast::Type>,
    associated: ImplAssociated,
    methods: BTreeMap<String, MethodDefinition>,
    span: Span,
    /// Concrete lowered header for monomorphic impls, used by coherence and by
    /// exact lookup. `None` for generic headers.
    concrete: Option<(TraitArguments, Type)>,
}
/// One match of a generic impl header against a concrete obligation.
#[derive(Debug, Clone)]
struct ImplMatch {
    header: usize,
    arguments: ImplArguments,
}
/// One interned generic-impl instantiation.
#[derive(Debug, Clone)]
struct ImplInstantiation {
    header: usize,
    arguments: ImplArguments,
    self_type: Type,
    trait_arguments: TraitArguments,
}
/// The category of one generic binder. Function generics and trait parameters
/// use the same classification; only ordinary types are runtime values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GenericCategory {
    Type,
    Const,
    Grade,
    Effect,
}
fn generic_category(resolution: &Resolution, generic: &ast::Generic) -> GenericCategory {
    if is_grade_generic(resolution, generic) {
        GenericCategory::Grade
    } else if is_const_generic(resolution, generic) {
        GenericCategory::Const
    } else if crate::runtime_types::is_effect_generic(resolution, generic) {
        GenericCategory::Effect
    } else {
        GenericCategory::Type
    }
}
/// Whether a type can be the declared type of an associated constant. Scalar
/// machine values and finite tuples/inline arrays of such values have a
/// canonical compile-time representation.
fn const_scalar_type(types: &Types<'_>, ty: Type) -> bool {
    fn allowed(types: &Types<'_>, ty: Type, depth: usize) -> bool {
        if depth >= 8 {
            return false;
        }
        if matches!(ty, Type::I64 | Type::Int(_) | Type::Bool | Type::Char) {
            return true;
        }
        let Some(layout) = ty.layout() else {
            return false;
        };
        if let Some((element, _)) = types.enums[layout].array {
            return allowed(types, element, depth + 1);
        }
        types.enums[layout].tuple
            && types.enums[layout].variants[0]
                .fields
                .iter()
                .all(|field| allowed(types, *field, depth + 1))
    }
    allowed(types, ty, 0)
}
/// Evaluate a constant expression for an associated constant. The subset is
/// deliberately compile-time only: scalar literals, tuple/array literals of
/// constants, earlier associated constants of the same impl, checked integer
/// arithmetic, shifts, boolean operators, and integer comparisons. Calls,
/// effects, and runtime values are rejected, so an associated constant can
/// never hide work at a use site.
fn evaluate_associated_const(
    types: &Types<'_>,
    expr: &ast::Expr,
    expected: Type,
    consts: &BTreeMap<String, ConstValue>,
) -> Result<ConstValue> {
    match expected {
        Type::Bool => {
            let value = evaluate_const_bool(expr, consts, 0)?;
            Ok(ConstValue::scalar(Type::Bool, i64::from(value)))
        }
        Type::Char => match &expr.kind {
            ast::ExprKind::Char(ch) => {
                Ok(ConstValue::scalar(Type::Char, i64::from(u32::from(*ch))))
            }
            ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                const_reference(types, consts, name, Type::Char)
            }
            _ => Err(Diagnostic::new(
                expr.span,
                "a Char associated constant must be a character literal or another Char constant",
            )),
        },
        Type::I64 | Type::Int(_) => {
            let value = evaluate_const_int(expr, consts)?;
            let kind = expected.int_kind().expect("integer constant type");
            let bits = kind.encode(value).ok_or_else(|| {
                Diagnostic::new(
                    expr.span,
                    format!(
                        "associated constant value {value} is outside the range of {}",
                        kind.name()
                    ),
                )
            })?;
            Ok(ConstValue::scalar(expected, bits))
        }
        _ => {
            let Some(layout) = expected.layout() else {
                return Err(Diagnostic::new(
                    expr.span,
                    "associated constants must have a compile-time scalar, tuple, or inline-array type",
                ));
            };
            if let Some((element, length)) = types.enums[layout].array {
                let items = match &expr.kind {
                    ast::ExprKind::Array(items) => items.clone(),
                    ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                        return const_reference(types, consts, name, expected);
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "an array associated constant must be an array literal or an earlier constant of the same type",
                        ));
                    }
                };
                if items.len() != length {
                    return Err(Diagnostic::new(
                        expr.span,
                        format!(
                            "array associated constant has {} element(s), but its type needs {length}",
                            items.len()
                        ),
                    ));
                }
                let mut elements = Vec::with_capacity(items.len());
                for item in &items {
                    elements.push(evaluate_associated_const(types, item, element, consts)?);
                }
                return Ok(ConstValue::aggregate(expected, elements));
            }
            if types.enums[layout].tuple {
                let field_types = types.enums[layout].variants[0].fields.clone();
                let items = match &expr.kind {
                    ast::ExprKind::Tuple(items) => items.clone(),
                    ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                        return const_reference(types, consts, name, expected);
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "a tuple associated constant must be a tuple literal or an earlier constant of the same type",
                        ));
                    }
                };
                if items.len() != field_types.len() {
                    return Err(Diagnostic::new(
                        expr.span,
                        format!(
                            "tuple associated constant has {} element(s), but its type needs {}",
                            items.len(),
                            field_types.len()
                        ),
                    ));
                }
                let mut elements = Vec::with_capacity(items.len());
                for (item, field_ty) in items.iter().zip(field_types) {
                    elements.push(evaluate_associated_const(types, item, field_ty, consts)?);
                }
                return Ok(ConstValue::aggregate(expected, elements));
            }
            Err(Diagnostic::new(
                expr.span,
                "associated constants must have a compile-time scalar, tuple, or inline-array type",
            ))
        }
    }
}
/// Lower one checked compile-time constant to an ordinary checked expression.
/// Scalars are literals; tuples and arrays reconstruct their canonical layout
/// from recursively lowered elements.
fn const_value_expr(value: &ConstValue, span: Span) -> Result<Expr> {
    let kind = if let Some(layout) = value.ty.layout() {
        let fields = value
            .elements
            .iter()
            .map(|element| const_value_expr(element, span))
            .collect::<Result<Vec<_>>>()?;
        ExprKind::Construct {
            enum_id: layout,
            tag: 0,
            fields,
        }
    } else {
        ExprKind::Constant(value.bits)
    };
    Ok(Expr {
        kind,
        ty: value.ty,
        span,
        resource: None,
    })
}
fn const_reference(
    types: &Types<'_>,
    consts: &BTreeMap<String, ConstValue>,
    name: &str,
    expected: Type,
) -> Result<ConstValue> {
    let Some(value) = consts.get(name) else {
        return Err(Diagnostic::new(
            Span::default(),
            format!(
                "unknown associated constant '{name}'; constants may reference earlier constants of the same impl"
            ),
        ));
    };
    if value.ty != expected {
        return Err(Diagnostic::new(
            Span::default(),
            format!(
                "associated constant '{name}' has type {}, not {}",
                types.name(value.ty),
                types.name(expected)
            ),
        ));
    }
    Ok(value.clone())
}
fn evaluate_const_int(expr: &ast::Expr, consts: &BTreeMap<String, ConstValue>) -> Result<i128> {
    match &expr.kind {
        ast::ExprKind::Integer(text) => text
            .parse::<i128>()
            .map_err(|_| Diagnostic::new(expr.span, "integer literal is too large for a constant")),
        ast::ExprKind::Unary {
            op: crate::lexer::Kind::Minus,
            operand,
            ..
        } => Ok(-evaluate_const_int(operand, consts)?),
        ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
            let Some(value) = consts.get(name) else {
                return Err(Diagnostic::new(
                    expr.span,
                    format!(
                        "unknown associated constant '{name}'; constants may reference earlier constants of the same impl"
                    ),
                ));
            };
            if !value.elements.is_empty() {
                return Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is an aggregate, not an integer",
                ));
            }
            match value.ty.int_kind() {
                Some(kind) => Ok(kind.decode(value.bits)),
                None => Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is not an integer",
                )),
            }
        }
        ast::ExprKind::Binary { op, left, right } => {
            let left = evaluate_const_int(left, consts)?;
            let right = evaluate_const_int(right, consts)?;
            use crate::lexer::Kind;
            let value = match op {
                Kind::Plus => left.checked_add(right),
                Kind::Minus => left.checked_sub(right),
                Kind::Star => left.checked_mul(right),
                Kind::Slash => left.checked_div(right),
                Kind::Percent => left.checked_rem(right),
                Kind::Shl => u32::try_from(right)
                    .ok()
                    .and_then(|shift| left.checked_shl(shift)),
                Kind::Shr => u32::try_from(right)
                    .ok()
                    .and_then(|shift| left.checked_shr(shift)),
                Kind::Amp => Some(left & right),
                Kind::Pipe => Some(left | right),
                Kind::Caret => Some(left ^ right),
                _ => {
                    return Err(Diagnostic::new(
                        expr.span,
                        "this operator is not supported in an integer associated constant",
                    ));
                }
            };
            value.ok_or_else(|| {
                Diagnostic::new(
                    expr.span,
                    "associated constant arithmetic overflows or divides by zero",
                )
            })
        }
        _ => Err(Diagnostic::new(
            expr.span,
            "associated constant values must be literals, earlier constants, and checked arithmetic",
        )),
    }
}
fn evaluate_const_bool(
    expr: &ast::Expr,
    consts: &BTreeMap<String, ConstValue>,
    depth: usize,
) -> Result<bool> {
    if depth >= 64 {
        return Err(Diagnostic::new(
            expr.span,
            "associated constant expression is too deeply nested",
        ));
    }
    match &expr.kind {
        ast::ExprKind::Bool(value) => Ok(*value),
        ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
            let Some(value) = consts.get(name) else {
                return Err(Diagnostic::new(
                    expr.span,
                    format!("unknown associated constant '{name}'"),
                ));
            };
            match value.ty {
                Type::Bool if value.elements.is_empty() => Ok(value.bits != 0),
                _ => Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is not a Bool",
                )),
            }
        }
        ast::ExprKind::Unary {
            op: crate::lexer::Kind::Bang,
            operand,
            ..
        } => Ok(!evaluate_const_bool(operand, consts, depth + 1)?),
        ast::ExprKind::Binary { op, left, right } => {
            use crate::lexer::Kind;
            match op {
                Kind::AmpAmp => {
                    let left = evaluate_const_bool(left, consts, depth + 1)?;
                    Ok(left && evaluate_const_bool(right, consts, depth + 1)?)
                }
                Kind::PipePipe => {
                    let left = evaluate_const_bool(left, consts, depth + 1)?;
                    Ok(left || evaluate_const_bool(right, consts, depth + 1)?)
                }
                Kind::Eq | Kind::Ne | Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => {
                    let left = evaluate_const_int(left, consts)?;
                    let right = evaluate_const_int(right, consts)?;
                    Ok(match op {
                        Kind::Eq => left == right,
                        Kind::Ne => left != right,
                        Kind::Lt => left < right,
                        Kind::Le => left <= right,
                        Kind::Gt => left > right,
                        Kind::Ge => left >= right,
                        _ => unreachable!(),
                    })
                }
                _ => Err(Diagnostic::new(
                    expr.span,
                    "this operator is not supported in a Bool associated constant",
                )),
            }
        }
        _ => Err(Diagnostic::new(
            expr.span,
            "Bool associated constant values must be literals, earlier constants, comparisons, and boolean operators",
        )),
    }
}
/// One statically dispatched method: its checked function binding and visibility.
#[derive(Debug, Clone, Copy)]
struct MethodDefinition {
    binding: BindingId,
    public: bool,
    unit: usize,
    /// Index into `Functions::impl_instantiations` for a method selected from a
    /// generic impl. Concrete methods leave this `None`.
    impl_arguments: Option<usize>,
}
/// Key of a checked function instance: binding plus type, grade, effect, and
/// natural const arguments.
type InstanceKey = (
    BindingId,
    Vec<Type>,
    Vec<Grade>,
    Vec<usize>,
    Vec<u16>,
    Option<usize>,
);
/// One receiver type's trait-provided methods, each with the specialization
/// arguments that select it.
type TraitMethodTable = BTreeMap<String, Vec<(BindingId, TraitArguments, MethodDefinition)>>;
/// Type, grade, const, and effect arguments of one specialization.
type GenericArguments = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u16>);
/// Generic arguments and checked values produced by inference.
type Inferred = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u16>, Vec<Expr>);
/// Lifetime metadata copied from the first member method into a synthesized
/// closed-world dispatcher: parameter lifetimes, result lifetime, and bounds.
type WitnessLifetimes = (
    Vec<Option<String>>,
    Option<String>,
    BTreeSet<(String, String)>,
);
/// FND-ROWS-INFER: the rows of private functions that omit theirs. The check
/// runs in passes: each assumes the rows the previous one found, checks every
/// inferred body with all effects available and records what it requires.
/// Rows only grow, so the passes reach the least fixed point; callees are
/// checked before their callers, so one pass usually settles it.
#[derive(Debug, Default)]
struct RowInference {
    /// Rows assumed at the start of this pass.
    guesses: BTreeMap<BindingId, u16>,
    /// Rows found by this pass: the union over each function's instances.
    found: BTreeMap<BindingId, u16>,
    /// A body was checked against a row that later grew in this pass.
    stale: bool,
}
/// Function instances. A monomorphic function has one instance; a generic
/// function gets one per distinct list of type arguments that is used.
struct Functions<'a> {
    stage_templates: BTreeSet<usize>,
    declared: BTreeMap<BindingId, Declared<'a>>,
    /// `where len >= N` clauses of struct fields, by struct and field name.
    field_lengths: BTreeMap<BindingId, BTreeMap<String, &'a ast::Expr>>,
    /// Element accesses whose bound was proved, and those checked at run
    /// time (reported with KUSH_PROOF_REPORT=1).
    bounds_proved: usize,
    bounds_checked: usize,
    /// PROOF-FUZZ: run-time checks the prover could not discharge, keyed so a
    /// body checked twice records each check once.
    obligations: BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
    /// Checks the prover discharged, keyed the same way.
    discharged: BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
    /// The function instance whose body is being checked.
    checking: usize,
    /// Frozen recursive result-origin summaries, solved once before any body
    /// is checked. Provisional summaries never reach signature construction.
    summaries: recursive_lifetimes::Summaries,
    signatures: Vec<Signature>,
    /// Checked bodies aligned with `signatures`; `None` still needs checking,
    /// `Some` is a synthetic lambda/adapter body.
    bodies: Vec<Option<Function>>,
    instances: BTreeMap<InstanceKey, usize>,
    /// Instances created so far of each declaration; see [`MAX_INSTANCES`].
    instance_counts: BTreeMap<BindingId, usize>,
    /// Instances with type, grade, natural, effect or impl arguments; see
    /// [`MAX_GENERIC_INSTANCES`].
    generic_instances: usize,
    pending: Vec<usize>,
    /// Synthetic function adapter cache, keyed by optional static source
    /// function index and the source/target arrow types.
    adapter_cache: BTreeMap<(Option<usize>, Type, Type), usize>,
    certificates: Vec<crate::facts::Certificate>,
    /// Checked foreign imports, keyed by the function-instance index used by
    /// `Target::Foreign`. Only direct calls reach these entries.
    foreign_functions: BTreeMap<usize, ForeignFunction>,
    /// Checked nested map fusions produced while specializing bodies.
    fusions: usize,
    /// Deduplicated allocator-context shapes built while checking bodies.
    allocator_contexts: Vec<AllocatorContextSpec>,
    /// Set when any body uses a structured-task operation.
    uses_tasks: bool,
    uses_threads: bool,
    uses_unwinding: bool,
    /// GPU-SUBSET: declarations marked `#[gpu]`.
    gpu: BTreeSet<BindingId>,
    /// Task body functions whose binding-based linear result must be rejected
    /// once their body has been checked.
    /// Monotonic counter for compiler-internal elided input lifetimes. The
    /// generated names are not surface syntax, so they cannot collide with a
    /// declared lifetime name.
    elided_lifetimes: usize,
    /// Declared traits and their method signatures (with `Self` still
    /// symbolic). Used for exact impl-signature comparison and to materialize
    /// inherited default bodies.
    traits: BTreeMap<BindingId, TraitDefinition<'a>>,
    /// Inherent methods keyed by concrete receiver type and method name.
    inherent: BTreeMap<Type, BTreeMap<String, MethodDefinition>>,
    /// Associated functions of a non-generic inherent impl: no receiver,
    /// called as `Type.name(..)` and never by dot-call on a value. Keyed by
    /// the type declaration's binding.
    associated_fns: BTreeMap<BindingId, BTreeMap<String, MethodDefinition>>,
    /// Trait methods keyed by trait binding, canonical trait arguments, and
    /// concrete receiver type, then method name.
    trait_impls: BTreeMap<(BindingId, TraitArguments, Type), BTreeMap<String, MethodDefinition>>,
    /// Every trait method available for a concrete receiver type, for
    /// unqualified dispatch and deterministic ambiguity diagnostics.
    methods_by_type: BTreeMap<Type, TraitMethodTable>,
    /// Trait specializations inherited by materialized default methods, indexed
    /// by `Declared::default_specialization`.
    default_specializations: Vec<(BindingId, TraitArguments)>,
    /// Associated values of each impl, indexed by `Declared::impl_associated`.
    impl_associated: Vec<ImplAssociated>,
    /// Inherent associated constants keyed by the nominal target type.
    inherent_consts: BTreeMap<Type, BTreeMap<String, ConstValue>>,
    /// Associated constants of every trait impl, keyed by trait, canonical
    /// trait arguments, and receiver type. Used by `Type.CONST` projections.
    trait_consts: BTreeMap<(BindingId, TraitArguments, Type), BTreeMap<String, ConstValue>>,
    /// Associated values of every trait impl, keyed like `trait_impls`.
    trait_associated: BTreeMap<(BindingId, TraitArguments, Type), ImplAssociated>,
    /// Every declared impl header, concrete or generic, in declaration order.
    /// Coherence comparisons and generic dispatch both use this table.
    impl_headers: Vec<ImplHeader>,
    /// Deduplicated instantiations of generic impl headers. A method selected
    /// from `impl_headers[i]` points here so its body is monomorphized once per
    /// concrete impl-argument list.
    impl_instantiations: Vec<ImplInstantiation>,
    impl_instantiation_cache: BTreeMap<(usize, ImplArguments), usize>,
    /// Closed-world trait objects keyed by their runtime union type. One union
    /// may represent several traits when their concrete member sets coincide;
    /// unqualified dispatch then requires an unambiguous trait method name.
    object_traits: BTreeMap<Type, Vec<(BindingId, TraitArguments)>>,
    /// Checked dynamic-dispatch functions, one per `(trait, arguments, method)`.
    dynamic_dispatch: BTreeMap<(BindingId, TraitArguments, String), (usize, Type)>,
    /// EFF-CAP-RESUME-CAPTURING trampolines by (operation, handler arrow).
    capability_thunks: BTreeMap<(usize, usize), (usize, Type)>,
    /// CAP-CAPTURING-LEXICAL: private operation ids handed out so far.
    private_operations: usize,
    /// FND-ROWS-INFER: private functions that omit their row.
    inferred_rows: BTreeSet<BindingId>,
    /// FND-ROWS-INFER: the rows assumed and found by this pass.
    rows: &'a mut RowInference,
    /// FND-ROWS-INFER: functions with an instance body checked (or being
    /// checked) in this pass; one that names a function whose row then
    /// grows observed a stale row.
    checked_bodies: BTreeSet<BindingId>,
    /// FND-ROWS-INFER: the bindings each declared function's body names.
    body_refs: BTreeMap<BindingId, BTreeSet<BindingId>>,
    /// Registered members of each dynamically dispatched object specialization.
    /// Indexed by `Type::DynObj`. A member identifier is its position here.
    dyn_members: Vec<Vec<DynMember>>,
    /// Monomorphized generic-method contracts per dynamic object. A member
    /// registered after a call site instantiates every recorded contract.
    dyn_methods: BTreeMap<usize, BTreeMap<DynMethodKey, DynMethodContract>>,
    /// Checked upcast edges `(from, to)` between dynamic objects: every member
    /// registered in `from` is also registered in `to`, so the runtime upcast
    /// can map each identifier through the member tables.
    dyn_upcasts: BTreeSet<(usize, usize)>,
    /// Checked call sites on dynamically dispatched trait objects.
    dyn_calls: Vec<DynCallSpec>,
    /// Checked borrowed call sites on closed-world union objects.
    union_calls: Vec<UnionCallSpec>,
    logical: &'a crate::check::LogicalEnvironment,
}
/// Most instances of any one declaration. Specialization only multiplies
/// instances of a declaration through its type, grade, natural or effect
/// arguments, so this is what stops polymorphic recursion (each call
/// instantiating the next with a larger type) from specializing forever. The
/// number of functions in a program is otherwise unbounded: at most this many
/// per declaration, plus the lambdas and adapters those instances contain.
const MAX_INSTANCES: usize = 256;
/// Most instances of generic declarations in a program, all together. In a
/// polymorphic recursion through several declarations each step wraps the
/// type once more, so the per-declaration cap alone would allow types
/// 256 times the number of declarations deep, and checking time grows with
/// the cube of that (32 declarations took over a minute to reject). Ordinary
/// functions have one instance each and are not counted.
const MAX_GENERIC_INSTANCES: usize = 1024;
/// Total attempts for the bounded cross-parameter partition replay. This is a
/// deterministic work budget, not a completeness claim: exhausting it is an
/// explicit diagnostic asking for specialization.
const UNIFY_BACKTRACK_BUDGET: usize = 4096;

/// Traits that must use the dynamically dispatched object representation.
/// A generic or blanket impl leaves the member set open; a `dyn` mention in
/// any nominal field (including through an alias) would make the layout depend
/// on impl collection. Both are decided syntactically before layout.
fn dynamic_trait_set(module: &ast::Module, resolution: &Resolution) -> BTreeSet<BindingId> {
    fn scan(ty: &ast::Type, resolution: &Resolution, out: &mut BTreeSet<BindingId>) {
        match &ty.kind {
            ast::TypeKind::Dyn(bounds) => {
                for bound in bounds {
                    if let Some(id) = resolution.reference(bound.trait_ref.span)
                        && resolution.bindings[id].kind == BindingKind::Trait
                    {
                        out.insert(id);
                    }
                }
                for inner in ast::dyn_types(bounds) {
                    scan(inner, resolution, out);
                }
            }
            ast::TypeKind::Named { arguments, .. } => {
                for argument in arguments {
                    scan(argument, resolution, out);
                }
            }
            ast::TypeKind::Tuple(items) => {
                for item in items {
                    scan(item, resolution, out);
                }
            }
            ast::TypeKind::Array(element, _) | ast::TypeKind::Slice(element) => {
                scan(element, resolution, out)
            }
            ast::TypeKind::Borrow { inner, .. } => scan(inner, resolution, out),
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                for parameter in parameters {
                    scan(&parameter.ty, resolution, out);
                }
                scan(result, resolution, out);
            }
            ast::TypeKind::Binary { left, right, .. } => {
                scan(left, resolution, out);
                scan(right, resolution, out);
            }
            ast::TypeKind::Graded { inner, .. } => scan(inner, resolution, out),
            ast::TypeKind::Structural { fields, row, .. } => {
                for field in fields {
                    scan(&field.ty, resolution, out);
                }
                if let Some(row) = row {
                    scan(row, resolution, out);
                }
            }
            _ => {}
        }
    }
    // A trait named in a multi-trait object always uses the dynamic
    // representation, so an upcast never has to convert a closed union.
    let mut out = resolution.multi_object_traits.clone();
    for declaration in &module.items {
        match &declaration.item.kind {
            ast::ItemKind::Impl {
                generics,
                trait_path: Some(trait_path),
                ..
            } if !generics.is_empty() => {
                if let Some(id) = resolution.reference(trait_path.span)
                    && resolution.bindings[id].kind == BindingKind::Trait
                {
                    out.insert(id);
                }
            }
            ast::ItemKind::Struct { fields, .. } => {
                for field in fields {
                    scan(&field.ty, resolution, &mut out);
                }
            }
            ast::ItemKind::Trait { methods, .. }
                if methods
                    .iter()
                    .any(|method| !method.function.generics.is_empty()) =>
            {
                // A generic method needs per-call monomorphization, which the
                // fixed-layout dynamic representation provides; keep the trait
                // out of the closed-world union path.
                if let Some(id) = resolution.declarations.get(&declaration.item.span.start) {
                    out.insert(*id);
                }
            }
            ast::ItemKind::Enum { variants, .. } => {
                for variant in variants {
                    match &variant.payload {
                        ast::Payload::Unit | ast::Payload::Fields(_) => {}
                        ast::Payload::Tuple(types) => {
                            for ty in types {
                                scan(ty, resolution, &mut out);
                            }
                        }
                        ast::Payload::Record(fields) => {
                            for field in fields {
                                scan(&field.ty, resolution, &mut out);
                            }
                        }
                    }
                }
            }
            ast::ItemKind::Alias { ty, .. } => scan(ty, resolution, &mut out),
            _ => {}
        }
    }
    out
}

/// Check one in-memory file. Only standard-library modules can be imported.
pub fn check(source: &str) -> Result<Executable> {
    let program = crate::program::load_source("<input>", source).map_err(|(_, e)| e)?;
    check_program(&program)
}
/// The kernel-checked logical half of a program that may also contain
/// executable code, exactly as `check_program` admits it, without checking
/// executable bodies. Used by `kush core` to export the logical environment.
pub fn logical_module(source: &str) -> Result<crate::check::CheckedModule> {
    let program = crate::program::load_source("<input>", source).map_err(|(_, e)| e)?;
    let injected = inject_allocator_protocol(&program)?;
    let module = &injected.module;
    let mut resolution = resolve::resolve_program(&injected)?;
    collect_default_bindings(module, &mut resolution)?;
    crate::grades::validate_algebras(&mut resolution)?;
    let logical =
        crate::kernel::on_kernel_stack(|| crate::check::check_program(module, &resolution))?;
    Ok(crate::check::CheckedModule {
        resolution,
        kernel: logical.kernel,
        definitions: logical.definitions,
    })
}
/// The checked allocator-instance protocol. It is an ordinary trait declaration
/// injected ahead of user items, so impls are checked exactly like any other
/// trait: receiver modes, parameter/result layouts, grades, and effect rows must
/// match. The context adapter runs `free` during implicit drop, hence its empty
/// effect row.
const ALLOCATOR_PROTOCOL_SOURCE: &str = r#"
trait AllocatorProtocol {
    fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc};
    fn free(self: &mut Self, block: Bytes) -> Unit ! {};
    fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc};
}
"#;
/// Synthetic spans sit far above any admitted source file (the loader rejects
/// programs over 16 MiB) so they cannot collide with a user declaration.
const ALLOCATOR_PROTOCOL_BASE: usize = 1 << 40;
/// Prepend the built-in allocator protocol trait to a loaded program.
fn inject_allocator_protocol(program: &crate::program::Program) -> Result<crate::program::Program> {
    let prelude = crate::parser::parse_at(ALLOCATOR_PROTOCOL_SOURCE, ALLOCATOR_PROTOCOL_BASE)?;
    let added = prelude.items.len();
    let mut injected = program.clone();
    // Give synthetic diagnostics a renderable source file rather than mapping
    // them onto the first user file.
    injected.sources.files.push(crate::program::SourceFile {
        name: "<allocator-protocol>".to_owned(),
        text: ALLOCATOR_PROTOCOL_SOURCE.to_owned(),
        base: ALLOCATOR_PROTOCOL_BASE,
    });
    for (index, unit) in injected.units.iter_mut().enumerate() {
        // The prelude belongs to the root unit, which is first. Later units
        // keep their own item ranges, shifted by the inserted item count.
        if index != 0 {
            unit.items.start += added;
        }
        unit.items.end += added;
    }
    // A root module header must remain item zero.
    let position = usize::from(
        injected
            .module
            .items
            .first()
            .is_some_and(|item| matches!(item.item.kind, ast::ItemKind::Module(_))),
    );
    let tail = injected.module.items.split_off(position);
    injected.module.items.extend(prelude.items);
    injected.module.items.extend(tail);
    Ok(injected)
}
/// Check a loaded multi-module program. Only the root module may define `main`.
/// KUSH-RUST-EXPORT: validate every `export "symbol" fn`. v1 crosses the
/// C ABI with scalars only: integers, floats and `Bool` parameters, a scalar
/// or `Unit` result, an effect row within `{panic}` (a panic aborts the
/// process), no generics, lifetimes, erased parameters or usage grades.
fn checked_exports(
    signatures: &[Signature],
    declared: &BTreeMap<BindingId, Declared<'_>>,
    resolution: &Resolution,
    types: &Types<'_>,
) -> Result<Vec<ExportedFunction>> {
    let primitive = |ty: Type| matches!(ty, Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_));
    // EXPORT-RECORDS: records of scalars (or such records) cross as C
    // structs; `&Bytes` parameters as a pointer and a length.
    fn scalar_record(types: &Types<'_>, ty: Type, depth: usize) -> bool {
        let Some(id) = ty.layout() else {
            return false;
        };
        let layout = &types.enums[id];
        depth < 8
            && layout.record
            && !layout.tuple
            && layout.array.is_none()
            && layout.dynamic_array.is_none()
            && layout.variants.len() == 1
            && !layout.variants[0].fields.is_empty()
            && layout.variants[0].fields.iter().all(|field| {
                matches!(
                    field,
                    Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_)
                ) || scalar_record(types, *field, depth + 1)
            })
    }
    let scalar = |ty: Type| primitive(ty) || scalar_record(types, ty, 0);
    let bytes_ref = |ty: Type| matches!(ty, Type::Ref(p) if types.pointees[p] == Type::Bytes);
    let mut exports: Vec<ExportedFunction> = Vec::new();
    // Generic functions have no instance until called, so check them here.
    for info in declared.values() {
        let f = info.ast;
        if f.export.is_some()
            && (!f.generics.is_empty() || !f.lifetimes.is_empty() || info.impl_template.is_some())
        {
            return Err(Diagnostic::new(
                info.span,
                format!(
                    "exported function '{}' cannot be generic or take lifetime parameters",
                    f.name
                ),
            ));
        }
    }
    for (index, sig) in signatures.iter().enumerate() {
        let Some(info) = declared.get(&sig.binding) else {
            continue;
        };
        let f = info.ast;
        let Some(symbol) = &f.export else {
            continue;
        };
        let fail = |message: String| Err(Diagnostic::new(sig.span, message));
        let valid_symbol = !symbol.is_empty()
            && symbol.len() <= 128
            && symbol.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            && symbol
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_');
        if !valid_symbol {
            return fail(format!(
                "export symbol '{symbol}' must be a C identifier of at most 128 characters"
            ));
        }
        if symbol.starts_with("kush_") || symbol == "main" {
            return fail(format!(
                "export symbol '{symbol}' is reserved for the Kush runtime"
            ));
        }
        if exports.iter().any(|e| e.symbol == *symbol) {
            return fail(format!("export symbol '{symbol}' is declared twice"));
        }
        if !f.generics.is_empty() || !f.lifetimes.is_empty() || info.impl_template.is_some() {
            return fail(format!(
                "exported function '{}' cannot be generic or take lifetime parameters",
                f.name
            ));
        }
        if f.parameters.iter().any(|p| p.erased)
            || sig.parameter_grades.iter().any(Option::is_some)
            || sig.result_grade.is_some()
        {
            return fail(format!(
                "exported function '{}' cannot take erased parameters or usage grades",
                f.name
            ));
        }
        // Every field of an exported record must be `pub`: a C or Rust
        // caller builds and reads the whole struct, which would bypass the
        // module's private fields.
        fn private_field(types: &Types<'_>, ty: Type, depth: usize) -> Option<String> {
            let id = ty.layout()?;
            let layout = &types.enums[id];
            if !layout.record || depth > 8 {
                return None;
            }
            let variant = layout.variants.first()?;
            for (name, field) in variant.names.iter().zip(&variant.fields) {
                if !types.field_public(layout.definition, name) {
                    return Some(name.clone());
                }
                if let Some(inner) = private_field(types, *field, depth + 1) {
                    return Some(inner);
                }
            }
            None
        }
        for ty in sig.parameters.iter().chain([&sig.result]) {
            if scalar_record(types, *ty, 0)
                && let Some(field) = private_field(types, *ty, 0)
            {
                return fail(format!(
                    "exported function '{}' passes a record whose field '{field}' is private; a C or Rust caller sees the whole struct, so mark every field 'pub'",
                    f.name
                ));
            }
        }
        if sig
            .parameters
            .iter()
            .any(|ty| !scalar(*ty) && !bytes_ref(*ty))
        {
            return fail(format!(
                "exported function '{}' takes only integers, floats, Bool, records of those, and &Bytes across the C ABI",
                f.name
            ));
        }
        if !(scalar(sig.result) || sig.result == Type::Unit) {
            return fail(format!(
                "exported function '{}' returns an integer, float, Bool, a record of those, or Unit across the C ABI",
                f.name
            ));
        }
        if sig.effects & !PANIC != 0 || !sig.effect_arguments.is_empty() {
            return fail(format!(
                "exported function '{}' must have the empty effect row {{}}; a panic aborts the process",
                f.name
            ));
        }
        let names = f
            .parameters
            .iter()
            .map(|p| {
                resolution
                    .binder(p.span)
                    .map(|id| resolution.bindings[id].name.clone())
                    .unwrap_or_else(|| "arg".to_owned())
            })
            .collect::<Vec<_>>();
        exports.push(ExportedFunction {
            symbol: symbol.clone(),
            index,
            parameters: names
                .into_iter()
                .zip(sig.parameters.iter().copied())
                .collect(),
            result: sig.result,
        });
    }
    Ok(exports)
}

pub fn check_program(program: &crate::program::Program) -> Result<Executable> {
    if let Some(prepared) = crate::staging::prepare(program)? {
        let (executable, initializers) =
            check_program_unstaged(&prepared.program, &prepared.entries, false, false)?;
        let mut executable =
            crate::staging::materialize(executable, initializers, &prepared.entries)?;
        crate::suspend::lower(&mut executable)?;
        return Ok(executable);
    }
    check_program_unstaged(program, &[], true, false).map(|(executable, _)| executable)
}

fn check_program_unstaged(
    source_program: &crate::program::Program,
    stage_entries: &[crate::staging::Entry],
    lower_suspensions: bool,
    validate_generic_staging: bool,
) -> Result<(Executable, BTreeMap<usize, usize>)> {
    // FND-ROWS-INFER: rerun the check while an inferred row grew after a
    // body had observed it. A pass that fails after a row grew is rerun too:
    // the failure may come from the smaller row it assumed.
    let mut guesses = BTreeMap::new();
    loop {
        let mut rows = RowInference {
            guesses: guesses.clone(),
            ..RowInference::default()
        };
        let result = check_program_pass(
            source_program,
            stage_entries,
            lower_suspensions,
            validate_generic_staging,
            &mut rows,
        );
        let grown = rows
            .found
            .iter()
            .any(|(binding, row)| row & !guesses.get(binding).copied().unwrap_or(0) != 0);
        if !grown || (result.is_ok() && !rows.stale) {
            return result;
        }
        for (binding, row) in rows.found {
            *guesses.entry(binding).or_insert(0) |= row;
        }
    }
}
fn check_program_pass(
    source_program: &crate::program::Program,
    stage_entries: &[crate::staging::Entry],
    lower_suspensions: bool,
    validate_generic_staging: bool,
    rows: &mut RowInference,
) -> Result<(Executable, BTreeMap<usize, usize>)> {
    let injected = inject_allocator_protocol(source_program)?;
    let program = &injected;
    let module = &program.module;
    reject_stored_capabilities(module)?;
    reject_omitted_method_rows(module)?;
    let mut resolution = resolve::resolve_staged_program(program)?;
    // Default trait methods inherited by an impl need one synthetic function
    // binding per (impl, method) pair. Allocate them before `Types` borrows the
    // resolver table: the table cannot be mutated once type lowering holds it.
    let default_bindings = collect_default_bindings(module, &mut resolution)?;
    crate::grades::validate_algebras(&mut resolution)?;
    let resolution = &resolution;
    let mut initializer_bindings = BTreeMap::new();
    for stage in stage_entries {
        let target = resolution.declarations[&stage.target.start];
        let initializer = resolution.declarations[&stage.initializer.start];
        initializer_bindings.insert(target, initializer);
    }
    // Total functions and aliases are erased and checked by the trusted kernel
    // before any executable body can cite them as proof evidence.
    let logical =
        crate::kernel::on_kernel_stack(|| crate::check::check_program(module, resolution))?;
    // A trait object whose member set is open (a generic or blanket impl) or
    // that appears inside a laid-out nominal field cannot use the inline
    // closed-world union: its width would depend on impl collection, which in
    // turn may depend on the layout. Those traits use the dynamically
    // dispatched fat-object representation instead. The decision must be made
    // before `Types::new` instantiates monomorphic layouts.
    let dynamic_traits = dynamic_trait_set(module, resolution);
    let mut types = Types::new(module, resolution, &logical, dynamic_traits)?;
    let mut field_lengths: BTreeMap<BindingId, BTreeMap<String, &ast::Expr>> = BTreeMap::new();
    for declaration in &module.items {
        if let ast::ItemKind::Struct { fields, .. } = &declaration.item.kind
            && fields.iter().any(|field| field.min_length.is_some())
        {
            let id = resolution.declarations[&declaration.item.span.start];
            let entry = field_lengths.entry(id).or_default();
            for field in fields {
                if let Some(length) = &field.min_length {
                    entry.insert(field.name.clone(), &**length);
                }
            }
        }
    }
    let mut functions = Functions {
        stage_templates: BTreeSet::new(),
        declared: BTreeMap::new(),
        field_lengths,
        bounds_proved: 0,
        bounds_checked: 0,
        obligations: BTreeMap::new(),
        discharged: BTreeMap::new(),
        checking: 0,
        summaries: recursive_lifetimes::Summaries::default(),
        signatures: Vec::new(),
        bodies: Vec::new(),
        instances: BTreeMap::new(),
        instance_counts: BTreeMap::new(),
        generic_instances: 0,
        pending: Vec::new(),
        adapter_cache: BTreeMap::new(),
        certificates: Vec::new(),
        foreign_functions: BTreeMap::new(),
        fusions: 0,
        allocator_contexts: Vec::new(),
        uses_tasks: false,
        uses_threads: false,
        uses_unwinding: false,
        gpu: BTreeSet::new(),
        elided_lifetimes: 0,
        traits: BTreeMap::new(),
        inherent: BTreeMap::new(),
        associated_fns: BTreeMap::new(),
        trait_impls: BTreeMap::new(),
        methods_by_type: BTreeMap::new(),
        default_specializations: Vec::new(),
        impl_associated: Vec::new(),
        inherent_consts: BTreeMap::new(),
        trait_consts: BTreeMap::new(),
        trait_associated: BTreeMap::new(),
        impl_headers: Vec::new(),
        impl_instantiations: Vec::new(),
        impl_instantiation_cache: BTreeMap::new(),
        object_traits: BTreeMap::new(),
        dynamic_dispatch: BTreeMap::new(),
        capability_thunks: BTreeMap::new(),
        private_operations: 0,
        inferred_rows: BTreeSet::new(),
        rows,
        checked_bodies: BTreeSet::new(),
        body_refs: BTreeMap::new(),
        dyn_members: Vec::new(),
        dyn_methods: BTreeMap::new(),
        dyn_upcasts: BTreeSet::new(),
        dyn_calls: Vec::new(),
        union_calls: Vec::new(),
        logical: &logical,
    };
    let mut effect_operations = BTreeMap::new();
    for declaration in &module.items {
        let ast::ItemKind::Effect {
            name,
            parameter,
            result,
            effects,
        } = &declaration.item.kind
        else {
            continue;
        };
        if effect_operations.contains_key(name) {
            return Err(Diagnostic::new(
                declaration.item.span,
                format!("duplicate effect operation '{name}'"),
            ));
        }
        let subst = crate::runtime_types::Subst::default();
        let parameter_ty = types.ty_in(parameter, &subst)?;
        let parameter_ty = types.full(parameter_ty, parameter.span)?;
        let result_ty = if types.names_never(result) {
            Type::Never
        } else {
            let result_ty = types.ty_in(result, &subst)?;
            types.full(result_ty, result.span)?
        };
        let parameter = parameter_ty;
        let result = result_ty;
        if matches!(parameter, Type::Never) {
            return Err(Diagnostic::new(
                declaration.item.span,
                "an effect operation cannot use Never as its payload type",
            ));
        }
        if parameter.is_view()
            || result.is_view()
            || matches!(parameter, Type::Ref(_) | Type::RefMut(_))
            || matches!(result, Type::Ref(_) | Type::RefMut(_))
        {
            return Err(Diagnostic::new(
                declaration.item.span,
                "dynamic effect operations cannot carry borrowed payloads or results; a handler stack entry has no caller lifetime to borrow from",
            ));
        }
        let (latent, variables) = crate::runtime_types::effect_bits_partial(resolution, effects)?;
        if !variables.is_empty() || latent & !EFFECT_BITS != 0 {
            return Err(Diagnostic::new(
                declaration.item.span,
                "an effect operation's handler effects are built-in effects (io, alloc, panic, suspend)",
            ));
        }
        let id = effect_operations.len();
        effect_operations.insert(
            name.clone(),
            EffectOperation {
                id,
                parameter,
                result,
                latent,
            },
        );
        types
            .capability_operations
            .insert(name.clone(), (parameter, result));
    }
    let mut abortive_operations = vec![false; effect_operations.len()];
    for operation in effect_operations.values() {
        abortive_operations[operation.id] = operation.result == Type::Never;
    }
    let mut effect_bits = vec![0; effect_operations.len()];
    for (name, operation) in &effect_operations {
        effect_bits[operation.id] = resolution.effect_bits.get(name).copied().unwrap_or(0);
    }
    let effect_operations = &effect_operations;
    let mut monomorphic = Vec::new();
    let mut main_stack = None;
    for declaration in &module.items {
        let span = declaration.item.span;
        // `#[kernel_steps(N)]` raises the kernel budget of a logical
        // declaration; the logical checker has already validated and used it.
        let logical_declaration = match &declaration.item.kind {
            ast::ItemKind::Function(f) => f.total,
            ast::ItemKind::Enum { total, .. } => *total,
            ast::ItemKind::Prop { .. } | ast::ItemKind::Alias { .. } => true,
            _ => false,
        };
        if let Some(attribute) = declaration
            .attributes
            .iter()
            .find(|attribute| attribute.kind == "kernel_steps" && !logical_declaration)
        {
            return Err(Diagnostic::new(
                attribute.span,
                "#[kernel_steps(N)] applies to logical declarations only: total fn, total enum, prop and type aliases",
            ));
        }
        if declaration
            .attributes
            .iter()
            .any(|attribute| attribute.kind != "kernel_steps")
            && !matches!(
                declaration.item.kind,
                ast::ItemKind::Function(_)
                    | ast::ItemKind::Enum { .. }
                    | ast::ItemKind::Struct { .. }
            )
        {
            return Err(Diagnostic::new(
                span,
                "attributes apply to functions, enums, and structs only",
            ));
        }
        let function = matches!(declaration.item.kind, ast::ItemKind::Function(_));
        let data = matches!(
            declaration.item.kind,
            ast::ItemKind::Struct { .. } | ast::ItemKind::Enum { .. }
        );
        for attribute in &declaration.attributes {
            if attribute.kind == "kernel_steps" {
                continue;
            }
            if attribute.kind == "stack_size" {
                // LANG-STACK-SIZE: only the program's own main, in MiB.
                let is_main = matches!(&declaration.item.kind, ast::ItemKind::Function(f) if f.name == "main")
                    && resolution
                        .declarations
                        .get(&span.start)
                        .is_some_and(|binding| resolution.unit_of.get(binding) == Some(&0));
                if !is_main {
                    return Err(Diagnostic::new(
                        attribute.span,
                        "#[stack_size(N)] applies to the program's main function only",
                    ));
                }
                let mebibytes = attribute
                    .argument
                    .as_deref()
                    .and_then(|text| text.parse::<u64>().ok())
                    .filter(|value| (1..=65536).contains(value))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            attribute.span,
                            "#[stack_size(N)] takes the main stack size in MiB, from 1 to 65536",
                        )
                    })?;
                if main_stack.replace(mebibytes << 20).is_some() {
                    return Err(Diagnostic::new(
                        attribute.span,
                        "#[stack_size(N)] may appear once",
                    ));
                }
                continue;
            }
            // FND-ROWS-ATTRS: the effect row is the contract. A row without
            // `alloc`/`suspend` (and whose row variables exclude it, as in
            // `e: Effects - alloc`) already says everything the attributes did.
            if function && matches!(attribute.kind.as_str(), "noalloc" | "nosuspend") {
                let effect = if attribute.kind == "noalloc" {
                    "alloc"
                } else {
                    "suspend"
                };
                return Err(Diagnostic::new(
                    attribute.span,
                    format!(
                        "#[{}] was removed: the effect row is the contract. Leave '{effect}' out of the row; for an effect-polymorphic row, exclude it from the row variable, as in 'e: Effects - {effect}'",
                        attribute.kind
                    ),
                ));
            }
            let valid = if function {
                matches!(attribute.kind.as_str(), "test" | "fuzz" | "gpu")
                    && attribute.argument.is_none()
            } else if data {
                (attribute.kind == "linear"
                    && attribute
                        .argument
                        .as_deref()
                        .is_none_or(|argument| argument.starts_with("unwind=")))
                    || attribute.kind == "foreign"
            } else {
                false
            };
            if !valid {
                return Err(Diagnostic::new(
                    attribute.span,
                    if function {
                        "functions support the #[test], #[fuzz], and #[gpu] attributes"
                    } else if data {
                        "data declarations support #[linear], #[linear(unwind = cleanup)] or #[foreign(\"release_symbol\")]"
                    } else {
                        "attributes apply to functions, enums, and structs only"
                    },
                ));
            }
            if attribute.kind == "foreign"
                && !matches!(declaration.item.kind, ast::ItemKind::Struct { .. })
            {
                return Err(Diagnostic::new(
                    attribute.span,
                    "#[foreign(\"release_symbol\")] declares an opaque resource and may only annotate a struct",
                ));
            }
        }
        let f = match &declaration.item.kind {
            ast::ItemKind::Module(_)
            | ast::ItemKind::Enum { .. }
            | ast::ItemKind::Prop { .. }
            | ast::ItemKind::Struct { .. }
            | ast::ItemKind::Trait { .. }
            | ast::ItemKind::Impl { .. }
            | ast::ItemKind::GradeAlgebra(_)
            | ast::ItemKind::Effect { .. }
            | ast::ItemKind::EffectRow { .. }
            | ast::ItemKind::Use(_) => continue,
            ast::ItemKind::Alias { .. } => continue,
            ast::ItemKind::Function(f) => f,
        };
        if f.total {
            // Checked by the logical kernel above and erased from runtime IR.
            continue;
        }
        // FND-ROWS-INFER: only a private function may omit its row; every
        // other row is a contract its callers outside the module rely on.
        if f.row_omitted() {
            let reason = if declaration.public {
                Some(
                    "a public function declares its effect row: it is the contract other modules check against",
                )
            } else if f.foreign.is_some() {
                Some("a foreign function declares its effect row")
            } else if f.export.is_some() {
                Some("an exported function declares its effect row")
            } else if declaration.attributes.iter().any(|a| a.kind == "gpu") {
                Some("a #[gpu] kernel declares its effect row")
            } else if f
                .generics
                .iter()
                .any(|generic| generic_category(resolution, generic) == GenericCategory::Effect)
            {
                Some("a function with effect parameters declares its effect row")
            } else {
                None
            };
            if let Some(reason) = reason {
                return Err(Diagnostic::new(
                    span,
                    format!("{reason}; add '! {{..}}' after the result type"),
                ));
            }
            functions
                .inferred_rows
                .insert(resolution.declarations[&span.start]);
        }
        for parameter in &f.parameters {
            if parameter.erased && split_grade(&parameter.ty).1.is_some() {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "erased parameters are already absent at runtime and cannot carry a usage grade",
                ));
            }
        }
        validate_erased_parameters(resolution, &logical, f)?;
        validate_length_templates(resolution, f)?;
        validate_runtime_length_signature(resolution, f, false)?;
        if f.body.is_none() {
            let Some(symbol) = &f.foreign else {
                return Err(Diagnostic::new(
                    span,
                    "executable functions require a body; declare an imported C function as 'foreign \"symbol\" fn name(...) -> T ! { io };'",
                ));
            };
            if !valid_c_symbol(symbol) {
                return Err(Diagnostic::new(
                    span,
                    "a foreign symbol must be a C identifier ([A-Za-z_][A-Za-z0-9_]*)",
                ));
            }
            // STD-SYS-FOREIGN: `kush_sys_*` symbols are the runtime's own host
            // stubs, which trust their arguments (a descriptor number, a
            // buffer's spare capacity). Only std may import them; the root
            // unit (0) may call itself `std.x`, so it never counts as std.
            if symbol.starts_with("kush_sys_") {
                let unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
                let std = unit != 0
                    && resolution
                        .units
                        .get(unit)
                        .is_some_and(|path| path.first().is_some_and(|p| p == "std"));
                if !std {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "foreign symbol '{symbol}' is reserved for the Kush standard library"
                        ),
                    ));
                }
            }
            if !f.generics.is_empty() || !f.lifetimes.is_empty() {
                return Err(Diagnostic::new(
                    span,
                    "a foreign function cannot be generic or lifetime-parameterized; declare one concrete C ABI signature",
                ));
            }
            if f.parameters.iter().any(|parameter| parameter.erased) {
                return Err(Diagnostic::new(
                    span,
                    "foreign functions cannot have erased proof parameters; FFI is runtime-only",
                ));
            }
            let (effects, _) = crate::runtime_types::effect_bits_partial(resolution, &f.effects)?;
            if effects & IO == 0 && !PURE_HOST_SYMBOLS.contains(&symbol.as_str()) {
                return Err(Diagnostic::new(
                    span,
                    "a foreign call has unchecked host side effects and requires the 'io' effect in its declared row",
                ));
            }
        } else if f.foreign.is_some() {
            return Err(Diagnostic::new(
                span,
                "a foreign declaration has no body; remove the implementation block",
            ));
        }
        if f.parameters.len() > 64 {
            return Err(Diagnostic::new(
                span,
                "executable limit exceeded (64 parameters)",
            ));
        }
        for generic in &f.generics {
            if let Some(bound) = &generic.bound {
                let binding = resolution
                    .reference(bound.span)
                    .map(|id| &resolution.bindings[id]);
                let supported = match binding {
                    Some(binding) if binding.kind == BindingKind::Builtin => {
                        matches!(binding.name.as_str(), "Type" | "Grade" | "Nat" | "Effects")
                    }
                    Some(binding) if binding.kind == BindingKind::Trait => {
                        matches!(&bound.kind, ast::TypeKind::Named { .. })
                    }
                    _ => false,
                };
                if !supported {
                    return Err(Diagnostic::new(
                        generic.span,
                        "executable generic parameters must be types, grades, compile-time naturals, effect rows, or declared traits ('T: Type', 'G: Grade', 'N: Nat', 'e: Effects', 'T: Trait')",
                    ));
                }
            }
        }
        let (fixed_effects, effect_variables) = if f.row_omitted() {
            (0, Default::default())
        } else {
            crate::runtime_types::effect_bits_partial(resolution, &f.effects)?
        };
        let binding = resolution.declarations[&span.start];
        if declaration.attributes.iter().any(|a| a.kind == "gpu") {
            crate::gpu::check_declaration(
                f,
                span,
                &declaration.attributes,
                fixed_effects,
                &effect_variables,
            )?;
            functions.gpu.insert(binding);
        }
        if f.name == "main"
            && !f.generics.is_empty()
            && resolution.unit_of.get(&binding) == Some(&0)
        {
            return Err(Diagnostic::new(span, "main must not be generic"));
        }
        functions.declared.insert(
            binding,
            Declared {
                ast: f,
                span,
                self_ty: None,
                default_specialization: None,
                impl_associated: None,
                impl_template: None,
            },
        );
        if f.generics.is_empty() {
            monomorphic.push(binding);
        }
    }
    let method_bindings = collect_methods(
        module,
        resolution,
        &default_bindings,
        &mut types,
        &logical,
        &mut functions,
    )?;
    prepare_trait_objects(&mut types, resolution, &mut functions)?;
    // Recursive borrow summaries are solved before any body is checked, so a
    // signature, callable arrow, or ownership judgment observes only the frozen
    // least fixed point. The solver rejects unseeded cycles and unsupported
    // boundaries instead of publishing a provisional contract.
    functions.summaries = recursive_lifetimes::solve(resolution, &functions.declared, &types)?;
    // Generic methods are monomorphized on demand at each call site. Only
    // monomorphic methods get an eagerly checked instance here.
    monomorphic.extend(method_bindings.into_iter().filter(|binding| {
        let declared = functions.declared[binding];
        // A generic impl method is instantiated only after dispatch
        // selects concrete impl arguments; it has no `Self` otherwise.
        declared.ast.generics.is_empty() && declared.impl_template.is_none()
    }));
    // FND-ROWS-INFER: check callees before their callers, so a body sees the
    // final rows of the inferred functions it names. Pending bodies are
    // checked last-in first-out, so callers are queued first.
    if !functions.inferred_rows.is_empty() {
        for (&binding, declared) in &functions.declared {
            let mut refs = BTreeSet::new();
            if let Some(body) = &declared.ast.body {
                collect_lambda_refs(resolution, body, &mut refs);
            }
            functions.body_refs.insert(binding, refs);
        }
        let mut order = Vec::new();
        let mut visited = BTreeSet::new();
        for &root in &monomorphic {
            // Iterative post-order: callees end up before callers.
            let mut stack = vec![(root, false)];
            while let Some((binding, expanded)) = stack.pop() {
                if expanded {
                    order.push(binding);
                    continue;
                }
                if !visited.insert(binding) {
                    continue;
                }
                stack.push((binding, true));
                if let Some(refs) = functions.body_refs.get(&binding) {
                    stack.extend(refs.iter().rev().map(|&callee| (callee, false)));
                }
            }
        }
        let wanted: BTreeSet<_> = monomorphic.iter().copied().collect();
        monomorphic = order
            .into_iter()
            .rev()
            .filter(|binding| wanted.contains(binding))
            .collect();
    }
    for binding in monomorphic {
        functions.instance(
            &mut types,
            resolution,
            binding,
            vec![],
            vec![],
            vec![],
            vec![],
            None,
            None,
        )?;
    }
    let mut entry = None;
    for declared in functions.declared.values() {
        crate::staging::check_generic_quotes(declared.ast, resolution)?;
    }
    let mut staged_generics = Vec::new();
    for (&binding, declared) in &functions.declared {
        let function = declared.ast;
        if declared.impl_template.is_none()
            && !function.generics.is_empty()
            && function.body.as_ref().is_some_and(block_contains_quote)
            && let Some(cases) =
                crate::staging::generic_quotation_cases(function, resolution, MAX_INSTANCES)?
        {
            staged_generics.push((binding, cases));
        }
    }
    if validate_generic_staging {
        for (binding, cases) in staged_generics {
            let arguments: Vec<_> = cases
                .types
                .iter()
                .map(|&id| types.staging_type_parameter(id))
                .collect();
            for effects in cases.effects {
                functions.instance(
                    &mut types,
                    resolution,
                    binding,
                    arguments.clone(),
                    vec![],
                    vec![],
                    effects,
                    None,
                    None,
                )?;
            }
        }
    } else if !staged_generics.is_empty() {
        // Use distinct type identities even when every actual specialization
        // chooses the same type for two parameters. The validation program
        // is discarded before materialization or backend lowering.
        check_program_unstaged(source_program, stage_entries, false, true)?;
    }
    let mut initializers = BTreeMap::new();
    loop {
        let Some(index) = functions.pending.pop() else {
            if initializer_bindings.is_empty() {
                break;
            }
            // An initializer can itself request another staged specialization.
            // Check every newly requested instance before evaluating any of them.
            let pending = functions
                .instances
                .iter()
                .filter_map(|(key, &target)| {
                    let &initializer = initializer_bindings.get(&key.0)?;
                    (!initializers.contains_key(&target))
                        .then(|| (target, initializer, key.clone()))
                })
                .collect::<Vec<_>>();
            if pending.is_empty() {
                break;
            }
            for (target, initializer, (_, type_args, grade_args, const_args, effect_args, _)) in
                pending
            {
                let instance = functions.instance(
                    &mut types,
                    resolution,
                    initializer,
                    type_args,
                    grade_args,
                    const_args,
                    effect_args,
                    None,
                    Some(functions.signatures[target].span),
                )?;
                initializers.insert(target, instance);
            }
            continue;
        };
        if functions.bodies[index].is_some() {
            continue;
        }
        let sig = functions.signatures[index].clone();
        let f = functions.declared[&sig.binding].ast;
        if sig.name == "main" && resolution.unit_of.get(&sig.binding) == Some(&0) {
            if !sig.parameters.is_empty() || !matches!(sig.result, Type::I64 | Type::Unit) {
                return Err(Diagnostic::new(
                    sig.span,
                    "main must have no parameters and return i64 or Unit",
                ));
            }
            if sig.result_grade.is_some() {
                return Err(Diagnostic::new(
                    sig.span,
                    "main cannot carry a result usage contract; its process result has no caller to transfer or erase it",
                ));
            }
            entry = Some(index);
        }
        functions.checking = index;
        // FND-ROWS-INFER: an inferred body is checked with every effect
        // available; what it requires becomes its row.
        let inferring_row = functions.inferred_rows.contains(&sig.binding);
        if !functions.inferred_rows.is_empty() {
            functions.checked_bodies.insert(sig.binding);
        }
        let all_effects = EFFECT_BITS
            | resolution
                .effect_bits
                .values()
                .fold(0u16, |bits, bit| bits | bit);
        let mut checker = Checker {
            inferring_row,
            quote_holes: BTreeMap::new(),
            quote_splices: BTreeMap::new(),
            lambda_holes: BTreeMap::new(),
            lambda_hint: None,
            required_effects: std::cell::Cell::new(0),
            pending_capability: None,
            expanding_constants: Vec::new(),
            writing_bounded_field: false,
            replace_min_length: None,
            body_invariant: None,
            parameter_lengths: BTreeMap::new(),
            refined_use_ok: false,
            lending_spans: BTreeSet::new(),
            abort_labels: 0,
            capability_slots: BTreeSet::new(),
            capability_passable: BTreeSet::new(),
            capability_resumable: BTreeSet::new(),
            capability_framed: BTreeMap::new(),
            capability_parameter_slots: BTreeSet::new(),
            capability_argument: false,
            resolution,
            types: &mut types,
            functions: &mut functions,
            substitution: sig.substitution.clone(),
            consts: sig.consts.clone(),
            grades: sig.grades.clone(),
            effect_arguments: sig.effect_arguments.clone(),
            locals: Vec::new(),
            slots: BTreeMap::new(),
            result: sig.result,
            parameter_lifetimes: sig.parameter_lifetimes.clone(),
            declared_lifetimes: f
                .lifetimes
                .iter()
                .map(|lifetime| lifetime.name.clone())
                .collect(),
            result_lifetime: sig.result_lifetime.clone(),
            lifetime_bounds: sig.lifetime_bounds.clone(),
            call_boundary: 0,
            result_grade: sig.result_grade,
            effects: if inferring_row {
                all_effects
            } else {
                sig.effects
            },
            depth: 0,
            loops: Vec::new(),
            facts: crate::facts::Facts::default(),
            written_slots: BTreeSet::new(),
            closure_writes: BTreeMap::new(),
            closure_captures: BTreeMap::new(),
            proofs: BTreeMap::new(),
            logical: &logical,
            kernel_locals: Vec::new(),
            kernel_types: BTreeMap::new(),
            kernel_proofs: BTreeMap::new(),
            scope_depth: 0,
            scope_parallel: false,
            next_scope_parallel: false,
            next_split: 0,
            self_type: sig.self_type,
            default_trait: sig.default_trait.clone(),
            associated_consts: sig.associated_consts.clone(),
            unit: resolution.unit_of.get(&sig.binding).copied().unwrap_or(0),
            field_place: false,
            binding: sig.binding,
            scalar_epochs: BTreeMap::new(),
            kernel_aliases: BTreeMap::new(),
            scalar_values: BTreeMap::new(),
            proof_values: BTreeMap::new(),
            effect_operations,
            handlers: Vec::new(),
            effect_constraints: Vec::new(),
            unify_plan: Vec::new(),
            unify_decisions: Vec::new(),
            unify_plan_active: false,
            unify_open_choice: false,
            partition_bound: BTreeSet::new(),
            row_bound: BTreeSet::new(),
            hoisted: Vec::new(),
            next_index_place: 0,
            index_relations: BTreeSet::new(),
            pending_lengths: BTreeMap::new(),
            ensures_context: None,
            ensures_tail: false,
            ensures_depth: std::cell::Cell::new(0),
            branch_tail: false,
        };
        let body = (|| {
            let mut runtime = sig.parameters.iter().zip(&sig.parameter_grades);
            let mut ensures_params = Vec::new();
            for p in &f.parameters {
                if p.erased {
                    checker.assume_parameter(p)?;
                } else {
                    let (ty, grade) = runtime.next().unwrap();
                    let slot = checker.bind(p.span, *ty, false)?;
                    ensures_params.push((resolution.binder(p.span).unwrap(), slot));
                    if let Some(length) = &p.min_length {
                        let refined = ty.ref_pointee().is_some_and(|pointer| {
                            matches!(checker.types.pointees[pointer], Type::Vec(_))
                        });
                        let Some(length) = checker.ast_integer(length, 0).filter(|_| refined)
                        else {
                            return Err(Diagnostic::new(
                                p.ty.span,
                                "'where len >= N' on a parameter needs a '&Vec<T>' or '&mut Vec<T>' type and a compile-time N",
                            ));
                        };
                        checker.parameter_lengths.insert(slot, length);
                    }
                    if matches!(split_grade(&p.ty).0.kind, ast::TypeKind::Capability { .. }) {
                        checker.capability_slots.insert(slot);
                        checker.capability_passable.insert(slot);
                        checker.capability_parameter_slots.insert(slot);
                    }
                    checker.locals[slot].grade = *grade;
                    checker.locals[slot].linear =
                        grade.is_some_and(Grade::is_one) && checker.owned_type(*ty);
                    checker.validate_grade(*grade, *ty, p.ty.span, false)?;
                    let id = resolution.binder(p.span).unwrap();
                    checker.admit_scalar_index(id, *ty, p.span)?;
                }
            }
            if !f.ensures.is_empty() {
                for clause in &f.ensures {
                    checker.validate_ensures_calls(&clause.body)?;
                }
                checker.ensures_context = Some(EnsuresContext {
                    clauses: f.ensures.clone(),
                    params: ensures_params,
                    result: sig.result,
                });
                checker.ensures_tail = true;
            }
            let body = checker.block(f.body.as_ref().unwrap(), Some(sig.result))?;
            if body.ty != Type::Never
                && !(sig.result_grade.is_some_and(Grade::is_zero) && body.ty == Type::Unit)
            {
                checker.expect(body.ty, sig.result, sig.span)?;
            }
            if body.ty != Type::Never
                && let Some(tail) = &body.tail
                && checker.observes_copyable_result(tail)
                && !checker.transfers_copyable_result_from(tail)
            {
                return Err(Diagnostic::new(
                    tail.span,
                    "this function returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the result as '@[1]' so every caller inherits exactly one observation, or observe the value inside the function",
                ));
            }
            Ok(body)
        })();
        let body = body.map_err(|mut e: Diagnostic| {
            if let Some((span, text)) = &sig.origin {
                e = e.with_note(
                    *span,
                    format!("in the specialization {text} requested here"),
                );
            }
            e
        })?;
        // A copyable `@[0]` result has no payload at runtime. The value is
        // still computed for effects (and for type checking against the
        // declared result), then erased in the callee. `Drop` is a checked
        // no-op for copyable values; an owning result is rejected by the
        // contract validator before this point.
        let mut body = body;
        if sig.result_grade.is_some_and(Grade::is_zero) && body.ty != Type::Never {
            let span = body.tail.as_deref().map_or(sig.span, |tail| tail.span);
            let tail = body.tail.take().unwrap_or_else(|| {
                Box::new(Expr {
                    kind: ExprKind::Constant(0),
                    ty: Type::Unit,
                    span,
                    resource: None,
                })
            });
            let erased = Expr {
                kind: ExprKind::Drop(tail),
                ty: Type::Unit,
                span,
                resource: None,
            };
            body.tail = Some(Box::new(erased));
            body.ty = Type::Unit;
        }
        let obligation = checker.return_obligation(&body);
        if let Some(span) = obligation
            && sig.result_grade.is_none()
            && !checker.linear_type(sig.result)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' returns a linear obligation through an ungraded result; annotate the result as '-> {} @[1]' so every caller must consume it, or consume the value inside this function",
                    sig.name,
                    checker.types.name(sig.result)
                ),
            ));
        }
        let (local_borrowed, local_copyable) = checker.local_classes(&checker.locals);
        let capability_parameters = (0..sig.parameters.len())
            .filter(|slot| checker.capability_slots.contains(slot))
            .collect();
        let required = checker.required_effects.get() & all_effects;
        let locals = checker.locals;
        functions.bodies[index] = Some(Function {
            name: sig.name.clone(),
            parameters: sig.parameters.len(),
            closure: None,
            capture_refs: vec![],
            capture_writes: vec![],
            locals,
            result: sig.result,
            body,
            span: sig.span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: sig.parameter_grades.clone(),
            result_grade: sig.result_grade,
            parameter_lifetimes: sig.parameter_lifetimes.clone(),
            result_lifetime: sig.result_lifetime.clone(),
            lifetime_bounds: sig.lifetime_bounds.clone(),
            declared_lifetimes: f
                .lifetimes
                .iter()
                .map(|lifetime| lifetime.name.clone())
                .collect(),
            index_relations: checker.index_relations.clone(),
            parameter_slots: None,
            local_borrowed,
            local_copyable,
            capability_parameters,
            shared_environment: false,
        });
        if inferring_row {
            functions.settle_inferred_row(sig.binding, required);
        }
    }
    // Re-check every proof certificate without the search that produced it.
    if let Some(bad) = functions
        .certificates
        .iter()
        .find(|c| !crate::facts::verify(c))
    {
        return Err(Diagnostic::new(
            bad.span,
            format!(
                "internal error: proof certificate for '{}' failed independent checking",
                bad.obligation
            ),
        ));
    }
    // Fusion selection runs only after every body exists, so it can inspect
    // callee effect rows and structural termination instead of guessing from
    // source types while bodies are still being checked.
    let automatic = automatic_fusion(&types, &mut functions);
    functions.fusions += automatic;
    if !validate_generic_staging && std::env::var_os("KUSH_PROOF_REPORT").is_some() {
        eprintln!(
            "proof report: {} element accesses proved in bounds (no runtime check), {} checked at run time",
            functions.bounds_proved, functions.bounds_checked
        );
        if std::env::var("KUSH_PROOF_REPORT").as_deref() == Ok("verbose") {
            for line in obligation_report(&program.sources, functions.obligations.values()) {
                eprintln!("  {line}");
            }
        }
    }
    let mut foreign_functions = vec![None; functions.bodies.len()];
    for (index, foreign) in functions.foreign_functions {
        foreign_functions[index] = Some(foreign);
    }
    let exports = checked_exports(
        &functions.signatures,
        &functions.declared,
        resolution,
        &types,
    )?;
    let gpu_functions = functions
        .signatures
        .iter()
        .map(|signature| functions.gpu.contains(&signature.binding))
        .collect();
    // PANIC-LINEAR-CLEANUP: `#[linear(unwind = f)]`, by record layout: the
    // function in the type's module run on a live value while a panic
    // unwinds past it. It takes the value by move and returns Unit.
    let mut unwind_functions = BTreeMap::new();
    for (layout, record) in types.enums.iter().enumerate() {
        let Some((name, span)) = types.unwind_names.get(&record.definition) else {
            continue;
        };
        let unit = resolution.unit_of.get(&record.definition).copied();
        let found = functions.signatures.iter().position(|signature| {
            signature.name == *name
                && resolution.unit_of.get(&signature.binding).copied() == unit
                && functions
                    .declared
                    .get(&signature.binding)
                    .is_some_and(|declared| declared.self_ty.is_none())
        });
        let Some(index) = found else {
            return Err(Diagnostic::new(
                *span,
                format!("#[linear(unwind = {name})] names no function '{name}' in this module"),
            ));
        };
        let signature = &functions.signatures[index];
        if signature.parameters != [Type::Enum(layout)] || signature.result != Type::Unit {
            return Err(Diagnostic::new(
                *span,
                format!(
                    "the unwind cleanup '{name}' must take the {} by value and return Unit",
                    resolution.bindings[record.definition].name
                ),
            ));
        }
        unwind_functions.insert(layout, index);
    }
    let simd_functions = functions
        .signatures
        .iter()
        .map(|signature| {
            let binding = signature.binding;
            let unit = *resolution.unit_of.get(&binding)?;
            let path = resolution.units.get(unit)?;
            // The root unit is never std (the loader also rejects a root
            // under `std`).
            if unit == 0 || path.len() != 2 || path[0] != "std" {
                return None;
            }
            let declared = functions.declared.get(&binding)?;
            // SIMD-X86-SHA: the intrinsics of std.x86, by function name.
            if path[1] == "x86" && declared.self_ty.is_none() {
                return Some(("x86".to_owned(), declared.ast.name.clone()));
            }
            if path[1] != "simd" {
                return None;
            }
            let layout = declared.self_ty?.layout()?;
            let ty = resolution.bindings[types.enums[layout].definition]
                .name
                .clone();
            Some((ty, declared.ast.name.clone()))
        })
        .collect();
    let mut executable = Executable {
        stage_templates: functions.stage_templates,
        gpu_functions,
        simd_functions,
        unwind_functions,
        eval_fuel: crate::eval::DEFAULT_EVAL_FUEL,
        _grade_algebras: resolution.lowered_algebras.values().cloned().collect(),
        fusions: functions.fusions,
        bounds_proved: functions.bounds_proved,
        bounds_checked: functions.bounds_checked,
        obligations: sorted_obligations(&functions.obligations),
        discharged: sorted_obligations(&functions.discharged),
        uses_tasks: functions.uses_tasks,
        uses_unwinding: functions.uses_unwinding,
        main_stack,
        // A channel type anywhere needs the threaded runtime (its drop glue).
        uses_threads: functions.uses_threads
            || types
                .pointees
                .iter()
                .any(|ty| matches!(ty, Type::Channel(_)))
            || types.enums.iter().any(|layout| {
                layout
                    .variants
                    .iter()
                    .any(|variant| variant.fields.iter().any(|f| matches!(f, Type::Channel(_))))
            }),
        effect_bits,
        abortive_operations,
        certificates: functions.certificates,
        allocator_contexts: functions.allocator_contexts,
        functions: functions.bodies.into_iter().map(Option::unwrap).collect(),
        entry,
        enums: types.enums,
        pointees: types.pointees,
        unions: types.unions,
        function_types: types.function_types,
        dyn_object_names: types
            .objects
            .iter()
            .map(|object| object.name.clone())
            .collect(),
        // An object type that never had a member coerced into it still has
        // an (empty) member table, so every backend can index it.
        dyn_members: {
            let mut members = functions.dyn_members;
            members.resize_with(types.objects.len().max(members.len()), Vec::new);
            members
        },
        dyn_calls: functions.dyn_calls,
        union_calls: functions.union_calls,
        reference_labels: types.reference_labels,
        variance: types.variance,
        owned_enums: vec![],
        linear_enums: vec![],
        foreign_functions,
        exports,
        logical_definitions: logical.definitions.clone(),
    };
    crate::gpu::check(&executable)?;
    crate::multishot::check(&executable)?;
    crate::suspend::mark_abort_calls(&mut executable)?;
    crate::ownership::check(&mut executable)?;
    crate::grades::check(&executable)?;
    if lower_suspensions {
        crate::suspend::lower(&mut executable)?;
    }
    Ok((executable, initializers))
}
/// A span-insensitive key for the simple expression forms admitted in erased
/// predicate parameters. Unsupported compound forms fall back to their debug
/// form: that can only reject a contract, never accept two different ones.
fn expr_key(expr: &ast::Expr) -> String {
    use ast::ExprKind as E;
    match &expr.kind {
        E::Name(name) => name.clone(),
        E::Integer(value) | E::Float(value) => value.clone(),
        E::String(value) => format!("{value:?}"),
        E::Char(value) => format!("'{value}'"),
        E::Bool(value) => value.to_string(),
        E::Handle { .. } | E::Perform { .. } => format!("{:?}", expr.kind),
        E::Tuple(items) => format!(
            "({})",
            items.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Array(items) => format!(
            "[{}]",
            items.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Unary {
            op,
            mutable,
            operand,
        } => format!(
            "{op:?}{}{}",
            if *mutable { " mut" } else { "" },
            expr_key(operand)
        ),
        E::Binary { op, left, right } => {
            format!("({op:?} {} {})", expr_key(left), expr_key(right))
        }
        E::Call { callee, arguments } => format!(
            "{}({})",
            expr_key(callee),
            arguments.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Specialize { callee, arguments } => format!(
            "{}::<{}>",
            expr_key(callee),
            arguments.iter().map(type_key).collect::<Vec<_>>().join(",")
        ),
        E::Field { value, name } => format!("{}.{name}", expr_key(value)),
        E::Cast { value, ty } => format!("({} as {})", expr_key(value), type_key(ty)),
        E::Is { value, variant } => format!("({} is {variant})", expr_key(value)),
        E::Index { value, index } => format!("{}[{}]", expr_key(value), expr_key(index)),
        E::Slice { value, start, end } => format!(
            "{}[{}..{}]",
            expr_key(value),
            start.as_deref().map(expr_key).unwrap_or_default(),
            end.as_deref().map(expr_key).unwrap_or_default()
        ),
        E::Try(value) => format!("{}?", expr_key(value)),
        E::Return(Some(value)) => format!("return {}", expr_key(value)),
        E::Return(None) => "return".to_owned(),
        E::Break(Some(value)) => format!("break {}", expr_key(value)),
        E::Break(None) => "break".to_owned(),
        E::Continue => "continue".to_owned(),
        E::Block(_)
        | E::Lambda(_)
        | E::If { .. }
        | E::Match { .. }
        | E::Record { .. }
        | E::StructuralLiteral(_)
        | E::While { .. }
        | E::Loop(_) => format!("{expr:?}"),
    }
}
/// Split a checked projection chain into its root reference expression and the
/// combined word offset from the record tag. Used only for field assignments
/// through `&mut Record`; reads use the ordinary `Project` expression.
/// A field place of a record held directly in a local (not behind a
/// reference): the local and the field's word offset.
fn split_local_projection(expr: &Expr) -> Option<(usize, usize)> {
    let ExprKind::Project(base, offset) = &expr.kind else {
        return None;
    };
    match &base.kind {
        ExprKind::Peek(slot) | ExprKind::Local(slot) if !base.ty.is_ref() => Some((*slot, *offset)),
        ExprKind::Project(..) => {
            let (slot, inner) = split_local_projection(base)?;
            Some((slot, inner + offset))
        }
        _ => None,
    }
}
fn split_reference_projection(expr: Expr) -> Option<(Expr, usize)> {
    let ExprKind::Project(base, offset) = expr.kind else {
        return None;
    };
    let base = *base;
    if base.ty.is_ref() {
        return Some((base, offset));
    }
    let (root, inner) = split_reference_projection(base)?;
    Some((root, inner + offset))
}
/// Outcome of a speculative unification; see `Checker::unify_trial`.
struct UnifyTrial<R> {
    result: Result<R>,
    /// A nested partition or indexed assignment took the first of several
    /// choices, so a failure does not rule the trial out.
    nested_choice: bool,
    effects: Vec<(crate::runtime_types::EffectRowTerm, u16)>,
}
/// Identity of a verified indexed-union assignment: its substitution, effect
/// evidence, and the members of bare variables a trial left unbound.
type IndexedSolutionKey = (
    crate::runtime_types::Subst,
    Vec<(crate::runtime_types::EffectRowTerm, u16)>,
    Vec<Vec<Type>>,
);
/// One surviving plan of the cross-parameter search.
struct ReplaySolution {
    subst: crate::runtime_types::Subst,
    /// The effect-row evidence this plan produced.
    effects: Vec<EffectConstraint>,
    /// Whether the plan passes the call's subtype checks, not only matching.
    valid: bool,
}
/// Whether two inference solutions bind every type and natural variable the
/// same way.
fn same_solution(
    left: &crate::runtime_types::Subst,
    right: &crate::runtime_types::Subst,
    type_vars: &[BindingId],
    const_vars: &[BindingId],
) -> bool {
    type_vars
        .iter()
        .all(|var| left.types.get(var) == right.types.get(var))
        && const_vars
            .iter()
            .all(|var| left.consts.get(var) == right.consts.get(var))
}
/// Layout budget exhaustion is a resource limit, never evidence against one
/// inference choice.
fn is_layout_budget_error(error: &Diagnostic) -> bool {
    error.message.contains("layout budget exhausted")
}
/// Spell a declared type for diagnostics, writing unions with `|`.
fn union_pattern_spelling(ty: &ast::Type) -> String {
    match &ty.kind {
        ast::TypeKind::Binary {
            op: crate::lexer::Kind::Pipe,
            left,
            right,
        } => format!(
            "{} | {}",
            union_pattern_spelling(left),
            union_pattern_spelling(right)
        ),
        ast::TypeKind::Named { path, arguments } if !arguments.is_empty() => format!(
            "{}<{}>",
            path.join("."),
            arguments
                .iter()
                .map(union_pattern_spelling)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ast::TypeKind::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(union_pattern_spelling)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ast::TypeKind::Array(inner, length) => format!(
            "[{}; {}]",
            union_pattern_spelling(inner),
            union_pattern_spelling(length)
        ),
        _ => type_key(ty),
    }
}
/// A span-insensitive canonical spelling of a declared type. Used only to
/// compare trait method contracts with their impls; it deliberately treats
/// `Self` as one stable placeholder because both sides must spell it the same
/// way.
fn type_key(ty: &ast::Type) -> String {
    match &ty.kind {
        ast::TypeKind::Named { path, arguments } => {
            let mut text = path.join(".");
            if !arguments.is_empty() {
                text.push('<');
                text.push_str(&arguments.iter().map(type_key).collect::<Vec<_>>().join(","));
                text.push('>');
            }
            text
        }
        ast::TypeKind::Dyn(bounds) => format!(
            "dyn {}",
            bounds
                .iter()
                .map(|bound| {
                    let mut text = type_key(&bound.trait_ref);
                    for (name, value) in &bound.bindings {
                        text.push_str(&format!("[{name}={}]", type_key(value)));
                    }
                    text
                })
                .collect::<Vec<_>>()
                .join(" + ")
        ),
        ast::TypeKind::Structural { fields, row, .. } => {
            let mut fields = fields
                .iter()
                .map(|field| (field.name.clone(), field.ty.clone()))
                .collect::<Vec<_>>();
            fields.sort_by(|left, right| left.0.cmp(&right.0));
            let tail = row
                .as_ref()
                .map(|row| format!(", ..{}", type_key(row)))
                .unwrap_or_default();
            format!(
                "struct{{{}{tail}}}",
                fields
                    .iter()
                    .map(|(name, ty)| format!("{name}:{}", type_key(ty)))
                    .collect::<Vec<_>>()
                    .join(","),
            )
        }
        ast::TypeKind::Integer(value) => value.clone(),
        ast::TypeKind::Bool(value) => format!("bool:{value}"),
        ast::TypeKind::Tuple(items) => {
            format!(
                "({})",
                items.iter().map(type_key).collect::<Vec<_>>().join(",")
            )
        }
        ast::TypeKind::Slice(inner) => format!("[{}]", type_key(inner)),
        ast::TypeKind::Array(inner, length) => {
            format!("[{};{}]", type_key(inner), type_key(length))
        }
        ast::TypeKind::Borrow {
            lifetime,
            mutable,
            inner,
        } => format!(
            "&{}{}{}",
            lifetime
                .as_ref()
                .map(|lifetime| format!("'{lifetime} "))
                .unwrap_or_default(),
            if *mutable { "mut " } else { "" },
            type_key(inner)
        ),
        ast::TypeKind::Lifetime(name) => format!("'{name}"),
        ast::TypeKind::SelfType => "Self".to_owned(),
        ast::TypeKind::Infer => "_".to_owned(),
        ast::TypeKind::Capability {
            operation,
            effects,
            multi,
        } => format!(
            "cap {}{operation} ! {{{}}}",
            if *multi { "multi " } else { "" },
            effects.iter().map(type_key).collect::<Vec<_>>().join(", ")
        ),
        ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
            call_multi,
        } => {
            let lifetimes = lifetimes
                .iter()
                .map(|lifetime| {
                    let mut text = lifetime.name.clone();
                    for bound in &lifetime.bounds {
                        text.push_str(&format!(":{}", bound.name));
                    }
                    text
                })
                .collect::<Vec<_>>()
                .join(",");
            let mut effects = effects.iter().map(type_key).collect::<Vec<_>>();
            effects.sort();
            effects.dedup();
            let effects = effects.join(",");
            format!(
                "{}fn<{lifetimes}>({})->{} ! {{ {effects} }}",
                if *call_linear {
                    "linear "
                } else if *call_once {
                    "once "
                } else if *call_multi {
                    "multi "
                } else {
                    ""
                },
                parameters
                    .iter()
                    .map(|parameter| type_key(&parameter.ty))
                    .collect::<Vec<_>>()
                    .join(","),
                type_key(result),
            )
        }
        ast::TypeKind::Binary { op, left, right } => {
            format!("{} {op:?} {}", type_key(left), type_key(right))
        }
        ast::TypeKind::Graded { inner, grade } => {
            format!("{} @[{}]", type_key(inner), type_key(grade))
        }
        ast::TypeKind::Predicate(expr) => format!("<predicate {}>", expr_key(expr)),
    }
}
/// Capture-avoiding alpha-normalization of one method signature for exact
/// trait/impl contract comparison.
///
/// Method generic parameters are renamed to unspellable canonical tokens first,
/// then `Self` and the trait's generic parameters are substituted. Trait
/// arguments are closed types (generic impls are rejected), so the substituted
/// text cannot be captured by a method binder. Parameter names stay part of
/// the contract because erased propositions may name earlier parameters.
struct ContractNames {
    types: BTreeMap<String, String>,
    lifetimes: BTreeMap<String, String>,
    self_ty: Option<ast::Type>,
    /// Trait parameter name -> concrete impl argument, applied after alpha
    /// renaming so a global type name cannot capture a method binder.
    trait_arguments: BTreeMap<String, ast::Type>,
    /// Associated type name -> impl-supplied value. Both the trait signature
    /// and the impl signature normalize `Self::Name` through this map, so the
    /// exact comparison sees the same type on both sides.
    associated_types: BTreeMap<String, ast::Type>,
}
impl ContractNames {
    fn new(
        resolution: &Resolution,
        function: &ast::Function,
        self_ty: Option<&ast::Type>,
        trait_arguments: Option<&BTreeMap<String, ast::Type>>,
        associated_types: Option<&BTreeMap<String, ast::Type>>,
    ) -> Self {
        let mut types = BTreeMap::new();
        for (index, generic) in function.generics.iter().enumerate() {
            let prefix = match generic_category(resolution, generic) {
                GenericCategory::Type => "T",
                GenericCategory::Const => "N",
                GenericCategory::Grade => "G",
                GenericCategory::Effect => "E",
            };
            types.insert(generic.name.clone(), format!("${prefix}{index}"));
        }
        let lifetimes = function
            .lifetimes
            .iter()
            .enumerate()
            .map(|(index, lifetime)| (lifetime.name.clone(), format!("$L{index}")))
            .collect();
        Self {
            types,
            lifetimes,
            self_ty: self_ty.cloned(),
            trait_arguments: trait_arguments.cloned().unwrap_or_default(),
            associated_types: associated_types.cloned().unwrap_or_default(),
        }
    }
    fn name(&self, name: &str) -> Option<ast::Type> {
        if let Some(token) = self.types.get(name) {
            return Some(ast::Type::new(
                ast::TypeKind::Named {
                    path: vec![token.clone()],
                    arguments: Vec::new(),
                },
                Span::default(),
            ));
        }
        self.trait_arguments.get(name).cloned()
    }
    fn ty(&self, ty: &ast::Type) -> ast::Type {
        let kind = match &ty.kind {
            ast::TypeKind::Named { path, arguments } => {
                if arguments.is_empty()
                    && path.len() == 1
                    && let Some(replacement) = self.name(&path[0])
                {
                    return replacement;
                }
                if arguments.is_empty()
                    && path.len() == 2
                    && path[0] == "Self"
                    && let Some(value) = self.associated_types.get(&path[1])
                {
                    return self.ty(value);
                }
                ast::TypeKind::Named {
                    path: path.clone(),
                    arguments: arguments.iter().map(|argument| self.ty(argument)).collect(),
                }
            }
            ast::TypeKind::Infer => ast::TypeKind::Infer,
            ast::TypeKind::Capability {
                operation,
                effects,
                multi,
            } => ast::TypeKind::Capability {
                operation: operation.clone(),
                effects: effects.iter().map(|effect| self.ty(effect)).collect(),
                multi: *multi,
            },
            ast::TypeKind::SelfType => {
                if let Some(self_ty) = &self.self_ty {
                    return self_ty.clone();
                }
                ast::TypeKind::SelfType
            }
            ast::TypeKind::Dyn(bounds) => ast::TypeKind::Dyn(
                bounds
                    .iter()
                    .map(|bound| ast::DynBound {
                        trait_ref: self.ty(&bound.trait_ref),
                        bindings: bound
                            .bindings
                            .iter()
                            .map(|(name, value)| (name.clone(), self.ty(value)))
                            .collect(),
                    })
                    .collect(),
            ),
            ast::TypeKind::Lifetime(name) => ast::TypeKind::Lifetime(self.lifetime(name)),
            ast::TypeKind::Borrow {
                lifetime,
                mutable,
                inner,
            } => ast::TypeKind::Borrow {
                lifetime: lifetime.as_deref().map(|name| self.lifetime(name)),
                mutable: *mutable,
                inner: Box::new(self.ty(inner)),
            },
            ast::TypeKind::Tuple(items) => {
                ast::TypeKind::Tuple(items.iter().map(|item| self.ty(item)).collect())
            }
            ast::TypeKind::Structural { fields, open, row } => ast::TypeKind::Structural {
                fields: fields
                    .iter()
                    .map(|field| ast::Field {
                        name: field.name.clone(),
                        source: field.source.clone(),
                        ty: self.ty(&field.ty),
                        span: field.span,
                        public: field.public,
                        min_length: None,
                    })
                    .collect(),
                open: *open,
                row: row.as_ref().map(|row| Box::new(self.ty(row))),
            },
            ast::TypeKind::Slice(inner) => ast::TypeKind::Slice(Box::new(self.ty(inner))),
            ast::TypeKind::Array(inner, length) => {
                ast::TypeKind::Array(Box::new(self.ty(inner)), Box::new(self.ty(length)))
            }
            ast::TypeKind::Binary { op, left, right } => ast::TypeKind::Binary {
                op: op.clone(),
                left: Box::new(self.ty(left)),
                right: Box::new(self.ty(right)),
            },
            ast::TypeKind::Graded { inner, grade } => ast::TypeKind::Graded {
                inner: Box::new(self.ty(inner)),
                grade: Box::new(self.ty(grade)),
            },
            ast::TypeKind::Function {
                lifetimes,
                parameters,
                result,
                effects,
                call_once,
                call_linear,
                call_multi,
            } => ast::TypeKind::Function {
                lifetimes: lifetimes
                    .iter()
                    .map(|lifetime| ast::Lifetime {
                        name: self.lifetime(&lifetime.name),
                        span: lifetime.span,
                        bounds: lifetime
                            .bounds
                            .iter()
                            .map(|bound| ast::LifetimeBound {
                                name: self.lifetime(&bound.name),
                                span: bound.span,
                            })
                            .collect(),
                    })
                    .collect(),
                parameters: parameters
                    .iter()
                    .map(|parameter| ast::TypeParameter {
                        name: parameter.name.clone(),
                        ty: self.ty(&parameter.ty),
                        span: parameter.span,
                    })
                    .collect(),
                result: Box::new(self.ty(result)),
                effects: effects.iter().map(|effect| self.ty(effect)).collect(),
                call_once: *call_once,
                call_linear: *call_linear,
                call_multi: *call_multi,
            },
            ast::TypeKind::Integer(value) => ast::TypeKind::Integer(value.clone()),
            ast::TypeKind::Bool(value) => ast::TypeKind::Bool(*value),
            ast::TypeKind::Predicate(expression) => ast::TypeKind::Predicate(expression.clone()),
        };
        ast::Type::new(kind, ty.span)
    }
    fn lifetime(&self, name: &str) -> String {
        self.lifetimes
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    }
}
/// The conservative exact method contract after alpha-renaming method
/// parameters and substituting `Self` and trait arguments: generic categories
/// and bounds, effect-exclusion sets, lifetimes, parameter names/types, erasure
/// markers, result type, and the effect row (order-insensitive).
fn method_contract_key(
    resolution: &Resolution,
    function: &ast::Function,
    self_ty: Option<&ast::Type>,
    trait_arguments: Option<&BTreeMap<String, ast::Type>>,
    associated_types: Option<&BTreeMap<String, ast::Type>>,
) -> Result<String> {
    let names = ContractNames::new(
        resolution,
        function,
        self_ty,
        trait_arguments,
        associated_types,
    );
    let mut lifetimes = String::new();
    for lifetime in &function.lifetimes {
        lifetimes.push_str(&names.lifetime(&lifetime.name));
        for bound in &lifetime.bounds {
            lifetimes.push_str(&format!(":{}", names.lifetime(&bound.name)));
        }
        lifetimes.push(',');
    }
    let mut generics = String::new();
    for generic in &function.generics {
        let category = generic_category(resolution, generic);
        generics.push_str(&format!("${category:?}"));
        if let Some(bound) = &generic.bound {
            generics.push_str(&format!(": {}", type_key(&names.ty(bound))));
        }
        // Compare the canonical concrete set, so a trait and impl that spell
        // the same union in a different order remain alpha-equivalent while a
        // stricter or looser implementation still differs.
        if let Some(included) = crate::runtime_types::effect_includes(resolution, generic)? {
            generics.push_str(&format!(" + {included:#b}"));
        }
        if let Some(excluded) = crate::runtime_types::effect_excludes(resolution, generic)? {
            generics.push_str(&format!(" - {excluded:#b}"));
        }
        generics.push(',');
    }
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            format!(
                "{}{}: {}",
                if parameter.erased { "erased " } else { "" },
                parameter.name,
                type_key(&names.ty(&parameter.ty))
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let mut effects = function
        .effects
        .iter()
        .map(|effect| type_key(&names.ty(effect)))
        .collect::<Vec<_>>();
    effects.sort();
    effects.dedup();
    Ok(format!(
        "generics=<{generics}> <{lifetimes}>({parameters}) -> {} ! {{{}}}",
        type_key(&names.ty(&function.result)),
        effects.join(", ")
    ))
}
/// Evaluate concrete trait-specialization arguments in a declaration order that
/// mirrors function instance keys. Trait arguments are static identity, never
/// runtime values.
#[allow(clippy::too_many_arguments)]
pub(crate) fn evaluate_trait_arguments(
    types: &mut Types<'_>,
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    generics: &[ast::Generic],
    arguments: &[ast::Type],
    substitution: &crate::runtime_types::Subst,
    trait_name: &str,
    span: Span,
) -> Result<TraitArguments> {
    if generics.len() != arguments.len() {
        return Err(Diagnostic::new(
            span,
            format!(
                "trait '{trait_name}' expects {} argument(s), found {}",
                generics.len(),
                arguments.len()
            ),
        ));
    }
    let mut out = TraitArguments::default();
    for (generic, argument) in generics.iter().zip(arguments) {
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let ty = types.ty_in(argument, substitution)?;
                let ty = types.full(ty, argument.span)?;
                if crate::runtime_types::has_borrow(types, ty) {
                    return Err(Diagnostic::new(
                        argument.span,
                        format!(
                            "trait argument for '{}' cannot be a borrowed type; references are call-scoped and cannot be erased through a generic trait parameter",
                            generic.name
                        ),
                    ));
                }
                out.types.push(ty);
            }
            GenericCategory::Const => out.consts.push(crate::length::eval_type(
                resolution,
                logical,
                &substitution.consts,
                argument,
            )?),
            GenericCategory::Grade => out.grades.push(crate::grades::evaluate(
                resolution,
                &substitution.grades,
                argument,
            )?),
            GenericCategory::Effect => out.effects.push(crate::runtime_types::effect_bits_with(
                resolution,
                std::slice::from_ref(argument),
                &substitution.effects,
            )?),
        }
    }
    Ok(out)
}
/// Seed one specialization substitution with a trait's concrete arguments for a
/// materialized default method. Trait parameters are classified exactly like
/// function generics, and their declaration order matches the argument vectors
/// produced by [`evaluate_trait_arguments`].
fn insert_trait_arguments(
    resolution: &Resolution,
    generics: &[ast::Generic],
    arguments: &TraitArguments,
    substitution: &mut crate::runtime_types::Subst,
    consts: &mut BTreeMap<BindingId, usize>,
    grades: &mut BTreeMap<BindingId, Grade>,
    effects: &mut BTreeMap<BindingId, u16>,
) {
    let mut types = arguments.types.iter();
    let mut const_values = arguments.consts.iter();
    let mut grade_values = arguments.grades.iter();
    let mut effect_values = arguments.effects.iter();
    for generic in generics {
        let Some(binder) = resolution.binder(generic.span) else {
            continue;
        };
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                if let Some(ty) = types.next() {
                    substitution.types.insert(binder, *ty);
                }
            }
            GenericCategory::Const => {
                if let Some(value) = const_values.next() {
                    consts.insert(binder, *value);
                }
            }
            GenericCategory::Grade => {
                if let Some(grade) = grade_values.next() {
                    grades.insert(binder, *grade);
                }
            }
            GenericCategory::Effect => {
                if let Some(bits) = effect_values.next() {
                    effects.insert(binder, *bits);
                }
            }
        }
    }
}
/// Render one trait specialization for diagnostics, in declared parameter order.
pub(crate) fn trait_specialization_name(
    resolution: &Resolution,
    types: &Types<'_>,
    generics: &[ast::Generic],
    arguments: &TraitArguments,
) -> String {
    let mut type_index = 0;
    let mut const_index = 0;
    let mut grade_index = 0;
    let mut effect_index = 0;
    let mut parts = Vec::new();
    for generic in generics {
        let part = match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let ty = arguments.types[type_index];
                type_index += 1;
                types.name(ty)
            }
            GenericCategory::Const => {
                let value = arguments.consts[const_index];
                const_index += 1;
                value.to_string()
            }
            GenericCategory::Grade => {
                let grade = arguments.grades[grade_index];
                grade_index += 1;
                grade.to_string()
            }
            GenericCategory::Effect => {
                let row = arguments.effects[effect_index];
                effect_index += 1;
                let names = crate::runtime_types::effect_name_list(resolution, row);
                if names.is_empty() {
                    "{}".to_owned()
                } else {
                    format!("{{{}}}", names.join(", "))
                }
            }
        };
        parts.push(part);
    }
    parts.join(", ")
}
/// A trait receiver is owned `Self` or a single shared/exclusive borrow of
/// `Self`. Lifetimes on the borrow are erased contract metadata and remain
/// part of the exact signature comparison.
/// One destructured level of a consumed projected field: the hidden binding
/// (or root local) matched, its aggregate type, and the binding pattern.
type ConsumedLevel = (usize, Type, Pattern);
/// Put the destructuring levels built by `consume_object_field` around a
/// consuming call, outermost aggregate first.
fn wrap_consumed_field(levels: Vec<ConsumedLevel>, call: Expr) -> Expr {
    let span = call.span;
    levels
        .into_iter()
        .rev()
        .fold(call, |body, (scrutinee, ty, pattern)| {
            let result = body.ty;
            Expr {
                kind: ExprKind::Match(
                    Box::new(Expr {
                        kind: ExprKind::Local(scrutinee),
                        ty,
                        span,
                        resource: None,
                    }),
                    vec![Arm {
                        pattern,
                        guard: None,
                        body,
                    }],
                ),
                ty: result,
                span,
                resource: None,
            }
        })
}
fn valid_trait_receiver(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Borrow { inner, .. } => matches!(inner.kind, ast::TypeKind::SelfType),
        _ => false,
    }
}
/// Check one method receiver against the concrete impl target and return the
/// runtime receiver type. Owned receivers are the target by value; borrowed
/// receivers are `&Target`/`&mut Target` and are limited to nominal records,
/// with no exclusive borrow of a record that already has borrowed fields.
fn checked_method_receiver(
    types: &mut Types<'_>,
    receiver_ty: &ast::Type,
    self_key: Type,
) -> Result<Type> {
    let subst = crate::runtime_types::Subst {
        self_type: Some(self_key),
        ..Default::default()
    };
    let expected_receiver = match &receiver_ty.kind {
        ast::TypeKind::Borrow { mutable, .. } => {
            if self_key.layout().is_none() || !types.enums[self_key.layout().unwrap()].record {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "borrowed receivers are supported only for nominal record targets in this subset",
                ));
            }
            let inner = match &receiver_ty.kind {
                ast::TypeKind::Borrow { inner, .. } => inner,
                _ => unreachable!(),
            };
            if types.ty_in(inner, &subst)? != self_key {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "a borrowed method receiver must borrow the impl target type, as in 'self: &Self' or 'self: &mut Self'",
                ));
            }
            if *mutable && types.enums[self_key.layout().unwrap()].borrowed {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "an exclusive '&mut self' receiver is not supported for a record with borrowed fields; borrow it shared, or update through an owning value",
                ));
            }
            if *mutable {
                Type::RefMut(types.pointer(self_key))
            } else {
                Type::Ref(types.pointer(self_key))
            }
        }
        _ => self_key,
    };
    let receiver_type = types.ty_in(receiver_ty, &subst)?;
    if receiver_type != expected_receiver {
        return Err(Diagnostic::new(
            receiver_ty.span,
            "a method receiver must borrow the impl target type exactly, as in '&Self' or '&mut Self', or be the target type by value",
        ));
    }
    Ok(expected_receiver)
}
/// Whether a reference parameter reaches `target` either directly or through
/// inline nominal-record fields. A returned `&Field` may borrow caller-owned
/// storage named by a `&Record` parameter; the ownership pass still proves the
/// exact origin is that parameter. Exclusive results require an exclusive
/// reference parameter.
fn reference_reaches_type(types: &Types<'_>, ty: Type, target: Type, mutable: bool) -> bool {
    fn contains(types: &Types<'_>, ty: Type, target: Type, depth: usize) -> bool {
        if ty.full() == target.full() {
            return true;
        }
        if depth >= 16 {
            return false;
        }
        let Some(id) = ty.layout().filter(|id| types.enums[*id].record) else {
            return false;
        };
        types.enums[id].variants[0]
            .fields
            .iter()
            .any(|field| contains(types, *field, target, depth + 1))
    }
    // A slice view parameter backs a reference to one of its elements (or a
    // field inside one): `&s[i]` borrows the caller's storage behind `s`.
    let (Type::Ref(pointer)
    | Type::RefMut(pointer)
    | Type::Slice(pointer)
    | Type::SliceMut(pointer)) = ty
    else {
        return false;
    };
    if mutable && !matches!(ty, Type::RefMut(_) | Type::SliceMut(_)) {
        return false;
    }
    contains(types, types.pointees[pointer], target, 0)
}
/// Collect every `Self::Name` projection mentioned by a type. Used to validate
/// associated type defaults and reject cyclic default chains before lowering.
fn type_self_associations(ty: &ast::Type, out: &mut BTreeSet<String>) {
    match &ty.kind {
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2 && path[0] == "Self" {
                out.insert(path[1].clone());
            }
            for argument in arguments {
                type_self_associations(argument, out);
            }
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                type_self_associations(item, out);
            }
        }
        ast::TypeKind::Structural { fields, row, .. } => {
            for field in fields {
                type_self_associations(&field.ty, out);
            }
            if let Some(row) = row {
                type_self_associations(row, out);
            }
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Borrow { inner, .. } => type_self_associations(inner, out),
        ast::TypeKind::Dyn(bounds) => {
            for inner in ast::dyn_types(bounds) {
                type_self_associations(inner, out);
            }
        }
        ast::TypeKind::Array(inner, length) => {
            type_self_associations(inner, out);
            type_self_associations(length, out);
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_self_associations(left, out);
            type_self_associations(right, out);
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                type_self_associations(&parameter.ty, out);
            }
            type_self_associations(result, out);
            for effect in effects {
                type_self_associations(effect, out);
            }
        }
        ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. }
        | ast::TypeKind::Predicate(_) => {}
    }
}

/// Validate an associated type default graph: every `Self::Name` must name a
/// declared associated type, and no default may depend on itself directly or
/// transitively. A cycle has no finite lowered representation, so it is
/// rejected at the trait declaration instead of surfacing as a depth error at
/// an arbitrary use site.
fn validate_associated_type_defaults(associated: &[ast::Associated]) -> Result<()> {
    let declared = associated
        .iter()
        .filter_map(|item| match item {
            ast::Associated::Type { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut defaults: BTreeMap<String, (ast::Type, Span)> = BTreeMap::new();
    for item in associated {
        let ast::Associated::Type {
            name,
            value: Some(default),
            span,
        } = item
        else {
            continue;
        };
        let mut references = BTreeSet::new();
        type_self_associations(default, &mut references);
        for reference in &references {
            if !declared.contains(reference) {
                return Err(Diagnostic::new(
                    default.span,
                    format!(
                        "associated type default references 'Self::{reference}', which is not a declared associated type"
                    ),
                ));
            }
        }
        defaults.insert(name.clone(), (default.clone(), *span));
    }
    // Depth-first search with an explicit color map: 1 = on the current path,
    // 2 = finished. A back edge names the cycle.
    let mut color: BTreeMap<String, u8> = BTreeMap::new();
    fn visit(
        name: &str,
        defaults: &BTreeMap<String, (ast::Type, Span)>,
        color: &mut BTreeMap<String, u8>,
        path: &mut Vec<String>,
    ) -> Result<()> {
        match color.get(name).copied().unwrap_or(0) {
            2 => return Ok(()),
            1 => {
                let start = path.iter().position(|item| item == name).unwrap_or(0);
                let mut cycle = path[start..].to_vec();
                cycle.push(name.to_owned());
                let (_, span) = defaults.get(name).expect("cycle node has a default");
                return Err(Diagnostic::new(
                    *span,
                    format!(
                        "associated type default cycle: {}; each default must resolve to a finite type",
                        cycle.join(" -> ")
                    ),
                ));
            }
            _ => {}
        }
        let Some((default, _)) = defaults.get(name) else {
            return Ok(());
        };
        color.insert(name.to_owned(), 1);
        path.push(name.to_owned());
        let mut references = BTreeSet::new();
        type_self_associations(default, &mut references);
        for reference in references {
            visit(&reference, defaults, color, path)?;
        }
        path.pop();
        color.insert(name.to_owned(), 2);
        Ok(())
    }
    for name in defaults.keys() {
        visit(name, &defaults, &mut color, &mut Vec::new())?;
    }
    Ok(())
}
fn type_mentions_self(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Infer | ast::TypeKind::Capability { .. } => false,
        ast::TypeKind::Named { path, arguments } => {
            path.first().is_some_and(|name| name == "Self")
                || arguments.iter().any(type_mentions_self)
        }
        ast::TypeKind::Tuple(arguments) => arguments.iter().any(type_mentions_self),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields.iter().any(|field| type_mentions_self(&field.ty))
                || row.as_ref().is_some_and(|row| type_mentions_self(row))
        }
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_mentions_self),
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_mentions_self(inner)
        }
        ast::TypeKind::Borrow { inner, .. } => type_mentions_self(inner),
        ast::TypeKind::Array(inner, length) => {
            type_mentions_self(inner) || type_mentions_self(length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_self(left) || type_mentions_self(right)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_self(&parameter.ty))
                || type_mentions_self(result)
                || effects.iter().any(type_mentions_self)
        }
        ast::TypeKind::Lifetime(_)
        | ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Predicate(_) => false,
    }
}

/// Like [`type_mentions_self`], but `Self.Assoc` for an associated type that is
/// agreed by every object impl is a concrete ABI type and is allowed.
fn type_mentions_self_outside_assoc(ty: &ast::Type, allowed: &BTreeSet<String>) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2
                && path[0] == "Self"
                && arguments.is_empty()
                && allowed.contains(&path[1])
            {
                return false;
            }
            path.first().is_some_and(|name| name == "Self")
                || arguments
                    .iter()
                    .any(|argument| type_mentions_self_outside_assoc(argument, allowed))
        }
        ast::TypeKind::Tuple(arguments) => arguments
            .iter()
            .any(|argument| type_mentions_self_outside_assoc(argument, allowed)),
        ast::TypeKind::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_mentions_self_outside_assoc(inner, allowed))
        }
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_mentions_self_outside_assoc(inner, allowed)
        }
        ast::TypeKind::Borrow { inner, .. } => type_mentions_self_outside_assoc(inner, allowed),
        ast::TypeKind::Array(inner, length) => {
            type_mentions_self_outside_assoc(inner, allowed)
                || type_mentions_self_outside_assoc(length, allowed)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_self_outside_assoc(left, allowed)
                || type_mentions_self_outside_assoc(right, allowed)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_self_outside_assoc(&parameter.ty, allowed))
                || type_mentions_self_outside_assoc(result, allowed)
                || effects
                    .iter()
                    .any(|effect| type_mentions_self_outside_assoc(effect, allowed))
        }
        _ => false,
    }
}

/// Whether a declared type syntax contains an open structural row. Impl
/// headers require an exact canonical row, so they reject `..`.
fn type_has_open_row(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::Structural { fields, open, row } => {
            *open || row.is_some() || fields.iter().any(|field| type_has_open_row(&field.ty))
        }
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            arguments.iter().any(type_has_open_row)
        }
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_has_open_row),
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Borrow { inner, .. } => type_has_open_row(inner),
        ast::TypeKind::Array(element, length) => {
            type_has_open_row(element) || type_has_open_row(length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_has_open_row(left) || type_has_open_row(right)
        }
        ast::TypeKind::Function {
            parameters, result, ..
        } => parameters.iter().any(|p| type_has_open_row(&p.ty)) || type_has_open_row(result),
        _ => false,
    }
}
/// Whether a type expression mentions any of the given generic binders.
fn type_references_any_binder(
    resolution: &Resolution,
    ty: &ast::Type,
    binders: &BTreeSet<BindingId>,
) -> bool {
    let mentions = |ty: &ast::Type| type_references_any_binder(resolution, ty, binders);
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } => {
            resolution
                .reference(ty.span)
                .is_some_and(|id| binders.contains(&id))
                || arguments.iter().any(mentions)
        }
        ast::TypeKind::Tuple(items) => items.iter().any(mentions),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields.iter().any(|field| mentions(&field.ty))
                || row.as_ref().is_some_and(|row| mentions(row))
        }
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => mentions(inner),
        ast::TypeKind::Borrow { inner, .. } => mentions(inner),
        ast::TypeKind::Array(inner, length) => mentions(inner) || mentions(length),
        ast::TypeKind::Binary { left, right, .. } => mentions(left) || mentions(right),
        ast::TypeKind::Function {
            parameters, result, ..
        } => parameters.iter().any(|parameter| mentions(&parameter.ty)) || mentions(result),
        _ => false,
    }
}
/// Whether an expression mentions any of the given generic binders. Used to
/// reject associated-constant values that would require generic const
/// evaluation, which is not part of this subset.
fn expression_mentions_generic(
    resolution: &Resolution,
    expr: &ast::Expr,
    binders: &BTreeSet<BindingId>,
) -> bool {
    match &expr.kind {
        ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => resolution
            .reference(expr.span)
            .is_some_and(|id| binders.contains(&id)),
        _ => false,
    }
}
/// Validate a method receiver written against a generic impl header. The
/// receiver must be `Self`/the concrete pattern by value or a shared/exclusive
/// nominal-record borrow of it.
fn checked_generic_method_receiver(
    types: &mut Types<'_>,
    receiver: &ast::Type,
    self_ty: &ast::Type,
    generics: &BTreeSet<BindingId>,
    resolution: &Resolution,
) -> Result<()> {
    let shape = match &receiver.kind {
        ast::TypeKind::SelfType => return Ok(()),
        ast::TypeKind::Borrow { inner, .. } => {
            if !matches!(inner.kind, ast::TypeKind::SelfType) {
                return Err(Diagnostic::new(
                    receiver.span,
                    "a generic impl receiver may borrow only 'Self' (write 'self: &Self' or '&self')",
                ));
            }
            true
        }
        ast::TypeKind::Named { .. } => {
            // The concrete pattern itself is accepted when it is syntactically
            // the header self type.
            if type_key(receiver) == type_key(self_ty) {
                return Ok(());
            }
            return Err(Diagnostic::new(
                receiver.span,
                "a generic impl receiver must be written 'self: Self', 'self: &Self', or 'self: &mut Self'",
            ));
        }
        _ => {
            return Err(Diagnostic::new(
                receiver.span,
                "a generic impl receiver must be written 'self: Self', 'self: &Self', or 'self: &mut Self'",
            ));
        }
    };
    let _ = (types, generics, resolution, shape);
    Ok(())
}

/// The receiver mode of a trait method declaration. Dynamic dispatch mirrors
/// the three statically checked modes, but mutable dispatch additionally writes
/// the updated object back to the caller's local.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReceiverMode {
    Owned,
    Shared,
    Mutable,
}
fn trait_receiver_mode(method: &ast::Function) -> ReceiverMode {
    match method
        .parameters
        .first()
        .map(|parameter| &parameter.ty.kind)
    {
        Some(ast::TypeKind::Borrow { mutable: true, .. }) => ReceiverMode::Mutable,
        Some(ast::TypeKind::Borrow { mutable: false, .. }) => ReceiverMode::Shared,
        _ => ReceiverMode::Owned,
    }
}

/// Translate `{ a < b && ... }` syntactically. Only earlier runtime parameters,
/// integer constants, `+`/`-` by constants, and `Bytes.len`/`Vec.len` of a
/// parameter may appear.
pub(crate) fn proposition_of(
    resolution: &Resolution,
    f: &ast::Function,
    parameter: &ast::Parameter,
) -> Result<crate::facts::Proposition> {
    use crate::facts::ParamTerm;
    let ast::TypeKind::Predicate(body) = &parameter.ty.kind else {
        return Err(Diagnostic::new(
            parameter.ty.span,
            "erased executable parameters must be propositions written '{ ... }'",
        ));
    };
    let mut indices = BTreeMap::new();
    for p in f.parameters.iter().filter(|p| !p.erased) {
        if std::ptr::eq(p, parameter) {
            break;
        }
        indices.insert(resolution.binder(p.span).unwrap(), indices.len());
    }
    let position = f
        .parameters
        .iter()
        .position(|p| std::ptr::eq(p, parameter))
        .unwrap();
    for p in f.parameters[..position].iter().filter(|p| !p.erased) {
        let _ = p;
    }
    let mut runtime_before = BTreeMap::new();
    for p in f.parameters[..position].iter().filter(|p| !p.erased) {
        runtime_before.insert(resolution.binder(p.span).unwrap(), runtime_before.len());
    }
    let unsupported = |span| {
        Diagnostic::new(
            span,
            "propositions support linear integer comparisons over earlier integer and Bool parameters, constants, 'x + c', 'c * x', Bytes.len/Vec.len/Slice.len, and Bool atoms 'b' / '!b', joined by '&&'",
        )
    };
    fn text(e: &ast::Expr) -> String {
        match &e.kind {
            ast::ExprKind::Name(n) | ast::ExprKind::Integer(n) => n.clone(),
            ast::ExprKind::Field { value, name } => format!("{}.{name}", text(value)),
            ast::ExprKind::Call { callee, arguments } => format!(
                "{}({})",
                text(callee),
                arguments.iter().map(text).collect::<Vec<_>>().join(", ")
            ),
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => format!("!({})", text(operand)),
            ast::ExprKind::Unary { operand, .. } => format!("-{}", text(operand)),
            ast::ExprKind::Bool(value) => value.to_string(),
            ast::ExprKind::Binary { op, left, right } => {
                let op = match op {
                    Kind::Lt => "<",
                    Kind::Le => "<=",
                    Kind::Gt => ">",
                    Kind::Ge => ">=",
                    Kind::EqEq => "==",
                    Kind::Plus => "+",
                    Kind::Minus => "-",
                    Kind::Star => "*",
                    Kind::AmpAmp => "&&",
                    Kind::PipePipe => "||",
                    Kind::Ne => "!=",
                    _ => "?",
                };
                format!("{} {op} {}", text(left), text(right))
            }
            _ => "?".into(),
        }
    }
    let linear = |e: &ast::Expr| -> Result<crate::facts::ParamLinear> {
        use crate::facts::ParamLinear;
        fn go(
            e: &ast::Expr,
            resolution: &Resolution,
            params: &BTreeMap<BindingId, usize>,
            unsupported: &dyn Fn(Span) -> Diagnostic,
        ) -> Result<ParamLinear> {
            match &e.kind {
                ast::ExprKind::Integer(n) => Ok(ParamLinear::constant(
                    n.parse().map_err(|_| unsupported(e.span))?,
                )),
                ast::ExprKind::Bool(value) => Ok(ParamLinear::constant(i128::from(*value))),
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                } => go(operand, resolution, params, unsupported)?
                    .negate()
                    .ok_or_else(|| unsupported(e.span)),
                ast::ExprKind::Name(_) => resolution
                    .reference(e.span)
                    .and_then(|id| params.get(&id))
                    .map(|i| ParamLinear::variable(ParamTerm::Param(*i), 1))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            e.span,
                            "a proposition may mention only runtime parameters declared before it",
                        )
                    }),
                ast::ExprKind::Binary {
                    op: op @ (Kind::Plus | Kind::Minus),
                    left,
                    right,
                } => {
                    let l = go(left, resolution, params, unsupported)?;
                    let r = go(right, resolution, params, unsupported)?;
                    if *op == Kind::Plus {
                        l.add(&r)
                    } else {
                        l.sub(&r)
                    }
                    .ok_or_else(|| unsupported(e.span))
                }
                ast::ExprKind::Binary {
                    op: Kind::Star,
                    left,
                    right,
                } => {
                    let l = go(left, resolution, params, unsupported)?;
                    let r = go(right, resolution, params, unsupported)?;
                    if l.coefficients.is_empty() {
                        r.scale(l.constant)
                    } else if r.coefficients.is_empty() {
                        l.scale(r.constant)
                    } else {
                        None
                    }
                    .ok_or_else(|| unsupported(e.span))
                }
                ast::ExprKind::Call { callee, arguments } if arguments.len() == 1 => {
                    let builtin = resolution.reference(callee.span).is_some_and(|id| {
                        let b = &resolution.bindings[id];
                        b.kind == BindingKind::Builtin
                            && matches!(b.name.as_str(), "Bytes.len" | "Vec.len" | "Slice.len")
                    });
                    match (builtin, go(&arguments[0], resolution, params, unsupported)?) {
                        (true, argument)
                            if argument.coefficients.len() == 1
                                && argument.constant == 0
                                && argument.coefficients.values().all(|c| *c == 1) =>
                        {
                            let ParamTerm::Param(index) =
                                *argument.coefficients.keys().next().unwrap()
                            else {
                                return Err(unsupported(e.span));
                            };
                            Ok(ParamLinear::variable(ParamTerm::Len(index), 1))
                        }
                        _ => Err(unsupported(e.span)),
                    }
                }
                _ => Err(unsupported(e.span)),
            }
        }
        go(e, resolution, &runtime_before, &unsupported)
    };
    type Atom = (crate::facts::ParamLinear, Kind, crate::facts::ParamLinear);
    type Formula = Vec<Vec<Atom>>;
    const MAX_DISJUNCTS: usize = 32;
    let too_large = |span| {
        Diagnostic::new(
            span,
            "this proposition expands to more than 32 cases; split it into several erased parameters",
        )
    };
    let and = |a: Formula, b: Formula, span| -> Result<Formula> {
        if a.len() * b.len() > MAX_DISJUNCTS {
            return Err(too_large(span));
        }
        let mut out = Vec::new();
        for left in &a {
            for right in &b {
                let mut both = left.clone();
                both.extend(right.iter().cloned());
                out.push(both);
            }
        }
        Ok(out)
    };
    let or = |mut a: Formula, b: Formula, span| -> Result<Formula> {
        a.extend(b);
        if a.len() > MAX_DISJUNCTS {
            return Err(too_large(span));
        }
        Ok(a)
    };
    let negated = |op: &Kind| match op {
        Kind::Lt => Kind::Ge,
        Kind::Le => Kind::Gt,
        Kind::Gt => Kind::Le,
        Kind::Ge => Kind::Lt,
        Kind::EqEq => Kind::Ne,
        _ => Kind::EqEq,
    };
    let mut booleans = Vec::new();
    // Negation is pushed to the atoms (PROVE-DISJ).
    #[allow(clippy::too_many_arguments)]
    fn formula(
        e: &ast::Expr,
        positive: bool,
        linear: &dyn Fn(&ast::Expr) -> Result<crate::facts::ParamLinear>,
        and: &dyn Fn(Formula, Formula, Span) -> Result<Formula>,
        or: &dyn Fn(Formula, Formula, Span) -> Result<Formula>,
        negated: &dyn Fn(&Kind) -> Kind,
        booleans: &mut Vec<usize>,
        unsupported: &dyn Fn(Span) -> Diagnostic,
    ) -> Result<Formula> {
        use crate::facts::{ParamLinear, ParamTerm};
        match &e.kind {
            ast::ExprKind::Binary {
                op: op @ (Kind::AmpAmp | Kind::PipePipe),
                left,
                right,
            } => {
                let l = formula(
                    left,
                    positive,
                    linear,
                    and,
                    or,
                    negated,
                    booleans,
                    unsupported,
                )?;
                let r = formula(
                    right,
                    positive,
                    linear,
                    and,
                    or,
                    negated,
                    booleans,
                    unsupported,
                )?;
                if (*op == Kind::AmpAmp) == positive {
                    and(l, r, e.span)
                } else {
                    or(l, r, e.span)
                }
            }
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => formula(
                operand,
                !positive,
                linear,
                and,
                or,
                negated,
                booleans,
                unsupported,
            ),
            ast::ExprKind::Binary {
                op: op @ (Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne),
                left,
                right,
            } => {
                let op = if positive { op.clone() } else { negated(op) };
                Ok(vec![vec![(linear(left)?, op, linear(right)?)]])
            }
            ast::ExprKind::Bool(value) => Ok(if *value == positive {
                vec![Vec::new()]
            } else {
                Vec::new()
            }),
            // A bare `Bool` parameter `b` is `b == 1`.
            ast::ExprKind::Name(_) => {
                let term = linear(e)?;
                let Some(ParamTerm::Param(index)) = term.coefficients.keys().next().copied() else {
                    return Err(unsupported(e.span));
                };
                booleans.push(index);
                Ok(vec![vec![(
                    term,
                    Kind::EqEq,
                    ParamLinear::constant(i128::from(positive)),
                )]])
            }
            _ => Err(unsupported(e.span)),
        }
    }
    let disjuncts = formula(
        body,
        true,
        &linear,
        &and,
        &or,
        &negated,
        &mut booleans,
        &unsupported,
    )?;
    let _ = indices;
    Ok(crate::facts::Proposition {
        disjuncts,
        booleans,
        text: text(body),
    })
}
/// The local whose storage a checked place lives in.
fn place_root_slot(expr: &Expr) -> Option<usize> {
    match &expr.kind {
        ExprKind::Local(slot)
        | ExprKind::Peek(slot)
        | ExprKind::Move(slot)
        | ExprKind::Borrow(slot) => Some(*slot),
        ExprKind::Project(base, _) | ExprKind::PlaceIndex { base, .. } => place_root_slot(base),
        ExprKind::BorrowPlace(base) | ExprKind::Coerce { value: base, .. } => place_root_slot(base),
        ExprKind::Slice { base, .. } => place_root_slot(base),
        _ => None,
    }
}
/// Source-like text of a postcondition clause, for diagnostics.
fn ensures_text(clause: &ast::Ensures) -> String {
    fn text(e: &ast::Expr) -> String {
        match &e.kind {
            ast::ExprKind::Name(n) | ast::ExprKind::Integer(n) => n.clone(),
            ast::ExprKind::Bool(value) => value.to_string(),
            ast::ExprKind::Field { value, name } => format!("{}.{name}", text(value)),
            ast::ExprKind::Is { value, variant } => format!("{} is {variant}", text(value)),
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => format!("!({})", text(operand)),
            ast::ExprKind::Unary { operand, .. } => format!("-{}", text(operand)),
            ast::ExprKind::Binary { op, left, right } => {
                let op = match op {
                    Kind::Lt => "<",
                    Kind::Le => "<=",
                    Kind::Gt => ">",
                    Kind::Ge => ">=",
                    Kind::EqEq => "==",
                    Kind::Ne => "!=",
                    Kind::Plus => "+",
                    Kind::Minus => "-",
                    Kind::Star => "*",
                    Kind::AmpAmp => "&&",
                    Kind::PipePipe => "||",
                    _ => "?",
                };
                // Parenthesise operands that bind looser than `op`.
                let level = |e: &ast::Expr| match &e.kind {
                    ast::ExprKind::Binary { op, .. } => match op {
                        Kind::PipePipe => 1,
                        Kind::AmpAmp => 2,
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne => 3,
                        Kind::Plus | Kind::Minus => 4,
                        _ => 5,
                    },
                    _ => 6,
                };
                let own = level(e);
                let side = |operand: &ast::Expr, right: bool| {
                    let inner = level(operand);
                    if inner < own || (right && inner == own && op != "&&" && op != "||") {
                        format!("({})", text(operand))
                    } else {
                        text(operand)
                    }
                };
                format!("{} {op} {}", side(left, false), side(right, true))
            }
            _ => "?".into(),
        }
    }
    let guard = match &clause.guard {
        ast::EnsuresGuard::Always => String::new(),
        ast::EnsuresGuard::Result(true) => "result => ".into(),
        ast::EnsuresGuard::Result(false) => "!result => ".into(),
        ast::EnsuresGuard::Variant { name, binders, .. } if binders.is_empty() => {
            format!("{name} => ")
        }
        ast::EnsuresGuard::Variant { name, binders, .. } => format!(
            "{name}({}) => ",
            binders
                .iter()
                .map(|(binder, _)| binder.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    };
    format!("{guard}{{ {} }}", text(&clause.body))
}
/// An integer literal checked against the range of its contextual type.
fn int_literal(text: &str, negative: bool, ty: Type, span: Span) -> Result<i64> {
    let kind = ty.int_kind().unwrap_or(crate::int::IntKind::I64);
    let magnitude = text.parse::<i128>().ok();
    magnitude
        .map(|m| if negative { -m } else { m })
        .and_then(|value| kind.encode(value))
        .ok_or_else(|| {
            Diagnostic::new(
                span,
                format!(
                    "integer literal is outside the {} range ({}..={})",
                    kind.name(),
                    kind.min(),
                    kind.max()
                ),
            )
        })
}
fn is_int_literal(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ast::ExprKind::Integer(_) => true,
        ast::ExprKind::Unary {
            op: Kind::Minus,
            operand,
            ..
        } => matches!(operand.kind, ast::ExprKind::Integer(_)),
        _ => false,
    }
}
/// A nonnegative or negated decimal float literal.
fn is_float_literal(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ast::ExprKind::Float(_) => true,
        ast::ExprKind::Unary {
            op: Kind::Minus,
            operand,
            ..
        } => matches!(operand.kind, ast::ExprKind::Float(_)),
        _ => false,
    }
}
#[allow(dead_code)]
fn integer(text: &str, negative: bool, span: Span) -> Result<i64> {
    let value = if negative {
        format!("-{text}")
    } else {
        text.to_owned()
    };
    value
        .parse()
        .map_err(|_| Diagnostic::new(span, "integer literal is outside the i64 range"))
}
struct Loop {
    /// Result type of `break value` (None for `while`).
    value: Option<Type>,
    is_while: bool,
    /// Type expected of the whole loop expression, for `break` values.
    expected: Option<Type>,
    /// Whether a `break` leaves this loop (then exit values need not be
    /// the loop-head values).
    broke: bool,
    /// The checked `invariant { P }` of a `while`, proved at each `continue`.
    invariant: Option<Expr>,
}
/// One inclusion constraint on an effect row during a call: the declared row
/// `fixed | e1 | e2 ...` must cover the actual callable row. Constraints are
/// accumulated across every higher-order argument before a finite solver picks
/// a unique minimal specialization.
/// How an unannotated lambda's row is decided.
#[derive(Clone, Copy, Debug)]
enum LambdaRow {
    Declared,
    /// From the expected arrow (bodies that handle or perform).
    Fixed(u16),
    /// The union of the effects the body requires.
    FromBody,
}
#[derive(Clone, Copy, Debug)]
struct LambdaInference {
    result_from_body: bool,
    row: LambdaRow,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum LambdaContext {
    Ordinary,
    TaskScope,
    Quotation,
}
/// Types a call or a binding's first use supplies for an unannotated
/// lambda's parameters and result (I-LAMBDA-INFER).
#[derive(Clone, Debug, Default)]
struct LambdaHint {
    parameters: Vec<Option<Type>>,
    result: Option<Type>,
}

#[derive(Debug, Clone)]
struct EffectConstraint {
    row: crate::runtime_types::EffectRowTerm,
    actual: u16,
    span: Span,
}

/// One declared effect operation. Dynamic `perform` calls use this signature;
/// lexical handlers still drive direct performs, while the declaration lets a
/// called function find the handler on the runtime stack.
#[derive(Clone, Copy)]
struct EffectOperation {
    id: usize,
    parameter: Type,
    result: Type,
    /// Built-in effects a handler may have (`effect Op: P -> R ! {..}`);
    /// every dynamic perform requires them.
    latent: u16,
}
/// The canonical kernel index of an admitted runtime scalar binding.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ScalarValue {
    /// A symbolic binder at this absolute position in `kernel_locals`.
    Position(usize),
    /// A machine literal known on every path reaching the current point.
    Literal(Term),
    /// A value changed on only some path or across a loop iteration. It has no
    /// stable index until [`Checker::fresh_scalar_value`] appends a binder.
    Unknown,
}
/// One lexical effect-handler binding. The handler is materialized in a hidden
/// local so `perform` can call it and the ownership pass can enforce the
/// callable's one-shot/linear contract.
/// What `checked_effect_body` needs to build a `Suspendable` node.
struct SuspendableSite {
    name: String,
    /// Types of the values the handler closure captures.
    handler_captures: Vec<Type>,
    /// The handler is a `once` callable, consumed by its first perform.
    handler_once: bool,
    handler_parameter: Type,
    /// Locals the handler captures by reference (it reads or writes them).
    handler_refs: Vec<usize>,
    handler_function: Option<usize>,
    /// The body performs the operation lexically outside its tail.
    lexical: bool,
    operation: Option<usize>,
    multishot: bool,
    /// The handler takes a `multi fn` token (docs/multishot-capabilities.md).
    multi: bool,
    handler_writes: Vec<usize>,
    effects: u16,
    token_effects: u16,
    /// The handler local of a capability whose calls become await points.
    capability_slot: Option<usize>,
}
struct HandlerScope {
    operation: String,
    parameter: Type,
    result: Type,
    slot: usize,
    handler_parameter: Type,
    handler_result: Type,
    effects: u16,
    /// The handler accepts the copyable multishot resumption token. Only a
    /// capture-free continuation has that representation.
    multishot: bool,
    /// The multishot token is a `multi fn` with a continuation-stack
    /// environment instead of a code pointer.
    multi: bool,
    /// Performs of this operation become `Suspend` points of a suspendable
    /// body instead of identity-token handler calls.
    region: bool,
    /// Suspension points issued so far for this handle.
    points: usize,
    /// The handle pushes a dynamic handler frame (declared operation).
    declared: bool,
    /// Abortive operation (`-> Never`): the label of the `AbortScope` its
    /// performs leave (E-ABORT-LEXICAL).
    abort: Option<usize>,
    /// Abortive operations that may leave the body through the resumption
    /// token (its row; E-ABORT-INTERACT).
    token_effects: u16,
    /// The handler was moved into its dynamic frame: a capturing one-shot
    /// handler of a declared operation, reusable or consumed by its first
    /// perform. Its performs, lexical ones included, go through the frame.
    in_frame: bool,
}

struct Checker<'a, 't> {
    /// FND-ROWS-INFER: this body's row is being inferred; `effects` holds
    /// every effect and `required_effects` collects the row.
    inferring_row: bool,
    /// Explicit quotation holes, keyed by original source occurrence. During
    /// template checking their slots are remapped to captured parameters.
    quote_holes: BTreeMap<(usize, usize), usize>,
    quote_splices: BTreeMap<(usize, usize), (usize, usize)>,
    types: &'t mut Types<'a>,
    resolution: &'a Resolution,
    functions: &'t mut Functions<'a>,
    substitution: BTreeMap<BindingId, Type>,
    /// Concrete values of this instance's compile-time natural parameters.
    consts: BTreeMap<BindingId, usize>,
    /// Concrete values of this instance's abstract grade parameters.
    grades: BTreeMap<BindingId, Grade>,
    /// Concrete effect rows of this instance's `e: Effects` parameters.
    effect_arguments: BTreeMap<BindingId, u16>,
    locals: Vec<Local>,
    slots: BTreeMap<BindingId, usize>,
    result: Type,
    /// Declared or freshly elided lifetime of each runtime parameter of the
    /// function currently being checked. Lambda captures inherit a declared
    /// parameter lifetime so a captured slice keeps the caller's identity.
    parameter_lifetimes: Vec<Option<String>>,
    /// Every lifetime declared by the function currently being checked. Nested
    /// record instantiations may mention these labels even when no runtime
    /// parameter is itself a reference, so the contextual witness classifies
    /// them as free occurrence labels instead of dropping the whole check.
    declared_lifetimes: BTreeSet<String>,
    /// Static result-transfer contract of the function/lambda currently being
    /// checked. Distinguishes owning `@[1]` transfers from must-use copyable
    /// transfers when a returned value is observed.
    result_grade: Option<Grade>,
    /// Declared result lifetime and outlives bounds of the function currently
    /// being checked. They are the evidence source for same-scope lifetime
    /// witnesses; the witness never invents an edge.
    result_lifetime: Option<String>,
    lifetime_bounds: BTreeSet<(String, String)>,
    /// Nonzero while checking an expression that is being coerced into a
    /// callee parameter. Callee-declared labels are instantiated by the call
    /// and are governed by the callee contract plus the ownership provenance
    /// mapping, so the same-scope contextual witness does not reinterpret them
    /// as the caller's declared lifetimes.
    call_boundary: usize,
    effects: u16,
    depth: usize,
    loops: Vec<Loop>,
    facts: crate::facts::Facts,
    /// Slots assigned by the function or lambda currently being checked.
    /// A lambda turns this set into `Function::capture_writes`, which decides
    /// whether a by-reference capture is a shared or exclusive loan.
    written_slots: BTreeSet<usize>,
    /// Captured outer slots that a call to a closure binding may write.
    /// Populated when a local is bound to a capturing lambda and consulted by
    /// indirect calls so proof facts never survive a writing call.
    closure_writes: BTreeMap<usize, Vec<usize>>,
    /// Types captured by the closure value a local holds, when known.
    closure_captures: BTreeMap<usize, Vec<Type>>,
    /// Types filled into omitted lambda annotations (`fn(x) { ... }`), keyed
    /// by the hole's span (I-LAMBDA-INFER).
    lambda_holes: BTreeMap<(usize, usize), Type>,
    /// Parameter/result types a generic call or a binding's first use
    /// supplies for the next unannotated lambda.
    lambda_hint: Option<LambdaHint>,
    /// Union of every effect `require`d in the current lambda body; an
    /// omitted lambda row is inferred as exactly these bits.
    required_effects: std::cell::Cell<u16>,
    /// The binder span of `handle Op as op`, consumed by `handle_effect`.
    pending_capability: Option<(String, Span)>,
    /// Constants whose value is being checked, to reject a cycle.
    expanding_constants: Vec<BindingId>,
    /// Set while an element write borrows a `where len >= N` field: the only
    /// exclusive borrow of such a field that cannot shorten it.
    writing_bounded_field: bool,
    /// Set while checking `place.replace(v)` on a length-refined field: the
    /// length `v` must be checked to have.
    replace_min_length: Option<i64>,
    /// The invariant the next checked block (a `while` body) must prove at
    /// its end.
    body_invariant: Option<Expr>,
    /// Reference parameters declared `where len >= N`, by slot.
    parameter_lengths: BTreeMap<usize, i64>,
    /// Set just before checking a refined parameter in a use that keeps its
    /// bound (a non-shortening method receiver).
    refined_use_ok: bool,
    /// Spans of call arguments passed to a length-refined parameter: such a
    /// parameter keeps the bound, so a refined place may be lent there.
    lending_spans: BTreeSet<(usize, usize)>,
    /// Next `AbortScope` label of this checker (unique per function body).
    abort_labels: usize,
    /// Locals holding a second-class capability (EFF-CAP-LEXICAL).
    capability_slots: BTreeSet<usize>,
    /// Capabilities that may be passed to functions: `cap` parameters and
    /// noncapturing, one-shot, tail-resumptive handlers. Others can only be
    /// performed in their own handle body (EFF-CAP-RESUME).
    capability_passable: BTreeSet<usize>,
    /// Capability locals of non-tail, noncapturing, one-shot handlers: they
    /// may be passed to `cap` parameters, and such calls become await
    /// points of the handled body (EFF-CAP-RESUME-CALLS).
    capability_resumable: BTreeSet<usize>,
    /// EFF-CAP-RESUME-CAPTURING: capability slots of capturing handlers kept
    /// in their dynamic frame: declared operation id and handler arrow type.
    capability_framed: BTreeMap<usize, (usize, usize, u16)>,
    /// `cap` parameters of this function: they may be bound to a handler
    /// with code after `resume`, so a lambda cannot capture them.
    capability_parameter_slots: BTreeSet<usize>,
    /// Set while checking an argument passed to a `cap` parameter.
    capability_argument: bool,
    /// Erased proof parameters in scope: binder -> proposition.
    proofs: BTreeMap<BindingId, crate::facts::Proposition>,
    /// Checked logical definitions and their kernel names.
    logical: &'a crate::check::LogicalEnvironment,
    /// Kernel binders in scope order: symbolic runtime scalars followed by
    /// erased logical/arithmetic evidence. A runtime scalar contributes its
    /// carrier type, so `Var(i)` is the symbolic value itself.
    kernel_locals: Vec<BindingId>,
    /// Kernel type of each binder in `kernel_locals` (including symbolic
    /// runtime scalars).
    kernel_types: BTreeMap<BindingId, Term>,
    /// Kernel type of each erased logical parameter in scope. Only these are
    /// evidence; a runtime scalar is never a proof and has no runtime-erased
    /// meaning.
    kernel_proofs: BTreeMap<BindingId, Term>,
    /// Lexical `Task.scope` nesting. `Task.spawn` is legal only when nonzero.
    /// Nested function values reset this to zero so spawn cannot be smuggled
    /// into a callback that outlives its scope.
    scope_depth: usize,
    /// THREAD-SCOPE: the immediate scope lambda is a `Thread.scope`.
    scope_parallel: bool,
    /// Kind of the scope lambda about to be checked by `task_callable`.
    next_scope_parallel: bool,
    /// Monotonic id for checked `Slice.split_at_mut` pairs in this body.
    next_split: usize,
    /// Concrete `Self` target when checking an impl method body.
    self_type: Option<Type>,
    /// Trait specialization of the default body being checked, if any. An
    /// unqualified method call on `Self` prefers this specialization.
    default_trait: Option<(BindingId, TraitArguments)>,
    /// Associated constants of the impl that owns this body, already evaluated
    /// for this specialization. `Self::NAME` projects them.
    associated_consts: BTreeMap<String, ConstValue>,
    /// Module unit of the function being checked, for method visibility.
    unit: usize,
    /// The current field expression is a place used to derive a subview
    /// (`&mut record.field[..]`), not a copied field value.
    field_place: bool,
    /// Binding of the function or method body being checked. Used to resolve
    /// `T.NAME` associated-constant projections through `T`'s trait bound.
    binding: BindingId,
    /// Version of each admitted symbolic runtime scalar local. Assignments
    /// append a fresh kernel binder and increment this counter, so later proof
    /// uses denote the new value while already-shifted proof types denote the
    /// old hypothesis. A mutable capture is still rejected because a closure
    /// environment would observe an unsynchronized runtime location.
    scalar_epochs: BTreeMap<BindingId, u32>,
    /// Snapshot positions in `kernel_locals` for scalar aliases introduced by
    /// `let alias = scalar_name`. The position is absolute, so a later
    /// assignment to the source appends a new binder and leaves the alias
    /// denoting the value copied at binding time.
    kernel_aliases: BTreeMap<BindingId, usize>,
    /// Canonical index value of an admitted scalar binding. `Position` names a
    /// symbolic binder; `Literal` is a machine literal known for every branch
    /// reaching this point; `Unknown` has no stable index until a fresh binder
    /// is appended at a branch or loop join.
    scalar_values: BTreeMap<BindingId, ScalarValue>,
    /// Erased proof-valued locals bound by `let p = <proof>`. Each entry stores
    /// the checked kernel term together with the context length at which it was
    /// elaborated, so later context growth can shift its free variables.
    proof_values: BTreeMap<BindingId, (Term, usize)>,
    /// Declared effect operations used by dynamic performs in called bodies.
    effect_operations: &'t BTreeMap<String, EffectOperation>,
    /// Lexically active effect handlers, innermost last. A handler is visible
    /// only to direct `perform` expressions in the same function body.
    handlers: Vec<HandlerScope>,
    /// Pending effect-row inclusion constraints for the current inference
    /// group. `infer` takes a mark and solves them after every argument has
    /// contributed its evidence.
    effect_constraints: Vec<EffectConstraint>,
    /// Cross-parameter backtracking state. `unify_plan` is the current choice
    /// sequence for multi-variable union partitions, `unify_decisions`
    /// records each decision's cardinality in the current replay, and
    /// `unify_plan_active` distinguishes a planned replay from ordinary
    /// left-to-right inference (which deterministically takes choice zero).
    unify_plan: Vec<usize>,
    unify_decisions: Vec<usize>,
    unify_plan_active: bool,
    /// Set when the ordinary inference pass took the first of several choices
    /// at a partition or indexed-union decision. Such a call is then searched
    /// exhaustively and accepted only when one substitution survives.
    unify_open_choice: bool,
    /// Type variables bound by a multi-variable union partition during the
    /// current `infer` call. Parameters that mention one of them are checked
    /// without a tentative expected type so the replay can reconsider the
    /// partition instead of failing during contextual checking.
    partition_bound: BTreeSet<BindingId>,
    /// Type variables bound as structural row tails in the current `infer`
    /// call. Parameters mentioning them are checked without a tentative
    /// expected row so a residual-row mismatch is reported by unification.
    row_bound: BTreeSet<BindingId>,
    /// Hidden owner bindings hoisted out of an expression so a checked
    /// reference to a temporary has real storage. Each enclosing statement
    /// list drains the entries created while checking it; the local's resource
    /// drops at that block's end, after every checked reference's last use.
    hoisted: Vec<Statement>,
    /// Last index-place identity handed out (see `index_place_id`).
    next_index_place: usize,
    /// Proved-distinct index-place pairs of the bodies checked so far.
    index_relations: BTreeSet<(usize, usize)>,
    /// Runtime-length binder renaming for the call whose `infer` is about to
    /// run: callee `i64` parameter -> caller binding passed for it.
    pending_lengths: BTreeMap<BindingId, BindingId>,
    /// ENSURES: the current function's postconditions, if any.
    ensures_context: Option<EnsuresContext>,
    /// The expression being checked is a value the function returns.
    ensures_tail: bool,
    /// ENSURES-PREDICATES: nesting of predicate expansions in a proposition.
    ensures_depth: std::cell::Cell<usize>,
    /// The `if`/`match`/block being checked is in return position, so its
    /// branch tails are too.
    branch_tail: bool,
}
/// The postconditions of the function being checked (ENSURES).
#[derive(Clone)]
struct EnsuresContext {
    clauses: Vec<ast::Ensures>,
    /// Runtime parameters: binder and slot.
    params: Vec<(BindingId, usize)>,
    result: Type,
}
/// A symbolic value in a postcondition: a path from a root, or a checked
/// expression (a construction or a scalar expression).
#[derive(Clone)]
enum Sym {
    Path(crate::facts::Root, Vec<crate::facts::Step>),
    Value(Box<Expr>),
    Unknown,
}
/// One actual lifetime supplied for a callee-declared binder at a parameter
/// occurrence. The polarity decides whether the actual identity must equal the
/// binder (invariant), outlive it (covariant), or be outlived by it
/// (contravariant).
#[derive(Clone, Debug)]
struct CallLifetimeOccurrence {
    actual: String,
    polarity: crate::variance::LabelPolarity,
}
impl Checker<'_, '_> {
    fn nested<T>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                span,
                "executable checking nesting budget exhausted",
            ));
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    /// The type of an integer literal: its expected integer type, else i64.
    fn literal_type(&self, expected: Option<Type>) -> Type {
        let expected = expected.map(|t| match t {
            Type::Union(id) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .find(|m| m.int_kind().is_some())
                .unwrap_or(t),
            t => t,
        });
        match expected.and_then(Type::int_kind) {
            Some(kind) => Type::int(kind),
            None => Type::I64,
        }
    }
    /// The type of a float literal: a contextual `f32`/`f64` (including a
    /// float union alternative), else the default `f64`.
    fn float_literal_type(&self, expected: Option<Type>) -> Type {
        let expected = expected.map(|t| match t {
            Type::Union(id) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .find(|m| m.float_kind().is_some())
                .unwrap_or(t),
            t => t,
        });
        match expected.and_then(Type::float_kind) {
            Some(kind) => Type::float(kind),
            None => Type::float(crate::float::FloatKind::F64),
        }
    }
    /// Both operands must be the same float type.
    fn same_float(&self, left: Type, right: Type, span: Span) -> Result<Type> {
        let left_kind = left.float_kind();
        let right_kind = right.float_kind();
        match (left, right, left_kind, right_kind) {
            (Type::Never, other, _, _) | (other, Type::Never, _, _) => {
                Ok(if other == Type::Never {
                    Type::float(crate::float::FloatKind::F64)
                } else {
                    other
                })
            }
            (_, _, Some(a), Some(b)) if a == b => Ok(left),
            (_, _, Some(_), Some(_)) => Err(Diagnostic::new(
                span,
                format!(
                    "floating-point operands must have the same type, found {} and {}; convert one explicitly with Float.try_to_f32 or Float.to_f64",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
            _ => Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: this operator needs two floats of one type, found {} and {}",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
        }
    }
    /// Both operands must be the same integer type.
    fn same_int(&self, left: Type, right: Type, span: Span) -> Result<Type> {
        let left_kind = left.int_kind();
        let right_kind = right.int_kind();
        match (left, right, left_kind, right_kind) {
            (Type::Never, other, _, _) | (other, Type::Never, _, _) => {
                Ok(if other == Type::Never {
                    Type::I64
                } else {
                    other
                })
            }
            (_, _, Some(a), Some(b)) if a == b => Ok(left),
            (_, _, Some(_), Some(_)) => Err(Diagnostic::new(
                span,
                format!(
                    "integer operands must have the same type, found {} and {}; convert one with Int.convert, Int.try_convert, or Int.truncate",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
            _ => Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: this operator needs integer operands, found {} and {}",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
        }
    }
    /// `(a, b, ...)`: elements are evaluated left to right, in layout order.
    /// If an element diverges, later source elements are unreachable and are
    /// not checked: a `return` or `?` in an earlier field must not make a later
    /// field's obligations look reachable.
    fn tuple_value(
        &mut self,
        values: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if let Some(expected) = expected
            && let Some(layout) = expected.layout().filter(|id| self.types.enums[*id].tuple)
        {
            let arity = self.types.enums[layout].arguments.len();
            if arity != values.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "tuple expression has {} elements, but the expected tuple type has {}",
                        values.len(),
                        arity
                    ),
                ));
            }
        }
        let candidates = self.expected_tuple_elements(expected, values.len());
        if candidates.len() > 1 {
            let mut accepted = Vec::new();
            let mut first_error = None;
            for candidate in &candidates {
                let mut fields = Vec::with_capacity(values.len());
                let mut failed = None;
                for (index, value) in values.iter().enumerate() {
                    match self.expr_expected(value, Some(candidate[index])) {
                        Ok(value) => match self.coerce(value, candidate[index], span) {
                            Ok(value) => fields.push(value),
                            Err(error) => {
                                failed = Some(error);
                                break;
                            }
                        },
                        Err(error) => {
                            failed = Some(error);
                            break;
                        }
                    }
                }
                if failed.is_none() {
                    accepted.push((candidate.clone(), fields));
                } else if first_error.is_none() {
                    first_error = failed;
                }
            }
            let (elements, fields) = match accepted.len() {
                1 => accepted.pop().expect("one accepted tuple alternative"),
                0 => {
                    return Err(
                        first_error.expect("a tuple literal candidate always attempts one element")
                    );
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this tuple literal fits several union alternatives; add an explicit annotation",
                    ));
                }
            };
            let ty = self.types.tuple(elements, span)?;
            let value = Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().unwrap(),
                    tag: 0,
                    fields,
                },
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let wanted = candidates.into_iter().next();
        let mut fields = Vec::with_capacity(values.len());
        for (index, value) in values.iter().enumerate() {
            let hint = wanted.as_ref().map(|w| w[index]);
            let value = self.expr_expected(value, hint)?;
            if value.ty == Type::Never {
                fields.push(value);
                return Ok(Expr {
                    kind: ExprKind::Block(Block {
                        statements: fields.into_iter().map(Statement::Expr).collect(),
                        tail: None,
                        ty: Type::Never,
                    }),
                    ty: Type::Never,
                    span,
                    resource: None,
                });
            }
            let value = match &wanted {
                Some(elements) => {
                    let span = value.span;
                    self.coerce(value, elements[index], span)?
                }
                None => value,
            };
            fields.push(value);
        }
        let elements = match wanted {
            Some(elements) => elements,
            None => fields
                .iter()
                .map(|field| self.types.full(field.ty, field.span))
                .collect::<Result<Vec<_>>>()?,
        };
        let ty = self.types.tuple(elements, span)?;
        let value = Expr {
            kind: ExprKind::Construct {
                enum_id: ty.layout().unwrap(),
                tag: 0,
                fields,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Element hints from an expected tuple type, or from the unique tuple
    /// alternative of an expected union with the same arity. An ambiguous
    /// union deliberately supplies no hints: each element stays independently
    /// typed and the whole tuple is injected into the union afterwards.
    fn expected_tuple_elements(&self, expected: Option<Type>, arity: usize) -> Vec<Vec<Type>> {
        let elements = |ty: Type| {
            ty.layout()
                .filter(|id| {
                    self.types.enums[*id].tuple && self.types.enums[*id].arguments.len() == arity
                })
                .map(|id| self.types.enums[id].arguments.clone())
        };
        match expected {
            Some(Type::Union(id)) => self.types.unions[id]
                .members
                .iter()
                .filter_map(|member| elements(*member))
                .collect(),
            Some(ty) => elements(ty).into_iter().collect(),
            None => Vec::new(),
        }
    }
    /// Every concrete effect bit in this program: the four built-ins plus each
    /// declared `effect` operation's row bit.
    fn all_effects(&self) -> u16 {
        EFFECT_BITS
            | self
                .resolution
                .effect_bits
                .values()
                .copied()
                .fold(0u16, |bits, bit| bits | bit)
    }
    /// Row bit of a declared effect operation, or zero for an undeclared
    /// lexically handled operation name.
    fn operation_effect(&self, operation: &str) -> u16 {
        self.resolution
            .effect_bits
            .get(operation)
            .copied()
            .unwrap_or(0)
    }
    fn require(&self, effects: u16, span: Span) -> Result<()> {
        self.required_effects
            .set(self.required_effects.get() | effects);
        let missing = effects & !self.effects;
        if missing == 0 {
            return Ok(());
        }
        let mut names = [(IO, "io"), (ALLOC, "alloc"), (SUSPEND, "suspend")]
            .into_iter()
            .filter_map(|(bit, name)| (missing & bit != 0).then_some(name.to_owned()))
            .collect::<Vec<_>>();
        names.extend(crate::runtime_types::user_effect_names(
            self.resolution,
            missing,
        ));
        Err(Diagnostic::new(
            span,
            format!(
                "operation requires effects {{{}}}; add them to the function signature",
                names.join(", ")
            ),
        ))
    }
    fn ty(&mut self, ty: &ast::Type) -> Result<Type> {
        reject_capability_type(ty)?;
        if matches!(ty.kind, ast::TypeKind::Infer) {
            return self
                .lambda_holes
                .get(&(ty.span.start, ty.span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(
                        ty.span,
                        "cannot infer this lambda type: no expected function type, generic call, or first use fixes it; add the annotation",
                    )
                });
        }
        let subst = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
            lengths: BTreeMap::new(),
        };
        let lowered = self.types.ty_in(ty, &subst)?;
        self.check_runtime_lengths(ty)?;
        Ok(lowered)
    }
    /// The local slot of a runtime-length binder. The binder must be an
    /// immutable `i64` parameter or local in scope, so the value the type
    /// describes can never change.
    fn runtime_length_slot(&self, binder: BindingId, span: Span) -> Result<usize> {
        let error = || {
            Diagnostic::new(
                span,
                format!(
                    "the length '{}' of a runtime-length array must be an immutable i64 parameter or local in scope",
                    self.resolution.bindings[binder].name
                ),
            )
        };
        let slot = *self.slots.get(&binder).ok_or_else(error)?;
        let local = &self.locals[slot];
        if local.ty != Type::I64 || local.mutable {
            return Err(error());
        }
        Ok(slot)
    }
    /// Validate every runtime-length binder written in an annotation in this
    /// body. Binders that arrive through a generic substitution were checked
    /// where the caller wrote them. A written callable type cannot carry one:
    /// an indirect call cannot substitute the caller's binder.
    fn check_runtime_lengths(&self, ty: &ast::Type) -> Result<()> {
        fn walk(checker: &Checker<'_, '_>, ty: &ast::Type, in_callable: bool) -> Result<()> {
            match &ty.kind {
                ast::TypeKind::Array(element, length) => {
                    if let Some((binder, _)) = runtime_length_parts(length) {
                        if in_callable {
                            return Err(Diagnostic::new(
                                ty.span,
                                "fn/once fn types and lambdas cannot mention a runtime-length array [T; n <= C]; call a named function instead",
                            ));
                        }
                        let id = runtime_length_binder(checker.resolution, binder)?;
                        checker.runtime_length_slot(id, binder.span)?;
                    }
                    walk(checker, element, in_callable)
                }
                ast::TypeKind::Named { arguments, .. } => {
                    for argument in arguments {
                        walk(checker, argument, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Tuple(items) => {
                    for item in items {
                        walk(checker, item, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Dyn(bounds) => {
                    for inner in ast::dyn_types(bounds) {
                        walk(checker, inner, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Slice(inner)
                | ast::TypeKind::Borrow { inner, .. }
                | ast::TypeKind::Graded { inner, .. } => walk(checker, inner, in_callable),
                ast::TypeKind::Structural { fields, .. } => {
                    for field in fields {
                        walk(checker, &field.ty, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Binary { left, right, .. } => {
                    walk(checker, left, in_callable)?;
                    walk(checker, right, in_callable)
                }
                ast::TypeKind::Function {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        walk(checker, &parameter.ty, true)?;
                    }
                    walk(checker, result, true)
                }
                _ => Ok(()),
            }
        }
        walk(self, ty, false)
    }
    /// A slice pattern over a shared `&DynArray<T, C>` (or `&[T; n <= C]`)
    /// scrutinee. Element names bind `&T` into the array's slots, so owning
    /// elements are matched without moving or copying them; `..rest` binds a
    /// `&[T]` view of the middle. Copyable elements may also use ordinary
    /// by-value sub-patterns, which test copies.
    ///
    /// Over an exclusive `&mut` scrutinee, element names bind `&mut T` and
    /// `..rest` binds `&mut [T]`. Each such binding gets its own split group,
    /// so the bindings are pairwise disjoint loans of the array. Like
    /// `&mut s[i]`, this requires non-owning, non-linear, non-view elements.
    fn borrowed_dyn_pattern(
        &mut self,
        parts: &[ast::Pattern],
        element: Type,
        capacity: usize,
        exclusive: bool,
        span: Span,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        let copyable =
            !(self.owned_type(element) || self.linear_type(element) || element.is_view());
        if exclusive && (!copyable || element.is_ref()) {
            return Err(Diagnostic::new(
                span,
                "a '&mut DynArray' pattern binds '&mut T' element references, which would alias an owning, linear, or view element; match a shared borrow instead, or move elements out with DynArray.pop",
            ));
        }
        let element_pointer = self.types.pointer(element);
        let (reference, view) = if exclusive {
            (
                Type::RefMut(element_pointer),
                Type::SliceMut(element_pointer),
            )
        } else {
            (Type::Ref(element_pointer), Type::Slice(element_pointer))
        };
        let mut prefix = Vec::new();
        let mut suffix = Vec::new();
        let mut rest = false;
        let mut rest_binding = None;
        let mut exclusive_slots = BTreeSet::new();
        let bind = |checker: &mut Self,
                    name: &str,
                    ty: Type,
                    part: &ast::Pattern,
                    bindings: &mut BTreeMap<String, (usize, Type)>,
                    exclusive_slots: &mut BTreeSet<usize>|
         -> Result<usize> {
            if let Some((slot, previous)) = bindings.get(name) {
                // Two exclusive references to different elements cannot share
                // one name.
                if exclusive && exclusive_slots.contains(slot) {
                    return Err(Diagnostic::new(
                        part.span,
                        format!("'{name}' is bound twice in one '&mut DynArray' pattern"),
                    ));
                }
                checker.expect(ty, *previous, part.span)?;
                return Ok(*slot);
            }
            let slot = checker.bind(part.span, ty, false)?;
            bindings.insert(name.to_owned(), (slot, ty));
            exclusive_slots.insert(slot);
            Ok(slot)
        };
        for part in parts {
            let checked = match &part.kind {
                ast::PatternKind::Rest(name) => {
                    if rest {
                        return Err(Diagnostic::new(
                            part.span,
                            "a DynArray pattern may contain at most one '..'",
                        ));
                    }
                    rest = true;
                    if let Some(name) = name {
                        if !copyable {
                            return Err(Diagnostic::new(
                                part.span,
                                "a borrowed DynArray pattern cannot bind '..name' over owning, linear, or view elements: a '&[T]' view of them has no checked operations; use '..' and bind the elements you need",
                            ));
                        }
                        rest_binding = Some(bind(
                            self,
                            name,
                            view,
                            part,
                            bindings,
                            &mut exclusive_slots,
                        )?);
                    }
                    continue;
                }
                ast::PatternKind::Wildcard => Pattern::Any,
                ast::PatternKind::Name(path)
                    if path.len() == 1 && !self.is_constructor_pattern(part) =>
                {
                    Pattern::Bind(bind(
                        self,
                        &path[0],
                        reference,
                        part,
                        bindings,
                        &mut exclusive_slots,
                    )?)
                }
                _ if copyable => self.pattern(part, element, bindings)?,
                _ => {
                    return Err(Diagnostic::new(
                        part.span,
                        "a borrowed DynArray pattern over owning, linear, or view elements supports only element names (bound as '&T'), '_', and '..'",
                    ));
                }
            };
            if rest {
                suffix.push(checked);
            } else {
                prefix.push(checked);
            }
        }
        if prefix.len() + suffix.len() > capacity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "DynArray pattern has {} element(s) but the capacity is {capacity}",
                    prefix.len() + suffix.len()
                ),
            ));
        }
        // One split group per exclusive binding; see `Pattern::DynArray`.
        let exclusive = exclusive.then(|| {
            let base = self.next_split;
            self.next_split += prefix
                .iter()
                .chain(&suffix)
                .filter(|pattern| matches!(pattern, Pattern::Bind(_)))
                .count()
                + usize::from(rest_binding.is_some());
            base
        });
        Ok(Pattern::DynArray {
            element,
            capacity,
            prefix,
            suffix,
            rest,
            rest_binding,
            borrowed: true,
            exclusive,
        })
    }
    /// `let v = &a[..]` over a runtime-length array `[T; n <= C]` records
    /// `Slice.len(v) == n`, so `Slice.at(v, i, _)` can be proved from facts
    /// about `n`.
    fn define_view_length(&mut self, slot: usize, value: &Expr) {
        let ExprKind::Slice {
            base,
            start: None,
            end: None,
            text: false,
            ..
        } = &value.kind
        else {
            return;
        };
        let owner = match base.ty {
            Type::Ref(pointer) | Type::RefMut(pointer) => self.types.pointees[pointer],
            ty => ty,
        };
        let Some(binder) = owner
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return;
        };
        let Ok(length) = self.runtime_length_term(binder, value.span) else {
            return;
        };
        let view =
            crate::facts::Linear::variable(crate::facts::Term::Len(slot, self.facts.version(slot)));
        let mut facts = Vec::new();
        crate::facts::compare(view, &Kind::EqEq, length, &mut facts);
        self.facts.add(facts);
    }
    /// `a[i]` on a runtime-length array `[T; n <= C]` (a local or a shared
    /// reference to one). When the facts prove `0 <= i && i < n` the read is
    /// proof-based and needs no `panic` effect; otherwise it is a checked read.
    /// Both lower to the checked `DynArray` read, whose bound check cannot
    /// fire on the proved path.
    fn runtime_array_index(
        &mut self,
        base: &Expr,
        index: &ast::Expr,
        span: Span,
    ) -> Result<Option<Expr>> {
        let array_ty = match base.ty {
            Type::Ref(pointer) | Type::RefMut(pointer) => self.types.pointees[pointer],
            ty => ty,
        };
        let Some(binder) = array_ty
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return Ok(None);
        };
        let (element, _) = self.types.enums[array_ty.layout().unwrap()]
            .dynamic_array
            .expect("runtime arrays use the DynArray layout");
        let array = match (&base.kind, base.ty) {
            (ExprKind::Peek(slot), Type::Ref(_)) => Expr {
                kind: ExprKind::Local(*slot),
                ty: base.ty,
                span: base.span,
                resource: None,
            },
            // An exclusive reference is read without being moved: the read
            // reborrows it as shared for this one element copy.
            (ExprKind::Peek(slot), Type::RefMut(pointer)) => Expr {
                kind: ExprKind::Peek(*slot),
                ty: Type::Ref(pointer),
                span: base.span,
                resource: None,
            },
            (ExprKind::Peek(slot), ty) if ty == array_ty => Expr {
                kind: ExprKind::Borrow(*slot),
                ty: Type::Ref(self.types.pointer(array_ty)),
                span: base.span,
                resource: None,
            },
            _ => {
                return Err(Diagnostic::new(
                    base.span,
                    "index a runtime-length array through a local binding or a reference parameter; bind the array to a local first",
                ));
            }
        };
        if self.owned_type(element) || self.linear_type(element) || element.is_view() {
            return Err(Diagnostic::new(
                span,
                "indexing a runtime-length array copies the element, but it owns resources, is linear, or is a view",
            ));
        }
        let index = self.expr_expected(index, Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        let length = self.runtime_length_term(binder, span).ok();
        let proved = match (self.facts.linear(&index), length) {
            (Some(position), Some(length)) => self.try_prove(
                vec![
                    (
                        crate::facts::Linear::constant(0),
                        Kind::Le,
                        position.clone(),
                    ),
                    (position, Kind::Lt, length),
                ],
                "0 <= index && index < n",
                span,
            ),
            _ => false,
        };
        if !proved {
            self.require(PANIC, span)?;
        }
        let ty = if index.ty == Type::Never {
            Type::Never
        } else {
            element
        };
        Ok(Some(Expr {
            kind: ExprKind::Call(
                Target::DynArray(DynArrayOp::Get, element),
                vec![array, index],
            ),
            ty,
            span,
            resource: None,
        }))
    }
    /// `DynArray.push`/`pop` change the runtime length, which a runtime-length
    /// array's type fixes to its binder.
    fn reject_length_change(&self, ty: Type, name: &str, span: Span) -> Result<()> {
        let Some(binder) = ty
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return Ok(());
        };
        Err(Diagnostic::new(
            span,
            format!(
                "{name} would change the length of a [T; {} <= C], which always equals '{}'; use a DynArray<T, C> for a growable length",
                self.resolution.bindings[binder].name, self.resolution.bindings[binder].name
            ),
        ))
    }
    /// A lambda is called indirectly, so its signature cannot carry a
    /// runtime-length binder the call would have to substitute.
    fn reject_lambda_runtime_length(&self, ty: Type, span: Span) -> Result<()> {
        if crate::runtime_types::runtime_length_binders(self.types, ty).is_empty() {
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            "fn/once fn types and lambdas cannot mention a runtime-length array [T; n <= C]; call a named function instead",
        ))
    }
    /// The solver term for the current value of a runtime-length binder.
    fn runtime_length_term(&self, binder: BindingId, span: Span) -> Result<crate::facts::Linear> {
        let slot = self.runtime_length_slot(binder, span)?;
        Ok(crate::facts::Linear::variable(crate::facts::Term::Var(
            slot,
            self.facts.version(slot),
        )))
    }
    /// Try to prove `l op r` for every atom from the facts in scope without
    /// reporting a failure. Proved goals record checked certificates.
    /// Prove a checked `Bool` proposition (linear comparisons with `&&`,
    /// `||` and `!`) from the facts here, recording its certificate.
    fn prove_condition(&mut self, condition: &Expr, what: &str) -> Result<()> {
        let Some(goal) = self.facts.formula_exact(condition, true) else {
            return Err(Diagnostic::new(
                condition.span,
                format!("{what} must be linear comparisons of integers joined by &&, || and !"),
            ));
        };
        match self.facts.certify(&goal, condition.span, what) {
            Some(certificates) => {
                self.functions.certificates.extend(certificates);
                Ok(())
            }
            None => Err(Diagnostic::new(
                condition.span,
                format!("cannot prove {what} from what is known here"),
            )),
        }
    }
    /// PROOF-FUZZ: remember a run-time check the prover left in place.
    fn record_obligation(&mut self, kind: ObligationKind, span: Span, goal: String) {
        self.record_check(kind, span, goal, false);
    }
    /// PROOF-FUZZ: remember a check, discharged (`proved`) or left in place.
    fn record_check(&mut self, kind: ObligationKind, span: Span, goal: String, proved: bool) {
        let function = self.functions.checking;
        let function_name = self.functions.signatures[function].name.clone();
        let table = if proved {
            &mut self.functions.discharged
        } else {
            &mut self.functions.obligations
        };
        table
            .entry((function, span.start, span.end, kind))
            .or_insert(Obligation {
                kind,
                span,
                function,
                function_name,
                goal,
            });
    }
    fn record_bounds(&mut self, container: Container, length: Option<i64>, span: Span) {
        let goal = match length {
            Some(length) => format!("0 <= index && index < {length}"),
            None => "0 <= index && index < len".to_owned(),
        };
        let kind = ObligationKind::Bounds {
            container,
            refined_length: length,
        };
        self.record_obligation(kind, span, goal);
    }
    fn try_prove(
        &mut self,
        atoms: Vec<(crate::facts::Linear, Kind, crate::facts::Linear)>,
        text: &str,
        span: Span,
    ) -> bool {
        let mut goals = Vec::new();
        let mut wanted = 0;
        for (left, op, right) in atoms {
            wanted += if op == Kind::EqEq { 2 } else { 1 };
            crate::facts::compare(left, &op, right, &mut goals);
        }
        // An overflowing translation drops a goal; never treat that as proved.
        if goals.len() != wanted {
            return false;
        }
        let Some(certificates) = self.facts.certify(&vec![goals], span, text) else {
            return false;
        };
        self.functions.certificates.extend(certificates);
        true
    }
    /// The caller binding for each callee `i64` parameter that sizes a
    /// runtime-length array in the callee's signature. The actual must name an
    /// immutable `i64` binding in scope.
    fn call_runtime_lengths(
        &self,
        f: &ast::Function,
        skip: usize,
        arguments: &[ast::Expr],
    ) -> Result<BTreeMap<BindingId, BindingId>> {
        fn collect(resolution: &Resolution, ty: &ast::Type, out: &mut BTreeSet<BindingId>) {
            match &ty.kind {
                ast::TypeKind::Array(element, length) => {
                    if let Some((binder, _)) = runtime_length_parts(length)
                        && let Ok(id) = runtime_length_binder(resolution, binder)
                    {
                        out.insert(id);
                    }
                    collect(resolution, element, out);
                }
                ast::TypeKind::Borrow { inner, .. }
                | ast::TypeKind::Graded { inner, .. }
                | ast::TypeKind::Slice(inner) => collect(resolution, inner, out),
                ast::TypeKind::Named { arguments, .. } => {
                    for argument in arguments {
                        collect(resolution, argument, out);
                    }
                }
                ast::TypeKind::Tuple(items) => {
                    for item in items {
                        collect(resolution, item, out);
                    }
                }
                ast::TypeKind::Structural { fields, .. } => {
                    for field in fields {
                        collect(resolution, &field.ty, out);
                    }
                }
                ast::TypeKind::Binary { left, right, .. } => {
                    collect(resolution, left, out);
                    collect(resolution, right, out);
                }
                _ => {}
            }
        }
        let parameters = &f.parameters[skip.min(f.parameters.len())..];
        let mut binders = BTreeSet::new();
        for parameter in parameters.iter().filter(|parameter| !parameter.erased) {
            collect(self.resolution, &parameter.ty, &mut binders);
        }
        collect(self.resolution, &f.result, &mut binders);
        let mut map = BTreeMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let Some(binder) = self.resolution.binder(parameter.span) else {
                continue;
            };
            if !binders.contains(&binder) {
                continue;
            }
            let error = || {
                Diagnostic::new(
                    argument.span,
                    format!(
                        "'{}' sizes a runtime-length array in the signature of '{}'; pass the name of an immutable i64 local",
                        parameter.name, f.name
                    ),
                )
            };
            let ast::ExprKind::Name(_) = &argument.kind else {
                return Err(error());
            };
            let actual = self.resolution.reference(argument.span).ok_or_else(error)?;
            self.runtime_length_slot(actual, argument.span)?;
            map.insert(binder, actual);
        }
        Ok(map)
    }
    /// Strip an outer result-transfer grade (through transparent aliases) for
    /// call-site inference. The grade itself is validated when the concrete
    /// instance is created, so no grade variables need to be bound here.
    fn result_type_hint(&self, ty: &ast::Type) -> Result<ast::Type> {
        let expanded = expand_result_aliases(self.resolution, self.types, ty)?;
        Ok(split_grade(&expanded).0.clone())
    }
    fn mask(&self, ty: Type) -> u64 {
        crate::runtime_types::mask_of(ty, &self.types.enums)
    }
    fn pattern(
        &mut self,
        pattern: &ast::Pattern,
        ty: Type,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        self.nested(pattern.span, |c| {
            if let ast::PatternKind::Type { ty: declared, inner } = &pattern.kind {
                let requested = c.ty(declared)?;
                if requested.is_union() {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "a narrowing pattern must name one union alternative, not another union",
                    ));
                }
                let Type::Union(id) = ty else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "type patterns narrow a heterogeneous union; the scrutinee has type {}",
                            c.types.name(ty)
                        ),
                    ));
                };
                let members = c.types.unions[id].members.clone();
                let Some((tag, _member)) = members.iter().enumerate().find(|(_, member)| {
                    c.subtype(**member, requested)
                        && c.narrow_representation_compatible(**member, requested)
                }) else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "{} is not an alternative of {} that can be narrowed without a representation adapter",
                            c.types.name(requested),
                            c.types.name(ty)
                        ),
                    ));
                };
                let inner = c.pattern(inner, requested, bindings)?;
                return Ok(Pattern::Type {
                    tag,
                    member: requested,
                    inner: Box::new(inner),
                });
            }
            if let ast::PatternKind::Structural { fields, rest: _ } = &pattern.kind {
                let record_layout = |c: &Checker, ty: Type| {
                    ty.layout()
                        .filter(|layout| c.types.enums[*layout].record)
                };
                let (member, narrowed) = if let Type::Union(id) = ty {
                    let members = c.types.unions[id].members.clone();
                    let mut matches = Vec::new();
                    for (tag, member) in members.into_iter().enumerate() {
                        let Some(layout) = record_layout(c, member) else {
                            continue;
                        };
                        let variant = &c.types.enums[layout].variants[0];
                        if fields.iter().all(|(name, _)| variant.names.contains(name)) {
                            matches.push((tag, member));
                        }
                    }
                    match matches.as_slice() {
                        [] => {
                            return Err(Diagnostic::new(
                                pattern.span,
                                format!(
                                    "structural pattern does not match any record alternative of {}",
                                    c.types.name(ty)
                                ),
                            ));
                        }
                        [one] => (one.1, true),
                        _ => {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "this structural pattern matches several union alternatives; narrow with 'Type @ pattern' first",
                            ));
                        }
                    }
                } else {
                    (ty, false)
                };
                let Some(layout) = record_layout(c, member) else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "a structural pattern matches a record value, found {}",
                            c.types.name(member)
                        ),
                    ));
                };
                let variant = c.types.enums[layout].variants[0].clone();
                let mut checked = Vec::new();
                let mut offset = c.types.enums[layout].tag_words();
                for (index, field_ty) in variant.fields.iter().enumerate() {
                    let sub = fields.iter().find(|(n, _)| *n == variant.names[index]);
                    if let Some((name, p)) = sub {
                        c.check_layout_field_visible(layout, name, p.span)?;
                    }
                    let p = match sub {
                        Some((_, p)) => c.pattern(p, *field_ty, bindings)?,
                        None => Pattern::Any,
                    };
                    checked.push((offset, p));
                    offset += c.types.width(*field_ty);
                }
                if let Some((name, p)) = fields.iter().find(|(n, _)| !variant.names.contains(n)) {
                    return Err(Diagnostic::new(
                        p.span,
                        format!("record has no field '{name}'"),
                    ));
                }
                let inner = Pattern::Variant {
                    tag: 0, tagged: c.types.enums[layout].tag_words() != 0, niche: c.types.enums[layout].niche(),
                    fields: checked,
                };
                if narrowed {
                    let tag = match ty {
                        Type::Union(id) => c.types.unions[id]
                            .members
                            .iter()
                            .position(|candidate| *candidate == member)
                            .expect("narrowed member is in the union"),
                        _ => unreachable!("only a union can be narrowed here"),
                    };
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                return Ok(inner);
            }
            // Constructor, record, and array/variant patterns can narrow a
            // union directly when exactly one alternative has the right shape.
            if let Type::Union(id) = ty {
                let members = c.types.unions[id].members.clone();
                if let Some(owner) = c
                    .resolution
                    .reference(pattern.span)
                    .filter(|id| c.resolution.bindings[*id].kind == BindingKind::Constructor)
                {
                    let (owner, _) = c.types.owner(owner);
                    let found = members.iter().enumerate().find(|(_, member)| {
                        member
                            .layout()
                            .is_some_and(|layout| c.types.enums[layout].definition == owner)
                    });
                    let ambiguous = members
                        .iter()
                        .filter(|member| {
                            member
                                .layout()
                                .is_some_and(|layout| c.types.enums[layout].definition == owner)
                        })
                        .count()
                        > 1;
                    if ambiguous {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this constructor matches several union alternatives; narrow with 'Type @ pattern' first",
                        ));
                    }
                    let Some((tag, member)) = found else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this constructor's enum is not an alternative of the union scrutinee",
                        ));
                    };
                    let member = *member;
                    let inner = c.pattern(pattern, member, bindings)?;
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                if let ast::PatternKind::Record { fields, .. } = &pattern.kind {
                    let Some(definition) = c
                        .resolution
                        .reference(pattern.span)
                        .filter(|id| c.types.is_record(*id))
                    else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "expected a record type in this pattern",
                        ));
                    };
                    let found = members.iter().enumerate().find(|(_, member)| {
                        member
                            .layout()
                            .is_some_and(|layout| c.types.enums[layout].definition == definition)
                    });
                    let ambiguous = members
                        .iter()
                        .filter(|member| {
                            member.layout().is_some_and(|layout| {
                                c.types.enums[layout].definition == definition
                            })
                        })
                        .count()
                        > 1;
                    if ambiguous {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this record pattern matches several union alternatives; narrow with 'Type @ pattern' first",
                        ));
                    }
                    let Some((tag, member)) = found else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "record {} is not an alternative of {}",
                                c.resolution.bindings[definition].name,
                                c.types.name(ty)
                            ),
                        ));
                    };
                    let member = *member;
                    let inner = c.record_pattern(pattern, fields, member, bindings)?;
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                if matches!(
                    pattern.kind,
                    ast::PatternKind::Integer(_)
                        | ast::PatternKind::Bool(_)
                        | ast::PatternKind::Slice(_)
                        | ast::PatternKind::Tuple(_)
                ) {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "narrow a heterogeneous union with 'Type @ pattern' before matching a literal or array payload",
                    ));
                }
            }
            if let Some(id) = c.resolution.reference(pattern.span)
                && c.resolution.bindings[id].kind == BindingKind::Constructor
            {
                let (owner, tag) = c.types.owner(id);
                let Some(index) = ty.layout() else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "enum constructor pattern requires an enum value",
                    ));
                };
                if c.types.enums[index].definition != owner {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "pattern constructor belongs to a different enum",
                    ));
                }
                if c.mask(ty) & (1 << tag) == 0 {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "variant {} is excluded by the scrutinee type {}",
                            c.types.enums[index].variants[tag].name,
                            c.types.name(ty)
                        ),
                    ));
                }
                let variant = c.types.enums[index].variants[tag].clone();
                let fields = match &pattern.kind {
                    ast::PatternKind::Constructor { fields, .. } if variant.tuple => {
                        fields.as_slice()
                    }
                    ast::PatternKind::Name(_) if !variant.tuple => &[][..],
                    _ => {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "enum pattern payload syntax does not match the variant",
                        ));
                    }
                };
                if fields.len() != variant.fields.len() {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "wrong enum pattern payload arity",
                    ));
                }
                let mut offset = c.types.enums[index].tag_words();
                let mut checked = Vec::new();
                for (field, ty) in fields.iter().zip(variant.fields) {
                    checked.push((offset, c.pattern(field, ty, bindings)?));
                    offset += c.types.width(ty);
                }
                return Ok(Pattern::Variant {
                    tag,
                    tagged: c.types.enums[index].tag_words() != 0,
                    niche: c.types.enums[index].niche(),
                    fields: checked,
                });
            }
            if let ast::PatternKind::Slice(parts) = &pattern.kind
                && let Type::Ref(pointer) | Type::RefMut(pointer) = ty
                && let Some((element, capacity)) = c.types.pointees[pointer]
                    .layout()
                    .and_then(|id| c.types.enums[id].dynamic_array)
            {
                let exclusive = matches!(ty, Type::RefMut(_));
                return c.borrowed_dyn_pattern(
                    parts,
                    element,
                    capacity,
                    exclusive,
                    pattern.span,
                    bindings,
                );
            }
            if let ast::PatternKind::Slice(parts) = &pattern.kind {
                if let Some((element, capacity)) = ty
                    .layout()
                    .and_then(|id| c.types.enums[id].dynamic_array)
                {
                    if c.owned_type(element) || c.linear_type(element) || element.is_view() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "DynArray patterns copy element bindings; owning, linear, and view elements cannot be matched by value",
                        ));
                    }
                    let mut prefix = Vec::new();
                    let mut suffix = Vec::new();
                    let mut rest = false;
                    let mut rest_binding = None;
                    // A runtime-length array's tail has a different length, so
                    // `..rest` is a plain DynArray with the same capacity.
                    let rest_ty = if ty
                        .layout()
                        .is_some_and(|id| c.types.enums[id].runtime_length.is_some())
                    {
                        c.types.dynamic_array(element, capacity, pattern.span)?
                    } else {
                        ty
                    };
                    for part in parts {
                        if let ast::PatternKind::Rest(name) = &part.kind {
                            if rest {
                                return Err(Diagnostic::new(
                                    part.span,
                                    "a DynArray pattern may contain at most one '..'",
                                ));
                            }
                            rest = true;
                            rest_binding = match name {
                                Some(name) => {
                                    if let Some((slot, previous)) = bindings.get(name) {
                                        c.expect(rest_ty, *previous, part.span)?;
                                        Some(*slot)
                                    } else {
                                        let slot = c.bind(part.span, rest_ty, false)?;
                                        bindings.insert(name.clone(), (slot, rest_ty));
                                        Some(slot)
                                    }
                                }
                                None => None,
                            };
                            continue;
                        }
                        // Elements after the rest match the trailing slots,
                        // counted back from the runtime length.
                        if rest {
                            suffix.push(c.pattern(part, element, bindings)?);
                        } else {
                            prefix.push(c.pattern(part, element, bindings)?);
                        }
                    }
                    if prefix.len() + suffix.len() > capacity {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "DynArray pattern has {} element(s) but the capacity is {capacity}",
                                prefix.len() + suffix.len()
                            ),
                        ));
                    }
                    return Ok(Pattern::DynArray {
                        element,
                        capacity,
                        prefix,
                        suffix,
                        rest,
                        rest_binding,
                        borrowed: false,
                        exclusive: None,
                    });
                }
                let Some((element, length)) = ty.layout().and_then(|id| c.types.enums[id].array)
                else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "array pattern requires an inline array",
                    ));
                };
                if parts
                    .iter()
                    .any(|part| matches!(part.kind, ast::PatternKind::Rest(_)))
                {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "inline array patterns require an exact element count; use a DynArray for a '..' rest pattern",
                    ));
                }
                if parts.len() != length {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "array pattern length differs from its type",
                    ));
                }
                let mut fields = Vec::new();
                for (i, part) in parts.iter().enumerate() {
                    fields.push((
                        1 + i * c.types.width(element),
                        c.pattern(part, element, bindings)?,
                    ));
                }
                return Ok(Pattern::Variant { tag: 0, tagged: true, niche: None, fields });
            }
            if let ast::PatternKind::Record { fields, .. } = &pattern.kind {
                return c.record_pattern(pattern, fields, ty, bindings);
            }
            match &pattern.kind {
                ast::PatternKind::Wildcard => Ok(Pattern::Any),
                ast::PatternKind::Name(path) if path.len() == 1 => {
                    if let Some((slot, previous)) = bindings.get(&path[0]) {
                        c.expect(ty, *previous, pattern.span)?;
                        return Ok(Pattern::Bind(*slot));
                    }
                    let slot = c.bind(pattern.span, ty, false)?;
                    bindings.insert(path[0].clone(), (slot, ty));
                    Ok(Pattern::Bind(slot))
                }
                ast::PatternKind::Integer(text) => {
                    let kind = match ty.int_kind() {
                        Some(kind) => kind,
                        None => {
                            c.expect(ty, Type::I64, pattern.span)?;
                            crate::int::IntKind::I64
                        }
                    };
                    let value = text
                        .parse::<i128>()
                        .ok()
                        .and_then(|v| kind.encode(v))
                        .ok_or_else(|| {
                            Diagnostic::new(
                                pattern.span,
                                format!("pattern is outside the {} range", kind.name()),
                            )
                        })?;
                    Ok(Pattern::Literal(value))
                }
                ast::PatternKind::Char(ch) => {
                    c.expect(ty, Type::Char, pattern.span)?;
                    Ok(Pattern::Literal(i64::from(u32::from(*ch))))
                }
                ast::PatternKind::Bool(value) => {
                    c.expect(ty, Type::Bool, pattern.span)?;
                    Ok(Pattern::Literal(i64::from(*value)))
                }
                ast::PatternKind::Tuple(values) if values.len() >= 2 => {
                    let Some(layout) = ty.layout().filter(|l| c.types.enums[*l].tuple) else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("tuple pattern does not match a value of type {}", c.types.name(ty)),
                        ));
                    };
                    let elements = c.types.enums[layout].arguments.clone();
                    if elements.len() != values.len() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("tuple pattern has {} elements, but the value has {}", values.len(), elements.len()),
                        ));
                    }
                    let mut fields = Vec::new();
                    let mut offset = 1;
                    for (value, element) in values.iter().zip(elements) {
                        fields.push((offset, c.pattern(value, element, bindings)?));
                        offset += c.types.width(element);
                    }
                    Ok(Pattern::Variant { tag: 0, tagged: true, niche: None, fields })
                }
                ast::PatternKind::Tuple(values) if values.is_empty() => {
                    c.expect(ty, Type::Unit, pattern.span)?;
                    Ok(Pattern::Literal(0))
                }
                ast::PatternKind::Tuple(values) if values.len() == 1 => Err(Diagnostic::new(
                    pattern.span,
                    "one-element tuple patterns are not supported; write '()' for unit or omit the trailing comma",
                )),
                ast::PatternKind::Or(patterns) => Ok(Pattern::Or(
                    patterns
                        .iter()
                        .map(|p| c.pattern(p, ty, bindings))
                        .collect::<Result<_>>()?,
                )),
                _ => Err(Diagnostic::new(pattern.span, "unsupported runtime pattern")),
            }
        })
    }
}

/// Two branch arms that produce the same borrowed record type must agree on
/// every invariant lifetime binder. For covariant or contravariant binders a
/// different label composes by polarity; for an invariant one the labels are
/// identity, and joining both would let one arm's provenance be laundered into
/// the other's by the label-erased normalization of the joined value.
fn check_branch_record_labels(
    types: &crate::runtime_types::Types<'_>,
    left: Type,
    right: Type,
    span: Span,
) -> Result<()> {
    if branch_record_label_mismatch(types, left, right, 0, &mut BTreeSet::new()) {
        return Err(Diagnostic::new(
            span,
            format!(
                "lifetime mismatch: {} is not a lifetime-compatible {}",
                types.name(left),
                types.name(right)
            ),
        )
        .with_note(
            span,
            "one branch reinterprets the other's provenance over an invariant record lifetime",
        ));
    }
    Ok(())
}

fn branch_record_label_mismatch(
    types: &crate::runtime_types::Types<'_>,
    left: Type,
    right: Type,
    depth: usize,
    seen: &mut BTreeSet<(Type, Type)>,
) -> bool {
    if left == right {
        return false;
    }
    if depth >= 32 || !seen.insert((left, right)) {
        return false;
    }
    // A wrapper whose coercions do not reinterpret a record's provenance
    // label unwraps into the pointee comparison.
    let pointee = |types: &crate::runtime_types::Types<'_>, value: Type| -> Option<Type> {
        match value {
            Type::Box(index)
            | Type::Vec(index)
            | Type::ArenaBox(index)
            | Type::AllocBox(index)
            | Type::AllocVec(index)
            | Type::Slice(index)
            | Type::SliceMut(index)
            | Type::Ref(index)
            | Type::RefMut(index) => Some(types.pointees[index]),
            Type::Annotated(index, _) => Some(types.pointees[index]),
            _ => None,
        }
    };
    if let (Some(left_pointee), Some(right_pointee)) = (pointee(types, left), pointee(types, right))
    {
        return branch_record_label_mismatch(types, left_pointee, right_pointee, depth + 1, seen);
    }
    match (left, right) {
        (Type::Enum(a), Type::Enum(b)) if a != b => {
            let left_def = &types.enums[a];
            let right_def = &types.enums[b];
            // Any same-declaration instantiation — record or a non-record
            // enum carrying borrowed payloads — compares its erased labels:
            // the arms' provenance identities must agree, or the truncating
            // union merges one arm into the other.
            if !left_def.structural
                && !right_def.structural
                && left_def.definition == right_def.definition
            {
                // Compare slot by slot. Only a slot whose own label is
                // compiler-internal (`<...>`) is excused; one internal label
                // must not exempt every other invariant binder on the arms.
                if left_def.lifetimes.len() != right_def.lifetimes.len()
                    || left_def
                        .lifetimes
                        .iter()
                        .zip(right_def.lifetimes.iter())
                        .any(|(left_label, right_label)| {
                            left_label != right_label
                                && !left_label.starts_with('<')
                                && !right_label.starts_with('<')
                        })
                {
                    return true;
                }
                for (left_variant, right_variant) in
                    left_def.variants.iter().zip(right_def.variants.iter())
                {
                    for (left_field, right_field) in
                        left_variant.fields.iter().zip(right_variant.fields.iter())
                    {
                        if branch_record_label_mismatch(
                            types,
                            *left_field,
                            *right_field,
                            depth + 1,
                            seen,
                        ) {
                            return true;
                        }
                    }
                }
            }
            false
        }
        (Type::Union(a), Type::Union(b)) => {
            // Composing arms keep their consumed labels as a laundering
            // channel when any misaligned pair exists.
            types.unions[a].members.len() != types.unions[b].members.len()
                || types.unions[a]
                    .members
                    .iter()
                    .zip(types.unions[b].members.iter())
                    .any(|(left, right)| {
                        branch_record_label_mismatch(types, *left, *right, depth + 1, seen)
                    })
        }
        (Type::Union(a), other) | (other, Type::Union(a)) => {
            // A same-definition union member against a single arm's value:
            // every member must agree on the labels.
            types.unions[a].members.iter().any(|member| {
                let same_definition = match (member, &other) {
                    (Type::Enum(m), Type::Enum(o)) => {
                        !types.enums[*m].structural
                            && !types.enums[*o].structural
                            && types.enums[*m].definition == types.enums[*o].definition
                    }
                    _ => false,
                };
                same_definition
                    && branch_record_label_mismatch(types, *member, other, depth + 1, seen)
            })
        }
        _ => false,
    }
}

/// Variants fully matched by an irrefutable-payload pattern.
fn covered_variants(pattern: &Pattern) -> u64 {
    fn irrefutable(p: &Pattern) -> bool {
        match p {
            Pattern::Any | Pattern::Bind(_) => true,
            Pattern::Or(ps) => ps.iter().any(irrefutable),
            _ => false,
        }
    }
    match pattern {
        Pattern::Any | Pattern::Bind(_) => u64::MAX,
        Pattern::Variant { tag, fields, .. } if fields.iter().all(|(_, p)| irrefutable(p)) => {
            1 << tag
        }
        Pattern::Type { tag, .. } => 1 << tag,
        Pattern::Or(ps) => ps.iter().map(covered_variants).fold(0, |a, b| a | b),
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// Redundant-drop lint
//
// Explicit `drop(x)` is optional for affine values: the checker emits cleanup
// at the end of the declaring block anyway. The lint reports the drops whose
// removal cannot be observed:
//
// * a copyable local has no storage to release, so `drop` of one is a no-op
//   wherever it appears;
// * an owning local is reported when nothing that could allocate, perform
//   I/O, or run user code executes between the drop and the cleanup point
//   (the end of its declaring block, a `return`, or the function end), and
//   the type contains no user release hook (`AllocBox`, `AllocVec`, allocator
//   contexts, closures, task handles, dynamic objects), whose destruction can
//   run user or generated code and whose ordering an explicit drop can choose.
//
// Code that runs after the declaring block is irrelevant: the value is freed
// either way before it. That makes `drop(x); return ..;` and a drop as the last
// statement of a function or match-tail arm redundant, while an early release
// followed by more work stays.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RedundantDropKind {
    /// A copyable local: dropping it releases nothing.
    Copyable,
    /// An affine owning local dropped at its cleanup point.
    AtCleanupPoint,
}

/// How the path after a position ends, for cleanup-point analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LintRest {
    /// Inert code up to the end of this block.
    Inert,
    /// A `return` with an inert value: every scope unwinds here.
    Return,
    /// Anything else can allocate, run user code, or observe the free time.
    Blocked,
}

#[derive(Default)]
struct LintScopes {
    /// One set per open block, outermost first.
    scopes: Vec<std::collections::BTreeSet<usize>>,
    /// Per open block: whether the work after it inside every enclosing block,
    /// up to any declaring block, is inert or ends in a return.
    readiness: Vec<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RedundantDrop {
    /// Span of the `drop(...)` expression in the loaded program's source map.
    pub span: Span,
    pub kind: RedundantDropKind,
}

/// PROOF-FUZZ: obligations in source order (then by function instance).
fn sorted_obligations(
    obligations: &BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
) -> Vec<Obligation> {
    let mut out: Vec<Obligation> = obligations.values().cloned().collect();
    out.sort_by_key(|o| (o.span.start, o.span.end, o.kind, o.function));
    out
}
fn op_text(op: &Kind) -> &'static str {
    match op {
        Kind::Plus => "+",
        Kind::Minus => "-",
        Kind::Star => "*",
        Kind::Slash => "/",
        Kind::Percent => "%",
        _ => "an operator",
    }
}
/// PROOF-FUZZ: one line per obligation, `file:line:column  kind  function:
/// goal`, in source order. A check in a generic function is listed once per
/// location, however many instances it has.
pub(crate) fn obligation_report<'o>(
    sources: &crate::program::SourceMap,
    obligations: impl Iterator<Item = &'o Obligation>,
) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut sorted: Vec<&Obligation> = obligations.collect();
    sorted.sort_by_key(|o| (o.span.start, o.span.end, o.kind));
    let mut lines = Vec::new();
    for obligation in sorted {
        if !seen.insert((obligation.span.start, obligation.span.end, obligation.kind)) {
            continue;
        }
        let Some(file) = sources.file(obligation.span) else {
            continue;
        };
        let offset = obligation.span.start - file.base;
        let before = &file.text[..offset.min(file.text.len())];
        let line = before.matches('\n').count() + 1;
        let column = before.len() - before.rfind('\n').map_or(0, |at| at + 1) + 1;
        let refined = match obligation.kind {
            ObligationKind::Bounds {
                refined_length: Some(_),
                ..
            } => " (length-refined field)",
            _ => "",
        };
        lines.push(format!(
            "not proved: {}:{line}:{column} {} in {}: {}{refined}",
            file.name,
            obligation.kind.label(),
            obligation.function_name,
            obligation.goal,
        ));
    }
    lines
}

#[cfg(test)]
mod recursive_summary_mapping_tests {
    use super::*;

    fn origin(parameter: usize, path: &[&str]) -> recursive_lifetimes::Origin {
        recursive_lifetimes::Origin {
            parameter,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    #[test]
    fn a_direct_parameter_origin_maps_even_when_a_field_path_is_present() {
        let lifetime = summary_origin_lifetime(
            &origin(0, &["view"]),
            &[Some("'a".to_owned())],
            &[],
            &BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(lifetime, "'a");
    }

    #[test]
    fn a_missing_field_path_is_rejected_instead_of_dropped() {
        let error =
            summary_origin_lifetime(&origin(0, &["missing"]), &[None], &[], &BTreeMap::new())
                .unwrap_err();
        assert!(error.contains("no source binder"), "{error}");
    }

    #[test]
    fn an_unborrowed_empty_path_origin_is_rejected() {
        let error =
            summary_origin_lifetime(&origin(0, &[]), &[None], &[], &BTreeMap::new()).unwrap_err();
        assert!(error.contains("no inferred borrow lifetime"), "{error}");
    }
}
