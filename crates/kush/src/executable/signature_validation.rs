//! Validating erased parameters, runtime lengths and type templates in signatures.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Validate every erased logical parameter of a function signature, in order.
/// A parameter type is an open kernel type: it may mention checked logical
/// definitions, *earlier erased kernel binders*, and earlier immutable runtime
/// scalars (`i64`, `Bool`, `Unit`) used as symbolic indices. Runtime type
/// generics, mutable locals, grades, const naturals, and owning data never enter
/// this context. Call-site checking substitutes the actual scalar terms and
/// earlier proof terms.
pub(super) fn validate_erased_parameters(
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    f: &ast::Function,
) -> Result<()> {
    let mut bindings: Vec<(BindingId, Term)> = Vec::new();
    for parameter in &f.parameters {
        let id = resolution.binder(parameter.span).unwrap();
        if parameter.erased {
            if matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
                continue;
            }
            let term = crate::check::elaborate_type(resolution, logical, &bindings, &parameter.ty)
                .map_err(|e| {
                    Diagnostic::new(
                        e.span,
                        format!(
                            "erased parameters must be arithmetic '{{ ... }}' propositions or logical types with closed checked dependencies: {}",
                            e.message
                        ),
                    )
                })?;
            let context = bindings
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect::<Vec<_>>();
            logical.kernel.sort_open(&term, &context).map_err(|e| {
                Diagnostic::new(
                    parameter.ty.span,
                    format!("invalid erased logical parameter: {e}"),
                )
            })?;
            bindings.push((id, term));
            continue;
        }
        // A plain runtime scalar parameter is a symbolic index binder. Its type
        // must itself be an admitted machine carrier; other runtime types are
        // omitted from the kernel context so any proof mention fails loudly.
        let Ok(term) = crate::check::elaborate_type(
            resolution,
            logical,
            &bindings,
            split_grade(&parameter.ty).0,
        ) else {
            continue;
        };
        let context = bindings
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>();
        let Ok(Some(carrier)) = logical.kernel.scalar_open(&term, &context) else {
            continue;
        };
        bindings.push((id, Term::Scalar(carrier)));
    }
    Ok(())
}
/// Check array lengths in a function signature before specialization. This
/// catches unbound, type/grade, and runtime-dependent lengths even when the
/// generic function is never instantiated; concrete lengths are still checked
/// during specialization.
/// Runtime-length arrays in a signature. A parameter or result type may
/// mention `[T; n <= C]` anywhere the call site rewrites binders (references,
/// containers, tuples, arrays, records, rows, unions), where `n` is an
/// earlier `i64` parameter (any `i64` parameter for the result; never a
/// method receiver). Foreign signatures, `fn` types, and trait object types
/// may not mention them: nothing substitutes the caller's binder there.
pub(super) fn validate_runtime_length_signature(
    resolution: &Resolution,
    f: &ast::Function,
    method: bool,
) -> Result<()> {
    fn is_i64(ty: &ast::Type) -> bool {
        matches!(&split_grade(ty).0.kind, ast::TypeKind::Named { path, arguments } if path.len() == 1 && path[0] == "i64" && arguments.is_empty())
    }
    fn walk(
        resolution: &Resolution,
        ty: &ast::Type,
        allowed: &BTreeSet<BindingId>,
        restricted: Option<&'static str>,
    ) -> Result<()> {
        match &ty.kind {
            ast::TypeKind::Array(element, length) => {
                if let Some((binder, capacity)) = runtime_length_parts(length) {
                    if let Some(reason) = restricted {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!("{reason} cannot mention a runtime-length array [T; n <= C]"),
                        ));
                    }
                    let id = runtime_length_binder(resolution, binder)?;
                    if !allowed.contains(&id) {
                        return Err(Diagnostic::new(
                            binder.span,
                            "the length of a runtime-length array in a signature must be an earlier i64 parameter of the same function",
                        ));
                    }
                    walk(resolution, capacity, allowed, restricted)?;
                }
                walk(resolution, element, allowed, restricted)
            }
            ast::TypeKind::Borrow { inner, .. } => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Graded { inner, .. } => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Named { arguments, .. } => {
                for argument in arguments {
                    walk(resolution, argument, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Tuple(items) => {
                for item in items {
                    walk(resolution, item, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Slice(inner) => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Dyn(bounds) => {
                for inner in ast::dyn_types(bounds) {
                    walk(resolution, inner, allowed, Some("a trait object type"))?;
                }
                Ok(())
            }
            ast::TypeKind::Structural { fields, .. } => {
                for field in fields {
                    walk(resolution, &field.ty, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Binary { left, right, .. } => {
                walk(resolution, left, allowed, restricted)?;
                walk(resolution, right, allowed, restricted)
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                let reason = Some("a fn/once fn type");
                for parameter in parameters {
                    walk(resolution, &parameter.ty, allowed, reason)?;
                }
                walk(resolution, result, allowed, reason)
            }
            _ => Ok(()),
        }
    }
    let restricted = if f.foreign.is_some() {
        Some("a foreign function signature")
    } else {
        None
    };
    // A method receiver is never a length binder: the call site substitutes
    // binders from the explicit argument list only.
    let binders = if method {
        &f.parameters[1.min(f.parameters.len())..]
    } else {
        &f.parameters[..]
    };
    let all = binders
        .iter()
        .filter(|parameter| !parameter.erased && is_i64(&parameter.ty))
        .filter_map(|parameter| resolution.binder(parameter.span))
        .collect::<BTreeSet<_>>();
    let mut earlier = BTreeSet::new();
    for (index, parameter) in f.parameters.iter().enumerate() {
        if parameter.erased {
            continue;
        }
        walk(resolution, &parameter.ty, &earlier, restricted)?;
        if is_i64(&parameter.ty)
            && (!method || index > 0)
            && let Some(id) = resolution.binder(parameter.span)
        {
            earlier.insert(id);
        }
    }
    walk(resolution, &f.result, &all, restricted)
}

pub(super) fn validate_length_templates(resolution: &Resolution, f: &ast::Function) -> Result<()> {
    let types = f
        .parameters
        .iter()
        .filter(|parameter| !parameter.erased)
        .map(|parameter| &parameter.ty)
        .chain(std::iter::once(&f.result))
        .collect::<Vec<_>>();
    validate_type_templates_for(resolution, &f.generics, &types)
}

/// Validate array lengths and natural-const usage in a signature or data
/// declaration before any specialization. Concrete lengths are still checked
/// when an instance is created.
pub(crate) fn validate_type_templates_for(
    resolution: &Resolution,
    generics: &[ast::Generic],
    types: &[&ast::Type],
) -> Result<()> {
    let consts = generics
        .iter()
        .filter(|generic| is_const_generic(resolution, generic))
        .map(|generic| resolution.binder(generic.span).unwrap())
        .collect::<BTreeSet<_>>();
    for ty in types {
        validate_type_template(resolution, ty, &consts, false, false)?;
    }
    Ok(())
}

pub(super) fn validate_type_template(
    resolution: &Resolution,
    ty: &ast::Type,
    consts: &BTreeSet<BindingId>,
    in_length: bool,
    as_argument: bool,
) -> Result<()> {
    match &ty.kind {
        ast::TypeKind::Array(element, length) => {
            validate_type_template(resolution, element, consts, false, false)?;
            if let Some((binder, capacity)) = runtime_length_parts(length) {
                runtime_length_binder(resolution, binder)?;
                return validate_length_template(resolution, capacity, consts);
            }
            validate_length_template(resolution, length, consts)
        }
        ast::TypeKind::Dyn(bounds) => {
            for inner in ast::dyn_types(bounds) {
                validate_type_template(resolution, inner, consts, false, true)?;
            }
            Ok(())
        }
        ast::TypeKind::Named { arguments, .. } => {
            if let Some(id) = resolution.reference(ty.span) {
                let binding = &resolution.bindings[id];
                if binding.kind == BindingKind::Generic {
                    if in_length && !consts.contains(&id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "array length parameter '{}' must be a compile-time natural ('N: Nat'), not a type or grade parameter",
                                binding.name
                            ),
                        ));
                    }
                    if !in_length && !as_argument && consts.contains(&id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "natural const parameter '{}' is not a runtime type; use it only as an array length or compile-time index",
                                binding.name
                            ),
                        ));
                    }
                }
                if in_length && matches!(binding.kind, BindingKind::Parameter | BindingKind::Local)
                {
                    return Err(Diagnostic::new(
                        ty.span,
                        "array length depends on a runtime value; give a runtime-length array an inline capacity as [T; n <= C], or use Vec<T> or a &[T] view",
                    ));
                }
            }
            for argument in arguments {
                validate_type_template(resolution, argument, consts, in_length, true)?;
            }
            Ok(())
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                validate_type_template(resolution, item, consts, in_length, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Structural { fields, row, .. } => {
            for field in fields {
                validate_type_template(resolution, &field.ty, consts, false, false)?;
            }
            if let Some(row) = row {
                validate_type_template(resolution, row, consts, false, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. } => {
            validate_type_template(resolution, inner, consts, in_length, false)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                validate_type_template(resolution, &parameter.ty, consts, false, false)?;
            }
            validate_type_template(resolution, result, consts, false, false)?;
            for effect in effects {
                validate_type_template(resolution, effect, consts, false, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Binary { left, right, .. } => {
            validate_type_template(resolution, left, consts, in_length, false)?;
            validate_type_template(resolution, right, consts, in_length, false)
        }
        ast::TypeKind::Predicate(_) => Ok(()),
        ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. } => Ok(()),
        ast::TypeKind::Integer(_) | ast::TypeKind::Bool(_) => Ok(()),
    }
}

/// Whether a written type mentions a runtime-length array `[T; n <= C]`
/// anywhere.
pub(crate) fn type_mentions_runtime_length(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::Array(element, length) => {
            runtime_length_parts(length).is_some() || type_mentions_runtime_length(element)
        }
        ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Slice(inner) => type_mentions_runtime_length(inner),
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_mentions_runtime_length),
        ast::TypeKind::Named { arguments, .. } => {
            arguments.iter().any(type_mentions_runtime_length)
        }
        ast::TypeKind::Tuple(items) => items.iter().any(type_mentions_runtime_length),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| type_mentions_runtime_length(&field.ty))
                || row.as_deref().is_some_and(type_mentions_runtime_length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_runtime_length(left) || type_mentions_runtime_length(right)
        }
        ast::TypeKind::Function {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_runtime_length(&parameter.ty))
                || type_mentions_runtime_length(result)
        }
        _ => false,
    }
}

/// Split the length of a runtime-length array `[T; n <= C]` into the binder
/// expression `n` and the compile-time capacity `C`.
pub(crate) fn runtime_length_parts(length: &ast::Type) -> Option<(&ast::Type, &ast::Type)> {
    match &length.kind {
        ast::TypeKind::Binary {
            op: Kind::Le,
            left,
            right,
        } => Some((left, right)),
        _ => None,
    }
}

/// Resolve the length binder of `[T; n <= C]`. It must be a plain name of a
/// runtime parameter or local; whether it is an immutable `i64` is checked
/// where the binding's type is known.
pub(crate) fn runtime_length_binder(
    resolution: &Resolution,
    binder: &ast::Type,
) -> Result<BindingId> {
    let error = || {
        Diagnostic::new(
            binder.span,
            "the length of [T; n <= C] must be the name of an immutable i64 parameter or local",
        )
    };
    let ast::TypeKind::Named { path, arguments } = &binder.kind else {
        return Err(error());
    };
    if path.len() != 1 || !arguments.is_empty() {
        return Err(error());
    }
    let id = resolution.reference(binder.span).ok_or_else(error)?;
    if !matches!(
        resolution.bindings[id].kind,
        BindingKind::Parameter | BindingKind::Local
    ) {
        return Err(error());
    }
    Ok(id)
}

pub(super) fn validate_length_template(
    resolution: &Resolution,
    ty: &ast::Type,
    consts: &BTreeSet<BindingId>,
) -> Result<()> {
    validate_type_template(resolution, ty, consts, true, false)
}

/// Whether a surface type mentions a particular binding. Used to decide whether
/// a runtime scalar must be frozen as a symbolic kernel index at a call: an
/// unrelated scalar argument keeps its ordinary evaluation.
pub(super) fn type_references_binding(
    resolution: &Resolution,
    ty: &ast::Type,
    id: BindingId,
) -> bool {
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } => {
            resolution.reference(ty.span) == Some(id)
                || arguments
                    .iter()
                    .any(|argument| type_references_binding(resolution, argument, id))
        }
        ast::TypeKind::Tuple(items) => items
            .iter()
            .any(|item| type_references_binding(resolution, item, id)),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| type_references_binding(resolution, &field.ty, id))
                || row
                    .as_ref()
                    .is_some_and(|row| type_references_binding(resolution, row, id))
        }
        ast::TypeKind::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_references_binding(resolution, inner, id))
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. } => type_references_binding(resolution, inner, id),
        ast::TypeKind::Array(element, length) => {
            type_references_binding(resolution, element, id)
                || type_references_binding(resolution, length, id)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_references_binding(resolution, &parameter.ty, id))
                || type_references_binding(resolution, result, id)
                || effects
                    .iter()
                    .any(|effect| type_references_binding(resolution, effect, id))
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_references_binding(resolution, left, id)
                || type_references_binding(resolution, right, id)
        }
        ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. }
        | ast::TypeKind::Predicate(_) => false,
    }
}
