//! Generic and blanket impls: header patterns, matching, overlap and specialization.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Validate that a generic impl's self type or trait argument is a first-order
/// pattern over its declared type parameters and nominal types. Borrows,
/// slices, function arrows, aliases, and associated projections cannot appear in
/// an impl header: their runtime representation would make coherence depend on
/// an unresolved lifetime or expansion.
pub(super) fn validate_impl_pattern(
    resolution: &Resolution,
    types: &Types<'_>,
    pattern: &ast::Type,
    generics: &BTreeSet<BindingId>,
    const_binders: &BTreeSet<BindingId>,
    what: &str,
) -> Result<()> {
    match &pattern.kind {
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2 {
                return Err(Diagnostic::new(
                    pattern.span,
                    format!(
                        "an impl {what} may not contain the associated projection '{}'; write the impl parameter or a nominal type",
                        path.join(".")
                    ),
                ));
            }
            let id = resolution.reference(pattern.span).ok_or_else(|| {
                Diagnostic::new(pattern.span, format!("impl {what} did not resolve"))
            })?;
            let binding = &resolution.bindings[id];
            match binding.kind {
                BindingKind::Generic | BindingKind::Parameter => {
                    if !generics.contains(&id) {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "impl {what} names '{}', which is not one of this impl's parameters",
                                binding.name
                            ),
                        ));
                    }
                    if !arguments.is_empty() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "an impl type parameter cannot take type arguments",
                        ));
                    }
                }
                BindingKind::Builtin | BindingKind::Data => {}
                BindingKind::Alias => {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "transparent aliases are not supported in generic impl headers; write the expanded nominal type",
                    ));
                }
                _ => {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!("'{}' cannot appear in a generic impl header", binding.name),
                    ));
                }
            }
            for argument in arguments {
                validate_impl_pattern(resolution, types, argument, generics, const_binders, what)?;
            }
            Ok(())
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                validate_impl_pattern(resolution, types, item, generics, const_binders, what)?;
            }
            Ok(())
        }
        ast::TypeKind::Array(element, length) => {
            validate_impl_pattern(resolution, types, element, generics, const_binders, what)?;
            // A header length may be a literal or a bare natural parameter.
            // Arithmetic would make declaration-time coherence depend on an
            // evaluator, so it is rejected here and must be written into the
            // trait arguments or a concrete array length instead.
            let simple = matches!(length.kind, ast::TypeKind::Integer(_))
                || pattern_binder(resolution, length).is_some_and(|id| const_binders.contains(&id));
            if !simple {
                return Err(Diagnostic::new(
                    length.span,
                    "an impl header array length must be an integer literal or a natural parameter",
                ));
            }
            validate_length_template(resolution, length, const_binders)?;
            Ok(())
        }
        ast::TypeKind::Integer(_) | ast::TypeKind::Bool(_) => Ok(()),
        ast::TypeKind::Structural { fields, open, row } => {
            if let Some(row) = row {
                // An open-row impl header is monomorphized per concrete
                // residual row. It must name a declared impl parameter, and
                // the tail participates in coherence exactly like a nominal
                // pattern variable.
                let Some(binder) = resolution.reference(row.span) else {
                    return Err(Diagnostic::new(
                        row.span,
                        format!(
                            "an impl {what} row tail must name a declared impl parameter, as in 'impl<r> Trait for struct {{ x: i64, ..r }}'"
                        ),
                    ));
                };
                if !generics.contains(&binder) {
                    return Err(Diagnostic::new(
                        row.span,
                        format!(
                            "row tail '{}' is not an impl parameter of this header",
                            resolution.bindings[binder].name
                        ),
                    ));
                }
            } else if *open {
                return Err(Diagnostic::new(
                    pattern.span,
                    format!(
                        "an impl {what} cannot use an unnamed open row ('..'); name a row parameter, as in 'impl<r> Trait for struct {{ x: i64, ..r }}'"
                    ),
                ));
            }
            for field in fields {
                validate_impl_pattern(resolution, types, &field.ty, generics, const_binders, what)?;
            }
            Ok(())
        }
        ast::TypeKind::Dyn(_) => Err(Diagnostic::new(
            pattern.span,
            format!("an impl {what} may not be a trait object; name the concrete receiver"),
        )),
        ast::TypeKind::Borrow { .. }
        | ast::TypeKind::Slice(_)
        | ast::TypeKind::Function { .. }
        | ast::TypeKind::Graded { .. }
        | ast::TypeKind::Binary { .. }
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::Predicate(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. } => Err(Diagnostic::new(
            pattern.span,
            format!(
                "an impl {what} must be an owned nominal type pattern built from the impl's type parameters; borrows, slices, arrows, unions, grades, lifetimes, predicates, and 'Self' are not supported (searched {})",
                types.name(Type::Unit)
            ),
        )),
    }
}
/// The binder of a bare type parameter pattern, if `ty` is one.
pub(super) fn pattern_binder(resolution: &Resolution, ty: &ast::Type) -> Option<BindingId> {
    let ast::TypeKind::Named { path, arguments } = &ty.kind else {
        return None;
    };
    if path.len() != 1 || !arguments.is_empty() {
        return None;
    }
    let id = resolution.reference(ty.span)?;
    (resolution.bindings[id].kind == BindingKind::Generic).then_some(id)
}
/// Bindings produced by matching one impl header pattern. Type, natural,
/// grade, and effect parameters are solved together because a single header may
/// mention all four categories while its receiver and trait arguments must agree
/// on each binding.
#[derive(Debug, Clone, Default)]
pub(super) struct PatternBindings {
    pub(super) types: BTreeMap<BindingId, Type>,
    pub(super) consts: BTreeMap<BindingId, usize>,
    pub(super) grades: BTreeMap<BindingId, Grade>,
    pub(super) effects: BTreeMap<BindingId, u16>,
}
impl PatternBindings {
    pub(super) fn subst(&self) -> crate::runtime_types::Subst {
        crate::runtime_types::Subst {
            types: self.types.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effects.clone(),
            ..Default::default()
        }
    }
}
/// Whether a pattern still contains a generic binder absent from `bindings`.
pub(super) fn pattern_has_unbound(
    resolution: &Resolution,
    ty: &ast::Type,
    bindings: &PatternBindings,
) -> bool {
    if let Some(id) = pattern_binder(resolution, ty) {
        return !bindings.types.contains_key(&id);
    }
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => arguments
            .iter()
            .any(|argument| pattern_has_unbound(resolution, argument, bindings)),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| pattern_has_unbound(resolution, &field.ty, bindings))
                || row
                    .as_ref()
                    .is_some_and(|row| pattern_has_unbound(resolution, row, bindings))
        }
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            pattern_has_unbound(resolution, inner, bindings)
        }
        ast::TypeKind::Borrow { inner, .. } => pattern_has_unbound(resolution, inner, bindings),
        ast::TypeKind::Array(inner, length) => {
            pattern_has_unbound(resolution, inner, bindings)
                || pattern_has_unbound(resolution, length, bindings)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            pattern_has_unbound(resolution, left, bindings)
                || pattern_has_unbound(resolution, right, bindings)
        }
        _ => false,
    }
}
/// Match one compile-time natural pattern (an array length or a `Nat` trait
/// argument). A bare unbound natural binder captures `actual`; any other
/// pattern must evaluate to that exact natural under the bindings already
/// solved.
pub(super) fn match_const_pattern(
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    pattern: &ast::Type,
    actual: usize,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.consts.get(&id) {
            return Ok(*existing == actual);
        }
        bindings.consts.insert(id, actual);
        return Ok(true);
    }
    let subst = bindings.subst();
    let expected = crate::length::eval_type(resolution, logical, &subst.consts, pattern)?;
    Ok(expected == actual)
}
/// Match one grade pattern (a `Grade` trait argument). A bare unbound grade
/// binder captures `actual`; any other pattern must evaluate to that grade under
/// the bindings already solved.
pub(super) fn match_grade_pattern(
    resolution: &Resolution,
    pattern: &ast::Type,
    actual: Grade,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.grades.get(&id) {
            return Ok(*existing == actual);
        }
        bindings.grades.insert(id, actual);
        return Ok(true);
    }
    let grades = crate::grades::evaluate(resolution, &bindings.grades, pattern)?;
    Ok(grades == actual)
}
/// First-order match of an impl type pattern against a concrete runtime type.
pub(super) fn match_type_pattern(
    resolution: &Resolution,
    types: &mut Types<'_>,
    pattern: &ast::Type,
    actual: Type,
    bindings: &mut PatternBindings,
    depth: usize,
) -> Result<bool> {
    if depth >= 64 {
        return Err(Diagnostic::new(
            pattern.span,
            "generic impl matching exceeded its nesting budget",
        ));
    }
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.types.get(&id) {
            return Ok(*existing == actual);
        }
        if actual == Type::Never
            || actual.is_view()
            || matches!(actual, Type::Ref(_) | Type::RefMut(_))
        {
            return Ok(false);
        }
        bindings.types.insert(id, actual.full());
        return Ok(true);
    }
    if !pattern_has_unbound(resolution, pattern, bindings) {
        let subst = bindings.subst();
        return Ok(types.ty_in(pattern, &subst)? == actual);
    }
    match &pattern.kind {
        ast::TypeKind::Named { arguments, .. } => {
            let Some(id) = resolution.reference(pattern.span) else {
                return Ok(false);
            };
            let binding = &resolution.bindings[id];
            match (binding.kind, binding.name.as_str(), actual) {
                (BindingKind::Builtin, "Box", Type::Box(pointer))
                | (BindingKind::Builtin, "Vec", Type::Vec(pointer))
                    if arguments.len() == 1 =>
                {
                    let pointee = types.pointees[pointer];
                    match_type_pattern(
                        resolution,
                        types,
                        &arguments[0],
                        pointee,
                        bindings,
                        depth + 1,
                    )
                }
                (BindingKind::Data, _, Type::Enum(layout))
                    if types.enums[layout].definition == id =>
                {
                    let actual_arguments = types.enums[layout].arguments.clone();
                    let actual_consts = types.enums[layout].consts.clone();
                    let kinds = types.generic_kinds(id);
                    let mut actual_types = actual_arguments.iter();
                    let mut actual_consts = actual_consts.iter();
                    for (argument, is_const) in arguments.iter().zip(kinds) {
                        if is_const {
                            let Some(value) = actual_consts.next() else {
                                return Ok(false);
                            };
                            if !match_const_pattern(
                                resolution,
                                types.logical(),
                                argument,
                                *value,
                                bindings,
                            )? {
                                return Ok(false);
                            }
                        } else {
                            let Some(actual) = actual_types.next() else {
                                return Ok(false);
                            };
                            if !match_type_pattern(
                                resolution,
                                types,
                                argument,
                                *actual,
                                bindings,
                                depth + 1,
                            )? {
                                return Ok(false);
                            }
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            }
        }
        ast::TypeKind::Tuple(items) => {
            let Some(layout) = actual.layout().filter(|layout| types.enums[*layout].tuple) else {
                return Ok(false);
            };
            let elements = types.enums[layout].arguments.clone();
            if elements.len() != items.len() {
                return Ok(false);
            }
            for (item, element) in items.iter().zip(elements) {
                if !match_type_pattern(resolution, types, item, element, bindings, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ast::TypeKind::Structural { fields, row, .. } => {
            // Structural impl headers match an anonymous structural row.
            // Nominal records are deliberately not matched here: they keep
            // their own identity, so a structural impl cannot silently overlap
            // a nominal impl. A `..r` tail binds the residual canonical row,
            // complete with each field's erased borrow label.
            let Some(row_fields) = types.structural_row_fields(actual) else {
                return Ok(false);
            };
            if row.is_none() && row_fields.len() != fields.len() {
                return Ok(false);
            }
            for field in fields {
                let Some(actual_field) = row_fields.iter().find(|actual| actual.name == field.name)
                else {
                    return Ok(false);
                };
                if !match_type_pattern(
                    resolution,
                    types,
                    &field.ty,
                    actual_field.ty,
                    bindings,
                    depth + 1,
                )? {
                    return Ok(false);
                }
            }
            if let Some(row) = row {
                let Some(binder) = resolution.reference(row.span) else {
                    return Ok(false);
                };
                let declared = fields
                    .iter()
                    .map(|field| field.name.as_str())
                    .collect::<BTreeSet<_>>();
                let residual = row_fields
                    .into_iter()
                    .filter(|field| !declared.contains(field.name.as_str()))
                    .collect::<Vec<_>>();
                let residual = types.structural_fields(residual, row.span)?;
                if let Some(bound) = bindings.types.get(&binder).copied() {
                    if types.structural_row_fields(bound) != types.structural_row_fields(residual) {
                        return Ok(false);
                    }
                } else {
                    bindings.types.insert(binder, residual);
                }
            }
            Ok(true)
        }
        ast::TypeKind::Array(element, length) => {
            let Some(layout) = actual.layout() else {
                return Ok(false);
            };
            let Some((actual_element, actual_length)) = types.enums[layout].array else {
                return Ok(false);
            };
            Ok(
                match_const_pattern(resolution, types.logical(), length, actual_length, bindings)?
                    && match_type_pattern(
                        resolution,
                        types,
                        element,
                        actual_element,
                        bindings,
                        depth + 1,
                    )?,
            )
        }
        _ => Ok(false),
    }
}
/// Match an impl header's raw trait arguments against the concrete arguments an
/// obligation requires, by the trait's declared generic categories.
#[allow(clippy::too_many_arguments)]
pub(super) fn match_trait_argument_patterns(
    resolution: &Resolution,
    types: &mut Types<'_>,
    logical: &crate::check::LogicalEnvironment,
    generics: &[ast::Generic],
    patterns: &[ast::Type],
    required: &TraitArguments,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if patterns.len() != generics.len() {
        return Ok(false);
    }
    let (mut type_index, mut const_index, mut grade_index, mut effect_index) = (0, 0, 0, 0);
    for (generic, pattern) in generics.iter().zip(patterns) {
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let Some(actual) = required.types.get(type_index) else {
                    return Ok(false);
                };
                type_index += 1;
                if !match_type_pattern(resolution, types, pattern, *actual, bindings, 0)? {
                    return Ok(false);
                }
            }
            GenericCategory::Const => {
                let Some(actual) = required.consts.get(const_index) else {
                    return Ok(false);
                };
                const_index += 1;
                if !match_const_pattern(resolution, logical, pattern, *actual, bindings)? {
                    return Ok(false);
                }
            }
            GenericCategory::Grade => {
                let Some(actual) = required.grades.get(grade_index) else {
                    return Ok(false);
                };
                grade_index += 1;
                if !match_grade_pattern(resolution, pattern, *actual, bindings)? {
                    return Ok(false);
                }
            }
            GenericCategory::Effect => {
                let Some(actual) = required.effects.get(effect_index) else {
                    return Ok(false);
                };
                effect_index += 1;
                if let Some(id) = pattern_binder(resolution, pattern) {
                    if let Some(existing) = bindings.effects.get(&id) {
                        if *existing != *actual {
                            return Ok(false);
                        }
                    } else {
                        bindings.effects.insert(id, *actual);
                    }
                    continue;
                }
                let effects = crate::runtime_types::effect_bits_with(
                    resolution,
                    std::slice::from_ref(pattern),
                    &bindings.effects,
                )?;
                if effects != *actual {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}
/// Pack solved header bindings into the category-ordered impl argument list.
/// Missing type bindings cannot occur for a constrained header; a missing
/// const/grade binding falls back to the category identity only so diagnostics
/// stay deterministic instead of indexing out of bounds.
pub(super) fn solved_impl_arguments(
    resolution: &Resolution,
    generics: &[ast::Generic],
    bindings: &PatternBindings,
) -> ImplArguments {
    let mut out = ImplArguments::default();
    for generic in generics {
        let binder = resolution.binder(generic.span).unwrap();
        match generic_category(resolution, generic) {
            GenericCategory::Type => out
                .types
                .push(bindings.types.get(&binder).copied().unwrap_or(Type::Unit)),
            GenericCategory::Const => out
                .consts
                .push(bindings.consts.get(&binder).copied().unwrap_or(0)),
            GenericCategory::Grade => out.grades.push(
                bindings
                    .grades
                    .get(&binder)
                    .copied()
                    .unwrap_or(Grade::Finite(0)),
            ),
            GenericCategory::Effect => out
                .effects
                .push(bindings.effects.get(&binder).copied().unwrap_or(0)),
        }
    }
    out
}
/// Build the full substitution of one solved impl header: type, natural, grade,
/// and effect parameters in declaration order.
pub(super) fn impl_arguments_subst(
    resolution: &Resolution,
    generics: &[ast::Generic],
    arguments: &ImplArguments,
) -> crate::runtime_types::Subst {
    let mut out = crate::runtime_types::Subst::default();
    let (mut type_index, mut const_index, mut grade_index, mut effect_index) = (0, 0, 0, 0);
    for generic in generics {
        let Some(binder) = resolution.binder(generic.span) else {
            continue;
        };
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                if let Some(ty) = arguments.types.get(type_index) {
                    out.types.insert(binder, *ty);
                }
                type_index += 1;
            }
            GenericCategory::Const => {
                if let Some(value) = arguments.consts.get(const_index) {
                    out.consts.insert(binder, *value);
                }
                const_index += 1;
            }
            GenericCategory::Grade => {
                if let Some(value) = arguments.grades.get(grade_index) {
                    out.grades.insert(binder, *value);
                }
                grade_index += 1;
            }
            GenericCategory::Effect => {
                if let Some(value) = arguments.effects.get(effect_index) {
                    out.effects.insert(binder, *value);
                }
                effect_index += 1;
            }
        }
    }
    out
}
/// Replace a mapped binder and recursively expand its value.
pub(super) fn expand_pattern(
    resolution: &Resolution,
    ty: &ast::Type,
    map: &BTreeMap<BindingId, ast::Type>,
    depth: usize,
) -> ast::Type {
    if depth >= 64 {
        return ty.clone();
    }
    if let Some(id) = pattern_binder(resolution, ty)
        && let Some(value) = map.get(&id)
    {
        return expand_pattern(resolution, value, map, depth + 1);
    }
    let kind = match &ty.kind {
        ast::TypeKind::Named { path, arguments } => ast::TypeKind::Named {
            path: path.clone(),
            arguments: arguments
                .iter()
                .map(|argument| expand_pattern(resolution, argument, map, depth + 1))
                .collect(),
        },
        ast::TypeKind::Tuple(items) => ast::TypeKind::Tuple(
            items
                .iter()
                .map(|item| expand_pattern(resolution, item, map, depth + 1))
                .collect(),
        ),
        ast::TypeKind::Array(inner, length) => ast::TypeKind::Array(
            Box::new(expand_pattern(resolution, inner, map, depth + 1)),
            Box::new(expand_pattern(resolution, length, map, depth + 1)),
        ),
        ast::TypeKind::Borrow {
            lifetime,
            mutable,
            inner,
        } => ast::TypeKind::Borrow {
            lifetime: lifetime.clone(),
            mutable: *mutable,
            inner: Box::new(expand_pattern(resolution, inner, map, depth + 1)),
        },
        ast::TypeKind::Slice(inner) => {
            ast::TypeKind::Slice(Box::new(expand_pattern(resolution, inner, map, depth + 1)))
        }
        other => other.clone(),
    };
    ast::Type::new(kind, ty.span)
}
/// Unify two type patterns. Binders in `flexible` may be assigned; every other
/// binder is rigid and compares by identity. Used both for overlap detection
/// (both sides flexible) and specificity (only the more general side flexible).
pub(super) fn unify_ast_patterns(
    resolution: &Resolution,
    left: &ast::Type,
    right: &ast::Type,
    flexible: &BTreeSet<BindingId>,
    map: &mut BTreeMap<BindingId, ast::Type>,
    depth: usize,
) -> bool {
    if depth >= 64 {
        return false;
    }
    let left = expand_pattern(resolution, left, map, 0);
    let right = expand_pattern(resolution, right, map, 0);
    if let Some(id) = pattern_binder(resolution, &left)
        && flexible.contains(&id)
    {
        if pattern_binder(resolution, &right) == Some(id) {
            return true;
        }
        if type_references_any_binder(resolution, &right, &BTreeSet::from([id])) {
            return false;
        }
        map.insert(id, right);
        return true;
    }
    if let Some(id) = pattern_binder(resolution, &right)
        && flexible.contains(&id)
    {
        if type_references_any_binder(resolution, &left, &BTreeSet::from([id])) {
            return false;
        }
        map.insert(id, left);
        return true;
    }
    match (&left.kind, &right.kind) {
        (
            ast::TypeKind::Named {
                arguments: left_arguments,
                ..
            },
            ast::TypeKind::Named {
                arguments: right_arguments,
                ..
            },
        ) => {
            if resolution.reference(left.span) != resolution.reference(right.span)
                || left_arguments.len() != right_arguments.len()
            {
                return false;
            }
            left_arguments
                .iter()
                .zip(right_arguments)
                .all(|(left, right)| {
                    unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
                })
        }
        (ast::TypeKind::Tuple(left), ast::TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
                })
        }
        (
            ast::TypeKind::Structural {
                fields: left,
                row: left_row,
                ..
            },
            ast::TypeKind::Structural {
                fields: right,
                row: right_row,
                ..
            },
        ) => {
            // Structural rows are canonical by field name. Common fields must
            // unify; a row tail can absorb every field the other header names.
            // With two named rows their tails are left flexible, which is
            // exactly the overlap relation needed for coherence.
            // A row tail absorbs fields only when its variable is flexible: the
            // general header's tail may stand for fields of the specific one,
            // but a rigid (specific) tail cannot invent fields the general
            // header names. Without this, `{x, y}` would "subsume" `{x, ..r}`
            // and genuine specializations were reported as duplicates.
            let absorbable = |holder: &Option<Box<ast::Type>>| {
                holder.as_deref().is_some_and(|row| {
                    pattern_binder(resolution, row).is_some_and(|id| flexible.contains(&id))
                })
            };
            for left_field in left {
                match right
                    .iter()
                    .find(|right_field| right_field.name == left_field.name)
                {
                    Some(right_field) => {
                        if !unify_ast_patterns(
                            resolution,
                            &left_field.ty,
                            &right_field.ty,
                            flexible,
                            map,
                            depth + 1,
                        ) {
                            return false;
                        }
                    }
                    None if absorbable(right_row) => {}
                    None => return false,
                }
            }
            for right_field in right {
                if left
                    .iter()
                    .any(|left_field| left_field.name == right_field.name)
                {
                    continue;
                }
                if !absorbable(left_row) {
                    return false;
                }
            }
            true
        }
        (
            ast::TypeKind::Array(left_element, left_length),
            ast::TypeKind::Array(right_element, right_length),
        ) => {
            unify_ast_patterns(
                resolution,
                left_element,
                right_element,
                flexible,
                map,
                depth + 1,
            ) && type_key(left_length) == type_key(right_length)
        }
        (
            ast::TypeKind::Borrow {
                mutable: left_mutable,
                inner: left_inner,
                ..
            },
            ast::TypeKind::Borrow {
                mutable: right_mutable,
                inner: right_inner,
                ..
            },
        ) => {
            left_mutable == right_mutable
                && unify_ast_patterns(
                    resolution,
                    left_inner,
                    right_inner,
                    flexible,
                    map,
                    depth + 1,
                )
        }
        (ast::TypeKind::Slice(left), ast::TypeKind::Slice(right)) => {
            unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
        }
        _ => type_key(&left) == type_key(&right),
    }
}
/// Whether `general` can produce `specific`: every parameter of `general` is
/// flexible, every parameter of `specific` is rigid.
pub(super) fn header_subsumes(
    resolution: &Resolution,
    general: &ImplHeader,
    specific: &ImplHeader,
) -> bool {
    let flexible = header_binders(resolution, general);
    let mut map = BTreeMap::new();
    if !unify_ast_patterns(
        resolution,
        &general.self_ty,
        &specific.self_ty,
        &flexible,
        &mut map,
        0,
    ) {
        return false;
    }
    general
        .trait_arguments
        .iter()
        .zip(&specific.trait_arguments)
        .all(|(general, specific)| {
            unify_ast_patterns(resolution, general, specific, &flexible, &mut map, 0)
        })
        && general.trait_arguments.len() == specific.trait_arguments.len()
}
/// Whether two impl headers can apply to one receiver and specialization.
pub(super) fn headers_overlap(
    resolution: &Resolution,
    left: &ImplHeader,
    right: &ImplHeader,
) -> bool {
    let mut flexible = header_binders(resolution, left);
    flexible.extend(header_binders(resolution, right));
    let mut map = BTreeMap::new();
    if !unify_ast_patterns(
        resolution,
        &left.self_ty,
        &right.self_ty,
        &flexible,
        &mut map,
        0,
    ) {
        return false;
    }
    left.trait_arguments.len() == right.trait_arguments.len()
        && left
            .trait_arguments
            .iter()
            .zip(&right.trait_arguments)
            .all(|(left, right)| {
                unify_ast_patterns(resolution, left, right, &flexible, &mut map, 0)
            })
}
pub(super) fn impl_header_label(
    resolution: &Resolution,
    types: &Types<'_>,
    header: &ImplHeader,
) -> String {
    let trait_name = match header.trait_id {
        Some(trait_id) => {
            let name = &resolution.bindings[trait_id].name;
            if header.trait_arguments.is_empty() {
                format!("trait '{name}'")
            } else {
                let arguments = header
                    .trait_arguments
                    .iter()
                    .map(type_key)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("trait '{name}<{arguments}>'")
            }
        }
        None => "an inherent impl".to_owned(),
    };
    let receiver = match header.concrete {
        Some((_, ty)) => types.name(ty),
        None => type_key(&header.self_ty),
    };
    let prefix = if header.generics.is_empty() {
        "impl".to_owned()
    } else {
        format!(
            "impl<{}>",
            header
                .generics
                .iter()
                .map(|generic| generic.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!("{prefix} {trait_name} for {receiver}")
}
pub(super) fn header_binders(resolution: &Resolution, header: &ImplHeader) -> BTreeSet<BindingId> {
    header
        .generics
        .iter()
        .filter_map(|generic| resolution.binder(generic.span))
        .collect()
}
/// Collect one generic or blanket impl. Its methods are registered once, as
/// templates; each concrete receiver match gets a checked instance keyed by the
/// impl argument list. Associated values are supplied to that instance exactly
/// like a concrete impl's.
#[allow(clippy::too_many_arguments)]
pub(super) fn collect_generic_impl<'a>(
    span: Span,
    generics: &'a [ast::Generic],
    trait_path: Option<&ast::Type>,
    trait_id: Option<BindingId>,
    self_ty: &'a ast::Type,
    associated: &'a [ast::Associated],
    methods: &'a [ast::Method],
    default_bindings: &BTreeMap<(usize, String), BindingId>,
    resolution: &Resolution,
    types: &mut Types<'a>,
    logical: &crate::check::LogicalEnvironment,
    functions: &mut Functions<'a>,
) -> Result<Vec<BindingId>> {
    let mut generic_ids = BTreeSet::new();
    for generic in generics {
        // Every binder category is admitted. Dispatch solves a natural from an
        // array length or `Nat` trait argument, a grade from a `Grade` trait
        // argument, and an effect row from an effect argument; a parameter that
        // no pattern determines is rejected by the constrained-parameter check
        // below.
        if generic.excludes.is_some() || generic.includes.is_some() {
            return Err(Diagnostic::new(
                generic.span,
                "effect-row bounds are not supported on impl parameters",
            ));
        }
        let id = resolution
            .binder(generic.span)
            .ok_or_else(|| Diagnostic::new(generic.span, "impl parameter did not resolve"))?;
        generic_ids.insert(id);
        if let Some(bound) = &generic.bound {
            let Some(bound_id) = resolution.reference(bound.span) else {
                return Err(Diagnostic::new(
                    bound.span,
                    "impl parameter bound did not resolve",
                ));
            };
            let binding = &resolution.bindings[bound_id];
            if binding.kind == BindingKind::Builtin {
                let expected = match generic_category(resolution, generic) {
                    GenericCategory::Type => "Type",
                    GenericCategory::Const => "Nat",
                    GenericCategory::Grade => "Grade",
                    GenericCategory::Effect => "Effects",
                };
                if binding.name != expected {
                    return Err(Diagnostic::new(
                        bound.span,
                        format!(
                            "impl parameter '{}' must be bounded by '{expected}' for its category",
                            generic.name
                        ),
                    ));
                }
                continue;
            }
            if binding.kind != BindingKind::Trait {
                return Err(Diagnostic::new(
                    bound.span,
                    "impl type parameters may be bounded only by declared traits, as in 'impl<T: Show> Show for Box<T>'",
                ));
            }
            if generic_category(resolution, generic) != GenericCategory::Type {
                return Err(Diagnostic::new(
                    bound.span,
                    "only an ordinary type parameter may carry a trait bound on an impl header",
                ));
            }
            let arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.len(),
                _ => 0,
            };
            let expected = functions.traits[&bound_id].generics.len();
            if arguments != expected {
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "trait '{}' expects {expected} argument(s), found {arguments}",
                        resolution.bindings[bound_id].name
                    ),
                ));
            }
        }
    }
    let trait_definition = trait_id.and_then(|id| functions.traits.get(&id).cloned());
    let trait_methods = trait_definition
        .as_ref()
        .map(|definition| definition.methods.clone())
        .unwrap_or_default();
    let trait_generics = trait_definition
        .as_ref()
        .map(|definition| definition.generics.clone())
        .unwrap_or_default();
    let trait_associated = trait_definition
        .as_ref()
        .map(|definition| definition.associated.clone())
        .unwrap_or_default();
    let trait_argument_ast = match trait_path {
        Some(ast::Type {
            kind: ast::TypeKind::Named { arguments, .. },
            ..
        }) => arguments.clone(),
        _ => Vec::new(),
    };
    if let Some(trait_id) = trait_id
        && trait_argument_ast.len() != trait_generics.len()
    {
        let name = resolution.bindings[trait_id].name.clone();
        return Err(Diagnostic::new(
            span,
            format!(
                "trait '{name}' expects {} argument(s), found {}",
                trait_generics.len(),
                trait_argument_ast.len()
            ),
        ));
    }
    for argument in &trait_argument_ast {
        if type_mentions_self(argument) {
            return Err(Diagnostic::new(
                argument.span,
                "'Self' cannot appear in a trait's specialization arguments; write a concrete impl target or an impl type parameter",
            ));
        }
    }
    let const_binders = generics
        .iter()
        .filter(|generic| is_const_generic(resolution, generic))
        .filter_map(|generic| resolution.binder(generic.span))
        .collect::<BTreeSet<_>>();
    validate_impl_pattern(
        resolution,
        types,
        self_ty,
        &generic_ids,
        &const_binders,
        "self type",
    )?;
    for argument in &trait_argument_ast {
        validate_impl_pattern(
            resolution,
            types,
            argument,
            &generic_ids,
            &const_binders,
            "trait argument",
        )?;
    }
    // Every declared parameter must be determined by the self type or the
    // trait arguments. An unconstrained parameter would make dispatch choose
    // an arbitrary representative and silently make coherence order-dependent.
    for generic in generics {
        let binder = resolution
            .binder(generic.span)
            .expect("impl parameter has a binder");
        let mut used = type_references_any_binder(resolution, self_ty, &BTreeSet::from([binder]));
        for argument in &trait_argument_ast {
            used |= type_references_any_binder(resolution, argument, &BTreeSet::from([binder]));
        }
        if !used {
            return Err(Diagnostic::new(
                generic.span,
                format!(
                    "impl parameter '{}' is unconstrained: it does not appear in the self type or trait arguments, so dispatch cannot solve it uniquely",
                    generic.name
                ),
            ));
        }
    }
    if trait_id.is_none()
        && !matches!(
            &self_ty.kind,
            ast::TypeKind::Named { path, .. }
                if path.len() == 1
                    && resolution
                        .reference(self_ty.span)
                        .is_some_and(|id| resolution.bindings[id].kind == BindingKind::Data)
        )
        && !matches!(&self_ty.kind, ast::TypeKind::Named { .. })
        && !matches!(
            &self_ty.kind,
            ast::TypeKind::Structural { row: Some(_), .. }
        )
    {
        return Err(Diagnostic::new(
            self_ty.span,
            "an inherent generic impl must target a nominal record/enum pattern or an open structural row with a row parameter",
        ));
    }
    let mut impl_associated = ImplAssociated::default();
    let mut provided = BTreeSet::new();
    for item in associated {
        match item {
            ast::Associated::Type { name, value, span } => {
                let Some(value) = value else {
                    return Err(Diagnostic::new(
                        *span,
                        "an associated type in an impl requires a value: 'type Name = Type;'",
                    ));
                };
                if trait_id.is_some()
                    && !matches!(
                        trait_associated.get(name),
                        Some(TraitAssociated::Type { .. })
                    )
                {
                    return Err(Diagnostic::new(
                        *span,
                        format!(
                            "associated type '{name}' is not declared by the implemented trait"
                        ),
                    ));
                }
                if trait_id.is_none() {
                    return Err(Diagnostic::new(
                        *span,
                        "inherent impls define associated constants only; associated types require a trait declaration",
                    ));
                }
                if !provided.insert(name.clone()) {
                    return Err(Diagnostic::new(
                        *span,
                        format!("duplicate item '{name}' in one impl"),
                    ));
                }
                impl_associated.types.insert(name.clone(), value.clone());
            }
            ast::Associated::Const {
                name,
                ty,
                value,
                span,
            } => {
                if type_mentions_self(ty) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                    ));
                }
                if type_references_any_binder(resolution, ty, &generic_ids) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an associated constant type in a generic impl may not depend on the impl's type parameters",
                    ));
                }
                let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                if !const_scalar_type(types, lowered) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                    ));
                }
                if trait_id.is_some()
                    && !matches!(
                        trait_associated.get(name),
                        Some(TraitAssociated::Const { .. })
                    )
                {
                    return Err(Diagnostic::new(
                        *span,
                        format!(
                            "associated constant '{name}' is not declared by the implemented trait"
                        ),
                    ));
                }
                if !provided.insert(name.clone()) {
                    return Err(Diagnostic::new(
                        *span,
                        format!("duplicate item '{name}' in one impl"),
                    ));
                }
                if let Some(declared) = trait_associated.get(name)
                    && let TraitAssociated::Const { ty: declared, .. } = declared
                {
                    let declared =
                        types.ty_in(declared, &crate::runtime_types::Subst::default())?;
                    if declared != lowered {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "associated constant '{name}' must have the declared type {}",
                                types.name(declared)
                            ),
                        ));
                    }
                }
                let Some(value) = value else {
                    continue;
                };
                if expression_mentions_generic(resolution, value, &generic_ids) {
                    return Err(Diagnostic::new(
                        value.span,
                        "an associated constant value in a generic impl may not depend on the impl's type parameters",
                    ));
                }
                let checked =
                    evaluate_associated_const(types, value, lowered, &impl_associated.consts)?;
                impl_associated.consts.insert(name.clone(), checked);
            }
        }
    }
    if let Some(trait_id) = trait_id {
        let associated_order = trait_definition
            .as_ref()
            .map(|definition| definition.associated_order.clone())
            .unwrap_or_default();
        for name in &associated_order {
            let Some(item) = trait_associated.get(name) else {
                continue;
            };
            match item {
                TraitAssociated::Type { default } => {
                    if !impl_associated.types.contains_key(name) {
                        let Some(default) = default else {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "missing associated type '{name}' for trait '{}' on this impl",
                                    resolution.bindings[trait_id].name
                                ),
                            ));
                        };
                        impl_associated.types.insert(name.clone(), default.clone());
                    }
                }
                TraitAssociated::Const { ty, default } => {
                    if impl_associated.consts.contains_key(name) {
                        continue;
                    }
                    let Some(default) = default else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "missing associated constant '{name}' for trait '{}'",
                                resolution.bindings[trait_id].name
                            ),
                        ));
                    };
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    let checked = evaluate_associated_const(
                        types,
                        default,
                        lowered,
                        &impl_associated.consts,
                    )?;
                    impl_associated.consts.insert(name.clone(), checked);
                }
            }
        }
    }
    let associated_index =
        (!impl_associated.types.is_empty() || !impl_associated.consts.is_empty()).then(|| {
            functions.impl_associated.push(impl_associated.clone());
            functions.impl_associated.len() - 1
        });
    let header_index = functions.impl_headers.len();
    functions.impl_headers.push(ImplHeader {
        trait_id,
        generics: generics.to_vec(),
        self_ty: self_ty.clone(),
        trait_arguments: trait_argument_ast.clone(),
        associated: impl_associated.clone(),
        methods: BTreeMap::new(),
        span,
        concrete: None,
    });
    let trait_argument_names = trait_generics
        .iter()
        .zip(&trait_argument_ast)
        .map(|(generic, argument)| (generic.name.clone(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut definitions = BTreeMap::new();
    let mut bindings = Vec::new();
    for method in methods {
        let f = &method.function;
        if f.total {
            return Err(Diagnostic::new(
                method.span,
                "impl methods are executable declarations and cannot be 'total'",
            ));
        }
        if let Some(collision) = f.generics.iter().find(|generic| {
            generics
                .iter()
                .any(|impl_generic| impl_generic.name == generic.name)
        }) {
            return Err(Diagnostic::new(
                collision.span,
                format!(
                    "method parameter '{}' must be distinct from the impl's parameters to avoid capture; rename one of them",
                    collision.name
                ),
            ));
        }
        let Some(receiver) = f.parameters.first() else {
            return Err(Diagnostic::new(
                method.span,
                "a method must declare a receiver as its first parameter: 'self: Self' or 'self: &Self'",
            ));
        };
        if receiver.erased || receiver.name != "self" {
            return Err(Diagnostic::new(
                receiver.span,
                "the first method parameter must be the receiver, written 'self: Self', 'self: &Self', 'self: &mut Self', or the concrete target type",
            ));
        }
        checked_generic_method_receiver(types, &receiver.ty, self_ty, &generic_ids, resolution)?;
        if Checker::builtin_method(&f.name) {
            return Err(Diagnostic::new(
                method.span,
                format!(
                    "method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                    f.name
                ),
            ));
        }
        if trait_id.is_some() {
            let Some(expected) = trait_methods.get(&f.name) else {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' is not declared by the implemented trait",
                        f.name
                    ),
                ));
            };
            if method_contract_key(
                resolution,
                expected.function,
                Some(self_ty),
                Some(&trait_argument_names),
                Some(&impl_associated.types),
            )? != method_contract_key(
                resolution,
                f,
                Some(self_ty),
                None,
                Some(&impl_associated.types),
            )? {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' does not match the trait signature exactly; parameters, parameter grades, erasure markers, result type, generic parameters and bounds, effect exclusions, lifetimes, effects, and substituted trait arguments must match",
                        f.name
                    ),
                ));
            }
        }
        for parameter in &f.parameters {
            if let Some(length) = &parameter.min_length {
                return Err(Diagnostic::new(
                    length.span,
                    "'where len >= N' parameters are supported on functions, not on methods yet",
                ));
            }
            if parameter.erased && type_mentions_self(&parameter.ty) {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "erased method parameters may not mention 'Self' in this subset",
                ));
            }
        }
        validate_erased_parameters(resolution, logical, f)?;
        validate_length_templates(resolution, f)?;
        validate_runtime_length_signature(resolution, f, true)?;
        let binding = resolution.method(method.span).ok_or_else(|| {
            Diagnostic::new(method.span, "internal error: impl method has no binding")
        })?;
        let definition = MethodDefinition {
            binding,
            public: method.public,
            unit: resolution.unit_of.get(&binding).copied().unwrap_or(0),
            impl_arguments: None,
        };
        if definitions.insert(f.name.clone(), definition).is_some() {
            return Err(Diagnostic::new(
                method.span,
                format!("duplicate method '{}' in one impl", f.name),
            ));
        }
        functions.declared.insert(
            binding,
            Declared {
                ast: f,
                span: method.span,
                self_ty: None,
                default_specialization: None,
                impl_associated: associated_index,
                impl_template: Some(header_index),
            },
        );
        bindings.push(binding);
    }
    if let Some(trait_id) = trait_id {
        let trait_public = resolution.public.contains(&trait_id);
        let impl_unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
        for (name, method) in &trait_methods {
            if definitions.contains_key(name) {
                continue;
            }
            if method.function.body.is_none() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "missing implementation of trait method '{name}' for {}",
                        type_key(self_ty)
                    ),
                ));
            }
            let receiver = method
                .function
                .parameters
                .first()
                .expect("trait receiver was validated at declaration");
            checked_generic_method_receiver(
                types,
                &receiver.ty,
                self_ty,
                &generic_ids,
                resolution,
            )?;
            let binding = *default_bindings
                .get(&(span.start, name.clone()))
                .ok_or_else(|| {
                    Diagnostic::new(
                        method.span,
                        "internal error: inherited default method has no binding",
                    )
                })?;
            let index = functions.default_specializations.len();
            functions
                .default_specializations
                .push((trait_id, TraitArguments::default()));
            functions.declared.insert(
                binding,
                Declared {
                    ast: method.function,
                    span: method.span,
                    self_ty: None,
                    default_specialization: Some(index),
                    impl_associated: associated_index,
                    impl_template: Some(header_index),
                },
            );
            definitions.insert(
                name.clone(),
                MethodDefinition {
                    binding,
                    public: trait_public,
                    unit: impl_unit,
                    impl_arguments: None,
                },
            );
            bindings.push(binding);
        }
    }
    functions.impl_headers[header_index].methods = definitions;
    Ok(bindings)
}
