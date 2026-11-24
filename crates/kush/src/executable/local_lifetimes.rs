//! Lifetimes of locals and helper results, elided structural results and outlives bounds.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Parameter lifetimes that the returned value syntactically derives from. A
/// direct name, field projection, or slice of a parameter carries that
/// parameter's lifetime; block/if/match value positions keep the branches that
/// actually produce the result. This is a conservative inference seed only:
/// the ownership pass still checks every returned origin against the chosen
/// lifetime, so a missed path becomes a checked dangling-borrow error rather
/// than an unsound widening.
pub(super) fn value_lifetime_candidates<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    expr: &ast::Expr,
    parameter_lifetimes: &BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
    out: &mut BTreeSet<String>,
) {
    match &expr.kind {
        ast::ExprKind::Name(_) => {
            if let Some(id) = resolution.reference(expr.span)
                && let Some(lifetime) = parameter_lifetimes.get(&id)
            {
                out.insert(lifetime.clone());
            }
        }
        ast::ExprKind::Field { value, .. } => {
            // A field projection of a multi-lifetime record parameter inherits
            // exactly that field's declared lifetime. Nested paths use the
            // record's field names, not its erased layout indices.
            if let Some((id, path)) = field_chain(resolution, expr)
                && let Some(fields) = parameter_field_lifetimes.get(&id)
                && let Some(lifetime) = fields.get(&path.join("."))
            {
                out.insert(lifetime.clone());
                return;
            }
            value_lifetime_candidates(
                resolution,
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Unary { operand: value, .. } | ast::ExprKind::Try(value) => {
            value_lifetime_candidates(
                resolution,
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Slice {
            value, start, end, ..
        } => {
            // Only the sliced base supplies the returned storage; endpoints
            // are integers and cannot name a borrow lifetime.
            let _ = (start, end);
            value_lifetime_candidates(
                resolution,
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Block(block) => {
            block_value_lifetime_candidates(
                resolution,
                declared,
                block,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::If {
            then, otherwise, ..
        } => {
            block_value_lifetime_candidates(
                resolution,
                declared,
                then,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
            if let Some(otherwise) = otherwise {
                value_lifetime_candidates(
                    resolution,
                    declared,
                    otherwise,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                    out,
                );
            }
        }
        ast::ExprKind::Match { arms, .. } => {
            for arm in arms {
                value_lifetime_candidates(
                    resolution,
                    declared,
                    &arm.body,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                    out,
                );
            }
        }
        ast::ExprKind::Call { callee, arguments } => {
            // Follow a helper's declared result source through the matching
            // argument. This keeps elided multi-input results inferable when
            // the body delegates to a checked helper (`fn alias(a, b) { tail(a) }`).
            for index in helper_result_parameters(resolution, declared, callee) {
                if let Some(argument) = arguments.get(index) {
                    value_lifetime_candidates(
                        resolution,
                        declared,
                        argument,
                        parameter_lifetimes,
                        parameter_field_lifetimes,
                        out,
                    );
                }
            }
        }
        _ => {}
    }
}
/// Record lifetimes introduced by local `let` bindings, so result inference can
/// follow a borrow through destructuring and simple aliases. This is a
/// conservative syntactic propagation: a binding receives a lifetime only when
/// its initializer has exactly one candidate lifetime. Anything ambiguous keeps
/// the existing explicit-annotation error.
pub(super) fn collect_local_lifetimes<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    block: &ast::Block,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { pattern, value, .. } => {
                bind_local_lifetime(
                    resolution,
                    declared,
                    pattern,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
            ast::Statement::Expr(expr) => collect_expr_local_lifetimes(
                resolution,
                declared,
                expr,
                parameter_lifetimes,
                parameter_field_lifetimes,
            ),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_local_lifetimes(
            resolution,
            declared,
            tail,
            parameter_lifetimes,
            parameter_field_lifetimes,
        );
    }
}

pub(super) fn collect_expr_local_lifetimes<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    expr: &ast::Expr,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    match &expr.kind {
        ast::ExprKind::Block(block) => collect_local_lifetimes(
            resolution,
            declared,
            block,
            parameter_lifetimes,
            parameter_field_lifetimes,
        ),
        ast::ExprKind::If {
            then, otherwise, ..
        } => {
            collect_local_lifetimes(
                resolution,
                declared,
                then,
                parameter_lifetimes,
                parameter_field_lifetimes,
            );
            if let Some(otherwise) = otherwise {
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    otherwise,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        ast::ExprKind::Match { arms, .. } => {
            for arm in arms {
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    &arm.body,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        ast::ExprKind::While { body, .. } | ast::ExprKind::Loop(body) => {
            collect_local_lifetimes(
                resolution,
                declared,
                body,
                parameter_lifetimes,
                parameter_field_lifetimes,
            );
        }
        // A lambda body is a separate callable scope; its own inference runs
        // when that body is checked.
        ast::ExprKind::Lambda(_) => {}
        _ => {}
    }
}

pub(super) fn bind_local_lifetime<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    pattern: &ast::Pattern,
    value: &ast::Expr,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    let chain = field_chain(resolution, value);
    match &pattern.kind {
        ast::PatternKind::Name(_) => {
            let Some(id) = resolution.binder(pattern.span) else {
                return;
            };
            let mut candidates = BTreeSet::new();
            value_lifetime_candidates(
                resolution,
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                &mut candidates,
            );
            if candidates.len() == 1 {
                parameter_lifetimes.insert(id, candidates.into_iter().next().unwrap());
            }
            // A plain alias of a borrowed record keeps the same field paths.
            if let Some((root, path)) = chain
                && let Some(fields) = parameter_field_lifetimes.get(&root).cloned()
            {
                let prefix = path.join(".");
                let mut copied = BTreeMap::new();
                for (name, lifetime) in fields {
                    let stripped = if prefix.is_empty() {
                        Some(name.as_str())
                    } else {
                        name.strip_prefix(&format!("{prefix}."))
                    };
                    if let Some(stripped) = stripped {
                        copied.insert(stripped.to_owned(), lifetime);
                    }
                }
                if !copied.is_empty() {
                    parameter_field_lifetimes.insert(id, copied);
                }
            }
        }
        ast::PatternKind::Record { fields, .. } | ast::PatternKind::Structural { fields, .. } => {
            let Some((root, base)) = chain else {
                return;
            };
            for (name, subpattern) in fields {
                let mut path = base.clone();
                path.push(name.clone());
                let lifetime = parameter_field_lifetimes
                    .get(&root)
                    .and_then(|fields| fields.get(&path.join(".")).cloned());
                if let Some(lifetime) = lifetime
                    && let ast::PatternKind::Name(_) = subpattern.kind
                    && let Some(id) = resolution.binder(subpattern.span)
                {
                    parameter_lifetimes.insert(id, lifetime);
                }
                if let ast::PatternKind::Name(_) = subpattern.kind
                    && let Some(id) = resolution.binder(subpattern.span)
                    && let Some(fields) = parameter_field_lifetimes.get(&root).cloned()
                {
                    // The binding may itself be a nested borrowed record; keep
                    // its child field lifetimes for a later destructuring.
                    let prefix = format!("{}.", path.join("."));
                    let mut copied = BTreeMap::new();
                    for (name, lifetime) in fields {
                        if let Some(stripped) = name.strip_prefix(&prefix) {
                            copied.insert(stripped.to_owned(), lifetime);
                        }
                    }
                    if !copied.is_empty() {
                        parameter_field_lifetimes.insert(id, copied);
                    }
                }
                if matches!(
                    subpattern.kind,
                    ast::PatternKind::Record { .. } | ast::PatternKind::Structural { .. }
                ) {
                    // Nested destructuring needs a synthetic root for the
                    // sub-record. Reuse the original root and extend the path
                    // through each nested field below.
                    bind_nested_record_lifetime(
                        resolution,
                        subpattern,
                        &root,
                        &path,
                        parameter_lifetimes,
                        parameter_field_lifetimes,
                    );
                }
            }
        }
        ast::PatternKind::Type { inner, .. } => bind_local_lifetime(
            resolution,
            declared,
            inner,
            value,
            parameter_lifetimes,
            parameter_field_lifetimes,
        ),
        ast::PatternKind::Or(patterns) => {
            for pattern in patterns {
                bind_local_lifetime(
                    resolution,
                    declared,
                    pattern,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        _ => {}
    }
}

pub(super) fn bind_nested_record_lifetime(
    resolution: &Resolution,
    pattern: &ast::Pattern,
    root: &BindingId,
    base: &[String],
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    let (ast::PatternKind::Record { fields, .. } | ast::PatternKind::Structural { fields, .. }) =
        &pattern.kind
    else {
        return;
    };
    for (name, subpattern) in fields {
        let mut path = base.to_vec();
        path.push(name.clone());
        let lifetime = parameter_field_lifetimes
            .get(root)
            .and_then(|fields| fields.get(&path.join(".")).cloned());
        if let Some(lifetime) = lifetime
            && let ast::PatternKind::Name(_) = subpattern.kind
            && let Some(id) = resolution.binder(subpattern.span)
        {
            parameter_lifetimes.insert(id, lifetime);
        }
        bind_nested_record_lifetime(
            resolution,
            subpattern,
            root,
            &path,
            parameter_lifetimes,
            parameter_field_lifetimes,
        );
    }
}

/// AST argument positions of `callee` whose written borrow lifetime supplies
/// its result. An explicit result lifetime selects every parameter that mentions
/// it; an elided borrowed result selects the single input lifetime, if any.
/// Positions are source positions because a call keeps erased proof arguments
/// in its AST argument list; they are not runtime parameter indices.
pub(super) fn helper_result_parameters<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    callee: &ast::Expr,
) -> Vec<usize> {
    let name = match &callee.kind {
        ast::ExprKind::Name(_) => callee,
        ast::ExprKind::Specialize { callee, .. } => callee,
        _ => return Vec::new(),
    };
    let Some(id) = resolution.reference(name.span) else {
        return Vec::new();
    };
    let Some(entry) = declared.get(&id) else {
        return Vec::new();
    };
    let function = entry.ast;
    let result = crate::grades::split(&function.result).0;
    if !matches!(
        result.kind,
        ast::TypeKind::Borrow { .. } | ast::TypeKind::Slice(_)
    ) {
        return Vec::new();
    }
    let explicit = borrow_lifetime(result);
    let mut inputs: Vec<(usize, Option<String>)> = Vec::new();
    for (position, parameter) in function.parameters.iter().enumerate() {
        if parameter.erased {
            continue;
        }
        let ty = crate::grades::split(&parameter.ty).0;
        if matches!(ty.kind, ast::TypeKind::Borrow { .. }) {
            inputs.push((position, borrow_lifetime(ty)));
        }
    }
    let Some(explicit) = explicit else {
        // Elided result: only an unambiguous single input borrow can tell us
        // which argument supplies it.
        let distinct = inputs
            .iter()
            .map(|(position, name)| name.clone().unwrap_or_else(|| format!("#{position}")))
            .collect::<BTreeSet<_>>();
        if distinct.len() == 1 {
            return inputs.iter().map(|(position, _)| *position).collect();
        }
        return Vec::new();
    };
    inputs
        .iter()
        .filter(|(_, name)| name.as_deref() == Some(explicit.as_str()))
        .map(|(position, _)| *position)
        .collect()
}

/// Map one solved stable origin onto this instance's declared lifetime. A
/// direct borrowed parameter owns every path through it. A by-value record
/// parameter uses its source field path. A missing mapping is an error, never a
/// silently dropped origin that would make the summary look smaller than it is.
pub(super) fn summary_origin_lifetime(
    origin: &recursive_lifetimes::Origin,
    parameter_lifetimes: &[Option<String>],
    parameter_binders: &[Option<BindingId>],
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
) -> std::result::Result<String, String> {
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    if origin.path.is_empty() {
        return Err(format!(
            "runtime parameter #{} has no inferred borrow lifetime; no borrowed input lifetime was recorded for this position",
            origin.parameter
        ));
    }
    let binder = parameter_binders
        .get(origin.parameter)
        .copied()
        .flatten()
        .ok_or_else(|| {
            format!(
                "runtime parameter #{} has no source binder",
                origin.parameter
            )
        })?;
    let path = origin.path.join(".");
    parameter_field_lifetimes
        .get(&binder)
        .and_then(|fields| fields.get(&path).cloned())
        .ok_or_else(|| {
            format!(
                "cannot be returned: runtime parameter #{} field path '{path}' has no declared lifetime",
                origin.parameter
            )
        })
}
/// Map one required-precondition endpoint onto this instance's declared input
/// lifetime. Unlike a result origin, a root leaf may name a container element
/// lifetime, which `collect_parameter_field_lifetimes` records at the empty
/// path. A missing field path is an error, never a dropped requirement.
pub(super) fn requirement_origin_lifetime(
    origin: &recursive_lifetimes::Origin,
    parameter_lifetimes: &[Option<String>],
    parameter_nested_lifetimes: &[Option<String>],
    parameter_binders: &[Option<BindingId>],
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
) -> std::result::Result<String, String> {
    if let Some(binder) = parameter_binders.get(origin.parameter).copied().flatten()
        && let Some(lifetime) = parameter_field_lifetimes
            .get(&binder)
            .and_then(|fields| fields.get(&origin.path.join(".")))
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
        && !lifetime.starts_with('<')
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_nested_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    summary_origin_lifetime(
        origin,
        parameter_lifetimes,
        parameter_binders,
        parameter_field_lifetimes,
    )
}
pub(super) fn block_value_lifetime_candidates<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    block: &ast::Block,
    parameter_lifetimes: &BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
    out: &mut BTreeSet<String>,
) {
    let mut returns = Vec::new();
    collect_block_returns(block, &mut returns);
    for returned in returns {
        value_lifetime_candidates(
            resolution,
            declared,
            returned,
            parameter_lifetimes,
            parameter_field_lifetimes,
            out,
        );
    }
    if let Some(tail) = &block.tail {
        value_lifetime_candidates(
            resolution,
            declared,
            tail,
            parameter_lifetimes,
            parameter_field_lifetimes,
            out,
        );
    }
}
/// The parameter binder and named field path of a projection chain rooted at a
/// parameter name.
pub(super) fn field_chain(
    resolution: &Resolution,
    expr: &ast::Expr,
) -> Option<(BindingId, Vec<String>)> {
    match &expr.kind {
        ast::ExprKind::Name(_) => Some((resolution.reference(expr.span)?, Vec::new())),
        ast::ExprKind::Field { value, name } => {
            let (id, mut path) = field_chain(resolution, value)?;
            path.push(name.clone());
            Some((id, path))
        }
        _ => None,
    }
}
/// Resolve an elided borrowed field inside a structural record result from the
/// function's single input borrow lifetime. Explicit labels, including the
/// concrete label of a `..r` row specialization, are retained exactly. Only a
/// direct structural view field without a label is filled, and only when one
/// input borrow lifetime is available. Zero or several distinct inputs keep the
/// field unresolved so the result gate reports the missing relation; a row
/// hidden behind an owning container is likewise left for that gate.
pub(super) fn resolve_elided_structural_result(
    types: &mut crate::runtime_types::Types<'_>,
    result: Type,
    input_lifetimes: &[(String, Span, Option<String>)],
    span: Span,
) -> Result<Type> {
    fn go(
        types: &mut crate::runtime_types::Types<'_>,
        ty: Type,
        label: Option<&str>,
        no_input: bool,
        span: Span,
        depth: usize,
    ) -> Result<Type> {
        if depth >= 64 {
            return Err(Diagnostic::new(
                span,
                "structural result nesting exceeded its finite lifetime-elision budget",
            ));
        }
        let Some(_id) = ty.layout().filter(|id| types.enums[*id].structural) else {
            return Ok(ty);
        };
        let fields = types
            .structural_row_fields(ty)
            .expect("structural layout has a canonical row");
        let mut rebuilt = Vec::with_capacity(fields.len());
        for field in &fields {
            let mut field_ty = field.ty;
            if field_ty
                .layout()
                .is_some_and(|id| types.enums[id].structural)
            {
                field_ty = go(types, field_ty, label, no_input, span, depth + 1)?;
            }
            let mut lifetime = field.lifetime.clone();
            if lifetime.is_none() && field_ty.is_view() {
                let Some(label) = label else {
                    return Err(Diagnostic::new(
                        span,
                        if no_input {
                            "a returned structural record field has an elided lifetime, but the function has no borrowed input to infer it from; write the field as '&'a [T]' with a declared lifetime or return a nominal record with declared field lifetimes"
                        } else {
                            "cannot recover the lifetime of an elided structural result field: the function has several distinct input borrow lifetimes; name the field's lifetime explicitly, as in 'struct { view: &'a [T] }'"
                        },
                    ));
                };
                lifetime = Some(label.to_owned());
            }
            rebuilt.push(crate::runtime_types::RowField::new(
                field.name.clone(),
                field_ty,
                lifetime,
            ));
        }
        if rebuilt == fields {
            return Ok(ty);
        }
        types.structural_fields(rebuilt, span)
    }
    let label = match input_lifetimes {
        [(only, _, _)] => Some(only.as_str()),
        _ => None,
    };
    go(types, result, label, input_lifetimes.is_empty(), span, 0)
}

/// Map each borrowed field path of a parameter type to its declared lifetime,
/// using source field names. Container element leaves use the container field's
/// name; a direct slice or reference field uses its own name.
pub(super) fn collect_parameter_field_lifetimes(
    types: &crate::runtime_types::Types<'_>,
    ty: Type,
    out: &mut BTreeMap<String, String>,
) -> Result<()> {
    fn names(types: &crate::runtime_types::Types<'_>, ty: Type, path: &[usize]) -> Option<String> {
        let mut current = ty;
        let mut names = Vec::with_capacity(path.len());
        for index in path {
            let id = current.layout().filter(|id| types.enums[*id].record)?;
            let variant = &types.enums[id].variants[0];
            names.push(variant.names.get(*index)?.clone());
            current = *variant.fields.get(*index)?;
        }
        Some(names.join("."))
    }
    for leaf in crate::runtime_types::borrow_leaves(types, ty)? {
        let Some(lifetime) = leaf.lifetime else {
            continue;
        };
        if let Some(name) = names(types, ty, &leaf.path) {
            out.insert(name, lifetime);
        }
    }
    Ok(())
}
/// A lifetime label that names no caller identity at this occurrence: an
/// inferred record identity, a freshened argument placeholder, or an elided
/// label. These are resolved by the ownership provenance pass and must not be
/// compared as if they were declared caller lifetimes.
pub(super) fn is_opaque_call_label(label: &str) -> bool {
    label.is_empty() || label == "_" || label.starts_with('<')
}
/// Whether `long` outlives `short` under a reflexive-transitive bound set.
/// Every lifetime outlives itself; declared bounds supply the strict steps.
pub(crate) fn outlives(bounds: &BTreeSet<(String, String)>, long: &str, short: &str) -> bool {
    long == short || bounds.contains(&(long.to_owned(), short.to_owned()))
}
/// Validate declared function lifetime binders and build the transitive closure
/// of their outlives bounds. Bounds name declared lifetimes only, duplicates and
/// cycles are rejected, and a self bound is accepted as reflexivity.
pub(crate) fn build_lifetime_bounds(
    lifetimes: &[ast::Lifetime],
) -> Result<BTreeSet<(String, String)>> {
    let declared = lifetimes
        .iter()
        .map(|lifetime| lifetime.name.as_str())
        .collect::<BTreeSet<_>>();
    let mut edges = BTreeSet::new();
    let mut spans = BTreeMap::new();
    let mut seen_bounds = BTreeSet::new();
    for lifetime in lifetimes {
        for bound in &lifetime.bounds {
            if !declared.contains(bound.name.as_str()) {
                return Err(Diagnostic::new(
                    bound.span,
                    format!(
                        "outlives bound refers to undeclared lifetime '{}'; declare it in the function's lifetime parameter list",
                        bound.name
                    ),
                ));
            }
            if !seen_bounds.insert((lifetime.name.clone(), bound.name.clone())) {
                return Err(Diagnostic::new(
                    bound.span,
                    format!(
                        "duplicate outlives bound '{}: {}'",
                        lifetime.name, bound.name
                    ),
                ));
            }
            // A self bound is satisfied by reflexivity and contributes no edge.
            if bound.name == lifetime.name {
                continue;
            }
            edges.insert((lifetime.name.clone(), bound.name.clone()));
            spans.insert((lifetime.name.clone(), bound.name.clone()), bound.span);
        }
    }
    let graph = crate::lifetimes::LifetimeGraph::new(&edges);
    let solution = graph.solve();
    let closure = solution.closure;
    debug_assert!(solution.components.iter().all(|c| !c.is_empty()));
    // A cycle makes the members equal, which needs one shared lifetime rather
    // than a mutually bounded pair. Rejecting it keeps the order a strict DAG.
    if let Some(((long, short), span)) = spans
        .iter()
        .find(|((long, short), _)| closure.contains(&(short.clone(), long.clone())))
    {
        return Err(Diagnostic::new(
            *span,
            format!(
                "cyclic outlives bounds are not supported: '{long}' and '{short}' would be the same lifetime; use one lifetime parameter"
            ),
        ).with_note(*span, format!("outlives cycle: {}", graph.path(short, long).unwrap().iter().map(|n| format!("'{n}")).chain(std::iter::once(format!("'{short}"))).collect::<Vec<_>>().join(" -> "))));
    }
    Ok(closure)
}
