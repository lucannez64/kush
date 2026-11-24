//! The expression checker.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    pub(super) fn expr_expected_unchecked(
        &mut self,
        expr: &ast::Expr,
        expected: Option<Type>,
    ) -> Result<Expr> {
        self.nested(expr.span, |c| {
            let span = expr.span;
            if let Some((form, value)) = expr.staging() {
                return match form {
                    ast::StagingForm::Quote => c.quote(value, expected, span),
                    ast::StagingForm::Lift if c.quote_holes.contains_key(&(span.start, span.end)) => {
                        let slot = c.quote_holes[&(span.start, span.end)];
                        let ty = c.locals[slot].ty;
                        let value = if matches!(ty, Type::Bytes | Type::String) {
                            c.require(ALLOC | PANIC, span)?;
                            c.copy_lifted_text(slot, span)
                        } else {
                            Expr { kind: ExprKind::Local(slot), ty, span, resource: None }
                        };
                        match expected { Some(ty) => c.coerce(value, ty, span), None => Ok(value) }
                    }
                    ast::StagingForm::Splice if c.quote_splices.contains_key(&(span.start, span.end)) => {
                        let (function, signature) = c.quote_splices[&(span.start, span.end)];
                        let value = Expr { kind: ExprKind::FnValue { function, captures: vec![] },
                            ty: Type::Fn(signature), span, resource: None };
                        match expected { Some(ty) => c.coerce(value, ty, span), None => Ok(value) }
                    }
                    _ => Err(Diagnostic::new(span,
                        "this staging operation has not been elaborated yet")),
                };
            }
            if let ast::ExprKind::Call { callee, arguments } = &expr.kind
                && c.resolution.reference(callee.span).is_some_and(|id|
                    c.resolution.bindings[id].kind == BindingKind::Builtin
                        && c.resolution.bindings[id].name == "Code.clone") {
                return c.clone_code(arguments, expected, span);
            }
            if let ast::ExprKind::Call { callee, arguments } = &expr.kind
                && let Some(id) = c.resolution.reference(callee.span)
                && c.resolution.bindings[id].kind == BindingKind::Builtin {
                match c.resolution.bindings[id].name.as_str() {
                    "Code.compile" => return c.compile_code(arguments, expected, span),
                    "Code.call" => return c.call_code(arguments, expected, span),
                    _ => {},
                }
            }
            if let Some(id) = c.logical_data_root(expr)
                && (c.logical.data.contains_key(&id)
                    || c.logical.constructors.contains_key(&id))
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "'{}' belongs to a total logical data type and has no runtime value; use it only in an erased proof argument",
                        c.resolution.bindings[id].name
                    ),
                ));
            }
            if let ast::ExprKind::Handle {
                operation,
                parameter,
                result,
                handler,
                body,
                capability,
            } = &expr.kind
            {
                c.pending_capability = capability.clone();
                let checked = c.handle_effect(
                    operation,
                    parameter,
                    result,
                    handler,
                    body,
                    expected,
                    span,
                );
                c.pending_capability = None;
                return checked;
            }
            if let ast::ExprKind::Perform { operation, value } = &expr.kind {
                return c.perform_effect(operation, value, expected, span);
            }
            if c.constructor_target(expr).is_some() {
                return c.construct(expr, None, expected, span);
            }
            if let ast::ExprKind::Lambda(lambda) = &expr.kind {
                return c.lambda(lambda, span, expected, LambdaContext::Ordinary);
            }
            if matches!(
                expr.kind,
                ast::ExprKind::Name(_) | ast::ExprKind::Field { .. }
            ) && let Some(id) = c.resolution.reference(span)
                && let Some(declared) = c.functions.declared.get(&id)
            {
                if declared.ast.constant {
                    return c.constant(id, expected, span);
                }
                return c.function_value(id, None, expected, span);
            }
            if let ast::ExprKind::Specialize { callee, arguments } = &expr.kind
                && let Some(id) = c.resolution.reference(callee.span)
                && c.functions.declared.contains_key(&id)
            {
                return c.function_value(id, Some(arguments), expected, span);
            }
            // `u8.MAX`, `i32.MIN`, ...: integer range constants.
            if matches!(expr.kind, ast::ExprKind::Field { .. })
                && let Some(id) = c.resolution.reference(span)
                && c.resolution.bindings[id].kind == BindingKind::Builtin
                && let Some((kind, bound)) = c.resolution.bindings[id].name.split_once('.')
                && let Some(kind) = crate::int::IntKind::named(kind)
                && matches!(bound, "MIN" | "MAX")
            {
                let value = if bound == "MIN" { kind.min() } else { kind.max() };
                let ty = Type::int(kind);
                if let Some(expected) = expected {
                    c.expect(ty, expected, span)?;
                }
                return Ok(Expr {
                    kind: ExprKind::Constant(kind.encode(value).unwrap()),
                    ty,
                    span,
                    resource: None,
                });
            }
            // `Self.NAME` and `Type.NAME`: associated constants. They are
            // compile-time substitutions with the declared scalar type, so the
            // lowered expression is an ordinary literal and has no storage or
            // accessor call.
            if let ast::ExprKind::Field { value, name } = &expr.kind {
                if matches!(&value.kind, ast::ExprKind::Name(root) if root == "Self") {
                    let Some(value) = c.associated_consts.get(name).cloned() else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "unknown associated constant '{name}'; an impl must define it or inherit a trait default"
                            ),
                        ));
                    };
                    let node = const_value_expr(&value, span)?;
                    return match expected {
                        Some(expected) => c.coerce(node, expected, span),
                        None => Ok(node),
                    };
                }
                if let Some(id) = c.resolution.reference(span)
                    && matches!(
                        c.resolution.bindings[id].kind,
                        BindingKind::Generic | BindingKind::Parameter
                    )
                    && let Some(value) = c.generic_associated_const(id, name, span)?
                {
                    let node = const_value_expr(&value, span)?;
                    return match expected {
                        Some(expected) => c.coerce(node, expected, span),
                        None => Ok(node),
                    };
                }
                if let Some(id) = c.resolution.reference(span)
                    && c.resolution.bindings[id].kind == BindingKind::Data
                    && let Some(layout) = c.types.nominal_by_binding(id)
                {
                    let nominal = Type::Enum(layout);
                    let mut candidates = Vec::new();
                    if let Some(value) = c
                        .functions
                        .inherent_consts
                        .get(&nominal)
                        .and_then(|values| values.get(name))
                    {
                        candidates.push(value.clone());
                    }
                    for ((_, _, receiver), values) in &c.functions.trait_consts {
                        if *receiver == nominal
                            && let Some(value) = values.get(name)
                            && !candidates.contains(value)
                        {
                            candidates.push(value.clone());
                        }
                    }
                    match candidates.as_slice() {
                        [] => {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "type '{}' has no associated constant '{name}'",
                                    c.types.name(nominal)
                                ),
                            ));
                        }
                        [value] => {
                            let node = const_value_expr(value, span)?;
                            return match expected {
                                Some(expected) => c.coerce(node, expected, span),
                                None => Ok(node),
                            };
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "associated constant '{name}' of '{}' is ambiguous between several traits; qualify it through that trait's method",
                                    c.types.name(nominal)
                                ),
                            ));
                        }
                    }
                }
            }
            let (kind, ty) = match &expr.kind {
                ast::ExprKind::Integer(text) => {
                    let ty = c.literal_type(expected);
                    (ExprKind::Constant(int_literal(text, false, ty, span)?), ty)
                }
                ast::ExprKind::Float(text) => {
                    let ty = c.float_literal_type(expected);
                    let kind = ty.float_kind().expect("float literal type");
                    (ExprKind::Constant(crate::float::literal(text, kind, span)?), ty)
                }
                ast::ExprKind::String(text) => {
                    c.require(ALLOC | PANIC, span)?;
                    (
                        ExprKind::BytesLiteral(text.as_bytes().to_vec()),
                        Type::String,
                    )
                }
                ast::ExprKind::Char(ch) => (ExprKind::Constant(i64::from(u32::from(*ch))), Type::Char),
                ast::ExprKind::Bool(b) => (ExprKind::Constant(i64::from(*b)), Type::Bool),
                ast::ExprKind::Tuple(values) if values.len() >= 2 => {
                    return c.tuple_value(values, expected, span);
                }
                ast::ExprKind::Tuple(values) if values.len() == 1 => {
                    return Err(Diagnostic::new(
                        span,
                        "one-element tuples are not supported; write '()' for unit or omit the trailing comma",
                    ));
                }
                ast::ExprKind::Tuple(values) if values.is_empty() => {
                    (ExprKind::Constant(0), Type::Unit)
                }
                ast::ExprKind::Name(name) if name == "_" => {
                    return Err(Diagnostic::new(
                        span,
                        "'_' is a proof hole; it is only valid as an erased argument",
                    ));
                }
                ast::ExprKind::Name(_) => {
                    if let Some(id) = c.resolution.reference(span) {
                        // A `&mut Vec` parameter that keeps `len >= N` is used
                        // only where the bound survives: indexing, methods
                        // that cannot shorten it, and refined parameters.
                        if let Some(slot) = c.slots.get(&id)
                            && c.parameter_lengths.contains_key(slot)
                            && matches!(c.locals[*slot].ty, Type::RefMut(_))
                            && !std::mem::take(&mut c.refined_use_ok)
                            && !c.lending_spans.contains(&(span.start, span.end))
                        {
                            return Err(Diagnostic::new(
                                span,
                                "this parameter keeps 'len >= N'; index it, call push/set/reserve/replace on it, or pass it to a parameter that keeps the bound",
                            ));
                        }
                        if let Some(slot) = c.slots.get(&id)
                            && c.capability_slots.contains(slot)
                            && !std::mem::take(&mut c.capability_argument)
                        {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "'{}' is a second-class capability: it can only be passed directly to a 'cap' parameter or used as 'perform {}(...)'",
                                    c.resolution.bindings[id].name,
                                    c.resolution.bindings[id].name
                                ),
                            ));
                        }
                        if c.logical.names.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "'{}' is a checked logical definition and has no runtime value; use it only in an erased proof argument",
                                    c.resolution.bindings[id].name
                                ),
                            ));
                        }
                        if c.logical.data.contains_key(&id)
                            || c.logical.constructors.contains_key(&id)
                        {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "'{}' belongs to a total logical data type and has no runtime value; use it only in an erased proof argument",
                                    c.resolution.bindings[id].name
                                ),
                            ));
                        }
                        if c.kernel_proofs.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                "erased logical proofs have no runtime value; pass them only to erased parameters",
                            ));
                        }
                        if c.proof_values.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                "an erased proof-valued local has no runtime value; pass it only to an erased parameter",
                            ));
                        }
                        if c.proofs.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                "erased proofs have no runtime value; pass them only to erased parameters",
                            ));
                        }
                    }
                    let slot = c.slot(span)?;
                    (ExprKind::Local(slot), c.locals[slot].ty)
                }
                ast::ExprKind::Field { value, name }
                    if c.resolution.reference(span).is_none() =>
                {
                    return c.field(value, name, span, expected);
                }
                ast::ExprKind::Record { ty, fields, base } => {
                    return match base {
                        // `record_update` establishes field lengths itself.
                        Some(base) => c.record_update(ty, fields, base, span, expected),
                        None => {
                            let value = c.record(ty, fields, span, expected)?;
                            c.establish_field_lengths(value)
                        }
                    };
                }
                ast::ExprKind::StructuralLiteral(fields) => {
                    return c.structural_literal(fields, expected, span);
                }
                ast::ExprKind::Cast { value, ty } => {
                    let expr = c.structural_cast(value, ty, span)?;
                    return match expected {
                        Some(expected) => c.coerce(expr, expected, span),
                        None => Ok(expr),
                    };
                }
                ast::ExprKind::Array(values) => {
                    let candidates = c.expected_array(expected, values.len());
                    if !candidates.is_empty() {
                        if values.len() != candidates[0].2 {
                            return Err(Diagnostic::new(
                                span,
                                "array literal length differs from its type",
                            ));
                        }
                        // Accumulate constraints instead of committing to the
                        // first union alternative: every candidate array layout
                        // is tried, and exactly one must accept every element.
                        let mut accepted = Vec::new();
                        let mut first_error = None;
                        for (id, element, _) in &candidates {
                            let mut fields = Vec::with_capacity(values.len());
                            let mut failed = None;
                            for value in values {
                                match c.expr_expected(value, Some(*element)) {
                                    Ok(value) => fields.push(value),
                                    Err(error) => {
                                        failed = Some(error);
                                        break;
                                    }
                                }
                            }
                            if failed.is_none() {
                                accepted.push((*id, fields));
                            } else if first_error.is_none() {
                                first_error = failed;
                            }
                        }
                        let (id, fields) = match accepted.len() {
                            1 => accepted.pop().expect("one accepted candidate"),
                            0 => {
                                return Err(first_error.expect(
                                    "an array literal candidate always attempts one element",
                                ));
                            }
                            _ => {
                                return Err(Diagnostic::new(
                                    span,
                                    "this array literal fits several union alternatives; add an explicit annotation or type arguments",
                                ));
                            }
                        };
                        let ty = if fields.iter().any(|v| v.ty == Type::Never) {
                            Type::Never
                        } else {
                            Type::Enum(id)
                        };
                        let value = Expr {
                            kind: ExprKind::Construct {
                                enum_id: id,
                                tag: 0,
                                fields,
                            },
                            ty,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    if let Some((element, capacity)) = expected
                        .and_then(|ty| ty.layout())
                        .and_then(|id| c.types.enums[id].dynamic_array)
                    {
                        // A contextual literal is the checked construction of
                        // a runtime-sized inline array. Its static length is at
                        // most the capacity, so the reused push guards are
                        // unreachable; no runtime panic can occur and no
                        // `panic` effect is required.
                        if values.len() > capacity {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "DynArray literal has {} elements but the capacity is {capacity}",
                                    values.len()
                                ),
                            ));
                        }
                        // A runtime-length target `[T; n <= C]` accepts a
                        // literal only when the facts prove `n == k`. There is
                        // no runtime fallback for a literal.
                        let runtime_binder = expected
                            .and_then(|ty| ty.layout())
                            .and_then(|id| c.types.enums[id].runtime_length);
                        if let Some(binder) = runtime_binder {
                            let term = c.runtime_length_term(binder, span)?;
                            let count = values.len() as i128;
                            if !c.try_prove(
                                vec![(term, Kind::EqEq, crate::facts::Linear::constant(count))],
                                &format!("n == {count}"),
                                span,
                            ) {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "cannot prove that '{}' == {} for this [T; {} <= {capacity}] literal; check the length first (for example 'if {} == {} {{ ... }}') or use Array.fill",
                                        c.resolution.bindings[binder].name,
                                        values.len(),
                                        c.resolution.bindings[binder].name,
                                        c.resolution.bindings[binder].name,
                                        values.len()
                                    ),
                                ));
                            }
                        }
                        let literal_ty = c.types.dynamic_array(element, capacity, span)?;
                        let mut current = Expr {
                            kind: ExprKind::DynArrayNew {
                                element,
                                capacity,
                            },
                            ty: literal_ty,
                            span,
                            resource: None,
                        };
                        for value in values {
                            let value = c.expr_expected(value, Some(element))?;
                            c.expect(value.ty, element, value.span)?;
                            let ty = current.ty;
                            current = Expr {
                                kind: ExprKind::DynArrayPush {
                                    array: Box::new(current),
                                    value: Box::new(value),
                                    element,
                                    capacity,
                                },
                                ty,
                                span,
                                resource: None,
                            };
                        }
                        if runtime_binder.is_some() && current.ty != Type::Never {
                            // Same inline layout; the proof above fixes the
                            // length to the binder.
                            current.ty = expected.expect("runtime-length literal target");
                        }
                        return match expected {
                            Some(expected) => c.coerce(current, expected, span),
                            None => Ok(current),
                        };
                    }
                    return c.vec_literal(values, span, expected);
                }
                ast::ExprKind::Index { value, index } => {
                    if let Some(value) = c.container_index(value, index, expected, span)? {
                        return Ok(value);
                    }
                    let base = c.place(value)?;
                    if base.ty.is_text() {
                        return Err(Diagnostic::new(
                            span,
                            "a &str view is not indexed by a single index; use Str.byte_at or Str.scalar_at, or take a checked byte-range subview with view[start..end]",
                        ));
                    }
                    if let Some(pointer) = base.ty.slice_element() {
                        let element = c.types.pointees[pointer];
                        if c.owned_type(element) {
                            return Err(Diagnostic::new(
                                span,
                                "indexing a slice copies the element, but it owns resources or is linear",
                            ));
                        }
                        c.require(PANIC, span)?;
                        c.record_bounds(Container::Slice, None, span);
                        let index = c.expr_expected(index, Some(Type::I64))?;
                        c.expect(index.ty, Type::I64, index.span)?;
                        let ty = if index.ty == Type::Never {
                            Type::Never
                        } else {
                            element
                        };
                        let value = Expr {
                            kind: ExprKind::Call(
                                Target::Slice(SliceOp::Get, element),
                                vec![base, index],
                            ),
                            ty,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    if let Some(value) = c.runtime_array_index(&base, index, span)? {
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    let Some((element, length)) =
                        base.ty.layout().and_then(|id| c.types.enums[id].array)
                    else {
                        return Err(Diagnostic::new(
                            span,
                            "index syntax requires an inline array or a &[T] slice view",
                        ));
                    };
                    if let Some(position) = crate::length::eval_expr(
                        c.resolution,
                        c.logical,
                        &c.consts,
                        index,
                    )? {
                        if position >= length {
                            return Err(Diagnostic::new(
                                index.span,
                                "array index out of bounds",
                            ));
                        }
                        if c.owned_type(element) {
                            return Err(Diagnostic::new(
                                span,
                                "indexing cannot copy owned or linear array elements; destructure or slice instead",
                            ));
                        }
                        let value = Expr {
                            kind: ExprKind::Project(
                                Box::new(base),
                                1 + position * c.types.width(element),
                            ),
                            ty: element,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    // Dynamic indexing lowers to a whole-array slice view and a
                    // checked element read. The view only lives for this
                    // expression, so it cannot dangle.
                    if c.owned_type(element) {
                        return Err(Diagnostic::new(
                            span,
                            "dynamic indexing copies the element, but it owns resources or is linear",
                        ));
                    }
                    c.require(PANIC, span)?;
                    c.record_bounds(Container::Array, None, span);
                    let view =
                        c.slice_from_expr(base, None, None, element, false, false, span, None, None)?;
                    let index = c.expr_expected(index, Some(Type::I64))?;
                    c.expect(index.ty, Type::I64, index.span)?;
                    let ty = if index.ty == Type::Never {
                        Type::Never
                    } else {
                        element
                    };
                    let value = Expr {
                        kind: ExprKind::Call(
                            Target::Slice(SliceOp::Get, element),
                            vec![view, index],
                        ),
                        ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => c.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                ast::ExprKind::Slice { value, start, end } => {
                    return c.slice_view(
                        value,
                        start.as_deref(),
                        end.as_deref(),
                        false,
                        span,
                        expected,
                    );
                }
                ast::ExprKind::While {
                    condition,
                    body,
                    invariant,
                } => {
                    // The invariant must hold on entry; after the loop-head
                    // widening it is assumed, so the body and the exit see it.
                    let invariant = match invariant {
                        Some(invariant) => {
                            let checked = c.expr_expected(invariant, Some(Type::Bool))?;
                            c.expect(checked.ty, Type::Bool, checked.span)?;
                            c.prove_condition(&checked, "the loop invariant on entry")?;
                            Some(checked)
                        }
                        None => None,
                    };
                    c.bump_assigned(body, Some(condition));
                    if let Some(invariant) = &invariant {
                        c.facts.assume(invariant, true);
                    }
                    let before = c.facts.version_stamp();
                    let condition = c.expr(condition)?;
                    c.expect(condition.ty, Type::Bool, condition.span)?;
                    let unwritten = c.facts.same_stamp(&before);
                    let mark = c.facts.mark();
                    let head = c.facts.clone();
                    if unwritten {
                        c.facts.assume_unwritten(&condition, true);
                    } else {
                        c.facts.assume(&condition, true);
                    }
                    let scalar_baseline = c.scalar_values.clone();
                    let scalar_live = c.kernel_locals.len();
                    c.loops.push(Loop { value: None, is_while: true, expected: None, broke: false, invariant: invariant.clone() });
                    c.body_invariant = invariant.clone();
                    let body = c.block(body, Some(Type::Unit));
                    c.body_invariant = None;
                    let broke = c.loops.pop().is_some_and(|state| state.broke);
                    c.facts.reset(mark);
                    // Without `break`, the loop exits only from the head, where
                    // every value written in the body is at its head version
                    // (already widened by `bump_assigned`) and the condition is
                    // false.
                    if !broke && body.as_ref().is_ok_and(|body| body.ty != Type::Never) {
                        c.facts.versions_from(&head);
                        if unwritten {
                            c.facts.assume_unwritten(&condition, false);
                        } else {
                            c.facts.assume(&condition, false);
                        }
                    }
                    let body = body?;
                    let body_scalars = c.scalar_values.clone();
                    c.scalar_values = scalar_baseline.clone();
                    c.join_loop_scalars(&scalar_baseline, &body_scalars, scalar_live);
                    c.expect(body.ty, Type::Unit, span)?;
                    (ExprKind::While(Box::new(condition), body), Type::Unit)
                }
                ast::ExprKind::Loop(body) => {
                    c.bump_assigned(body, None);
                    let scalar_baseline = c.scalar_values.clone();
                    let scalar_live = c.kernel_locals.len();
                    c.loops.push(Loop { value: Some(Type::Never), is_while: false, expected, broke: false, invariant: None });
                    let body = c.block(body, Some(Type::Unit));
                    let state = c.loops.pop().unwrap();
                    let body = body?;
                    let body_scalars = c.scalar_values.clone();
                    c.scalar_values = scalar_baseline.clone();
                    c.join_loop_scalars(&scalar_baseline, &body_scalars, scalar_live);
                    c.expect(body.ty, Type::Unit, span)?;
                    (ExprKind::Loop(body), state.value.unwrap())
                }
                ast::ExprKind::Break(value) => {
                    let Some(state) = c.loops.last_mut() else {
                        return Err(Diagnostic::new(span, "'break' outside of a loop"));
                    };
                    state.broke = true;
                    let state = &*state;
                    let value = match value {
                        Some(value) if state.is_while => {
                            return Err(Diagnostic::new(
                                value.span,
                                "'break' with a value is only allowed in 'loop'; 'while' always produces Unit",
                            ));
                        }
                        Some(value) => {
                            let wanted = state.expected.or(state.value.filter(|t| *t != Type::Never).map(Type::full));
                            let value = c.expr_expected(value, wanted)?;
                            if value.ty.is_view() {
                                return Err(Diagnostic::new(
                                    value.span,
                                    "a borrowed view cannot escape a loop; use it inside the loop body",
                                ));
                            }
                            let previous = c.loops.last().unwrap().value.unwrap();
                            let joined = c.join(previous, value.ty, value.span)?;
                            c.loops.last_mut().unwrap().value = Some(joined);
                            Some(Box::new(value))
                        }
                        None => {
                            if state.is_while {
                                None
                            } else {
                                let previous = state.value.unwrap();
                                let wanted = state.expected.unwrap_or_else(|| {
                                    if previous == Type::Never {
                                        Type::Unit
                                    } else {
                                        previous.full()
                                    }
                                });
                                let unit = Expr {
                                    kind: ExprKind::Constant(0),
                                    ty: Type::Unit,
                                    span,
                                    resource: None,
                                };
                                let value = c.coerce(unit, wanted, span)?;
                                let joined = c.join(previous, value.ty, span)?;
                                c.loops.last_mut().unwrap().value = Some(joined);
                                Some(Box::new(value))
                            }
                        }
                    };
                    (ExprKind::Break(value, vec![]), Type::Never)
                }
                ast::ExprKind::Continue => {
                    if c.loops.is_empty() {
                        return Err(Diagnostic::new(span, "'continue' outside of a loop"));
                    }
                    if let Some(invariant) = c.loops.last().and_then(|state| state.invariant.clone()) {
                        c.prove_condition(&invariant, "the loop invariant at this 'continue'")?;
                    }
                    (ExprKind::Continue(vec![]), Type::Never)
                }
                ast::ExprKind::Block(block) => {
                    c.ensures_tail = std::mem::take(&mut c.branch_tail);
                    let block = c.block(block, expected)?;
                    let ty = block.ty;
                    (ExprKind::Block(block), ty)
                }
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                } if matches!(operand.kind, ast::ExprKind::Integer(_)) => {
                    let ast::ExprKind::Integer(text) = &operand.kind else {
                        unreachable!()
                    };
                    let ty = c.literal_type(expected);
                    (ExprKind::Constant(int_literal(text, true, ty, span)?), ty)
                }
                ast::ExprKind::Unary { op: Kind::Amp, mutable, operand } => {
                    // A field that keeps `len >= N` is never lent exclusively
                    // to code that could shorten it; element writes and pushes
                    // go through `place[i] = v` and `place.push(v)`.
                    if *mutable
                        && !c.writing_bounded_field
                        && !c.lending_spans.contains(&(span.start, span.end))
                        && c.place_min_length(operand).is_some()
                    {
                        return Err(Diagnostic::new(
                            span,
                            "this place keeps 'len >= N', so it cannot be borrowed with '&mut' except by a parameter that keeps the bound; write elements with place[i] = value, append with place.push(value), or swap the vector with place.replace(other)",
                        ));
                    }
                    // Explicit reborrow: `&*p` narrows an existing reference
                    // for one call without consuming the reference binding, and
                    // `&mut *p` may only reborrow an exclusive reference. The
                    // runtime representation is the existing one-word pointer,
                    // so the reborrow lowers to the reference local itself; the
                    // ownership pass keeps the source capability live and
                    // records the underlying storage provenance.
                    if let ast::ExprKind::Unary {
                        op: Kind::Star,
                        operand: target,
                        ..
                    } = &operand.kind
                    {
                        let ast::ExprKind::Name(_) = &target.kind else {
                            return Err(Diagnostic::new(
                                span,
                                "an explicit reborrow names one reference binding, as in '&*p' or '&mut *p'",
                            ));
                        };
                        let slot = c.slot(target.span)?;
                        let ty = c.locals[slot].ty;
                        let Some(pointer) = ty.ref_pointee() else {
                            return Err(Diagnostic::new(
                                target.span,
                                format!(
                                    "explicit reborrow expects a reference binding, found {}",
                                    c.types.name(ty)
                                ),
                            ));
                        };
                        if *mutable && !matches!(ty, Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                span,
                                "cannot reborrow a shared reference as exclusive '&mut *p'; shared storage cannot be upgraded",
                            ));
                        }
                        let reborrow = if *mutable {
                            Type::RefMut(pointer)
                        } else {
                            Type::Ref(pointer)
                        };
                        c.locals[slot].pinned = true;
                        let value = Expr {
                            kind: ExprKind::Local(slot),
                            ty: reborrow,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    if let ast::ExprKind::Slice { value, start, end } = &operand.kind {
                        return c.slice_view(
                            value,
                            start.as_deref(),
                            end.as_deref(),
                            *mutable,
                            span,
                            expected,
                        );
                    }
                    if let ast::ExprKind::Name(_) = &operand.kind {
                        let slot = c.slot(operand.span)?;
                        let value = c.borrow_local(slot, *mutable, span)?;
                        if *mutable {
                            // Writes through the reference are invisible to
                            // the solver, so the local leaves the fact system.
                            c.facts.make_opaque(slot);
                        }
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    // A field chain or index is a real addressable place.
                    // `&p.field`, `&mut p.inner.x`, and `&mut owner[i]` alias
                    // the root owner's storage instead of copying the
                    // projection into a temporary.
                    if matches!(
                        operand.kind,
                        ast::ExprKind::Field { .. } | ast::ExprKind::Index { .. }
                    ) {
                        let value = c.borrow_place_expr(operand, *mutable, span)?;
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    // A temporary owner or aggregate needs hidden storage whose
                    // cleanup outlives every checked reference. Hoist it into
                    // the enclosing statement list, then borrow that binding.
                    let value = c.expr_expected(operand, None)?;
                    if value.ty == Type::Never || value.ty.is_view() || value.ty == Type::Str {
                        return Err(Diagnostic::new(
                            span,
                            "borrow a direct local binding or an addressable field/index place; this temporary value has no stable storage",
                        ));
                    }
                    let slot = c.hoist_owner(value.ty, *mutable, span)?;
                    // Validate the hidden owner exactly as a direct local
                    // borrow would (views, nested references, mutable record
                    // fields, owner handles) and pin its storage.
                    let borrow = c.borrow_local(slot, *mutable, span)?;
                    let value = Expr {
                        kind: ExprKind::BorrowInit {
                            slot,
                            value: Box::new(value),
                        },
                        ty: borrow.ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => c.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                ast::ExprKind::Unary { op: Kind::Star, operand, .. } => {
                    // A general checked dereference read. Copying an owning or
                    // linear payload out of borrowed storage would duplicate an
                    // obligation, so only non-owning pointees may be read.
                    let reference = c.expr_expected(operand, None)?;
                    let Some(pointer) = reference.ty.ref_pointee() else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "dereference requires a reference, found {}",
                                c.types.name(reference.ty)
                            ),
                        ));
                    };
                    let pointee = c.types.pointees[pointer];
                    if c.owned_type(pointee) || c.linear_type(pointee) {
                        return Err(Diagnostic::new(
                            span,
                            "dereferencing would copy an owning or linear payload out of borrowed storage; move it with the owning operation (Box.take, Vec.pop) or read through a shared reference operation",
                        ));

                    }
                    let ty = if reference.ty == Type::Never {
                        Type::Never
                    } else {
                        pointee
                    };
                    let value = Expr {
                        kind: ExprKind::RefRead(Box::new(reference)),
                        ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => c.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                ast::ExprKind::Unary { op, operand, .. } => {
                    let hint = expected
                        .filter(|t| t.int_kind().is_some() || t.float_kind().is_some());
                    let operand = c.expr_expected(operand, hint)?;
                    let ty = match op {
                        Kind::Minus if operand.ty.float_kind().is_some() => {
                            if operand.ty == Type::Never {
                                Type::float(crate::float::FloatKind::F64)
                            } else {
                                operand.ty
                            }
                        }
                        Kind::Minus => {
                            match operand.ty.int_kind() {
                                Some(kind) if kind.signed() => {}
                                Some(kind) => {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!("cannot negate an unsigned {} value", kind.name()),
                                    ));
                                }
                                None => c.expect(operand.ty, Type::I64, span)?,
                            }
                            c.require(PANIC, span)?;
                            let goal = format!("the negation stays in {}", c.types.name(operand.ty));
                            c.record_obligation(ObligationKind::Overflow, span, goal);
                            if operand.ty == Type::Never { Type::I64 } else { operand.ty }
                        }
                        Kind::Bang if operand.ty.int_kind().is_some() => operand.ty,
                        Kind::Bang => {
                            c.expect(operand.ty, Type::Bool, span)?;
                            Type::Bool
                        }
                        Kind::Star => {
                            return Err(Diagnostic::new(
                                span,
                                "dereferencing a reference is supported only as an explicit reborrow '&*p' or '&mut *p'; read fields through 'p.field' and pass the reference itself to a call",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                "borrowing is not supported by the scalar executable subset",
                            ));
                        }
                    };
                    let ty = if operand.ty == Type::Never {
                        Type::Never
                    } else {
                        ty
                    };
                    (ExprKind::Unary(op.clone(), Box::new(operand)), ty)
                }
                ast::ExprKind::Binary {
                    op: Kind::Eq,
                    left,
                    right,
                } => {
                    if let ast::ExprKind::Name(_) = left.kind {
                        let slot = c.slot(left.span)?;
                        if !c.locals[slot].mutable {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot assign to an immutable binding; declare it with let mut",
                            ));
                        }
                        let value = c.expr_expected(right, Some(c.locals[slot].ty))?;
                        c.expect(value.ty, c.locals[slot].ty, right.span)?;
                        if let Some(required) = c.copyable_result_grade(&value)
                            && !c.locals[slot].grade.is_some_and(|grade| grade == required)
                        {
                            return Err(Diagnostic::new(
                                right.span,
                                format!(
                                    "this copyable result has the must-use @[{required}] contract; assigning it to a binding with another grade would lose the obligation. Bind it with `let` or assign it to a matching @[{required}] binding"
                                ),
                            ));
                        }
                        c.locals[slot].linear |= c.value_moves_linear(&value);
                        c.facts.assign(slot, &value);
                        c.renew_scalar_index(slot, &value)?;
                        c.written_slots.insert(slot);
                        c.closure_writes.remove(&slot);
                        if let Some(targets) = c.closure_write_targets(&value) {
                            c.closure_writes.insert(slot, targets);
                        }
                        c.closure_captures.remove(&slot);
                        if let Some(types) = c.closure_capture_types(&value) {
                            c.closure_captures.insert(slot, types);
                        }
                        let ty = if value.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Unit
                        };
                        (ExprKind::Assign(slot, Box::new(value)), ty)
                    } else if matches!(left.kind, ast::ExprKind::Field { .. })
                        && c.is_place(left)
                    {
                        let target = c.place(left)?;
                        let field_ty = target.ty;
                        // A field of a `let mut` record local is written
                        // through an exclusive borrow of that local, exactly
                        // as through an explicit `&mut` receiver.
                        let through_local = matches!(
                            split_local_projection(&target),
                            Some((slot, _)) if c.locals[slot].mutable
                        );
                        let target = match split_local_projection(&target) {
                            Some((slot, offset)) if c.locals[slot].mutable => {
                                // Facts about the local's fields are stale
                                // after a write through a borrow.
                                c.facts.make_opaque(slot);
                                let record = c.locals[slot].ty;
                                let pointer = c.types.pointer(record);
                                let borrow = Expr {
                                    kind: ExprKind::Borrow(slot),
                                    ty: Type::RefMut(pointer),
                                    span: left.span,
                                    resource: None,
                                };
                                Expr {
                                    kind: ExprKind::Project(Box::new(borrow), offset),
                                    ty: field_ty,
                                    span: target.span,
                                    resource: None,
                                }
                            }
                            Some(_) => {
                                return Err(Diagnostic::new(
                                    left.span,
                                    "cannot assign to a field of an immutable binding; declare it with let mut",
                                ));
                            }
                            None => target,
                        };
                        let Some((reference, offset)) = split_reference_projection(target) else {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment requires a 'let mut' record local or an exclusive '&mut Record' receiver",
                            ));
                        };
                        let Some(pointer) = reference.ty.ref_pointee() else {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment requires an exclusive '&mut Record' receiver",
                            ));
                        };
                        if !matches!(reference.ty, Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot write through a shared reference; the receiver must be an exclusive '&mut Record'",
                            ));
                        }
                        if c.types.pointees[pointer].layout().is_none() {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment through a reference is supported only for nominal records",
                            ));
                        }
                        if c.owned_type(field_ty)
                            || c.linear_type(field_ty)
                            || field_ty.is_view()
                            || field_ty
                                .layout()
                                .is_some_and(|id| c.types.enums[id].borrowed)
                            || field_ty
                                .layout()
                                .is_some_and(|id| c.types.enums[id].mutable_borrow)
                        {
                            return Err(Diagnostic::new(
                                left.span,
                                "only copyable, non-owning, non-borrowed record fields may be replaced through '&mut Record'; destructure or update an owning value for owned fields",
                            ));
                        }
                        let value = c.expr_expected(right, Some(field_ty))?;
                        c.expect(value.ty, field_ty, right.span)?;
                        let ty = if value.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Unit
                        };
                        if through_local && ty != Type::Never {
                            // The value may read the local (`r.a = r.a + 1`):
                            // evaluate it before the write borrows the local.
                            let slot = c.fresh_local(value.span, field_ty)?;
                            let value_span = value.span;
                            let write = Expr {
                                kind: ExprKind::RefAssign(
                                    Box::new(reference),
                                    offset,
                                    Box::new(Expr {
                                        kind: ExprKind::Local(slot),
                                        ty: field_ty,
                                        span: value_span,
                                        resource: None,
                                    }),
                                ),
                                ty,
                                span,
                                resource: None,
                            };
                            (
                                ExprKind::Block(Block {
                                    statements: vec![Statement::Let(slot, value)],
                                    tail: Some(Box::new(write)),
                                    ty,
                                }),
                                ty,
                            )
                        } else {
                            (
                                ExprKind::RefAssign(Box::new(reference), offset, Box::new(value)),
                                ty,
                            )
                        }
                    } else if let ast::ExprKind::Index {
                        value: base,
                        index,
                    } = &left.kind
                    {
                        return c.index_assign(base, index, right, span);
                    } else if let ast::ExprKind::Unary { op: Kind::Star, operand, .. } = &left.kind {
                        // `*p = value` replaces the referent exactly once. The
                        // old affine (non-linear) payload is destroyed by the
                        // lowering before the new value is stored. Owning
                        // handles keep their dedicated operations so a pointer
                        // word is never silently reinterpreted as payload.
                        let reference = c.expr_expected(operand, None)?;
                        let Some(pointer) = reference.ty.ref_pointee() else {
                            return Err(Diagnostic::new(
                                left.span,
                                "assignment through '*' requires a reference",
                            ));
                        };
                        if !matches!(reference.ty, Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot write through a shared reference; the operand must be an exclusive '&mut T'",
                            ));
                        }
                        let pointee = c.types.pointees[pointer];
                        if c.linear_type(pointee) {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot replace a linear payload through a reference; move it into an owning operation so its obligation is consumed exactly once",
                            ));
                        }
                        if matches!(
                            pointee,
                            Type::Box(_)
                                | Type::Arena
                                | Type::ArenaBox(_)
                                | Type::Bytes
                                | Type::String
                                | Type::Vec(_)
                                | Type::AllocBox(_)
                                | Type::AllocVec(_)
                        ) {
                            return Err(Diagnostic::new(
                                left.span,
                                "replace an owning handle through its own operation (Box.set/Box.reuse, Vec.push/set/clear), not by assigning through a place reference",
                            ));
                        }
                        let value = c.expr_expected(right, Some(pointee))?;
                        c.expect(value.ty, pointee, right.span)?;
                        let ty = if value.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Unit
                        };
                        (
                            ExprKind::DerefWrite(Box::new(reference), Box::new(value)),
                            ty,
                        )
                    } else {
                        return Err(Diagnostic::new(
                            left.span,
                            "assignment requires a mutable local name, a field of an exclusive '&mut Record' receiver, or an exclusive dereference '*p'",
                        ));
                    }
                }
                ast::ExprKind::Binary { op, left: left_ast, right: right_ast } => {
                    let arithmetic = matches!(
                        op,
                        Kind::Plus | Kind::Minus | Kind::Star | Kind::Slash | Kind::Percent
                            | Kind::Amp | Kind::Pipe | Kind::Caret
                    );
                    let compares = matches!(
                        op,
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne
                    );
                    let hint = if arithmetic || matches!(op, Kind::Shl | Kind::Shr) {
                        expected.filter(|t| t.int_kind().is_some() || t.float_kind().is_some())
                    } else {
                        None
                    };
                    // A literal takes its type from the other operand, so
                    // `x + 1.5` and `0.5 < x` work for both float widths. A
                    // literal operand is pure, so checking the other side first
                    // does not change evaluation order.
                    let literal = is_int_literal(left_ast) || is_float_literal(left_ast);
                    let other_literal = is_int_literal(right_ast) || is_float_literal(right_ast);
                    let (left, right) = if (arithmetic || compares) && literal && !other_literal {
                        let right = c.expr_expected(right_ast, hint)?;
                        let left = c.expr_expected(
                            left_ast,
                            right
                                .ty
                                .int_kind()
                                .map(Type::int)
                                .or_else(|| right.ty.float_kind().map(Type::float))
                                .or(hint),
                        )?;
                        (left, right)
                    } else {
                        let left = c.expr_expected(left_ast, hint)?;
                        // The right operand of && / || runs only when the left is true / false.
                        let mark = c.facts.mark();
                        let logical = matches!(op, Kind::AmpAmp | Kind::PipePipe);
                        // Taken before the right operand can bump versions.
                        let not_ran = logical
                            .then(|| c.facts.formula(&left, *op != Kind::AmpAmp))
                            .flatten();
                        if logical {
                            c.facts.assume(&left, *op == Kind::AmpAmp);
                        }
                        let inner = c.facts.mark();
                        let right_hint = if arithmetic || compares {
                            left.ty
                                .int_kind()
                                .map(Type::int)
                                .or_else(|| left.ty.float_kind().map(Type::float))
                        } else {
                            None
                        };
                        let right = c.expr_expected(right_ast, right_hint);
                        if logical {
                            // What the right operand taught (a call's
                            // postconditions) holds whenever it ran.
                            c.facts.reset_guarded(mark, inner, not_ran);
                        } else {
                            c.facts.reset(mark);
                        }
                        (left, right?)
                    };
                    if matches!(op, Kind::EqEq | Kind::Ne)
                        && left.ty == right.ty
                        && let Some((element, capacity)) = left
                            .ty
                            .layout()
                            .and_then(|id| c.types.enums[id].dynamic_array)
                    {
                        if c.owned_type(element) || c.linear_type(element) || element.is_view()
                        {
                            return Err(Diagnostic::new(
                                span,
                                "DynArray equality reads elements; owning, linear, and view elements are not comparable",
                            ));
                        }
                        if !matches!(
                            element,
                            Type::I64 | Type::Int(_) | Type::Float(_) | Type::Bool | Type::Char
                        ) {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "DynArray equality requires comparable one-word elements, found {}",
                                    c.types.name(element)
                                ),
                            ));
                        }
                        let ty = if left.ty == Type::Never || right.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Bool
                        };
                        return Ok(Expr {
                            kind: ExprKind::DynArrayEqual {
                                left: Box::new(left),
                                right: Box::new(right),
                                element,
                                capacity,
                                negate: *op == Kind::Ne,
                            },
                            ty,
                            span,
                            resource: None,
                        });
                    }
                    let mut unchecked = false;
                    let ty = match op {
                        Kind::Plus | Kind::Minus | Kind::Star | Kind::Slash | Kind::Percent
                        | Kind::Amp | Kind::Pipe | Kind::Caret => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                if !matches!(
                                    op,
                                    Kind::Plus
                                        | Kind::Minus
                                        | Kind::Star
                                        | Kind::Slash
                                        | Kind::Percent
                                ) {
                                    return Err(Diagnostic::new(
                                        span,
                                        "floating-point values support +, -, *, /, %, comparisons, and unary -, but not bitwise operators",
                                    ));
                                }
                                c.same_float(left.ty, right.ty, span)?
                            } else {
                                let ty = c.same_int(left.ty, right.ty, span)?;
                                if !matches!(op, Kind::Amp | Kind::Pipe | Kind::Caret) {
                                    // OVERFLOW-ELIDE: a result the facts keep
                                    // in range needs no runtime check.
                                    let proved = if matches!(op, Kind::Plus | Kind::Minus | Kind::Star)
                                        && ty != Type::Never
                                    {
                                        c.facts.in_range(op, &left, &right, ty, span)
                                    } else {
                                        None
                                    };
                                    match proved {
                                        Some(certificates) => {
                                            c.functions.certificates.extend(certificates);
                                            unchecked = true;
                                            let goal = format!("the result of {} stays in {}", op_text(op), c.types.name(ty));
                                            c.record_check(ObligationKind::Overflow, span, goal, true);
                                        }
                                        None => {
                                            c.require(PANIC, span)?;
                                            let (kind, goal) = if matches!(op, Kind::Slash | Kind::Percent) {
                                                (ObligationKind::Division, "the divisor is not zero and the quotient fits".to_owned())
                                            } else {
                                                (ObligationKind::Overflow, format!("the result of {} stays in {}", op_text(op), c.types.name(ty)))
                                            };
                                            c.record_obligation(kind, span, goal);
                                        }
                                    }
                                }
                                ty
                            }
                        }
                        Kind::Shl | Kind::Shr => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                return Err(Diagnostic::new(
                                    span,
                                    "floating-point values support +, -, *, /, %, comparisons, and unary -, but not shifts",
                                ));
                            }
                            let ty = c.same_int(left.ty, left.ty, span)?;
                            c.same_int(right.ty, right.ty, right_ast.span)?;
                            let goal = format!("the shift amount is below the width of {}", c.types.name(ty));
                            // SHIFT-ELIDE: an amount the facts keep in
                            // 0..bits needs no runtime check.
                            let bits = ty.int_kind().map(|kind| kind.bits());
                            let proved = match bits {
                                Some(bits) if ty != Type::Never && right.ty != Type::Never => {
                                    c.facts.shift_amount(&right, bits, span)
                                }
                                _ => None,
                            };
                            match proved {
                                Some(certificates) => {
                                    c.functions.certificates.extend(certificates);
                                    unchecked = true;
                                    c.record_check(ObligationKind::Shift, span, goal, true);
                                }
                                None => {
                                    c.require(PANIC, span)?;
                                    c.record_obligation(ObligationKind::Shift, span, goal);
                                }
                            }
                            ty
                        }
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                c.same_float(left.ty, right.ty, span)?;
                            } else if left.ty == Type::Char || right.ty == Type::Char {
                                c.expect(left.ty, Type::Char, span)?;
                                c.expect(right.ty, Type::Char, span)?;
                            } else {
                                c.same_int(left.ty, right.ty, span)?;
                            }
                            Type::Bool
                        }
                        Kind::EqEq | Kind::Ne => {
                            if left.ty.layout().is_some()
                                && right.ty.layout().is_some()
                                && c.types.is_structural(left.ty)
                                && c.types.is_structural(right.ty)
                            {
                                if left.ty != right.ty {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!(
                                            "structural equality operands must have the same canonical row, found {} and {}",
                                            c.types.name(left.ty),
                                            c.types.name(right.ty)
                                        ),
                                    ));
                                }
                                if !c.structurally_comparable(left.ty) {
                                    return Err(Diagnostic::new(
                                        span,
                                        "structural equality requires copyable scalar fields (integers, Char, Bool, Unit) or nested structural records of them; owning, borrowed, union, callable, nominal, and floating-point fields are not comparable",
                                    ));
                                }
                                return Ok(Expr {
                                    kind: ExprKind::StructEq {
                                        left: Box::new(left),
                                        right: Box::new(right),
                                        negated: *op == Kind::Ne,
                                    },
                                    ty: Type::Bool,
                                    span,
                                    resource: None,
                                });
                            }
                            let opaque = |t: Type| {
                                t.layout().is_some()
                                    || t.is_union()
                                    || matches!(
                                        t,
                                        Type::Box(_)
                                            | Type::Bytes
                                            | Type::String
                                            | Type::Stdin
                                            | Type::Stdout
                                            | Type::Ref(_)
                                            | Type::RefMut(_)
                                            | Type::Vec(_)
                                            | Type::Slice(_)
                                            | Type::SliceMut(_)
                                            | Type::Task(_) | Type::Thread(_)
                                    )
                            };
                            if opaque(left.ty) || opaque(right.ty)
                            {
                                return Err(Diagnostic::new(
                                    span,
                                    "enum equality and opaque-handle equality are not supported; union values must be narrowed with a match first. Equality requires integers, floats, Char, Bool, or Unit",
                                ));
                            }
                            if left.ty != Type::Never
                                && right.ty != Type::Never
                                && left.ty != right.ty
                            {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "equality operands must have the same type, found {} and {}",
                                        c.types.name(left.ty),
                                        c.types.name(right.ty)
                                    ),
                                ));
                            }
                            Type::Bool
                        }
                        Kind::AmpAmp | Kind::PipePipe => {
                            c.expect(left.ty, Type::Bool, span)?;
                            c.expect(right.ty, Type::Bool, span)?;
                            Type::Bool
                        }
                        _ => return Err(Diagnostic::new(span, "unsupported executable operator")),
                    };
                    let ty = if left.ty == Type::Never
                        || (right.ty == Type::Never && !matches!(op, Kind::AmpAmp | Kind::PipePipe))
                    {
                        Type::Never
                    } else {
                        ty
                    };
                    if unchecked && ty != Type::Never {
                        let kind = ty.int_kind().unwrap_or(crate::int::IntKind::I64);
                        let int_op = match op {
                            Kind::Plus => crate::int::IntOp::Unchecked(crate::int::ArithOp::Add),
                            Kind::Minus => crate::int::IntOp::Unchecked(crate::int::ArithOp::Sub),
                            Kind::Shl => crate::int::IntOp::UncheckedShift(crate::int::Shift::Left),
                            Kind::Shr => crate::int::IntOp::UncheckedShift(crate::int::Shift::Right),
                            _ => crate::int::IntOp::Unchecked(crate::int::ArithOp::Mul),
                        };
                        (
                            ExprKind::Call(Target::Int(int_op, kind, kind), vec![left, right]),
                            ty,
                        )
                    } else {
                        (
                            ExprKind::Binary(op.clone(), Box::new(left), Box::new(right)),
                            ty,
                        )
                    }
                }
                ast::ExprKind::Call { callee, arguments } => {
                    if c.constructor_target(callee).is_some() {
                        return c.construct(callee, Some(arguments), expected, span);
                    }
                    let (target_expr, explicit) = match &callee.kind {
                        ast::ExprKind::Specialize { callee, arguments } => (callee.as_ref(), Some(arguments.as_slice())),
                        _ => (callee.as_ref(), None),
                    };
                    let Some(id) = c.resolution.reference(target_expr.span) else {
                        if let ast::ExprKind::Field { value, name } = &target_expr.kind {
                            // `Type.name(..)`: an associated function.
                            if matches!(value.kind, ast::ExprKind::Name(_))
                                && let Some(type_id) = c.resolution.reference(value.span)
                                && c.resolution.bindings[type_id].kind == BindingKind::Data
                            {
                                let Some(definition) = c
                                    .functions
                                    .associated_fns
                                    .get(&type_id)
                                    .and_then(|table| table.get(name))
                                    .copied()
                                else {
                                    let type_name = &c.resolution.bindings[type_id].name;
                                    return Err(Diagnostic::new(
                                        target_expr.span,
                                        format!("unknown qualified name '{type_name}.{name}'"),
                                    ));
                                };
                                c.check_method_visibility(definition, name, span)?;
                                return c.user_call(definition.binding, explicit, arguments, expected, span);
                            }
                            if let Some((receiver, method, trait_id, trait_arguments)) =
                                c.qualified_method(target_expr)
                            {
                                return c.user_method_call(
                                    receiver,
                                    method,
                                    Some(trait_id),
                                    trait_arguments,
                                    explicit,
                                    arguments,
                                    expected,
                                    span,
                                );
                            }
                            // `replace` is a Vec method only on a Vec place
                            // (or a `&mut Vec`): the name stays free for user
                            // methods on other types.
                            let vec_replace = name == "replace"
                                && c.place_type(value).is_some_and(|ty| {
                                    let ty = match ty {
                                        Type::RefMut(pointer) => c.types.pointees[pointer],
                                        ty => ty,
                                    };
                                    matches!(ty, Type::Vec(_))
                                });
                            if Self::builtin_method(name) || vec_replace {
                                return c.method_call(
                                    value, name, explicit, arguments, expected, span,
                                );
                            }
                            return c.user_method_call(
                                value, name, None, None, explicit, arguments, expected, span,
                            );
                        }
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                callee.span,
                                "type arguments apply only to a generic named function",
                            ));
                        }
                        return c.indirect_call(callee, arguments, expected, span);
                    };
                    let binding = &c.resolution.bindings[id];
                    if c.logical.names.contains_key(&id) {
                        return Err(Diagnostic::new(
                            callee.span,
                            format!(
                                "checked logical definition '{}' is erased and cannot be called at runtime; pass it only as an erased proof argument",
                                binding.name
                            ),
                        ));
                    }
                    if c.logical.data.contains_key(&id) || c.logical.constructors.contains_key(&id) {
                        return Err(Diagnostic::new(
                            callee.span,
                            format!(
                                "'{}' belongs to a total logical data type and is erased before runtime lowering; pass it only as an erased proof argument",
                                binding.name
                            ),
                        ));
                    }
                    if c.functions.declared.contains_key(&id) {
                        return c.user_call(id, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && binding.name.starts_with("AllocatorContext.")
                    {
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                span,
                                "allocator context operations take no explicit type arguments",
                            ));
                        }
                        let name = binding.name.clone();
                        return match name.as_str() {
                            "AllocatorContext.new" => {
                                if arguments.len() != 1 {
                                    return Err(Diagnostic::new(
                                        span,
                                        "AllocatorContext.new expects one allocator-protocol instance",
                                    ));
                                }
                                c.allocator_context_new(&arguments[0], span)
                            }
                            "AllocatorContext.share" => {
                                if arguments.len() != 1 {
                                    return Err(Diagnostic::new(
                                        span,
                                        "AllocatorContext.share expects one &AllocatorContext",
                                    ));
                                }
                                c.allocator_context_share(&arguments[0], span)
                            }
                            _ => Err(Diagnostic::new(
                                span,
                                format!("unsupported allocator context operation '{name}'"),
                            )),
                        };
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("Allocator.")
                            || binding.name.starts_with("AllocBox.")
                            || binding.name.starts_with("AllocVec."))
                    {
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                span,
                                "allocator operations take no explicit type arguments; annotate the binding instead",
                            ));
                        }
                        let name = binding.name.clone();
                        return match name.as_str() {
                            "Allocator.new" => {
                                if arguments.len() != 2 {
                                    return Err(Diagnostic::new(
                                        span,
                                        "Allocator.new expects an allocation function and a release function",
                                    ));
                                }
                                c.allocator_new(&arguments[0], &arguments[1], None, span)
                            }
                            "Allocator.with_realloc" => {
                                if arguments.len() != 3 {
                                    return Err(Diagnostic::new(
                                        span,
                                        "Allocator.with_realloc expects an allocation function, a release function, and a growth function",
                                    ));
                                }
                                c.allocator_new(
                                    &arguments[0],
                                    &arguments[1],
                                    Some(&arguments[2]),
                                    span,
                                )
                            }
                            "AllocBox.new" | "AllocBox.try_new" => {
                                if arguments.len() != 2 {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!("{name} expects an allocator and one payload"),
                                    ));
                                }
                                if name == "AllocBox.new" {
                                    c.alloc_box_new(&arguments[0], &arguments[1], expected, span)
                                } else {
                                    c.alloc_box_try_new(&arguments[0], &arguments[1], expected, span)
                                }
                            }
                            "AllocBox.read" | "AllocBox.take" => {
                                if arguments.len() != 1 {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!("{name} takes exactly one argument"),
                                    ));
                                }
                                if name == "AllocBox.read" {
                                    c.alloc_box_read(&arguments[0], span)
                                } else {
                                    c.alloc_box_take(&arguments[0], span)
                                }
                            }
                            "AllocVec.new" | "AllocVec.with_capacity" => {
                                let wanted = if name == "AllocVec.new" { 1 } else { 2 };
                                if arguments.len() != wanted {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!("{name} expects {wanted} argument(s)"),
                                    ));
                                }
                                c.alloc_vec_new(
                                    &arguments[0],
                                    arguments.get(1),
                                    expected,
                                    span,
                                )
                            }
                            "AllocVec.len"
                            | "AllocVec.get"
                            | "AllocVec.push"
                            | "AllocVec.try_push"
                            | "AllocVec.pop"
                            | "AllocVec.set"
                            | "AllocVec.clear" => {
                                c.alloc_vec_call(&name, arguments, expected, span)
                            }
                            _ => Err(Diagnostic::new(
                                span,
                                format!("unsupported allocator operation '{name}'"),
                            )),
                        };
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Channel.") {
                        return c.channel_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Atomic.") {
                        return c.atomic_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("GpuBuf.") {
                        return c.gpu_buf_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && (binding.name.starts_with("Task.") || binding.name.starts_with("Thread.")) {
                        return c.task_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("DynArray.") || binding.name == "Array.fill")
                    {
                        return c.dyn_array_call(
                            &binding.name.clone(),
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Vec.") || binding.name == "Bytes.at" {
                        return c.vec_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Slice.") {
                        return c.slice_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("String.") {
                        let name = binding.name.clone();
                        return c.string_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Str.") {
                        let name = binding.name.clone();
                        return c.str_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("Int.")
                            || binding.name.starts_with("Char.")
                            || binding.name == "print_int")
                    {
                        let name = binding.name.clone();
                        return c.int_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("Float.") || binding.name == "print_float")
                    {
                        let name = binding.name.clone();
                        return c.float_call_with(
                            None,
                            &name,
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    if explicit.is_some() {
                        return Err(Diagnostic::new(callee.span, "this callee takes no type arguments"));
                    }
                    if binding.kind == BindingKind::Builtin
                        && matches!(
                            binding.name.as_str(),
                            "Arena.new"
                                | "Arena.with_strategy"
                                | "Arena.alloc"
                                | "Arena.try_alloc"
                                | "ArenaBox.read"
                                | "ArenaBox.take"
                        )
                    {
                        let name = binding.name.as_str();
                        let arity = match name {
                            "Arena.new" => 0,
                            "Arena.with_strategy" | "ArenaBox.read" | "ArenaBox.take" => 1,
                            _ => 2,
                        };
                        if arguments.len() != arity {
                            return Err(Diagnostic::new(
                                span,
                                format!("{name} requires exactly {arity} argument(s)"),
                            ));
                        }
                        match name {
                            "Arena.new" => return c.arena_new(span),
                            "Arena.with_strategy" => {
                                return c.arena_new_with(&arguments[0], span);
                            }
                            "Arena.alloc" => {
                                return c.arena_alloc(&arguments[0], &arguments[1], expected, span);
                            }
                            "Arena.try_alloc" => {
                                return c.arena_try_alloc(
                                    &arguments[0],
                                    &arguments[1],
                                    expected,
                                    span,
                                );
                            }
                            "ArenaBox.read" => {
                                return c.arena_box_read(&arguments[0], span);
                            }
                            _ => return c.arena_box_take(&arguments[0], span),
                        }
                    }
                    if binding.kind == BindingKind::Builtin && binding.name == "Bytes.try_with_capacity" {
                        if arguments.len() != 1 {
                            return Err(Diagnostic::new(
                                span,
                                "Bytes.try_with_capacity takes exactly one capacity argument",
                            ));
                        }
                        return c.bytes_try_with_capacity(&arguments[0], expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name == "Bytes.from" {
                        if let [ast::Node { kind: ast::ExprKind::String(text), .. }] = arguments.as_slice() {
                            c.require(ALLOC | PANIC, span)?;
                            let value = Expr { kind: ExprKind::BytesLiteral(text.as_bytes().to_vec()), ty: Type::Bytes, span, resource: None };
                            return match expected {
                                Some(expected) => c.coerce(value, expected, span),
                                None => Ok(value),
                            };
                        }
                        return Err(Diagnostic::new(span, "Bytes.from requires exactly one string literal; general runtime strings are deferred"));
                    }
                    if binding.kind == BindingKind::Builtin && matches!(binding.name.as_str(), "Box.new" | "Box.take" | "Box.read" | "Box.set" | "Box.reuse" | "Box.reuse_grow" | "Box.try_new" | "Box.try_reuse" | "drop") {
                        let name = binding.name.as_str();
                        let arity = if matches!(name, "Box.reuse" | "Box.reuse_grow" | "Box.try_reuse" | "Box.set") { 2 } else { 1 };
                        if arguments.len() != arity { return Err(Diagnostic::new(span, format!("{name} requires exactly {arity} argument(s)"))); }
                        match name {
                            "Box.reuse" => return c.box_reuse(&arguments[0], &arguments[1], expected, span),
                            "Box.reuse_grow" => return c.box_reuse_grow(&arguments[0], &arguments[1], expected, span),
                            "Box.try_new" => return c.box_try_new(&arguments[0], expected, span),
                            "Box.try_reuse" => return c.box_try_reuse(&arguments[0], &arguments[1], expected, span),
                            _ => {}
                        }
                        let expected_inner = if name == "Box.new" { expected.and_then(|ty| if let Type::Box(index) = ty { Some(c.types.pointees[index]) } else { None }) } else { None };
                        let arg = c.expr_expected(&arguments[0], expected_inner)?;
                        let (kind, ty) = match name {
                            "Box.new" => {
                                c.require(ALLOC | PANIC, span)?;
                                if arg.ty == Type::Never { return Err(Diagnostic::new(span, "Box.new cannot store a divergent value")); }
                                if crate::runtime_types::has_borrow(c.types, arg.ty) && !arg.ty.is_ref() && arg.ty != Type::Str && !crate::runtime_types::is_borrowed_record(c.types, arg.ty) { return Err(Diagnostic::new(span, "Box.new can store a reference element, a text view, a borrowed record, or an ordinary value, but not a slice view; keep slice views in a lexical record")); }
                                if crate::runtime_types::contains_task(c.types, arg.ty) { return Err(Diagnostic::new(span, "task handles cannot be stored in Box; join them in the scope that owns them")); }
                                let pointee = match expected_inner {
                                    Some(inner) if matches!(inner, Type::Annotated(..)) => inner,
                                    _ => c.types.full(arg.ty, span)?,
                                };
                                let ty = Type::Box(c.types.pointer(pointee)); (ExprKind::BoxNew(Box::new(arg)), ty)
                            }
                            "Box.take" => { let Type::Box(index) = arg.ty else { return Err(Diagnostic::new(span, "Box.take requires an owned Box<T>")); }; let ty = c.unannotate(c.types.pointees[index]); (ExprKind::BoxTake(Box::new(arg)), ty) }
                            "Box.read" => { let (Type::Ref(index) | Type::RefMut(index)) = arg.ty else { return Err(Diagnostic::new(span, "Box.read requires a &Box<T> or &mut Box<T>")); }; let Type::Box(inner) = c.types.pointees[index] else { return Err(Diagnostic::new(span, "Box.read requires a &Box<T> or &mut Box<T>, not another borrow type")); }; let payload = c.types.pointees[inner]; if matches!(c.unannotate(payload), Type::RefMut(_)) { return Err(Diagnostic::new(span, "Box.read cannot copy an exclusive reference element; move it out with Box.take")); } let ty = c.unannotate(payload); (ExprKind::BoxRead(Box::new(arg)), ty) }
                            "Box.set" => {
                                let Type::RefMut(index) = arg.ty else { return Err(Diagnostic::new(span, "Box.set requires an exclusive &mut Box<T>")); };
                                let Type::Box(inner) = c.types.pointees[index] else { return Err(Diagnostic::new(span, "Box.set requires an exclusive &mut Box<T>")); };
                                let payload = c.unannotate(c.types.pointees[inner]);
                                let value = c.expr_expected(&arguments[1], Some(payload))?;
                                if value.ty != Type::Never {
                                    c.expect(value.ty, payload, value.span)?;
                                }
                                if c.owned_type(value.ty) || c.linear_type(value.ty) {
                                    return Err(Diagnostic::new(value.span, "Box.set can replace a reference or copyable payload, but not an owning value; replace an owning Box with Box.reuse"));
                                }
                                (ExprKind::BoxWrite(Box::new(arg), Box::new(value)), Type::Unit)
                            }
                            _ => { if matches!(arg.ty, Type::Ref(_) | Type::RefMut(_)) { return Err(Diagnostic::new(span, "drop consumes owned/copy values, not borrowed handles")); } (ExprKind::Drop(Box::new(arg)), Type::Unit) }
                        };
                        let value = Expr { kind, ty, span, resource: None };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    let bytes_op = (binding.kind == BindingKind::Builtin).then(|| BytesOp::named(&binding.name)).flatten();
                    let io_op = (binding.kind == BindingKind::Builtin).then(|| IoOp::named(&binding.name)).flatten();
                    let host_op = (binding.kind == BindingKind::Builtin).then(|| HostOp::named(&binding.name)).flatten();
                    let (target, parameters, result, effects) = if let Some(op) = io_op {
                        match op {
                            IoOp::Stdin => (Target::Io(op, None), vec![], Type::Stdin, IO),
                            IoOp::Stdout => (Target::Io(op, None), vec![], Type::Stdout, IO),
                            IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk | IoOp::Write => {
                                let ok = if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) { Type::Bytes } else { Type::Unit };
                                let result = c.types.io_result(ok, span)?;
                                let shape = c.types.result(result, span)?;
                                let parameters = if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) {
                                    vec![Type::Stdin, Type::Bytes]
                                } else {
                                    vec![Type::Stdout, Type::Ref(c.types.pointer(Type::Bytes))]
                                };
                                (Target::Io(op, Some(shape)), parameters, result, IO)
                            }
                        }
                    } else if let Some(op) = host_op {
                        // RAW-FS-HANDLES: descriptor numbers can be reused once
                        // closed, so only std (std.file's linear File) may
                        // call the raw handle builtins. A std module is never
                        // the root unit (0), which may name itself `std.x`.
                        if op.raw_handle()
                            && (c.unit == 0
                                || c
                                    .resolution
                                    .units
                                    .get(c.unit)
                                    .is_none_or(|path| path.first().is_none_or(|p| p != "std")))
                        {
                            return Err(Diagnostic::new(
                                callee.span,
                                "raw file handle builtins are reserved for std; use std.file (open_read, read_at, write_at, sync, truncate, size, close)",
                            ));
                        }
                        let bytes = Type::Bytes;
                        let borrowed = Type::Ref(c.types.pointer(Type::Bytes));
                        let parameters = match op {
                            HostOp::FsRead | HostOp::FsList => vec![borrowed, bytes],
                            HostOp::FsWrite | HostOp::FsWriteExclusive | HostOp::FsAppend
                            | HostOp::FsRename => {
                                vec![borrowed, borrowed]
                            }
                            HostOp::FsRemove
                            | HostOp::FsMkdir
                            | HostOp::FsRemoveDir
                            | HostOp::FsIsFile
                            | HostOp::FsIsDir
                            | HostOp::FsSize
                            | HostOp::FsExists => vec![borrowed],
                            HostOp::EnvArgCount | HostOp::EnvVarCount => vec![],
                            HostOp::EnvArg => vec![Type::I64, bytes],
                            HostOp::EnvVar => vec![borrowed, bytes],
                            HostOp::TimeUnixSeconds | HostOp::TimeMonotonicNs => vec![],
                            HostOp::TimeSleepMs => vec![Type::I64],
                            HostOp::ProcRun => vec![
                                borrowed,
                                borrowed,
                                Type::RefMut(c.types.pointer(bytes)),
                                Type::I64,
                            ],
                            HostOp::NetTcpExchange => vec![
                                borrowed,
                                Type::I64,
                                borrowed,
                                Type::RefMut(c.types.pointer(bytes)),
                                Type::I64,
                            ],
                            HostOp::OsStrerror => vec![Type::I64, bytes],
                            HostOp::FsOpen => vec![borrowed, Type::I64],
                            HostOp::FsReadAt => vec![Type::I64, Type::I64, Type::I64, bytes],
                            HostOp::FsWriteAt => vec![Type::I64, Type::I64, borrowed],
                            HostOp::FsTruncate => vec![Type::I64, Type::I64],
                            HostOp::FsSync | HostOp::FsFileSize | HostOp::FsClose => {
                                vec![Type::I64]
                            }
                            HostOp::FsSyncDir => vec![borrowed],
                        };
                        let ok = match op.payload() {
                            HostPayload::Bytes => Type::Bytes,
                            HostPayload::Bool => Type::Bool,
                            HostPayload::I64 => Type::I64,
                            HostPayload::Unit => Type::Unit,
                        };
                        let (result, shape) = c.types.result_type(ok, Type::I64, span)?;
                        (Target::Host(op, shape), parameters, result, IO)
                    } else if let Some(op) = bytes_op {
                        let borrowed = Type::Ref(c.types.pointer(Type::Bytes));
                        let parameters = match op {
                            BytesOp::Clear => vec![Type::Bytes], BytesOp::WithCapacity => vec![Type::I64], BytesOp::Len | BytesOp::Capacity | BytesOp::Copy => vec![borrowed],
                            BytesOp::Get => vec![borrowed, Type::I64], BytesOp::Push | BytesOp::PushReserved => vec![Type::Bytes, Type::I64],
                        };
                        let result = match op { BytesOp::Len | BytesOp::Capacity | BytesOp::Get => Type::I64, _ => Type::Bytes };
                        let effects = match op { BytesOp::Len | BytesOp::Capacity | BytesOp::Clear => 0, BytesOp::Get | BytesOp::PushReserved => PANIC, _ => ALLOC | PANIC };
                        (Target::Bytes(op), parameters, result, effects)
                    } else if binding.kind == BindingKind::Builtin && binding.name == "print_i64" {
                        (Target::Print, vec![Type::I64], Type::Unit, IO | PANIC)
                    } else if binding.kind == BindingKind::Builtin && binding.name == "panic" {
                        (Target::Panic, vec![], Type::Never, PANIC)
                    } else {
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                callee.span,
                                "this callee takes no type arguments",
                            ));
                        }
                        return c.indirect_call(callee, arguments, expected, span);
                    };
                    if parameters.len() != arguments.len() {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "wrong argument count: expected {}, found {}",
                                parameters.len(),
                                arguments.len()
                            ),
                        ));
                    }
                    c.require(effects, span)?;
                    let mut args = Vec::new();
                    let mut diverges = false;
                    for (arg, ty) in arguments.iter().zip(parameters) {
                        let arg = c.expr_expected(arg, Some(ty))?;
                        c.expect(arg.ty, ty, arg.span)?;
                        diverges |= arg.ty == Type::Never;
                        args.push(arg);
                    }
                    (
                        ExprKind::Call(target, args),
                        if diverges { Type::Never } else { result },
                    )
                }
                ast::ExprKind::Return(value) => {
                    let value = if let Some(value) = value {
                        c.expr_expected_result(value, Some(c.result))?
                    } else {
                        let unit = Expr {
                            kind: ExprKind::Constant(0),
                            ty: Type::Unit,
                            span,
                            resource: None,
                        };
                        c.coerce(unit, c.result, span)?
                    };
                    if !(c.erased_result_context(Some(c.result)) && value.ty == Type::Unit) {
                        c.expect(value.ty, c.result, span)?;
                    }
                    if c.observes_copyable_result(&value)
                        && !c.transfers_copyable_result_from(&value)
                    {
                        return Err(Diagnostic::new(
                            value.span,
                            "this returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the function result as '@[1]' so every caller inherits exactly one observation, or observe the value here",
                        ));
                    }
                    c.check_postconditions(&value)?;
                    (ExprKind::Return(Box::new(value)), Type::Never)
                }
                ast::ExprKind::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    // Infer a branch join from its actual occurrences before
                    // instantiating an outer call parameter. Coercing both arms
                    // to an argument placeholder would erase their distinct
                    // lifetime identities before the join can compare them.
                    let expected = expected.filter(|ty| {
                        !crate::runtime_types::borrow_lifetimes(c.types, *ty)
                            .iter()
                            .any(|label| label.starts_with("<argument "))
                    });
                    let branch_tail = std::mem::take(&mut c.branch_tail);
                    let before = c.facts.version_stamp();
                    let condition = c.expr(condition)?;
                    c.expect(condition.ty, Type::Bool, condition.span)?;
                    let unwritten = c.facts.same_stamp(&before);
                    let baseline = c.facts.clone();
                    let scalar_baseline = c.scalar_values.clone();
                    let scalar_live = c.kernel_locals.len();
                    if unwritten {
                        c.facts.assume_unwritten(&condition, true);
                    } else {
                        c.facts.assume(&condition, true);
                    }
                    let has_else = otherwise.is_some();
                    let then_expected = if has_else { expected } else { Some(Type::Unit) };
                    c.ensures_tail = branch_tail && has_else;
                    let then = c.block(then, then_expected);
                    let then_facts = c.facts.clone();
                    c.facts = baseline.clone();
                    let then = then?;
                    let then_scalars = c.scalar_values.clone();
                    c.scalar_values = scalar_baseline.clone();
                    let otherwise = if let Some(otherwise) = otherwise {
                        if unwritten {
                            c.facts.assume_unwritten(&condition, false);
                        } else {
                            c.facts.assume(&condition, false);
                        }
                        // With the call-argument expectation deferred above,
                        // no fallback context may erase the arm's actual
                        // labels either.
                        let context = expected;
                        c.ensures_tail = branch_tail;
                        let tail = c.expr_expected_result(otherwise, context);

                        let tail = tail?;
                        let ty = tail.ty;
                        Block {
                            statements: vec![],
                            tail: Some(Box::new(tail)),
                            ty,
                        }
                    } else {
                        Block {
                            statements: vec![],
                            tail: None,
                            ty: Type::Unit,
                        }
                    };
                    let otherwise_scalars = c.scalar_values.clone();
                    // Only a branch that falls through reaches the join, so
                    // a diverging branch's rewrites do not weaken the facts
                    // after it (its opaque slots stay opaque: that set is
                    // sticky and loop heads rely on it).
                    if then.ty == Type::Never && otherwise.ty != Type::Never {
                        c.facts.keep_opaque_of(&then_facts);
                    } else if otherwise.ty == Type::Never && then.ty != Type::Never {
                        let mut kept = then_facts;
                        kept.keep_opaque_of(&c.facts);
                        c.facts = kept;
                    } else {
                        c.facts = crate::facts::Facts::branch_join(&baseline, &then_facts, &c.facts);
                    }
                    c.join_scalars(
                        &scalar_baseline,
                        &then_scalars,
                        &otherwise_scalars,
                        scalar_live,
                        then.ty == Type::Never,
                        otherwise.ty == Type::Never,
                    );
                    let (then, otherwise, ty) = if has_else {
                        if c.erased_result_context(expected)
                            && (then.ty == Type::Unit || otherwise.ty == Type::Unit)
                        {
                            (c.erase_block_value(then, span), c.erase_block_value(otherwise, span), Type::Unit)
                        } else {
                            // Branch arms must not launder an invariant record
                            // lifetime through one another: the call or the
                            // surrounding context derives identities from
                            // these actual labels. If they disagree, the
                            // union's label-erased normalization would silently
                            // absorb one arm into the other.
                            check_branch_record_labels(c.types, then.ty, otherwise.ty, span)?;
                            let ty = c.join(then.ty, otherwise.ty, span)?;
                            let then = c.coerce_block(then, ty, span)?;
                            let otherwise = c.coerce_block(otherwise, ty, span)?;
                            (then, otherwise, ty)
                        }
                    } else {
                        // An `if` without `else` is a statement: the taken
                        // branch must produce Unit, never an implicit optional
                        // union value.
                        let then = c.coerce_block(then, Type::Unit, span)?;
                        (then, otherwise, Type::Unit)
                    };
                    (ExprKind::If(Box::new(condition), then, otherwise), ty)
                }
                ast::ExprKind::Try(value) => {
                    if c.ensures_context.is_some() {
                        return Err(Diagnostic::new(
                            span,
                            "'?' cannot leave a function with postconditions; match the result and return explicitly",
                        ));
                    }
                    let value = c.expr(value)?;
                    let input = c.types.result(value.ty, span)?;
                    let output = c.types.result(c.result, span)?;
                    c.expect(input.error, output.error, span)?;
                    if !c.same_layout(input.error, output.error) {
                        return Err(Diagnostic::new(
                            span,
                            "'?' cannot repack a heterogeneous error type; widen the operand explicitly or match the error before returning",
                        ));
                    }
                    let ty = input.ok;
                    (
                        ExprKind::Try {
                            value: Box::new(value),
                            input,
                            output,
                        },
                        ty,
                    )
                }
                ast::ExprKind::Match { value, arms } => {
                    let branch_tail = std::mem::take(&mut c.branch_tail);
                    let value = c.expr(value)?;
                    // A shared or exclusive reference to a DynArray is matched
                    // by borrowed slice patterns; every other borrow is
                    // rejected.
                    let borrowed_array = matches!(value.ty, Type::Ref(pointer) | Type::RefMut(pointer)
                        if c.types.pointees[pointer]
                            .layout()
                            .is_some_and(|id| c.types.enums[id].dynamic_array.is_some()));
                    if !borrowed_array
                        && (matches!(value.ty, Type::Never | Type::Ref(_) | Type::RefMut(_))
                            || value.ty.is_view())
                    {
                        return Err(Diagnostic::new(
                            value.span,
                            "cannot match a divergent, borrowed-reference, or borrowed-view expression (including &str)",
                        ));
                    }
                    if borrowed_array
                        && let Some(arm) = arms.iter().find(|arm| {
                            !matches!(
                                arm.pattern.kind,
                                ast::PatternKind::Slice(_) | ast::PatternKind::Wildcard
                            )
                        })
                    {
                        return Err(Diagnostic::new(
                            arm.pattern.span,
                            "a match on a '&DynArray' or '&mut DynArray' borrow supports slice patterns such as '[x, .., y]' and '_'",
                        ));
                    }
                    let mut coverage = Coverage::new(span);
                    // Variants excluded by the scrutinee's type need no arm.
                    if let Type::Variants(id, mask) = value.ty {
                        for (tag, variant) in c.types.enums[id].variants.iter().enumerate() {
                            if mask & (1 << tag) == 0 {
                                coverage.add(&Pattern::Variant {
                                    tag,
                                    tagged: true, niche: None,
                                    fields: variant.fields.iter().map(|_| (0, Pattern::Any)).collect(),
                                });
                            }
                        }
                    }
                    let mut result = Type::Never;
                    let mut checked = Vec::new();
                    // Every arm starts from the scalar state before the match,
                    // and the reaching arms are joined afterwards.
                    let scalar_baseline = c.scalar_values.clone();
                    let scalar_live = c.kernel_locals.len();
                    let mut arm_scalars = Vec::new();
                    // Variants still possible after earlier unguarded arms.
                    let mut remaining = c.mask(value.ty);
                    // An unguarded `[..]` / `[..rest]` matches every DynArray
                    // length. Coverage keeps treating it as a length pattern so
                    // a later `_` stays accepted, but the match is exhaustive.
                    let mut length_catch_all = false;
                    for arm in arms {
                        c.scalar_values = scalar_baseline.clone();
                        let pattern = c.pattern_refined(&arm.pattern, value.ty, remaining)?;
                        c.linear_pattern(
                            &pattern,
                            c.value_moves_linear(&value) && !c.linear_type(value.ty),
                        );
                        if !coverage.useful(&pattern, value.ty, &c.types.enums, &c.types.unions)? {
                            return Err(Diagnostic::new(arm.span, "unreachable match arm/pattern"));
                        }
                        let mark = c.facts.mark();
                        c.assume_pattern(&value, &pattern);
                        let guard = arm.guard.as_ref().map(|guard| c.expr(guard)).transpose()?;
                        if let Some(guard) = &guard {
                            c.expect(guard.ty, Type::Bool, guard.span)?;
                            c.facts.assume(guard, true);
                        }
                        let context = match expected {
                            Some(expected) => Some(expected),
                            None if c.needs_context(&arm.body) && result != Type::Never => {
                                Some(c.types.full(result, span)?)
                            }
                            None => None,
                        };
                        c.ensures_tail = branch_tail;
                        let body = c.expr_expected_result(&arm.body, context);
                        c.facts.reset(mark);
                        let body = body?;
                        arm_scalars.push((c.scalar_values.clone(), body.ty == Type::Never));
                        result = c.join(result, body.ty, body.span)?;
                        if guard.is_none() {
                            remaining &= !covered_variants(&pattern);
                        }
                        if guard.is_none() {
                            coverage.add(&pattern);
                            length_catch_all |= matches!(
                                &pattern,
                                Pattern::DynArray { prefix, suffix, rest: true, .. }
                                    if prefix.is_empty() && suffix.is_empty()
                            );
                        }
                        checked.push(Arm {
                            pattern,
                            guard,
                            body,
                        });
                    }
                    if !length_catch_all
                        && coverage.useful(&Pattern::Any, value.ty, &c.types.enums, &c.types.unions)?
                    {
                        return Err(Diagnostic::new(
                            span,
                            "non-exhaustive match; add missing cases or an unguarded catch-all",
                        ));
                    }
                    c.scalar_values = scalar_baseline.clone();
                    let arm_refs = arm_scalars
                        .iter()
                        .map(|(map, diverges)| (map, *diverges))
                        .collect::<Vec<_>>();
                    c.join_scalar_arms(&scalar_baseline, &arm_refs, scalar_live);
                    if c.erased_result_context(expected)
                        && (checked.iter().any(|arm| {
                            arm.body.ty == Type::Unit || arm.body.ty == Type::Never
                        }))
                    {
                        for arm in &mut checked {
                            if arm.body.ty == Type::Never {
                                continue;
                            }
                            let placeholder = Expr {
                                kind: ExprKind::Constant(0),
                                ty: Type::Unit,
                                span: arm.body.span,
                                resource: None,
                            };
                            let body = std::mem::replace(&mut arm.body, placeholder);
                            arm.body = c.erase_value(body, span);
                        }
                        result = Type::Unit;
                    }
                    if result != Type::Never && result != expected.unwrap_or(Type::Never) {
                        for arm in &mut checked {
                            if arm.body.ty == Type::Never {
                                continue;
                            }
                            let placeholder = Expr {
                                kind: ExprKind::Constant(0),
                                ty: Type::Unit,
                                span: arm.body.span,
                                resource: None,
                            };
                            let body = std::mem::replace(&mut arm.body, placeholder);
                            arm.body = c.coerce(body, result, span)?;
                        }
                    }
                    (ExprKind::Match(Box::new(value), checked), result)
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this expression is not implemented in the executable subset yet",
                    ));
                }
            };
            let expr = Expr {
                kind,
                ty,
                span,
                resource: None,
            };
            if let Some(expected) = expected {
                return c.coerce(expr, expected, span);
            }
            Ok(expr)
        })
    }
}
