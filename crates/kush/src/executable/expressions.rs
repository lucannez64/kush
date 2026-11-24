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
                // LANG-NAT-VALUE: a `N: Nat` parameter read as a value is the
                // instance's `i64` constant, so the prover knows its value.
                ast::ExprKind::Name(_)
                    if let Some(id) = c.resolution.reference(span)
                        && let Some(&value) = c.consts.get(&id) =>
                {
                    let value = i64::try_from(value).map_err(|_| {
                        Diagnostic::new(
                            span,
                            format!("the natural {value} does not fit in an i64 value"),
                        )
                    })?;
                    (ExprKind::Constant(value), Type::I64)
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
                    return c.array_expression(expr, values, expected);
                }
                ast::ExprKind::Index { value, index } => {
                    return c.index_expression(expr, value, index, expected);
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
                    return c.assignment_expression(expr, left, right, expected);
                }
                ast::ExprKind::Binary { op, left: left_ast, right: right_ast } => {
                    return c.binary_expression(expr, op, left_ast, right_ast, expected);
                }
                ast::ExprKind::Call { callee, arguments } => {
                    return c.call_expression(expr, callee, arguments, expected);
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
                    return c.if_expression(expr, condition, then, otherwise, expected);
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
            c.finish_expression(kind, ty, span, expected)
        })
    }
    /// The shared tail of `expr_expected_unchecked`: build the expression
    /// from its kind and type, and coerce it to the expected type.
    pub(super) fn finish_expression(
        &mut self,
        kind: ExprKind,
        ty: Type,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let expr = Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        if let Some(expected) = expected {
            return self.coerce(expr, expected, span);
        }
        Ok(expr)
    }
}
