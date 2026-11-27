//! Effect handlers: handle, capability thunks and abortive handles.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Check one lexically scoped, one-shot tail-resumptive handler.
    ///
    /// The handler is an ordinary first-class callable of type
    /// `fn(P, linear once fn(R) -> R) -> R` (or `once`/`linear once`). It is
    /// evaluated once and stored in a hidden local. `perform` calls it with the
    /// payload and a fresh identity resumption token. The token is linear, so
    /// the handler must invoke it exactly once on every normal path; invoking it
    /// twice is a use-after-move, and returning without invoking it is an
    /// unconsumed linear obligation. There is no captured continuation, so a
    /// second resumption (multishot) is unrepresentable.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn handle_effect(
        &mut self,
        operation: &str,
        parameter: &ast::Type,
        result: &ast::Type,
        handler: &ast::Expr,
        body: &ast::Block,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let capability = self.pending_capability.take();
        let parameter_ty = self.ty(parameter)?;
        let result_ty = if self.types.names_never(result) {
            Type::Never
        } else {
            self.ty(result)?
        };
        let declared = self.effect_operations.get(operation).copied();
        if capability.is_some() && declared.is_none() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'handle {operation} as ...' binds a capability, which needs a declared effect operation; write 'effect {operation}: P -> R;'"
                ),
            ));
        }
        if let Some(declared) = declared
            && (parameter_ty != declared.parameter || result_ty != declared.result)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "handler for '{operation}' must use the declared operation signature {} -> {}, found {} -> {}",
                    self.types.name(declared.parameter),
                    self.types.name(declared.result),
                    self.types.name(parameter_ty),
                    self.types.name(result_ty)
                ),
            ));
        }
        if matches!(parameter_ty, Type::Never) {
            return Err(Diagnostic::new(
                span,
                "a handled operation cannot use Never as its payload type",
            ));
        }
        if matches!(result_ty, Type::Never) {
            return self.abortive_handle(
                operation,
                parameter_ty,
                handler,
                body,
                expected,
                span,
                capability.is_some(),
                declared.map(|declared| declared.id),
            );
        }
        let handler_value = self.expr(handler)?;
        let Some((handler_id, _)) = Self::function_parts(handler_value.ty) else {
            return Err(Diagnostic::new(
                handler.span,
                "an effect handler must be a first-class fn/once fn value",
            ));
        };
        let signature = self.types.function_types[handler_id].clone();
        let one_shot = self.resume_type(result_ty, false);
        let multi_shot = self.resume_type(result_ty, true);
        if signature.parameters.len() != 2 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "an effect handler takes the payload and one resumption token, found {} parameter(s)",
                    signature.parameters.len()
                ),
            ));
        }
        // A one-shot token of a lexical operation may name abortive
        // operations that leave through it (E-ABORT-INTERACT).
        // E-ABORT-ENTRIES: also tokens of declared operations and multishot
        // tokens (`fn(R) -> R ! {F}`).
        let (token_effects, token_multishot) = match signature.parameters[1] {
            Type::Once(id) | Type::Fn(id) => {
                let effects = self.types.function_types[id].effects;
                let multishot = matches!(signature.parameters[1], Type::Fn(_));
                let named = effects != 0
                    && effects & !self.abortive_bits() == 0
                    && signature.parameters[1]
                        == self.resume_type_with(result_ty, multishot, effects);
                (named.then_some(effects), multishot)
            }
            Type::Multi(id) => {
                let effects = self.types.function_types[id].effects;
                let named = effects != 0
                    && effects & !self.abortive_bits() == 0
                    && signature.parameters[1]
                        == Type::Multi(self.types.multi_token_with(result_ty, effects));
                (named.then_some(effects), true)
            }
            _ => (None, false),
        };
        let multi_token = Type::Multi(self.types.multi_token(result_ty));
        let multi = signature.parameters[1] == multi_token
            || (matches!(signature.parameters[1], Type::Multi(_)) && token_effects.is_some());
        let multishot = if multi {
            true
        } else if signature.parameters[1] == one_shot
            || (token_effects.is_some() && !token_multishot)
        {
            false
        } else if signature.parameters[1] == multi_shot || token_effects.is_some() {
            true
        } else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler's second parameter must be exactly 'linear once fn({}) -> {}' for one-shot resumption, or 'multi fn({}) -> {}' or 'fn({}) -> {}' for multishot resumption",
                    self.types.name(result_ty),
                    self.types.name(result_ty),
                    self.types.name(result_ty),
                    self.types.name(result_ty),
                    self.types.name(result_ty),
                    self.types.name(result_ty)
                ),
            ));
        };
        if !self.subtype(parameter_ty, signature.parameters[0]) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler parameter accepts {}, which is not a supertype of the performed payload {}",
                    self.types.name(signature.parameters[0]),
                    self.types.name(parameter_ty)
                ),
            ));
        }
        if !self.subtype(signature.result, result_ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler returns {}, which is not a subtype of the operation result {}",
                    self.types.name(signature.result),
                    self.types.name(result_ty)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        // A capability handler with effects is capability-only: it is not
        // pushed on the dynamic stack, so no call can perform `Op` by name
        // through it and hide its effects from a row.
        let capability_only = capability.is_some() && signature.effects != 0;
        // Only a noncapturing, one-shot, tail-resumptive capability runs in
        // place anywhere, so only it may be passed to functions; any other
        // handler bound `as op` is performed through the lexical machinery
        // of its own body.
        let passable = matches!(
            &handler_value.kind,
            ExprKind::FnValue { captures, .. } if captures.is_empty()
        ) && matches!(handler_value.ty, Type::Fn(_))
            && (!multishot || multi)
            && tail_resumptive_handler(self.resolution, handler)
            // A handler that performs declared operations would run in place
            // inside the callee, where the callee's own handlers could
            // intercept them; only builtin effects may travel with it.
            && signature.effects & !EFFECT_BITS == 0;
        if declared.is_some() && !capability_only {
            if !matches!(handler_value.ty, Type::Fn(_) | Type::Once(_)) {
                return Err(Diagnostic::new(
                    handler.span,
                    "a dynamically visible handler must be a fn or once fn value",
                ));
            }
            // Declared operations name the effects their handlers may have;
            // E-ABORT-ENTRIES: a one-shot handler may also abort with the
            // abortive operations its token names.
            let latent = declared.map_or(0, |declared| declared.latent);
            if signature.effects & !(latent | token_effects.unwrap_or(0)) != 0 {
                return Err(Diagnostic::new(
                    handler.span,
                    if latent == 0 {
                        "a dynamically visible handler must be pure; perform in a called function would otherwise hide the handler's effects from the caller's row. Declare the effects the handler may have on the operation: 'effect Op: P -> R ! { io };'".to_owned()
                    } else {
                        format!(
                            "this handler's effects {} are not among the operation's declared effects {}",
                            effect_names(self.resolution, signature.effects),
                            effect_names(self.resolution, latent)
                        )
                    },
                ));
            }
        }
        // A multishot handler bound `as op` is never on the dynamic stack (a
        // perform by name would bring a one-shot token), so it is
        // capability-only too: it does not discharge `Op` for its body.
        let declared = declared.filter(|_| !capability_only && !(multi && capability.is_some()));
        let handler_type = handler_value.ty;
        let slot = self.fresh_local(span, handler_type)?;
        if let Some((_, binder)) = &capability {
            let id = self.resolution.binder(*binder).ok_or_else(|| {
                Diagnostic::new(*binder, "internal error: unresolved capability binder")
            })?;
            self.slots.insert(id, slot);
            self.capability_slots.insert(slot);
        }
        self.locals[slot].linear = signature.linear;
        if let Some(targets) = self.closure_write_targets(&handler_value) {
            self.closure_writes.insert(slot, targets);
        }
        let handler_parameter = signature.parameters[0];
        let handler_result = signature.result;
        // A statically tail-resumptive handler (`resume(e)` as its only use of
        // the token, in tail position) observes no continuation: `h(p, k)` is
        // `k(e)`, so every perform may use the identity token and continue in
        // place. Otherwise any perform outside the body's tail suspends.
        // A declared operation can also be performed by called functions;
        // under a non-tail handler those calls become await points.
        let lexical = body_has_non_tail_perform(body, operation)
            || capability
                .as_ref()
                .is_some_and(|(name, _)| body_has_non_tail_perform(body, name));
        // A multishot handler for a declared operation is never pushed on the
        // dynamic stack (a dynamic perform supplies the one-shot token), so
        // its body is always checked as suspendable and calls that could
        // perform the operation are rejected.
        // A tail-resumptive handler runs in place at the perform, under any
        // handler the body installed. If its own row has a declared
        // operation that the body also handles, its perform would reach the
        // body's handler instead of the one outside this `handle`; such a
        // handler suspends instead, where performs inside nested handles are
        // rejected.
        let shadows_handler_effects = body_handles_any(body, signature.effects, self.resolution);
        // The body passes its capability to called functions: under a
        // non-tail handler those calls resume through resumable entries keyed
        // by the capability parameter (EFF-CAP-RESUME-CALLS).
        let capability_awaits = capability.as_ref().is_some_and(|(_, binder)| {
            let mut refs = BTreeSet::new();
            collect_lambda_refs(self.resolution, body, &mut refs);
            self.resolution
                .binder(*binder)
                .is_some_and(|id| refs.contains(&id))
        });
        // EFF-CAP-RESUME-CAPTURING: a capturing one-shot handler of a declared
        // operation lives in its dynamic frame; callees given its capability
        // reach that frame through a trampoline, under resumable entries only.
        let noncapturing = matches!(
            &handler_value.kind,
            ExprKind::FnValue { captures, .. } if captures.is_empty()
        ) && matches!(handler_value.ty, Type::Fn(_));
        // CAP-CAPTURING-LEXICAL: a capturing handler with effects is not
        // dynamically visible; it gets a frame under a private operation id
        // that only its trampoline looks up.
        let private_frame = capability_only && !multishot && !noncapturing;
        // Types of the handler's captured values. An opaque handler value
        // (not a lambda or function here) was checked where it was built;
        // its captures are not visible.
        let known_captures = self.closure_capture_types(&handler_value);
        let copyable_captures = matches!(handler_value.ty, Type::Once(_))
            && !signature.linear
            && known_captures.as_ref().is_some_and(|captures| {
                !captures.is_empty()
                    && captures
                        .iter()
                        .all(|ty| !self.owned_type(*ty) && !self.linear_type(*ty))
            });
        // EFF-CAP-RESUME-MULTISHOT: a capturing `multi fn` handler whose
        // captures are copyable gets a reusable frame under a private
        // operation id; callees reach it through a trampoline that passes
        // their `multi fn` token on, once per perform.
        let multi_framed = capability.is_some() && multi && !noncapturing && copyable_captures;
        let framed = (capability.is_some()
            && (declared.is_some() || private_frame)
            && !multishot
            && !noncapturing)
            || multi_framed;
        // Only when the capability is passed to a call: in its own body the
        // handler is performed through its local.
        let passes_capability = capability.as_ref().is_some_and(|(_, binder)| {
            self.resolution
                .binder(*binder)
                .is_some_and(|id| block_passes_binding(self.resolution, body, id))
        });
        // A framed handler on the dynamic stack resumes callees through
        // resumable entries only when its capability is passed to them; a
        // tail-resumptive one performed only in its own body is served from
        // its frame like a perform by name.
        let region = ((!tail_resumptive_handler(self.resolution, handler)
            || shadows_handler_effects)
            && (lexical || declared.is_some() || capability_awaits))
            || (declared.is_some() && multishot)
            || (framed && capability_awaits && (declared.is_none() || passes_capability));
        if capability.is_some() && passable && !region {
            self.capability_passable.insert(slot);
        }
        // A noncapturing one-shot handler with code after `resume`: calls
        // given its capability become await points.
        // A noncapturing `multi fn` handler resumes callees through their
        // `cap multi` entries (docs/multishot-capabilities.md section 6.1).
        let capability_resumable = capability.is_some()
            && region
            && ((!multishot && (noncapturing || framed)) || (multi && (noncapturing || framed)));
        if capability_resumable {
            self.capability_resumable.insert(slot);
        }
        // A multishot handler is never found by name: its frame is private.
        let private_operation =
            (framed && region && passes_capability && (declared.is_none() || multi)).then(|| {
                self.functions.private_operations += 1;
                PRIVATE_OPERATION_BASE + self.functions.private_operations
            });
        if framed
            && region
            && let Some(operation_id) = declared
                .filter(|_| !multi)
                .map(|declared| declared.id)
                .or(private_operation)
        {
            self.capability_framed
                .insert(slot, (operation_id, handler_id, signature.effects));
        }
        let handler_function = match &handler_value.kind {
            ExprKind::FnValue { function, captures } if captures.is_empty() => Some(*function),
            _ => None,
        };
        let handler_writes = self.closure_writes.get(&slot).cloned().unwrap_or_default();
        let handler_refs = self.closure_reference_targets(&handler_value);
        // A capturing tail-resumptive handler of a declared operation whose
        // captures are all copyable (references, by-reference scalars,
        // plain values) can serve every perform from a copy of its
        // environment, like a noncapturing `fn`.
        let reusable = declared.is_some() && !multishot && !region && copyable_captures;
        // Any other capturing handler pushed on the dynamic stack is moved
        // there too: a perform in its own body reaches it through the frame
        // (a second one panics, as a second perform from a callee does).
        let in_frame =
            declared.is_some() && !multishot && !region && !matches!(handler_type, Type::Fn(_));
        let handler_capture_types = known_captures.unwrap_or_default();
        self.handlers.push(HandlerScope {
            operation: operation.to_owned(),
            parameter: parameter_ty,
            result: result_ty,
            slot,
            handler_parameter,
            handler_result,
            effects: signature.effects,
            multishot,
            multi,
            region,
            points: 0,
            declared: declared.is_some(),
            abort: None,
            token_effects: token_effects.unwrap_or(0),
            in_frame,
        });
        // A lexical handle discharges the declared operation's row requirement
        // for its body: the body is checked as if `Op` were available, while the
        // enclosing function row is untouched. Calls to other functions that
        // declare `{Op}` are therefore satisfied here.
        // Only a handler on the dynamic stack (or an undeclared lexical
        // operation, whose bit is 0) discharges the operation's row bit: a
        // capability-only handler must not hide a called function's `Op`.
        let operation_effect = if declared.is_some() || capability.is_none() {
            self.operation_effect(operation)
        } else {
            0
        };
        let saved_effects = self.effects;
        self.effects |= operation_effect;
        // The discharged operation never reaches an inferred lambda row.
        let saved_required = self.required_effects.replace(0);
        let checked = self.checked_effect_body(
            body,
            result_ty,
            expected,
            span,
            region.then_some(SuspendableSite {
                name: operation.to_owned(),
                handler_captures: handler_capture_types.clone(),
                handler_once: matches!(handler_type, Type::Once(_)),
                handler_parameter,
                handler_refs: handler_refs.clone(),
                lexical,
                operation: declared.map(|declared| declared.id),
                multishot,
                multi,
                handler_function,
                handler_writes,
                effects: saved_effects,
                token_effects: token_effects.unwrap_or(0),
                capability_slot: capability_resumable.then_some(slot),
            }),
        );
        self.effects = saved_effects;
        self.required_effects
            .set(saved_required | (self.required_effects.get() & !operation_effect));
        self.handlers.pop();
        let inner = checked?;
        let ty = inner.ty;
        let pushed = declared
            .filter(|_| !multishot)
            .map(|declared| declared.id)
            .or(private_operation);
        let tail = match pushed {
            Some(operation) => Expr {
                kind: ExprKind::HandlerPush {
                    operation,
                    handler: Box::new(Expr {
                        kind: ExprKind::Local(slot),
                        ty: handler_type,
                        span,
                        resource: None,
                    }),
                    body: Box::new(inner),
                    // A multishot frame serves every perform of every branch.
                    reusable: reusable || multi_framed,
                },
                ty,
                span,
                resource: None,
            },
            None => Expr {
                kind: ExprKind::Block(inner),
                ty,
                span,
                resource: None,
            },
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements: vec![Statement::Let(slot, handler_value)],
                tail: Some(Box::new(tail)),
                ty,
            }),
            ty,
            span,
            resource: None,
        })
    }
    /// EFF-CAP-RESUME-CAPTURING: a noncapturing function
    /// `fn(P, token) -> R ! {}` that performs the declared operation
    /// through the dynamic stack. Passed in place of a capturing capability,
    /// it reaches the capability's own frame: callees perform through it only
    /// in resumable entries, which never run under a nested handler for the
    /// operation, and resumed continuations hide frames the handler pushed.
    /// The frame's consumed flag makes a second perform panic.
    pub(super) fn capability_thunk(
        &mut self,
        operation: usize,
        arrow: usize,
        effects: u16,
        span: Span,
    ) -> Result<(usize, Type)> {
        if let Some(found) = self.functions.capability_thunks.get(&(operation, arrow)) {
            return Ok(*found);
        }
        let handler = self.types.function_types[arrow].clone();
        let parameters = handler.parameters.clone();
        let result = handler.result;
        // The trampoline has the handler's effects (a capability-only
        // handler may have some) and `panic` for a consumed frame.
        let id = self.types.function_type_with(
            parameters.clone(),
            result,
            PANIC | effects,
            vec![None; parameters.len()],
            None,
            false,
            false,
            crate::runtime_types::BorrowSig::default(),
        );
        let ty = Type::Fn(id);
        let locals = parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| Local {
                ty: *ty,
                mutable: false,
                linear: index == 1,
                pinned: false,
                grade: None,
                span,
            })
            .collect();
        let local = |slot: usize| Expr {
            kind: ExprKind::Local(slot),
            ty: parameters[slot],
            span,
            resource: None,
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::DynamicPerform {
                    operation,
                    payload: Box::new(local(0)),
                    resume: Box::new(local(1)),
                    handler: arrow,
                },
                ty: result,
                span,
                resource: None,
            })),
            ty: result,
        };
        let function = Function {
            name: "<capability trampoline>".to_owned(),
            parameters: parameters.len(),
            closure: None,
            capture_refs: vec![],
            capture_writes: vec![],
            locals,
            result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: vec![None; parameters.len()],
            result_grade: None,
            parameter_lifetimes: vec![None; parameters.len()],
            result_lifetime: None,
            lifetime_bounds: BTreeSet::new(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: BTreeSet::new(),
            parameter_slots: None,
            local_borrowed: vec![],
            local_copyable: vec![],
            capability_parameters: vec![],
            shared_environment: false,
        };
        let signature = Signature {
            call_contract: None,
            binding: usize::MAX,
            name: function.name.clone(),
            parameters: parameters.clone(),
            result,
            effects: PANIC | effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: vec![None; parameters.len()],
            result_grade: None,
            parameter_lifetimes: vec![None; parameters.len()],
            result_lifetime: None,
            lifetime_bounds: BTreeSet::new(),
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        let index = self.functions.add_synthetic(signature, function)?;
        self.functions
            .capability_thunks
            .insert((operation, arrow), (index, ty));
        Ok((index, ty))
    }
    /// `handle F: P -> Never with h { body }` (E-ABORT-LEXICAL,
    /// docs/abortive-handlers.md 3.1-3.2). `h` takes only the payload and
    /// returns the `handle`'s result; a `perform F(x)` lexically inside the
    /// body leaves it like a labelled `break`, with the cleanup and linear
    /// checks of an early exit, and the `handle`'s value is `h(x)`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn abortive_handle(
        &mut self,
        operation: &str,
        parameter_ty: Type,
        handler: &ast::Expr,
        body: &ast::Block,
        expected: Option<Type>,
        span: Span,
        capability: bool,
        declared: Option<usize>,
    ) -> Result<Expr> {
        if capability {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the abortive operation '{operation}' cannot be bound as a capability; capabilities serve resumptive operations"
                ),
            ));
        }
        if self.borrowing_type(parameter_ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the payload of the abortive operation '{operation}' cannot hold a borrow: it outlives the body it leaves"
                ),
            ));
        }
        let handler_value = self.expr(handler)?;
        let Some((handler_id, _)) = Self::function_parts(handler_value.ty) else {
            return Err(Diagnostic::new(
                handler.span,
                "an effect handler must be a first-class fn/once fn value",
            ));
        };
        let signature = self.types.function_types[handler_id].clone();
        if signature.parameters.len() != 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a handler for the abortive operation '{operation}' takes only the payload and no resumption token, found {} parameter(s)",
                    signature.parameters.len()
                ),
            ));
        }
        if signature.linear || !matches!(handler_value.ty, Type::Fn(_) | Type::Once(_)) {
            return Err(Diagnostic::new(
                handler.span,
                "a handler for an abortive operation runs only when the body aborts, so it must be a 'fn' or 'once fn' value, not a linear one",
            ));
        }
        if !self.subtype(parameter_ty, signature.parameters[0]) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler parameter accepts {}, which is not a supertype of the performed payload {}",
                    self.types.name(signature.parameters[0]),
                    self.types.name(parameter_ty)
                ),
            ));
        }
        // A dynamic perform hands over the declared payload unconverted.
        if declared.is_some() && signature.parameters[0] != parameter_ty {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler of the declared abortive operation '{operation}' must take exactly its payload type {}, found {}",
                    self.types.name(parameter_ty),
                    self.types.name(signature.parameters[0])
                ),
            ));
        }
        if signature.result == Type::Never || self.borrowing_type(signature.result) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a handler for the abortive operation '{operation}' must return a value without borrows, found {}",
                    self.types.name(signature.result)
                ),
            ));
        }
        if signature.effects & self.abortive_bits() != 0 {
            return Err(Diagnostic::new(
                handler.span,
                "a handler for an abortive operation cannot itself perform an abortive operation; handle it inside the handler",
            ));
        }
        self.require(signature.effects, span)?;
        let handler_type = handler_value.ty;
        let slot = self.fresh_local(span, handler_type)?;
        let label = self.abort_labels;
        self.abort_labels += 1;
        self.handlers.push(HandlerScope {
            operation: operation.to_owned(),
            parameter: parameter_ty,
            result: Type::Never,
            slot,
            handler_parameter: signature.parameters[0],
            handler_result: signature.result,
            effects: signature.effects,
            multishot: false,
            multi: false,
            region: false,
            points: 0,
            declared: declared.is_some(),
            abort: Some(label),
            token_effects: 0,
            in_frame: false,
        });
        let operation_effect = self.operation_effect(operation);
        let saved_effects = self.effects;
        self.effects |= operation_effect;
        let saved_required = self.required_effects.replace(0);
        let checked = self.block(body, Some(expected.unwrap_or(signature.result)));
        self.effects = saved_effects;
        self.required_effects
            .set(saved_required | (self.required_effects.get() & !operation_effect));
        self.handlers.pop();
        let checked = checked?;
        let ty = if checked.ty == Type::Never {
            signature.result
        } else {
            checked.ty
        };
        if signature.result != ty {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler of the abortive operation '{operation}' returns {}, but the handled body produces {}; both become the value of the 'handle'",
                    self.types.name(signature.result),
                    self.types.name(ty)
                ),
            ));
        }
        let scope = Expr {
            kind: ExprKind::AbortScope {
                label,
                body: checked,
                handler: Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty: handler_type,
                    span,
                    resource: None,
                }),
                operation: declared,
            },
            ty,
            span,
            resource: None,
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements: vec![Statement::Let(slot, handler_value)],
                tail: Some(Box::new(scope)),
                ty,
            }),
            ty,
            span,
            resource: None,
        })
    }
    /// Row bits of every declared abortive operation.
    pub(super) fn abortive_bits(&self) -> u16 {
        self.effect_operations
            .iter()
            .filter(|(_, operation)| operation.result == Type::Never)
            .map(|(name, _)| self.operation_effect(name))
            .fold(0, |bits, bit| bits | bit)
    }
    /// Row bits of every declared resumptive operation: a function value
    /// receives their capabilities as hidden parameters
    /// (docs/one-handler-model.md rule 4).
    pub(super) fn resumptive_bits(&self) -> u16 {
        self.effect_operations
            .iter()
            .filter(|(_, operation)| operation.result != Type::Never)
            .map(|(name, _)| self.operation_effect(name))
            .fold(0, |bits, bit| bits | bit)
    }
    /// Whether an abort of `bit` from the top of the handler stack may leave
    /// through every non-tail handler body above scope `index` (exclusive):
    /// each must be a one-shot lexical handler whose token row names it.
    pub(super) fn abort_crossing(&self, start: usize, bit: u16) -> Option<&HandlerScope> {
        self.handlers[start..]
            .iter()
            .find(|scope| scope.region && (bit == 0 || scope.token_effects & bit == 0))
    }
}
