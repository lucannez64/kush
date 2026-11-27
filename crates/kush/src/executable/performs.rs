//! Resumption tokens, handled bodies, await marking and performs.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Intern a resumption callable type. One-shot resumption is
    /// `linear once fn(R) -> R`; multishot resumption is the copyable
    /// `fn(R) -> R`. The copyable form is only sound when the continuation
    /// owns no environment, which the checker enforces at the perform site.
    pub(super) fn resume_type(&mut self, result: Type, multishot: bool) -> Type {
        self.resume_type_with(result, multishot, 0)
    }
    /// A resumption token whose row names the abortive operations that may
    /// leave through it (E-ABORT-INTERACT).
    pub(super) fn resume_type_with(&mut self, result: Type, multishot: bool, effects: u16) -> Type {
        let id = self.types.function_type_with(
            vec![result],
            result,
            effects,
            vec![None],
            None,
            !multishot,
            !multishot,
            crate::runtime_types::BorrowSig::default(),
        );
        if multishot {
            Type::Fn(id)
        } else {
            Type::Once(id)
        }
    }
    /// Build the identity resumption value. The linear contract is enforced by
    /// the ordinary callable ownership rules; no hidden continuation or stack
    /// pointer exists, so a token that is transferred and called normally is
    /// still a one-shot operation result.
    /// The token type a handler receives: a `multi fn` token when the
    /// handler declares one, otherwise `resume_type_with`.
    pub(super) fn token_type(
        &mut self,
        result: Type,
        multishot: bool,
        multi: bool,
        effects: u16,
    ) -> Type {
        if multi {
            Type::Multi(self.types.multi_token_with(result, effects))
        } else {
            self.resume_type_with(result, multishot, effects)
        }
    }
    /// The identity `multi fn(R) -> R` token of a perform that continues in
    /// place. It takes (and ignores) an environment word; its environment
    /// is null, so nothing is pushed on the continuation stack.
    pub(super) fn multi_identity(
        &mut self,
        result: Type,
        effects: u16,
        span: Span,
    ) -> Result<Expr> {
        let id = self.types.multi_token_with(result, effects);
        let signature = self.types.function_types[id].clone();
        let locals = vec![Local {
            ty: result,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        }];
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::Local(0),
                ty: result,
                span,
                resource: None,
            })),
            ty: result,
        };
        let function = self.register_adapter(
            "effect resume",
            &signature,
            vec![],
            true,
            locals,
            body,
            span,
        )?;
        Ok(Expr {
            kind: ExprKind::FnValue {
                function,
                captures: vec![],
            },
            ty: Type::Multi(id),
            span,
            resource: None,
        })
    }
    pub(super) fn resume_value(
        &mut self,
        result: Type,
        multishot: bool,
        span: Span,
    ) -> Result<Expr> {
        self.resume_value_with(result, multishot, 0, span)
    }
    pub(super) fn resume_value_with(
        &mut self,
        result: Type,
        multishot: bool,
        effects: u16,
        span: Span,
    ) -> Result<Expr> {
        let ty = self.resume_type_with(result, multishot, effects);
        let (id, env_parameter) = match ty {
            Type::Once(id) => (id, true),
            Type::Fn(id) => (id, false),
            _ => unreachable!("resume type is callable"),
        };
        let signature = self.types.function_types[id].clone();
        let locals = vec![Local {
            ty: result,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        }];
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::Local(0),
                ty: result,
                span,
                resource: None,
            })),
            ty: result,
        };
        let function = self.register_adapter(
            "effect resume",
            &signature,
            vec![],
            env_parameter,
            locals,
            body,
            span,
        )?;
        Ok(Expr {
            kind: ExprKind::FnValue {
                function,
                captures: vec![],
            },
            ty,
            span,
            resource: None,
        })
    }
    /// Check the body of a lexical handler.
    ///
    /// Without a suspendable site every perform resolves to an identity-token
    /// handler call (`perform_effect`). With one, performs became `Suspend`
    /// points; the body is put in A-normal form so each point is a statement
    /// value, and wrapped in a `Suspendable` node that `crate::suspend`
    /// lowers after ownership and grades have checked it as written.
    pub(super) fn checked_effect_body(
        &mut self,
        body: &ast::Block,
        result_ty: Type,
        expected: Option<Type>,
        span: Span,
        site: Option<SuspendableSite>,
    ) -> Result<Block> {
        let Some(site) = site else {
            return self.block(body, expected);
        };
        if site.lexical && self.linear_type(result_ty) {
            return Err(Diagnostic::new(
                span,
                "non-tail resumption of a linear operation result is not supported; return an owning value through the resumption or use a tail-resuming handler",
            ));
        }
        let mut block = if site.lexical {
            let block = self.block(body, Some(result_ty))?;
            self.expect(block.ty, result_ty, span)?;
            block
        } else {
            self.block(body, expected)?
        };
        if let Some(operation) = site.operation {
            let bit = self.operation_effect(&site.name);
            let before = self.handlers.last().map_or(0, |scope| scope.points);
            self.mark_awaits_in_block(&mut block, operation, bit, &site.name, site.multishot)?;
            let awaits = self.handlers.last().map_or(0, |scope| scope.points) > before;
            if awaits && site.handler_once {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "a capturing ('once') handler for '{}' is consumed by its first perform, so it cannot resume performs in called functions, where a second perform would have no handler; use a noncapturing 'fn' handler",
                        site.name
                    ),
                ));
            }
        }
        if let Some(slot) = site.capability_slot {
            self.mark_capability_awaits_in_block(&mut block, slot)?;
            if let Some((operation, arrow, effects)) = self.capability_framed.get(&slot).copied() {
                for statement in &mut block.statements {
                    if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                        self.replace_framed_arguments(value, slot, operation, arrow, effects)?;
                    }
                }
                if let Some(tail) = block.tail.as_deref_mut() {
                    self.replace_framed_arguments(tail, slot, operation, arrow, effects)?;
                }
            }
        }
        if self.handlers.last().is_none_or(|scope| scope.points == 0) {
            if site.operation.is_none() {
                return Ok(block);
            }
            // No suspension point, but the lowering still rejects ways the
            // body could perform the operation that cannot be resumed (task
            // scopes, trait objects, callbacks), which would otherwise run
            // with the identity token under this non-tail handler.
            let ty = block.ty;
            let token = self.token_type(result_ty, site.multishot, site.multi, site.token_effects);
            return Ok(Block {
                statements: vec![],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Suspendable(Box::new(Suspendable {
                        handler_function: site.handler_function,
                        operation: site.operation,
                        result: ty,
                        token,
                        multishot: site.multishot,
                        handler_writes: site.handler_writes.clone(),
                        handler_refs: site.handler_refs.clone(),
                        effects: site.effects,
                        body: block,
                        span,
                    })),
                    ty,
                    span,
                    resource: None,
                })),
                ty,
            });
        }
        // A resumption token runs the rest of the body, whose effects and
        // dynamic handlers belong to this `handle`; it must not outlive the
        // handler activation. The handler can only hand it on through its
        // result, its payload, or a local it writes through a capture.
        let escape = if self.contains_callable(result_ty) {
            Some(
                "the operation result type can hold a function value, so the handler could return its resumption token",
            )
        } else if self.contains_callable(site.handler_parameter) {
            Some(
                "the handler's payload type can hold a function value, so the handler could store its resumption token",
            )
        } else if site
            .handler_writes
            .iter()
            .any(|slot| self.contains_callable(self.locals[*slot].ty))
            || site
                .handler_captures
                .iter()
                .any(|ty| self.mutable_callable_storage(*ty))
        {
            Some(
                "the handler writes a captured local, or captures mutable access to storage, that can hold a function value, so it could store its resumption token",
            )
        } else {
            None
        };
        if let Some(reason) = escape {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{reason} and call it after the 'handle' ends, running the rest of the body outside it; use a tail-resumptive handler or a result type without function values"
                ),
            ));
        }
        if !site.lexical {
            if self.linear_type(result_ty) {
                return Err(Diagnostic::new(
                    span,
                    "non-tail resumption of a linear operation result is not supported; return an owning value through the resumption or use a tail-resuming handler",
                ));
            }
            self.expect(block.ty, result_ty, span).map_err(|_| {
                Diagnostic::new(
                    span,
                    format!(
                        "this handled body calls functions that perform '{}', so under a handler with code after 'resume' it must produce the operation result type {}, which the handler's resumption returns",
                        site.name,
                        self.types.name(result_ty)
                    ),
                )
            })?;
        }
        self.anf_block(&mut block)?;
        // FND-ROWS-INFER: whether a continuation allocates is only known when
        // the suspension is lowered, after the row is settled, so an inferred
        // row takes `alloc` for every suspension point.
        if self.inferring_row {
            self.require(ALLOC, span)?;
        }
        let token = self.token_type(result_ty, site.multishot, site.multi, site.token_effects);
        let suspendable = Expr {
            kind: ExprKind::Suspendable(Box::new(Suspendable {
                handler_function: site.handler_function,
                operation: site.operation,
                result: result_ty,
                token,
                multishot: site.multishot,
                handler_writes: site.handler_writes.clone(),
                handler_refs: site.handler_refs.clone(),
                effects: site.effects,
                body: block,
                span,
            })),
            ty: result_ty,
            span,
            resource: None,
        };
        let value = match expected {
            Some(expected) => self.coerce(suspendable, expected, span)?,
            None => suspendable,
        };
        let ty = value.ty;
        Ok(Block {
            statements: vec![],
            tail: Some(Box::new(value)),
            ty,
        })
    }
    /// Classify locals for the suspension lowering: whether each holds a
    /// borrow, and whether each is copyable.
    pub(super) fn local_classes(&self, locals: &[Local]) -> (Vec<bool>, Vec<bool>) {
        let borrowed = locals
            .iter()
            .map(|local| {
                let ty = local.ty;
                ty.is_view()
                    || ty.is_ref()
                    || ty.is_text()
                    || crate::runtime_types::has_borrow(self.types, ty)
                    || crate::runtime_types::contains_task(self.types, ty)
            })
            .collect();
        let copyable = locals
            .iter()
            .map(|local| !local.linear && !self.owned_type(local.ty) && !self.linear_type(local.ty))
            .collect();
        (borrowed, copyable)
    }
    /// Turn every direct call in a suspendable body that passes the
    /// capability held in `slot` to a `cap` parameter into an await point
    /// keyed by that parameter (EFF-CAP-RESUME-CALLS). Calls inside nested
    /// handlers cannot be resumed by this handle.
    pub(super) fn mark_capability_awaits_in_block(
        &mut self,
        block: &mut Block,
        slot: usize,
    ) -> Result<()> {
        for statement in &mut block.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                self.mark_capability_awaits(value, slot, false)?;
            }
        }
        if let Some(tail) = block.tail.as_deref_mut() {
            self.mark_capability_awaits(tail, slot, false)?;
        }
        Ok(())
    }
    pub(super) fn mark_capability_awaits_in_call(
        &mut self,
        expr: &mut Expr,
        slot: usize,
        nested: bool,
    ) -> Result<()> {
        let ExprKind::Suspend { call, .. } = &mut expr.kind else {
            unreachable!("called for suspension points")
        };
        let mut result = Ok(());
        call.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = self.mark_capability_awaits(child, slot, nested);
            }
        });
        result
    }
    /// EFF-CAP-RESUME-CAPTURING: replace the placeholders of a framed
    /// capability passed to `cap` parameters (the local at the parameter's
    /// type) by the trampoline.
    pub(super) fn replace_framed_arguments(
        &mut self,
        expr: &mut Expr,
        slot: usize,
        operation: usize,
        arrow: usize,
        effects: u16,
    ) -> Result<()> {
        if matches!(expr.kind, ExprKind::Local(local) if local == slot)
            && expr.ty != self.locals[slot].ty
        {
            let (function, ty) = self.capability_thunk(operation, arrow, effects, expr.span)?;
            let thunk = Expr {
                kind: ExprKind::FnValue {
                    function,
                    captures: vec![],
                },
                ty,
                span: expr.span,
                resource: None,
            };
            *expr = self.coerce(thunk, expr.ty, expr.span)?;
            return Ok(());
        }
        let mut result = Ok(());
        expr.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = self.replace_framed_arguments(child, slot, operation, arrow, effects);
            }
        });
        result
    }
    pub(super) fn mark_capability_awaits(
        &mut self,
        expr: &mut Expr,
        slot: usize,
        nested: bool,
    ) -> Result<()> {
        fn passes(argument: &Expr, slot: usize) -> bool {
            match &argument.kind {
                ExprKind::Local(local) | ExprKind::Move(local) | ExprKind::Peek(local) => {
                    *local == slot
                }
                ExprKind::Coerce { value, .. } => passes(value, slot),
                _ => false,
            }
        }
        let nested = match &expr.kind {
            ExprKind::HandlerPush { .. }
            | ExprKind::Suspendable(_)
            | ExprKind::AbortScope { .. } => true,
            ExprKind::Suspend {
                call,
                callee: Some(_),
                ..
            } => {
                let found = matches!(
                    &call.kind,
                    ExprKind::Call(_, arguments) if arguments.iter().any(|argument| passes(argument, slot))
                );
                if found {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a call that may perform the handled operation and also receives its capability is not supported under a handler with code after 'resume'",
                    ));
                }
                return self.mark_capability_awaits_in_call(expr, slot, nested);
            }
            // A point's own call is the handler or awaited call; calls in its
            // operands may still pass the capability.
            ExprKind::Suspend { .. } => {
                return self.mark_capability_awaits_in_call(expr, slot, nested);
            }
            _ => nested,
        };
        let mut result = Ok(());
        expr.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = self.mark_capability_awaits(child, slot, nested);
            }
        });
        result?;
        let ExprKind::Call(Target::Function(callee), arguments) = &expr.kind else {
            return Ok(());
        };
        let Some(index) = arguments.iter().position(|argument| passes(argument, slot)) else {
            return Ok(());
        };
        if arguments
            .iter()
            .filter(|argument| passes(argument, slot))
            .count()
            > 1
        {
            return Err(Diagnostic::new(
                expr.span,
                "a capability of a handler with code after 'resume' cannot be passed to two parameters of one call",
            ));
        }
        let callee = *callee;
        if nested {
            return Err(Diagnostic::new(
                expr.span,
                "a call given a capability inside a nested handler cannot be resumed by its handler with code after 'resume'; move the call out of the nested 'handle'",
            ));
        }
        let scope = self.handlers.last_mut().expect("a handle scope is active");
        scope.points += 1;
        let point = scope.points;
        let (ty, span) = (expr.ty, expr.span);
        let call = std::mem::replace(
            expr,
            Expr {
                kind: ExprKind::Constant(0),
                ty,
                span,
                resource: None,
            },
        );
        expr.kind = ExprKind::Suspend {
            point,
            call: Box::new(call),
            callee: Some(callee),
            capability: Some(index),
        };
        Ok(())
    }
    /// Turn every direct call in a suspendable body that may perform the
    /// handled declared operation into an await point. Calls under a nested
    /// handler for the same operation belong to that handler.
    pub(super) fn mark_awaits_in_block(
        &mut self,
        block: &mut Block,
        operation: usize,
        bit: u16,
        name: &str,
        multishot: bool,
    ) -> Result<()> {
        for statement in &mut block.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                self.mark_awaits(value, operation, bit, name, false, multishot)?;
            }
        }
        if let Some(tail) = block.tail.as_deref_mut() {
            self.mark_awaits(tail, operation, bit, name, false, multishot)?;
        }
        Ok(())
    }
    pub(super) fn mark_awaits(
        &mut self,
        expr: &mut Expr,
        operation: usize,
        bit: u16,
        name: &str,
        nested: bool,
        multishot: bool,
    ) -> Result<()> {
        let nested = match &expr.kind {
            ExprKind::HandlerPush {
                operation: inner, ..
            } if *inner == operation => return Ok(()),
            ExprKind::HandlerPush { .. }
            | ExprKind::Suspendable(_)
            | ExprKind::AbortScope { .. } => true,
            _ => nested,
        };
        let mut result = Ok(());
        expr.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = self.mark_awaits(child, operation, bit, name, nested, multishot);
            }
        });
        result?;
        let callee = match &expr.kind {
            ExprKind::TaskSpawn { body, .. }
                if multishot
                    && Self::function_parts(body.ty).is_some_and(|(id, _)| {
                        self.types.function_types[id].effects & bit != 0
                    }) =>
            {
                return Err(Diagnostic::new(
                    expr.span,
                    format!(
                        "a task spawned under a multishot handler for '{name}' cannot perform it: the handler is not visible to other tasks"
                    ),
                ));
            }
            ExprKind::Call(Target::Function(function), _) => {
                (self.functions.signatures[*function].effects & bit != 0).then_some(*function)
            }
            ExprKind::CallIndirect { callee, .. }
                if Self::function_parts(callee.ty)
                    .is_some_and(|(id, _)| self.types.function_types[id].effects & bit != 0) =>
            {
                return Err(Diagnostic::new(
                    expr.span,
                    format!(
                        "calling a function value that may perform '{name}' is not supported in the body of a handler with code after 'resume': the call cannot be resumed. Call a named function instead"
                    ),
                ));
            }
            _ => None,
        };
        let Some(callee) = callee else {
            return Ok(());
        };
        if nested {
            return Err(Diagnostic::new(
                expr.span,
                format!(
                    "a call that may perform '{name}' inside a nested handler for another operation cannot be resumed by the outer handler; move the call out of the nested 'handle'"
                ),
            ));
        }
        if multishot {
            return Err(Diagnostic::new(
                expr.span,
                format!(
                    "multishot resumption of '{name}' through a called function is not supported; perform '{name}' directly in the handled body"
                ),
            ));
        }
        let scope = self.handlers.last_mut().expect("a handle scope is active");
        scope.points += 1;
        let point = scope.points;
        let span = expr.span;
        let ty = expr.ty;
        let call = std::mem::replace(
            expr,
            Expr {
                kind: ExprKind::Constant(0),
                ty,
                span,
                resource: None,
            },
        );
        expr.kind = ExprKind::Suspend {
            point,
            call: Box::new(call),
            callee: Some(callee),
            capability: None,
        };
        Ok(())
    }
    /// Check a direct `perform` against the innermost lexical handler.
    /// `perform op(x)` through a capability: an indirect call of exactly the
    /// bound handler with the identity token. No dynamic lookup, so neither
    /// the operation's row bit nor `panic` for a missing handler is required;
    /// the handler's own row is.
    pub(super) fn capability_perform(
        &mut self,
        slot: usize,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if let Some(index) = self.handlers.iter().rposition(|scope| scope.slot == slot) {
            let operation = self.handlers[index].operation.clone();
            // A reusable handler was moved into its dynamic frame, which
            // serves every perform from a copy of its environment; perform
            // through the frame, as a perform by name does. A nested handle
            // for the same operation would intercept that perform.
            if self.handlers[index].in_frame {
                if let Some(inner) = self.handlers[index + 1..]
                    .iter()
                    .find(|inner| inner.operation == operation)
                {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "this capability's capturing handler lives in its dynamic frame, which the nested 'handle {}' hides; perform it outside the nested handle",
                            inner.operation
                        ),
                    ));
                }
                return self.dynamic_perform(&operation, value, expected, span);
            }
            let operation_effect = self.operation_effect(&operation);
            return self.lexical_perform(
                index,
                &operation,
                operation_effect,
                value,
                expected,
                span,
            );
        }
        let handler_ty = self.locals[slot].ty;
        let Type::Fn(arrow) = handler_ty else {
            return Err(Diagnostic::new(
                span,
                "internal error: a capability is not a handler function",
            ));
        };
        let arrow = self.types.function_types[arrow].clone();
        self.require(arrow.effects, span)?;
        let payload = self.expr_expected(value, Some(arrow.parameters[0]))?;
        let payload = self.coerce_argument(payload, arrow.parameters[0], span)?;
        let resume = if let Type::Multi(token) = arrow.parameters[1] {
            let effects = self.types.function_types[token].effects;
            self.multi_identity(arrow.result, effects, span)?
        } else {
            self.resume_value(arrow.result, false, span)?
        };
        let call = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty: handler_ty,
                    span,
                    resource: None,
                }),
                arguments: vec![payload, resume],
            },
            ty: arrow.result,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(call, expected, span),
            None => Ok(call),
        }
    }
    /// A perform served by the lexical handler scope `index` of this function.
    pub(super) fn lexical_perform(
        &mut self,
        index: usize,
        operation: &str,
        operation_effect: u16,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // A scope that is not on the dynamic stack never discharged the
        // operation's bit, so a lexical perform through it does not need it.
        let operation_effect = if self.handlers[index].declared {
            operation_effect
        } else {
            0
        };
        let scope = &self.handlers[index];
        let (parameter, result, slot, handler_parameter, handler_result, effects, multishot) = (
            scope.parameter,
            scope.result,
            scope.slot,
            scope.handler_parameter,
            scope.handler_result,
            scope.effects,
            scope.multishot,
        );
        let region = scope.region;
        let multi = scope.multi;
        let token_effects = scope.token_effects;
        let handler_ty = self.locals[slot].ty;
        if let Some(label) = scope.abort {
            return self.abort_exit(index, label, operation_effect, value, span);
        }
        if region
            && let Some(inner) = self.handlers[index + 1..]
                .iter()
                .find(|inner| inner.region || inner.declared)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a non-tail 'perform {operation}' inside the body of a nested 'handle {}' is not supported: resuming it would have to reinstate the inner handler; perform it outside the nested handle or make the outer handler tail-resumptive",
                    inner.operation
                ),
            ));
        }
        // A suspension inside an abortive scope would move the scope's exits
        // into a continuation function they cannot leave.
        if region
            && let Some(inner) = self.handlers[index + 1..]
                .iter()
                .find(|inner| inner.abort.is_some())
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a non-tail 'perform {operation}' inside the body of the abortive 'handle {}' is not supported; perform it outside that handle or make the handler for '{operation}' tail-resumptive",
                    inner.operation
                ),
            ));
        }
        self.require(effects | operation_effect, span)?;
        let payload = self.expr_expected(value, Some(parameter))?;
        let payload = self.coerce_argument(payload, handler_parameter, span)?;
        self.apply_handler_writes(slot);
        if region {
            self.handlers[index].points += 1;
            let point = self.handlers[index].points;
            let token = self.token_type(result, multishot, multi, token_effects);
            let call = Expr {
                kind: ExprKind::CallIndirect {
                    callee: Box::new(Expr {
                        kind: ExprKind::Local(slot),
                        ty: handler_ty,
                        span,
                        resource: None,
                    }),
                    arguments: vec![
                        payload,
                        Expr {
                            kind: ExprKind::Erased(token),
                            ty: token,
                            span,
                            resource: None,
                        },
                    ],
                },
                ty: handler_result,
                span,
                resource: None,
            };
            let call = self.coerce(call, result, span)?;
            let suspend = Expr {
                kind: ExprKind::Suspend {
                    point,
                    call: Box::new(call),
                    callee: None,
                    capability: None,
                },
                ty: result,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(suspend, expected, span),
                None => Ok(suspend),
            };
        }
        let resume = if multi {
            self.multi_identity(result, token_effects, span)?
        } else {
            self.resume_value_with(result, multishot, token_effects, span)?
        };
        let call = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty: handler_ty,
                    span,
                    resource: None,
                }),
                arguments: vec![payload, resume],
            },
            ty: handler_result,
            span,
            resource: None,
        };
        let call = self.coerce(call, result, span)?;
        match expected {
            Some(expected) => self.coerce(call, expected, span),
            None => Ok(call),
        }
    }
    /// An abortive `perform` served by the enclosing abortive scope `index`
    /// of this function: leave it with the payload.
    pub(super) fn abort_exit(
        &mut self,
        index: usize,
        label: usize,
        operation_effect: u16,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Expr> {
        let (operation, parameter, handler_parameter) = {
            let scope = &self.handlers[index];
            (
                scope.operation.clone(),
                scope.parameter,
                scope.handler_parameter,
            )
        };
        let bit = if self.handlers[index].declared {
            operation_effect
        } else {
            0
        };
        if let Some(inner) = self.abort_crossing(index + 1, bit) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the abortive 'perform {operation}' cannot leave the body of 'handle {}', whose handler has code after 'resume'; perform it outside that handle, or name '{operation}' in the row of its one-shot resumption token",
                    inner.operation
                ),
            ));
        }
        self.require(operation_effect, span)?;
        let payload = self.expr_expected(value, Some(parameter))?;
        let payload = self.coerce_argument(payload, handler_parameter, span)?;
        let declared = if self.handlers[index].declared {
            self.effect_operations
                .get(&operation)
                .map(|declared| declared.id)
        } else {
            None
        };
        Ok(Expr {
            kind: ExprKind::AbortExit {
                label,
                value: Box::new(payload),
                cleanup: Vec::new(),
                operation: declared,
                capability: None,
            },
            ty: Type::Never,
            span,
            resource: None,
        })
    }
    /// A dynamic abortive perform (E-ABORT-PROPAGATE): it leaves this
    /// function like `return`, and the innermost dynamic `handle F` receives
    /// the payload. A missing handler aborts the program, hence `panic`.
    pub(super) fn abort_perform(
        &mut self,
        operation: &str,
        declared: EffectOperation,
        operation_effect: u16,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Expr> {
        if let Some(inner) = self.abort_crossing(0, operation_effect) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the abortive 'perform {operation}' cannot leave the body of 'handle {}', whose handler has code after 'resume'; perform it outside that handle, or name '{operation}' in the row of its one-shot resumption token",
                    inner.operation
                ),
            ));
        }
        self.require(PANIC | operation_effect | declared.latent, span)?;
        let payload = self.expr_expected(value, Some(declared.parameter))?;
        let payload = self.coerce_argument(payload, declared.parameter, span)?;
        Ok(Expr {
            kind: ExprKind::AbortPerform {
                operation: declared.id,
                value: Box::new(payload),
                capability: None,
            },
            ty: Type::Never,
            span,
            resource: None,
        })
    }
    pub(super) fn perform_effect(
        &mut self,
        operation: &str,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if let Some(id) = self.resolution.reference(span)
            && let Some(&slot) = self.slots.get(&id)
            && self.capability_slots.contains(&slot)
        {
            return self.capability_perform(slot, value, expected, span);
        }
        let operation_effect = self.operation_effect(operation);
        if let Some(index) = self
            .handlers
            .iter()
            .rposition(|scope| scope.operation == operation)
            && !self.handlers[index].in_frame
        {
            return self.lexical_perform(index, operation, operation_effect, value, expected, span);
        }
        self.dynamic_perform(operation, value, expected, span)
    }
    /// A perform of `operation` served by the innermost handler on the
    /// dynamic stack.
    pub(super) fn dynamic_perform(
        &mut self,
        operation: &str,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let operation_effect = self.operation_effect(operation);
        let Some(declared) = self.effect_operations.get(operation).copied() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "perform '{operation}' has no lexically enclosing handler and no declared effect operation; write 'effect {operation}: P -> R;' to enable a dynamically scoped handler"
                ),
            ));
        };
        if declared.result == Type::Never {
            return self.abort_perform(operation, declared, operation_effect, value, span);
        }
        // No handler may be active at run time, which aborts the program, so
        // a dynamically resolved operation can always panic. A declared
        // operation is a concrete row effect too: the enclosing function must
        // list it (a lexical handle removes it for its body).
        self.require(PANIC | operation_effect | declared.latent, span)?;
        let payload = self.expr_expected(value, Some(declared.parameter))?;
        let payload = self.coerce_argument(payload, declared.parameter, span)?;
        let resume = self.resume_value(declared.result, false, span)?;
        let handler = self.types.function_type_with(
            vec![declared.parameter, resume.ty],
            declared.result,
            0,
            vec![None, None],
            None,
            false,
            false,
            crate::runtime_types::BorrowSig::default(),
        );
        let call = Expr {
            kind: ExprKind::DynamicPerform {
                operation: declared.id,
                payload: Box::new(payload),
                resume: Box::new(resume),
                handler,
                cell: None,
            },
            ty: declared.result,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(call, expected, span),
            None => Ok(call),
        }
    }
}
