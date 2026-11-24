//! Constructors, temporaries and staged code (quote, splice, emit).
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Whether checking `expr` needs an expected type to infer a generic
    /// constructor/record. Used only to preserve that inference for a later
    /// branch without forcing an unrelated branch into an earlier type.
    pub(super) fn needs_context(&self, expr: &ast::Expr) -> bool {
        if let Some((id, arguments)) = self.constructor_target(expr) {
            let (owner, _) = self.types.owner(id);
            if arguments.is_empty() && self.types.generic_count(owner) != 0 {
                return true;
            }
        }
        match &expr.kind {
            ast::ExprKind::Block(block) => block
                .tail
                .as_deref()
                .is_some_and(|tail| self.needs_context(tail)),
            ast::ExprKind::If {
                then, otherwise, ..
            } => {
                then.tail
                    .as_deref()
                    .is_some_and(|tail| self.needs_context(tail))
                    || otherwise
                        .as_deref()
                        .is_some_and(|otherwise| self.needs_context(otherwise))
            }
            ast::ExprKind::Match { arms, .. } => {
                arms.iter().any(|arm| self.needs_context(&arm.body))
            }
            ast::ExprKind::Record { ty, .. } => {
                if matches!(ty.kind, ast::ExprKind::Specialize { .. }) {
                    return false;
                }
                self.resolution.reference(ty.span).is_some_and(|id| {
                    self.types.is_record(id) && !self.types.record_fields(id).0.is_empty()
                })
            }
            _ => false,
        }
    }
    /// The binding at the root of a name/field/specialization expression, used
    /// to reject erased logical data before any runtime meaning is invented.
    pub(super) fn logical_data_root(&self, expr: &ast::Expr) -> Option<BindingId> {
        match &expr.kind {
            ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => {
                self.resolution.reference(expr.span)
            }
            ast::ExprKind::Specialize { callee, .. } => self.logical_data_root(callee),
            _ => None,
        }
    }
    pub(super) fn constructor_target<'e>(
        &self,
        expr: &'e ast::Expr,
    ) -> Option<(BindingId, &'e [ast::Type])> {
        let (base, arguments) = match &expr.kind {
            ast::ExprKind::Specialize { callee, arguments } => {
                (callee.as_ref(), arguments.as_slice())
            }
            _ => (expr, &[][..]),
        };
        let id = self.resolution.reference(base.span)?;
        (self.resolution.bindings[id].kind == BindingKind::Constructor
            && !self.logical.constructors.contains_key(&id))
        .then_some((id, arguments))
    }
    pub(super) fn construct(
        &mut self,
        callee: &ast::Expr,
        values: Option<&[ast::Expr]>,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let (id, arguments) = self.constructor_target(callee).unwrap();
        let (owner, tag) = self.types.owner(id);
        let mut expected_layout = None;
        if let Some(index) = expected.and_then(Type::layout) {
            if self.types.enums[index].definition != owner {
                return Err(Diagnostic::new(
                    span,
                    "constructor belongs to a different enum than the expected type",
                ));
            }
            expected_layout = Some(index);
        } else if arguments.is_empty()
            && let Some(Type::Union(union)) = expected
        {
            let matching = self.types.unions[union]
                .members
                .iter()
                .filter_map(|member| {
                    member
                        .layout()
                        .filter(|index| self.types.enums[*index].definition == owner)
                })
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {}
                [index] => expected_layout = Some(*index),
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this constructor fits several union alternatives; write explicit type arguments",
                    ));
                }
            }
        }
        let enum_id = if arguments.is_empty() {
            if let Some(index) = expected_layout {
                index
            } else {
                if self.types.generic_count(owner) != 0 {
                    return Err(Diagnostic::new(
                        span,
                        "generic constructor needs an expected enum type or explicit constructor::<type arguments>",
                    ));
                }
                self.types
                    .instantiate(owner, vec![], vec![], vec![], span)?
            }
        } else {
            let kinds = self.types.generic_kinds(owner);
            if arguments.len() != kinds.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "constructor expects {} type arguments, found {}",
                        kinds.len(),
                        arguments.len()
                    ),
                ));
            }
            let mut args = Vec::new();
            let mut consts = Vec::new();
            for (argument, is_const) in arguments.iter().zip(kinds) {
                if is_const {
                    consts.push(crate::length::eval_type(
                        self.resolution,
                        self.logical,
                        &self.consts,
                        argument,
                    )?);
                } else {
                    let ty = self.ty(argument)?;
                    args.push(self.types.full(ty, span)?);
                }
            }
            self.types.instantiate(owner, args, consts, vec![], span)?
        };
        let variant = self.types.enums[enum_id].variants[tag].clone();
        if variant.tuple != values.is_some() {
            return Err(Diagnostic::new(
                span,
                "tuple variants require a call; unit variants are values without parentheses",
            ));
        }
        let values = values.unwrap_or(&[]);
        if values.len() != variant.fields.len() {
            return Err(Diagnostic::new(span, "wrong enum payload arity"));
        }
        if self.types.enums[enum_id].name == "TaskExit"
            && variant
                .fields
                .iter()
                .any(|ty| crate::runtime_types::has_borrow(self.types, *ty))
        {
            return Err(Diagnostic::new(
                span,
                "TaskExit<T> with a borrowed payload is produced only by Task.join; construct the record first, or join the child task and match its result",
            ));
        }
        let mut fields = Vec::new();
        let mut diverges = false;
        for (value, ty) in values.iter().zip(variant.fields) {
            let value = self.expr_expected(value, Some(ty))?;
            diverges |= value.ty == Type::Never;
            fields.push(value);
        }
        // A constructor's principal type is its single variant.
        let ty = if diverges {
            Type::Never
        } else {
            crate::runtime_types::refine(&self.types.enums, enum_id, 1 << tag)
        };
        let value = Expr {
            kind: ExprKind::Construct {
                enum_id,
                tag,
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
    pub(super) fn temp(&mut self, ty: Type, span: Span) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
            ));
        }
        self.locals.push(Local {
            ty,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        });
        Ok(self.locals.len() - 1)
    }
    /// Check an explicitly typed lambda. Captures are discovered from resolved
    /// names; a noncapturing lambda is a copyable function pointer, while a
    /// lambda capturing affine owned storage is an owning once-consuming
    /// closure. Capturing a linear `@[1]`/`#[linear]` obligation produces a
    /// `linear once fn` value whose environment must be consumed by a call.
    pub(super) fn splice_placeholder(&mut self, signature: usize, span: Span) -> Result<usize> {
        let f = self.types.function_types[signature].clone();
        let locals = f
            .parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let body = Block {
            statements: vec![],
            tail: None,
            ty: Type::Unit,
        };
        let never = Expr {
            kind: ExprKind::Loop(body),
            ty: Type::Never,
            span,
            resource: None,
        };
        let (local_borrowed, local_copyable) = self.local_classes(&locals);
        let function = Function {
            name: "splice placeholder".into(),
            parameters: f.parameters.len(),
            closure: None,
            capture_refs: vec![],
            capture_writes: vec![],
            locals,
            result: f.result,
            body: Block {
                statements: vec![],
                tail: Some(Box::new(never)),
                ty: Type::Never,
            },
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: f.parameter_grades.clone(),
            result_grade: f.result_grade,
            parameter_lifetimes: f.borrows.parameters.clone(),
            result_lifetime: f.borrows.result.clone(),
            lifetime_bounds: f.borrows.bounds.clone(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: BTreeSet::new(),
            parameter_slots: None,
            local_borrowed,
            local_copyable,
            capability_parameters: vec![],
            shared_environment: false,
        };
        let signature = Signature {
            call_contract: None,
            binding: usize::MAX,
            name: function.name.clone(),
            parameters: f.parameters,
            result: f.result,
            effects: f.effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: f.parameter_grades,
            result_grade: f.result_grade,
            parameter_lifetimes: f.borrows.parameters,
            result_lifetime: f.borrows.result,
            lifetime_bounds: f.borrows.bounds,
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        self.functions.add_synthetic(signature, function)
    }

    pub(super) fn stage_emit_byte(
        buffer: usize,
        byte: Expr,
        statements: &mut Vec<Statement>,
        span: Span,
    ) {
        let buffer_value = Expr {
            kind: ExprKind::Local(buffer),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        let pushed = Expr {
            kind: ExprKind::Call(Target::Bytes(BytesOp::Push), vec![buffer_value, byte]),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        statements.push(Statement::Expr(Expr {
            kind: ExprKind::Assign(buffer, Box::new(pushed)),
            ty: Type::Unit,
            span,
            resource: None,
        }));
    }

    pub(super) fn stage_emit_word(
        buffer: usize,
        word: Expr,
        statements: &mut Vec<Statement>,
        span: Span,
    ) {
        for shift in (0..64).step_by(8) {
            let constant = |n| Expr {
                kind: ExprKind::Constant(n),
                ty: Type::I64,
                span,
                resource: None,
            };
            let shifted = Expr {
                kind: ExprKind::Binary(
                    Kind::Shr,
                    Box::new(word.clone()),
                    Box::new(constant(shift)),
                ),
                ty: Type::I64,
                span,
                resource: None,
            };
            let byte = Expr {
                kind: ExprKind::Binary(Kind::Amp, Box::new(shifted), Box::new(constant(255))),
                ty: Type::I64,
                span,
                resource: None,
            };
            Self::stage_emit_byte(buffer, byte, statements, span);
        }
    }

    pub(super) fn stage_emit_code(
        &mut self,
        buffer: usize,
        capture: &Expr,
        stub: usize,
        statements: &mut Vec<Statement>,
        span: Span,
    ) -> Result<()> {
        let constant = |n| Expr {
            kind: ExprKind::Constant(n),
            ty: Type::I64,
            span,
            resource: None,
        };
        Self::stage_emit_word(buffer, constant(stub as i64), statements, span);
        let ExprKind::Local(slot) = capture.kind else {
            return Err(Diagnostic::new(
                span,
                "a code splice must name a checked captured owner",
            ));
        };
        let Type::Enum(layout) = capture.ty else {
            unreachable!()
        };
        let field = Expr {
            kind: ExprKind::Project(
                Box::new(Expr {
                    kind: ExprKind::Peek(slot),
                    ty: capture.ty,
                    span,
                    resource: None,
                }),
                self.types.enums[layout].tag_words(),
            ),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        let reference_ty = Type::Ref(self.types.pointer(Type::Bytes));
        let reference = Expr {
            kind: ExprKind::BorrowPlace(Box::new(field)),
            ty: reference_ty,
            span,
            resource: None,
        };
        self.stage_emit_blob(buffer, reference, statements, span)
    }

    pub(super) fn stage_emit_blob(
        &mut self,
        buffer: usize,
        reference: Expr,
        statements: &mut Vec<Statement>,
        span: Span,
    ) -> Result<()> {
        let constant = |n| Expr {
            kind: ExprKind::Constant(n),
            ty: Type::I64,
            span,
            resource: None,
        };
        let reference_ty = reference.ty;
        let reference_slot = self.fresh_local(span, reference_ty)?;
        statements.push(Statement::Let(reference_slot, reference));
        let reference = || Expr {
            kind: ExprKind::Local(reference_slot),
            ty: reference_ty,
            span,
            resource: None,
        };
        let length = Expr {
            kind: ExprKind::Call(Target::Bytes(BytesOp::Len), vec![reference()]),
            ty: Type::I64,
            span,
            resource: None,
        };
        let length_slot = self.fresh_local(span, Type::I64)?;
        statements.push(Statement::Let(length_slot, length));
        let length = || Expr {
            kind: ExprKind::Local(length_slot),
            ty: Type::I64,
            span,
            resource: None,
        };
        Self::stage_emit_word(buffer, length(), statements, span);
        let index = self.fresh_local(span, Type::I64)?;
        self.locals[index].mutable = true;
        statements.push(Statement::Let(index, constant(0)));
        let index_value = || Expr {
            kind: ExprKind::Local(index),
            ty: Type::I64,
            span,
            resource: None,
        };
        let byte = Expr {
            kind: ExprKind::Call(
                Target::Bytes(BytesOp::Get),
                vec![reference(), index_value()],
            ),
            ty: Type::I64,
            span,
            resource: None,
        };
        let mut body = Vec::new();
        Self::stage_emit_byte(buffer, byte, &mut body, span);
        let next = Expr {
            kind: ExprKind::Binary(Kind::Plus, Box::new(index_value()), Box::new(constant(1))),
            ty: Type::I64,
            span,
            resource: None,
        };
        body.push(Statement::Expr(Expr {
            kind: ExprKind::Assign(index, Box::new(next)),
            ty: Type::Unit,
            span,
            resource: None,
        }));
        let condition = Expr {
            kind: ExprKind::Binary(Kind::Lt, Box::new(index_value()), Box::new(length())),
            ty: Type::Bool,
            span,
            resource: None,
        };
        statements.push(Statement::Expr(Expr {
            kind: ExprKind::While(
                Box::new(condition),
                Block {
                    statements: body,
                    tail: None,
                    ty: Type::Unit,
                },
            ),
            ty: Type::Unit,
            span,
            resource: None,
        }));
        Ok(())
    }

    pub(super) fn compile_code(
        &mut self,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if arguments.len() != 1 {
            return Err(Diagnostic::new(
                span,
                "Code.compile expects one owned code graph",
            ));
        }
        self.require(ALLOC, span)?;
        let code = self.expr(&arguments[0])?;
        let signature = self.types.code_signature(code.ty).ok_or_else(|| {
            Diagnostic::new(span, "Code.compile expects an owned Code<fn(...)> value")
        })?;
        // An ordinary Fn return cannot express an artifact-owner lifetime.
        // Admit owning data and serialized Code results, but do not publish
        // unowned callable addresses through an otherwise owned result.
        if self.contains_callable(self.types.function_types[signature].result) {
            return Err(Diagnostic::new(
                span,
                "a compiled callable cannot return a value that may carry an unowned callable outside its artifact owner",
            ));
        }
        let owner = self.types.compiled_code_type(Type::Fn(signature), span)?;
        let (ty, shape) = self.types.result_type(owner, Type::I64, span)?;
        let value = Expr {
            kind: ExprKind::Call(Target::StageCompile(shape), vec![code]),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(ty) => self.coerce(value, ty, span),
            None => Ok(value),
        }
    }

    pub(super) fn call_code(
        &mut self,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let Some(owner) = arguments.first() else {
            return Err(Diagnostic::new(
                span,
                "Code.call expects a borrowed compiled owner and its arguments",
            ));
        };
        let owner = self.expr(owner)?;
        let Type::Ref(pointer) = owner.ty else {
            return Err(Diagnostic::new(
                span,
                "Code.call expects &CompiledCode<fn(...)>",
            ));
        };
        let signature = self
            .types
            .compiled_code_signature(self.types.pointees[pointer])
            .ok_or_else(|| Diagnostic::new(span, "Code.call expects &CompiledCode<fn(...)>"))?;
        let owner_ty = owner.ty;
        let owner_slot = self.fresh_local(span, owner_ty)?;
        let mut statements = vec![Statement::Let(owner_slot, owner)];
        let owner = Expr {
            kind: ExprKind::Local(owner_slot),
            ty: owner_ty,
            span,
            resource: None,
        };
        let entry = Expr {
            kind: ExprKind::Call(Target::StageEntry(signature), vec![owner]),
            ty: Type::Fn(signature),
            span,
            resource: None,
        };
        let mut call = self.indirect_call_checked(entry, &arguments[1..], None, span)?;
        let ExprKind::CallIndirect { arguments, .. } = &mut call.kind else {
            unreachable!()
        };
        // Coerced arguments are evaluated before the pure entry load. The
        // owner's reference is used after all of them, so its loan cannot end
        // while an argument could move/drop the compiled artifact.
        for argument in arguments {
            let slot = self.fresh_local(argument.span, argument.ty)?;
            let value = Expr {
                kind: ExprKind::Local(slot),
                ty: argument.ty,
                span: argument.span,
                resource: None,
            };
            statements.push(Statement::Let(slot, std::mem::replace(argument, value)));
        }
        let value = Self::after(statements, call);
        match expected {
            Some(ty) => self.coerce(value, ty, span),
            None => Ok(value),
        }
    }

    pub(super) fn clone_code(
        &mut self,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if arguments.len() != 1 {
            return Err(Diagnostic::new(
                span,
                "Code.clone expects one shared code reference",
            ));
        }
        self.require(ALLOC | PANIC, span)?;
        let reference = self.expr(&arguments[0])?;
        let Type::Ref(pointer) = reference.ty else {
            return Err(Diagnostic::new(span, "Code.clone expects &Code<fn(...)>"));
        };
        let ty = self.types.pointees[pointer];
        if self.types.code_signature(ty).is_none() {
            return Err(Diagnostic::new(span, "Code.clone expects &Code<fn(...)>"));
        }
        let Type::Enum(enum_id) = ty else {
            unreachable!()
        };
        let reference_ty = reference.ty;
        let slot = self.fresh_local(span, reference_ty)?;
        let statements = vec![Statement::Let(slot, reference)];
        let reference = Expr {
            kind: ExprKind::Peek(slot),
            ty: reference_ty,
            span,
            resource: None,
        };
        let field = Expr {
            kind: ExprKind::Project(Box::new(reference), self.types.enums[enum_id].tag_words()),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        let borrowed = Expr {
            kind: ExprKind::BorrowPlace(Box::new(field)),
            ty: Type::Ref(self.types.pointer(Type::Bytes)),
            span,
            resource: None,
        };
        let bytes = Expr {
            kind: ExprKind::Call(Target::Bytes(BytesOp::Copy), vec![borrowed]),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        let code = Expr {
            kind: ExprKind::Construct {
                enum_id,
                tag: 0,
                fields: vec![bytes],
            },
            ty,
            span,
            resource: None,
        };
        let code = Self::after(statements, code);
        match expected {
            Some(expected) => self.coerce(code, expected, span),
            None => Ok(code),
        }
    }

    /// Check a quotation using the ordinary callable checker. The body is
    /// retained as a checked template function; constructing code serializes
    /// its identity rather than evaluating or returning a closure.
    pub(super) fn quote(
        &mut self,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let ast::ExprKind::Lambda(lambda) = &value.kind else {
            return Err(Diagnostic::new(
                span,
                "a quotation requires a callable body",
            ));
        };
        self.require(ALLOC | PANIC, span)?;
        let mut statements = Vec::new();
        let mut holes = BTreeMap::new();
        let mut splices = BTreeMap::new();
        let mut pending = vec![(value, 1usize)];
        while let Some((expression, stage)) = pending.pop() {
            if let Some((form, operand)) = expression.staging() {
                match form {
                    ast::StagingForm::Quote => {
                        pending.push((operand, stage + 1));
                        continue;
                    }
                    ast::StagingForm::Lift | ast::StagingForm::Splice if stage > 1 => {
                        pending.push((operand, stage - 1));
                        continue;
                    }
                    ast::StagingForm::Lift => {
                        let lifted = self.expr(operand)?;
                        if !is_live_scalar(lifted.ty)
                            && !matches!(lifted.ty, Type::Bytes | Type::String)
                            && !self.types.is_staging_type_parameter(lifted.ty)
                        {
                            return Err(Diagnostic::new(
                                expression.span,
                                "lifting owned values is not implemented yet",
                            ));
                        }
                        let slot = self.fresh_local(expression.span, lifted.ty)?;
                        holes.insert((expression.span.start, expression.span.end), slot);
                        statements.push(Statement::Let(slot, lifted));
                        continue;
                    }
                    ast::StagingForm::Splice => {
                        let code = self.expr(operand)?;
                        let signature = self.types.code_signature(code.ty).ok_or_else(|| {
                            Diagnostic::new(expression.span, "splice expects Code<fn(...)>")
                        })?;
                        let stub = self.splice_placeholder(signature, expression.span)?;
                        let slot = self.fresh_local(expression.span, code.ty)?;
                        let key = (expression.span.start, expression.span.end);
                        holes.insert(key, slot);
                        splices.insert(key, (stub, signature));
                        statements.push(Statement::Let(slot, code));
                        continue;
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expression.span,
                            "invalid quotation stage form",
                        ));
                    }
                }
            }
            let mut children = Vec::new();
            ast_children(expression, &mut |child| children.push(child));
            pending.extend(children.into_iter().rev().map(|child| (child, stage)));
        }
        let expected_callable = match expected {
            Some(ty) => Some(Type::Fn(self.types.code_signature(ty).ok_or_else(
                || {
                    Diagnostic::new(
                        span,
                        "a quotation produces Code<fn(...)>, not an ordinary callable",
                    )
                },
            )?)),
            None => None,
        };
        let expected_callable = match expected_callable {
            Some(Type::Fn(signature)) if !holes.is_empty() => {
                let f = self.types.function_types[signature].clone();
                Some(Type::Once(self.types.function_type_with(
                    f.parameters,
                    f.result,
                    f.effects,
                    f.parameter_grades,
                    f.result_grade,
                    true,
                    false,
                    f.borrows,
                )))
            }
            other => other,
        };
        let hole_slots = holes.clone();
        let saved_holes = std::mem::replace(&mut self.quote_holes, holes);
        let saved_splices = std::mem::replace(&mut self.quote_splices, splices.clone());
        let callable = self.lambda(lambda, span, expected_callable, LambdaContext::Quotation);
        self.quote_holes = saved_holes;
        self.quote_splices = saved_splices;
        let callable = callable?;
        let ExprKind::FnValue { function, captures } = &callable.kind else {
            return Err(Diagnostic::new(
                span,
                "a quoted template must be a closed callable",
            ));
        };
        self.functions.stage_templates.insert(*function);
        if captures.iter().any(|c| {
            !is_live_scalar(c.ty)
                && !matches!(c.ty, Type::Bytes | Type::String)
                && self.types.code_signature(c.ty).is_none()
                && !self.types.is_staging_type_parameter(c.ty)
        }) {
            return Err(Diagnostic::new(
                span,
                "a quoted capture must currently be a scalar",
            ));
        }
        let signature = match callable.ty {
            Type::Fn(signature) => signature,
            Type::Once(signature) => {
                let f = self.types.function_types[signature].clone();
                self.types.function_type_with(
                    f.parameters,
                    f.result,
                    f.effects,
                    f.parameter_grades,
                    f.result_grade,
                    false,
                    false,
                    f.borrows,
                )
            }
            _ => return Err(Diagnostic::new(span, "invalid quoted callable signature")),
        };
        let ty = self.types.code_type(Type::Fn(signature), span)?;
        let Type::Enum(enum_id) = ty else {
            unreachable!()
        };
        // A rigid lifted value has no serialization yet. Its hole still has
        // the rigid type throughout callable checking and the capture is moved
        // below. Only the concrete specialization can produce a real graph.
        let abstract_capture = captures
            .iter()
            .any(|c| self.types.is_staging_type_parameter(c.ty));
        let composed = !splices.is_empty()
            || captures
                .iter()
                .any(|c| matches!(c.ty, Type::Bytes | Type::String));
        let mut encoded = if abstract_capture {
            &b""[..]
        } else if captures.is_empty() {
            b"KUSHCD01"
        } else if composed {
            b"KUSHCD03"
        } else {
            b"KUSHCD02"
        }
        .to_vec();
        if !abstract_capture {
            encoded.extend_from_slice(&(*function as u64).to_le_bytes());
            if !captures.is_empty() {
                encoded.extend_from_slice(&(captures.len() as u64).to_le_bytes());
            }
        }
        let mut bytes = Expr {
            kind: ExprKind::BytesLiteral(encoded),
            ty: Type::Bytes,
            span,
            resource: None,
        };
        if abstract_capture {
            statements.extend(captures.iter().cloned().map(Statement::Expr));
        } else if !captures.is_empty() {
            let slot = self.fresh_local(span, Type::Bytes)?;
            self.locals[slot].mutable = true;
            statements.push(Statement::Let(slot, bytes));
            for capture in captures {
                if matches!(capture.ty, Type::Bytes | Type::String) {
                    let ExprKind::Local(capture_slot) = capture.kind else {
                        unreachable!()
                    };
                    let tag = Expr {
                        kind: ExprKind::Constant(2),
                        ty: Type::I64,
                        span,
                        resource: None,
                    };
                    Self::stage_emit_byte(slot, tag, &mut statements, span);
                    let reference = Expr {
                        kind: ExprKind::Borrow(capture_slot),
                        ty: Type::Ref(self.types.pointer(capture.ty)),
                        span,
                        resource: None,
                    };
                    self.stage_emit_blob(slot, reference, &mut statements, span)?;
                } else if self.types.code_signature(capture.ty).is_some() {
                    let ExprKind::Local(capture_slot) = capture.kind else {
                        unreachable!()
                    };
                    let key = hole_slots
                        .iter()
                        .find(|(_, value)| **value == capture_slot)
                        .map(|(key, _)| key)
                        .expect("captured code has a splice hole");
                    let stub = splices[key].0;
                    let tag = Expr {
                        kind: ExprKind::Constant(1),
                        ty: Type::I64,
                        span,
                        resource: None,
                    };
                    Self::stage_emit_byte(slot, tag, &mut statements, span);
                    self.stage_emit_code(slot, capture, stub, &mut statements, span)?;
                } else {
                    if composed {
                        let tag = Expr {
                            kind: ExprKind::Constant(0),
                            ty: Type::I64,
                            span,
                            resource: None,
                        };
                        Self::stage_emit_byte(slot, tag, &mut statements, span);
                    }
                    // Local scalar representations are word bits, not an
                    // arithmetic cast. Lift expressions have already run once.
                    let raw = if capture.ty == Type::Unit {
                        ExprKind::Constant(0)
                    } else {
                        capture.kind.clone()
                    };
                    let raw = Expr {
                        kind: raw,
                        ty: Type::I64,
                        span,
                        resource: None,
                    };
                    Self::stage_emit_word(slot, raw, &mut statements, span);
                }
            }
            bytes = Expr {
                kind: ExprKind::Local(slot),
                ty: Type::Bytes,
                span,
                resource: None,
            };
        }
        let code = Expr {
            kind: ExprKind::Construct {
                enum_id,
                tag: 0,
                fields: vec![bytes],
            },
            ty,
            span,
            resource: None,
        };
        Ok(Self::after(statements, code))
    }
    pub(super) fn copy_lifted_text(&mut self, slot: usize, span: Span) -> Expr {
        let ty = self.locals[slot].ty;
        let reference = Expr {
            kind: ExprKind::Borrow(slot),
            ty: Type::Ref(self.types.pointer(ty)),
            span,
            resource: None,
        };
        // Both text types use the buffer layout, so copying a checked String
        // this way preserves its UTF-8 invariant.
        Expr {
            kind: ExprKind::Call(Target::Bytes(BytesOp::Copy), vec![reference]),
            ty,
            span,
            resource: None,
        }
    }
}
