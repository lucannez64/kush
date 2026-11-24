//! Blocks, statements, destructuring and result obligations.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    pub(super) fn block(&mut self, block: &ast::Block, expected: Option<Type>) -> Result<Block> {
        // A loop body proves its loop's invariant at its end, before the
        // facts it learnt are dropped.
        let invariant = self.body_invariant.take();
        self.nested(block.span, |c| {
            let mark = c.facts.mark();
            let stamp = c.facts.version_stamp();
            let kernel_mark = c.kernel_locals.len();
            let result = c.statements(
                &block.statements,
                block.tail.as_deref(),
                block.span,
                expected,
            );
            if let (Some(invariant), Ok(checked)) = (&invariant, &result)
                && checked.ty != Type::Never
            {
                c.prove_condition(invariant, "the loop invariant at the end of the body")?;
            }
            let preserved = match &result {
                Ok(checked) if checked.ty != Type::Never => c.facts.preserved_since(&stamp),
                _ => Vec::new(),
            };
            c.facts.reset(mark);
            c.facts.add(preserved);
            c.truncate_kernel(kernel_mark);
            result
        })
    }
    /// Elaborate the restricted borrow-pair statement
    ///
    /// ```text
    /// let (left, right) = Slice.split_at_mut(view, mid);
    /// ```
    ///
    /// The pair is not a storable value. It lowers to one checked midpoint
    /// local plus two ordinary slice views whose ranges are exactly
    /// `[0, mid)` and `[mid, len)`. Ownership checking marks the pair as a
    /// checked split rather than granting a general sibling exemption.
    pub(super) fn split_binding(
        &mut self,
        mutable: bool,
        pattern: &ast::Pattern,
        annotation: Option<&ast::Type>,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Option<Vec<Statement>>> {
        let ast::PatternKind::Tuple(parts) = &pattern.kind else {
            return Ok(None);
        };
        let ast::ExprKind::Call { callee, arguments } = &value.kind else {
            return Ok(None);
        };
        let Some(id) = self.resolution.reference(callee.span) else {
            return Ok(None);
        };
        let binding = &self.resolution.bindings[id];
        if binding.kind != BindingKind::Builtin || binding.name != "Slice.split_at_mut" {
            return Ok(None);
        }
        if mutable {
            return Err(Diagnostic::new(
                pattern.span,
                "split borrow bindings are move-only views and cannot be declared with 'let mut'",
            ));
        }
        if annotation.is_some() {
            return Err(Diagnostic::new(
                pattern.span,
                "a split borrow pair takes its view types from the receiver; omit the binding annotation",
            ));
        }
        if arguments.len() != 2 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Slice.split_at_mut expects 2 arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        let [left_name, right_name] = parts.as_slice() else {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut must destructure into exactly two names: let (left, right) = ...",
            ));
        };
        let (ast::PatternKind::Name(left_path), ast::PatternKind::Name(right_path)) =
            (&left_name.kind, &right_name.kind)
        else {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut binds exactly two simple local names; wildcards, fields, and nested patterns are not supported",
            ));
        };
        if left_path.len() != 1 || right_path.len() != 1 {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut binds exactly two simple local names",
            ));
        }
        if left_path == right_path {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut requires two distinct binding names",
            ));
        }

        // Evaluate the receiver exactly once. A named mutable view is used
        // directly; an explicit `&mut owner[..]` or `&mut parent[..]` becomes
        // a hidden parent capability so the midpoint is always split from one
        // stable checked view.
        let (parent_slot, parent_statement) = if matches!(arguments[0].kind, ast::ExprKind::Name(_))
        {
            let slot = self.slot(arguments[0].span)?;
            match self.locals[slot].ty {
                Type::SliceMut(_) => (slot, None),
                other => {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!(
                            "Slice.split_at_mut requires an exclusive '&mut [T]' view or '&mut owner[..]'; found {}",
                            self.types.name(other)
                        ),
                    )
                    .with_note(
                        self.locals[slot].span,
                        "bind a mutable slice view first, or pass &mut owner[..]",
                    ));
                }
            }
        } else if matches!(
            &arguments[0].kind,
            ast::ExprKind::Unary {
                op: Kind::Amp,
                mutable: true,
                operand,
            } if matches!(operand.kind, ast::ExprKind::Slice { .. })
        ) {
            let checked = self.expr(&arguments[0])?;
            let Type::SliceMut(_) = checked.ty else {
                return Err(Diagnostic::new(
                    arguments[0].span,
                    "Slice.split_at_mut requires an exclusive '&mut [T]' receiver",
                ));
            };
            let slot = self.fresh_local(arguments[0].span, checked.ty)?;
            (slot, Some(Statement::Let(slot, checked)))
        } else {
            return Err(Diagnostic::new(
                arguments[0].span,
                "Slice.split_at_mut receiver must be a mutable slice-view local or an explicit '&mut owner[..]' / '&mut parent[..]' reborrow",
            ));
        };
        let Type::SliceMut(pointer) = self.locals[parent_slot].ty else {
            unreachable!("split parent was checked as an exclusive slice")
        };
        let element = self.types.pointees[pointer];
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot split a slice view over owning or linear elements ({}); element reads would move owners",
                    self.types.name(element)
                ),
            ));
        }
        let midpoint = self.expr_expected(&arguments[1], Some(Type::I64))?;
        self.expect(midpoint.ty, Type::I64, midpoint.span)?;
        if midpoint.ty == Type::Never {
            return Err(Diagnostic::new(
                midpoint.span,
                "the midpoint of Slice.split_at_mut must produce an i64 value",
            ));
        }
        self.require(PANIC, span)?;
        let mid_slot = self.fresh_local(arguments[1].span, Type::I64)?;
        let group = self.next_split;
        self.next_split += 1;
        let view_ty = Type::SliceMut(pointer);
        let left_slot = self.bind(left_name.span, view_ty, false)?;
        let right_slot = self.bind(right_name.span, view_ty, false)?;
        let base = |span: Span| Expr {
            kind: ExprKind::Local(parent_slot),
            ty: view_ty,
            span,
            resource: None,
        };
        let mid = |span: Span| Expr {
            kind: ExprKind::Local(mid_slot),
            ty: Type::I64,
            span,
            resource: None,
        };
        let mut left = self.slice_from_expr(
            base(left_name.span),
            None,
            Some(mid(left_name.span)),
            element,
            true,
            true,
            left_name.span,
            None,
            None,
        )?;
        let mut right = self.slice_from_expr(
            base(right_name.span),
            Some(mid(right_name.span)),
            None,
            element,
            true,
            true,
            right_name.span,
            None,
            None,
        )?;
        if let ExprKind::Slice { split, .. } = &mut left.kind {
            *split = Some((group, true));
        }
        if let ExprKind::Slice { split, .. } = &mut right.kind {
            *split = Some((group, false));
        }
        let mut statements = Vec::with_capacity(4);
        if let Some(parent) = parent_statement {
            statements.push(parent);
        }
        statements.push(Statement::Let(mid_slot, midpoint));
        statements.push(Statement::Let(left_slot, left));
        statements.push(Statement::Let(right_slot, right));
        Ok(Some(statements))
    }
    /// Check a statement sequence. A destructuring `let` turns the rest of the
    /// sequence into the body of a single-arm match, so its bindings scope over it.
    pub(super) fn statements(
        &mut self,
        statements: &[ast::Statement],
        tail: Option<&ast::Expr>,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Block> {
        // Only the tail of a block in return position is returned.
        let tail_ensures = std::mem::take(&mut self.ensures_tail);
        let mut checked = Vec::new();
        let mut diverges = false;
        // Hidden temporary owners created while checking this statement list
        // belong to its scope. A nested block starts a fresh base, so its own
        // temporaries never leak into the enclosing statement list.
        let hoist_base = self.hoisted.len();
        for (index, statement) in statements.iter().enumerate() {
            if diverges {
                return Err(Diagnostic::new(
                    span,
                    "unreachable statement after return/panic/break",
                ));
            }
            match statement {
                ast::Statement::Let {
                    mutable,
                    pattern,
                    ty,
                    value,
                    ..
                } => {
                    if let Some(generated) =
                        self.split_binding(*mutable, pattern, ty.as_ref(), value, span)?
                    {
                        self.drain_hoisted(hoist_base, &mut checked);
                        checked.extend(generated);
                        continue;
                    }
                    let (annotation, grade) = match ty {
                        Some(ty) => {
                            let (inner, grade) = split_grade(ty);
                            let grade = grade
                                .map(|grade| grades::evaluate(self.resolution, &self.grades, grade))
                                .transpose()?;
                            (Some(self.ty(inner)?), grade)
                        }
                        None => (None, None),
                    };
                    // A `let p = <proof>` binding is erased: it introduces a
                    // checked kernel term, never a runtime local. Proof-valued
                    // locals may be re-passed to erased parameters and shadow
                    // each other exactly like ordinary lexical bindings.
                    if annotation.is_none()
                        && matches!(&pattern.kind, ast::PatternKind::Name(path) if path.len() == 1)
                        && !self.is_constructor_pattern(pattern)
                        && self.erased_proof_expression(value)
                    {
                        if *mutable {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "a proof-valued local is erased and cannot be mutable",
                            ));
                        }
                        let id = self.resolution.binder(pattern.span).unwrap();
                        let term = self.elaborate_proof_local(value)?;
                        self.proof_values
                            .insert(id, (term, self.kernel_locals.len()));
                        continue;
                    }
                    // `let f = fn(x) { ... }`: the binding's first use fixes
                    // the omitted lambda types (I-LAMBDA-INFER).
                    if annotation.is_none()
                        && let ast::ExprKind::Lambda(lambda) = &value.kind
                        && lambda_has_holes(lambda)
                        && matches!(&pattern.kind, ast::PatternKind::Name(path) if path.len() == 1)
                        && let Some(id) = self.resolution.binder(pattern.span)
                    {
                        self.lambda_hint =
                            self.first_use_hint(id, lambda, &statements[index + 1..], tail)?;
                    }
                    let value = self.expr_expected(value, annotation);
                    self.lambda_hint = None;
                    let value = value?;
                    self.drain_hoisted(hoist_base, &mut checked);
                    if value.ty.is_ref() && *mutable {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "reference bindings are immutable: a reborrow derives from the stored reference, so assign a new reference by binding a fresh 'let' instead of rebinding it",
                        ));
                    }
                    if value.ty.is_view() && *mutable {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "borrowed views are not mutable bindings and cannot be reassigned; bind them with 'let' without 'mut'",
                        ));
                    }
                    diverges = value.ty == Type::Never;
                    let ty = match annotation {
                        Some(ty) if self.types.is_structural(ty) => value.ty,
                        Some(ty) => ty,
                        // Mutable locals keep the declared enum, not one variant.
                        None if *mutable => self.types.full(value.ty, pattern.span)?,
                        None => value.ty,
                    };
                    if (!matches!(&pattern.kind, ast::PatternKind::Name(path) if path.len() == 1)
                        || self.is_constructor_pattern(pattern))
                        && !diverges
                    {
                        if grade.is_some() {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "usage grades require a simple name binding; destructure first, then annotate each binding separately",
                            ));
                        }
                        if *mutable {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "destructuring let bindings are immutable; rebind a field with 'let mut' afterwards",
                            ));
                        }
                        return self.destructure(
                            checked,
                            pattern,
                            value,
                            ty,
                            (&statements[index + 1..], tail),
                            span,
                            expected,
                        );
                    }
                    let slot = self.bind(pattern.span, ty, *mutable)?;
                    self.closure_writes.remove(&slot);
                    if let Some(targets) = self.closure_write_targets(&value) {
                        self.closure_writes.insert(slot, targets);
                    }
                    self.closure_captures.remove(&slot);
                    if let Some(types) = self.closure_capture_types(&value) {
                        self.closure_captures.insert(slot, types);
                    }
                    // Both immutable and mutable scalar bindings are symbolic
                    // index candidates. A mutable one is versioned: assignment
                    // appends a new binder instead of reinterpreting an old
                    // proof at the final value.
                    let id = self.resolution.binder(pattern.span).unwrap();
                    // `let alias = scalar` is a by-value copy. Keeping the
                    // source's current kernel binder lets proofs about the
                    // source value apply to the alias, while a later assignment
                    // to the source appends a new binder and leaves the alias
                    // frozen at the copied version.
                    let alias_source = match &value.kind {
                        ExprKind::Local(source_slot) => {
                            self.slots.iter().find_map(|(candidate, slot)| {
                                (*slot == *source_slot).then_some(*candidate)
                            })
                        }
                        _ => None,
                    };
                    self.admit_scalar_index(id, ty, pattern.span)?;
                    if let Some(source) = alias_source
                        && ty.scalar_carrier().is_some()
                    {
                        self.alias_scalar_index(id, source);
                    }
                    self.facts.define(slot, &value);
                    // `let x = S { .. }` knows each scalar field (STRUCT-UPDATE).
                    self.record_literal_facts(slot, &value);
                    // A whole value bound by `let` keeps the symbolic identity
                    // its postcondition facts talk about (ENSURES).
                    if crate::facts::scalar_range(value.ty).is_none()
                        && let Some((root, steps)) = self.facts.root_of(&value)
                    {
                        self.facts.alias(slot, root, steps);
                    }
                    self.define_view_length(slot, &value);
                    let must_use = self.copyable_result_grade(&value);
                    if let Some(required) = must_use
                        && let Some(annotation) = grade
                        && annotation != required
                    {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "a copyable result with the must-use @[{required}] contract cannot be bound to a local graded @[{annotation}]; bind it ungraded or as @[{required}]"
                            ),
                        ));
                    }
                    self.locals[slot].grade = grade.or(must_use);
                    self.locals[slot].linear = self.value_moves_linear(&value)
                        || (self.locals[slot].grade.is_some_and(Grade::is_one)
                            && self.owned_type(ty));
                    if !diverges {
                        self.validate_grade(grade, ty, pattern.span, true)?;
                    }
                    checked.push(Statement::Let(slot, value));
                }
                ast::Statement::Expr(expr) => {
                    let before = self.facts.clone();
                    let expr = self.expr(expr)?;
                    self.drain_hoisted(hoist_base, &mut checked);
                    if expr.ty != Type::Never && self.observes_copyable_result(&expr) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "this copyable result has the must-use `@[1]` contract and its value is discarded by an expression statement; bind it with 'let' and observe it exactly once, or pass it to a call",
                        ));
                    }
                    diverges = expr.ty == Type::Never;
                    // `if c { return; }` establishes `!c` for the rest of the block.
                    if let ExprKind::If(condition, yes, no) = &expr.kind
                        && self.facts.same_versions(&before)
                    {
                        if yes.ty == Type::Never && no.ty != Type::Never {
                            self.facts.assume(condition, false);
                        } else if no.ty == Type::Never && yes.ty != Type::Never {
                            self.facts.assume(condition, true);
                        }
                    }
                    checked.push(Statement::Expr(expr));
                }
            }
        }
        if let (true, Some(tail)) = (diverges, tail) {
            return Err(Diagnostic::new(
                tail.span,
                "unreachable expression after return/panic/break",
            ));
        }
        self.ensures_tail = tail_ensures && tail.is_some();
        if tail_ensures && tail.is_none() && !diverges {
            let unit = Expr {
                kind: ExprKind::Constant(0),
                ty: Type::Unit,
                span,
                resource: None,
            };
            self.check_postconditions(&unit)?;
        }
        let tail = tail
            .map(|tail| self.expr_expected_result(tail, expected).map(Box::new))
            .transpose()?;
        self.drain_hoisted(hoist_base, &mut checked);
        let ty = if diverges {
            Type::Never
        } else {
            tail.as_ref().map_or(Type::Unit, |tail| tail.ty)
        };
        Ok(Block {
            statements: checked,
            tail,
            ty,
        })
    }
    pub(super) fn is_constructor_pattern(&self, pattern: &ast::Pattern) -> bool {
        self.resolution
            .reference(pattern.span)
            .is_some_and(|id| self.resolution.bindings[id].kind == BindingKind::Constructor)
    }

    /// Exact usage grade evidenced by an already-checked argument expression.
    /// Only forms that carry one annotated binding are used for inference;
    /// everything else stays unknown instead of defaulting to one.
    pub(super) fn expression_grade(&self, expr: &Expr) -> Option<Grade> {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.locals[*slot].grade,
            ExprKind::Coerce { value, .. } => self.expression_grade(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .and_then(|tail| self.expression_grade(tail)),
            ExprKind::If(_, yes, no) => {
                let left = (yes.ty != Type::Never)
                    .then(|| {
                        yes.tail
                            .as_ref()
                            .and_then(|tail| self.expression_grade(tail))
                    })
                    .flatten();
                let right = (no.ty != Type::Never)
                    .then(|| {
                        no.tail
                            .as_ref()
                            .and_then(|tail| self.expression_grade(tail))
                    })
                    .flatten();
                match (left, right) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    /// Whether this expression evaluates to a copyable result carrying the
    /// must-use `@[1]` contract. The obligation is transferred through value
    /// positions (`let`, assignment, `return`, blocks, branches, match arms,
    /// loop break values, and coercions) and is discharged by an observation:
    /// a call argument, aggregate field, read, match scrutinee, or `?` operand.
    /// It is never an owning/linear move, even though it uses the same literal
    /// `@[1]` surface grade.
    pub(super) fn copyable_result_grade(&self, expr: &Expr) -> Option<Grade> {
        match &expr.kind {
            ExprKind::Call(Target::Function(index), _) => {
                self.functions.signatures.get(*index).and_then(|signature| {
                    signature
                        .result_grade
                        .filter(|grade| grade.is_one() && !self.owned_type(signature.result))
                })
            }
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                    self.types.function_types.get(id).and_then(|signature| {
                        signature
                            .result_grade
                            .filter(|grade| grade.is_one() && !self.owned_type(signature.result))
                    })
                }
                _ => None,
            },
            ExprKind::Coerce { value, .. } => self.copyable_result_grade(value),
            ExprKind::Block(block) | ExprKind::AbortScope { body: block, .. } => block
                .tail
                .as_ref()
                .and_then(|tail| self.copyable_result_grade(tail)),
            ExprKind::If(_, yes, no) => (yes.ty != Type::Never)
                .then(|| {
                    yes.tail
                        .as_ref()
                        .and_then(|tail| self.copyable_result_grade(tail))
                })
                .flatten()
                .or_else(|| {
                    (no.ty != Type::Never)
                        .then(|| {
                            no.tail
                                .as_ref()
                                .and_then(|tail| self.copyable_result_grade(tail))
                        })
                        .flatten()
                }),
            ExprKind::Match(_, arms) => arms.iter().find_map(|arm| {
                (arm.body.ty != Type::Never)
                    .then(|| self.copyable_result_grade(&arm.body))
                    .flatten()
            }),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .find_map(|value| self.copyable_result_grade(value)),
            // A copyable `@[1]` task result is delivered as `Completed` on both
            // the normal and cancellation paths. Joining the (linear) handle
            // produces a must-use `TaskExit<T>`; a scope returns the must-use
            // value directly.
            ExprKind::TaskJoin { obligation, .. } | ExprKind::TaskScope { obligation, .. } => {
                (*obligation && !self.owned_type(expr.ty)).then_some(Grade::ONE)
            }
            _ => None,
        }
    }
    pub(super) fn copyable_result_obligation(&self, expr: &Expr) -> bool {
        self.copyable_result_grade(expr).is_some()
    }
    /// Whether a returned value would observe a copyable must-use obligation.
    /// An owning `@[1]` result is a move instead and is handled by the
    /// ownership pass.
    pub(super) fn observes_copyable_result(&self, expr: &Expr) -> bool {
        self.copyable_result_obligation(expr) && !self.owned_type(expr.ty)
    }
    /// Whether a returned copyable must-use obligation may be transferred to
    /// the current function result. Only a matching `@[1]` copyable result
    /// contract can carry it; otherwise the caller would receive an ordinary
    /// value with no obligation.
    /// Whether a returned must-use obligation matches the current result
    /// contract. Exact grade equality is required: a custom algebra's `one` is
    /// not silently equated with the builtin exactly-one observation.
    pub(super) fn transfers_copyable_result_from(&self, expr: &Expr) -> bool {
        !self.owned_type(self.result)
            && self.result_grade.is_some()
            && self.result_grade == self.copyable_result_grade(expr)
    }
    /// Propagate binding obligations before lambda types and capture slots are
    /// elaborated. The ownership pass independently validates consumption later.
    ///
    /// A call whose checked signature declares a `@[1]` result contract returns
    /// an owning linear resource obligation even though its runtime type is
    /// merely owning. The obligation is derived from the already-created
    /// signature, so it is known before closure capture typing and synthetic
    /// capture locals. A copyable `@[1]` result is a must-use obligation, not a
    /// move, and is tracked by the grade pass instead.
    pub(super) fn value_moves_linear(&self, expr: &Expr) -> bool {
        if self.linear_type(expr.ty) {
            return true;
        }
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.locals[*slot].linear,
            ExprKind::Call(Target::Function(index), _) => self
                .functions
                .signatures
                .get(*index)
                .is_some_and(|signature| {
                    signature.result_grade.is_some_and(Grade::is_one)
                        && self.owned_type(signature.result)
                }),
            ExprKind::Call(
                Target::Vec(VecOp::Reserve | VecOp::Clear | VecOp::TryReserve { .. }, _),
                args,
            ) => args
                .first()
                .is_some_and(|owner| self.value_moves_linear(owner)),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                    self.types.function_types.get(id).is_some_and(|signature| {
                        signature.result_grade.is_some_and(Grade::is_one)
                            && self.owned_type(signature.result)
                    })
                }
                _ => false,
            },
            ExprKind::Block(b) | ExprKind::AbortScope { body: b, .. } => {
                b.tail.as_ref().is_some_and(|e| self.value_moves_linear(e))
            }
            ExprKind::If(_, a, b) => [a, b].iter().any(|b| {
                b.ty != Type::Never && b.tail.as_ref().is_some_and(|e| self.value_moves_linear(e))
            }),
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|a| a.body.ty != Type::Never && self.value_moves_linear(&a.body)),
            ExprKind::Loop(b) => crate::ownership::loop_break_values(b)
                .into_iter()
                .any(|e| self.value_moves_linear(e)),
            ExprKind::Construct { fields, .. } => fields.iter().any(|e| self.value_moves_linear(e)),
            ExprKind::FnValue { captures, .. } => {
                captures.iter().any(|e| self.value_moves_linear(e))
            }
            ExprKind::BoxNew(e)
            | ExprKind::Try { value: e, .. }
            | ExprKind::Coerce { value: e, .. } => self.value_moves_linear(e),
            ExprKind::BoxTake(e) if self.owned_type(expr.ty) => self.value_moves_linear(e),
            // Reuse returns an owner carrying the old binding obligation.
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            } => self.value_moves_linear(owner) || self.value_moves_linear(payload),
            ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            }
            | ExprKind::ArenaTryAlloc { value, .. }
            | ExprKind::ArenaBoxTake(value) => self.value_moves_linear(value),
            // In-place map returns the same vector owner it consumed.
            ExprKind::VecMap { vector, .. } => self.value_moves_linear(vector),
            ExprKind::DynArrayPush { array, value, .. } => {
                self.value_moves_linear(array) || self.value_moves_linear(value)
            }
            ExprKind::DynArrayFill { length, value, .. } => {
                self.value_moves_linear(length) || self.value_moves_linear(value)
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                self.value_moves_linear(array)
                    || self.value_moves_linear(index)
                    || self.value_moves_linear(value)
            }
            ExprKind::DynArrayPop { array, .. } => self.value_moves_linear(array),
            ExprKind::DynArrayEqual { left, right, .. } => {
                self.value_moves_linear(left) || self.value_moves_linear(right)
            }
            ExprKind::HandlerPush { body, .. } => body
                .tail
                .as_deref()
                .is_some_and(|tail| self.value_moves_linear(tail)),
            ExprKind::DynamicPerform { .. } => {
                self.owned_type(expr.ty) || self.linear_type(expr.ty)
            }
            // A task/scope whose result carries an owning or linear obligation
            // transfers it to the handle (or to the joined TaskExit).
            ExprKind::TaskSpawn { obligation, .. }
            | ExprKind::TaskScope { obligation, .. }
            | ExprKind::TaskJoin { obligation, .. } => *obligation,
            _ => false,
        }
    }
    /// Whether any normal return of `block` transfers a binding-based or
    /// graded result obligation. Intrinsic linear result types carry their
    /// obligation in the type itself and are reported by the caller separately.
    ///
    /// This walks every `return` expression, including returns nested in
    /// arguments, branches, and loops, plus the block's tail value. It is
    /// deliberately syntactic and conservative: the ownership pass later
    /// revalidates the same obligation on each path.
    pub(super) fn return_obligation(&self, block: &Block) -> Option<Span> {
        fn find(checker: &Checker, expr: &Expr) -> Option<Span> {
            match &expr.kind {
                ExprKind::Return(value) => checker
                    .value_moves_linear(value)
                    .then_some(value.span)
                    .or_else(|| find(checker, value)),
                ExprKind::Block(block) => find_in_block(checker, block),
                ExprKind::If(condition, yes, no) => find(checker, condition)
                    .or_else(|| find_in_block(checker, yes))
                    .or_else(|| find_in_block(checker, no)),
                ExprKind::Match(scrutinee, arms) => find(checker, scrutinee).or_else(|| {
                    arms.iter().find_map(|arm| {
                        arm.guard
                            .as_ref()
                            .and_then(|guard| find(checker, guard))
                            .or_else(|| find(checker, &arm.body))
                    })
                }),
                ExprKind::Loop(block) => find_in_block(checker, block),
                ExprKind::While(condition, block) => {
                    find(checker, condition).or_else(|| find_in_block(checker, block))
                }
                ExprKind::Call(_, arguments)
                | ExprKind::Construct {
                    fields: arguments, ..
                } => arguments
                    .iter()
                    .find_map(|argument| find(checker, argument)),
                ExprKind::CallIndirect { callee, arguments } => {
                    find(checker, callee).or_else(|| {
                        arguments
                            .iter()
                            .find_map(|argument| find(checker, argument))
                    })
                }
                ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                    find(checker, body)
                }
                ExprKind::Unary(_, inner)
                | ExprKind::BoxNew(inner)
                | ExprKind::BoxTake(inner)
                | ExprKind::BoxRead(inner)
                | ExprKind::BoxTryNew { value: inner, .. }
                | ExprKind::BytesTryWithCapacity {
                    capacity: inner, ..
                }
                | ExprKind::ArenaBoxRead(inner)
                | ExprKind::ArenaBoxTake(inner)
                | ExprKind::Drop(inner)
                | ExprKind::Project(inner, _)
                | ExprKind::InitOwner { value: inner, .. }
                | ExprKind::BorrowInit { value: inner, .. }
                | ExprKind::Coerce { value: inner, .. }
                | ExprKind::Assign(_, inner)
                | ExprKind::Break(Some(inner), _)
                | ExprKind::Try { value: inner, .. }
                | ExprKind::TaskCancel(inner)
                | ExprKind::TaskJoin { task: inner, .. } => find(checker, inner),
                ExprKind::Binary(_, left, right)
                | ExprKind::BytesAt(left, right)
                | ExprKind::StructEq { left, right, .. }
                | ExprKind::DynArrayEqual { left, right, .. } => {
                    find(checker, left).or_else(|| find(checker, right))
                }
                ExprKind::RefAssign(reference, _, value) | ExprKind::BoxWrite(reference, value) => {
                    find(checker, reference).or_else(|| find(checker, value))
                }
                ExprKind::BoxReuse { owner, payload }
                | ExprKind::ArenaAlloc {
                    arena: owner,
                    value: payload,
                }
                | ExprKind::ArenaTryAlloc {
                    arena: owner,
                    value: payload,
                    ..
                } => find(checker, owner).or_else(|| find(checker, payload)),
                ExprKind::ArenaNew => None,
                ExprKind::ArenaNewWith { strategy } => find(checker, strategy),
                ExprKind::DynArrayPush { array, value, .. } => {
                    find(checker, array).or_else(|| find(checker, value))
                }
                ExprKind::DynArrayFill { length, value, .. } => {
                    find(checker, length).or_else(|| find(checker, value))
                }
                ExprKind::DynArraySet {
                    array,
                    index,
                    value,
                    ..
                } => find(checker, array)
                    .or_else(|| find(checker, index))
                    .or_else(|| find(checker, value)),
                ExprKind::DynArrayPop { array, .. } => find(checker, array),
                ExprKind::HandlerPush { handler, body, .. } => {
                    find(checker, handler).or_else(|| find_in_block(checker, body))
                }
                ExprKind::AbortScope { handler, body, .. } => {
                    find(checker, handler).or_else(|| find_in_block(checker, body))
                }
                ExprKind::AbortExit { value, .. } => find(checker, value),
                ExprKind::DynamicPerform {
                    payload, resume, ..
                } => find(checker, payload).or_else(|| find(checker, resume)),
                ExprKind::DynArrayNew { .. } => None,
                ExprKind::VecMap {
                    vector, callbacks, ..
                } => find(checker, vector).or_else(|| {
                    callbacks
                        .iter()
                        .find_map(|callback| find(checker, callback))
                }),
                ExprKind::Slice {
                    base, start, end, ..
                } => find(checker, base)
                    .or_else(|| start.as_deref().and_then(|e| find(checker, e)))
                    .or_else(|| end.as_deref().and_then(|e| find(checker, e))),
                ExprKind::FnValue { captures, .. } => {
                    captures.iter().find_map(|capture| find(checker, capture))
                }
                _ => None,
            }
        }
        fn find_in_block(checker: &Checker, block: &Block) -> Option<Span> {
            block
                .statements
                .iter()
                .find_map(|statement| match statement {
                    Statement::Let(_, value) | Statement::Expr(value) => find(checker, value),
                    Statement::Declare(_) => None,
                })
                .or_else(|| block.tail.as_deref().and_then(|tail| find(checker, tail)))
        }
        find_in_block(self, block).or_else(|| {
            let tail = block.tail.as_deref()?;
            self.value_moves_linear(tail).then_some(tail.span)
        })
    }
    /// Parts bound by a pattern inherit a graded `@[1]` obligation of the
    /// value they come from. A value whose type is itself linear carries its
    /// obligation in the type: destructuring discharges it and each part keeps
    /// only the obligation of its own type.
    pub(super) fn linear_pattern(&mut self, pattern: &Pattern, linear: bool) {
        if linear {
            let mut slots = std::collections::BTreeSet::new();
            crate::ownership::pattern_bindings(pattern, &mut slots);
            for slot in slots {
                if self.owned_type(self.locals[slot].ty) {
                    self.locals[slot].linear = true;
                }
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn destructure(
        &mut self,
        mut checked: Vec<Statement>,
        pattern: &ast::Pattern,
        value: Expr,
        ty: Type,
        rest: (&[ast::Statement], Option<&ast::Expr>),
        span: Span,
        expected: Option<Type>,
    ) -> Result<Block> {
        let pattern_ir = self.pattern(pattern, ty, &mut BTreeMap::new())?;
        if self.observes_copyable_result(&value) {
            return Err(Diagnostic::new(
                pattern.span,
                "a copyable result with the must-use `@[1]` contract must be bound to a simple name or observed directly; destructuring would split off the obligation without a tracked destination",
            ));
        }
        self.linear_pattern(
            &pattern_ir,
            self.value_moves_linear(&value) && !self.linear_type(value.ty),
        );
        let mut coverage = Coverage::new(pattern.span);
        coverage.add(&pattern_ir);
        if coverage.useful(&Pattern::Any, ty, &self.types.enums, &self.types.unions)? {
            return Err(Diagnostic::new(
                pattern.span,
                "let patterns must be irrefutable; use match for patterns that can fail",
            ));
        }
        let body = {
            let kernel_mark = self.kernel_locals.len();
            let body = self.statements(rest.0, rest.1, span, expected);
            self.truncate_kernel(kernel_mark);
            body
        }?;
        let result = body.ty;
        let body = Expr {
            kind: ExprKind::Block(body),
            ty: result,
            span,
            resource: None,
        };
        let matched = Expr {
            kind: ExprKind::Match(
                Box::new(value),
                vec![Arm {
                    pattern: pattern_ir,
                    guard: None,
                    body,
                }],
            ),
            ty: result,
            span,
            resource: None,
        };
        let ty = matched.ty;
        checked.push(Statement::Expr(matched));
        let _ = ty;
        // The match is the block's final value.
        let Statement::Expr(tail) = checked.pop().unwrap() else {
            unreachable!()
        };
        Ok(Block {
            statements: checked,
            ty: tail.ty,
            tail: Some(Box::new(tail)),
        })
    }
    pub(super) fn expr(&mut self, expr: &ast::Expr) -> Result<Expr> {
        self.expr_expected(expr, None)
    }
    /// Whether an expected type is the enclosing function's erased result.
    /// Such a position accepts `Unit` as the erased value in addition to the
    /// declared copyable payload type.
    pub(super) fn erased_result_context(&self, expected: Option<Type>) -> bool {
        self.result_grade.is_some_and(Grade::is_zero) && expected == Some(self.result)
    }
    /// Check a value in a possible erased-result position. A nested call to
    /// another erased-result function produces `Unit`; returning it through an
    /// erased result is well-typed and carries no payload. Every other value is
    /// checked against the declared payload type normally.
    pub(super) fn expr_expected_result(
        &mut self,
        expr: &ast::Expr,
        expected: Option<Type>,
    ) -> Result<Expr> {
        if !self.erased_result_context(expected) {
            return self.expr_expected(expr, expected);
        }
        let value = self.expr(expr)?;
        if matches!(value.ty, Type::Unit | Type::Never) {
            return Ok(value);
        }
        let span = value.span;
        self.coerce(value, self.result, span)
    }
    /// Erase an expression's value in an erased-result position while keeping
    /// its effects and cleanup. `Drop` is a checked no-op for the copyable
    /// payload types admitted by `@[0]`.
    pub(super) fn erase_value(&mut self, value: Expr, span: Span) -> Expr {
        if matches!(value.ty, Type::Unit | Type::Never) {
            return value;
        }
        Expr {
            kind: ExprKind::Drop(Box::new(value)),
            ty: Type::Unit,
            span,
            resource: None,
        }
    }
    pub(super) fn erase_block_value(&mut self, mut block: Block, span: Span) -> Block {
        if matches!(block.ty, Type::Unit | Type::Never) {
            return block;
        }
        let tail = block.tail.take().expect("non-unit block has a tail");
        block.tail = Some(Box::new(self.erase_value(*tail, span)));
        block.ty = Type::Unit;
        block
    }
    /// Check an expression; when it is a value the function returns, also
    /// prove the function's postconditions for it (ENSURES).
    pub(super) fn expr_expected(
        &mut self,
        expr: &ast::Expr,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let tail = std::mem::take(&mut self.ensures_tail);
        if !tail {
            let value = self.expr_expected_unchecked(expr, expected)?;
            self.forget_mutable_borrows(&value);
            return Ok(value);
        }
        if matches!(
            expr.kind,
            ast::ExprKind::If { .. } | ast::ExprKind::Match { .. } | ast::ExprKind::Block(_)
        ) {
            self.branch_tail = true;
            let result = self.expr_expected_unchecked(expr, expected);
            self.branch_tail = false;
            // An `if` without `else` returns unit when its condition fails.
            if let (
                Ok(value),
                ast::ExprKind::If {
                    otherwise: None, ..
                },
            ) = (&result, &expr.kind)
            {
                self.check_postconditions(value)?;
            }
            return result;
        }
        let value = self.expr_expected_unchecked(expr, expected)?;
        self.forget_mutable_borrows(&value);
        self.check_postconditions(&value)?;
        Ok(value)
    }
    /// Writes through an exclusive borrow are invisible to the facts, so a
    /// local borrowed `&mut` (also as a method receiver or a field place)
    /// leaves the fact system for the rest of the function.
    pub(super) fn forget_mutable_borrows(&mut self, value: &Expr) {
        let mut roots = Vec::new();
        let mut visit = |e: &Expr| {
            if (matches!(e.ty, Type::RefMut(_)) || e.ty.is_mut_slice())
                && let Some(root) = place_root_slot(e)
            {
                roots.push(root);
            }
        };
        visit(value);
        value.for_each_child(&mut visit);
        for root in roots {
            self.facts.make_opaque(root);
        }
    }
}
