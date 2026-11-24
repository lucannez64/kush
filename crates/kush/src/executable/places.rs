//! Ownership classes, constants, length facts, places and fields.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Strip the checker-only lifetime annotation from a container element.
    /// The annotation has no runtime representation and never reaches a
    /// user-visible expression type.
    pub(super) fn unannotate(&self, ty: Type) -> Type {
        match ty {
            Type::Annotated(p, _) => self.types.pointees[p],
            ty => ty,
        }
    }
    /// Whether values of `ty` own heap storage (computed from layouts).
    pub(super) fn carrier_type(&self, ty: Type) -> bool {
        ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
    }
    pub(super) fn owned_type(&self, ty: Type) -> bool {
        fn go(types: &Types<'_>, ty: Type, depth: usize) -> bool {
            match ty {
                Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::AllocatorContext
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::Once(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_) => true,
                // Never copied: reads go through `Atomic.*` (it owns nothing
                // to drop; the ownership pass only tracks its moves).
                Type::Atomic | Type::Channel(_) | Type::GpuBuf(_) => true,
                Type::Enum(id) | Type::Variants(id, _) if depth < 64 => {
                    types.enums[id].linear
                        || types.enums[id]
                            .variants
                            .iter()
                            .any(|v| v.fields.iter().any(|f| go(types, *f, depth + 1)))
                }
                Type::Union(id) if depth < 64 => types.unions[id]
                    .members
                    .iter()
                    .any(|member| go(types, *member, depth + 1)),
                _ => false,
            }
        }
        go(self.types, ty, 0)
    }
    /// A use of `const NAME: Type = value;`: `value`, checked here against
    /// `Type`. A literal value therefore compiles to that literal.
    pub(super) fn constant(
        &mut self,
        id: BindingId,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let declared = &self.functions.declared[&id];
        let f = declared.ast;
        let Some(value) = f.body.as_ref().and_then(|body| body.tail.as_deref()) else {
            unreachable!("a constant always has a value");
        };
        if self.expanding_constants.contains(&id) {
            return Err(Diagnostic::new(
                span,
                "this constant's value refers to itself",
            ));
        }
        let ty = self.ty(&f.result)?;
        self.expanding_constants.push(id);
        let checked = self.expr_expected(value, Some(ty));
        self.expanding_constants.pop();
        let mut checked = checked?;
        self.expect(checked.ty, ty, span)?;
        checked.span = span;
        match expected {
            Some(expected) => self.coerce(checked, expected, span),
            None => Ok(checked),
        }
    }
    /// The value of a compile-time integer expression: literals, constants,
    /// parentheses, unary minus and `+ - * / % << >> & | ^` over them.
    pub(super) fn ast_integer(&self, expr: &ast::Expr, depth: usize) -> Option<i64> {
        if depth > 64 {
            return None;
        }
        match &expr.kind {
            ast::ExprKind::Integer(text) => text.parse::<i64>().ok(),
            ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => {
                let id = self.resolution.reference(expr.span)?;
                let declared = self.functions.declared.get(&id)?;
                if !declared.ast.constant {
                    return None;
                }
                let value = declared.ast.body.as_ref()?.tail.as_deref()?;
                self.ast_integer(value, depth + 1)
            }
            ast::ExprKind::Unary {
                op: Kind::Minus,
                operand,
                ..
            } => self.ast_integer(operand, depth + 1)?.checked_neg(),
            ast::ExprKind::Binary { op, left, right } => {
                let l = self.ast_integer(left, depth + 1)?;
                let r = self.ast_integer(right, depth + 1)?;
                match op {
                    Kind::Plus => l.checked_add(r),
                    Kind::Minus => l.checked_sub(r),
                    Kind::Star => l.checked_mul(r),
                    Kind::Slash => l.checked_div(r),
                    Kind::Percent => l.checked_rem(r),
                    Kind::Shl => u32::try_from(r).ok().and_then(|r| l.checked_shl(r)),
                    Kind::Shr => u32::try_from(r).ok().and_then(|r| l.checked_shr(r)),
                    Kind::Amp => Some(l & r),
                    Kind::Pipe => Some(l | r),
                    Kind::Caret => Some(l ^ r),
                    _ => None,
                }
            }
            ast::ExprKind::Block(block) if block.statements.is_empty() => {
                self.ast_integer(block.tail.as_deref()?, depth + 1)
            }
            _ => None,
        }
    }
    /// A record literal whose fields declare `where len >= N`: each such
    /// vector is checked once here (a read of element N - 1), so every later
    /// access may rely on the length.
    /// A `&Vec<T>` / `&mut Vec<T>` argument checked at run time to reach a
    /// vector of at least `length` elements; the reference itself is passed.
    pub(super) fn reference_length_checked(&mut self, value: Expr, length: i64) -> Result<Expr> {
        let ty = value.ty;
        let Some(Type::Vec(pointer)) = ty.ref_pointee().map(|pointer| self.types.pointees[pointer])
        else {
            return Err(Diagnostic::new(
                value.span,
                "'where len >= N' needs a '&Vec<T>' or '&mut Vec<T>' argument",
            ));
        };
        let element = self.unannotate(self.types.pointees[pointer]);
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                value.span,
                "this argument's length must be known to reach 'len >= N' (its elements own resources, so it cannot be checked by reading one)",
            ));
        }
        if length <= 0 {
            return Ok(value);
        }
        self.require(PANIC, value.span)?;
        let span = value.span;
        let slot = self.fresh_local(span, ty)?;
        let reader = Expr {
            kind: ExprKind::Peek(slot),
            ty: Type::Ref(self.types.pointer(Type::Vec(pointer))),
            span,
            resource: None,
        };
        let check = Expr {
            kind: ExprKind::Call(
                Target::Vec(VecOp::Get, element),
                vec![
                    reader,
                    Expr {
                        kind: ExprKind::Constant(length - 1),
                        ty: Type::I64,
                        span,
                        resource: None,
                    },
                ],
            ),
            ty: element,
            span,
            resource: None,
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements: vec![Statement::Let(slot, value), Statement::Expr(check)],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span,
                    resource: None,
                })),
                ty,
            }),
            ty,
            span,
            resource: None,
        })
    }
    /// `value` (a `Vec<T>` of type `ty`), checked at run time to hold at
    /// least `length` elements: the value of a length-refined field.
    pub(super) fn length_checked(&mut self, value: Expr, ty: Type, length: i64) -> Result<Expr> {
        let Type::Vec(pointer) = ty else {
            return Err(Diagnostic::new(
                value.span,
                "'where len >= N' applies to Vec<T> fields",
            ));
        };
        if value.ty == Type::Never || length <= 0 {
            return Ok(value);
        }
        let element = self.unannotate(self.types.pointees[pointer]);
        self.require(PANIC, value.span)?;
        let span = value.span;
        let slot = self.fresh_local(span, ty)?;
        let borrow = Expr {
            kind: ExprKind::Borrow(slot),
            ty: Type::Ref(self.types.pointer(ty)),
            span,
            resource: None,
        };
        let check = Expr {
            kind: ExprKind::Call(
                Target::Vec(VecOp::Get, element),
                vec![
                    borrow,
                    Expr {
                        kind: ExprKind::Constant(length - 1),
                        ty: Type::I64,
                        span,
                        resource: None,
                    },
                ],
            ),
            ty: element,
            span,
            resource: None,
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements: vec![Statement::Let(slot, value), Statement::Expr(check)],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span,
                    resource: None,
                })),
                ty,
            }),
            ty,
            span,
            resource: None,
        })
    }
    pub(super) fn establish_field_lengths(&mut self, mut value: Expr) -> Result<Expr> {
        let target = match &mut value.kind {
            ExprKind::Coerce { value: inner, .. } => &mut **inner,
            _ => &mut value,
        };
        let ExprKind::Construct {
            enum_id, fields, ..
        } = &mut target.kind
        else {
            return Ok(value);
        };
        let definition = self.types.enums[*enum_id].definition;
        let Some(lengths) = self.functions.field_lengths.get(&definition).cloned() else {
            return Ok(value);
        };
        let names = self.types.enums[*enum_id].variants[0].names.clone();
        let types = self.types.enums[*enum_id].variants[0].fields.clone();
        for (index, name) in names.iter().enumerate() {
            let Some(length) = lengths.get(name) else {
                continue;
            };
            let Some(length) = self.ast_integer(length, 0) else {
                return Err(Diagnostic::new(
                    length.span,
                    "the length in 'where len >= N' must be a compile-time integer",
                ));
            };
            if !matches!(types[index], Type::Vec(_)) {
                return Err(Diagnostic::new(
                    fields[index].span,
                    "'where len >= N' applies to Vec<T> fields",
                ));
            }
            let field = std::mem::replace(
                &mut fields[index],
                Expr {
                    kind: ExprKind::Constant(0),
                    ty: Type::I64,
                    span: target.span,
                    resource: None,
                },
            );
            fields[index] = self.length_checked(field, types[index], length)?;
        }
        Ok(value)
    }
    /// The minimum length a field place is declared to keep
    /// (`where len >= N`), when `place` is such a field.
    pub(super) fn place_min_length(&self, place: &ast::Expr) -> Option<i64> {
        match &place.kind {
            ast::ExprKind::Name(_) => {
                return self
                    .slot(place.span)
                    .ok()
                    .and_then(|slot| self.parameter_lengths.get(&slot).copied());
            }
            ast::ExprKind::Unary {
                op: Kind::Star,
                operand,
                ..
            } => return self.place_min_length(operand),
            _ => {}
        }
        let ast::ExprKind::Field { value, name } = &place.kind else {
            return None;
        };
        let record = self.place_type(value)?;
        let record = match record.ref_pointee() {
            Some(pointer) => self.types.pointees[pointer],
            None => record,
        };
        let id = record.layout()?;
        let definition = self.types.enums.get(id)?.definition;
        let length = self.functions.field_lengths.get(&definition)?.get(name)?;
        self.ast_integer(length, 0)
    }
    /// Try to prove `0 <= index < length` from the facts in scope; count the
    /// outcome for the proof report.
    pub(super) fn prove_in_bounds(
        &mut self,
        index: &Expr,
        length: Option<i64>,
        span: Span,
    ) -> bool {
        let proved = match (length, self.facts.linear(index)) {
            (Some(length), Some(position)) => self.try_prove(
                vec![
                    (
                        crate::facts::Linear::constant(0),
                        Kind::Le,
                        position.clone(),
                    ),
                    (
                        position,
                        Kind::Lt,
                        crate::facts::Linear::constant(i128::from(length)),
                    ),
                ],
                &format!("0 <= index && index < {length}"),
                span,
            ),
            _ => false,
        };
        if proved {
            self.functions.bounds_proved += 1;
            let kind = ObligationKind::Bounds {
                container: Container::Vec,
                refined_length: length,
            };
            self.record_check(kind, span, "0 <= index && index < len".to_owned(), true);
        } else {
            self.functions.bounds_checked += 1;
            self.record_bounds(Container::Vec, length, span);
        }
        proved
    }
    /// The type of a place (a local or a field chain rooted at one), looked
    /// up without checking or reading it, so no ownership rule applies yet.
    pub(super) fn place_type(&self, expr: &ast::Expr) -> Option<Type> {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => {
                self.slot(expr.span).ok().map(|slot| self.locals[slot].ty)
            }
            ast::ExprKind::Field { value, name }
                if self.resolution.reference(expr.span).is_none() =>
            {
                let base = self.place_type(value)?;
                let base = match base.ref_pointee() {
                    Some(pointer) => self.types.pointees[pointer],
                    None => base,
                };
                self.record_offset(base, name, expr.span)
                    .ok()
                    .map(|(_, ty)| ty)
            }
            _ => None,
        }
    }
    /// The receiver for an element access of an owning `Vec`/`Bytes` place:
    /// an existing reference is passed on (reborrowed), anything else is
    /// borrowed in place, as `&place` / `&mut place` would be.
    pub(super) fn container_receiver(&mut self, base: &ast::Expr, mutable: bool) -> Result<Expr> {
        let reference = self.place_type(base).is_some_and(|ty| ty.is_ref());
        if reference && matches!(base.kind, ast::ExprKind::Name(_)) {
            let slot = self.slot(base.span)?;
            let ty = self.locals[slot].ty;
            if mutable && !matches!(ty, Type::RefMut(_)) {
                return Err(Diagnostic::new(
                    base.span,
                    "cannot write through a shared reference; it must be an exclusive '&mut'",
                ));
            }
            return Ok(match (mutable, ty) {
                // A shared read through `&mut` reborrows it as shared.
                (false, Type::RefMut(pointer)) => Expr {
                    kind: ExprKind::Peek(slot),
                    ty: Type::Ref(pointer),
                    span: base.span,
                    resource: None,
                },
                _ => Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span: base.span,
                    resource: None,
                },
            });
        }
        let borrow = ast::Expr {
            kind: ast::ExprKind::Unary {
                op: Kind::Amp,
                mutable,
                operand: Box::new(base.clone()),
            },
            span: base.span,
        };
        self.expr(&borrow)
    }
    /// `place[index]` for a `Vec<T>` or `Bytes` place, including a field
    /// reached through a reference: the same checked read as
    /// `Vec.get(&place, index)` / `Bytes.get(&place, index)`.
    pub(super) fn container_index(
        &mut self,
        base: &ast::Expr,
        index: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Option<Expr>> {
        if !self.is_place(base) {
            return Ok(None);
        }
        let Some(ty) = self.place_type(base) else {
            return Ok(None);
        };
        let pointee = match ty.ref_pointee() {
            Some(pointer) => self.types.pointees[pointer],
            None => ty,
        };
        match pointee {
            Type::Vec(pointer) => {
                let receiver = self.container_receiver(base, false)?;
                let length = self.place_min_length(base);
                if length.is_none() {
                    self.functions.bounds_checked += 1;
                    self.record_bounds(Container::Vec, None, span);
                    return self
                        .vec_call_with(
                            "Vec.get",
                            receiver,
                            std::slice::from_ref(index),
                            expected,
                            span,
                        )
                        .map(Some);
                }
                // A field that keeps `len >= N`: an index proved below N is
                // read without a check.
                let element = self.unannotate(self.types.pointees[pointer]);
                if self.owned_type(element) {
                    return Err(Diagnostic::new(
                        span,
                        "indexing copies the element, but it owns resources",
                    ));
                }
                let index = self.expr_expected(index, Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                let op = if self.prove_in_bounds(&index, length, span) {
                    VecOp::At
                } else {
                    self.require(PANIC, span)?;
                    VecOp::Get
                };
                let ty = if index.ty == Type::Never {
                    Type::Never
                } else {
                    element
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::Vec(op, element), vec![receiver, index]),
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span).map(Some),
                    None => Ok(Some(value)),
                }
            }
            Type::Bytes => {
                let receiver = self.container_receiver(base, false)?;
                self.bytes_method(
                    BytesOp::Get,
                    receiver,
                    std::slice::from_ref(index),
                    expected,
                    span,
                )
                .map(Some)
            }
            _ => Ok(None),
        }
    }
    /// `place[index] = value`. The index and the value are evaluated first,
    /// in that order, into hidden locals; only then is the place borrowed
    /// exclusively for the write. So the value may read the place's owner
    /// (`m.memory[i] = m.a`), as a call that took `&mut` first could not.
    /// A `Vec<T>` place is written as `Vec.set(&mut place, i, v)`; an inline
    /// array or an exclusive slice view as `Slice.set(&mut place[..], i, v)`.
    pub(super) fn index_assign(
        &mut self,
        base: &ast::Expr,
        index: &ast::Expr,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Expr> {
        let ty = self.place_type(base);
        let pointee = ty.map(|ty| match ty.ref_pointee() {
            Some(pointer) => self.types.pointees[pointer],
            None => ty,
        });
        let element = match pointee {
            Some(Type::Vec(pointer)) => Some(self.types.pointees[pointer]),
            Some(Type::Bytes) => {
                return Err(Diagnostic::new(
                    span,
                    "a byte of Bytes is written through a byte view: Slice.set(&mut bytes[..], index, value); or store the bytes in a Vec<u8>, which supports place[index] = value",
                ));
            }
            _ => None,
        };
        let element = match element {
            Some(element) => element,
            None => {
                // Inline arrays and exclusive slice views: the element type
                // comes from the view.
                let probe = match ty {
                    Some(Type::SliceMut(pointer)) => Some(self.types.pointees[pointer]),
                    Some(ty) => ty
                        .layout()
                        .and_then(|id| self.types.enums[id].array)
                        .map(|(element, _)| element),
                    None => None,
                };
                let Some(element) = probe else {
                    return Err(Diagnostic::new(
                        base.span,
                        "index assignment needs a Vec<T>, an inline array or an exclusive '&mut [T]' view",
                    ));
                };
                element
            }
        };
        if self.owned_type(element) || self.linear_type(element) {
            return Err(Diagnostic::new(
                span,
                "index assignment replaces a copyable element; this element owns resources or is linear",
            ));
        }
        self.require(PANIC, span)?;
        let index = self.expr_expected(index, Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        let value = self.expr_expected(value, Some(element))?;
        self.expect(value.ty, element, value.span)?;
        if index.ty == Type::Never || value.ty == Type::Never {
            let mut statements = vec![Statement::Expr(index)];
            statements.push(Statement::Expr(value));
            return Ok(Expr {
                kind: ExprKind::Block(Block {
                    statements,
                    tail: None,
                    ty: Type::Never,
                }),
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let index_slot = self.fresh_local(index.span, Type::I64)?;
        let value_slot = self.fresh_local(value.span, element)?;
        // The hidden index local equals the index expression, for the proof.
        self.facts.assign(index_slot, &index);
        let local = |slot, ty, span| Expr {
            kind: ExprKind::Local(slot),
            ty,
            span,
            resource: None,
        };
        let index_span = index.span;
        let value_span = value.span;
        let statements = vec![
            Statement::Let(index_slot, index),
            Statement::Let(value_slot, value),
        ];
        let call = if matches!(pointee, Some(Type::Vec(_))) {
            let length = self.place_min_length(base);
            let probe = local(index_slot, Type::I64, index_span);
            let op = if length.is_some() && self.prove_in_bounds(&probe, length, span) {
                VecOp::SetProved
            } else {
                if length.is_none() {
                    self.functions.bounds_checked += 1;
                    self.record_bounds(Container::Vec, None, span);
                }
                VecOp::SetBorrowed
            };
            self.writing_bounded_field = true;
            let receiver = self.container_receiver(base, true);
            self.writing_bounded_field = false;
            let receiver = receiver?;
            Expr {
                kind: ExprKind::Call(
                    Target::Vec(op, element),
                    vec![
                        receiver,
                        local(index_slot, Type::I64, index_span),
                        local(value_slot, element, value_span),
                    ],
                ),
                ty: Type::Unit,
                span,
                resource: None,
            }
        } else {
            let view = self.slice_view(base, None, None, true, span, None)?;
            Expr {
                kind: ExprKind::Call(
                    Target::Slice(SliceOp::Set, element),
                    vec![
                        view,
                        local(index_slot, Type::I64, index_span),
                        local(value_slot, element, value_span),
                    ],
                ),
                ty: Type::Unit,
                span,
                resource: None,
            }
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements,
                tail: Some(Box::new(call)),
                ty: Type::Unit,
            }),
            ty: Type::Unit,
            span,
            resource: None,
        })
    }
    /// A non-moving read of a local or a nested record field of one.
    pub(super) fn place(&mut self, expr: &ast::Expr) -> Result<Expr> {
        self.place_at(expr, false)
    }
    /// `intermediate`: this place is only a step towards a field of it
    /// (`m.apu` in `m.apu.powered`). An owning record may be such a step
    /// through a reference: nothing is moved or copied but the final field,
    /// which must itself be copyable.
    pub(super) fn place_at(&mut self, expr: &ast::Expr, intermediate: bool) -> Result<Expr> {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => {
                if let Ok(slot) = self.slot(expr.span) {
                    return Ok(Expr {
                        kind: ExprKind::Peek(slot),
                        ty: self.locals[slot].ty,
                        span: expr.span,
                        resource: None,
                    });
                }
            }
            ast::ExprKind::Field { value, name }
                if self.resolution.reference(expr.span).is_none() =>
            {
                let base = self.place_at(value, true)?;
                if base.ty.is_ref() {
                    let pointer = base.ty.ref_pointee().expect("reference pointee");
                    let pointee = self.types.pointees[pointer];
                    let (offset, ty) = self.record_offset(pointee, name, expr.span)?;
                    let owning_step = intermediate
                        && ty.layout().is_some_and(|id| self.types.enums[id].record)
                        && !self.linear_type(ty);
                    if (self.owned_type(ty) && !owning_step)
                        || self.linear_type(ty)
                        || (ty.is_view() && ty.is_mut_slice())
                        || matches!(ty, Type::RefMut(_))
                        || ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
                        || ty
                            .layout()
                            .is_some_and(|id| self.types.enums[id].mutable_borrow)
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "field '{name}' cannot be read through a record reference because it owns storage or contains a borrow; destructure an owning value instead"
                            ),
                        ));
                    }
                    return Ok(Expr {
                        kind: ExprKind::Project(Box::new(base), offset),
                        ty,
                        span: expr.span,
                        resource: None,
                    });
                }
                let (offset, ty) = self.field_offset(&base, name, expr.span)?;
                return Ok(Expr {
                    kind: ExprKind::Project(Box::new(base), offset),
                    ty,
                    span: expr.span,
                    resource: None,
                });
            }
            _ => {}
        }
        let value = self.expr(expr)?;
        if self.owned_type(value.ty) {
            return Err(Diagnostic::new(
                expr.span,
                "bind this owned value to a local before reading its fields",
            ));
        }
        Ok(value)
    }
    pub(super) fn field_offset(
        &self,
        base: &Expr,
        name: &str,
        span: Span,
    ) -> Result<(usize, Type)> {
        if base.ty.layout().is_none() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "field access requires a record value, found {}",
                    self.types.name(base.ty)
                ),
            ));
        }
        self.record_offset(base.ty, name, span)
    }
    /// Root local and field-index path of a record-field projection chain.
    /// Only direct local places have stable storage that both backends can pin
    /// for a live `DynArray` view; temporaries, calls, and reference
    /// projections deliberately have no root.
    /// Whether a field chain `a.b.c` starts at a direct local record binding
    /// (not a reference and not a temporary).
    pub(super) fn field_root_is_local_record(&self, expr: &ast::Expr) -> bool {
        let mut current = expr;
        while let ast::ExprKind::Field { value, .. } = &current.kind {
            if self.resolution.reference(current.span).is_some() {
                return false;
            }
            current = value;
        }
        matches!(current.kind, ast::ExprKind::Name(_))
            && self.slot(current.span).is_ok_and(|slot| {
                self.locals[slot]
                    .ty
                    .layout()
                    .is_some_and(|id| self.types.enums[id].record)
            })
    }
    /// A `DynArray` field place rooted at a record reference or a hoisted
    /// temporary record: the checked place, its element type, and the field
    /// index path from the root record (the referent for a reference root).
    /// `None` when the place is not a DynArray field, so the ordinary field
    /// path reports its own diagnostic.
    pub(super) fn indirect_dyn_field_place(
        &mut self,
        value: &ast::Expr,
        mutable: bool,
    ) -> Result<Option<(Expr, Type, Vec<usize>)>> {
        let place = self.checked_place(value, mutable)?;
        let Some((element, _)) = place
            .ty
            .layout()
            .and_then(|id| self.types.enums[id].dynamic_array)
        else {
            return Ok(None);
        };
        let mut path = Vec::new();
        let mut current = &place;
        let root = loop {
            match &current.kind {
                ExprKind::Project(base, offset) => {
                    let record = match base.ty {
                        Type::Ref(pointer) | Type::RefMut(pointer) => self.types.pointees[pointer],
                        ty => ty,
                    };
                    let Some(index) = self.field_index_at(record, *offset) else {
                        return Ok(None);
                    };
                    path.push(index);
                    current = base;
                }
                ExprKind::Peek(slot) | ExprKind::Local(slot) | ExprKind::InitOwner { slot, .. } => {
                    break (*slot, current.ty);
                }
                _ => return Ok(None),
            }
        };
        path.reverse();
        let (slot, root_ty) = root;
        if mutable {
            let writable = match root_ty {
                Type::RefMut(_) => true,
                Type::Ref(_) => false,
                _ => self.locals[slot].mutable,
            };
            if !writable {
                return Err(Diagnostic::new(
                    value.span,
                    "cannot create an exclusive '&mut [T]' view of a field behind a shared '&Record' reference; shared storage cannot be upgraded",
                ));
            }
        }
        if matches!(place.kind, ExprKind::Project(..)) {
            Ok(Some((place, element, path)))
        } else {
            Ok(None)
        }
    }
    /// The field index at a word offset of a record layout.
    pub(super) fn field_index_at(&self, ty: Type, offset: usize) -> Option<usize> {
        let id = ty.layout().filter(|id| self.types.enums[*id].record)?;
        let variant = &self.types.enums[id].variants[0];
        let mut at = self.types.enums[id].tag_words();
        for (index, field) in variant.fields.iter().enumerate() {
            if at == offset {
                return Some(index);
            }
            at += self.types.width(*field);
        }
        None
    }
    pub(super) fn projection_root(&self, expr: &Expr) -> Option<(usize, Vec<usize>)> {
        let mut path = Vec::new();
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::Project(base, offset) => {
                    let id = base.ty.layout().filter(|id| self.types.enums[*id].record)?;
                    let variant = &self.types.enums[id].variants[0];
                    let mut field_offset = self.types.enums[id].tag_words();
                    let mut index = None;
                    for (position, field) in variant.fields.iter().enumerate() {
                        if field_offset == *offset {
                            index = Some(position);
                            break;
                        }
                        field_offset += self.types.width(*field);
                    }
                    path.push(index?);
                    current = base;
                }
                ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                    if current
                        .ty
                        .layout()
                        .is_some_and(|id| self.types.enums[id].record) =>
                {
                    path.reverse();
                    return Some((*slot, path));
                }
                _ => return None,
            }
        }
    }
    /// FIELD-PRIVACY: a field without `pub` is visible only inside the module
    /// that declares its struct.
    pub(super) fn check_field_visible(
        &self,
        definition: BindingId,
        name: &str,
        span: Span,
    ) -> Result<()> {
        let unit = self.resolution.unit_of.get(&definition);
        if unit.is_none_or(|unit| *unit == self.unit) || self.types.field_public(definition, name) {
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            format!(
                "field '{name}' of '{}' is private to its module; mark it 'pub' or use the module's functions",
                self.resolution.bindings[definition].name
            ),
        ))
    }
    pub(super) fn check_layout_field_visible(
        &self,
        layout: usize,
        name: &str,
        span: Span,
    ) -> Result<()> {
        self.check_field_visible(self.types.enums[layout].definition, name, span)
    }
    pub(super) fn record_offset(&self, ty: Type, name: &str, span: Span) -> Result<(usize, Type)> {
        let Some(id) = ty.layout().filter(|id| self.types.enums[*id].record) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "field access requires a record value, found {}",
                    self.types.name(ty)
                ),
            ));
        };
        self.check_layout_field_visible(id, name, span)?;
        let variant = &self.types.enums[id].variants[0];
        let Some(index) = variant.names.iter().position(|n| n == name) else {
            return if self.types.enums[id].tuple {
                Err(Diagnostic::new(
                    span,
                    format!(
                        "tuple {} has no element '{name}' (elements: {})",
                        self.types.name(ty),
                        variant.names.join(", ")
                    ),
                ))
            } else {
                Err(Diagnostic::new(
                    span,
                    format!(
                        "record {} has no field '{name}' (fields: {})",
                        self.types.name(ty),
                        variant.names.join(", ")
                    ),
                ))
            };
        };
        let offset = self.types.enums[id].tag_words()
            + variant.fields[..index]
                .iter()
                .map(|t| self.types.width(*t))
                .sum::<usize>();
        Ok((offset, variant.fields[index]))
    }
    pub(super) fn field(
        &mut self,
        value: &ast::Expr,
        name: &str,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        // The base is only a step towards the field: an owning record may be
        // reached through a reference when the field read is copyable.
        let base = self.place_at(value, true)?;
        if base.ty.is_ref() {
            let pointer = base.ty.ref_pointee().expect("reference pointee");
            let pointee = self.types.pointees[pointer];
            let (offset, ty) = self.record_offset(pointee, name, span)?;
            if self.owned_type(ty)
                || self.linear_type(ty)
                || (ty.is_view() && ty.is_mut_slice())
                || matches!(ty, Type::RefMut(_))
                || ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
                || ty
                    .layout()
                    .is_some_and(|id| self.types.enums[id].mutable_borrow)
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "field '{name}' cannot be read through a record reference because it owns storage or contains a borrow; destructure an owning value instead"
                    ),
                ));
            }
            let projected = Expr {
                kind: ExprKind::Project(Box::new(base), offset),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(projected, expected, span),
                None => Ok(projected),
            };
        }
        self.project_field(base, name, span, expected)
    }
    /// Checked field projection from an already checked place. Shared by
    /// ordinary field access and callable-field method syntax so both reject
    /// owned, exclusive, and nested-exclusive projections identically.
    pub(super) fn project_field(
        &mut self,
        base: Expr,
        name: &str,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (offset, ty) = self.field_offset(&base, name, span)?;
        if ty.is_mut_slice() && !self.field_place {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project exclusive field '{name}' out of a record; destructure the record first, as in 'let R {{ {name}, .. }} = value;', or derive a subview with '&mut value.{name}[..]'"
                ),
            ));
        }
        if matches!(ty, Type::RefMut(_)) && !self.field_place {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project exclusive reference field '{name}' out of a record; destructure the record first, as in 'let R {{ {name}, .. }} = value;'"
                ),
            ));
        }
        if !self.field_place
            && ty
                .layout()
                .is_some_and(|id| self.types.enums[id].mutable_borrow)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project field '{name}' directly: it contains an exclusive '&mut [T]' field. Destructure the parent record first"
                ),
            ));
        }
        if self.owned_type(ty) {
            let record = self.types.name(base.ty);
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot move owned field '{name}' out of {record}; destructure the record instead: let {} {{ {name}: value }} = ...;",
                    record.split('<').next().unwrap_or(&record)
                ),
            ));
        }
        let value = Expr {
            kind: ExprKind::Project(Box::new(base), offset),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
}
