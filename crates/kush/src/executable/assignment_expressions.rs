//! Assignments: to locals, fields, references and indexed places.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;
use crate::lexer::Kind;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn assignment_expression(
        &mut self,
        expr: &ast::Expr,
        left: &Box<ast::Expr>,
        right: &Box<ast::Expr>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        let (kind, ty) = {
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
            } else if matches!(left.kind, ast::ExprKind::Field { .. }) && c.is_place(left) {
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
            } else if let ast::ExprKind::Index { value: base, index } = &left.kind {
                return c.index_assign(base, index, right, span);
            } else if let ast::ExprKind::Unary {
                op: Kind::Star,
                operand,
                ..
            } = &left.kind
            {
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
        };
        c.finish_expression(kind, ty, span, expected)
    }
}
