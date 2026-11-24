//! Grades, boxes, arenas, allocators and allocator-backed containers.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Reject grades that would duplicate or discard owning/linear storage.
    pub(super) fn validate_grade(
        &self,
        grade: Option<Grade>,
        ty: Type,
        span: Span,
        allow_affine_drop: bool,
    ) -> Result<()> {
        if !self.owned_type(ty) {
            return Ok(());
        }
        match grade {
            None => Ok(()),
            Some(grade) if grade.is_one() => Ok(()),
            Some(grade) if grade.is_zero() => {
                if self.linear_type(ty) {
                    Err(Diagnostic::new(
                        span,
                        format!(
                            "grade @[0] would silently discard the linear obligation of {}; consume it with grade @[1] or leave it ungraded",
                            self.types.name(ty)
                        ),
                    ))
                } else if allow_affine_drop {
                    // Affine owned storage may be initialized and dropped
                    // eagerly: the binding itself is not materialized, but the
                    // value is destroyed exactly once at the binding site.
                    Ok(())
                } else {
                    Err(Diagnostic::new(
                        span,
                        format!(
                            "grade @[0] would silently discard the owning/linear value {}; consume it with grade @[1] or leave it ungraded",
                            self.types.name(ty)
                        ),
                    ))
                }
            }
            Some(grade) if grade.is_many() => Err(Diagnostic::new(
                span,
                format!(
                    "grade 'many' allows duplication, but {} owns resources or is linear",
                    self.types.name(ty)
                ),
            )),
            Some(grade) => Err(Diagnostic::new(
                span,
                format!(
                    "grade @[{grade}] would duplicate the owning/linear value {}; owning and linear values support only @[1]",
                    self.types.name(ty)
                ),
            )),
        }
    }
    /// Checked unique-box reuse. The allocation comes from `owner`; the old
    /// affine payload is destroyed exactly once after both arguments have been
    /// evaluated, and the new payload is stored in the same storage. There is
    /// no allocating fallback and no implicit destruction of linear payloads.
    pub(super) fn box_reuse(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            return Ok(Expr {
                kind: ExprKind::BoxReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.reuse requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        let expected_inner = expected.and_then(|ty| {
            if let Type::Box(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::BoxReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse cannot store a borrowed reference or slice view (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        let payload = self.coerce(payload, new, span)?;
        let old_width = self.types.width(old);
        let new_width = self.types.width(new);
        if new_width > old_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse cannot store {} ({new_width} word(s)) in an allocation sized for {} ({old_width} word(s)); there is no allocating fallback. Allocate a new Box or reduce the payload layout",
                    self.types.name(new),
                    self.types.name(old)
                ),
            ));
        }
        let ty = Type::Box(self.types.pointer(new));
        let value = Expr {
            kind: ExprKind::BoxReuse {
                owner: Box::new(owner),
                payload: Box::new(payload),
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
    /// Checked widening reuse. This is the explicit allocating fallback: a
    /// payload wider than the old one may grow and move the allocation. It
    /// requires `{alloc, panic}` and is therefore illegal under `#[noalloc]`.
    /// The old payload is still destroyed exactly once before any new storage
    /// is written, and the returned owner keeps every obligation of the old
    /// owner and of the new payload.
    pub(super) fn box_reuse_grow(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            return Ok(Expr {
                kind: ExprKind::BoxReuseGrow {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.reuse_grow requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse_grow cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse_grow cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        self.require(ALLOC | PANIC, span)?;
        let expected_inner = expected.and_then(|ty| {
            if let Type::Box(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::BoxReuseGrow {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse_grow cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        let payload = self.coerce(payload, new, span)?;
        let ty = Type::Box(self.types.pointer(new));
        let value = Expr {
            kind: ExprKind::BoxReuseGrow {
                owner: Box::new(owner),
                payload: Box::new(payload),
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
    /// Fallible box construction. The payload is moved into the `Ok` box on
    /// success and returned unchanged in `Err` on failure, so no owner is
    /// destroyed or silently duplicated by a rejected allocation.
    pub(super) fn box_try_new(
        &mut self,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::Box(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let value = self.expr_expected(value, expected_inner)?;
        if value.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::BoxTryNew {
                    value: Box::new(value),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.try_new cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        let value = self.coerce(value, pointee, span)?;
        let ok = Type::Box(self.types.pointer(pointee));
        let (ty, shape) = self.types.result_type(ok, pointee, span)?;
        let expression = Expr {
            kind: ExprKind::BoxTryNew {
                value: Box::new(value),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Fallible growth-capable reuse. On allocation failure the old owner is
    /// returned untouched in `Err`. The new payload must be non-owning, so the
    /// failure path preserves every supplied owner exactly.
    pub(super) fn box_try_reuse(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            let shape = ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            };
            return Ok(Expr {
                kind: ExprKind::BoxTryReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.try_reuse requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.try_reuse cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.try_reuse cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        self.require(ALLOC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::Box(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::BoxTryReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.try_reuse cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        if self.owned_type(new) || self.linear_type(new) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.try_reuse requires a non-owning new payload so a failed allocation can preserve every supplied owner; {} owns resources. Use Box.reuse_grow for an aborting swap, or consume the owner first",
                    self.types.name(new)
                ),
            ));
        }
        let payload = self.coerce(payload, new, span)?;
        let ok = Type::Box(self.types.pointer(new));
        let error = Type::Box(self.types.pointer(old));
        let (ty, shape) = self.types.result_type(ok, error, span)?;
        let expression = Expr {
            kind: ExprKind::BoxTryReuse {
                owner: Box::new(owner),
                payload: Box::new(payload),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Fallible byte-buffer construction with an exact requested capacity.
    pub(super) fn bytes_try_with_capacity(
        &mut self,
        capacity: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC, span)?;
        let capacity = self.expr_expected(capacity, Some(Type::I64))?;
        self.expect(capacity.ty, Type::I64, capacity.span)?;
        let (ty, shape) = self.types.result_type(Type::Bytes, Type::I64, span)?;
        let expression = Expr {
            kind: ExprKind::BytesTryWithCapacity {
                capacity: Box::new(capacity),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Create one owning bump-allocator region.
    pub(super) fn arena_new(&mut self, span: Span) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        Ok(Expr {
            kind: ExprKind::ArenaNew,
            ty: Type::Arena,
            span,
            resource: None,
        })
    }
    /// Create a region with a user-defined chunk-sizing strategy.
    ///
    /// The strategy is a copyable noncapturing `fn(need, current) -> capacity`
    /// with the empty effect row. It is stored in the region as a code pointer,
    /// so no environment, borrow, or owning value can outlive the region. The
    /// strategy only chooses chunk capacity; arbitrary user-supplied
    /// allocator/deallocator callbacks remain outside this contract.
    pub(super) fn arena_new_with(&mut self, strategy: &ast::Expr, span: Span) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let strategy = self.expr(strategy)?;
        let Type::Fn(index) = strategy.ty else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Arena.with_strategy expects a noncapturing fn(i64, i64) -> i64 strategy, found {}",
                    self.types.name(strategy.ty)
                ),
            ));
        };
        let signature = self.types.function_types[index].clone();
        if signature.parameters.len() != 2
            || signature.parameters[0] != Type::I64
            || signature.parameters[1] != Type::I64
            || signature.result != Type::I64
            || signature.parameter_erased(0)
            || signature.parameter_erased(1)
            || signature.result_erased()
        {
            return Err(Diagnostic::new(
                span,
                "Arena.with_strategy expects an exact fn(i64, i64) -> i64 signature; graded parameters or results and other types are rejected",
            ));
        }
        if signature.effects != 0 {
            return Err(Diagnostic::new(
                span,
                "Arena.with_strategy requires a strategy with the empty effect row; a strategy that allocates, performs I/O, or suspends cannot run inside allocator bookkeeping (a panic in it aborts the process)",
            ));
        }
        Ok(Expr {
            kind: ExprKind::ArenaNewWith {
                strategy: Box::new(strategy),
            },
            ty: Type::Arena,
            span,
            resource: None,
        })
    }
    /// Check `Arena.alloc(&arena, value)`. The borrow keeps the arena value
    /// live for the duration of the call; the returned `ArenaBox` carries its
    /// own region reference, so dropping the arena binding does not invalidate
    /// it.
    pub(super) fn arena_alloc(
        &mut self,
        arena: &ast::Expr,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let expected_inner = expected.and_then(|ty| {
            if let Type::ArenaBox(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let pointer = self.types.pointer(Type::Arena);
        let arena = self.expr_expected(arena, Some(Type::Ref(pointer)))?;
        self.expect(arena.ty, Type::Ref(pointer), arena.span)?;
        let value = self.expr_expected(value, expected_inner)?;
        if value.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::ArenaAlloc {
                    arena: Box::new(arena),
                    value: Box::new(value),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "Arena.alloc cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Arena; join them in the scope that owns them",
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        if self.linear_type(pointee) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Arena.alloc cannot place the linear value {} in a region that destroys its contents implicitly; consume it inside the region scope instead",
                    self.types.name(pointee)
                ),
            ));
        }
        if self.value_moves_linear(&value) && self.owned_type(pointee) {
            return Err(Diagnostic::new(
                span,
                "Arena.alloc cannot store an owned payload that may carry a propagated linear obligation; consume it explicitly",
            ));
        }
        let value = self.coerce(value, pointee, span)?;
        let ty = Type::ArenaBox(self.types.pointer(pointee));
        let expression = Expr {
            kind: ExprKind::ArenaAlloc {
                arena: Box::new(arena),
                value: Box::new(value),
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Fallible arena allocation. A refused chunk request returns the untouched
    /// payload in `Err`; the region's references, chunks, and bump position are
    /// unchanged, so a later ordinary or fallible allocation can proceed.
    pub(super) fn arena_try_alloc(
        &mut self,
        arena: &ast::Expr,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::ArenaBox(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let pointer = self.types.pointer(Type::Arena);
        let arena = self.expr_expected(arena, Some(Type::Ref(pointer)))?;
        self.expect(arena.ty, Type::Ref(pointer), arena.span)?;
        let value = self.expr_expected(value, expected_inner)?;
        if value.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::ArenaTryAlloc {
                    arena: Box::new(arena),
                    value: Box::new(value),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "Arena.try_alloc cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Arena; join them in the scope that owns them",
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        if self.linear_type(pointee) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Arena.try_alloc cannot place the linear value {} in a region that destroys its contents implicitly; consume it inside the region scope instead",
                    self.types.name(pointee)
                ),
            ));
        }
        if self.value_moves_linear(&value) && self.owned_type(pointee) {
            return Err(Diagnostic::new(
                span,
                "Arena.try_alloc cannot store an owned payload that may carry a propagated linear obligation; consume it explicitly",
            ));
        }
        let value = self.coerce(value, pointee, span)?;
        let ok = Type::ArenaBox(self.types.pointer(pointee));
        let (ty, shape) = self.types.result_type(ok, pointee, span)?;
        let expression = Expr {
            kind: ExprKind::ArenaTryAlloc {
                arena: Box::new(arena),
                value: Box::new(value),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Read a copyable payload through `&ArenaBox<T>`. Ownership rejects
    /// copying an owning payload, exactly as for `Box.read`.
    pub(super) fn arena_box_read(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr_expected(value, None)?;
        let Type::Ref(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.read requires an immutable &ArenaBox<T>",
            ));
        };
        let Type::ArenaBox(inner) = self.types.pointees[index] else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.read requires an immutable &ArenaBox<T>, not another borrow type",
            ));
        };
        let ty = self.types.pointees[inner];
        Ok(Expr {
            kind: ExprKind::ArenaBoxRead(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Move the payload out of an owning `ArenaBox<T>`.
    pub(super) fn arena_box_take(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr(value)?;
        let Type::ArenaBox(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.take requires an owned ArenaBox<T>",
            ));
        };
        let ty = self.types.pointees[index];
        Ok(Expr {
            kind: ExprKind::ArenaBoxTake(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Check one allocator callback. Allocation must be a noncapturing
    /// `fn(i64) -> Bytes` whose body may allocate or panic; release must be a
    /// pure noncapturing `fn(Bytes) -> Unit`, because release also runs during
    /// implicit drop and therefore cannot acquire effects the surrounding
    /// scope did not declare.
    pub(super) fn allocator_callback(
        &mut self,
        value: &ast::Expr,
        allocation: bool,
        span: Span,
    ) -> Result<Expr> {
        let checked = self.expr(value)?;
        let Type::Fn(id) = checked.ty else {
            return Err(Diagnostic::new(
                span,
                if allocation {
                    "Allocator.new requires a noncapturing 'fn(i64) -> Bytes' allocation function"
                } else {
                    "Allocator.new requires a noncapturing 'fn(Bytes) -> Unit' release function"
                },
            ));
        };
        let signature = self.types.function_types[id].clone();
        let expected_parameters = if allocation {
            vec![Type::I64]
        } else {
            vec![Type::Bytes]
        };
        let expected_result = if allocation { Type::Bytes } else { Type::Unit };
        if signature.parameters != expected_parameters
            || signature.result != expected_result
            || signature.result_grade.is_some()
            || signature
                .parameter_grades
                .iter()
                .any(|grade| grade.is_some())
        {
            return Err(Diagnostic::new(
                span,
                if allocation {
                    "Allocator.new expects an exact noncapturing 'fn(bytes: i64) -> Bytes' allocation function; graded parameters/results and other types are rejected"
                } else {
                    "Allocator.new expects an exact noncapturing 'fn(block: Bytes) -> Unit' release function; graded parameters/results and other types are rejected"
                },
            ));
        }
        let allowed = if allocation { ALLOC | PANIC } else { 0 };
        if signature.effects & !allowed != 0 {
            return Err(Diagnostic::new(
                span,
                if allocation {
                    "Allocator.new allocation callbacks may only declare the 'alloc' effect"
                } else {
                    "Allocator.new release callbacks must have the empty effect row; release also runs during implicit drop, so it cannot allocate, perform I/O, or suspend (a panic in it aborts the process)"
                },
            ));
        }
        Ok(checked)
    }
    /// Check one optional realloc hook. It consumes the previous `Bytes` block
    /// and returns a block with at least `bytes` capacity. The callback may
    /// allocate or panic; a smaller returned block is a runtime panic, never a
    /// silent partial move, because the old block was already consumed.
    pub(super) fn allocator_realloc_callback(
        &mut self,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Expr> {
        let checked = self.expr(value)?;
        let Type::Fn(id) = checked.ty else {
            return Err(Diagnostic::new(
                span,
                "Allocator.with_realloc requires a noncapturing 'fn(Bytes, i64, i64) -> Bytes' growth function",
            ));
        };
        let signature = self.types.function_types[id].clone();
        if signature.parameters != vec![Type::Bytes, Type::I64, Type::I64]
            || signature.result != Type::Bytes
            || signature.result_grade.is_some()
            || signature
                .parameter_grades
                .iter()
                .any(|grade| grade.is_some())
        {
            return Err(Diagnostic::new(
                span,
                "Allocator.with_realloc expects an exact noncapturing 'fn(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes' growth function; graded parameters/results and other types are rejected",
            ));
        }
        if signature.effects & !(ALLOC | PANIC) != 0 {
            return Err(Diagnostic::new(
                span,
                "Allocator.with_realloc growth callbacks may only declare the 'alloc' effect",
            ));
        }
        Ok(checked)
    }
    /// Build a user-defined allocator value from an allocation function and a
    /// release function. The result is copyable: containers store their own
    /// copy of the pair, so moving or dropping the allocator binding can never
    /// leave an allocation without its release function. An optional growth
    /// hook is stored as a third code pointer; it owns nothing.
    pub(super) fn allocator_new(
        &mut self,
        alloc: &ast::Expr,
        free: &ast::Expr,
        realloc: Option<&ast::Expr>,
        span: Span,
    ) -> Result<Expr> {
        let alloc = self.allocator_callback(alloc, true, span)?;
        let free = self.allocator_callback(free, false, span)?;
        let realloc = realloc
            .map(|realloc| self.allocator_realloc_callback(realloc, span))
            .transpose()?
            .map(Box::new);
        Ok(Expr {
            kind: ExprKind::AllocatorNew {
                alloc: Box::new(alloc),
                free: Box::new(free),
                realloc,
            },
            ty: Type::Allocator,
            span,
            resource: None,
        })
    }
    /// The injected allocator-instance protocol trait binding.
    pub(super) fn allocator_protocol_binding(&self) -> Result<BindingId> {
        self.resolution
            .bindings
            .iter()
            .position(|binding| {
                binding.kind == BindingKind::Trait && binding.name == "AllocatorProtocol"
            })
            .ok_or_else(|| {
                Diagnostic::new(
                    Span::default(),
                    "internal error: the built-in AllocatorProtocol trait is not resolved",
                )
            })
    }
    /// Resolve and validate one `AllocatorProtocol` method for a concrete state
    /// type.
    pub(super) fn allocator_protocol_method(
        &mut self,
        trait_id: BindingId,
        state: Type,
        name: &str,
        expected: (&[Type], Type, u16),
        span: Span,
    ) -> Result<usize> {
        let definition = self.lookup_method(
            state,
            name,
            Some((trait_id, TraitArguments::default())),
            span,
        )?;
        self.check_method_visibility(definition, name, span)?;
        let index = self.functions.instance(
            self.types,
            self.resolution,
            definition.binding,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            definition.impl_arguments,
            Some(span),
        )?;
        let signature = self.functions.signatures[index].clone();
        let (parameters, result, effects) = expected;
        if signature.parameters != parameters
            || signature.result != result
            || signature.effects & !effects != 0
            || signature.result_grade.is_some()
            || signature
                .parameter_grades
                .iter()
                .any(|grade| grade.is_some())
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "allocator state type '{}' has an incompatible checked '{name}' method after specialization",
                    self.types.name(state)
                ),
            ));
        }
        Ok(index)
    }
    /// Check `AllocatorContext.new(instance)`. The instance is moved into the
    /// context, so the state must be an owned record with stable inline
    /// storage and no borrowed leaves. The three protocol methods are selected
    /// statically for that concrete type and validated before the context is
    /// constructed.
    pub(super) fn allocator_context_new(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        // Creating a context allocates compiler-owned metadata and a state
        // block, either of which can refuse through the ordinary panic path.
        self.require(ALLOC | PANIC, span)?;
        let value = self.expr(value)?;
        if value.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::AllocatorContextNew {
                    value: Box::new(value),
                    spec: usize::MAX,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let state = value.ty;
        if !state
            .layout()
            .is_some_and(|id| self.types.enums[id].record && !self.types.enums[id].borrowed)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "AllocatorContext.new requires an owned record instance with no borrowed fields, found {}",
                    self.types.name(state)
                ),
            ));
        }
        if crate::runtime_types::has_borrow(self.types, state)
            || crate::runtime_types::contains_task(self.types, state)
            || self.linear_type(state)
            || matches!(state, Type::AllocatorContext)
        {
            return Err(Diagnostic::new(
                span,
                "an allocator instance cannot contain borrowed leaves, task handles, linear obligations, or another allocator context",
            ));
        }
        let trait_id = self.allocator_protocol_binding()?;
        let pointer = self.types.pointer(state);
        let receiver = Type::RefMut(pointer);
        let alloc = self.allocator_protocol_method(
            trait_id,
            state,
            "alloc",
            (&[receiver, Type::I64], Type::Bytes, ALLOC | PANIC),
            span,
        )?;
        let free = self.allocator_protocol_method(
            trait_id,
            state,
            "free",
            (&[receiver, Type::Bytes], Type::Unit, 0),
            span,
        )?;
        let grow = self.allocator_protocol_method(
            trait_id,
            state,
            "grow",
            (
                &[receiver, Type::Bytes, Type::I64, Type::I64],
                Type::Bytes,
                ALLOC | PANIC,
            ),
            span,
        )?;
        let spec = AllocatorContextSpec {
            state,
            alloc,
            free,
            grow,
        };
        let spec_index = match self
            .functions
            .allocator_contexts
            .iter()
            .position(|existing| *existing == spec)
        {
            Some(index) => index,
            None => {
                self.functions.allocator_contexts.push(spec);
                self.functions.allocator_contexts.len() - 1
            }
        };
        Ok(Expr {
            kind: ExprKind::AllocatorContextNew {
                value: Box::new(value),
                spec: spec_index,
            },
            ty: Type::AllocatorContext,
            span,
            resource: None,
        })
    }
    /// Check `AllocatorContext.share(&context)`: one explicit additional
    /// reference. Contexts are affine, so this is the only way to hand the same
    /// instance to several containers.
    pub(super) fn allocator_context_share(
        &mut self,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Expr> {
        let value = self.expr(value)?;
        let Type::Ref(pointer) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "AllocatorContext.share requires an immutable &AllocatorContext",
            ));
        };
        if self.types.pointees[pointer] != Type::AllocatorContext {
            return Err(Diagnostic::new(
                span,
                "AllocatorContext.share requires an immutable &AllocatorContext",
            ));
        }
        Ok(Expr {
            kind: ExprKind::AllocatorContextShare(Box::new(value)),
            ty: Type::AllocatorContext,
            span,
            resource: None,
        })
    }
    /// Shared payload validation for allocator-backed storage. Linear values
    /// are rejected because the container must destroy remaining contents
    /// implicitly; borrowed values are rejected because the block is not a
    /// provenance-representing record.
    pub(super) fn allocator_payload(
        &mut self,
        value: ast::Expr,
        expected_inner: Option<Type>,
        operation: &str,
        span: Span,
    ) -> Result<(Expr, Type)> {
        let value = self.expr_expected(&value, expected_inner)?;
        if value.ty == Type::Never {
            let pointee = self.types.full(value.ty, span)?;
            return Ok((value, pointee));
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{operation} cannot store a borrowed reference, slice view, or borrowed record (including &str text views)"
                ),
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "task handles cannot be stored in {operation}; join them in the scope that owns them"
                ),
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        if self.linear_type(pointee) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{operation} cannot place the linear value {} in storage that destroys its contents implicitly; consume it explicitly",
                    self.types.name(pointee)
                ),
            ));
        }
        if self.value_moves_linear(&value) && self.owned_type(pointee) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{operation} cannot store an owned payload that may carry a propagated linear obligation; consume it explicitly"
                ),
            ));
        }
        let value = self.coerce(value, pointee, span)?;
        Ok((value, pointee))
    }
    /// Check an allocator operand accepted by the container constructors. Both
    /// the legacy copyable code-pointer value and an owning instance context
    /// are admitted; the container records whichever was supplied.
    pub(super) fn allocator_operand(&mut self, value: &ast::Expr, operation: &str) -> Result<Expr> {
        let value = self.expr(value)?;
        if matches!(value.ty, Type::Allocator | Type::AllocatorContext) {
            Ok(value)
        } else {
            Err(Diagnostic::new(
                value.span,
                format!(
                    "{operation} requires an Allocator or AllocatorContext value, found {}",
                    self.types.name(value.ty)
                ),
            ))
        }
    }
    /// Check `AllocBox.new(allocator, value)`.
    pub(super) fn alloc_box_new(
        &mut self,
        allocator: &ast::Expr,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let expected_inner = expected.and_then(|ty| {
            if let Type::AllocBox(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let allocator = self.allocator_operand(allocator, "AllocBox.new")?;
        let (value, pointee) =
            self.allocator_payload(value.clone(), expected_inner, "AllocBox.new", span)?;
        if value.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::AllocBoxNew {
                    allocator: Box::new(allocator),
                    value: Box::new(value),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let ty = Type::AllocBox(self.types.pointer(pointee));
        let expression = Expr {
            kind: ExprKind::AllocBoxNew {
                allocator: Box::new(allocator),
                value: Box::new(value),
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Check `AllocBox.try_new(allocator, value)`. A refused block returns the
    /// untouched payload in `Err`; the allocator value is copyable, so no part
    /// of the supplied state is lost on either path.
    pub(super) fn alloc_box_try_new(
        &mut self,
        allocator: &ast::Expr,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::AllocBox(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let allocator = self.allocator_operand(allocator, "AllocBox.try_new")?;
        let (value, pointee) =
            self.allocator_payload(value.clone(), expected_inner, "AllocBox.try_new", span)?;
        if value.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::AllocBoxTryNew {
                    allocator: Box::new(allocator),
                    value: Box::new(value),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let ok = Type::AllocBox(self.types.pointer(pointee));
        let (ty, shape) = self.types.result_type(ok, pointee, span)?;
        let expression = Expr {
            kind: ExprKind::AllocBoxTryNew {
                allocator: Box::new(allocator),
                value: Box::new(value),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Read a copyable payload through `&AllocBox<T>`.
    pub(super) fn alloc_box_read(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr(value)?;
        let Type::Ref(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "AllocBox.read requires an immutable &AllocBox<T>",
            ));
        };
        let Type::AllocBox(inner) = self.types.pointees[index] else {
            return Err(Diagnostic::new(
                span,
                "AllocBox.read requires an immutable &AllocBox<T>, not another borrow type",
            ));
        };
        let ty = self.types.pointees[inner];
        if self.owned_type(ty) || self.linear_type(ty) || ty.is_view() {
            return Err(Diagnostic::new(
                span,
                "AllocBox.read copies its payload; owning, linear, and view payloads need AllocBox.take",
            ));
        }
        Ok(Expr {
            kind: ExprKind::AllocBoxRead(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Move the payload out of an owning `AllocBox<T>`.
    pub(super) fn alloc_box_take(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr(value)?;
        let Type::AllocBox(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "AllocBox.take requires an owned AllocBox<T>",
            ));
        };
        let ty = self.types.pointees[index];
        Ok(Expr {
            kind: ExprKind::AllocBoxTake(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Check allocator-backed vector construction. The element type comes from
    /// the annotation, exactly like `Vec.new`/`Vec.with_capacity`.
    pub(super) fn alloc_vec_new(
        &mut self,
        allocator: &ast::Expr,
        capacity: Option<&ast::Expr>,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let element = expected.and_then(|ty| match ty {
            Type::AllocVec(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let Some(element) = element else {
            return Err(Diagnostic::new(
                span,
                "cannot infer the AllocVec element type; annotate the binding as AllocVec<T>",
            ));
        };
        if crate::runtime_types::has_borrow(self.types, element) {
            return Err(Diagnostic::new(
                span,
                "AllocVec cannot hold a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        let allocator = self.allocator_operand(allocator, "AllocVec.new")?;
        let capacity = match capacity {
            Some(capacity) => {
                let capacity = self.expr_expected(capacity, Some(Type::I64))?;
                self.expect(capacity.ty, Type::I64, capacity.span)?;
                Some(Box::new(capacity))
            }
            None => None,
        };
        Ok(Expr {
            kind: ExprKind::AllocVecNew {
                allocator: Box::new(allocator),
                capacity,
                element,
            },
            ty: Type::AllocVec(self.types.pointer(element)),
            span,
            resource: None,
        })
    }
    /// Check an `AllocVec` operation. `get`/`len` borrow; `push`/`try_push`/
    /// `pop`/`set`/`clear` consume the owning vector and return it.
    pub(super) fn alloc_vec_call(
        &mut self,
        name: &str,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let arity = match name {
            "AllocVec.len" | "AllocVec.clear" | "AllocVec.pop" => 1,
            "AllocVec.get" | "AllocVec.push" | "AllocVec.try_push" => 2,
            "AllocVec.set" => 3,
            _ => 0,
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} argument(s), found {}",
                    arguments.len()
                ),
            ));
        }
        let array = self.expr(&arguments[0])?;
        let element = match (name, array.ty) {
            ("AllocVec.len" | "AllocVec.get", Type::Ref(index)) => {
                match self.types.pointees[index] {
                    Type::AllocVec(pointer) => self.types.pointees[pointer],
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            format!("{name} requires a '&AllocVec<T>' borrow"),
                        ));
                    }
                }
            }
            (
                "AllocVec.clear" | "AllocVec.push" | "AllocVec.try_push" | "AllocVec.pop"
                | "AllocVec.set",
                Type::AllocVec(pointer),
            ) => self.types.pointees[pointer],
            (_, ty) => {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "{name} requires an AllocVec<T> value, found {}",
                        self.types.name(ty)
                    ),
                ));
            }
        };
        let operation = match name {
            "AllocVec.len" => AllocVecOp::Len,
            "AllocVec.get" => AllocVecOp::Get,
            "AllocVec.push" => AllocVecOp::Push,
            "AllocVec.try_push" => AllocVecOp::TryPush,
            "AllocVec.pop" => AllocVecOp::Pop,
            "AllocVec.set" => AllocVecOp::Set,
            _ => AllocVecOp::Clear,
        };
        if matches!(operation, AllocVecOp::Push | AllocVecOp::Clear) {
            self.require(ALLOC | PANIC, span)?;
        }
        if matches!(operation, AllocVecOp::TryPush) {
            // Refusal is checked, not a panic, but the allocation callback may
            // itself panic; the caller must declare the callback's effects.
            self.require(ALLOC | PANIC, span)?;
        }
        if matches!(operation, AllocVecOp::Get | AllocVecOp::Pop) {
            if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "{name} copies its element; owning, linear, and view elements need an explicit consuming operation"
                    ),
                ));
            }
            self.require(PANIC, span)?;
        }
        let mut values = vec![array];
        if matches!(operation, AllocVecOp::Get | AllocVecOp::Set) {
            let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
            self.expect(index.ty, Type::I64, index.span)?;
            values.push(index);
        }
        if matches!(
            operation,
            AllocVecOp::Push | AllocVecOp::TryPush | AllocVecOp::Set
        ) {
            let value_index = if operation == AllocVecOp::Set { 2 } else { 1 };
            let value = self.expr_expected(&arguments[value_index], Some(element))?;
            self.expect(value.ty, element, value.span)?;
            values.push(value);
        }
        let vector = Type::AllocVec(self.types.pointer(element));
        let ty = match operation {
            AllocVecOp::Len => Type::I64,
            AllocVecOp::Get => element,
            AllocVecOp::Push | AllocVecOp::Set | AllocVecOp::Clear => vector,
            AllocVecOp::Pop => self.types.tuple(vec![vector, element], span)?,
            AllocVecOp::TryPush => {
                let failure = self.types.tuple(vec![vector, element], span)?;
                self.types.result_type(vector, failure, span)?.0
            }
        };
        let value = Expr {
            kind: ExprKind::Call(Target::AllocVec(operation, element), values),
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
