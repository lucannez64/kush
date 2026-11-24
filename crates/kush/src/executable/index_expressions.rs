//! Indexing of arrays, slices, vectors and text.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn index_expression(
        &mut self,
        expr: &ast::Expr,
        value: &Box<ast::Expr>,
        index: &Box<ast::Expr>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        {
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
                    kind: ExprKind::Call(Target::Slice(SliceOp::Get, element), vec![base, index]),
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
            let Some((element, length)) = base.ty.layout().and_then(|id| c.types.enums[id].array)
            else {
                return Err(Diagnostic::new(
                    span,
                    "index syntax requires an inline array or a &[T] slice view",
                ));
            };
            if let Some(position) =
                crate::length::eval_expr(c.resolution, c.logical, &c.consts, index)?
            {
                if position >= length {
                    return Err(Diagnostic::new(index.span, "array index out of bounds"));
                }
                if c.owned_type(element) {
                    return Err(Diagnostic::new(
                        span,
                        "indexing cannot copy owned or linear array elements; destructure or slice instead",
                    ));
                }
                let value = Expr {
                    kind: ExprKind::Project(Box::new(base), 1 + position * c.types.width(element)),
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
            let view =
                c.slice_from_expr(base, None, None, element, false, false, span, None, None)?;
            let index = c.expr_expected(index, Some(Type::I64))?;
            c.expect(index.ty, Type::I64, index.span)?;
            // ARRAY-INDEX-PROOF: an index the facts keep in `0..N` reads
            // without a check, as a proved vector access does.
            let length = i64::try_from(length).ok();
            let proved = match (length, c.facts.linear(&index)) {
                (Some(length), Some(position)) => c.try_prove(
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
                    &format!("0 <= index && index < {}", length),
                    span,
                ),
                _ => false,
            };
            let op = if proved {
                c.functions.bounds_proved += 1;
                c.record_check(
                    ObligationKind::Bounds {
                        container: Container::Array,
                        refined_length: length,
                    },
                    span,
                    "0 <= index && index < len".to_owned(),
                    true,
                );
                SliceOp::At
            } else {
                c.require(PANIC, span)?;
                c.functions.bounds_checked += 1;
                c.record_bounds(Container::Array, length, span);
                SliceOp::Get
            };
            let ty = if index.ty == Type::Never {
                Type::Never
            } else {
                element
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Slice(op, element), vec![view, index]),
                ty,
                span,
                resource: None,
            };
            match expected {
                Some(expected) => c.coerce(value, expected, span),
                None => Ok(value),
            }
        }
    }
}
