//! Array literals.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;
use crate::lexer::Kind;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn array_expression(
        &mut self,
        expr: &ast::Expr,
        values: &Vec<ast::Expr>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        {
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
                        return Err(first_error
                            .expect("an array literal candidate always attempts one element"));
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
                    kind: ExprKind::DynArrayNew { element, capacity },
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
            c.vec_literal(values, span, expected)
        }
    }
}
