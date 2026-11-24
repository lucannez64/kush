//! Binary operators: arithmetic, comparisons, logic and shifts.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;
use crate::lexer::Kind;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn binary_expression(
        &mut self,
        expr: &ast::Expr,
        op: &Kind,
        left_ast: &Box<ast::Expr>,
        right_ast: &Box<ast::Expr>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        let (kind, ty) = {
            let arithmetic = matches!(
                op,
                Kind::Plus
                    | Kind::Minus
                    | Kind::Star
                    | Kind::Slash
                    | Kind::Percent
                    | Kind::Amp
                    | Kind::Pipe
                    | Kind::Caret
            );
            let compares = matches!(
                op,
                Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne
            );
            let hint = if arithmetic || matches!(op, Kind::Shl | Kind::Shr) {
                expected.filter(|t| t.int_kind().is_some() || t.float_kind().is_some())
            } else {
                None
            };
            // A literal takes its type from the other operand, so
            // `x + 1.5` and `0.5 < x` work for both float widths. A
            // literal operand is pure, so checking the other side first
            // does not change evaluation order.
            let literal = is_int_literal(left_ast) || is_float_literal(left_ast);
            let other_literal = is_int_literal(right_ast) || is_float_literal(right_ast);
            let (left, right) = if (arithmetic || compares) && literal && !other_literal {
                let right = c.expr_expected(right_ast, hint)?;
                let left = c.expr_expected(
                    left_ast,
                    right
                        .ty
                        .int_kind()
                        .map(Type::int)
                        .or_else(|| right.ty.float_kind().map(Type::float))
                        .or(hint),
                )?;
                (left, right)
            } else {
                let left = c.expr_expected(left_ast, hint)?;
                // The right operand of && / || runs only when the left is true / false.
                let mark = c.facts.mark();
                let logical = matches!(op, Kind::AmpAmp | Kind::PipePipe);
                // Taken before the right operand can bump versions.
                let not_ran = logical
                    .then(|| c.facts.formula(&left, *op != Kind::AmpAmp))
                    .flatten();
                if logical {
                    c.facts.assume(&left, *op == Kind::AmpAmp);
                }
                let inner = c.facts.mark();
                let right_hint = if arithmetic || compares {
                    left.ty
                        .int_kind()
                        .map(Type::int)
                        .or_else(|| left.ty.float_kind().map(Type::float))
                } else {
                    None
                };
                let right = c.expr_expected(right_ast, right_hint);
                if logical {
                    // What the right operand taught (a call's
                    // postconditions) holds whenever it ran.
                    c.facts.reset_guarded(mark, inner, not_ran);
                } else {
                    c.facts.reset(mark);
                }
                (left, right?)
            };
            if matches!(op, Kind::EqEq | Kind::Ne)
                && left.ty == right.ty
                && let Some((element, capacity)) = left
                    .ty
                    .layout()
                    .and_then(|id| c.types.enums[id].dynamic_array)
            {
                if c.owned_type(element) || c.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray equality reads elements; owning, linear, and view elements are not comparable",
                    ));
                }
                if !matches!(
                    element,
                    Type::I64 | Type::Int(_) | Type::Float(_) | Type::Bool | Type::Char
                ) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "DynArray equality requires comparable one-word elements, found {}",
                            c.types.name(element)
                        ),
                    ));
                }
                let ty = if left.ty == Type::Never || right.ty == Type::Never {
                    Type::Never
                } else {
                    Type::Bool
                };
                return Ok(Expr {
                    kind: ExprKind::DynArrayEqual {
                        left: Box::new(left),
                        right: Box::new(right),
                        element,
                        capacity,
                        negate: *op == Kind::Ne,
                    },
                    ty,
                    span,
                    resource: None,
                });
            }
            let mut unchecked = false;
            let ty = match op {
                Kind::Plus
                | Kind::Minus
                | Kind::Star
                | Kind::Slash
                | Kind::Percent
                | Kind::Amp
                | Kind::Pipe
                | Kind::Caret => {
                    if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                        if !matches!(
                            op,
                            Kind::Plus | Kind::Minus | Kind::Star | Kind::Slash | Kind::Percent
                        ) {
                            return Err(Diagnostic::new(
                                span,
                                "floating-point values support +, -, *, /, %, comparisons, and unary -, but not bitwise operators",
                            ));
                        }
                        c.same_float(left.ty, right.ty, span)?
                    } else {
                        let ty = c.same_int(left.ty, right.ty, span)?;
                        if !matches!(op, Kind::Amp | Kind::Pipe | Kind::Caret) {
                            // OVERFLOW-ELIDE: a result the facts keep
                            // in range needs no runtime check.
                            let proved = if matches!(op, Kind::Plus | Kind::Minus | Kind::Star)
                                && ty != Type::Never
                            {
                                c.facts.in_range(op, &left, &right, ty, span)
                            } else {
                                None
                            };
                            match proved {
                                Some(certificates) => {
                                    c.functions.certificates.extend(certificates);
                                    unchecked = true;
                                    let goal = format!(
                                        "the result of {} stays in {}",
                                        op_text(op),
                                        c.types.name(ty)
                                    );
                                    c.record_check(ObligationKind::Overflow, span, goal, true);
                                }
                                None => {
                                    c.require(PANIC, span)?;
                                    let (kind, goal) = if matches!(op, Kind::Slash | Kind::Percent)
                                    {
                                        (
                                            ObligationKind::Division,
                                            "the divisor is not zero and the quotient fits"
                                                .to_owned(),
                                        )
                                    } else {
                                        (
                                            ObligationKind::Overflow,
                                            format!(
                                                "the result of {} stays in {}",
                                                op_text(op),
                                                c.types.name(ty)
                                            ),
                                        )
                                    };
                                    c.record_obligation(kind, span, goal);
                                }
                            }
                        }
                        ty
                    }
                }
                Kind::Shl | Kind::Shr => {
                    if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                        return Err(Diagnostic::new(
                            span,
                            "floating-point values support +, -, *, /, %, comparisons, and unary -, but not shifts",
                        ));
                    }
                    let ty = c.same_int(left.ty, left.ty, span)?;
                    c.same_int(right.ty, right.ty, right_ast.span)?;
                    let goal = format!(
                        "the shift amount is below the width of {}",
                        c.types.name(ty)
                    );
                    // SHIFT-ELIDE: an amount the facts keep in
                    // 0..bits needs no runtime check.
                    let bits = ty.int_kind().map(|kind| kind.bits());
                    let proved = match bits {
                        Some(bits) if ty != Type::Never && right.ty != Type::Never => {
                            c.facts.shift_amount(&right, bits, span)
                        }
                        _ => None,
                    };
                    match proved {
                        Some(certificates) => {
                            c.functions.certificates.extend(certificates);
                            unchecked = true;
                            c.record_check(ObligationKind::Shift, span, goal, true);
                        }
                        None => {
                            c.require(PANIC, span)?;
                            c.record_obligation(ObligationKind::Shift, span, goal);
                        }
                    }
                    ty
                }
                Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => {
                    if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                        c.same_float(left.ty, right.ty, span)?;
                    } else if left.ty == Type::Char || right.ty == Type::Char {
                        c.expect(left.ty, Type::Char, span)?;
                        c.expect(right.ty, Type::Char, span)?;
                    } else {
                        c.same_int(left.ty, right.ty, span)?;
                    }
                    Type::Bool
                }
                Kind::EqEq | Kind::Ne => {
                    if left.ty.layout().is_some()
                        && right.ty.layout().is_some()
                        && c.types.is_structural(left.ty)
                        && c.types.is_structural(right.ty)
                    {
                        if left.ty != right.ty {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "structural equality operands must have the same canonical row, found {} and {}",
                                    c.types.name(left.ty),
                                    c.types.name(right.ty)
                                ),
                            ));
                        }
                        if !c.structurally_comparable(left.ty) {
                            return Err(Diagnostic::new(
                                span,
                                "structural equality requires copyable scalar fields (integers, Char, Bool, Unit) or nested structural records of them; owning, borrowed, union, callable, nominal, and floating-point fields are not comparable",
                            ));
                        }
                        return Ok(Expr {
                            kind: ExprKind::StructEq {
                                left: Box::new(left),
                                right: Box::new(right),
                                negated: *op == Kind::Ne,
                            },
                            ty: Type::Bool,
                            span,
                            resource: None,
                        });
                    }
                    let opaque = |t: Type| {
                        t.layout().is_some()
                            || t.is_union()
                            || matches!(
                                t,
                                Type::Box(_)
                                    | Type::Bytes
                                    | Type::String
                                    | Type::Stdin
                                    | Type::Stdout
                                    | Type::Ref(_)
                                    | Type::RefMut(_)
                                    | Type::Vec(_)
                                    | Type::Slice(_)
                                    | Type::SliceMut(_)
                                    | Type::Task(_)
                                    | Type::Thread(_)
                            )
                    };
                    if opaque(left.ty) || opaque(right.ty) {
                        return Err(Diagnostic::new(
                            span,
                            "enum equality and opaque-handle equality are not supported; union values must be narrowed with a match first. Equality requires integers, floats, Char, Bool, or Unit",
                        ));
                    }
                    if left.ty != Type::Never && right.ty != Type::Never && left.ty != right.ty {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "equality operands must have the same type, found {} and {}",
                                c.types.name(left.ty),
                                c.types.name(right.ty)
                            ),
                        ));
                    }
                    Type::Bool
                }
                Kind::AmpAmp | Kind::PipePipe => {
                    c.expect(left.ty, Type::Bool, span)?;
                    c.expect(right.ty, Type::Bool, span)?;
                    Type::Bool
                }
                _ => return Err(Diagnostic::new(span, "unsupported executable operator")),
            };
            let ty = if left.ty == Type::Never
                || (right.ty == Type::Never && !matches!(op, Kind::AmpAmp | Kind::PipePipe))
            {
                Type::Never
            } else {
                ty
            };
            if unchecked && ty != Type::Never {
                let kind = ty.int_kind().unwrap_or(crate::int::IntKind::I64);
                let int_op = match op {
                    Kind::Plus => crate::int::IntOp::Unchecked(crate::int::ArithOp::Add),
                    Kind::Minus => crate::int::IntOp::Unchecked(crate::int::ArithOp::Sub),
                    Kind::Shl => crate::int::IntOp::UncheckedShift(crate::int::Shift::Left),
                    Kind::Shr => crate::int::IntOp::UncheckedShift(crate::int::Shift::Right),
                    _ => crate::int::IntOp::Unchecked(crate::int::ArithOp::Mul),
                };
                (
                    ExprKind::Call(Target::Int(int_op, kind, kind), vec![left, right]),
                    ty,
                )
            } else {
                (
                    ExprKind::Binary(op.clone(), Box::new(left), Box::new(right)),
                    ty,
                )
            }
        };
        c.finish_expression(kind, ty, span, expected)
    }
}
