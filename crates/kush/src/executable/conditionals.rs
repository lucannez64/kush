//! `if` and `match` expressions.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn if_expression(
        &mut self,
        expr: &ast::Expr,
        condition: &Box<ast::Expr>,
        then: &ast::Block,
        otherwise: &Option<Box<ast::Expr>>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        let (kind, ty) = {
            // Infer a branch join from its actual occurrences before
            // instantiating an outer call parameter. Coercing both arms
            // to an argument placeholder would erase their distinct
            // lifetime identities before the join can compare them.
            let expected = expected.filter(|ty| {
                !crate::runtime_types::borrow_lifetimes(c.types, *ty)
                    .iter()
                    .any(|label| label.starts_with("<argument "))
            });
            let branch_tail = std::mem::take(&mut c.branch_tail);
            let before = c.facts.version_stamp();
            let condition = c.expr(condition)?;
            c.expect(condition.ty, Type::Bool, condition.span)?;
            let unwritten = c.facts.same_stamp(&before);
            let baseline = c.facts.clone();
            let scalar_baseline = c.scalar_values.clone();
            let scalar_live = c.kernel_locals.len();
            if unwritten {
                c.facts.assume_unwritten(&condition, true);
            } else {
                c.facts.assume(&condition, true);
            }
            let has_else = otherwise.is_some();
            let then_expected = if has_else { expected } else { Some(Type::Unit) };
            c.ensures_tail = branch_tail && has_else;
            let then = c.block(then, then_expected);
            let then_facts = c.facts.clone();
            c.facts = baseline.clone();
            let then = then?;
            let then_scalars = c.scalar_values.clone();
            c.scalar_values = scalar_baseline.clone();
            let otherwise = if let Some(otherwise) = otherwise {
                if unwritten {
                    c.facts.assume_unwritten(&condition, false);
                } else {
                    c.facts.assume(&condition, false);
                }
                // With the call-argument expectation deferred above,
                // no fallback context may erase the arm's actual
                // labels either.
                let context = expected;
                c.ensures_tail = branch_tail;
                let tail = c.expr_expected_result(otherwise, context);

                let tail = tail?;
                let ty = tail.ty;
                Block {
                    statements: vec![],
                    tail: Some(Box::new(tail)),
                    ty,
                }
            } else {
                Block {
                    statements: vec![],
                    tail: None,
                    ty: Type::Unit,
                }
            };
            let otherwise_scalars = c.scalar_values.clone();
            // Only a branch that falls through reaches the join, so
            // a diverging branch's rewrites do not weaken the facts
            // after it (its opaque slots stay opaque: that set is
            // sticky and loop heads rely on it).
            if then.ty == Type::Never && otherwise.ty != Type::Never {
                c.facts.keep_opaque_of(&then_facts);
            } else if otherwise.ty == Type::Never && then.ty != Type::Never {
                let mut kept = then_facts;
                kept.keep_opaque_of(&c.facts);
                c.facts = kept;
            } else {
                c.facts = crate::facts::Facts::branch_join(&baseline, &then_facts, &c.facts);
            }
            c.join_scalars(
                &scalar_baseline,
                &then_scalars,
                &otherwise_scalars,
                scalar_live,
                then.ty == Type::Never,
                otherwise.ty == Type::Never,
            );
            let (then, otherwise, ty) = if has_else {
                if c.erased_result_context(expected)
                    && (then.ty == Type::Unit || otherwise.ty == Type::Unit)
                {
                    (
                        c.erase_block_value(then, span),
                        c.erase_block_value(otherwise, span),
                        Type::Unit,
                    )
                } else {
                    // Branch arms must not launder an invariant record
                    // lifetime through one another: the call or the
                    // surrounding context derives identities from
                    // these actual labels. If they disagree, the
                    // union's label-erased normalization would silently
                    // absorb one arm into the other.
                    check_branch_record_labels(c.types, then.ty, otherwise.ty, span)?;
                    let ty = c.join(then.ty, otherwise.ty, span)?;
                    let then = c.coerce_block(then, ty, span)?;
                    let otherwise = c.coerce_block(otherwise, ty, span)?;
                    (then, otherwise, ty)
                }
            } else {
                // An `if` without `else` is a statement: the taken
                // branch must produce Unit, never an implicit optional
                // union value.
                let then = c.coerce_block(then, Type::Unit, span)?;
                (then, otherwise, Type::Unit)
            };
            (ExprKind::If(Box::new(condition), then, otherwise), ty)
        };
        c.finish_expression(kind, ty, span, expected)
    }
}
