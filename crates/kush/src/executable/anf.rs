//! A-normal form for suspendable handled bodies (plan node E-EXPR).
//!
//! The checker turns every non-tail `perform` of a suspending handler into an
//! `ExprKind::Suspend` wherever it appears. Before ownership runs, this pass
//! moves each suspension point into statement position: a point nested in an
//! operand becomes `let t = Suspend(..);`, and every operand to its left is
//! evaluated into its own temporary first, so evaluation order is unchanged.
//! Control constructs (blocks, `if`, `match`, loops) keep their points inside
//! their own blocks; the lowering resumes into them structurally.
//!
//! Short-circuit operators become `if` so a perform on the right is skipped
//! exactly when the operator skips it. A `while` whose condition suspends
//! becomes `loop { let c = cond; if !c { break } body }`.
//!
//! The rewritten body is ordinary checked IR, so ownership and grades check
//! the temporaries like any other `let`.
use super::*;

/// Whether `expr` contains a suspension point of the region being normalized.
/// Nested suspendable bodies own their points and were normalized already.
pub(super) fn contains_suspend(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Suspend { .. } => true,
        ExprKind::Suspendable(_) => false,
        _ => {
            let mut found = false;
            expr.for_each_child(&mut |child| found |= contains_suspend(child));
            found
        }
    }
}

fn block_contains_suspend(block: &Block) -> bool {
    block.statements.iter().any(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => contains_suspend(value),
        Statement::Declare(_) => false,
    }) || block.tail.as_deref().is_some_and(contains_suspend)
}

fn placeholder(span: Span) -> Expr {
    Expr {
        kind: ExprKind::Constant(0),
        ty: Type::Unit,
        span,
        resource: None,
    }
}

fn unsupported(span: Span) -> Diagnostic {
    Diagnostic::new(
        span,
        "a non-tail 'perform' is not supported in this position; bind the operand to a local with 'let' first",
    )
}

impl Checker<'_, '_> {
    /// Normalize every statement of `block` so suspension points are whole
    /// statement values or sit inside control constructs.
    pub(super) fn anf_block(&mut self, block: &mut Block) -> Result<()> {
        if !block_contains_suspend(block) {
            return Ok(());
        }
        let statements = std::mem::take(&mut block.statements);
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            match statement {
                Statement::Let(slot, mut value) => {
                    self.anf_statement_value(&mut value, &mut out)?;
                    out.push(Statement::Let(slot, value));
                }
                Statement::Expr(mut value) => {
                    self.anf_statement_value(&mut value, &mut out)?;
                    out.push(Statement::Expr(value));
                }
                Statement::Declare(slot) => out.push(Statement::Declare(slot)),
            }
        }
        if let Some(tail) = block.tail.as_deref_mut() {
            self.anf_statement_value(tail, &mut out)?;
        }
        block.statements = out;
        Ok(())
    }

    /// Normalize the value of a statement (or block tail). The value may stay
    /// a suspension point or a control construct containing points.
    fn anf_statement_value(&mut self, expr: &mut Expr, out: &mut Vec<Statement>) -> Result<()> {
        if !contains_suspend(expr) {
            return Ok(());
        }
        self.short_circuit_to_if(expr);
        match &mut expr.kind {
            ExprKind::Suspend { call, .. } => self.anf_operands(call, out),
            ExprKind::Block(block) | ExprKind::Loop(block) => self.anf_block(block),
            ExprKind::If(condition, yes, no) => {
                self.anf_value(condition, out)?;
                self.anf_block(yes)?;
                self.anf_block(no)
            }
            ExprKind::Match(scrutinee, arms) => {
                self.anf_value(scrutinee, out)?;
                for arm in arms {
                    if let Some(guard) = &arm.guard
                        && contains_suspend(guard)
                    {
                        return Err(Diagnostic::new(
                            guard.span,
                            "a non-tail 'perform' cannot appear in a match guard; perform it in the arm body",
                        ));
                    }
                    if contains_suspend(&arm.body) {
                        let span = arm.body.span;
                        let ty = arm.body.ty;
                        let body = std::mem::replace(&mut arm.body, placeholder(span));
                        let mut block = match body.kind {
                            ExprKind::Block(block) => block,
                            _ => Block {
                                statements: vec![],
                                tail: Some(Box::new(body)),
                                ty,
                            },
                        };
                        self.anf_block(&mut block)?;
                        arm.body = Expr {
                            kind: ExprKind::Block(block),
                            ty,
                            span,
                            resource: None,
                        };
                    }
                }
                Ok(())
            }
            ExprKind::While(condition, _) if contains_suspend(condition) => {
                self.while_to_loop(expr)?;
                self.anf_statement_value(expr, out)
            }
            ExprKind::While(_, body) => self.anf_block(body),
            _ => self.anf_operands(expr, out),
        }
    }

    /// Normalize an operand so it contains no suspension point at all: points
    /// and suspending control constructs are hoisted into temporaries.
    fn anf_value(&mut self, expr: &mut Expr, out: &mut Vec<Statement>) -> Result<()> {
        if !contains_suspend(expr) {
            return Ok(());
        }
        self.short_circuit_to_if(expr);
        match &expr.kind {
            ExprKind::Suspend { .. }
            | ExprKind::Block(_)
            | ExprKind::Loop(_)
            | ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::While(..) => {
                self.anf_statement_value(expr, out)?;
                self.hoist(expr, out)
            }
            _ => self.anf_operands(expr, out),
        }
    }

    /// Hoist the operands of a value node: every operand left of the last one
    /// that suspends is evaluated into a temporary first.
    fn anf_operands(&mut self, expr: &mut Expr, out: &mut Vec<Statement>) -> Result<()> {
        let span = expr.span;
        let operands: Vec<&mut Expr> = match &mut expr.kind {
            ExprKind::Binary(op, left, right) if !matches!(op, Kind::AmpAmp | Kind::PipePipe) => {
                vec![left, right]
            }
            ExprKind::StructEq { left, right, .. } => vec![left, right],
            ExprKind::Unary(_, value)
            | ExprKind::Coerce { value, .. }
            | ExprKind::Return(value)
            | ExprKind::Try { value, .. }
            | ExprKind::Project(value, _)
            | ExprKind::Assign(_, value)
            | ExprKind::Break(Some(value), _)
            | ExprKind::Drop(value)
            | ExprKind::BoxNew(value) => vec![value],
            ExprKind::Call(_, arguments)
            | ExprKind::Construct {
                fields: arguments, ..
            } => arguments.iter_mut().collect(),
            ExprKind::CallIndirect { callee, arguments } => {
                let mut operands = vec![callee.as_mut()];
                operands.extend(arguments.iter_mut());
                operands
            }
            _ => return Err(unsupported(span)),
        };
        let Some(last) = operands
            .iter()
            .rposition(|operand| contains_suspend(operand))
        else {
            return Ok(());
        };
        for (index, operand) in operands.into_iter().enumerate() {
            if index < last {
                if matches!(
                    operand.kind,
                    ExprKind::Constant(_) | ExprKind::Erased(_) | ExprKind::Peek(_)
                ) {
                    continue;
                }
                self.anf_value(operand, out)?;
                self.hoist(operand, out)?;
            } else if index == last {
                self.anf_value(operand, out)?;
            }
        }
        Ok(())
    }

    /// Replace `expr` by a fresh immutable local initialized just before.
    fn hoist(&mut self, expr: &mut Expr, out: &mut Vec<Statement>) -> Result<()> {
        let span = expr.span;
        let ty = expr.ty;
        let slot = self.fresh_local(span, ty)?;
        let value = std::mem::replace(
            expr,
            Expr {
                kind: ExprKind::Local(slot),
                ty,
                span,
                resource: None,
            },
        );
        out.push(Statement::Let(slot, value));
        Ok(())
    }

    /// `a && b` becomes `if a { b } else { false }` and `a || b` becomes
    /// `if a { true } else { b }` when `b` suspends, so the point is skipped
    /// exactly when the operator skips it.
    fn short_circuit_to_if(&mut self, expr: &mut Expr) {
        let ExprKind::Binary(op @ (Kind::AmpAmp | Kind::PipePipe), _, right) = &expr.kind else {
            return;
        };
        if !contains_suspend(right) {
            return;
        }
        let and = *op == Kind::AmpAmp;
        let span = expr.span;
        let ExprKind::Binary(_, left, right) =
            std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
        else {
            unreachable!("matched above")
        };
        let constant = |value: bool| Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::Constant(i64::from(value)),
                ty: Type::Bool,
                span,
                resource: None,
            })),
            ty: Type::Bool,
        };
        let evaluated = Block {
            statements: vec![],
            tail: Some(right),
            ty: Type::Bool,
        };
        let (yes, no) = if and {
            (evaluated, constant(false))
        } else {
            (constant(true), evaluated)
        };
        expr.kind = ExprKind::If(left, yes, no);
    }

    /// `while c { body }` becomes `loop { let t = c; if !t { break } body }`;
    /// `continue` still re-evaluates the condition at the loop head.
    fn while_to_loop(&mut self, expr: &mut Expr) -> Result<()> {
        let span = expr.span;
        let ExprKind::While(condition, body) =
            std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
        else {
            unreachable!("caller matched a while loop")
        };
        let test = self.fresh_local(span, Type::Bool)?;
        let local = Expr {
            kind: ExprKind::Local(test),
            ty: Type::Bool,
            span,
            resource: None,
        };
        let not = Expr {
            kind: ExprKind::Unary(Kind::Bang, Box::new(local)),
            ty: Type::Bool,
            span,
            resource: None,
        };
        let exit = Expr {
            kind: ExprKind::If(
                Box::new(not),
                Block {
                    statements: vec![],
                    tail: Some(Box::new(Expr {
                        kind: ExprKind::Break(None, vec![]),
                        ty: Type::Never,
                        span,
                        resource: None,
                    })),
                    ty: Type::Never,
                },
                Block {
                    statements: vec![],
                    tail: None,
                    ty: Type::Unit,
                },
            ),
            ty: Type::Unit,
            span,
            resource: None,
        };
        let mut statements = vec![Statement::Let(test, *condition), Statement::Expr(exit)];
        statements.extend(body.statements);
        if let Some(tail) = body.tail {
            statements.push(Statement::Expr(*tail));
        }
        expr.kind = ExprKind::Loop(Block {
            statements,
            tail: None,
            ty: Type::Unit,
        });
        expr.ty = Type::Unit;
        Ok(())
    }
}
