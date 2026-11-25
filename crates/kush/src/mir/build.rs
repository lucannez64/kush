//! Lower one checked function to a [`Body`].
//!
//! Coverage grows node by node (docs/mir-design.md section 6). Today the
//! builder takes functions whose locals and values are one-word scalars
//! (integers, floats, `char`, `bool`, `()`), with arithmetic, assignments,
//! `if`, `match` on literals, loops, direct calls, `print` of integers and
//! `panic`. Anything else is reported by name, and native code generation
//! then lowers that function from the tree.

use super::*;
use crate::executable::{Expr, ExprKind, Function, Pattern, Target};
use crate::executable::Statement as TreeStatement;

pub(crate) fn build(program: &Executable, index: usize) -> Result<Body, String> {
    let function = &program.functions[index];
    eligible(function)?;
    let mut builder = Builder {
        program,
        locals: function
            .locals
            .iter()
            .map(|local| LocalDecl {
                ty: local.ty,
                mutable: local.mutable,
                temporary: false,
            })
            .collect(),
        blocks: Vec::new(),
        current: None,
        loops: Vec::new(),
    };
    let entry = builder.new_block();
    builder.current = Some(entry);
    if let Some(value) = builder.block(&function.body)? {
        let span = function.body.tail.as_ref().map_or(function.span, |tail| tail.span);
        builder.terminate(TerminatorKind::Return(value), span);
    }
    let blocks = builder
        .blocks
        .into_iter()
        .enumerate()
        .map(|(index, block)| {
            let terminator = block
                .terminator
                .ok_or_else(|| format!("internal: bb{index} has no terminator"))?;
            Ok(BasicBlock {
                statements: block.statements,
                terminator,
                unwind: None,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Body {
        name: function.name.clone(),
        parameters: function.parameters,
        locals: builder.locals,
        blocks,
        result: function.result,
    })
}

/// A one-word value with no ownership: the types the builder covers.
fn scalar(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64
            | Type::Int(_)
            | Type::Float(_)
            | Type::Char
            | Type::Bool
            | Type::Unit
            | Type::Never
    )
}

fn erased(grade: Option<crate::grades::Grade>) -> bool {
    grade.is_some_and(crate::grades::Grade::is_zero)
}

/// The function's frame and calling convention are ones the builder covers.
fn eligible(function: &Function) -> Result<(), String> {
    if function.closure.is_some() || !function.capture_refs.is_empty() {
        return Err("a closure".into());
    }
    if function.parameter_slots.is_some() || function.shared_environment {
        return Err("a continuation".into());
    }
    if !function.capability_parameters.is_empty() {
        return Err("a capability parameter".into());
    }
    if erased(function.result_grade) || function.parameter_grades.iter().any(|g| erased(*g)) {
        return Err("an erased parameter or result".into());
    }
    if !scalar(function.result) {
        return Err(format!("a {:?} result", function.result));
    }
    for (slot, local) in function.locals.iter().enumerate() {
        if !scalar(local.ty) {
            return Err(format!("a local of type {:?}", local.ty));
        }
        if local.pinned {
            return Err("a local whose address is taken".into());
        }
        if erased(local.grade) {
            return Err("an erased local".into());
        }
        if function.local_resources.get(slot).copied().flatten().is_some() {
            return Err("a local that owns a resource".into());
        }
    }
    Ok(())
}

/// A callee the builder may call directly: its arguments and result are
/// passed as plain words.
fn callable(program: &Executable, index: usize) -> Result<(), String> {
    let callee = &program.functions[index];
    if callee.closure.is_some() || callee.parameter_slots.is_some() {
        return Err("a call to a closure or continuation".into());
    }
    if erased(callee.result_grade) || callee.parameter_grades.iter().any(|g| erased(*g)) {
        return Err("a call with an erased parameter or result".into());
    }
    if !scalar(callee.result) {
        return Err(format!("a call returning {:?}", callee.result));
    }
    if callee.locals[..callee.parameters]
        .iter()
        .any(|local| !scalar(local.ty))
    {
        return Err("a call with a non-scalar parameter".into());
    }
    Ok(())
}

/// An expression whose evaluation cannot assign a local.
fn leaf(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Constant(_) | ExprKind::Local(_) | ExprKind::Peek(_) | ExprKind::Move(_)
    )
}

struct Partial {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

struct Loop {
    head: BlockId,
    /// Created by the first `break`.
    exit: Option<BlockId>,
    /// Receives the value of `break value`.
    result: Option<LocalId>,
}

struct Builder<'a> {
    program: &'a Executable,
    locals: Vec<LocalDecl>,
    blocks: Vec<Partial>,
    /// The block being filled; `None` after a terminator, until the next
    /// block is entered (code after `return` or `break` is unreachable).
    current: Option<BlockId>,
    loops: Vec<Loop>,
}

impl Builder<'_> {
    fn new_block(&mut self) -> BlockId {
        self.blocks.push(Partial {
            statements: Vec::new(),
            terminator: None,
        });
        self.blocks.len() - 1
    }
    fn enter(&mut self, block: BlockId) {
        debug_assert!(self.current.is_none());
        self.current = Some(block);
    }
    fn temp(&mut self, ty: Type) -> LocalId {
        self.locals.push(LocalDecl {
            ty,
            mutable: false,
            temporary: true,
        });
        self.locals.len() - 1
    }
    fn assign(&mut self, local: LocalId, rvalue: Rvalue, span: Span) {
        let block = self.current.expect("an assignment in reachable code");
        self.blocks[block].statements.push(Statement {
            kind: StatementKind::Assign(local, rvalue),
            span,
        });
    }
    fn terminate(&mut self, kind: TerminatorKind, span: Span) {
        let block = self.current.take().expect("a terminator in reachable code");
        self.blocks[block].terminator = Some(Terminator { kind, span });
    }
    fn goto(&mut self, target: BlockId, span: Span) {
        self.terminate(TerminatorKind::Goto(target), span);
    }
    /// Jump to a join block, creating it on first use.
    fn goto_join(&mut self, join: &mut Option<BlockId>, span: Span) {
        let target = *join.get_or_insert_with(|| {
            self.blocks.push(Partial {
                statements: Vec::new(),
                terminator: None,
            });
            self.blocks.len() - 1
        });
        self.goto(target, span);
    }
    /// The value of a unit or never-typed expression, which has no storage.
    fn no_value(ty: Type) -> Operand {
        Operand::Constant(0, ty)
    }
    /// A temporary for an expression's result, unless it has no storage.
    fn result_temp(&mut self, ty: Type) -> Option<LocalId> {
        (!matches!(ty, Type::Unit | Type::Never)).then(|| self.temp(ty))
    }
    fn result(temp: Option<LocalId>, ty: Type) -> Operand {
        temp.map_or_else(|| Self::no_value(ty), Operand::Move)
    }

    fn block(&mut self, block: &crate::executable::Block) -> Result<Option<Operand>, String> {
        for statement in &block.statements {
            match statement {
                TreeStatement::Let(slot, expr) => {
                    let Some(value) = self.expr(expr)? else {
                        return Ok(None);
                    };
                    self.assign(*slot, Rvalue::Use(value), expr.span);
                }
                TreeStatement::Declare(_) => return Err("a temporary owner".into()),
                TreeStatement::Expr(expr) => {
                    if self.expr(expr)?.is_none() {
                        return Ok(None);
                    }
                }
            }
        }
        match &block.tail {
            Some(tail) => self.expr(tail),
            None => Ok(Some(Self::no_value(Type::Unit))),
        }
    }

    /// Lower expressions evaluated left to right. A value read from a
    /// source local is copied to a temporary when a later expression could
    /// assign that local first.
    fn operands(&mut self, exprs: &[&Expr]) -> Result<Option<Vec<Operand>>, String> {
        let mut values = Vec::with_capacity(exprs.len());
        for (index, expr) in exprs.iter().enumerate() {
            let Some(value) = self.expr(expr)? else {
                return Ok(None);
            };
            let exposed = match value {
                Operand::Copy(local) | Operand::Move(local) => !self.locals[local].temporary,
                Operand::Constant(..) => false,
            };
            let value = if exposed && exprs[index + 1..].iter().any(|later| !leaf(later)) {
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Use(value), expr.span);
                Operand::Move(temp)
            } else {
                value
            };
            values.push(value);
        }
        Ok(Some(values))
    }

    fn expr(&mut self, expr: &Expr) -> Result<Option<Operand>, String> {
        if expr.resource.is_some() {
            return Err("an owned resource".into());
        }
        if !scalar(expr.ty) {
            return Err(format!("a value of type {:?}", expr.ty));
        }
        let span = expr.span;
        Ok(Some(match &expr.kind {
            ExprKind::Constant(value) => Operand::Constant(*value, expr.ty),
            ExprKind::Local(slot) | ExprKind::Peek(slot) => Operand::Copy(*slot),
            ExprKind::Move(slot) => Operand::Move(*slot),
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Unary(op, operand) => {
                let op = UnOp::from_kind(op).ok_or("an unknown unary operator")?;
                let Some(value) = self.expr(operand)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Unary(op, value), span);
                Operand::Move(temp)
            }
            ExprKind::Binary(op @ (Kind::AmpAmp | Kind::PipePipe), left, right) => {
                return self.short_circuit(op, left, right, span);
            }
            ExprKind::Binary(op, left, right) => {
                let op = BinOp::from_kind(op).ok_or("an unknown binary operator")?;
                let Some(values) = self.operands(&[left, right])? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Binary(op, values[0], values[1]), span);
                Operand::Move(temp)
            }
            ExprKind::Assign(slot, value) => {
                let Some(value) = self.expr(value)? else {
                    return Ok(None);
                };
                self.assign(*slot, Rvalue::Use(value), span);
                Self::no_value(expr.ty)
            }
            ExprKind::If(condition, yes, no) => {
                let Some(condition) = self.expr(condition)? else {
                    return Ok(None);
                };
                let then_block = self.new_block();
                let else_block = self.new_block();
                self.terminate(
                    TerminatorKind::Switch {
                        value: condition,
                        targets: vec![(0, else_block)],
                        otherwise: then_block,
                    },
                    span,
                );
                let temp = self.result_temp(expr.ty);
                let mut join = None;
                for (block, arm) in [(then_block, yes), (else_block, no)] {
                    self.enter(block);
                    if let Some(value) = self.block(arm)? {
                        if let Some(temp) = temp {
                            self.assign(temp, Rvalue::Use(value), span);
                        }
                        self.goto_join(&mut join, span);
                    }
                }
                let Some(join) = join else {
                    return Ok(None);
                };
                self.enter(join);
                Self::result(temp, expr.ty)
            }
            ExprKind::Match(scrutinee, arms) => return self.matching(expr, scrutinee, arms),
            ExprKind::While(condition, body) => {
                let head = self.new_block();
                self.goto(head, span);
                self.enter(head);
                let Some(condition) = self.expr(condition)? else {
                    return Ok(None);
                };
                let body_block = self.new_block();
                let exit = self.new_block();
                self.terminate(
                    TerminatorKind::Switch {
                        value: condition,
                        targets: vec![(0, exit)],
                        otherwise: body_block,
                    },
                    span,
                );
                self.loops.push(Loop {
                    head,
                    exit: Some(exit),
                    result: None,
                });
                self.enter(body_block);
                let finished = self.block(body);
                self.loops.pop();
                if finished?.is_some() {
                    self.goto(head, span);
                }
                self.enter(exit);
                Self::no_value(expr.ty)
            }
            ExprKind::Loop(body) => {
                let head = self.new_block();
                self.goto(head, span);
                self.enter(head);
                let result = self.result_temp(expr.ty);
                self.loops.push(Loop {
                    head,
                    exit: None,
                    result,
                });
                let finished = self.block(body);
                let scope = self.loops.pop().expect("the loop's scope");
                if finished?.is_some() {
                    self.goto(head, span);
                }
                let Some(exit) = scope.exit else {
                    return Ok(None);
                };
                self.enter(exit);
                Self::result(result, expr.ty)
            }
            ExprKind::Break(value, cleanup) => {
                if !cleanup.is_empty() {
                    return Err("a break that drops resources".into());
                }
                if let Some(value) = value {
                    let Some(value) = self.expr(value)? else {
                        return Ok(None);
                    };
                    if let Some(result) = self.loops.last().and_then(|scope| scope.result) {
                        self.assign(result, Rvalue::Use(value), span);
                    }
                }
                let scope = self.loops.len().checked_sub(1).ok_or("a break outside a loop")?;
                let mut exit = self.loops[scope].exit;
                self.goto_join(&mut exit, span);
                self.loops[scope].exit = exit;
                return Ok(None);
            }
            ExprKind::Continue(cleanup) => {
                if !cleanup.is_empty() {
                    return Err("a continue that drops resources".into());
                }
                let head = self.loops.last().ok_or("a continue outside a loop")?.head;
                self.goto(head, span);
                return Ok(None);
            }
            ExprKind::Return(value) => {
                let Some(value) = self.expr(value)? else {
                    return Ok(None);
                };
                self.terminate(TerminatorKind::Return(value), span);
                return Ok(None);
            }
            ExprKind::Call(target, args) => return self.call(expr, target, args),
            other => return Err(variant_name(other)),
        }))
    }

    fn short_circuit(
        &mut self,
        op: &Kind,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Result<Option<Operand>, String> {
        let Some(left) = self.expr(left)? else {
            return Ok(None);
        };
        let temp = self.temp(Type::Bool);
        let rhs = self.new_block();
        let shortcut = self.new_block();
        let (on_false, on_true) = if *op == Kind::AmpAmp {
            (shortcut, rhs)
        } else {
            (rhs, shortcut)
        };
        self.terminate(
            TerminatorKind::Switch {
                value: left,
                targets: vec![(0, on_false)],
                otherwise: on_true,
            },
            span,
        );
        let mut join = None;
        self.enter(shortcut);
        let value = Operand::Constant(i64::from(*op == Kind::PipePipe), Type::Bool);
        self.assign(temp, Rvalue::Use(value), span);
        self.goto_join(&mut join, span);
        self.enter(rhs);
        if let Some(value) = self.expr(right)? {
            self.assign(temp, Rvalue::Use(value), span);
            self.goto_join(&mut join, span);
        }
        self.enter(join.expect("the shortcut reaches the join"));
        Ok(Some(Operand::Move(temp)))
    }

    fn matching(
        &mut self,
        expr: &Expr,
        scrutinee: &Expr,
        arms: &[crate::executable::Arm],
    ) -> Result<Option<Operand>, String> {
        let span = expr.span;
        let Some(value) = self.expr(scrutinee)? else {
            return Ok(None);
        };
        // Arms may assign the scrutinee's local; test a copy.
        let subject = self.temp(scrutinee.ty);
        self.assign(subject, Rvalue::Use(value), scrutinee.span);
        let temp = self.result_temp(expr.ty);
        let mut join = None;
        for arm in arms {
            let (literals, binding) = match &arm.pattern {
                Pattern::Any => (None, None),
                Pattern::Bind(slot) => (None, Some(*slot)),
                Pattern::Literal(value) => (Some(vec![*value]), None),
                Pattern::Or(patterns) => {
                    let mut literals = Some(Vec::new());
                    for pattern in patterns {
                        match pattern {
                            Pattern::Literal(value) => {
                                if let Some(literals) = &mut literals {
                                    literals.push(*value);
                                }
                            }
                            Pattern::Any => literals = None,
                            _ => return Err("a pattern other than a literal".into()),
                        }
                    }
                    (literals, None)
                }
                _ => return Err("a pattern other than a literal".into()),
            };
            // An arm without a test or guard matches everything left.
            let irrefutable = literals.is_none() && arm.guard.is_none();
            let next = if irrefutable { usize::MAX } else { self.new_block() };
            if let Some(literals) = literals {
                let body = self.new_block();
                self.terminate(
                    TerminatorKind::Switch {
                        value: Operand::Copy(subject),
                        targets: literals.into_iter().map(|value| (value, body)).collect(),
                        otherwise: next,
                    },
                    arm.body.span,
                );
                self.enter(body);
            }
            if let Some(slot) = binding {
                self.assign(slot, Rvalue::Use(Operand::Copy(subject)), arm.body.span);
            }
            if let Some(guard) = &arm.guard {
                match self.expr(guard)? {
                    Some(condition) => {
                        let body = self.new_block();
                        self.terminate(
                            TerminatorKind::Switch {
                                value: condition,
                                targets: vec![(0, next)],
                                otherwise: body,
                            },
                            guard.span,
                        );
                        self.enter(body);
                    }
                    None => {
                        self.enter(next);
                        continue;
                    }
                }
            }
            if let Some(value) = self.expr(&arm.body)? {
                if let Some(temp) = temp {
                    self.assign(temp, Rvalue::Use(value), arm.body.span);
                }
                self.goto_join(&mut join, arm.body.span);
            }
            if irrefutable {
                break;
            }
            self.enter(next);
        }
        if self.current.is_some() {
            // The checker proved the arms exhaustive.
            self.terminate(TerminatorKind::Unreachable, span);
        }
        let Some(join) = join else {
            return Ok(None);
        };
        self.enter(join);
        Ok(Some(Self::result(temp, expr.ty)))
    }

    fn call(
        &mut self,
        expr: &Expr,
        target: &Target,
        args: &[Expr],
    ) -> Result<Option<Operand>, String> {
        let span = expr.span;
        let callee = match target {
            Target::Function(index) => {
                callable(self.program, *index)?;
                Callee::Function(*index)
            }
            Target::Int(op, source, target) if int_op_name(*op).is_some() => {
                let args = args.iter().collect::<Vec<_>>();
                let Some(values) = self.operands(&args)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Int(*op, *source, *target, values), span);
                return Ok(Some(Operand::Move(temp)));
            }
            Target::Print => Callee::PrintInt(IntKind::I64),
            Target::PrintInt(kind) => Callee::PrintInt(*kind),
            Target::Panic => {
                // The message is not part of a native panic.
                if !args.iter().all(|arg| {
                    matches!(arg.kind, ExprKind::Constant(_) | ExprKind::BytesLiteral(_))
                }) {
                    return Err("a panic with a computed message".into());
                }
                self.terminate(TerminatorKind::Panic { unwind: None }, span);
                return Ok(None);
            }
            other => return Err(format!("a call to {}", target_name(other))),
        };
        let args = args.iter().collect::<Vec<_>>();
        let Some(args) = self.operands(&args)? else {
            return Ok(None);
        };
        let destination = self.temp(expr.ty);
        let next = self.new_block();
        self.terminate(
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                unwind: None,
            },
            span,
        );
        self.enter(next);
        if expr.ty == Type::Never {
            self.terminate(TerminatorKind::Unreachable, span);
            return Ok(None);
        }
        Ok(Some(Operand::Move(destination)))
    }
}

fn target_name(target: &Target) -> String {
    let text = format!("{target:?}");
    let end = text
        .find(|c: char| !c.is_alphanumeric())
        .unwrap_or(text.len());
    format!("the builtin {}", &text[..end])
}

/// The variant's name, without formatting its whole subtree.
fn variant_name(kind: &ExprKind) -> String {
    struct Name(String);
    impl std::fmt::Write for Name {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            let end = text
                .find(|c: char| !c.is_alphanumeric())
                .unwrap_or(text.len());
            self.0.push_str(&text[..end]);
            if end < text.len() {
                Err(std::fmt::Error)
            } else {
                Ok(())
            }
        }
    }
    let mut name = Name(String::new());
    let _ = std::fmt::Write::write_fmt(&mut name, format_args!("{kind:?}"));
    format!("an expression of kind {}", name.0)
}
