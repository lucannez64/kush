//! Lower one checked function to a [`Body`].
//!
//! Coverage grows node by node (docs/mir-design.md section 6). Today the
//! builder takes functions whose values are scalars (integers, floats,
//! `char`, `bool`, `()`) or records and enums of them that own nothing and
//! hold no borrow, with arithmetic, assignments, construction, field reads,
//! `if`, `match` on literals and variants, loops, direct calls, `print` of
//! integers and `panic`. Anything else is reported by name, and native code
//! generation then lowers that function from the tree.

use super::*;
use crate::executable::{Expr, ExprKind, Function, Pattern, Target};
use crate::executable::Statement as TreeStatement;

pub(crate) fn build(program: &Executable, index: usize) -> Result<Body, String> {
    let function = &program.functions[index];
    eligible(program, function)?;
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

/// A one-word value with no ownership.
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

/// A value the builder covers: a scalar, or a record or enum of such
/// values that owns nothing and holds no borrow.
fn plain(program: &Executable, ty: Type) -> bool {
    fn go(program: &Executable, ty: Type, depth: usize) -> bool {
        if scalar(ty) {
            return true;
        }
        let Some(id) = ty.layout() else {
            return false;
        };
        let definition = &program.enums[id];
        depth < 16
            && !program.owns(ty)
            && !definition.borrowed
            && !definition.mutable_borrow
            && definition.array.is_none()
            && definition.dynamic_array.is_none()
            && definition.runtime_length.is_none()
            && definition
                .variants
                .iter()
                .all(|variant| variant.fields.iter().all(|field| go(program, *field, depth + 1)))
    }
    go(program, ty, 0)
}

fn erased(grade: Option<crate::grades::Grade>) -> bool {
    grade.is_some_and(crate::grades::Grade::is_zero)
}

/// The function's frame and calling convention are ones the builder covers.
fn eligible(program: &Executable, function: &Function) -> Result<(), String> {
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
    if !plain(program, function.result) {
        return Err(format!("a {:?} result", function.result));
    }
    for (slot, local) in function.locals.iter().enumerate() {
        if !plain(program, local.ty) {
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
    if !plain(program, callee.result) {
        return Err(format!("a call returning {:?}", callee.result));
    }
    if callee.locals[..callee.parameters]
        .iter()
        .any(|local| !plain(program, local.ty))
    {
        return Err("a call with a parameter the IR does not cover".into());
    }
    Ok(())
}

/// Patterns the builder compiles: literals, variants and bindings, and
/// alternatives without bindings.
fn supported(pattern: &Pattern) -> Result<(), String> {
    match pattern {
        Pattern::Any | Pattern::Bind(_) | Pattern::Literal(_) => Ok(()),
        Pattern::Variant { fields, .. } => fields.iter().try_for_each(|(_, p)| supported(p)),
        Pattern::Or(alternatives) => alternatives.iter().try_for_each(|p| {
            if binds(p) {
                Err("alternatives with bindings".into())
            } else {
                supported(p)
            }
        }),
        Pattern::Type { .. } => Err("a union pattern".into()),
        Pattern::DynArray { .. } => Err("an array pattern".into()),
    }
}

fn binds(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| binds(p)),
        Pattern::Or(alternatives) => alternatives.iter().any(binds),
        _ => false,
    }
}

/// Whether a pattern can fail to match a value of its type.
fn refutable(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Any | Pattern::Bind(_) => false,
        Pattern::Variant {
            fields,
            tagged,
            niche,
            ..
        } => niche.is_some() || *tagged || fields.iter().any(|(_, p)| refutable(p)),
        Pattern::Or(alternatives) => alternatives.iter().all(refutable),
        _ => true,
    }
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
        temp.map_or_else(|| Self::no_value(ty), |temp| Operand::Move(Place::local(temp)))
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
                Operand::Copy(place) | Operand::Move(place) => !self.locals[place.local].temporary,
                Operand::Constant(..) => false,
            };
            let value = if exposed && exprs[index + 1..].iter().any(|later| !leaf(later)) {
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Use(value), expr.span);
                Operand::Move(Place::local(temp))
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
        if !plain(self.program, expr.ty) {
            return Err(format!("a value of type {:?}", expr.ty));
        }
        let span = expr.span;
        Ok(Some(match &expr.kind {
            ExprKind::Constant(value) => Operand::Constant(*value, expr.ty),
            ExprKind::Local(slot) | ExprKind::Peek(slot) => Operand::Copy(Place::local(*slot)),
            ExprKind::Move(slot) => Operand::Move(Place::local(*slot)),
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Construct { enum_id, tag, fields } => {
                let fields = fields.iter().collect::<Vec<_>>();
                let Some(values) = self.operands(&fields)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Aggregate(Type::Enum(*enum_id), *tag, values), span);
                Operand::Move(Place::local(temp))
            }
            ExprKind::Project(base, offset) => {
                if base.ty.is_ref() {
                    return Err("a field read through a reference".into());
                }
                let Some(value) = self.expr(base)? else {
                    return Ok(None);
                };
                let place = value.place().ok_or("a field of a constant")?;
                Operand::Copy(Place {
                    local: place.local,
                    field: Some(Field {
                        offset: place.field.map_or(0, |field| field.offset) + offset,
                        ty: expr.ty,
                    }),
                })
            }
            ExprKind::Unary(op, operand) => {
                let op = UnOp::from_kind(op).ok_or("an unknown unary operator")?;
                let Some(value) = self.expr(operand)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Unary(op, value), span);
                Operand::Move(Place::local(temp))
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
                Operand::Move(Place::local(temp))
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
        Ok(Some(Operand::Move(Place::local(temp))))
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
            supported(&arm.pattern)?;
            // An arm without a test or guard matches everything left.
            let irrefutable = !refutable(&arm.pattern) && arm.guard.is_none();
            let next = if irrefutable { usize::MAX } else { self.new_block() };
            self.test(subject, 0, &arm.pattern, next, arm.body.span);
            self.bind(subject, 0, &arm.pattern, arm.body.span);
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

    /// The word at `offset` of the subject, as an integer.
    fn word(&self, subject: LocalId, offset: usize) -> Operand {
        if offset == 0 && self.program.width(self.locals[subject].ty) == 1 {
            Operand::Copy(Place::local(subject))
        } else {
            Operand::Copy(Place {
                local: subject,
                field: Some(Field {
                    offset,
                    ty: Type::I64,
                }),
            })
        }
    }

    /// Continue when `value` equals (or, with `equal` false, differs from)
    /// `constant`; otherwise jump to `fail`.
    fn expect_word(&mut self, value: Operand, constant: i64, equal: bool, fail: BlockId, span: Span) {
        let ok = self.new_block();
        let (hit, miss) = if equal { (ok, fail) } else { (fail, ok) };
        self.terminate(
            TerminatorKind::Switch {
                value,
                targets: vec![(constant, hit)],
                otherwise: miss,
            },
            span,
        );
        self.enter(ok);
    }

    /// Emit the tests of `pattern` against the subject's words from
    /// `offset`: the current block continues when they pass, and jumps to
    /// `fail` when one does not.
    fn test(&mut self, subject: LocalId, offset: usize, pattern: &Pattern, fail: BlockId, span: Span) {
        match pattern {
            Pattern::Any | Pattern::Bind(_) => {}
            Pattern::Literal(value) => {
                let word = self.word(subject, offset);
                self.expect_word(word, *value, true, fail, span);
            }
            Pattern::Variant {
                tag,
                fields,
                tagged,
                niche,
            } => {
                let word = self.word(subject, offset);
                if let Some(niche) = niche {
                    match niche.decoder(*tag) {
                        crate::layout_cert::Decoder::Equal(constant) => {
                            self.expect_word(word, constant, true, fail, span);
                        }
                        crate::layout_cert::Decoder::NotEqual(constant) => {
                            self.expect_word(word, constant, false, fail, span);
                        }
                    }
                } else if *tagged {
                    self.expect_word(word, *tag as i64, true, fail, span);
                }
                for (field, pattern) in fields {
                    self.test(subject, offset + field, pattern, fail, span);
                }
            }
            Pattern::Or(alternatives) => {
                let success = self.new_block();
                for alternative in alternatives {
                    if !refutable(alternative) {
                        self.goto(success, span);
                        self.enter(success);
                        return;
                    }
                    let next = self.new_block();
                    self.test(subject, offset, alternative, next, span);
                    self.goto(success, span);
                    self.enter(next);
                }
                self.goto(fail, span);
                self.enter(success);
            }
            _ => unreachable!("supported() rejects other patterns"),
        }
    }

    /// Assign the bindings of a pattern that matched.
    fn bind(&mut self, subject: LocalId, offset: usize, pattern: &Pattern, span: Span) {
        match pattern {
            Pattern::Bind(slot) => {
                let ty = self.locals[*slot].ty;
                let whole = offset == 0
                    && self.program.width(ty) == self.program.width(self.locals[subject].ty);
                let place = Place {
                    local: subject,
                    field: (!whole).then_some(Field { offset, ty }),
                };
                self.assign(*slot, Rvalue::Use(Operand::Copy(place)), span);
            }
            Pattern::Variant { fields, .. } => {
                for (field, pattern) in fields {
                    self.bind(subject, offset + field, pattern, span);
                }
            }
            _ => {}
        }
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
                return Ok(Some(Operand::Move(Place::local(temp))));
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
        Ok(Some(Operand::Move(Place::local(destination))))
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
