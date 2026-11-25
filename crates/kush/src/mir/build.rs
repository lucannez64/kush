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
use crate::executable::Statement as TreeStatement;
use crate::executable::{Expr, ExprKind, Function, Pattern, Target};

pub(crate) fn build(program: &Executable, index: usize) -> Result<Body, String> {
    let function = &program.functions[index];
    eligible(program, function)?;
    let mut builder = Builder {
        program,
        function,
        resources: Vec::new(),
        cleanup: None,
        in_cleanup: false,
        builtins: Vec::new(),
        coercions: Vec::new(),
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
    builder.start(function.span);
    if let Some(value) = builder.block(&function.body)? {
        let span = function
            .body
            .tail
            .as_ref()
            .map_or(function.span, |tail| tail.span);
        builder.return_value(value, span);
    }
    builder.finish_cleanup(function.span);
    let unwind = builder.cleanup;
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
                unwind: if block.cleanup { None } else { unwind },
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Body {
        name: function.name.clone(),
        parameters: function.parameters,
        locals: builder.locals,
        blocks,
        result: function.result,
        builtins: Builtins(builder.builtins),
        coercions: Coercions(builder.coercions),
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

/// A value the builder covers: a scalar, a box, vector, reference, view,
/// `Bytes` or `String`, or a record, enum or inline array of such values.
fn plain(program: &Executable, ty: Type) -> bool {
    fn go(program: &Executable, ty: Type, depth: usize) -> bool {
        if scalar(ty) || matches!(ty, Type::Bytes | Type::String | Type::Str | Type::StrMut) {
            return true;
        }
        if matches!(ty, Type::Fn(_) | Type::Once(_) | Type::DynObj(_)) {
            return true;
        }
        if let Type::Union(id) = ty {
            return depth < 16
                && program.unions[id]
                    .members
                    .iter()
                    .all(|member| go(program, *member, depth + 1));
        }
        if let Type::Box(pointee)
        | Type::Vec(pointee)
        | Type::Ref(pointee)
        | Type::RefMut(pointee)
        | Type::Slice(pointee)
        | Type::SliceMut(pointee) = ty
        {
            return depth < 16 && go(program, program.pointees[pointee], depth + 1);
        }
        let Some(id) = ty.layout() else {
            return false;
        };
        let definition = &program.enums[id];
        depth < 16
            && definition.dynamic_array.is_none()
            && definition.runtime_length.is_none()
            && definition.variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .all(|field| go(program, *field, depth + 1))
            })
    }
    go(program, ty, 0)
}

fn erased(grade: Option<crate::grades::Grade>) -> bool {
    grade.is_some_and(crate::grades::Grade::is_zero)
}

/// The function's frame and calling convention are ones the builder covers.
fn eligible(program: &Executable, function: &Function) -> Result<(), String> {
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
    for local in &function.locals {
        if !plain(program, local.ty) {
            return Err(format!("a local of type {:?}", local.ty));
        }
        if erased(local.grade) {
            return Err("an erased local".into());
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
        Pattern::Type { inner, .. } => supported(inner),
        Pattern::DynArray { .. } => Err("an array pattern".into()),
    }
}

fn has_alternatives(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Or(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| has_alternatives(p)),
        Pattern::Type { inner, .. } => has_alternatives(inner),
        _ => false,
    }
}

fn binds(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| binds(p)),
        Pattern::Type { inner, .. } => binds(inner),
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
    /// Part of the unwind cleanup: a panic here continues unwinding.
    cleanup: bool,
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
    function: &'a Function,
    /// Per checked resource that owns something: its drop flag and the
    /// local holding its value (the tree path's tracked words).
    resources: Vec<Option<(LocalId, LocalId)>>,
    /// The cleanup block every panic unwinds to, when the function has
    /// owned resources: it drops each one whose flag is set.
    cleanup: Option<BlockId>,
    /// Blocks created now belong to the cleanup.
    in_cleanup: bool,
    /// The builtin targets called so far.
    builtins: Vec<Target>,
    /// The coercions applied so far.
    coercions: Vec<(Type, crate::executable::Coercion)>,
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
            cleanup: self.in_cleanup,
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
        self.store(Place::local(local), rvalue, span);
    }
    fn store(&mut self, place: Place, rvalue: Rvalue, span: Span) {
        let block = self.current.expect("an assignment in reachable code");
        self.blocks[block].statements.push(Statement {
            kind: StatementKind::Assign(place, rvalue),
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
        let target = match *join {
            Some(target) => target,
            None => {
                let target = self.new_block();
                *join = Some(target);
                target
            }
        };
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
        temp.map_or_else(
            || Self::no_value(ty),
            |temp| Operand::Move(Place::local(temp)),
        )
    }

    /// Drop flags start clear; owned parameters are live on entry. A
    /// local's resource is dropped from the local itself, which a write
    /// through `&mut` may have replaced; others from their own local.
    fn start(&mut self, span: Span) {
        let types = self.function.resources.clone();
        for (id, ty) in types.into_iter().enumerate() {
            let owner = self
                .function
                .local_resources
                .iter()
                .position(|resource| *resource == Some(id));
            let resource = self.program.owns(ty).then(|| {
                let flag = self.temp(Type::Bool);
                let value = owner.unwrap_or_else(|| self.temp(ty));
                (flag, value)
            });
            if let Some((flag, _)) = resource {
                self.assign(flag, Rvalue::Use(Operand::Constant(0, Type::Bool)), span);
            }
            self.resources.push(resource);
        }
        if self.resources.iter().any(Option::is_some) {
            self.in_cleanup = true;
            self.cleanup = Some(self.new_block());
            self.in_cleanup = false;
        }
        for slot in 0..self.function.parameters {
            self.activate_local(slot, span);
        }
    }
    fn resource(&self, id: Option<usize>) -> Option<(LocalId, LocalId)> {
        id.and_then(|id| self.resources[id])
    }
    fn set_flag(&mut self, id: Option<usize>, live: bool, span: Span) {
        if let Some((flag, _)) = self.resource(id) {
            let value = Operand::Constant(i64::from(live), Type::Bool);
            self.assign(flag, Rvalue::Use(value), span);
        }
    }
    /// The tree path's `track`: an expression's owned result is live.
    fn track(&mut self, expr: &Expr, value: Operand) {
        if let Some((flag, slot)) = self.resource(expr.resource) {
            let value = match value {
                Operand::Move(place) => Operand::Copy(place),
                other => other,
            };
            self.assign(slot, Rvalue::Use(value), expr.span);
            self.assign(
                flag,
                Rvalue::Use(Operand::Constant(1, Type::Bool)),
                expr.span,
            );
        }
    }
    /// A parent took ownership of the expression's result.
    fn consume(&mut self, expr: &Expr) {
        self.set_flag(expr.resource, false, expr.span);
    }
    fn local_resource(&self, slot: LocalId) -> Option<usize> {
        self.function.local_resources.get(slot).copied().flatten()
    }
    /// A local now owns its value.
    fn activate_local(&mut self, slot: LocalId, span: Span) {
        self.set_flag(self.local_resource(slot), true, span);
    }
    /// Drop a resource if its flag is set, and clear the flag.
    fn cleanup_resource(&mut self, id: Option<usize>, span: Span) {
        let Some((flag, value)) = self.resource(id) else {
            return;
        };
        let live = self.new_block();
        let skip = self.new_block();
        self.terminate(
            TerminatorKind::Switch {
                value: Operand::Copy(Place::local(flag)),
                targets: vec![(0, skip)],
                otherwise: live,
            },
            span,
        );
        self.enter(live);
        self.assign(flag, Rvalue::Use(Operand::Constant(0, Type::Bool)), span);
        self.terminate(
            TerminatorKind::Drop {
                place: Place::local(value),
                next: skip,
                unwind: None,
            },
            span,
        );
        self.enter(skip);
    }
    fn cleanup_all(&mut self, span: Span) {
        for id in (0..self.resources.len()).rev() {
            self.cleanup_resource(Some(id), span);
        }
    }
    /// Run drop glue on a place, then continue in a new block.
    fn drop_place(&mut self, place: Place, span: Span) {
        let next = self.new_block();
        self.terminate(
            TerminatorKind::Drop {
                place,
                next,
                unwind: None,
            },
            span,
        );
        self.enter(next);
    }
    /// A local holding the reference `value`, so places can go through it.
    fn pointer_local(&mut self, value: Operand, ty: Type, span: Span) -> LocalId {
        match value.place() {
            Some(place) if !place.deref && place.field.is_none() => place.local,
            _ => {
                let temp = self.temp(ty);
                self.assign(temp, Rvalue::Use(value), span);
                temp
            }
        }
    }
    /// The place a checked place expression names, for taking its address:
    /// a local, or fields of one, possibly through references.
    fn place_of(&mut self, expr: &Expr) -> Result<Option<Place>, String> {
        Ok(Some(match &expr.kind {
            // The tree path takes such an address with `local_address`,
            // which a whole-local field also selects natively.
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                Place::field(*slot, 0, self.locals[*slot].ty)
            }
            ExprKind::Project(base, offset) if base.ty.is_ref() => {
                let Some(value) = self.expr(base)? else {
                    return Ok(None);
                };
                let pointer = self.pointer_local(value, base.ty, expr.span);
                Place::deref(pointer, *offset, expr.ty)
            }
            ExprKind::Project(base, offset) => {
                let Some(place) = self.place_of(base)? else {
                    return Ok(None);
                };
                Place {
                    local: place.local,
                    deref: place.deref,
                    field: Some(Field {
                        offset: place.field.map_or(0, |field| field.offset) + offset,
                        ty: expr.ty,
                    }),
                }
            }
            other => return Err(format!("a borrow of {}", variant_name(other))),
        }))
    }
    /// The unwind edge of a call or panic.
    fn unwind(&self) -> Option<BlockId> {
        self.cleanup
    }
    /// Copy a value read from a source local into a temporary, so drops
    /// emitted before it is used cannot reach it first.
    fn settle(&mut self, value: Operand, ty: Type, span: Span) -> Operand {
        match value.place() {
            Some(place) if place.deref || !self.locals[place.local].temporary => {
                let temp = self.temp(ty);
                self.assign(temp, Rvalue::Use(value), span);
                Operand::Move(Place::local(temp))
            }
            _ => value,
        }
    }
    fn return_value(&mut self, value: Operand, span: Span) {
        let ty = self.function.result;
        let value = if self.cleanup.is_some() {
            self.settle(value, ty, span)
        } else {
            value
        };
        self.cleanup_all(span);
        self.terminate(TerminatorKind::Return(value), span);
    }
    /// Fill the cleanup block: drop every live resource, then resume.
    fn finish_cleanup(&mut self, span: Span) {
        let Some(cleanup) = self.cleanup else {
            return;
        };
        self.in_cleanup = true;
        self.enter(cleanup);
        self.cleanup_all(span);
        self.terminate(TerminatorKind::Resume, span);
        self.in_cleanup = false;
    }

    fn block(&mut self, block: &crate::executable::Block) -> Result<Option<Operand>, String> {
        let mut slots = Vec::new();
        for statement in &block.statements {
            match statement {
                TreeStatement::Let(slot, expr) => {
                    let Some(value) = self.expr(expr)? else {
                        return Ok(None);
                    };
                    self.consume(expr);
                    self.assign(*slot, Rvalue::Use(value), expr.span);
                    self.activate_local(*slot, expr.span);
                    slots.push(*slot);
                }
                TreeStatement::Declare(_) => return Err("a temporary owner".into()),
                TreeStatement::Expr(expr) => {
                    if self.expr(expr)?.is_none() {
                        return Ok(None);
                    }
                    self.cleanup_resource(expr.resource, expr.span);
                }
            }
        }
        let (value, span) = match &block.tail {
            Some(tail) => {
                let Some(value) = self.expr(tail)? else {
                    return Ok(None);
                };
                self.consume(tail);
                (value, tail.span)
            }
            None => (Self::no_value(Type::Unit), Span::new(0, 0)),
        };
        let owned = slots
            .iter()
            .any(|slot| self.resource(self.local_resource(*slot)).is_some());
        if !owned {
            return Ok(Some(value));
        }
        let value = self.settle(value, block.ty, span);
        for slot in slots.into_iter().rev() {
            self.cleanup_resource(self.local_resource(slot), span);
        }
        Ok(Some(value))
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
            // A read through a reference is exposed too: a later expression
            // may write through another one.
            let exposed = match value {
                Operand::Copy(place) | Operand::Move(place) => {
                    place.deref || !self.locals[place.local].temporary
                }
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

    /// Lower an expression; an owned result becomes live, as the tree
    /// path's `expr` tracks it.
    fn expr(&mut self, expr: &Expr) -> Result<Option<Operand>, String> {
        if !plain(self.program, expr.ty) {
            return Err(format!("a value of type {:?}", expr.ty));
        }
        let value = self.expression(expr)?;
        if let Some(value) = value {
            self.track(expr, value);
        }
        Ok(value)
    }

    fn expression(&mut self, expr: &Expr) -> Result<Option<Operand>, String> {
        let span = expr.span;
        Ok(Some(match &expr.kind {
            ExprKind::Constant(value) => Operand::Constant(*value, expr.ty),
            ExprKind::Local(slot) | ExprKind::Peek(slot) => Operand::Copy(Place::local(*slot)),
            ExprKind::Move(slot) => {
                self.set_flag(self.local_resource(*slot), false, span);
                Operand::Move(Place::local(*slot))
            }
            ExprKind::BytesLiteral(bytes) => {
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Bytes(bytes.clone()), span);
                Operand::Move(Place::local(temp))
            }
            ExprKind::BoxNew(value) | ExprKind::BoxTake(value) => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                let rvalue = if matches!(expr.kind, ExprKind::BoxNew(_)) {
                    Rvalue::BoxNew(operand)
                } else {
                    Rvalue::BoxTake(operand)
                };
                self.assign(temp, rvalue, span);
                self.consume(value);
                Operand::Move(Place::local(temp))
            }
            ExprKind::Drop(value) => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                if self.program.owns(value.ty) {
                    let place = match operand.place() {
                        Some(place) => place,
                        None => return Err("a drop of a constant".into()),
                    };
                    self.drop_place(place, span);
                }
                Self::no_value(expr.ty)
            }
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Construct {
                enum_id,
                tag,
                fields,
            } => {
                let fields = fields.iter().collect::<Vec<_>>();
                let Some(values) = self.operands(&fields)? else {
                    return Ok(None);
                };
                for field in &fields {
                    self.consume(field);
                }
                let temp = self.temp(expr.ty);
                self.assign(
                    temp,
                    Rvalue::Aggregate(Type::Enum(*enum_id), *tag, values),
                    span,
                );
                Operand::Move(Place::local(temp))
            }
            ExprKind::Project(base, offset) if base.ty.is_ref() => {
                let Some(value) = self.expr(base)? else {
                    return Ok(None);
                };
                let pointer = self.pointer_local(value, base.ty, span);
                Operand::Copy(Place::deref(pointer, *offset, expr.ty))
            }
            ExprKind::RefRead(reference) => {
                let Some(value) = self.expr(reference)? else {
                    return Ok(None);
                };
                let pointer = self.pointer_local(value, reference.ty, span);
                Operand::Copy(Place::deref(pointer, 0, expr.ty))
            }
            ExprKind::Slice {
                base,
                start,
                end,
                element,
                check,
                split: _,
                text,
                field,
            } => {
                if field.is_some() {
                    return Err("a view of a record field".into());
                }
                let array = match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot)
                        if !text
                            && base
                                .ty
                                .layout()
                                .is_some_and(|id| self.program.enums[id].array.is_some()) =>
                    {
                        Some(*slot)
                    }
                    _ => None,
                };
                let mut exprs = Vec::new();
                if array.is_none() {
                    exprs.push(&**base);
                }
                exprs.extend(start.as_deref());
                exprs.extend(end.as_deref());
                let Some(mut values) = self.operands(&exprs)? else {
                    return Ok(None);
                };
                let source = match array {
                    Some(slot) => ViewSource::Array(slot),
                    None => ViewSource::Value(values.remove(0)),
                };
                let mut values = values.into_iter();
                let start = start.as_ref().map(|_| values.next().expect("start"));
                let end = end.as_ref().map(|_| values.next().expect("end"));
                let temp = self.temp(expr.ty);
                self.assign(
                    temp,
                    Rvalue::View {
                        source,
                        start,
                        end,
                        element: *element,
                        check: *check,
                        text: *text,
                    },
                    span,
                );
                Operand::Move(Place::local(temp))
            }
            ExprKind::Coerce {
                value,
                to,
                coercion,
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                self.coercions.push((*to, coercion.clone()));
                let temp = self.temp(expr.ty);
                self.assign(
                    temp,
                    Rvalue::Coerce(operand, self.coercions.len() - 1),
                    span,
                );
                Operand::Move(Place::local(temp))
            }
            ExprKind::FnValue { function, captures } => {
                let by_address = &self.program.functions[*function].capture_refs;
                let mut values = Vec::new();
                for (index, capture) in captures.iter().enumerate() {
                    if !by_address.get(index).copied().unwrap_or(false) {
                        values.push(capture);
                    }
                }
                let Some(operands) = self.operands(&values)? else {
                    return Ok(None);
                };
                let mut operands = operands.into_iter();
                let mut lowered = Vec::with_capacity(captures.len());
                for (index, capture) in captures.iter().enumerate() {
                    if by_address.get(index).copied().unwrap_or(false) {
                        let (ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)) =
                            capture.kind
                        else {
                            return Err("a by-reference capture of a non-local".into());
                        };
                        lowered.push(Capture::Address(slot));
                    } else {
                        lowered.push(Capture::Value(operands.next().expect("a capture")));
                    }
                }
                for capture in captures {
                    self.consume(capture);
                }
                let temp = self.temp(expr.ty);
                let function = *function;
                self.assign(
                    temp,
                    Rvalue::FnValue {
                        function,
                        captures: lowered,
                    },
                    span,
                );
                Operand::Move(Place::local(temp))
            }
            ExprKind::CallIndirect { callee, arguments } => {
                let mut exprs = vec![&**callee];
                exprs.extend(arguments);
                let Some(mut values) = self.operands(&exprs)? else {
                    return Ok(None);
                };
                for consumed in &exprs {
                    self.consume(consumed);
                }
                let code = values.remove(0);
                return Ok(self.emit_call(expr, Callee::Indirect(code), values));
            }
            ExprKind::Borrow(slot) => {
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Ref(Place::local(*slot)), span);
                Operand::Move(Place::local(temp))
            }
            ExprKind::BorrowPlace(place) => {
                let Some(place) = self.place_of(place)? else {
                    return Ok(None);
                };
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Ref(place), span);
                Operand::Move(Place::local(temp))
            }
            ExprKind::RefAssign(reference, offset, replacement) => {
                let Some(values) = self.operands(&[reference, replacement])? else {
                    return Ok(None);
                };
                let pointer = self.pointer_local(values[0], reference.ty, span);
                let place = Place::deref(pointer, *offset, replacement.ty);
                self.store(place, Rvalue::Use(values[1]), span);
                self.consume(replacement);
                Self::no_value(expr.ty)
            }
            ExprKind::DerefWrite(reference, replacement) => {
                let Some(values) = self.operands(&[reference, replacement])? else {
                    return Ok(None);
                };
                let pointer = self.pointer_local(values[0], reference.ty, span);
                let pointee = reference
                    .ty
                    .ref_pointee()
                    .map(|pointee| self.program.pointees[pointee])
                    .ok_or("a write through a non-reference")?;
                let place = Place::deref(pointer, 0, pointee);
                if self.program.owns(pointee) {
                    self.drop_place(place, span);
                }
                self.store(place, Rvalue::Use(values[1]), span);
                self.consume(replacement);
                Self::no_value(expr.ty)
            }
            ExprKind::Project(base, offset) => {
                let Some(value) = self.expr(base)? else {
                    return Ok(None);
                };
                let place = value.place().ok_or("a field of a constant")?;
                Operand::Copy(Place {
                    local: place.local,
                    deref: place.deref,
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
            ExprKind::Assign(slot, replacement) => {
                let Some(value) = self.expr(replacement)? else {
                    return Ok(None);
                };
                self.consume(replacement);
                let old = self.local_resource(*slot);
                let value = if self.resource(old).is_some() {
                    let value = self.settle(value, replacement.ty, span);
                    self.cleanup_resource(old, span);
                    value
                } else {
                    value
                };
                self.assign(*slot, Rvalue::Use(value), span);
                self.activate_local(*slot, span);
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
                if let Some(value) = value {
                    let Some(operand) = self.expr(value)? else {
                        return Ok(None);
                    };
                    self.consume(value);
                    if let Some(result) = self.loops.last().and_then(|scope| scope.result) {
                        self.assign(result, Rvalue::Use(operand), span);
                    }
                }
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                let scope = self
                    .loops
                    .len()
                    .checked_sub(1)
                    .ok_or("a break outside a loop")?;
                let mut exit = self.loops[scope].exit;
                self.goto_join(&mut exit, span);
                self.loops[scope].exit = exit;
                return Ok(None);
            }
            ExprKind::Continue(cleanup) => {
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                let head = self.loops.last().ok_or("a continue outside a loop")?.head;
                self.goto(head, span);
                return Ok(None);
            }
            ExprKind::Return(value) => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                self.return_value(operand, span);
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
        let owned = self.program.owns(scrutinee.ty);
        for arm in arms {
            supported(&arm.pattern)?;
            if owned && has_alternatives(&arm.pattern) {
                return Err("alternatives over an owned value".into());
            }
            // An arm without a test or guard matches everything left.
            let irrefutable = !refutable(&arm.pattern) && arm.guard.is_none();
            let next = if irrefutable {
                usize::MAX
            } else {
                self.new_block()
            };
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
            // The arm owns the scrutinee: bindings take their parts, and
            // the parts no binding takes are dropped.
            self.consume(scrutinee);
            self.dispose(subject, 0, &arm.pattern, scrutinee.ty, arm.body.span);
            if let Some(value) = self.expr(&arm.body)? {
                self.consume(&arm.body);
                if let Some(temp) = temp {
                    self.assign(temp, Rvalue::Use(value), arm.body.span);
                }
                let mut slots = std::collections::BTreeSet::new();
                crate::ownership::pattern_bindings(&arm.pattern, &mut slots);
                for slot in slots.into_iter().rev() {
                    self.cleanup_resource(self.local_resource(slot), arm.body.span);
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
            Operand::Copy(Place::field(subject, offset, Type::I64))
        }
    }

    /// Continue when `value` equals (or, with `equal` false, differs from)
    /// `constant`; otherwise jump to `fail`.
    fn expect_word(
        &mut self,
        value: Operand,
        constant: i64,
        equal: bool,
        fail: BlockId,
        span: Span,
    ) {
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
    fn test(
        &mut self,
        subject: LocalId,
        offset: usize,
        pattern: &Pattern,
        fail: BlockId,
        span: Span,
    ) {
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
            Pattern::Type { tag, inner, .. } => {
                let word = self.word(subject, offset);
                self.expect_word(word, *tag as i64, true, fail, span);
                self.test(subject, offset + 1, inner, fail, span);
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

    /// The tree path's `dispose_pattern`: after a match, each binding owns
    /// its part of the subject, and each owned part under `_` is dropped.
    fn dispose(
        &mut self,
        subject: LocalId,
        offset: usize,
        pattern: &Pattern,
        ty: Type,
        span: Span,
    ) {
        match pattern {
            Pattern::Any => {
                if self.program.owns(ty) {
                    let place = self.part(subject, offset, ty);
                    self.drop_place(place, span);
                }
            }
            Pattern::Bind(slot) => self.activate_local(*slot, span),
            Pattern::Type { member, inner, .. } => {
                self.dispose(subject, offset + 1, inner, *member, span);
            }
            Pattern::Variant { tag, fields, .. } => {
                let layout = ty
                    .layout()
                    .expect("a variant pattern over a record or enum");
                let types = self.program.enums[layout].variants[*tag].fields.clone();
                for ((field, pattern), ty) in fields.iter().zip(types).rev() {
                    self.dispose(subject, offset + field, pattern, ty, span);
                }
            }
            _ => {}
        }
    }

    /// The words of type `ty` at `offset` in the subject.
    fn part(&self, subject: LocalId, offset: usize, ty: Type) -> Place {
        // A niche payload has the subject's word but not its type.
        let whole = offset == 0 && ty == self.locals[subject].ty;
        if whole {
            Place::local(subject)
        } else {
            Place::field(subject, offset, ty)
        }
    }

    /// Assign the bindings of a pattern that matched.
    fn bind(&mut self, subject: LocalId, offset: usize, pattern: &Pattern, span: Span) {
        match pattern {
            Pattern::Bind(slot) => {
                let place = self.part(subject, offset, self.locals[*slot].ty);
                self.assign(*slot, Rvalue::Use(Operand::Copy(place)), span);
            }
            Pattern::Variant { fields, .. } => {
                for (field, pattern) in fields {
                    self.bind(subject, offset + field, pattern, span);
                }
            }
            Pattern::Type { inner, .. } => self.bind(subject, offset + 1, inner, span),
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
                self.terminate(
                    TerminatorKind::Panic {
                        unwind: self.unwind(),
                    },
                    span,
                );
                return Ok(None);
            }
            Target::StageCompile(_) | Target::StageEntry(_) => {
                return Err(format!("a call to {}", target_name(target)));
            }
            other => {
                self.builtins.push(*other);
                Callee::Builtin(self.builtins.len() - 1)
            }
        };
        let exprs = args.iter().collect::<Vec<_>>();
        let Some(args) = self.operands(&exprs)? else {
            return Ok(None);
        };
        for arg in exprs {
            self.consume(arg);
        }
        Ok(self.emit_call(expr, callee, args))
    }

    /// A call terminator whose result `expr` continues in a new block.
    fn emit_call(&mut self, expr: &Expr, callee: Callee, args: Vec<Operand>) -> Option<Operand> {
        let span = expr.span;
        let destination = self.temp(expr.ty);
        let next = self.new_block();
        self.terminate(
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                unwind: self.unwind(),
            },
            span,
        );
        self.enter(next);
        if expr.ty == Type::Never {
            self.terminate(TerminatorKind::Unreachable, span);
            return None;
        }
        Some(Operand::Move(Place::local(destination)))
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
