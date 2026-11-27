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
        regions: Vec::new(),
        aborts: Vec::new(),
        installs_handlers: crate::native::block_installs_handler(&function.body),
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
    let mut body = Body {
        name: function.name.clone(),
        parameters: function.parameters,
        locals: builder.locals,
        blocks,
        result: function.result,
        builtins: Builtins(builder.builtins),
        coercions: Coercions(builder.coercions),
    };
    super::drop_flags::eliminate(&mut body);
    super::copy_prop::propagate(&mut body);
    Ok(body)
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
    /// `visiting` holds the types being checked: meeting one again (through
    /// a box in a recursive enum) adds nothing, so it counts as covered.
    fn go(program: &Executable, ty: Type, visiting: &mut Vec<Type>) -> bool {
        if scalar(ty)
            || matches!(
                ty,
                Type::Bytes | Type::String | Type::Str | Type::StrMut | Type::Stdin | Type::Stdout
            )
        {
            return true;
        }
        // Function values, objects and opaque handles: words whose
        // operations are builtins or coercions.
        if matches!(
            ty,
            Type::Fn(_)
                | Type::Once(_)
                | Type::Multi(_)
                | Type::DynObj(_)
                | Type::Atomic
                | Type::Arena
                | Type::Allocator
                | Type::AllocatorContext
                | Type::Task(_)
                | Type::Thread(_)
                | Type::Channel(_)
                | Type::ArenaBox(_)
                | Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::GpuBuf(_)
        ) {
            return true;
        }
        let ty = ty.full();
        if visiting.contains(&ty) {
            return true;
        }
        visiting.push(ty);
        let covered = match ty {
            Type::Union(id) => program.unions[id]
                .members
                .iter()
                .all(|member| go(program, *member, visiting)),
            Type::Box(pointee)
            | Type::Vec(pointee)
            | Type::Annotated(pointee, _)
            | Type::Ref(pointee)
            | Type::RefMut(pointee)
            | Type::Slice(pointee)
            | Type::SliceMut(pointee) => go(program, program.pointees[pointee], visiting),
            _ => ty.layout().is_some_and(|id| {
                let definition = &program.enums[id];
                // A runtime-length array's elements are its first variant's
                // fields, as for any record.
                definition.variants.iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| go(program, *field, visiting))
                })
            }),
        };
        visiting.pop();
        covered
    }
    go(program, ty, &mut Vec::new())
}

fn erased(grade: Option<crate::grades::Grade>) -> bool {
    grade.is_some_and(crate::grades::Grade::is_zero)
}

/// The function's frame and calling convention are ones the builder covers.
fn eligible(program: &Executable, function: &Function) -> Result<(), String> {
    if !plain(program, function.result) {
        return Err(format!("a {:?} result", function.result));
    }
    for local in &function.locals {
        if !plain(program, local.ty) {
            return Err(format!("a local of type {:?}", local.ty));
        }
    }
    Ok(())
}

/// A callee the builder may call directly: its arguments and result are
/// passed as plain words.
fn callable(program: &Executable, index: usize) -> Result<(), String> {
    let callee = &program.functions[index];
    if !plain(program, callee.result) {
        return Err(format!("a call returning {:?}", callee.result));
    }
    // A continuation receives its parameters at the slots it names; the
    // arguments are already in its physical order, as on the tree path.
    let slot = |position: usize| {
        callee
            .parameter_slots
            .as_ref()
            .map_or(position, |slots| slots[position])
    };
    if (0..callee.parameters).any(|position| !plain(program, callee.locals[slot(position)].ty)) {
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
        Pattern::Or(alternatives) => alternatives.iter().try_for_each(supported),
        Pattern::Type { inner, .. } => supported(inner),
        Pattern::DynArray { prefix, suffix, .. } => {
            prefix.iter().chain(suffix).try_for_each(supported)
        }
    }
}

fn binds(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| binds(p)),
        Pattern::Type { inner, .. } => binds(inner),
        Pattern::Or(alternatives) => alternatives.iter().any(binds),
        Pattern::DynArray {
            prefix,
            suffix,
            rest_binding,
            ..
        } => rest_binding.is_some() || prefix.iter().chain(suffix).any(binds),
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

/// A lowered `Region`: what `RegionExit` and `TryExit` leave to.
struct Region {
    /// The handler-stack depth on entry, when the function installs
    /// handlers: an exit pops the frames installed inside.
    depth: Option<LocalId>,
    /// Created by the first jump to it.
    exit: Option<BlockId>,
    /// The finish block and the local holding its input.
    finish: Option<(BlockId, LocalId)>,
    /// Receives the region's value.
    result: Option<LocalId>,
}

/// An enclosing `AbortScope`: where its aborts land.
struct Abort {
    label: usize,
    /// Runs the handler on the payload.
    aborted: BlockId,
    /// Receives the payload.
    payload: LocalId,
    payload_ty: Type,
    /// The handler-stack depth before the scope pushed anything.
    depth: Option<LocalId>,
    /// The payload buffer of a declared operation's frame; its address is
    /// the abort word that targets this scope.
    buffer: Option<LocalId>,
}

struct Loop {
    head: BlockId,
    /// The handler-stack depth on entry (see [`Region::depth`]).
    depth: Option<LocalId>,
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
    regions: Vec<Region>,
    aborts: Vec<Abort>,
    /// The function installs dynamic handler frames (the native frame
    /// setup then restores the entry depth on every return).
    installs_handlers: bool,
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
        // A continuation receives its captures and parameters at the
        // enclosing function's slots; the native frame setup puts them there.
        for position in 0..self.function.parameters {
            let slot = self
                .function
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position]);
            // An erased parameter has no words and owns nothing.
            if !self.erased_local(slot) {
                self.activate_local(slot, span);
            }
        }
    }
    /// A grade-zero binding: no storage, so its value is dropped at once.
    fn erased_local(&self, slot: LocalId) -> bool {
        self.function
            .locals
            .get(slot)
            .is_some_and(|local| erased(local.grade))
    }
    /// Drop a value nothing keeps (the initializer of an erased binding).
    fn discard(&mut self, value: Operand, ty: Type, span: Span) {
        if !self.program.owns(ty) {
            return;
        }
        if let Some(place) = value.place() {
            self.drop_place(place, span);
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
    /// Store a temporary owner's value in its declared slot, dropping the
    /// value an earlier loop iteration left there (the tree path's
    /// `store_initialized_owner`).
    fn init_owner(&mut self, slot: LocalId, value: &Expr) -> Result<Option<()>, String> {
        let Some(operand) = self.expr(value)? else {
            return Ok(None);
        };
        self.consume(value);
        let previous = self.local_resource(slot);
        let operand = if self.resource(previous).is_some() {
            let operand = self.settle(operand, value.ty, value.span);
            self.cleanup_resource(previous, value.span);
            operand
        } else {
            operand
        };
        self.assign(slot, Rvalue::Use(operand), value.span);
        self.activate_local(slot, value.span);
        Ok(Some(()))
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
            ExprKind::InitOwner { slot, value } => {
                if self.init_owner(*slot, value)?.is_none() {
                    return Ok(None);
                }
                Place::field(*slot, 0, self.locals[*slot].ty)
            }
            // An element: its checked address in a pointer local, then the
            // element behind it.
            ExprKind::PlaceIndex { base, index, .. } => {
                let element_base = if base.ty.is_slice() {
                    let Some(view) = self.expr(base)? else {
                        return Ok(None);
                    };
                    let view = self.settle(view, base.ty, expr.span);
                    ElementBase::Slice(view)
                } else {
                    let Some(place) = self.place_of(base)? else {
                        return Ok(None);
                    };
                    ElementBase::Stored(place)
                };
                let Some(index) = self.expr(index)? else {
                    return Ok(None);
                };
                let pointer = self.temp(Type::I64);
                self.assign(
                    pointer,
                    Rvalue::ElementAddress(element_base, index),
                    expr.span,
                );
                Place {
                    local: pointer,
                    deref: true,
                    field: Some(Field {
                        offset: 0,
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
                TreeStatement::Let(slot, expr) if self.erased_local(*slot) => {
                    let Some(value) = self.expr(expr)? else {
                        return Ok(None);
                    };
                    self.consume(expr);
                    self.discard(value, expr.ty, expr.span);
                }
                TreeStatement::Let(slot, expr) => {
                    // FND-MIR-DIRECT-INIT: the binding takes the value as
                    // soon as it exists, so nothing can panic while only a
                    // temporary holds it. The temporary needs no resource
                    // (no cleanup copy, no drop flag), and its definition
                    // can write the binding itself.
                    let Some(value) = self.untracked(expr)? else {
                        return Ok(None);
                    };
                    self.initialize(*slot, value, expr.span);
                    self.activate_local(*slot, expr.span);
                    slots.push(*slot);
                }
                // A temporary owner's storage: initialized where it is
                // used (`InitOwner`), cleaned up at the end of this block.
                TreeStatement::Declare(slot) => slots.push(*slot),
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
        let value = self.untracked(expr)?;
        if let Some(value) = value {
            self.track(expr, value);
        }
        Ok(value)
    }

    /// Lower an expression whose owned result a parent takes at once: its
    /// resource is never live, so nothing tracks it.
    fn untracked(&mut self, expr: &Expr) -> Result<Option<Operand>, String> {
        if !plain(self.program, expr.ty) {
            return Err(format!("a value of type {:?}", expr.ty));
        }
        self.expression(expr)
    }

    /// `slot = value` for a new binding. When `value` moves a temporary
    /// defined just before (by the last statement, or by the call that
    /// ends the previous block), that definition writes `slot` instead.
    fn initialize(&mut self, slot: LocalId, value: Operand, span: Span) {
        if let Operand::Move(place) = value
            && place.field.is_none()
            && !place.deref
            && self.locals[place.local].temporary
            && self.locals[place.local].ty == self.locals[slot].ty
            && self.retarget(place.local, slot)
        {
            return;
        }
        self.assign(slot, Rvalue::Use(value), span);
    }

    /// Make the definition of `temp` that immediately precedes the current
    /// point write `slot`. Returns whether there was one.
    fn retarget(&mut self, temp: LocalId, slot: LocalId) -> bool {
        let Some(current) = self.current else {
            return false;
        };
        if let Some(last) = self.blocks[current].statements.last_mut() {
            let StatementKind::Assign(place, _) = &mut last.kind;
            if *place == Place::local(temp) {
                *place = Place::local(slot);
                return true;
            }
            return false;
        }
        // An empty block entered from the call that defines the temporary.
        for block in &mut self.blocks {
            if let Some(Terminator {
                kind:
                    TerminatorKind::Call {
                        destination, next, ..
                    },
                ..
            }) = &mut block.terminator
                && *destination == temp
                && *next == current
            {
                *destination = slot;
                return true;
            }
        }
        false
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
                // A view of a runtime-length array aliases its storage: a
                // borrowed local, or a record field (as on the tree path).
                let stored = match &base.kind {
                    _ if field.is_some() => Some(base),
                    ExprKind::Borrow(_)
                        if base
                            .ty
                            .ref_pointee()
                            .map(|pointee| self.program.pointees[pointee])
                            .and_then(|pointee| pointee.layout())
                            .is_some_and(|id| self.program.enums[id].dynamic_array.is_some()) =>
                    {
                        Some(base)
                    }
                    _ => None,
                };
                if let Some(base) = stored {
                    let place = match &base.kind {
                        ExprKind::Borrow(slot) => Place::field(*slot, 0, self.locals[*slot].ty),
                        _ => match self.place_of(base)? {
                            Some(place) => place,
                            None => return Ok(None),
                        },
                    };
                    let bounds = start.iter().chain(end).map(|bound| &**bound).collect::<Vec<_>>();
                    let Some(values) = self.operands(&bounds)? else {
                        return Ok(None);
                    };
                    let mut values = values.into_iter();
                    let start = start.as_ref().map(|_| values.next().expect("start"));
                    let end = end.as_ref().map(|_| values.next().expect("end"));
                    let temp = self.temp(expr.ty);
                    let view = Rvalue::View {
                        source: ViewSource::DynArray(place),
                        start,
                        end,
                        element: *element,
                        check: *check,
                        text: false,
                    };
                    self.assign(temp, view, span);
                    return Ok(Some(Operand::Move(Place::local(temp))));
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
            ExprKind::InitOwner { slot, value } => {
                if self.init_owner(*slot, value)?.is_none() {
                    return Ok(None);
                }
                Operand::Copy(Place::local(*slot))
            }
            ExprKind::BorrowInit { slot, value } => {
                if self.init_owner(*slot, value)?.is_none() {
                    return Ok(None);
                }
                let temp = self.temp(expr.ty);
                self.assign(temp, Rvalue::Ref(Place::local(*slot)), span);
                Operand::Move(Place::local(temp))
            }
            ExprKind::BoxRead(reference) => {
                let Some(value) = self.expr(reference)? else {
                    return Ok(None);
                };
                let reference_local = self.pointer_local(value, reference.ty, span);
                let pointee = reference
                    .ty
                    .ref_pointee()
                    .map(|pointee| self.program.pointees[pointee])
                    .ok_or("a box read through a non-reference")?;
                let boxed = self.temp(pointee);
                let handle = Operand::Copy(Place::deref(reference_local, 0, pointee));
                self.assign(boxed, Rvalue::Use(handle), span);
                Operand::Copy(Place::deref(boxed, 0, expr.ty))
            }
            ExprKind::BytesAt(bytes, index) => {
                let Some(values) = self.operands(&[bytes, index])? else {
                    return Ok(None);
                };
                let reference = self.pointer_local(values[0], bytes.ty, span);
                let handle = self.temp(Type::Bytes);
                let read = Operand::Copy(Place::deref(reference, 0, Type::Bytes));
                self.assign(handle, Rvalue::Use(read), span);
                let temp = self.temp(expr.ty);
                self.assign(
                    temp,
                    Rvalue::ByteAt(Operand::Copy(Place::local(handle)), values[1]),
                    span,
                );
                Operand::Move(Place::local(temp))
            }
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                let mut children = vec![(&**alloc, false), (&**free, false)];
                children.extend(realloc.as_deref().map(|realloc| (realloc, false)));
                return self.alloc_op(expr, AllocOp::AllocatorNew, &children);
            }
            ExprKind::AllocatorContextNew { value, spec } => {
                let op = AllocOp::ContextNew { spec: *spec };
                return self.alloc_op(expr, op, &[(value, true)]);
            }
            ExprKind::AllocatorContextShare(argument) => {
                return self.alloc_op(expr, AllocOp::ContextShare, &[(argument, false)]);
            }
            ExprKind::ArenaNew => return self.alloc_op(expr, AllocOp::ArenaNew, &[]),
            ExprKind::ArenaNewWith { strategy } => {
                return self.alloc_op(expr, AllocOp::ArenaNewWith, &[(strategy, true)]);
            }
            ExprKind::ArenaAlloc { arena, value } => {
                let children = [(&**arena, true), (&**value, true)];
                return self.alloc_op(expr, AllocOp::ArenaAlloc, &children);
            }
            ExprKind::AllocBoxNew { allocator, value } => {
                let children = [(&**allocator, true), (&**value, true)];
                return self.alloc_op(expr, AllocOp::BoxNew, &children);
            }
            ExprKind::AllocBoxRead(argument) => {
                return self.alloc_op(expr, AllocOp::BoxRead, &[(argument, false)]);
            }
            ExprKind::AllocBoxTake(argument) => {
                return self.alloc_op(expr, AllocOp::BoxTake, &[(argument, true)]);
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                element,
            } => {
                let mut children = vec![(&**allocator, true)];
                children.extend(capacity.as_deref().map(|capacity| (capacity, false)));
                let op = AllocOp::VecNew { element: *element };
                return self.alloc_op(expr, op, &children);
            }
            ExprKind::ArenaBoxRead(argument) => {
                return self.alloc_op(expr, AllocOp::ArenaBoxRead, &[(argument, false)]);
            }
            ExprKind::ArenaBoxTake(argument) => {
                return self.alloc_op(expr, AllocOp::ArenaBoxTake, &[(argument, true)]);
            }
            ExprKind::BoxReuse { owner, payload } | ExprKind::BoxReuseGrow { owner, payload } => {
                let grow = matches!(expr.kind, ExprKind::BoxReuseGrow { .. });
                let children = [(&**owner, true), (&**payload, true)];
                return self.alloc_op(expr, AllocOp::BoxReuse { grow }, &children);
            }
            ExprKind::BoxWrite(reference, value) => {
                let children = [(&**reference, false), (&**value, true)];
                return self.alloc_op(expr, AllocOp::BoxWrite, &children);
            }
            ExprKind::BoxTryNew { value, shape } => {
                let op = AllocOp::BoxTryNew { shape: *shape };
                return self.alloc_op(expr, op, &[(value, true)]);
            }
            ExprKind::BoxTryReuse {
                owner,
                payload,
                shape,
            } => {
                let children = [(&**owner, true), (&**payload, true)];
                let op = AllocOp::BoxTryReuse { shape: *shape };
                return self.alloc_op(expr, op, &children);
            }
            ExprKind::BytesTryWithCapacity { capacity, shape } => {
                let op = AllocOp::BytesTryWithCapacity { shape: *shape };
                return self.alloc_op(expr, op, &[(capacity, true)]);
            }
            ExprKind::AllocBoxTryNew {
                allocator,
                value,
                shape,
            } => {
                let children = [(&**allocator, true), (&**value, true)];
                let op = AllocOp::AllocBoxTryNew { shape: *shape };
                return self.alloc_op(expr, op, &children);
            }
            ExprKind::ArenaTryAlloc {
                arena,
                value,
                shape,
            } => {
                let children = [(&**arena, true), (&**value, true)];
                let op = AllocOp::ArenaTryAlloc { shape: *shape };
                return self.alloc_op(expr, op, &children);
            }
            ExprKind::Erased(ty) => Operand::Constant(0, *ty),
            ExprKind::StructEq {
                left,
                right,
                negated,
            } => {
                let negated = *negated;
                let children = [(&**left, false), (&**right, false)];
                return self.operation(expr, &children, |values| {
                    Rvalue::StructEq(values[0], values[1], negated)
                });
            }
            ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
                grow,
                capabilities,
            } => {
                let functions = callbacks
                    .iter()
                    .map(|callback| match &callback.kind {
                        ExprKind::FnValue { function, captures } if captures.is_empty() => {
                            Some(*function)
                        }
                        _ => None,
                    })
                    .collect();
                let op = MapOp {
                    source: *source,
                    target: *target,
                    grow: *grow,
                    functions,
                };
                // Operands: the vector, the callbacks, then each callback's
                // capabilities in order.
                let mut children = vec![(&**vector, true)];
                children.extend(callbacks.iter().map(|callback| (callback, true)));
                children.extend(capabilities.iter().map(|capability| (capability, true)));
                return self.operation(expr, &children, |values| Rvalue::Map(op, values));
            }
            ExprKind::DynArrayNew { element, capacity } => {
                let op = ArrayOp::New {
                    element: *element,
                    capacity: *capacity,
                };
                return self.array_op(expr, op, &[]);
            }
            ExprKind::DynArrayPush {
                array,
                value,
                element,
                capacity,
            } => {
                let op = ArrayOp::Push {
                    element: *element,
                    capacity: *capacity,
                };
                return self.array_op(expr, op, &[(array, true), (value, true)]);
            }
            ExprKind::DynArrayFill {
                length,
                value,
                element,
                capacity,
                ..
            } => {
                let op = ArrayOp::Fill {
                    element: *element,
                    capacity: *capacity,
                };
                return self.array_op(expr, op, &[(length, true), (value, true)]);
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                element,
                capacity,
            } => {
                let op = ArrayOp::Set {
                    element: *element,
                    capacity: *capacity,
                };
                let children = [(&**array, true), (&**index, true), (&**value, true)];
                return self.array_op(expr, op, &children);
            }
            ExprKind::DynArrayPop {
                array,
                element,
                capacity,
            } => {
                let op = ArrayOp::Pop {
                    element: *element,
                    capacity: *capacity,
                };
                return self.array_op(expr, op, &[(array, true)]);
            }
            ExprKind::DynArrayEqual {
                left,
                right,
                element,
                capacity,
                negate,
            } => {
                let op = ArrayOp::Equal {
                    element: *element,
                    capacity: *capacity,
                    negate: *negate,
                };
                return self.array_op(expr, op, &[(left, false), (right, false)]);
            }
            ExprKind::AbortScope {
                label,
                body,
                handler,
                operation,
                capability,
            } => {
                return self.abort_scope(expr, *label, body, handler, *operation, *capability);
            }
            ExprKind::AbortExit {
                label,
                value,
                cleanup,
                ..
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                let target = self.abort_target(*label)?;
                let (aborted, payload, depth) = (target.aborted, target.payload, target.depth);
                self.restore_depth(depth, span);
                self.assign(payload, Rvalue::Use(operand), span);
                self.goto(aborted, span);
                return Ok(None);
            }
            ExprKind::AbortPerform {
                operation,
                value,
                capability,
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                let op = RuntimeOp::AbortRaise {
                    operation: *operation,
                };
                match capability {
                    // A zero capability (no scope supplied one) finds the
                    // frame on the dynamic stack.
                    Some(capability) => {
                        let Some(target) = self.expr(capability)? else {
                            return Ok(None);
                        };
                        let dynamic = self.new_block();
                        let direct = self.new_block();
                        let join = self.new_block();
                        self.terminate(
                            TerminatorKind::Switch {
                                value: target,
                                targets: vec![(0, dynamic)],
                                otherwise: direct,
                            },
                            span,
                        );
                        self.enter(dynamic);
                        self.runtime(op, vec![operand], Type::Unit, span);
                        self.goto(join, span);
                        self.enter(direct);
                        self.runtime(
                            RuntimeOp::AbortRaiseAt,
                            vec![target, operand],
                            Type::Unit,
                            span,
                        );
                        self.goto(join, span);
                        self.enter(join);
                    }
                    None => {
                        self.runtime(op, vec![operand], Type::Unit, span);
                    }
                }
                self.cleanup_all(span);
                self.terminate(TerminatorKind::Abort, span);
                return Ok(None);
            }
            ExprKind::AbortCall {
                call,
                exits,
                propagates,
            } => return self.abort_call(call, exits, *propagates),
            ExprKind::DynamicPerform {
                operation,
                payload,
                resume,
                handler,
                cell,
            } => {
                // FND-HANDLERS-ONE-CELLS: a third operand names the
                // activation's cell (zero: search the stack).
                let mut operands = vec![&**payload, &**resume];
                operands.extend(cell.as_deref());
                let Some(values) = self.operands(&operands)? else {
                    return Ok(None);
                };
                self.consume(payload);
                self.consume(resume);
                let op = RuntimeOp::Perform {
                    operation: *operation,
                    handler: *handler,
                };
                let result = self.runtime(op, values, expr.ty, span);
                Operand::Move(Place::local(result))
            }
            ExprKind::ContinuationScope { body } => {
                let mark = self.runtime(RuntimeOp::ContinuationMark, vec![], Type::I64, span);
                let Some(value) = self.block(body)? else {
                    return Ok(None);
                };
                let value = self.settle(value, expr.ty, span);
                let mark = Operand::Copy(Place::local(mark));
                self.runtime(RuntimeOp::ContinuationRestore, vec![mark], Type::Unit, span);
                value
            }
            ExprKind::HandlerPush {
                operation,
                handler,
                body,
                reusable,
                cell,
            } => {
                let Some(callable) = self.expr(handler)? else {
                    return Ok(None);
                };
                self.consume(handler);
                // A noncapturing handler owns nothing, so its cell needs no
                // runtime frame: no perform searches frames, and nothing is
                // dropped when the activation ends (FND-HANDLERS-ONE-DELETE).
                let framed = !matches!(handler.ty, Type::Fn(_));
                let op = if framed {
                    RuntimeOp::HandlerPush {
                        operation: *operation,
                        reusable: *reusable,
                    }
                } else {
                    RuntimeOp::HandlerCell
                };
                // The push answers the activation's cell.
                let pushed = self.runtime(op, vec![callable], Type::I64, span);
                if let Some(cell) = cell {
                    self.assign(
                        *cell,
                        Rvalue::Use(Operand::Copy(Place::local(pushed))),
                        span,
                    );
                }
                let Some(value) = self.block(body)? else {
                    return Ok(None);
                };
                let value = self.settle(value, expr.ty, span);
                if framed {
                    self.runtime(RuntimeOp::HandlerPop, vec![], Type::Unit, span);
                }
                value
            }
            ExprKind::TaskSpawn {
                body,
                result,
                obligation,
                parallel,
            } => {
                let op = TaskOp::Spawn {
                    result: *result,
                    obligation: *obligation,
                    parallel: *parallel,
                };
                return self.task(expr, op, Some(body), true);
            }
            ExprKind::TaskScope {
                body,
                failure,
                catch,
                parallel,
                ..
            } => {
                let op = TaskOp::Scope {
                    failure: *failure,
                    catch: *catch,
                    parallel: *parallel,
                };
                return self.task(expr, op, Some(body), true);
            }
            ExprKind::TaskYield => return self.task(expr, TaskOp::Yield, None, false),
            ExprKind::TaskCheckCancel => return self.task(expr, TaskOp::CheckCancel, None, false),
            ExprKind::TaskCancel(reference) => {
                return self.task(expr, TaskOp::Cancel, Some(reference), false);
            }
            ExprKind::TaskJoin {
                task,
                exit,
                parallel,
                ..
            } => {
                let op = TaskOp::Join {
                    exit: *exit,
                    parallel: *parallel,
                };
                return self.task(expr, op, Some(task), true);
            }
            ExprKind::Region { body, finish } => return self.region(expr, body, finish.as_deref()),
            ExprKind::RegionExit {
                value,
                finish,
                cleanup,
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                self.leave_region(operand, *finish, span)?;
                return Ok(None);
            }
            ExprKind::TryExit {
                value,
                input,
                output,
                cleanup,
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                let subject = self.temp(value.ty);
                self.assign(subject, Rvalue::Use(operand), span);
                let (_, input_local) = self
                    .regions
                    .last()
                    .and_then(|region| region.finish)
                    .ok_or("a `?` exit outside a region with a finish")?;
                let finish_ty = self.locals[input_local].ty;
                let layout = finish_ty
                    .layout()
                    .ok_or("a `?` exit to a non-enum finish")?;
                let ok = self.new_block();
                let failed = self.new_block();
                self.terminate(
                    TerminatorKind::Switch {
                        value: self.word(subject, 0),
                        targets: vec![(input.ok_tag as i64, ok)],
                        otherwise: failed,
                    },
                    span,
                );
                // The error goes to the caller's continuation (the finish).
                self.enter(failed);
                let error = Operand::Copy(Place::field(subject, 1, input.error));
                let returned = self.temp(finish_ty);
                self.assign(
                    returned,
                    Rvalue::Aggregate(Type::Enum(layout), output.err_tag, vec![error]),
                    span,
                );
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                self.leave_region(Operand::Move(Place::local(returned)), true, span)?;
                self.enter(ok);
                Operand::Copy(Place::field(subject, 1, input.ok))
            }
            ExprKind::Try {
                value,
                input,
                output,
            } => {
                let Some(operand) = self.expr(value)? else {
                    return Ok(None);
                };
                self.consume(value);
                let subject = self.temp(value.ty);
                self.assign(subject, Rvalue::Use(operand), span);
                let result = self.function.result;
                let layout = result
                    .layout()
                    .ok_or("a `?` in a function without a result enum")?;
                let ok = self.new_block();
                let failed = self.new_block();
                self.terminate(
                    TerminatorKind::Switch {
                        value: self.word(subject, 0),
                        targets: vec![(input.ok_tag as i64, ok)],
                        otherwise: failed,
                    },
                    span,
                );
                // The error propagates: the function returns it in its own
                // result shape, after dropping what is live.
                self.enter(failed);
                let error = Operand::Copy(Place::field(subject, 1, input.error));
                let returned = self.temp(result);
                self.assign(
                    returned,
                    Rvalue::Aggregate(Type::Enum(layout), output.err_tag, vec![error]),
                    span,
                );
                self.return_value(Operand::Move(Place::local(returned)), span);
                self.enter(ok);
                Operand::Copy(Place::field(subject, 1, input.ok))
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
                if self.erased_local(*slot) {
                    self.discard(value, replacement.ty, span);
                    return Ok(Some(Self::no_value(expr.ty)));
                }
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
                let depth = self.save_depth(span);
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
                    depth,
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
                let depth = self.save_depth(span);
                let head = self.new_block();
                self.goto(head, span);
                self.enter(head);
                let result = self.result_temp(expr.ty);
                self.loops.push(Loop {
                    head,
                    depth,
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
                self.restore_depth(self.loops[scope].depth, span);
                let mut exit = self.loops[scope].exit;
                self.goto_join(&mut exit, span);
                self.loops[scope].exit = exit;
                return Ok(None);
            }
            ExprKind::Continue(cleanup) => {
                for id in cleanup {
                    self.cleanup_resource(Some(*id), span);
                }
                let scope = self.loops.last().ok_or("a continue outside a loop")?;
                let (head, depth) = (scope.head, scope.depth);
                self.restore_depth(depth, span);
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

    /// An allocator or arena operation on its children, consuming those
    /// marked `true` (the ones the tree path's arm consumes).
    fn alloc_op(
        &mut self,
        expr: &Expr,
        op: AllocOp,
        children: &[(&Expr, bool)],
    ) -> Result<Option<Operand>, String> {
        self.operation(expr, children, |values| Rvalue::Alloc(op, values))
    }

    /// A runtime-length array operation, as `alloc_op`.
    fn array_op(
        &mut self,
        expr: &Expr,
        op: ArrayOp,
        children: &[(&Expr, bool)],
    ) -> Result<Option<Operand>, String> {
        self.operation(expr, children, |values| Rvalue::Array(op, values))
    }

    /// The rvalue `rvalue` makes of the values of `children` into a
    /// temporary, consuming the children marked `true`.
    fn operation(
        &mut self,
        expr: &Expr,
        children: &[(&Expr, bool)],
        rvalue: impl FnOnce(Vec<Operand>) -> Rvalue,
    ) -> Result<Option<Operand>, String> {
        let exprs = children.iter().map(|(child, _)| *child).collect::<Vec<_>>();
        let Some(values) = self.operands(&exprs)? else {
            return Ok(None);
        };
        for (child, consumed) in children {
            if *consumed {
                self.consume(child);
            }
        }
        let temp = self.temp(expr.ty);
        self.assign(temp, rvalue(values), expr.span);
        Ok(Some(Operand::Move(Place::local(temp))))
    }

    /// The innermost enclosing abort scope with `label`.
    fn abort_target(&self, label: usize) -> Result<&Abort, String> {
        self.aborts
            .iter()
            .rev()
            .find(|scope| scope.label == label)
            .ok_or_else(|| "an abort outside its scope".into())
    }

    /// An `AbortScope`: the body runs with an abort frame for `operation`
    /// installed; an abort to it lands in a block that runs `handler` on
    /// the payload, as on the tree path.
    fn abort_scope(
        &mut self,
        expr: &Expr,
        label: usize,
        body: &crate::executable::Block,
        handler: &Expr,
        operation: Option<usize>,
        capability: Option<usize>,
    ) -> Result<Option<Operand>, String> {
        let span = expr.span;
        let (Type::Fn(id) | Type::Once(id)) = handler.ty else {
            return Err("an abortive handler that is not a function value".into());
        };
        let payload_ty = self.program.function_types[id].parameters[0];
        if !plain(self.program, payload_ty) {
            return Err(format!("an abort payload of type {payload_ty:?}"));
        }
        let aborted = self.new_block();
        let payload = self.temp(payload_ty);
        let depth = self.save_depth(span);
        // An abort can leave a multishot `handle` without its
        // continuation-stack restore; the landing restores instead.
        let mark = self
            .program
            .functions
            .iter()
            .any(|function| function.shared_environment)
            .then(|| self.runtime(RuntimeOp::ContinuationMark, vec![], Type::I64, span));
        let buffer = operation.map(|operation| {
            let words = self.program.width(payload_ty);
            let buffer = self.runtime(RuntimeOp::AbortBuffer { words }, vec![], Type::I64, span);
            let push = RuntimeOp::AbortHandlerPush { operation };
            self.runtime(
                push,
                vec![Operand::Copy(Place::local(buffer))],
                Type::Unit,
                span,
            );
            if let Some(capability) = capability {
                self.assign(
                    capability,
                    Rvalue::Use(Operand::Copy(Place::local(buffer))),
                    span,
                );
            }
            buffer
        });
        let result = self.result_temp(expr.ty);
        let mut exit = None;
        self.aborts.push(Abort {
            label,
            aborted,
            payload,
            payload_ty,
            depth,
            buffer,
        });
        let finished = self.block(body);
        self.aborts.pop();
        if let Some(value) = finished? {
            if buffer.is_some() {
                self.runtime(RuntimeOp::HandlerPop, vec![], Type::Unit, span);
            }
            if let Some(result) = result {
                self.assign(result, Rvalue::Use(value), span);
            }
            self.goto_join(&mut exit, span);
        }
        self.enter(aborted);
        if let Some(mark) = mark {
            let mark = Operand::Copy(Place::local(mark));
            self.runtime(RuntimeOp::ContinuationRestore, vec![mark], Type::Unit, span);
        }
        if let Some(callable) = self.expr(handler)? {
            self.consume(handler);
            let call = Expr {
                kind: ExprKind::Constant(0),
                ty: expr.ty,
                span,
                resource: None,
            };
            let payload = Operand::Move(Place::local(payload));
            if let Some(value) = self.emit_call(&call, Callee::Indirect(callable), vec![payload]) {
                if let Some(result) = result {
                    self.assign(result, Rvalue::Use(value), span);
                }
                self.goto_join(&mut exit, span);
            }
        }
        let Some(exit) = exit else {
            return Ok(None);
        };
        self.enter(exit);
        Ok(Some(Self::result(result, expr.ty)))
    }

    /// A call whose callee may abort to an enclosing scope: after it, a set
    /// abort word is dispatched to the scope it names, or keeps travelling.
    fn abort_call(
        &mut self,
        call: &Expr,
        exits: &[(usize, Vec<usize>)],
        propagates: bool,
    ) -> Result<Option<Operand>, String> {
        let span = call.span;
        let Some(value) = self.expr(call)? else {
            return Ok(None);
        };
        let word = self.runtime(RuntimeOp::AbortWord, vec![], Type::I64, span);
        let dispatch = self.new_block();
        let normal = self.new_block();
        self.terminate(
            TerminatorKind::Switch {
                value: Operand::Copy(Place::local(word)),
                targets: vec![(0, normal)],
                otherwise: dispatch,
            },
            span,
        );
        self.enter(dispatch);
        // The call's result words are meaningless on this path.
        self.consume(call);
        for (label, cleanup) in exits {
            let target = self.abort_target(*label)?;
            let Some(buffer) = target.buffer else {
                continue;
            };
            let (aborted, payload, payload_ty, depth) = (
                target.aborted,
                target.payload,
                target.payload_ty,
                target.depth,
            );
            let same = self.temp(Type::Bool);
            self.assign(
                same,
                Rvalue::Binary(
                    BinOp::Eq,
                    Operand::Copy(Place::local(word)),
                    Operand::Copy(Place::local(buffer)),
                ),
                span,
            );
            let hit = self.new_block();
            let miss = self.new_block();
            self.terminate(
                TerminatorKind::Switch {
                    value: Operand::Copy(Place::local(same)),
                    targets: vec![(0, miss)],
                    otherwise: hit,
                },
                span,
            );
            self.enter(hit);
            self.runtime(RuntimeOp::AbortClear, vec![], Type::Unit, span);
            for id in cleanup {
                self.cleanup_resource(Some(*id), span);
            }
            self.restore_depth(depth, span);
            let landed = Operand::Copy(Place::deref(buffer, 0, payload_ty));
            self.assign(payload, Rvalue::Use(landed), span);
            self.goto(aborted, span);
            self.enter(miss);
        }
        if propagates || self.program.uses_unwinding {
            // A foreign abort, or a panic unwinding through.
            self.cleanup_all(span);
            self.terminate(TerminatorKind::Abort, span);
        } else {
            self.terminate(TerminatorKind::Unreachable, span);
        }
        self.enter(normal);
        Ok(Some(value))
    }

    /// A handler- or continuation-stack operation; the local holding its
    /// result.
    fn runtime(&mut self, op: RuntimeOp, operands: Vec<Operand>, ty: Type, span: Span) -> LocalId {
        let temp = self.temp(ty);
        self.assign(temp, Rvalue::Runtime(op, operands), span);
        temp
    }
    /// The handler-stack depth on entry to a loop or region, when the
    /// function installs handlers.
    fn save_depth(&mut self, span: Span) -> Option<LocalId> {
        self.installs_handlers
            .then(|| self.runtime(RuntimeOp::HandlerDepth, vec![], Type::I64, span))
    }
    /// Pop the handler frames installed since `depth` was saved.
    fn restore_depth(&mut self, depth: Option<LocalId>, span: Span) {
        if let Some(depth) = depth {
            let depth = Operand::Copy(Place::local(depth));
            self.runtime(RuntimeOp::HandlerRestore, vec![depth], Type::Unit, span);
        }
    }

    /// A task operation on at most one operand, which it consumes when
    /// `consumes` (as the tree path's arm does).
    fn task(
        &mut self,
        expr: &Expr,
        op: TaskOp,
        operand: Option<&Expr>,
        consumes: bool,
    ) -> Result<Option<Operand>, String> {
        let mut operands = Vec::new();
        if let Some(operand) = operand {
            let Some(value) = self.expr(operand)? else {
                return Ok(None);
            };
            if consumes {
                self.consume(operand);
            }
            operands.push(value);
        }
        let temp = self.temp(expr.ty);
        self.assign(temp, Rvalue::Task(op, operands), expr.span);
        if expr.ty == Type::Never {
            self.terminate(TerminatorKind::Unreachable, expr.span);
            return Ok(None);
        }
        Ok(Some(Operand::Move(Place::local(temp))))
    }

    /// A `Region`: its body may leave early through `RegionExit` and
    /// `TryExit`; a value that reaches the finish is passed to the finish
    /// callable, whose result is the region's.
    fn region(
        &mut self,
        expr: &Expr,
        body: &crate::executable::Block,
        finish: Option<&Expr>,
    ) -> Result<Option<Operand>, String> {
        let span = expr.span;
        let finish_input = match finish {
            Some(finish) => {
                let (Type::Fn(id) | Type::Once(id) | Type::Multi(id)) = finish.ty else {
                    return Err("a region finish that is not a function value".into());
                };
                let input = self.program.function_types[id].parameters[0];
                if !plain(self.program, input) {
                    return Err(format!("a region finish taking {input:?}"));
                }
                let block = self.new_block();
                Some((block, self.temp(input)))
            }
            None => None,
        };
        let result = self.result_temp(expr.ty);
        let depth = self.save_depth(span);
        self.regions.push(Region {
            depth,
            exit: None,
            finish: finish_input,
            result,
        });
        let finished = self.block(body);
        let finished = match finished {
            Ok(value) => value,
            Err(error) => {
                self.regions.pop();
                return Err(error);
            }
        };
        if let Some(value) = finished {
            let into_finish = finish_input.is_some();
            if let Err(error) = self.leave_region(value, into_finish, span) {
                self.regions.pop();
                return Err(error);
            }
        }
        let region = self.regions.pop().expect("the region's scope");
        let mut exit = region.exit;
        if let (Some((block, input)), Some(finish)) = (finish_input, finish) {
            self.enter(block);
            let Some(callable) = self.expr(finish)? else {
                return Ok(exit.map(|exit| {
                    self.enter(exit);
                    Self::result(result, expr.ty)
                }));
            };
            self.consume(finish);
            let call = Expr {
                kind: ExprKind::Constant(0),
                ty: expr.ty,
                span,
                resource: None,
            };
            let input = Operand::Move(Place::local(input));
            if let Some(value) = self.emit_call(&call, Callee::Indirect(callable), vec![input]) {
                if let Some(result) = result {
                    self.assign(result, Rvalue::Use(value), span);
                }
                self.goto_join(&mut exit, span);
            }
        }
        let Some(exit) = exit else {
            return Ok(None);
        };
        self.enter(exit);
        Ok(Some(Self::result(result, expr.ty)))
    }

    /// Leave the innermost region with `value`: to its finish, or to its
    /// exit with the value as the region's result.
    fn leave_region(&mut self, value: Operand, finish: bool, span: Span) -> Result<(), String> {
        let depth = self
            .regions
            .len()
            .checked_sub(1)
            .ok_or("a region exit outside a region")?;
        self.restore_depth(self.regions[depth].depth, span);
        if finish {
            let (block, input) = self.regions[depth]
                .finish
                .ok_or("a finish exit without a finish")?;
            self.assign(input, Rvalue::Use(value), span);
            self.goto(block, span);
            return Ok(());
        }
        if let Some(result) = self.regions[depth].result {
            self.assign(result, Rvalue::Use(value), span);
        }
        let mut exit = self.regions[depth].exit;
        self.goto_join(&mut exit, span);
        self.regions[depth].exit = exit;
        Ok(())
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
        // A borrowed scrutinee (a `&DynArray` under an array pattern): the
        // patterns test a copy of the array, and element names bind
        // addresses in it, as on the tree path.
        let borrowed = match scrutinee.ty {
            Type::Ref(pointee) | Type::RefMut(pointee) => {
                let reference = self.pointer_local(value, scrutinee.ty, scrutinee.span);
                Some((reference, self.program.pointees[pointee]))
            }
            _ => None,
        };
        // Arms may assign the scrutinee's local; test a copy.
        let subject = match borrowed {
            Some((reference, array)) => {
                let subject = self.temp(array);
                let words = Operand::Copy(Place::deref(reference, 0, array));
                self.assign(subject, Rvalue::Use(words), scrutinee.span);
                subject
            }
            None => {
                let subject = self.temp(scrutinee.ty);
                self.assign(subject, Rvalue::Use(value), scrutinee.span);
                subject
            }
        };
        let temp = self.result_temp(expr.ty);
        let mut join = None;
        for arm in arms {
            supported(&arm.pattern)?;
            // An arm without a test or guard matches everything left.
            let irrefutable = !refutable(&arm.pattern) && arm.guard.is_none();
            let next = if irrefutable {
                usize::MAX
            } else {
                self.new_block()
            };
            self.test(subject, 0, &arm.pattern, next, arm.body.span);
            match borrowed {
                Some((reference, _)) => {
                    self.bind_borrowed(subject, reference, &arm.pattern, arm.body.span);
                }
                None => self.bind(subject, 0, &arm.pattern, arm.body.span),
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
            // The arm owns the scrutinee: bindings take their parts, and
            // the parts no binding takes are dropped.
            self.consume(scrutinee);
            if borrowed.is_none() {
                self.dispose(subject, 0, &arm.pattern, scrutinee.ty, arm.body.span);
            }
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
            Pattern::DynArray {
                element,
                prefix,
                suffix,
                rest,
                ..
            } => {
                let width = self.program.width(*element);
                let length = self.word(subject, offset);
                let required = (prefix.len() + suffix.len()) as i64;
                if *rest {
                    let enough = self.temp(Type::Bool);
                    let at_least = Rvalue::Binary(
                        BinOp::Ge,
                        length,
                        Operand::Constant(required, Type::I64),
                    );
                    self.assign(enough, at_least, span);
                    let enough = Operand::Move(Place::local(enough));
                    self.expect_word(enough, 0, false, fail, span);
                } else {
                    self.expect_word(length, required, true, fail, span);
                }
                for (index, pattern) in prefix.iter().enumerate() {
                    self.test(subject, offset + 1 + index * width, pattern, fail, span);
                }
                for (index, part) in suffix.iter().enumerate() {
                    if refutable(part) {
                        let item = self.suffix_item(subject, offset, pattern, index, span);
                        self.test(item, 0, part, fail, span);
                    }
                }
            }
        }
    }

    /// The runtime-length array of `element`s with `capacity` slots at
    /// `offset` in the subject.
    fn array_part(&self, subject: LocalId, offset: usize, element: Type, capacity: usize) -> Place {
        let matches = |ty: Type| {
            ty.layout()
                .is_some_and(|id| self.program.enums[id].dynamic_array == Some((element, capacity)))
        };
        let whole = self.locals[subject].ty;
        if offset == 0 && matches(whole) {
            return Place::local(subject);
        }
        // Every array type of this element and capacity has one layout.
        let id = (0..self.program.enums.len())
            .find(|id| self.program.enums[*id].dynamic_array == Some((element, capacity)))
            .expect("the array pattern's type");
        Place::field(subject, offset, Type::Enum(id))
    }

    /// A temporary holding suffix element `index` of the array at `offset`
    /// in the subject, matched by the array pattern `pattern`.
    fn suffix_item(
        &mut self,
        subject: LocalId,
        offset: usize,
        pattern: &Pattern,
        index: usize,
        span: Span,
    ) -> LocalId {
        let Pattern::DynArray {
            element,
            capacity,
            prefix,
            suffix,
            ..
        } = pattern
        else {
            unreachable!("an array pattern");
        };
        let item = self.temp(*element);
        let op = ArrayOp::Suffix {
            element: *element,
            capacity: *capacity,
            prefix: prefix.len(),
            suffix: suffix.len(),
            index,
        };
        let array = Operand::Copy(self.array_part(subject, offset, *element, *capacity));
        self.assign(item, Rvalue::Array(op, vec![array]), span);
        item
    }

    /// Bind an array pattern over a borrowed array: element names receive
    /// slot addresses, the rest a view, and other element patterns bind
    /// from the copy in `subject`. Other patterns bind nothing, as on the
    /// tree path.
    fn bind_borrowed(
        &mut self,
        subject: LocalId,
        reference: LocalId,
        pattern: &Pattern,
        span: Span,
    ) {
        let Pattern::DynArray {
            element,
            prefix,
            suffix,
            rest_binding,
            ..
        } = pattern
        else {
            return;
        };
        let width = self.program.width(*element);
        let behind = Operand::Copy(Place::local(reference));
        for (index, part) in prefix.iter().enumerate() {
            let offset = 1 + index * width;
            match part {
                Pattern::Bind(slot) => {
                    let place = Place::deref(reference, offset, *element);
                    self.assign(*slot, Rvalue::Ref(place), span);
                }
                part => self.bind(subject, offset, part, span),
            }
        }
        for (index, part) in suffix.iter().enumerate() {
            match part {
                Pattern::Bind(slot) => {
                    let op = ArrayOp::SuffixAddress {
                        element: *element,
                        suffix: suffix.len(),
                        index,
                    };
                    self.assign(*slot, Rvalue::Array(op, vec![behind]), span);
                }
                part if binds(part) => {
                    let item = self.suffix_item(subject, 0, pattern, index, span);
                    self.bind(item, 0, part, span);
                }
                _ => {}
            }
        }
        if let Some(slot) = rest_binding {
            let op = ArrayOp::RestView {
                element: *element,
                prefix: prefix.len(),
                suffix: suffix.len(),
            };
            self.assign(*slot, Rvalue::Array(op, vec![behind]), span);
        }
    }

    /// Run `action` for the first alternative that matches the subject (the
    /// whole pattern matched, so one does), as the tree path does when it
    /// binds or disposes through an or-pattern.
    fn each_alternative(
        &mut self,
        subject: LocalId,
        offset: usize,
        alternatives: &[Pattern],
        span: Span,
        action: impl Fn(&mut Self, &Pattern),
    ) {
        let join = self.new_block();
        for alternative in alternatives {
            let next = self.new_block();
            self.test(subject, offset, alternative, next, span);
            action(self, alternative);
            self.goto(join, span);
            self.enter(next);
        }
        self.terminate(TerminatorKind::Unreachable, span);
        self.enter(join);
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
            Pattern::Or(alternatives) if self.program.owns(ty) || binds(pattern) => {
                self.each_alternative(subject, offset, alternatives, span, |builder, p| {
                    builder.dispose(subject, offset, p, ty, span);
                });
            }
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
            Pattern::DynArray {
                element,
                capacity,
                prefix,
                suffix,
                rest_binding,
                ..
            } => {
                let width = self.program.width(*element);
                for (index, part) in prefix.iter().enumerate() {
                    self.bind(subject, offset + 1 + index * width, part, span);
                }
                for (index, part) in suffix.iter().enumerate() {
                    if binds(part) {
                        let item = self.suffix_item(subject, offset, pattern, index, span);
                        self.bind(item, 0, part, span);
                    }
                }
                if let Some(slot) = rest_binding {
                    let op = ArrayOp::Rest {
                        element: *element,
                        capacity: *capacity,
                        prefix: prefix.len(),
                        suffix: suffix.len(),
                    };
                    let array = Operand::Copy(self.array_part(subject, offset, *element, *capacity));
                    self.assign(*slot, Rvalue::Array(op, vec![array]), span);
                }
            }
            Pattern::Or(alternatives) if binds(pattern) => {
                self.each_alternative(subject, offset, alternatives, span, |builder, p| {
                    builder.bind(subject, offset, p, span);
                });
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
                debug_assert!(args.is_empty(), "panic() takes no arguments");
                self.terminate(
                    TerminatorKind::Panic {
                        unwind: self.unwind(),
                    },
                    span,
                );
                return Ok(None);
            }
            other => {
                self.builtins.push(*other);
                Callee::Builtin {
                    index: self.builtins.len() - 1,
                    hint: CallHint::None,
                }
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
