//! Structural checks of a built [`Body`]: every block, local and parameter
//! it names exists, operands have the types their operations need, and a
//! returned value has the function's result type. Fields lie inside their
//! local, and aggregates have their variant's fields.

use super::*;

/// The same type, or the same record or enum with other variant refinements.
fn compatible(a: Type, b: Type) -> bool {
    a == b || a == Type::Never || (a.layout().is_some() && a.layout() == b.layout())
}

pub(crate) fn verify(program: &Executable, body: &Body) -> Result<(), String> {
    if body.parameters > body.locals.len() {
        return Err("more parameters than locals".into());
    }
    if body.blocks.is_empty() {
        return Err("a body without blocks".into());
    }
    let block = |target: BlockId| {
        if target < body.blocks.len() {
            Ok(())
        } else {
            Err(format!("bb{target} does not exist"))
        }
    };
    let local = |local: LocalId| {
        if local < body.locals.len() {
            Ok(())
        } else {
            Err(format!("_{local} does not exist"))
        }
    };
    let place = |place: Place| {
        local(place.local)?;
        let base = body.locals[place.local].ty;
        let base = if place.deref {
            let Some(field) = place.field else {
                return Err(format!("*_{} names no field", place.local));
            };
            if base == Type::I64 {
                // A computed element address: the field names what is there.
                return Ok(());
            }
            // A reference, or a box: both point at their pointee.
            let pointee = match base {
                Type::Box(pointee) => Some(pointee),
                other => other.ref_pointee(),
            }
            .ok_or_else(|| format!("*_{} dereferences a {base:?}", place.local))?;
            let _ = field;
            program.pointees[pointee]
        } else {
            base
        };
        if let Some(field) = place.field {
            let width = program.width(base);
            if field.offset + program.width(field.ty) > width {
                return Err(format!(
                    "_{}.{} reads past the {width} words of its value",
                    place.local, field.offset
                ));
            }
        }
        Ok(())
    };
    let operand = |operand: Operand| match operand {
        Operand::Copy(target) | Operand::Move(target) => place(target),
        Operand::Constant(..) => Ok(()),
    };
    for (index, data) in body.blocks.iter().enumerate() {
        let here = |e: String| format!("bb{index}: {e}");
        if let Some(unwind) = data.unwind {
            block(unwind).map_err(here)?;
        }
        for statement in &data.statements {
            let StatementKind::Assign(target, rvalue) = &statement.kind;
            place(*target).map_err(here)?;
            let target_ty = body.place_ty(*target);
            let ty = match rvalue {
                Rvalue::Use(value) => {
                    operand(*value).map_err(here)?;
                    body.operand_ty(*value)
                }
                Rvalue::Unary(_, value) => {
                    operand(*value).map_err(here)?;
                    body.operand_ty(*value)
                }
                Rvalue::Int(op, _, target, values) => {
                    if int_op_name(*op).is_none() {
                        return Err(here(format!(
                            "the integer builtin {op:?} has no one-word result"
                        )));
                    }
                    for value in values {
                        operand(*value).map_err(here)?;
                    }
                    Type::int(*target)
                }
                Rvalue::Aggregate(ty, tag, values) => {
                    let layout = ty
                        .layout()
                        .ok_or_else(|| here(format!("an aggregate of {ty:?}")))?;
                    let variant = program.enums[layout]
                        .variants
                        .get(*tag)
                        .ok_or_else(|| here(format!("variant {tag} of {ty:?} does not exist")))?;
                    if variant.fields.len() != values.len() {
                        return Err(here(format!(
                            "variant {tag} of {ty:?} has {} fields, given {}",
                            variant.fields.len(),
                            values.len()
                        )));
                    }
                    for (field, value) in variant.fields.iter().zip(values) {
                        operand(*value).map_err(here)?;
                        if program.width(*field) != program.width(body.operand_ty(*value)) {
                            return Err(here(format!(
                                "a {:?} given for a field of type {field:?}",
                                body.operand_ty(*value)
                            )));
                        }
                    }
                    *ty
                }
                Rvalue::BoxNew(value) => {
                    operand(*value).map_err(here)?;
                    match target_ty {
                        Type::Box(pointee)
                            if compatible(body.operand_ty(*value), program.pointees[pointee]) =>
                        {
                            Type::Box(pointee)
                        }
                        other => return Err(here(format!("box_new into a {other:?}"))),
                    }
                }
                Rvalue::BoxTake(value) => {
                    operand(*value).map_err(here)?;
                    match body.operand_ty(*value) {
                        Type::Box(pointee) => program.pointees[pointee],
                        other => return Err(here(format!("box_take of a {other:?}"))),
                    }
                }
                // A text literal is `Bytes` with a UTF-8 invariant.
                Rvalue::Bytes(_) => match target_ty {
                    Type::Bytes | Type::String => target_ty,
                    other => return Err(here(format!("bytes stored in a {other:?}"))),
                },
                Rvalue::View {
                    source, start, end, ..
                } => {
                    match source {
                        ViewSource::Array(array) => local(*array).map_err(here)?,
                        ViewSource::Value(value) => operand(*value).map_err(here)?,
                        ViewSource::DynArray(stored) => place(*stored).map_err(here)?,
                    }
                    for bound in start.iter().chain(end) {
                        operand(*bound).map_err(here)?;
                    }
                    match target_ty {
                        Type::Slice(_) | Type::SliceMut(_) | Type::Str | Type::StrMut => target_ty,
                        other => return Err(here(format!("a view stored in a {other:?}"))),
                    }
                }
                Rvalue::ElementAddress(base, index) => {
                    match base {
                        ElementBase::Slice(view) => operand(*view).map_err(here)?,
                        ElementBase::Stored(stored) => place(*stored).map_err(here)?,
                    }
                    operand(*index).map_err(here)?;
                    target_ty
                }
                Rvalue::Task(_, values)
                | Rvalue::Runtime(_, values)
                | Rvalue::Alloc(_, values)
                | Rvalue::Array(_, values)
                | Rvalue::Map(_, values) => {
                    for value in values {
                        operand(*value).map_err(here)?;
                    }
                    target_ty
                }
                Rvalue::ByteAt(handle, index) => {
                    operand(*handle).map_err(here)?;
                    operand(*index).map_err(here)?;
                    target_ty
                }
                Rvalue::Buffer(vector, _) => {
                    operand(*vector).map_err(here)?;
                    Type::I64
                }
                Rvalue::SetLength(vector, length) => {
                    operand(*vector).map_err(here)?;
                    operand(*length).map_err(here)?;
                    if !matches!(body.operand_ty(*vector), Type::Vec(_))
                        || body.operand_ty(*length) != Type::I64
                    {
                        return Err(here(
                            "a length store that is not a vector and an i64".into(),
                        ));
                    }
                    Type::Unit
                }
                Rvalue::Deferred(deferral, values) => {
                    for value in values {
                        operand(*value).map_err(here)?;
                    }
                    local(deferral.sticky).map_err(here)?;
                    let arity = if deferral.op.is_some() { 2 } else { 1 };
                    if values.len() != arity || body.locals[deferral.sticky].ty != Type::I64 {
                        return Err(here("a malformed deferred operation".into()));
                    }
                    body.operand_ty(values[0])
                }
                Rvalue::Loop(op, values) => {
                    for value in values {
                        operand(*value).map_err(here)?;
                    }
                    match op {
                        LoopOp::Magnitude { .. } => Type::I64,
                        LoopOp::ChunkLimit { .. } => match values.first() {
                            Some(start) => body.operand_ty(*start),
                            None => return Err(here("a chunk limit without a start".into())),
                        },
                        LoopOp::Outside { .. }
                        | LoopOp::Certificate { .. }
                        | LoopOp::Unsuitable { .. } => Type::Bool,
                    }
                }
                Rvalue::StructEq(left, right, _) => {
                    operand(*left).map_err(here)?;
                    operand(*right).map_err(here)?;
                    Type::Bool
                }
                Rvalue::Coerce(value, index) => {
                    operand(*value).map_err(here)?;
                    let (to, _) = body
                        .coercions
                        .0
                        .get(*index)
                        .ok_or_else(|| here(format!("coercion {index} does not exist")))?;
                    *to
                }
                Rvalue::FnValue { function, captures } => {
                    if *function >= program.functions.len() {
                        return Err(here(format!("function {function} does not exist")));
                    }
                    for capture in captures {
                        match capture {
                            Capture::Value(value) => operand(*value).map_err(here)?,
                            Capture::Address(captured) => local(*captured).map_err(here)?,
                        }
                    }
                    target_ty
                }
                Rvalue::Ref(source) => {
                    place(*source).map_err(here)?;
                    match target_ty {
                        Type::Ref(_) | Type::RefMut(_) => target_ty,
                        other => return Err(here(format!("a reference stored in a {other:?}"))),
                    }
                }
                Rvalue::Binary(op, left, right) => {
                    operand(*left).map_err(here)?;
                    operand(*right).map_err(here)?;
                    let shift = matches!(op, BinOp::Shl | BinOp::Shr);
                    if !shift && !compatible(body.operand_ty(*left), body.operand_ty(*right)) {
                        return Err(here(format!(
                            "{} of {:?} and {:?}",
                            op.name(),
                            body.operand_ty(*left),
                            body.operand_ty(*right)
                        )));
                    }
                    if matches!(
                        op,
                        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
                    ) {
                        Type::Bool
                    } else {
                        body.operand_ty(*left)
                    }
                }
            };
            if !compatible(ty, target_ty) {
                return Err(here(format!(
                    "{target:?} of type {:?} is assigned a {ty:?}",
                    target_ty
                )));
            }
        }
        match &data.terminator.kind {
            TerminatorKind::Goto(target) => block(*target).map_err(here)?,
            TerminatorKind::Switch {
                value,
                targets,
                otherwise,
            } => {
                operand(*value).map_err(here)?;
                for (_, target) in targets {
                    block(*target).map_err(here)?;
                }
                block(*otherwise).map_err(here)?;
            }
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                unwind,
            } => {
                if let Callee::Indirect(code) = callee {
                    operand(*code).map_err(here)?;
                }
                let words = match callee {
                    Callee::Builtin {
                        hint: CallHint::Shadow(length, capacity),
                        ..
                    } => vec![*length, *capacity],
                    Callee::Builtin {
                        hint: CallHint::Fill(length),
                        ..
                    } => vec![*length],
                    _ => Vec::new(),
                };
                {
                    for word in &words {
                        local(*word).map_err(here)?;
                        if body.locals[*word].ty != Type::I64 {
                            return Err(here(format!("a shadow word _{word} that is not an i64")));
                        }
                    }
                }
                for arg in args {
                    operand(*arg).map_err(here)?;
                }
                local(*destination).map_err(here)?;
                block(*next).map_err(here)?;
                if let Some(unwind) = unwind {
                    block(*unwind).map_err(here)?;
                }
            }
            TerminatorKind::Return(value) => {
                operand(*value).map_err(here)?;
                let ty = body.operand_ty(*value);
                if !compatible(ty, body.result) {
                    return Err(here(format!(
                        "returns a {ty:?} from a function of result {:?}",
                        body.result
                    )));
                }
            }
            TerminatorKind::Panic { unwind } => {
                if let Some(unwind) = unwind {
                    block(*unwind).map_err(here)?;
                }
            }
            TerminatorKind::Drop {
                place: dropped,
                next,
                unwind,
            } => {
                operand(Operand::Copy(*dropped)).map_err(here)?;
                block(*next).map_err(here)?;
                if let Some(unwind) = unwind {
                    block(*unwind).map_err(here)?;
                }
            }
            TerminatorKind::Resume | TerminatorKind::Abort | TerminatorKind::Unreachable => {}
        }
    }
    Ok(())
}
