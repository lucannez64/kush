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
    let operand = |operand: Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            local(place.local)?;
            if let Some(field) = place.field {
                let width = program.width(body.locals[place.local].ty);
                if field.offset + program.width(field.ty) > width {
                    return Err(format!(
                        "_{}.{} reads past the {width} words of the local",
                        place.local, field.offset
                    ));
                }
            }
            Ok(())
        }
        Operand::Constant(..) => Ok(()),
    };
    for (index, data) in body.blocks.iter().enumerate() {
        let here = |e: String| format!("bb{index}: {e}");
        if let Some(unwind) = data.unwind {
            block(unwind).map_err(here)?;
        }
        for statement in &data.statements {
            let StatementKind::Assign(target, rvalue) = &statement.kind;
            local(*target).map_err(here)?;
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
                        return Err(here(format!("the integer builtin {op:?} has no one-word result")));
                    }
                    for value in values {
                        operand(*value).map_err(here)?;
                    }
                    Type::int(*target)
                }
                Rvalue::Aggregate(ty, tag, values) => {
                    let layout = ty.layout().ok_or_else(|| here(format!("an aggregate of {ty:?}")))?;
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
                    match body.locals[*target].ty {
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
                Rvalue::Bytes(_) => Type::Bytes,
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
            if !compatible(ty, body.locals[*target].ty) {
                return Err(here(format!(
                    "_{target} of type {:?} is assigned a {ty:?}",
                    body.locals[*target].ty
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
                args,
                destination,
                next,
                unwind,
                ..
            } => {
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
            TerminatorKind::Drop { place, next, unwind } => {
                operand(Operand::Copy(*place)).map_err(here)?;
                block(*next).map_err(here)?;
                if let Some(unwind) = unwind {
                    block(*unwind).map_err(here)?;
                }
            }
            TerminatorKind::Resume | TerminatorKind::Unreachable => {}
        }
    }
    Ok(())
}
