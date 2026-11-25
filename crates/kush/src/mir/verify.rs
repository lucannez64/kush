//! Structural checks of a built [`Body`]: every block, local and parameter
//! it names exists, operands have the types their operations need, and a
//! returned value has the function's result type.

use super::*;

pub(crate) fn verify(body: &Body) -> Result<(), String> {
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
        Operand::Copy(id) | Operand::Move(id) => local(id),
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
                Rvalue::Binary(op, left, right) => {
                    operand(*left).map_err(here)?;
                    operand(*right).map_err(here)?;
                    let shift = matches!(op, BinOp::Shl | BinOp::Shr);
                    if !shift && body.operand_ty(*left) != body.operand_ty(*right) {
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
            if ty != body.locals[*target].ty && ty != Type::Never {
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
                if ty != body.result && ty != Type::Never {
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
            TerminatorKind::Unreachable => {}
        }
    }
    Ok(())
}
