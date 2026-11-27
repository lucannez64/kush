//! `KUSH_KEEP_PROVED_CHECKS=1`: build a program as if its proofs removed no
//! runtime check, to measure what they buy.
//!
//! Every proof is still checked as usual; afterwards each operation a proof
//! made unchecked gets its runtime check back: proved indexing and
//! `Slice.at` / `Vec.at` / `Bytes.at` become the checked reads, and `+`,
//! `-`, `*`, `<<` and `>>` whose result or amount was proved in range become
//! the checked operators. The rewrite runs before automatic fusion, which
//! fuses only callbacks that cannot panic.
use super::*;
use crate::int::{ArithOp, IntOp, Shift};

/// Whether `KUSH_KEEP_PROVED_CHECKS` is set (to anything).
pub(crate) fn keep_proved_checks() -> bool {
    static KEEP: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *KEEP.get_or_init(|| std::env::var_os("KUSH_KEEP_PROVED_CHECKS").is_some())
}

/// Put the runtime checks back into every checked body.
pub(super) fn restore_checks(bodies: &mut [Option<Function>]) {
    for function in bodies.iter_mut().flatten() {
        restore_block(&mut function.body);
    }
}

fn restore_block(block: &mut Block) {
    for statement in &mut block.statements {
        match statement {
            Statement::Let(_, value) | Statement::Expr(value) => restore(value),
            Statement::Declare(_) => {}
        }
    }
    if let Some(tail) = &mut block.tail {
        restore(tail);
    }
}

fn restore(expr: &mut Expr) {
    expr.for_each_child_mut(&mut restore);
    let checked = match &mut expr.kind {
        ExprKind::Call(Target::Int(op, _, _), arguments) if arguments.len() == 2 => {
            let operator = match *op {
                IntOp::Unchecked(ArithOp::Add) => Kind::Plus,
                IntOp::Unchecked(ArithOp::Sub) => Kind::Minus,
                IntOp::Unchecked(ArithOp::Mul) => Kind::Star,
                IntOp::UncheckedShift(Shift::Left) => Kind::Shl,
                IntOp::UncheckedShift(Shift::Right) => Kind::Shr,
                _ => return,
            };
            let right = arguments.pop().expect("two arguments");
            let left = arguments.pop().expect("two arguments");
            ExprKind::Binary(operator, Box::new(left), Box::new(right))
        }
        ExprKind::Call(Target::Slice(op @ SliceOp::At, _), _) => {
            *op = SliceOp::Get;
            return;
        }
        ExprKind::Call(Target::Vec(op @ VecOp::At, _), _) => {
            *op = VecOp::Get;
            return;
        }
        ExprKind::BytesAt(..) => {
            let ExprKind::BytesAt(bytes, index) =
                std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
            else {
                unreachable!()
            };
            ExprKind::Call(Target::Bytes(BytesOp::Get), vec![*bytes, *index])
        }
        _ => return,
    };
    expr.kind = checked;
}
