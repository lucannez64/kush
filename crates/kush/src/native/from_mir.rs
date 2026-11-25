//! Native code from the CFG IR (FND-MIR, docs/mir-design.md).
//!
//! The generator's frame setup (parameters, handler depth, local storage) is
//! shared with the tree path; this module lowers the body's blocks. Leaf
//! operations call the same helpers as the tree path, so checks, panics and
//! run-time calls are the ones the tree emits.

use super::*;
use crate::mir::{Body, Callee, Operand, Place, Rvalue, StatementKind, TerminatorKind};

impl Generator<'_, '_> {
    pub(super) fn mir_body(&mut self, body: &Body) {
        // Temporaries follow the checked function's locals.
        for local in &body.locals[self.variables.len()..] {
            let variables = (0..self.program.width(local.ty))
                .map(|_| self.builder.declare_var(I64))
                .collect();
            self.variables.push(variables);
            self.locations.push(None);
        }
        let blocks = body
            .blocks
            .iter()
            .map(|_| self.builder.create_block())
            .collect::<Vec<_>>();
        self.jump(blocks[0], &[]);
        'blocks: for (index, block) in body.blocks.iter().enumerate() {
            self.builder.switch_to_block(blocks[index]);
            for statement in &block.statements {
                let StatementKind::Assign(local, rvalue) = &statement.kind;
                let ty = body.locals[*local].ty;
                let Some(words) = self.mir_rvalue(body, rvalue, ty, statement.span) else {
                    // The operation always panics; the block has ended.
                    continue 'blocks;
                };
                self.assign(*local, &words);
            }
            self.mir_terminator(&blocks, &block.terminator.kind);
        }
    }

    fn mir_place(&mut self, place: Place) -> Words {
        let words = self.local_words(place.local);
        match place.field {
            Some(field) => {
                let width = self.program.width(field.ty);
                words[field.offset..field.offset + width].to_vec()
            }
            None => words,
        }
    }

    fn mir_operand(&mut self, operand: Operand) -> Words {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.mir_place(place),
            Operand::Constant(value, _) => vec![self.constant(value)],
        }
    }

    /// A one-word operand.
    fn mir_scalar(&mut self, operand: Operand) -> Value {
        self.mir_operand(operand)[0]
    }

    fn mir_operands(&mut self, operands: &[Operand]) -> Words {
        operands
            .iter()
            .flat_map(|operand| self.mir_operand(*operand))
            .collect()
    }

    /// `ty` is the type of the local receiving the value.
    fn mir_rvalue(
        &mut self,
        body: &Body,
        rvalue: &Rvalue,
        ty: Type,
        span: crate::Span,
    ) -> Option<Words> {
        match rvalue {
            Rvalue::Use(operand) => Some(self.mir_operand(*operand)),
            Rvalue::Unary(op, operand) => {
                let ty = body.operand_ty(*operand);
                let value = self.mir_scalar(*operand);
                self.unary_value(span, &op.kind(), ty, value, None, 0)
                    .map(|value| vec![value])
            }
            Rvalue::Binary(op, left, right) => {
                let op = op.kind();
                let left_ty = body.operand_ty(*left);
                let right_ty = body.operand_ty(*right);
                let left = self.mir_scalar(*left);
                let right = self.mir_scalar(*right);
                let left_kind = left_ty.int_kind();
                let right_kind = right_ty.int_kind();
                self.fuzz_arith(span, &op, left_kind, right_kind, left, right);
                if let Some(kind) = left_ty.float_kind() {
                    let left = self.float_value(kind, left);
                    let right = self.float_value(kind, right);
                    return Some(vec![self.float_binary(kind, &op, left, right)]);
                }
                Some(vec![self.scalar_binary(&op, left_kind, right_kind, left, right, None)])
            }
            Rvalue::Int(op, source, target, operands) => {
                let values = self.mir_operands(operands);
                Some(self.int_builtin(*op, *source, *target, &values, ty))
            }
            Rvalue::Aggregate(aggregate, tag, operands) => {
                let payload = self.mir_operands(operands);
                Some(self.encode_variant(*aggregate, *tag, &payload))
            }
        }
    }

    fn mir_terminator(&mut self, blocks: &[ir::Block], kind: &TerminatorKind) {
        match kind {
            TerminatorKind::Goto(target) => self.jump(blocks[*target], &[]),
            TerminatorKind::Switch {
                value,
                targets,
                otherwise,
            } => {
                let value = self.mir_scalar(*value);
                if let [(0, zero)] = targets[..] {
                    self.builder
                        .ins()
                        .brif(value, blocks[*otherwise], &[], blocks[zero], &[]);
                    return;
                }
                for (case, target) in targets {
                    let hit = self.builder.ins().icmp_imm_s(IntCC::Equal, value, *case);
                    let next = self.builder.create_block();
                    self.builder.ins().brif(hit, blocks[*target], &[], next, &[]);
                    self.builder.switch_to_block(next);
                }
                self.jump(blocks[*otherwise], &[]);
            }
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                ..
            } => {
                let values = self.mir_operands(args);
                let result = match callee {
                    Callee::Function(index) => self.function_call(*index, values),
                    Callee::PrintInt(kind) => {
                        let print = if *kind == IntKind::U64 {
                            self.print_u64
                        } else {
                            self.print
                        };
                        vec![self.runtime_call(print, &values)]
                    }
                };
                self.assign(*destination, &result);
                self.jump(blocks[*next], &[]);
            }
            TerminatorKind::Return(value) => {
                let words = self.mir_operand(*value);
                self.cleanup_all();
                self.return_value(&words);
            }
            TerminatorKind::Panic { .. } => self.abort(),
            TerminatorKind::Unreachable => {
                self.builder.ins().trap(TrapCode::unwrap_user(2));
            }
        }
    }
}
