//! Native code from the CFG IR (FND-MIR, docs/mir-design.md).
//!
//! The generator's frame setup (parameters, handler depth, local storage) is
//! shared with the tree path; this module lowers the body's blocks. Leaf
//! operations call the same helpers as the tree path, so checks, panics and
//! run-time calls are the ones the tree emits.

use super::*;
use crate::mir::{
    BlockId, Body, Callee, Operand, Place, Rvalue, StatementKind, Terminator, TerminatorKind,
    ViewSource,
};

impl Generator<'_, '_> {
    pub(super) fn mir_body(&mut self, body: &Body) {
        // The MIR states every drop, including those on unwind edges; the
        // tree path's resource tracking stays empty.
        self.tracked.clear();
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
            self.mir_unwind = block.unwind.map(|target| blocks[target]);
            for statement in &block.statements {
                let StatementKind::Assign(place, rvalue) = &statement.kind;
                let ty = body.place_ty(*place);
                let depth = self.fuzz_depth;
                let words = self.mir_rvalue(body, rvalue, ty, statement.span);
                if self.fuzz_depth > depth {
                    // As the tree path's `expr`: leave the obligation site.
                    self.fuzz_depth = depth;
                    if words.is_some()
                        && let Some(leave) = self.fuzz.as_ref().map(|f| f.leave)
                    {
                        self.runtime_void(leave, &[]);
                    }
                }
                let Some(words) = words else {
                    // The operation always panics; the block has ended.
                    continue 'blocks;
                };
                self.mir_store(*place, &words);
            }
            self.mir_terminator(body, &blocks, &block.terminator);
        }
        self.mir_unwind = None;
    }

    fn unwind_block(blocks: &[ir::Block], unwind: Option<BlockId>) -> Option<ir::Block> {
        unwind.map(|target| blocks[target])
    }

    fn mir_place(&mut self, place: Place) -> Words {
        let words = self.local_words(place.local);
        match place.field {
            Some(field) if place.deref => {
                let width = self.program.width(field.ty);
                self.load_words(words[0], (field.offset * 8) as i32, width)
            }
            Some(field) => {
                let width = self.program.width(field.ty);
                words[field.offset..field.offset + width].to_vec()
            }
            None => words,
        }
    }

    fn mir_store(&mut self, place: Place, values: &[Value]) {
        match place.field {
            Some(field) if place.deref => {
                let pointer = self.local_words(place.local)[0];
                for (index, value) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        ((field.offset + index) * 8) as i32,
                    );
                }
            }
            Some(field) => {
                let mut words = self.local_words(place.local);
                words[field.offset..field.offset + values.len()].copy_from_slice(values);
                self.assign(place.local, &words);
            }
            None => self.assign(place.local, values),
        }
    }

    /// The address of a place, as the tree path takes it: `borrow_local_value`
    /// for a whole local, `local_address` plus the offset for a field.
    fn mir_address(&mut self, place: Place) -> Value {
        let offset = place.field.map_or(0, |field| field.offset * 8) as i64;
        let base = if place.deref {
            self.local_words(place.local)[0]
        } else if place.field.is_none()
            && place.local < self.program.functions[self.function_index].locals.len()
        {
            return self.borrow_local_value(place.local)[0];
        } else {
            self.local_address(place.local)
        };
        if offset == 0 {
            base
        } else {
            self.builder.ins().iadd_imm_s(base, offset)
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
                Some(vec![self.scalar_binary(
                    &op, left_kind, right_kind, left, right, None,
                )])
            }
            Rvalue::Int(op, source, target, operands) => {
                let values = self.mir_operands(operands);
                Some(self.int_builtin(*op, *source, *target, &values, ty))
            }
            Rvalue::Aggregate(aggregate, tag, operands) => {
                let payload = self.mir_operands(operands);
                Some(self.encode_variant(*aggregate, *tag, &payload))
            }
            Rvalue::BoxNew(operand) => {
                let values = self.mir_operand(*operand);
                let bytes = self.constant((values.len() * 8) as i64);
                let pointer = self.runtime_call(self.allocate, &[bytes]);
                for (i, value) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (i * 8) as i32,
                    );
                }
                Some(vec![pointer])
            }
            Rvalue::BoxTake(operand) => {
                let pointer = self.mir_scalar(*operand);
                let values = self.load_words(pointer, 0, self.program.width(ty));
                emit_drop(&mut self.builder, self.module, self.free, &[pointer]);
                Some(values)
            }
            Rvalue::Ref(place) => Some(vec![self.mir_address(*place)]),
            Rvalue::View {
                source,
                start,
                end,
                element,
                check,
                text,
            } => {
                let base_ty = source.ty(body);
                let (location, values) = match source {
                    ViewSource::Array(local) => {
                        let location = self.locations[*local];
                        let values = if location.is_some() {
                            Vec::new()
                        } else {
                            self.local_words(*local)
                        };
                        (location, values)
                    }
                    ViewSource::Value(operand) => (None, self.mir_operand(*operand)),
                };
                let start = match start {
                    Some(start) => self.mir_scalar(*start),
                    None => self.constant(0),
                };
                if *text {
                    let (pointer, length) = self.text_view_source(base_ty, &values);
                    let end = end.map_or(length, |end| self.mir_scalar(end));
                    return Some(self.finish_text_view(pointer, length, start, end, *check));
                }
                let width = self.program.width(*element);
                let (pointer, length, stride, bytes) =
                    self.view_source(base_ty, width, location, None, &values);
                let end = end.map_or(length, |end| self.mir_scalar(end));
                Some(self.finish_view(pointer, length, stride, bytes, start, end, *check))
            }
            Rvalue::Bytes(bytes) => {
                let id = match self.module.literal(bytes) {
                    Ok(id) => id,
                    Err(diagnostic) => {
                        self.module.failure.get_or_insert(diagnostic);
                        self.abort();
                        return None;
                    }
                };
                let gv = self.module.declare_data_in_func(id, self.builder.func);
                let address = self.builder.ins().symbol_value(I64, gv);
                let length = self.constant(bytes.len() as i64);
                Some(vec![self.runtime_call(self.bytes_from, &[address, length])])
            }
        }
    }

    fn mir_terminator(&mut self, body: &Body, blocks: &[ir::Block], terminator: &Terminator) {
        match &terminator.kind {
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
                    self.builder
                        .ins()
                        .brif(hit, blocks[*target], &[], next, &[]);
                    self.builder.switch_to_block(next);
                }
                self.jump(blocks[*otherwise], &[]);
            }
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                unwind,
            } => {
                self.mir_unwind = Self::unwind_block(blocks, *unwind);
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
                    Callee::Builtin(index) => {
                        let ty = body.locals[*destination].ty;
                        let target = body.builtins.0[*index];
                        let Some(words) =
                            self.call_target(&target, values, ty, terminator.span, None)
                        else {
                            // The builtin always panics; the block has ended.
                            return;
                        };
                        words
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
            TerminatorKind::Panic { unwind } => {
                self.mir_unwind = Self::unwind_block(blocks, *unwind);
                self.abort();
            }
            TerminatorKind::Drop { place, next, .. } => {
                // Drop glue does not report panics (as on the tree path).
                let ty = body.place_ty(*place);
                let words = self.mir_place(*place);
                self.drop_value(ty, &words);
                self.jump(blocks[*next], &[]);
            }
            TerminatorKind::Resume => self.return_dummy(),
            TerminatorKind::Unreachable => {
                self.builder.ins().trap(TrapCode::unwrap_user(2));
            }
        }
    }
}
