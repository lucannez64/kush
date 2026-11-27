//! Native code from the CFG IR (FND-MIR, docs/mir-design.md).
//!
//! The generator's frame setup (parameters, handler depth, local storage) is
//! shared with the tree path; this module lowers the body's blocks. Leaf
//! operations call the same helpers as the tree path, so checks, panics and
//! run-time calls are the ones the tree emits.

use super::*;
use crate::mir::{
    AllocOp, ArrayOp, BinOp, BlockId, Body, Bound, BufferWord, CallHint, Callee, Capture,
    DeferMode, ElementBase, LoopOp, Operand, Place, RuntimeOp, Rvalue, StatementKind, TaskOp,
    Terminator, TerminatorKind, ViewSource,
};

impl<E: Emit> Generator<'_, E> {
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
                    self.builder.store(
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
            self.builder.iadd_imm_s(base, offset)
        }
    }

    fn mir_operand(&mut self, operand: Operand) -> Words {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.mir_place(place),
            // A constant of a wider type (an erased argument) pads with zeros.
            Operand::Constant(value, ty) => {
                let mut words = vec![self.constant(value)];
                let width = self.program.width(ty);
                if width > 1 {
                    let zero = self.constant(0);
                    words.resize(width, zero);
                }
                words
            }
        }
    }

    /// A one-word operand.
    fn mir_scalar(&mut self, operand: Operand) -> Value {
        self.mir_operand(operand)[0]
    }

    /// An allocator `(alloc, release, realloc, context)` from an operand of
    /// type `Allocator` or `AllocatorContext` (the tree path's
    /// `allocator_words`).
    fn mir_allocator(&mut self, ty: Type, values: &[Value]) -> [Value; 4] {
        let zero = self.constant(0);
        match ty {
            Type::Allocator => [values[0], values[1], values[2], zero],
            Type::AllocatorContext => [zero, zero, zero, values[0]],
            _ => unreachable!("checked allocator operand"),
        }
    }

    /// The allocator and arena operations, as the tree path's arms lower
    /// them; `ty` is the result type. `None` when the operation can only
    /// fail (an allocator context spec the program does not have).
    fn mir_alloc(
        &mut self,
        op: AllocOp,
        words: &[Words],
        types: &[Type],
        ty: Type,
    ) -> Option<Words> {
        let width = self.program.width(ty);
        Some(match op {
            AllocOp::AllocatorNew => {
                let grow = match words.get(2) {
                    Some(realloc) => realloc[0],
                    None => self.constant(0),
                };
                vec![words[0][0], words[1][0], grow]
            }
            AllocOp::ContextNew { spec } => {
                let spec_index = (spec < self.program.allocator_contexts.len()).then_some(spec)?;
                let checked = self.program.allocator_contexts[spec_index];
                let state_bytes =
                    self.constant((self.program.width(checked.state).max(1) * 8) as i64);
                let state = self.runtime_call(self.allocate, &[state_bytes]);
                self.store_words(state, &words[0]);
                let drop = self
                    .builder
                    .declare_func(self.module, self.context_drops[spec_index]);
                let drop = self.builder.func_addr(I64, drop);
                let function = |g: &mut Self, index: usize| {
                    let reference = g.builder.declare_func(g.module, g.ids[index]);
                    g.builder.func_addr(I64, reference)
                };
                let alloc = function(self, checked.alloc);
                let release = function(self, checked.free);
                let grow = function(self, checked.grow);
                vec![self.runtime_call(
                    self.alloc_ops.context_new,
                    &[state, drop, alloc, release, grow],
                )]
            }
            AllocOp::ContextShare => {
                let handle = self.load_words(words[0][0], 0, 1)[0];
                vec![self.runtime_call(self.alloc_ops.context_share, &[handle])]
            }
            AllocOp::ArenaNew => vec![self.runtime_call(self.arena_new, &[])],
            AllocOp::ArenaNewWith => {
                vec![self.runtime_call(self.arena_new_with_strategy, &[words[0][0]])]
            }
            AllocOp::ArenaAlloc => {
                let handle = self.load_words(words[0][0], 0, 1)[0];
                let bytes = self.constant((self.program.width(types[1]) * 8) as i64);
                let pointer = self.runtime_call(self.arena_alloc, &[handle, bytes]);
                self.store_words(pointer, &words[1]);
                vec![pointer]
            }
            AllocOp::BoxNew => {
                let pair = self.mir_allocator(types[0], &words[0]);
                let bytes = self.constant((self.program.width(types[1]) * 8) as i64);
                let block =
                    self.runtime_call(self.alloc_ops.block, &[pair[0], pair[1], pair[3], bytes]);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                self.store_words(data, &words[1]);
                vec![self.runtime_call(
                    self.alloc_ops.box_create,
                    &[pair[0], pair[1], block, pair[3]],
                )]
            }
            AllocOp::BoxRead => {
                let handle = self.load_words(words[0][0], 0, 1)[0];
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                self.load_words(data, 0, width)
            }
            AllocOp::BoxTake => {
                let handle = words[0][0];
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                let payload = self.load_words(data, 0, width);
                self.runtime_void(self.alloc_ops.box_release, &[handle]);
                payload
            }
            AllocOp::VecNew { element } => {
                let pair = self.mir_allocator(types[0], &words[0]);
                let capacity = match words.get(1) {
                    Some(capacity) => capacity[0],
                    None => self.constant(0),
                };
                let element_width = self.constant(self.program.width(element) as i64);
                vec![self.runtime_call(
                    self.alloc_ops.vec_create,
                    &[pair[0], pair[1], pair[2], pair[3], capacity, element_width],
                )]
            }
            AllocOp::ArenaBoxRead => {
                let pointer = self.load_words(words[0][0], 0, 1)[0];
                self.load_words(pointer, 0, width)
            }
            AllocOp::ArenaBoxTake => {
                let pointer = words[0][0];
                let values = self.load_words(pointer, 0, width);
                self.runtime_void(self.arena_box_release, &[pointer]);
                values
            }
            AllocOp::BoxReuse { grow } => {
                vec![self.box_reuse(words[0][0], types[0], &words[1], types[1], grow)]
            }
            AllocOp::BoxWrite => {
                let pointer = self.load_words(words[0][0], 0, 1)[0];
                self.store_words(pointer, &words[1]);
                vec![self.constant(0)]
            }
            AllocOp::BoxTryNew { shape } => self.box_try_new(&words[0], types[0], ty, shape),
            AllocOp::BoxTryReuse { shape } => {
                self.box_try_reuse(words[0][0], types[0], &words[1], types[1], ty, shape)
            }
            AllocOp::BytesTryWithCapacity { shape } => {
                self.bytes_try_with_capacity(words[0][0], ty, shape)
            }
            AllocOp::AllocBoxTryNew { shape } => {
                let pair = self.mir_allocator(types[0], &words[0]);
                self.alloc_box_try_new(pair, &words[1], types[1], ty, shape)
            }
            AllocOp::ArenaTryAlloc { shape } => {
                let handle = self.load_words(words[0][0], 0, 1)[0];
                self.arena_try_alloc(handle, &words[1], types[1], ty, shape)
            }
        })
    }

    /// A computation of a deferred loop's frame, through the tree path's
    /// helpers. `words` has each operand's words.
    fn mir_loop(&mut self, op: &LoopOp, words: &[Words]) -> Value {
        let scalar = |at: usize| words[at][0];
        match op {
            LoopOp::Magnitude { bias: None } => self.magnitude(scalar(0)),
            LoopOp::Magnitude { bias: Some(bias) } => {
                self.builder.iadd_imm_s(scalar(0), 1i64 << bias)
            }
            LoopOp::ChunkLimit {
                comparison,
                unsigned,
                step,
            } => self.chunk_limit(&comparison.kind(), *unsigned, scalar(0), scalar(1), *step),
            LoopOp::Outside { comparison, ranges } => {
                let ranges = ranges
                    .iter()
                    .enumerate()
                    .map(|(at, (least, most))| (scalar(2 + at), *least, *most))
                    .collect::<Vec<_>>();
                let outside =
                    self.ranges_outside(&comparison.kind(), scalar(0), scalar(1), &ranges);
                self.builder.uextend(I64, outside)
            }
            LoopOp::Certificate {
                obligations,
                comparison,
                step,
                accumulating,
            } => {
                let (start, end) = (scalar(0), scalar(1));
                // How many terms the reductions took in, at most (see
                // `lower_deferred_while`).
                let distance = match comparison {
                    BinOp::Lt | BinOp::Le => self.builder.isub(end, start),
                    _ => self.builder.isub(start, end),
                };
                let iterations = if *step == 1 {
                    distance
                } else {
                    let step = self.constant(*step);
                    self.builder.udiv(distance, step)
                };
                let started = self.builder.iadd_imm_s(iterations, 1);
                let count = self.builder.imul_imm_s(started, *accumulating);
                let bounds = words[2..].iter().map(|word| word[0]).collect::<Vec<_>>();
                let mut worst = self.constant(0);
                for obligation in obligations {
                    let value = self.mir_bound(obligation, &bounds, count);
                    worst = self.builder.umax(worst, value);
                }
                let proved =
                    self.builder
                        .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, worst, deferred::LIMIT);
                self.builder.uextend(I64, proved)
            }
            LoopOp::Unsuitable { overlaps, layouts } => {
                let mut unsuitable = self.constant(0);
                let range = |g: &mut Self, view: &Words| {
                    let bytes = g.builder.imul(view[1], view[2]);
                    (view[0], g.builder.iadd(view[0], bytes))
                };
                for (stored, loaded) in overlaps {
                    let (stored_start, stored_end) = range(self, &words[*stored]);
                    let (loaded_start, loaded_end) = range(self, &words[*loaded]);
                    let before =
                        self.builder
                            .icmp(IntCC::UnsignedLessThan, stored_start, loaded_end);
                    let after =
                        self.builder
                            .icmp(IntCC::UnsignedLessThan, loaded_start, stored_end);
                    let both = self.builder.band(before, after);
                    let both = self.builder.uextend(I64, both);
                    unsuitable = self.builder.bor(unsuitable, both);
                }
                for (view, stride) in layouts {
                    let view = &words[*view];
                    let other = self.builder.icmp_imm_s(IntCC::NotEqual, view[2], *stride);
                    let other = self.builder.uextend(I64, other);
                    let flag = self.builder.icmp_imm_s(IntCC::NotEqual, view[3], 0);
                    let flag = self.builder.uextend(I64, flag);
                    unsuitable = self.builder.bor(unsuitable, other);
                    unsuitable = self.builder.bor(unsuitable, flag);
                }
                unsuitable
            }
        }
    }

    /// A certificate bound's value: `u` with `|value| <= 2^u`, from the
    /// magnitude words and the reduction term count.
    fn mir_bound(&mut self, bound: &Bound, words: &[Value], count: Value) -> Value {
        match bound {
            Bound::Constant(bits) => self.constant(i64::from(*bits)),
            Bound::Word(at) => self.magnitude_bound(words[*at]),
            Bound::Biased(at, bias) => self.biased_bound(words[*at], *bias),
            Bound::Sum(left, right) => {
                let left = self.mir_bound(left, words, count);
                let right = self.mir_bound(right, words, count);
                let larger = self.builder.umax(left, right);
                self.builder.iadd_imm_s(larger, 1)
            }
            Bound::Product(left, right) => {
                let left = self.mir_bound(left, words, count);
                let right = self.mir_bound(right, words, count);
                self.builder.iadd(left, right)
            }
            Bound::Accumulated { entry, operands } => {
                let mut largest = self.magnitude_bound(words[*entry]);
                for operand in operands {
                    let operand = self.mir_bound(operand, words, count);
                    largest = self.builder.umax(largest, operand);
                }
                let zeros = self.leading_zeros(count);
                let sixty_four = self.constant(64);
                let bits = self.builder.isub(sixty_four, zeros);
                self.builder.iadd(largest, bits)
            }
        }
    }

    /// The runtime-length array operations, through the tree path's
    /// helpers.
    fn mir_array(&mut self, op: ArrayOp, words: &[Words]) -> Words {
        match op {
            ArrayOp::New { element, capacity } => {
                let width = self.program.width(element);
                vec![self.constant(0); 1 + width * capacity]
            }
            ArrayOp::Push { element, capacity } => {
                self.dyn_array_push(words[0].clone(), &words[1], element, capacity)
            }
            ArrayOp::Fill { element, capacity } => {
                self.dyn_array_fill(words[0][0], &words[1], element, capacity)
            }
            ArrayOp::Set { element, capacity } => {
                self.dyn_array_set(words[0].clone(), words[1][0], &words[2], element, capacity)
            }
            ArrayOp::Pop { element, capacity } => {
                self.dyn_array_pop(words[0].clone(), element, capacity)
            }
            ArrayOp::Equal {
                element,
                capacity,
                negate,
            } => vec![self.dyn_array_equal(&words[0], &words[1], element, capacity, negate)],
            ArrayOp::Suffix {
                element,
                capacity,
                prefix,
                suffix,
                index,
            } => {
                let width = self.program.width(element);
                self.dyn_suffix_element(&words[0], width, capacity, prefix, suffix, index)
            }
            ArrayOp::Rest {
                element,
                capacity,
                prefix,
                suffix,
            } => {
                let width = self.program.width(element);
                self.dyn_rest(&words[0], width, capacity, prefix, suffix)
            }
            ArrayOp::SuffixAddress {
                element,
                suffix,
                index,
            } => {
                let pointer = words[0][0];
                let length = self.load_words(pointer, 0, 1)[0];
                let width = self.program.width(element);
                vec![self.dyn_suffix_address(pointer, length, width, suffix, index)]
            }
            ArrayOp::RestView {
                element,
                prefix,
                suffix,
            } => {
                let pointer = words[0][0];
                let length = self.load_words(pointer, 0, 1)[0];
                let width = self.program.width(element);
                self.dyn_rest_view(pointer, length, width, prefix, suffix)
            }
        }
    }

    /// A function value, laid out as on the tree path: a code pointer, and
    /// for a closure an environment `[drop glue, captures...]` it owns.
    fn mir_fn_value(
        &mut self,
        body: &Body,
        function: usize,
        captures: &[Capture],
        ty: Type,
    ) -> Words {
        let reference = self.builder.declare_func(self.module, self.ids[function]);
        let code = self.builder.func_addr(I64, reference);
        if captures.is_empty() {
            if matches!(ty, Type::Once(_) | Type::Multi(_)) {
                let zero = self.constant(0);
                return vec![code, zero];
            }
            return vec![code];
        }
        if matches!(ty, Type::Multi(_)) {
            // A multishot token: the captures go on the continuation stack,
            // after a word holding the environment size.
            let words = captures
                .iter()
                .map(|capture| match capture {
                    Capture::Value(operand) => self.mir_operand(*operand),
                    Capture::Address(local) => vec![self.local_address(*local)],
                })
                .collect::<Vec<_>>();
            let bytes = 8 + words.iter().map(|words| words.len() * 8).sum::<usize>();
            let size = self.constant(bytes as i64);
            let environment = self.runtime_call(self.kstack_push, &[size]);
            self.builder
                .store(ir::MemFlagsData::new(), size, environment, 0);
            let mut offset = 8;
            for word in words.iter().flatten() {
                self.builder
                    .store(ir::MemFlagsData::new(), *word, environment, offset);
                offset += 8;
            }
            return vec![code, environment];
        }
        let types = captures
            .iter()
            .map(|capture| match capture {
                Capture::Value(operand) => body.operand_ty(*operand).full(),
                Capture::Address(local) => body.locals[*local].ty.full(),
            })
            .collect::<Vec<_>>();
        // An address capture is a call-scoped scalar: one word either way.
        let bytes = 8 + types
            .iter()
            .map(|ty| self.program.width(*ty) * 8)
            .sum::<usize>();
        let size = self.constant(bytes as i64);
        let environment = self.runtime_call(self.allocate, &[size]);
        let drop = self.closure_drops[&types];
        let drop = self.builder.declare_func(self.module, drop);
        let drop = self.builder.func_addr(I64, drop);
        self.builder
            .store(ir::MemFlagsData::new(), drop, environment, 0);
        let mut offset = 8;
        for capture in captures {
            let words = match capture {
                Capture::Address(local) => vec![self.local_address(*local)],
                Capture::Value(operand) => self.mir_operand(*operand),
            };
            for word in &words {
                self.builder
                    .store(ir::MemFlagsData::new(), *word, environment, offset);
                offset += 8;
            }
        }
        vec![code, environment]
    }

    /// A call through a `fn` or `once fn` value, with the tree path's ABI:
    /// result pointer, environment word, then the non-erased arguments.
    fn mir_indirect_call(
        &mut self,
        callee_ty: Type,
        callable: &[Value],
        arguments: Vec<Words>,
    ) -> Words {
        let (id, once) = match callee_ty {
            Type::Fn(id) => (id, false),
            Type::Once(id) | Type::Multi(id) => (id, true),
            other => unreachable!("an indirect call through a {other:?}"),
        };
        let signature = self.program.function_types[id].clone();
        let result = signature.result;
        let pointer = if !signature.result_erased() && aggregate_result(self.program, result) {
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (self.program.width(result) * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
            ));
            Some(self.builder.stack_addr(I64, slot, 0))
        } else {
            None
        };
        let mut values = Vec::new();
        values.extend(pointer);
        if once {
            values.push(callable[1]);
        }
        for (index, words) in arguments.into_iter().enumerate() {
            if !signature.parameter_erased(index) {
                values.extend(words);
            }
        }
        if matches!(callee_ty, Type::Multi(_)) {
            // Everything the token call pushes is released when it returns
            // (docs/multishot-capabilities.md section 5).
            let mark = self.runtime_call(self.kstack_mark, &[]);
            let words = self.finish_indirect_call_mode(id, callable[0], pointer, values, true);
            self.runtime_void(self.kstack_restore, &[mark]);
            return words;
        }
        self.finish_indirect_call(id, callable[0], pointer, values)
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
                self.unary_value(span, &op.kind(), ty, value, None)
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
                    self.builder
                        .store(ir::MemFlagsData::new(), *value, pointer, (i * 8) as i32);
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
            Rvalue::ElementAddress(base, index) => Some(vec![match base {
                ElementBase::Slice(view) => {
                    let descriptor = self.mir_operand(*view);
                    let index = self.mir_scalar(*index);
                    self.slice_element_address(&descriptor, index)
                }
                ElementBase::Stored(place) => {
                    let location = self.mir_address(*place);
                    let index = self.mir_scalar(*index);
                    self.element_address(body.place_ty(*place), location, index)
                }
            }]),
            Rvalue::Deferred(deferral, operands) => {
                let mode = match deferral.mode {
                    DeferMode::Exact => deferred::Mode::Exact,
                    DeferMode::Certified => deferred::Mode::Certified,
                    DeferMode::Accumulate => deferred::Mode::Accumulate,
                };
                let ty = body.operand_ty(operands[0]);
                let values = self.mir_operands(operands);
                self.mir_sticky = Some(self.variables[deferral.sticky][0]);
                let value = match deferral.op {
                    Some(op) => {
                        let right_kind = body.operand_ty(operands[1]).int_kind();
                        Some(self.scalar_binary(
                            &op.kind(),
                            ty.int_kind(),
                            right_kind,
                            values[0],
                            values[1],
                            Some(mode),
                        ))
                    }
                    None => self.unary_value(span, &Kind::Minus, ty, values[0], Some(mode)),
                };
                self.mir_sticky = None;
                value.map(|value| vec![value])
            }
            Rvalue::Loop(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.mir_operand(*operand))
                    .collect::<Vec<_>>();
                Some(vec![self.mir_loop(op, &words)])
            }
            Rvalue::SetLength(vector, length) => {
                let handle = self.mir_scalar(*vector);
                let length = self.mir_scalar(*length);
                self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                    g.builder.store(ir::MemFlagsData::new(), length, handle, 0);
                });
                Some(Vec::new())
            }
            Rvalue::Buffer(vector, word) => {
                let handle = self.mir_scalar(*vector);
                Some(vec![match word {
                    BufferWord::Length => self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                        g.builder.load(I64, ir::MemFlagsData::new(), handle, 0)
                    }),
                    BufferWord::Capacity => self.buffer_capacity(handle),
                }])
            }
            Rvalue::StructEq(left, right, negated) => {
                let ty = body.operand_ty(*left);
                let left = self.mir_operand(*left);
                let right = self.mir_operand(*right);
                let equal = self.struct_eq_words(ty, &left, &right);
                let value = if *negated {
                    self.builder.bxor_imm_s(equal, 1)
                } else {
                    equal
                };
                Some(vec![self.builder.uextend(I64, value)])
            }
            Rvalue::ByteAt(handle, index) => {
                let handle = self.mir_scalar(*handle);
                let index = self.mir_scalar(*index);
                // Data follows the 16-byte header.
                let address = self.builder.iadd(handle, index);
                Some(vec![self.builder.uload8(
                    I64,
                    ir::MemFlagsData::new(),
                    address,
                    16,
                )])
            }
            Rvalue::Coerce(operand, index) => {
                let (to, coercion) = body.coercions.0[*index].clone();
                let values = self.mir_operand(*operand);
                self.coerce_values(values, to, &coercion)
            }
            Rvalue::FnValue { function, captures } => {
                Some(self.mir_fn_value(body, *function, captures, ty))
            }
            Rvalue::View {
                source,
                start,
                end,
                element,
                check,
                text,
            } => {
                let base_ty = source.ty(body);
                let start_value = |g: &mut Self| match start {
                    Some(start) => g.mir_scalar(*start),
                    None => g.constant(0),
                };
                if let ViewSource::DynArray(place) = source {
                    let location = self.mir_address(*place);
                    let start = start_value(self);
                    let width = self.program.width(*element);
                    let (pointer, length, stride, bytes) =
                        self.view_source(base_ty, width, None, Some((location, 0)), &[]);
                    let end = end.map_or(length, |end| self.mir_scalar(end));
                    return Some(
                        self.finish_view(pointer, length, stride, bytes, start, end, *check),
                    );
                }
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
                    ViewSource::DynArray(_) => unreachable!("lowered above"),
                };
                let start = start_value(self);
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
            Rvalue::Alloc(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.mir_operand(*operand))
                    .collect::<Vec<_>>();
                let types = operands
                    .iter()
                    .map(|operand| body.operand_ty(*operand))
                    .collect::<Vec<_>>();
                self.mir_alloc(*op, &words, &types, ty)
            }
            Rvalue::Array(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.mir_operand(*operand))
                    .collect::<Vec<_>>();
                Some(self.mir_array(*op, &words))
            }
            Rvalue::Map(op, operands) => {
                let handle = self.mir_scalar(operands[0]);
                let callbacks = &operands[1..=op.functions.len()];
                let capabilities = operands[1 + op.functions.len()..]
                    .iter()
                    .map(|capability| self.mir_scalar(*capability))
                    .collect::<Vec<_>>();
                let codes = callbacks
                    .iter()
                    .map(|callback| self.mir_scalar(*callback))
                    .collect::<Vec<_>>();
                let types = callbacks
                    .iter()
                    .map(|callback| body.operand_ty(*callback))
                    .collect::<Vec<_>>();
                let plans = op
                    .functions
                    .iter()
                    .zip(&types)
                    .map(|(function, ty)| {
                        let function = (*function)?;
                        self.codegen
                            .inline_scalar_callbacks
                            .then(|| ScalarCallback::function(self.program, function, *ty))
                            .flatten()
                    })
                    .collect::<Vec<_>>();
                Some(vec![self.vec_map(
                    handle,
                    &codes,
                    &types,
                    &plans,
                    op.source,
                    op.target,
                    op.grow,
                    &capabilities,
                )])
            }
            Rvalue::Runtime(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.mir_operand(*operand))
                    .collect::<Vec<_>>();
                let unit = |g: &mut Self| vec![g.constant(0)];
                Some(match *op {
                    RuntimeOp::HandlerDepth => vec![self.runtime_call(self.handler_depth, &[])],
                    RuntimeOp::HandlerRestore => {
                        self.runtime_void(self.handler_restore, &[words[0][0]]);
                        unit(self)
                    }
                    RuntimeOp::HandlerPush {
                        operation,
                        reusable,
                    } => {
                        let values = &words[0];
                        let code = values[0];
                        let (environment, once) =
                            if matches!(body.operand_ty(operands[0]), Type::Once(_)) {
                                let environment =
                                    values.get(1).copied().unwrap_or_else(|| self.constant(0));
                                (environment, self.constant(if reusable { 2 } else { 1 }))
                            } else {
                                (self.constant(0), self.constant(0))
                            };
                        let op = self.constant(operation as i64);
                        // The frame lives in this function's stack: operation,
                        // code, environment, once, consumed, previous, owner.
                        let slot = self.stack_words(7);
                        vec![
                            self.runtime_call(
                                self.handler_push,
                                &[op, code, environment, once, slot],
                            ),
                        ]
                    }
                    // A noncapturing handler's cell is its code address
                    // (positive: frames, the other cells, have the sign bit
                    // set): a perform calls it without a load.
                    RuntimeOp::HandlerCell => vec![words[0][0]],
                    RuntimeOp::HandlerPop => {
                        self.runtime_void(self.handler_pop, &[]);
                        unit(self)
                    }
                    RuntimeOp::Perform {
                        operation,
                        handler,
                        helper,
                    } => {
                        let cell = words.get(2).map(|cell| cell[0]);
                        self.dynamic_perform(operation, handler, &words[0], &words[1], cell, helper)
                    }
                    RuntimeOp::AbortBuffer { words } => vec![self.stack_words(words)],
                    RuntimeOp::AbortRaise { operation } => {
                        let out = self.stack_words(3);
                        let op = self.constant(operation as i64);
                        let found = self.runtime_call(self.handler_lookup, &[op, out]);
                        let missing = self.builder.icmp_imm_s(IntCC::Equal, found, 0);
                        self.guard(missing);
                        let buffer = self.builder.load(I64, ir::MemFlagsData::new(), out, 0);
                        self.store_words(buffer, &words[0]);
                        let word = self.abort_word_address();
                        self.builder.store(ir::MemFlagsData::new(), buffer, word, 0);
                        unit(self)
                    }
                    RuntimeOp::AbortRaiseAt => {
                        let buffer = words[0][0];
                        self.store_words(buffer, &words[1]);
                        let word = self.abort_word_address();
                        self.builder.store(ir::MemFlagsData::new(), buffer, word, 0);
                        unit(self)
                    }
                    RuntimeOp::AbortWord => {
                        let address = self.abort_word_address();
                        vec![self.builder.load(I64, ir::MemFlagsData::new(), address, 0)]
                    }
                    RuntimeOp::AbortClear => {
                        let address = self.abort_word_address();
                        let zero = self.constant(0);
                        self.builder
                            .store(ir::MemFlagsData::new(), zero, address, 0);
                        unit(self)
                    }
                    RuntimeOp::ContinuationMark => vec![self.runtime_call(self.kstack_mark, &[])],
                    RuntimeOp::ContinuationRestore => {
                        self.runtime_void(self.kstack_restore, &[words[0][0]]);
                        unit(self)
                    }
                })
            }
            Rvalue::Task(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.mir_operand(*operand))
                    .collect::<Vec<_>>();
                match *op {
                    TaskOp::Spawn {
                        result,
                        obligation,
                        parallel,
                    } => {
                        let body_ty = body.operand_ty(operands[0]);
                        Some(vec![self.task_spawn(
                            &words[0], body_ty, result, obligation, parallel,
                        )])
                    }
                    TaskOp::Scope {
                        failure,
                        catch,
                        parallel,
                    } => {
                        let body_ty = body.operand_ty(operands[0]);
                        self.task_scope(&words[0], body_ty, ty, failure, catch, parallel)
                    }
                    TaskOp::Yield => Some(vec![self.runtime_call(self.task_yield, &[])]),
                    TaskOp::CheckCancel => {
                        Some(vec![self.runtime_call(self.task_check_cancel, &[])])
                    }
                    TaskOp::Cancel => {
                        self.runtime_void(self.task_cancel, &[words[0][0]]);
                        Some(vec![self.constant(0)])
                    }
                    TaskOp::Join { exit, parallel } => {
                        Some(self.task_join(words[0][0], exit, parallel))
                    }
                }
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
                let gv = self.builder.declare_data(self.module, id);
                let address = self.builder.symbol_value(I64, gv);
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
                        .brif(value, blocks[*otherwise], &[], blocks[zero], &[]);
                    return;
                }
                for (case, target) in targets {
                    let hit = self.builder.icmp_imm_s(IntCC::Equal, value, *case);
                    let next = self.builder.create_block();
                    self.builder.brif(hit, blocks[*target], &[], next, &[]);
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
                    Callee::Function(index) => {
                        // Erased parameters have no words in the call.
                        let grades = &self.program.functions[*index].parameter_grades;
                        let mut kept = Vec::new();
                        for (position, arg) in args.iter().enumerate() {
                            let erased = grades
                                .get(position)
                                .copied()
                                .flatten()
                                .is_some_and(Grade::is_zero);
                            if !erased {
                                kept.extend(self.mir_operand(*arg));
                            }
                        }
                        self.function_call(*index, kept)
                    }
                    Callee::PrintInt(kind) => {
                        let print = if *kind == IntKind::U64 {
                            self.print_u64
                        } else {
                            self.print
                        };
                        vec![self.runtime_call(print, &values)]
                    }
                    Callee::Indirect(code) => {
                        let callee_ty = body.operand_ty(*code);
                        let callable = self.mir_operand(*code);
                        let arguments = args
                            .iter()
                            .map(|arg| self.mir_operand(*arg))
                            .collect::<Vec<_>>();
                        self.mir_indirect_call(callee_ty, &callable, arguments)
                    }
                    Callee::Builtin { index, hint } => {
                        let ty = body.locals[*destination].ty;
                        let target = body.builtins.0[*index];
                        match hint {
                            CallHint::None => {}
                            CallHint::Below => self.index_below = true,
                            CallHint::Proved => self.access_proved = true,
                            CallHint::Shadow(length, capacity) => {
                                self.push_shadow = Some((
                                    self.variables[*length][0],
                                    self.variables[*capacity][0],
                                ));
                            }
                            CallHint::Fill(length) => {
                                self.push_fill = Some(self.variables[*length][0]);
                            }
                        }
                        let words = self.call_target(&target, values, ty, terminator.span);
                        self.index_below = false;
                        self.access_proved = false;
                        self.push_shadow = None;
                        self.push_fill = None;
                        let Some(words) = words else {
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
                let function = &self.program.functions[self.function_index];
                if function.result_grade.is_some_and(Grade::is_zero) {
                    // An erased result has no words; a copyable value
                    // still gets its (empty) cleanup, as on the tree path.
                    self.drop_value(body.operand_ty(*value), &words);
                    self.return_value(&[]);
                } else {
                    self.return_value(&words);
                }
            }
            // Without unwinding, every panic of the function shares one
            // block (FND-LLVM-PANIC-SHARE).
            TerminatorKind::Panic { .. } if !self.program.uses_unwinding => {
                self.jump_to_panic();
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
            TerminatorKind::Resume | TerminatorKind::Abort => self.return_dummy(),
            TerminatorKind::Unreachable => {
                self.builder.trap(TrapCode::unwrap_user(2));
            }
        }
    }
}
