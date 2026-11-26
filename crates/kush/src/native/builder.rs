//! The instruction builder of one function body, for either backend
//! (FND-LLVM-BUILDER): Cranelift's `FunctionBuilder`, or the typed LLVM
//! builder, or both at once ([`Both`]). The lowering is generic over
//! [`Emit`]; this one type lets it be instantiated once and choose the
//! backend per function.

use super::both::Both;
use super::emit::{Cranelift, Emit};
use super::llvm_builder::LlvmBuilder;
use cranelift_codegen::ir::{
    self, AtomicRmwOp, MemFlagsData, TrapCode,
    condcodes::{FloatCC, IntCC},
    immediates::{Imm64, Offset32, Uimm8},
};
use cranelift_frontend::Variable;
use cranelift_module::{DataId, FuncId, Module};

pub(super) enum Builder<'a> {
    Cranelift(Cranelift<'a>),
    Llvm(Box<LlvmBuilder>),
    /// Staging recipes and Cranelift IR dumps under the LLVM backend.
    Both(Box<Both<'a>>),
}

impl Emit for Builder<'_> {
    fn create_block(&mut self) -> ir::Block {
        match self {
            Builder::Cranelift(inner) => inner.create_block(),
            Builder::Llvm(inner) => inner.create_block(),
            Builder::Both(inner) => inner.create_block(),
        }
    }
    fn switch_to_block(&mut self, block: ir::Block) {
        match self {
            Builder::Cranelift(inner) => inner.switch_to_block(block),
            Builder::Llvm(inner) => inner.switch_to_block(block),
            Builder::Both(inner) => inner.switch_to_block(block),
        }
    }
    fn append_block_param(&mut self, block: ir::Block, ty: ir::Type) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.append_block_param(block, ty),
            Builder::Llvm(inner) => inner.append_block_param(block, ty),
            Builder::Both(inner) => inner.append_block_param(block, ty),
        }
    }
    fn append_block_params_for_function_params(&mut self, block: ir::Block) {
        match self {
            Builder::Cranelift(inner) => inner.append_block_params_for_function_params(block),
            Builder::Llvm(inner) => inner.append_block_params_for_function_params(block),
            Builder::Both(inner) => inner.append_block_params_for_function_params(block),
        }
    }
    fn block_params(&self, block: ir::Block) -> &[ir::Value] {
        match self {
            Builder::Cranelift(inner) => inner.block_params(block),
            Builder::Llvm(inner) => inner.block_params(block),
            Builder::Both(inner) => inner.block_params(block),
        }
    }
    fn seal_all_blocks(&mut self) {
        match self {
            Builder::Cranelift(inner) => inner.seal_all_blocks(),
            Builder::Llvm(inner) => inner.seal_all_blocks(),
            Builder::Both(inner) => inner.seal_all_blocks(),
        }
    }
    fn declare_var(&mut self, ty: ir::Type) -> Variable {
        match self {
            Builder::Cranelift(inner) => inner.declare_var(ty),
            Builder::Llvm(inner) => inner.declare_var(ty),
            Builder::Both(inner) => inner.declare_var(ty),
        }
    }
    fn def_var(&mut self, var: Variable, value: ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.def_var(var, value),
            Builder::Llvm(inner) => inner.def_var(var, value),
            Builder::Both(inner) => inner.def_var(var, value),
        }
    }
    fn use_var(&mut self, var: Variable) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.use_var(var),
            Builder::Llvm(inner) => inner.use_var(var),
            Builder::Both(inner) => inner.use_var(var),
        }
    }
    fn create_sized_stack_slot(&mut self, data: ir::StackSlotData) -> ir::StackSlot {
        match self {
            Builder::Cranelift(inner) => inner.create_sized_stack_slot(data),
            Builder::Llvm(inner) => inner.create_sized_stack_slot(data),
            Builder::Both(inner) => inner.create_sized_stack_slot(data),
        }
    }
    fn import_signature(&mut self, signature: ir::Signature) -> ir::SigRef {
        match self {
            Builder::Cranelift(inner) => inner.import_signature(signature),
            Builder::Llvm(inner) => inner.import_signature(signature),
            Builder::Both(inner) => inner.import_signature(signature),
        }
    }
    fn declare_func(&mut self, module: &mut impl Module, id: FuncId) -> ir::FuncRef {
        match self {
            Builder::Cranelift(inner) => inner.declare_func(module, id),
            Builder::Llvm(inner) => inner.declare_func(module, id),
            Builder::Both(inner) => inner.declare_func(module, id),
        }
    }
    fn declare_data(&mut self, module: &mut impl Module, id: DataId) -> ir::GlobalValue {
        match self {
            Builder::Cranelift(inner) => inner.declare_data(module, id),
            Builder::Llvm(inner) => inner.declare_data(module, id),
            Builder::Both(inner) => inner.declare_data(module, id),
        }
    }
    fn inst_results(&self, inst: ir::Inst) -> &[ir::Value] {
        match self {
            Builder::Cranelift(inner) => inner.inst_results(inst),
            Builder::Llvm(inner) => inner.inst_results(inst),
            Builder::Both(inner) => inner.inst_results(inst),
        }
    }
    fn constant_of(&self, value: ir::Value) -> Option<i64> {
        match self {
            Builder::Cranelift(inner) => inner.constant_of(value),
            Builder::Llvm(inner) => inner.constant_of(value),
            Builder::Both(inner) => inner.constant_of(value),
        }
    }
    fn value_type(&self, value: ir::Value) -> ir::Type {
        match self {
            Builder::Cranelift(inner) => inner.value_type(value),
            Builder::Llvm(inner) => inner.value_type(value),
            Builder::Both(inner) => inner.value_type(value),
        }
    }
    fn set_memory_class(&mut self, class: Option<u32>) -> Option<u32> {
        match self {
            Builder::Cranelift(inner) => inner.set_memory_class(class),
            Builder::Llvm(inner) => inner.set_memory_class(class),
            Builder::Both(inner) => inner.set_memory_class(class),
        }
    }
    fn jump(&mut self, block: ir::Block, args: &[ir::Value]) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.jump(block, args),
            Builder::Llvm(inner) => inner.jump(block, args),
            Builder::Both(inner) => inner.jump(block, args),
        }
    }
    fn brif(
        &mut self,
        condition: ir::Value,
        then: ir::Block,
        then_args: &[ir::Value],
        otherwise: ir::Block,
        otherwise_args: &[ir::Value],
    ) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => {
                inner.brif(condition, then, then_args, otherwise, otherwise_args)
            }
            Builder::Llvm(inner) => {
                inner.brif(condition, then, then_args, otherwise, otherwise_args)
            }
            Builder::Both(inner) => {
                inner.brif(condition, then, then_args, otherwise, otherwise_args)
            }
        }
    }
    fn return_(&mut self, values: &[ir::Value]) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.return_(values),
            Builder::Llvm(inner) => inner.return_(values),
            Builder::Both(inner) => inner.return_(values),
        }
    }
    fn trap(&mut self, code: impl Into<TrapCode>) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.trap(code),
            Builder::Llvm(inner) => inner.trap(code),
            Builder::Both(inner) => inner.trap(code),
        }
    }
    fn call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.call(callee, args),
            Builder::Llvm(inner) => inner.call(callee, args),
            Builder::Both(inner) => inner.call(callee, args),
        }
    }
    fn call_indirect(
        &mut self,
        signature: ir::SigRef,
        callee: ir::Value,
        args: &[ir::Value],
    ) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.call_indirect(signature, callee, args),
            Builder::Llvm(inner) => inner.call_indirect(signature, callee, args),
            Builder::Both(inner) => inner.call_indirect(signature, callee, args),
        }
    }
    fn iconst(&mut self, ty: ir::Type, value: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.iconst(ty, value),
            Builder::Llvm(inner) => inner.iconst(ty, value),
            Builder::Both(inner) => inner.iconst(ty, value),
        }
    }
    fn stack_addr(
        &mut self,
        ty: ir::Type,
        slot: ir::StackSlot,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.stack_addr(ty, slot, offset),
            Builder::Llvm(inner) => inner.stack_addr(ty, slot, offset),
            Builder::Both(inner) => inner.stack_addr(ty, slot, offset),
        }
    }
    fn func_addr(&mut self, ty: ir::Type, callee: ir::FuncRef) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.func_addr(ty, callee),
            Builder::Llvm(inner) => inner.func_addr(ty, callee),
            Builder::Both(inner) => inner.func_addr(ty, callee),
        }
    }
    fn symbol_value(&mut self, ty: ir::Type, global: ir::GlobalValue) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.symbol_value(ty, global),
            Builder::Llvm(inner) => inner.symbol_value(ty, global),
            Builder::Both(inner) => inner.symbol_value(ty, global),
        }
    }
    fn load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.load(ty, flags, pointer, offset),
            Builder::Llvm(inner) => inner.load(ty, flags, pointer, offset),
            Builder::Both(inner) => inner.load(ty, flags, pointer, offset),
        }
    }
    fn uload8(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.uload8(ty, flags, pointer, offset),
            Builder::Llvm(inner) => inner.uload8(ty, flags, pointer, offset),
            Builder::Both(inner) => inner.uload8(ty, flags, pointer, offset),
        }
    }
    fn store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.store(flags, value, pointer, offset),
            Builder::Llvm(inner) => inner.store(flags, value, pointer, offset),
            Builder::Both(inner) => inner.store(flags, value, pointer, offset),
        }
    }
    fn istore8(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.istore8(flags, value, pointer, offset),
            Builder::Llvm(inner) => inner.istore8(flags, value, pointer, offset),
            Builder::Both(inner) => inner.istore8(flags, value, pointer, offset),
        }
    }
    fn atomic_load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.atomic_load(ty, flags, pointer),
            Builder::Llvm(inner) => inner.atomic_load(ty, flags, pointer),
            Builder::Both(inner) => inner.atomic_load(ty, flags, pointer),
        }
    }
    fn atomic_store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
    ) -> ir::Inst {
        match self {
            Builder::Cranelift(inner) => inner.atomic_store(flags, value, pointer),
            Builder::Llvm(inner) => inner.atomic_store(flags, value, pointer),
            Builder::Both(inner) => inner.atomic_store(flags, value, pointer),
        }
    }
    fn atomic_rmw(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        op: impl Into<AtomicRmwOp>,
        pointer: ir::Value,
        value: ir::Value,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.atomic_rmw(ty, flags, op, pointer, value),
            Builder::Llvm(inner) => inner.atomic_rmw(ty, flags, op, pointer, value),
            Builder::Both(inner) => inner.atomic_rmw(ty, flags, op, pointer, value),
        }
    }
    fn atomic_cas(
        &mut self,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        expected: ir::Value,
        replacement: ir::Value,
    ) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.atomic_cas(flags, pointer, expected, replacement),
            Builder::Llvm(inner) => inner.atomic_cas(flags, pointer, expected, replacement),
            Builder::Both(inner) => inner.atomic_cas(flags, pointer, expected, replacement),
        }
    }
    fn iadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.iadd(x, y),
            Builder::Llvm(inner) => inner.iadd(x, y),
            Builder::Both(inner) => inner.iadd(x, y),
        }
    }
    fn isub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.isub(x, y),
            Builder::Llvm(inner) => inner.isub(x, y),
            Builder::Both(inner) => inner.isub(x, y),
        }
    }
    fn imul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.imul(x, y),
            Builder::Llvm(inner) => inner.imul(x, y),
            Builder::Both(inner) => inner.imul(x, y),
        }
    }
    fn udiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.udiv(x, y),
            Builder::Llvm(inner) => inner.udiv(x, y),
            Builder::Both(inner) => inner.udiv(x, y),
        }
    }
    fn sdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.sdiv(x, y),
            Builder::Llvm(inner) => inner.sdiv(x, y),
            Builder::Both(inner) => inner.sdiv(x, y),
        }
    }
    fn urem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.urem(x, y),
            Builder::Llvm(inner) => inner.urem(x, y),
            Builder::Both(inner) => inner.urem(x, y),
        }
    }
    fn srem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.srem(x, y),
            Builder::Llvm(inner) => inner.srem(x, y),
            Builder::Both(inner) => inner.srem(x, y),
        }
    }
    fn band(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.band(x, y),
            Builder::Llvm(inner) => inner.band(x, y),
            Builder::Both(inner) => inner.band(x, y),
        }
    }
    fn bor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bor(x, y),
            Builder::Llvm(inner) => inner.bor(x, y),
            Builder::Both(inner) => inner.bor(x, y),
        }
    }
    fn bxor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bxor(x, y),
            Builder::Llvm(inner) => inner.bxor(x, y),
            Builder::Both(inner) => inner.bxor(x, y),
        }
    }
    fn band_not(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.band_not(x, y),
            Builder::Llvm(inner) => inner.band_not(x, y),
            Builder::Both(inner) => inner.band_not(x, y),
        }
    }
    fn bnot(&mut self, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bnot(x),
            Builder::Llvm(inner) => inner.bnot(x),
            Builder::Both(inner) => inner.bnot(x),
        }
    }
    fn ineg(&mut self, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.ineg(x),
            Builder::Llvm(inner) => inner.ineg(x),
            Builder::Both(inner) => inner.ineg(x),
        }
    }
    fn ishl(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.ishl(x, y),
            Builder::Llvm(inner) => inner.ishl(x, y),
            Builder::Both(inner) => inner.ishl(x, y),
        }
    }
    fn ushr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.ushr(x, y),
            Builder::Llvm(inner) => inner.ushr(x, y),
            Builder::Both(inner) => inner.ushr(x, y),
        }
    }
    fn sshr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.sshr(x, y),
            Builder::Llvm(inner) => inner.sshr(x, y),
            Builder::Both(inner) => inner.sshr(x, y),
        }
    }
    fn umax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.umax(x, y),
            Builder::Llvm(inner) => inner.umax(x, y),
            Builder::Both(inner) => inner.umax(x, y),
        }
    }
    fn umin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.umin(x, y),
            Builder::Llvm(inner) => inner.umin(x, y),
            Builder::Both(inner) => inner.umin(x, y),
        }
    }
    fn smax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.smax(x, y),
            Builder::Llvm(inner) => inner.smax(x, y),
            Builder::Both(inner) => inner.smax(x, y),
        }
    }
    fn smin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.smin(x, y),
            Builder::Llvm(inner) => inner.smin(x, y),
            Builder::Both(inner) => inner.smin(x, y),
        }
    }
    fn clz(&mut self, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.clz(x),
            Builder::Llvm(inner) => inner.clz(x),
            Builder::Both(inner) => inner.clz(x),
        }
    }
    fn iadd_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.iadd_imm_s(x, y),
            Builder::Llvm(inner) => inner.iadd_imm_s(x, y),
            Builder::Both(inner) => inner.iadd_imm_s(x, y),
        }
    }
    fn imul_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.imul_imm_s(x, y),
            Builder::Llvm(inner) => inner.imul_imm_s(x, y),
            Builder::Both(inner) => inner.imul_imm_s(x, y),
        }
    }
    fn band_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.band_imm_s(x, y),
            Builder::Llvm(inner) => inner.band_imm_s(x, y),
            Builder::Both(inner) => inner.band_imm_s(x, y),
        }
    }
    fn bor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bor_imm_s(x, y),
            Builder::Llvm(inner) => inner.bor_imm_s(x, y),
            Builder::Both(inner) => inner.bor_imm_s(x, y),
        }
    }
    fn bxor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bxor_imm_s(x, y),
            Builder::Llvm(inner) => inner.bxor_imm_s(x, y),
            Builder::Both(inner) => inner.bxor_imm_s(x, y),
        }
    }
    fn icmp(&mut self, cond: impl Into<IntCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.icmp(cond, x, y),
            Builder::Llvm(inner) => inner.icmp(cond, x, y),
            Builder::Both(inner) => inner.icmp(cond, x, y),
        }
    }
    fn icmp_imm_s(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.icmp_imm_s(cond, x, y),
            Builder::Llvm(inner) => inner.icmp_imm_s(cond, x, y),
            Builder::Both(inner) => inner.icmp_imm_s(cond, x, y),
        }
    }
    fn icmp_imm_u(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.icmp_imm_u(cond, x, y),
            Builder::Llvm(inner) => inner.icmp_imm_u(cond, x, y),
            Builder::Both(inner) => inner.icmp_imm_u(cond, x, y),
        }
    }
    fn select(&mut self, c: ir::Value, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.select(c, x, y),
            Builder::Llvm(inner) => inner.select(c, x, y),
            Builder::Both(inner) => inner.select(c, x, y),
        }
    }
    fn uextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.uextend(ty, x),
            Builder::Llvm(inner) => inner.uextend(ty, x),
            Builder::Both(inner) => inner.uextend(ty, x),
        }
    }
    fn sextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.sextend(ty, x),
            Builder::Llvm(inner) => inner.sextend(ty, x),
            Builder::Both(inner) => inner.sextend(ty, x),
        }
    }
    fn ireduce(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.ireduce(ty, x),
            Builder::Llvm(inner) => inner.ireduce(ty, x),
            Builder::Both(inner) => inner.ireduce(ty, x),
        }
    }
    fn sadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.sadd_overflow(x, y),
            Builder::Llvm(inner) => inner.sadd_overflow(x, y),
            Builder::Both(inner) => inner.sadd_overflow(x, y),
        }
    }
    fn ssub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.ssub_overflow(x, y),
            Builder::Llvm(inner) => inner.ssub_overflow(x, y),
            Builder::Both(inner) => inner.ssub_overflow(x, y),
        }
    }
    fn smul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.smul_overflow(x, y),
            Builder::Llvm(inner) => inner.smul_overflow(x, y),
            Builder::Both(inner) => inner.smul_overflow(x, y),
        }
    }
    fn uadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.uadd_overflow(x, y),
            Builder::Llvm(inner) => inner.uadd_overflow(x, y),
            Builder::Both(inner) => inner.uadd_overflow(x, y),
        }
    }
    fn usub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.usub_overflow(x, y),
            Builder::Llvm(inner) => inner.usub_overflow(x, y),
            Builder::Both(inner) => inner.usub_overflow(x, y),
        }
    }
    fn umul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        match self {
            Builder::Cranelift(inner) => inner.umul_overflow(x, y),
            Builder::Llvm(inner) => inner.umul_overflow(x, y),
            Builder::Both(inner) => inner.umul_overflow(x, y),
        }
    }
    fn fadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fadd(x, y),
            Builder::Llvm(inner) => inner.fadd(x, y),
            Builder::Both(inner) => inner.fadd(x, y),
        }
    }
    fn fsub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fsub(x, y),
            Builder::Llvm(inner) => inner.fsub(x, y),
            Builder::Both(inner) => inner.fsub(x, y),
        }
    }
    fn fmul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fmul(x, y),
            Builder::Llvm(inner) => inner.fmul(x, y),
            Builder::Both(inner) => inner.fmul(x, y),
        }
    }
    fn fdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fdiv(x, y),
            Builder::Llvm(inner) => inner.fdiv(x, y),
            Builder::Both(inner) => inner.fdiv(x, y),
        }
    }
    fn sqrt(&mut self, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.sqrt(x),
            Builder::Llvm(inner) => inner.sqrt(x),
            Builder::Both(inner) => inner.sqrt(x),
        }
    }
    fn fcmp(&mut self, cond: impl Into<FloatCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fcmp(cond, x, y),
            Builder::Llvm(inner) => inner.fcmp(cond, x, y),
            Builder::Both(inner) => inner.fcmp(cond, x, y),
        }
    }
    fn fpromote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fpromote(ty, x),
            Builder::Llvm(inner) => inner.fpromote(ty, x),
            Builder::Both(inner) => inner.fpromote(ty, x),
        }
    }
    fn fdemote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.fdemote(ty, x),
            Builder::Llvm(inner) => inner.fdemote(ty, x),
            Builder::Both(inner) => inner.fdemote(ty, x),
        }
    }
    fn bitcast(&mut self, ty: ir::Type, flags: impl Into<MemFlagsData>, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.bitcast(ty, flags, x),
            Builder::Llvm(inner) => inner.bitcast(ty, flags, x),
            Builder::Both(inner) => inner.bitcast(ty, flags, x),
        }
    }
    fn extractlane(&mut self, x: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.extractlane(x, lane),
            Builder::Llvm(inner) => inner.extractlane(x, lane),
            Builder::Both(inner) => inner.extractlane(x, lane),
        }
    }
    fn insertlane(&mut self, x: ir::Value, y: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.insertlane(x, y, lane),
            Builder::Llvm(inner) => inner.insertlane(x, y, lane),
            Builder::Both(inner) => inner.insertlane(x, y, lane),
        }
    }
    fn scalar_to_vector(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.scalar_to_vector(ty, x),
            Builder::Llvm(inner) => inner.scalar_to_vector(ty, x),
            Builder::Both(inner) => inner.scalar_to_vector(ty, x),
        }
    }
    fn shuffle(&mut self, a: ir::Value, b: ir::Value, mask: ir::Immediate) -> ir::Value {
        match self {
            Builder::Cranelift(inner) => inner.shuffle(a, b, mask),
            Builder::Llvm(inner) => inner.shuffle(a, b, mask),
            Builder::Both(inner) => inner.shuffle(a, b, mask),
        }
    }
    fn shuffle_mask(&mut self, bytes: &[u8]) -> ir::Immediate {
        match self {
            Builder::Cranelift(inner) => inner.shuffle_mask(bytes),
            Builder::Llvm(inner) => inner.shuffle_mask(bytes),
            Builder::Both(inner) => inner.shuffle_mask(bytes),
        }
    }
}
