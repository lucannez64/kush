//! The instruction builder the native lowering writes to
//! (FND-LLVM-EMIT, docs/mir-design.md section 10).
//!
//! `Emit` has one method per operation the lowering uses, with Cranelift's
//! names and argument order, plus blocks, variables, stack slots, function
//! and data references, and the facts an LLVM builder needs (memory
//! classes). [`Cranelift`] implements it with Cranelift's `FunctionBuilder`;
//! a typed LLVM builder is the second implementation (FND-LLVM-BUILDER).

use cranelift_codegen::ir::{
    self, AtomicRmwOp, BlockArg, InstBuilder, MemFlagsData, TrapCode,
    condcodes::{FloatCC, IntCC},
    immediates::{Imm64, Offset32, Uimm8},
};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{DataId, FuncId, Module};

/// An instruction builder for one function.
pub(super) trait Emit {
    type Value: Copy + PartialEq + std::fmt::Debug;
    type Block: Copy + PartialEq + std::fmt::Debug;
    type Var: Copy;
    type Slot: Copy;
    type FuncRef: Copy;
    type SigRef: Copy;
    type Global: Copy;
    type Inst: Copy;

    // ---- blocks, variables, slots, references ----------------------------
    fn create_block(&mut self) -> Self::Block;
    fn switch_to_block(&mut self, block: Self::Block);
    fn append_block_param(&mut self, block: Self::Block, ty: ir::Type) -> Self::Value;
    fn append_block_params_for_function_params(&mut self, block: Self::Block);
    fn block_params(&self, block: Self::Block) -> &[Self::Value];
    fn seal_all_blocks(&mut self);
    fn declare_var(&mut self, ty: ir::Type) -> Self::Var;
    fn def_var(&mut self, var: Self::Var, value: Self::Value);
    fn use_var(&mut self, var: Self::Var) -> Self::Value;
    fn create_sized_stack_slot(&mut self, data: ir::StackSlotData) -> Self::Slot;
    fn import_signature(&mut self, signature: ir::Signature) -> Self::SigRef;
    fn declare_func(&mut self, module: &mut impl Module, id: FuncId) -> Self::FuncRef;
    fn declare_data(&mut self, module: &mut impl Module, id: DataId) -> Self::Global;
    fn inst_results(&self, inst: Self::Inst) -> &[Self::Value];
    /// The integer a value is, when it is a constant.
    fn constant_of(&self, value: Self::Value) -> Option<i64>;
    fn value_type(&self, value: Self::Value) -> ir::Type;
    /// The memory class of the loads and stores built from now on (`None`:
    /// no class); returns the previous one.
    fn set_memory_class(&mut self, class: Option<u32>) -> Option<u32>;

    // ---- control -----------------------------------------------------------
    fn jump(&mut self, block: Self::Block, args: &[Self::Value]) -> Self::Inst;
    fn brif(
        &mut self,
        condition: Self::Value,
        then: Self::Block,
        then_args: &[Self::Value],
        otherwise: Self::Block,
        otherwise_args: &[Self::Value],
    ) -> Self::Inst;
    fn return_(&mut self, values: &[Self::Value]) -> Self::Inst;
    fn trap(&mut self, code: impl Into<TrapCode>) -> Self::Inst;
    fn call(&mut self, callee: Self::FuncRef, args: &[Self::Value]) -> Self::Inst;
    fn call_indirect(
        &mut self,
        signature: Self::SigRef,
        callee: Self::Value,
        args: &[Self::Value],
    ) -> Self::Inst;

    // ---- constants and addresses ----------------------------------------------
    fn iconst(&mut self, ty: ir::Type, value: impl Into<Imm64>) -> Self::Value;
    fn stack_addr(
        &mut self,
        ty: ir::Type,
        slot: Self::Slot,
        offset: impl Into<Offset32>,
    ) -> Self::Value;
    fn func_addr(&mut self, ty: ir::Type, callee: Self::FuncRef) -> Self::Value;
    fn symbol_value(&mut self, ty: ir::Type, global: Self::Global) -> Self::Value;

    // ---- memory ------------------------------------------------------------
    fn load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: Self::Value,
        offset: impl Into<Offset32>,
    ) -> Self::Value;
    fn uload8(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: Self::Value,
        offset: impl Into<Offset32>,
    ) -> Self::Value;
    fn store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: Self::Value,
        pointer: Self::Value,
        offset: impl Into<Offset32>,
    ) -> Self::Inst;
    fn istore8(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: Self::Value,
        pointer: Self::Value,
        offset: impl Into<Offset32>,
    ) -> Self::Inst;
    fn atomic_load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: Self::Value,
    ) -> Self::Value;
    fn atomic_store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: Self::Value,
        pointer: Self::Value,
    ) -> Self::Inst;
    fn atomic_rmw(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        op: impl Into<AtomicRmwOp>,
        pointer: Self::Value,
        value: Self::Value,
    ) -> Self::Value;
    fn atomic_cas(
        &mut self,
        flags: impl Into<MemFlagsData>,
        pointer: Self::Value,
        expected: Self::Value,
        replacement: Self::Value,
    ) -> Self::Value;

    // ---- integers ----------------------------------------------------------
    fn iadd(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn isub(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn imul(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn udiv(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn sdiv(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn urem(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn srem(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn band(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn bor(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn bxor(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn band_not(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn bnot(&mut self, x: Self::Value) -> Self::Value;
    fn ineg(&mut self, x: Self::Value) -> Self::Value;
    fn ishl(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn ushr(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn sshr(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn umax(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn umin(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn smax(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn smin(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn clz(&mut self, x: Self::Value) -> Self::Value;
    fn iadd_imm_s(&mut self, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn imul_imm_s(&mut self, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn band_imm_s(&mut self, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn bor_imm_s(&mut self, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn bxor_imm_s(&mut self, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn icmp(&mut self, cond: impl Into<IntCC>, x: Self::Value, y: Self::Value) -> Self::Value;
    fn icmp_imm_s(&mut self, cond: IntCC, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn icmp_imm_u(&mut self, cond: IntCC, x: Self::Value, y: impl Into<Imm64>) -> Self::Value;
    fn select(&mut self, c: Self::Value, x: Self::Value, y: Self::Value) -> Self::Value;
    fn uextend(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn sextend(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn ireduce(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn sadd_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);
    fn ssub_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);
    fn smul_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);
    fn uadd_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);
    fn usub_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);
    fn umul_overflow(&mut self, x: Self::Value, y: Self::Value) -> (Self::Value, Self::Value);

    // ---- floats and vectors -----------------------------------------------
    fn fadd(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn fsub(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn fmul(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn fdiv(&mut self, x: Self::Value, y: Self::Value) -> Self::Value;
    fn sqrt(&mut self, x: Self::Value) -> Self::Value;
    fn fcmp(&mut self, cond: impl Into<FloatCC>, x: Self::Value, y: Self::Value) -> Self::Value;
    fn fpromote(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn fdemote(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn bitcast(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        x: Self::Value,
    ) -> Self::Value;
    fn extractlane(&mut self, x: Self::Value, lane: impl Into<Uimm8>) -> Self::Value;
    fn insertlane(&mut self, x: Self::Value, y: Self::Value, lane: impl Into<Uimm8>)
    -> Self::Value;
    fn scalar_to_vector(&mut self, ty: ir::Type, x: Self::Value) -> Self::Value;
    fn shuffle(&mut self, a: Self::Value, b: Self::Value, mask: ir::Immediate) -> Self::Value;
    /// The immediate of a shuffle mask.
    fn shuffle_mask(&mut self, bytes: &[u8]) -> ir::Immediate;
}

/// Cranelift's `FunctionBuilder` as an [`Emit`].
pub(super) struct Cranelift<'a> {
    pub(super) builder: FunctionBuilder<'a>,
}

impl<'a> Cranelift<'a> {
    pub(super) fn new(builder: FunctionBuilder<'a>) -> Self {
        Cranelift { builder }
    }
    pub(super) fn finalize(self, config: cranelift_codegen::isa::TargetFrontendConfig) {
        self.builder.finalize(config);
    }
}

fn block_args(values: &[ir::Value]) -> Vec<BlockArg> {
    values.iter().copied().map(Into::into).collect()
}

impl Emit for Cranelift<'_> {
    type Value = ir::Value;
    type Block = ir::Block;
    type Var = Variable;
    type Slot = ir::StackSlot;
    type FuncRef = ir::FuncRef;
    type SigRef = ir::SigRef;
    type Global = ir::GlobalValue;
    type Inst = ir::Inst;

    fn create_block(&mut self) -> ir::Block {
        self.builder.create_block()
    }
    fn switch_to_block(&mut self, block: ir::Block) {
        self.builder.switch_to_block(block);
    }
    fn append_block_param(&mut self, block: ir::Block, ty: ir::Type) -> ir::Value {
        self.builder.append_block_param(block, ty)
    }
    fn append_block_params_for_function_params(&mut self, block: ir::Block) {
        self.builder.append_block_params_for_function_params(block);
    }
    fn block_params(&self, block: ir::Block) -> &[ir::Value] {
        self.builder.block_params(block)
    }
    fn seal_all_blocks(&mut self) {
        self.builder.seal_all_blocks();
    }
    fn declare_var(&mut self, ty: ir::Type) -> Variable {
        self.builder.declare_var(ty)
    }
    fn def_var(&mut self, var: Variable, value: ir::Value) {
        self.builder.def_var(var, value);
    }
    fn use_var(&mut self, var: Variable) -> ir::Value {
        self.builder.use_var(var)
    }
    fn create_sized_stack_slot(&mut self, data: ir::StackSlotData) -> ir::StackSlot {
        self.builder.create_sized_stack_slot(data)
    }
    fn import_signature(&mut self, signature: ir::Signature) -> ir::SigRef {
        self.builder.import_signature(signature)
    }
    fn declare_func(&mut self, module: &mut impl Module, id: FuncId) -> ir::FuncRef {
        module.declare_func_in_func(id, self.builder.func)
    }
    fn declare_data(&mut self, module: &mut impl Module, id: DataId) -> ir::GlobalValue {
        module.declare_data_in_func(id, self.builder.func)
    }
    fn inst_results(&self, inst: ir::Inst) -> &[ir::Value] {
        self.builder.inst_results(inst)
    }
    fn constant_of(&self, value: ir::Value) -> Option<i64> {
        let ir::ValueDef::Result(inst, _) = self.builder.func.dfg.value_def(value) else {
            return None;
        };
        match self.builder.func.dfg.insts[inst] {
            ir::InstructionData::UnaryImm {
                opcode: ir::Opcode::Iconst,
                imm,
            } => Some(imm.bits()),
            _ => None,
        }
    }
    fn value_type(&self, value: ir::Value) -> ir::Type {
        self.builder.func.dfg.value_type(value)
    }
    fn set_memory_class(&mut self, class: Option<u32>) -> Option<u32> {
        // The class travels as the instructions' source location, which
        // Cranelift's code generator ignores and the LLVM translator turns
        // into alias metadata. Locations are stored relative to a base: fix
        // it at zero so that no class coincides with "no location".
        self.builder
            .func
            .params
            .ensure_base_srcloc(ir::SourceLoc::new(0));
        let previous = self.builder.srcloc();
        self.builder.set_srcloc(match class {
            Some(class) => ir::SourceLoc::new(class),
            None => ir::SourceLoc::default(),
        });
        (!previous.is_default()).then(|| previous.bits())
    }

    fn jump(&mut self, block: ir::Block, args: &[ir::Value]) -> ir::Inst {
        self.builder.ins().jump(block, &block_args(args))
    }
    fn brif(
        &mut self,
        condition: ir::Value,
        then: ir::Block,
        then_args: &[ir::Value],
        otherwise: ir::Block,
        otherwise_args: &[ir::Value],
    ) -> ir::Inst {
        self.builder.ins().brif(
            condition,
            then,
            &block_args(then_args),
            otherwise,
            &block_args(otherwise_args),
        )
    }
    fn return_(&mut self, values: &[ir::Value]) -> ir::Inst {
        self.builder.ins().return_(values)
    }
    fn trap(&mut self, code: impl Into<TrapCode>) -> ir::Inst {
        self.builder.ins().trap(code)
    }
    fn call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        self.builder.ins().call(callee, args)
    }
    fn call_indirect(
        &mut self,
        signature: ir::SigRef,
        callee: ir::Value,
        args: &[ir::Value],
    ) -> ir::Inst {
        self.builder.ins().call_indirect(signature, callee, args)
    }

    fn iconst(&mut self, ty: ir::Type, value: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().iconst(ty, value)
    }
    fn stack_addr(
        &mut self,
        ty: ir::Type,
        slot: ir::StackSlot,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        self.builder.ins().stack_addr(ty, slot, offset)
    }
    fn func_addr(&mut self, ty: ir::Type, callee: ir::FuncRef) -> ir::Value {
        self.builder.ins().func_addr(ty, callee)
    }
    fn symbol_value(&mut self, ty: ir::Type, global: ir::GlobalValue) -> ir::Value {
        self.builder.ins().symbol_value(ty, global)
    }

    fn load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        self.builder.ins().load(ty, flags, pointer, offset)
    }
    fn uload8(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        self.builder.ins().uload8(ty, flags, pointer, offset)
    }
    fn store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        self.builder.ins().store(flags, value, pointer, offset)
    }
    fn istore8(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        self.builder.ins().istore8(flags, value, pointer, offset)
    }
    fn atomic_load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
    ) -> ir::Value {
        self.builder.ins().atomic_load(ty, flags, pointer)
    }
    fn atomic_store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
    ) -> ir::Inst {
        self.builder.ins().atomic_store(flags, value, pointer)
    }
    fn atomic_rmw(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        op: impl Into<AtomicRmwOp>,
        pointer: ir::Value,
        value: ir::Value,
    ) -> ir::Value {
        self.builder.ins().atomic_rmw(ty, flags, op, pointer, value)
    }
    fn atomic_cas(
        &mut self,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        expected: ir::Value,
        replacement: ir::Value,
    ) -> ir::Value {
        self.builder
            .ins()
            .atomic_cas(flags, pointer, expected, replacement)
    }

    fn iadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().iadd(x, y)
    }
    fn isub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().isub(x, y)
    }
    fn imul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().imul(x, y)
    }
    fn udiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().udiv(x, y)
    }
    fn sdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().sdiv(x, y)
    }
    fn urem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().urem(x, y)
    }
    fn srem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().srem(x, y)
    }
    fn band(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().band(x, y)
    }
    fn bor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().bor(x, y)
    }
    fn bxor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().bxor(x, y)
    }
    fn band_not(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().band_not(x, y)
    }
    fn bnot(&mut self, x: ir::Value) -> ir::Value {
        self.builder.ins().bnot(x)
    }
    fn ineg(&mut self, x: ir::Value) -> ir::Value {
        self.builder.ins().ineg(x)
    }
    fn ishl(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().ishl(x, y)
    }
    fn ushr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().ushr(x, y)
    }
    fn sshr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().sshr(x, y)
    }
    fn umax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().umax(x, y)
    }
    fn umin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().umin(x, y)
    }
    fn smax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().smax(x, y)
    }
    fn smin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().smin(x, y)
    }
    fn clz(&mut self, x: ir::Value) -> ir::Value {
        self.builder.ins().clz(x)
    }
    fn iadd_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().iadd_imm_s(x, y)
    }
    fn imul_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().imul_imm_s(x, y)
    }
    fn band_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().band_imm_s(x, y)
    }
    fn bor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().bor_imm_s(x, y)
    }
    fn bxor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().bxor_imm_s(x, y)
    }
    fn icmp(&mut self, cond: impl Into<IntCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().icmp(cond, x, y)
    }
    fn icmp_imm_s(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().icmp_imm_s(cond, x, y)
    }
    fn icmp_imm_u(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        self.builder.ins().icmp_imm_u(cond, x, y)
    }
    fn select(&mut self, c: ir::Value, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().select(c, x, y)
    }
    fn uextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().uextend(ty, x)
    }
    fn sextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().sextend(ty, x)
    }
    fn ireduce(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().ireduce(ty, x)
    }
    fn sadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().sadd_overflow(x, y)
    }
    fn ssub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().ssub_overflow(x, y)
    }
    fn smul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().smul_overflow(x, y)
    }
    fn uadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().uadd_overflow(x, y)
    }
    fn usub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().usub_overflow(x, y)
    }
    fn umul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.builder.ins().umul_overflow(x, y)
    }

    fn fadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().fadd(x, y)
    }
    fn fsub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().fsub(x, y)
    }
    fn fmul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().fmul(x, y)
    }
    fn fdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().fdiv(x, y)
    }
    fn sqrt(&mut self, x: ir::Value) -> ir::Value {
        self.builder.ins().sqrt(x)
    }
    fn fcmp(&mut self, cond: impl Into<FloatCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        self.builder.ins().fcmp(cond, x, y)
    }
    fn fpromote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().fpromote(ty, x)
    }
    fn fdemote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().fdemote(ty, x)
    }
    fn bitcast(&mut self, ty: ir::Type, flags: impl Into<MemFlagsData>, x: ir::Value) -> ir::Value {
        self.builder.ins().bitcast(ty, flags, x)
    }
    fn extractlane(&mut self, x: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        self.builder.ins().extractlane(x, lane)
    }
    fn insertlane(&mut self, x: ir::Value, y: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        self.builder.ins().insertlane(x, y, lane)
    }
    fn scalar_to_vector(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.builder.ins().scalar_to_vector(ty, x)
    }
    fn shuffle(&mut self, a: ir::Value, b: ir::Value, mask: ir::Immediate) -> ir::Value {
        self.builder.ins().shuffle(a, b, mask)
    }
    fn shuffle_mask(&mut self, bytes: &[u8]) -> ir::Immediate {
        self.builder
            .func
            .dfg
            .immediates
            .push(ir::ConstantData::from(bytes))
    }
}
