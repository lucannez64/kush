//! One lowering fed to both code generators (FND-LLVM-SWITCH).
//!
//! A staging recipe needs Cranelift's machine code, which the staging
//! runtime copies, and an LLVM definition in the program module; a build
//! that dumps Cranelift IR needs that IR next to the LLVM module. [`Both`]
//! passes every call to Cranelift and to the typed LLVM builder and answers
//! with Cranelift's handles, keeping the LLVM builder's handle for each.
//!
//! Generated from the `Emit` trait: one method per trait method.
use super::emit::{Cranelift, Emit};
use super::llvm_builder::LlvmBuilder;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::{
    self, AtomicRmwOp, MemFlagsData, TrapCode,
    condcodes::{FloatCC, IntCC},
    immediates::{Imm64, Offset32, Uimm8},
};
use cranelift_frontend::Variable;
use cranelift_module::{DataId, FuncId, Module};

/// For each Cranelift handle (by index), the LLVM builder's handle.
struct Map<K, V>(Vec<Option<V>>, std::marker::PhantomData<K>);

impl<K: EntityRef, V: Copy> Map<K, V> {
    fn new() -> Self {
        Map(Vec::new(), std::marker::PhantomData)
    }
    fn set(&mut self, key: K, value: V) {
        let index = key.index();
        if self.0.len() <= index {
            self.0.resize(index + 1, None);
        }
        self.0[index] = Some(value);
    }
    fn get(&self, key: K) -> V {
        self.0
            .get(key.index())
            .copied()
            .flatten()
            .expect("a handle the LLVM builder was given")
    }
}

/// Cranelift and the typed LLVM builder, fed the same calls.
pub(super) struct Both<'a> {
    pub(super) cranelift: Cranelift<'a>,
    pub(super) llvm: LlvmBuilder,
    values: Map<ir::Value, ir::Value>,
    blocks: Map<ir::Block, ir::Block>,
    variables: Map<Variable, Variable>,
    slots: Map<ir::StackSlot, ir::StackSlot>,
    signatures: Map<ir::SigRef, ir::SigRef>,
    functions: Map<ir::FuncRef, ir::FuncRef>,
    globals: Map<ir::GlobalValue, ir::GlobalValue>,
    immediates: Map<ir::Immediate, ir::Immediate>,
}

impl<'a> Both<'a> {
    pub(super) fn new(cranelift: Cranelift<'a>, llvm: LlvmBuilder) -> Self {
        Both {
            cranelift,
            llvm,
            values: Map::new(),
            blocks: Map::new(),
            variables: Map::new(),
            slots: Map::new(),
            signatures: Map::new(),
            functions: Map::new(),
            globals: Map::new(),
            immediates: Map::new(),
        }
    }
    fn vs(&self, values: &[ir::Value]) -> Vec<ir::Value> {
        values.iter().map(|value| self.values.get(*value)).collect()
    }
    /// Pair the results of one instruction built by both.
    fn results(&mut self, cranelift: ir::Inst, llvm: ir::Inst) -> ir::Inst {
        let pairs: Vec<(ir::Value, ir::Value)> = self
            .cranelift
            .inst_results(cranelift)
            .iter()
            .copied()
            .zip(self.llvm.inst_results(llvm).iter().copied())
            .collect();
        for (cranelift, llvm) in pairs {
            self.values.set(cranelift, llvm);
        }
        cranelift
    }
}

impl Emit for Both<'_> {
    fn create_block(&mut self) -> ir::Block {
        let cranelift = self.cranelift.create_block();
        let llvm = self.llvm.create_block();
        self.blocks.set(cranelift, llvm);
        cranelift
    }
    fn switch_to_block(&mut self, block: ir::Block) {
        let l0 = self.blocks.get(block);
        self.cranelift.switch_to_block(block);
        self.llvm.switch_to_block(l0);
    }
    fn append_block_param(&mut self, block: ir::Block, ty: ir::Type) -> ir::Value {
        let l0 = self.blocks.get(block);
        let cranelift = self.cranelift.append_block_param(block, ty);
        let llvm = self.llvm.append_block_param(l0, ty);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn append_block_params_for_function_params(&mut self, block: ir::Block) {
        let l0 = self.blocks.get(block);
        self.cranelift
            .append_block_params_for_function_params(block);
        self.llvm.append_block_params_for_function_params(l0);
        let pairs: Vec<(ir::Value, ir::Value)> = self
            .cranelift
            .block_params(block)
            .iter()
            .copied()
            .zip(self.llvm.block_params(l0).iter().copied())
            .collect();
        for (cranelift, llvm) in pairs {
            self.values.set(cranelift, llvm);
        }
    }
    fn block_params(&self, block: ir::Block) -> &[ir::Value] {
        self.cranelift.block_params(block)
    }
    fn seal_all_blocks(&mut self) {
        self.cranelift.seal_all_blocks();
        self.llvm.seal_all_blocks();
    }
    fn declare_var(&mut self, ty: ir::Type) -> Variable {
        let cranelift = self.cranelift.declare_var(ty);
        let llvm = self.llvm.declare_var(ty);
        self.variables.set(cranelift, llvm);
        cranelift
    }
    fn def_var(&mut self, var: Variable, value: ir::Value) {
        let l0 = self.variables.get(var);
        let l1 = self.values.get(value);
        self.cranelift.def_var(var, value);
        self.llvm.def_var(l0, l1);
    }
    fn use_var(&mut self, var: Variable) -> ir::Value {
        let l0 = self.variables.get(var);
        let cranelift = self.cranelift.use_var(var);
        let llvm = self.llvm.use_var(l0);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn create_sized_stack_slot(&mut self, data: ir::StackSlotData) -> ir::StackSlot {
        let cranelift = self.cranelift.create_sized_stack_slot(data.clone());
        let llvm = self.llvm.create_sized_stack_slot(data);
        self.slots.set(cranelift, llvm);
        cranelift
    }
    fn import_signature(&mut self, signature: ir::Signature) -> ir::SigRef {
        let cranelift = self.cranelift.import_signature(signature.clone());
        let llvm = self.llvm.import_signature(signature);
        self.signatures.set(cranelift, llvm);
        cranelift
    }
    fn declare_func(&mut self, module: &mut impl Module, id: FuncId) -> ir::FuncRef {
        let cranelift = self.cranelift.declare_func(module, id);
        let llvm = self.llvm.declare_func(module, id);
        self.functions.set(cranelift, llvm);
        cranelift
    }
    fn declare_data(&mut self, module: &mut impl Module, id: DataId) -> ir::GlobalValue {
        let cranelift = self.cranelift.declare_data(module, id);
        let llvm = self.llvm.declare_data(module, id);
        self.globals.set(cranelift, llvm);
        cranelift
    }
    fn inst_results(&self, inst: ir::Inst) -> &[ir::Value] {
        self.cranelift.inst_results(inst)
    }
    fn constant_of(&self, value: ir::Value) -> Option<i64> {
        self.cranelift.constant_of(value)
    }
    fn value_type(&self, value: ir::Value) -> ir::Type {
        self.cranelift.value_type(value)
    }
    fn set_memory_class(&mut self, class: Option<u32>) -> Option<u32> {
        let cranelift = self.cranelift.set_memory_class(class);
        self.llvm.set_memory_class(class);
        cranelift
    }
    fn jump(&mut self, block: ir::Block, args: &[ir::Value]) -> ir::Inst {
        let l0 = self.blocks.get(block);
        let l1 = &self.vs(args);
        let cranelift = self.cranelift.jump(block, args);
        let llvm = self.llvm.jump(l0, l1);
        self.results(cranelift, llvm)
    }
    fn brif(
        &mut self,
        condition: ir::Value,
        then: ir::Block,
        then_args: &[ir::Value],
        otherwise: ir::Block,
        otherwise_args: &[ir::Value],
    ) -> ir::Inst {
        let l0 = self.values.get(condition);
        let l1 = self.blocks.get(then);
        let l2 = &self.vs(then_args);
        let l3 = self.blocks.get(otherwise);
        let l4 = &self.vs(otherwise_args);
        let cranelift = self
            .cranelift
            .brif(condition, then, then_args, otherwise, otherwise_args);
        let llvm = self.llvm.brif(l0, l1, l2, l3, l4);
        self.results(cranelift, llvm)
    }
    fn return_(&mut self, values: &[ir::Value]) -> ir::Inst {
        let l0 = &self.vs(values);
        let cranelift = self.cranelift.return_(values);
        let llvm = self.llvm.return_(l0);
        self.results(cranelift, llvm)
    }
    fn trap(&mut self, code: impl Into<TrapCode>) -> ir::Inst {
        let code: TrapCode = code.into();
        let cranelift = self.cranelift.trap(code);
        let llvm = self.llvm.trap(code);
        self.results(cranelift, llvm)
    }
    fn call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        let l0 = self.functions.get(callee);
        let l1 = &self.vs(args);
        let cranelift = self.cranelift.call(callee, args);
        let llvm = self.llvm.call(l0, l1);
        self.results(cranelift, llvm)
    }
    fn call_indirect(
        &mut self,
        signature: ir::SigRef,
        callee: ir::Value,
        args: &[ir::Value],
    ) -> ir::Inst {
        let l0 = self.signatures.get(signature);
        let l1 = self.values.get(callee);
        let l2 = &self.vs(args);
        let cranelift = self.cranelift.call_indirect(signature, callee, args);
        let llvm = self.llvm.call_indirect(l0, l1, l2);
        self.results(cranelift, llvm)
    }
    fn iconst(&mut self, ty: ir::Type, value: impl Into<Imm64>) -> ir::Value {
        let value: Imm64 = value.into();
        let cranelift = self.cranelift.iconst(ty, value);
        let llvm = self.llvm.iconst(ty, value);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn stack_addr(
        &mut self,
        ty: ir::Type,
        slot: ir::StackSlot,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        let offset: Offset32 = offset.into();
        let l1 = self.slots.get(slot);
        let cranelift = self.cranelift.stack_addr(ty, slot, offset);
        let llvm = self.llvm.stack_addr(ty, l1, offset);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn func_addr(&mut self, ty: ir::Type, callee: ir::FuncRef) -> ir::Value {
        let l1 = self.functions.get(callee);
        let cranelift = self.cranelift.func_addr(ty, callee);
        let llvm = self.llvm.func_addr(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn symbol_value(&mut self, ty: ir::Type, global: ir::GlobalValue) -> ir::Value {
        let l1 = self.globals.get(global);
        let cranelift = self.cranelift.symbol_value(ty, global);
        let llvm = self.llvm.symbol_value(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let offset: Offset32 = offset.into();
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.load(ty, flags, pointer, offset);
        let llvm = self.llvm.load(ty, flags, l2, offset);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn uload8(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let offset: Offset32 = offset.into();
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.uload8(ty, flags, pointer, offset);
        let llvm = self.llvm.uload8(ty, flags, l2, offset);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        let flags: MemFlagsData = flags.into();
        let offset: Offset32 = offset.into();
        let l1 = self.values.get(value);
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.store(flags, value, pointer, offset);
        let llvm = self.llvm.store(flags, l1, l2, offset);
        self.results(cranelift, llvm)
    }
    fn istore8(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        let flags: MemFlagsData = flags.into();
        let offset: Offset32 = offset.into();
        let l1 = self.values.get(value);
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.istore8(flags, value, pointer, offset);
        let llvm = self.llvm.istore8(flags, l1, l2, offset);
        self.results(cranelift, llvm)
    }
    fn atomic_load(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
    ) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.atomic_load(ty, flags, pointer);
        let llvm = self.llvm.atomic_load(ty, flags, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn atomic_store(
        &mut self,
        flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
    ) -> ir::Inst {
        let flags: MemFlagsData = flags.into();
        let l1 = self.values.get(value);
        let l2 = self.values.get(pointer);
        let cranelift = self.cranelift.atomic_store(flags, value, pointer);
        let llvm = self.llvm.atomic_store(flags, l1, l2);
        self.results(cranelift, llvm)
    }
    fn atomic_rmw(
        &mut self,
        ty: ir::Type,
        flags: impl Into<MemFlagsData>,
        op: impl Into<AtomicRmwOp>,
        pointer: ir::Value,
        value: ir::Value,
    ) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let op: AtomicRmwOp = op.into();
        let l3 = self.values.get(pointer);
        let l4 = self.values.get(value);
        let cranelift = self.cranelift.atomic_rmw(ty, flags, op, pointer, value);
        let llvm = self.llvm.atomic_rmw(ty, flags, op, l3, l4);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn atomic_cas(
        &mut self,
        flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        expected: ir::Value,
        replacement: ir::Value,
    ) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let l1 = self.values.get(pointer);
        let l2 = self.values.get(expected);
        let l3 = self.values.get(replacement);
        let cranelift = self
            .cranelift
            .atomic_cas(flags, pointer, expected, replacement);
        let llvm = self.llvm.atomic_cas(flags, l1, l2, l3);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn iadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.iadd(x, y);
        let llvm = self.llvm.iadd(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn isub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.isub(x, y);
        let llvm = self.llvm.isub(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn imul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.imul(x, y);
        let llvm = self.llvm.imul(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn udiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.udiv(x, y);
        let llvm = self.llvm.udiv(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn sdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.sdiv(x, y);
        let llvm = self.llvm.sdiv(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn urem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.urem(x, y);
        let llvm = self.llvm.urem(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn srem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.srem(x, y);
        let llvm = self.llvm.srem(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn band(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.band(x, y);
        let llvm = self.llvm.band(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.bor(x, y);
        let llvm = self.llvm.bor(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bxor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.bxor(x, y);
        let llvm = self.llvm.bxor(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn band_not(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.band_not(x, y);
        let llvm = self.llvm.band_not(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bnot(&mut self, x: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.bnot(x);
        let llvm = self.llvm.bnot(l0);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn ineg(&mut self, x: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.ineg(x);
        let llvm = self.llvm.ineg(l0);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn ishl(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.ishl(x, y);
        let llvm = self.llvm.ishl(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn ushr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.ushr(x, y);
        let llvm = self.llvm.ushr(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn sshr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.sshr(x, y);
        let llvm = self.llvm.sshr(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn umax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.umax(x, y);
        let llvm = self.llvm.umax(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn umin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.umin(x, y);
        let llvm = self.llvm.umin(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn smax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.smax(x, y);
        let llvm = self.llvm.smax(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn smin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.smin(x, y);
        let llvm = self.llvm.smin(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn clz(&mut self, x: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.clz(x);
        let llvm = self.llvm.clz(l0);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn iadd_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.iadd_imm_s(x, y);
        let llvm = self.llvm.iadd_imm_s(l0, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn imul_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.imul_imm_s(x, y);
        let llvm = self.llvm.imul_imm_s(l0, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn band_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.band_imm_s(x, y);
        let llvm = self.llvm.band_imm_s(l0, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.bor_imm_s(x, y);
        let llvm = self.llvm.bor_imm_s(l0, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bxor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.bxor_imm_s(x, y);
        let llvm = self.llvm.bxor_imm_s(l0, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn icmp(&mut self, cond: impl Into<IntCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        let cond: IntCC = cond.into();
        let l1 = self.values.get(x);
        let l2 = self.values.get(y);
        let cranelift = self.cranelift.icmp(cond, x, y);
        let llvm = self.llvm.icmp(cond, l1, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn icmp_imm_s(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.icmp_imm_s(cond, x, y);
        let llvm = self.llvm.icmp_imm_s(cond, l1, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn icmp_imm_u(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y: Imm64 = y.into();
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.icmp_imm_u(cond, x, y);
        let llvm = self.llvm.icmp_imm_u(cond, l1, y);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn select(&mut self, c: ir::Value, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(c);
        let l1 = self.values.get(x);
        let l2 = self.values.get(y);
        let cranelift = self.cranelift.select(c, x, y);
        let llvm = self.llvm.select(l0, l1, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn uextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.uextend(ty, x);
        let llvm = self.llvm.uextend(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn sextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.sextend(ty, x);
        let llvm = self.llvm.sextend(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn ireduce(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.ireduce(ty, x);
        let llvm = self.llvm.ireduce(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn sadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.sadd_overflow(x, y);
        let llvm = self.llvm.sadd_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn ssub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.ssub_overflow(x, y);
        let llvm = self.llvm.ssub_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn smul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.smul_overflow(x, y);
        let llvm = self.llvm.smul_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn uadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.uadd_overflow(x, y);
        let llvm = self.llvm.uadd_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn usub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.usub_overflow(x, y);
        let llvm = self.llvm.usub_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn umul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.umul_overflow(x, y);
        let llvm = self.llvm.umul_overflow(l0, l1);
        self.values.set(cranelift.0, llvm.0);
        self.values.set(cranelift.1, llvm.1);
        cranelift
    }
    fn fadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.fadd(x, y);
        let llvm = self.llvm.fadd(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fsub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.fsub(x, y);
        let llvm = self.llvm.fsub(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fmul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.fmul(x, y);
        let llvm = self.llvm.fmul(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.fdiv(x, y);
        let llvm = self.llvm.fdiv(l0, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn sqrt(&mut self, x: ir::Value) -> ir::Value {
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.sqrt(x);
        let llvm = self.llvm.sqrt(l0);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fcmp(&mut self, cond: impl Into<FloatCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        let cond: FloatCC = cond.into();
        let l1 = self.values.get(x);
        let l2 = self.values.get(y);
        let cranelift = self.cranelift.fcmp(cond, x, y);
        let llvm = self.llvm.fcmp(cond, l1, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fpromote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.fpromote(ty, x);
        let llvm = self.llvm.fpromote(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn fdemote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.fdemote(ty, x);
        let llvm = self.llvm.fdemote(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn bitcast(&mut self, ty: ir::Type, flags: impl Into<MemFlagsData>, x: ir::Value) -> ir::Value {
        let flags: MemFlagsData = flags.into();
        let l2 = self.values.get(x);
        let cranelift = self.cranelift.bitcast(ty, flags, x);
        let llvm = self.llvm.bitcast(ty, flags, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn extractlane(&mut self, x: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        let lane: Uimm8 = lane.into();
        let l0 = self.values.get(x);
        let cranelift = self.cranelift.extractlane(x, lane);
        let llvm = self.llvm.extractlane(l0, lane);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn insertlane(&mut self, x: ir::Value, y: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        let lane: Uimm8 = lane.into();
        let l0 = self.values.get(x);
        let l1 = self.values.get(y);
        let cranelift = self.cranelift.insertlane(x, y, lane);
        let llvm = self.llvm.insertlane(l0, l1, lane);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn scalar_to_vector(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let l1 = self.values.get(x);
        let cranelift = self.cranelift.scalar_to_vector(ty, x);
        let llvm = self.llvm.scalar_to_vector(ty, l1);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn shuffle(&mut self, a: ir::Value, b: ir::Value, mask: ir::Immediate) -> ir::Value {
        let l0 = self.values.get(a);
        let l1 = self.values.get(b);
        let l2 = self.immediates.get(mask);
        let cranelift = self.cranelift.shuffle(a, b, mask);
        let llvm = self.llvm.shuffle(l0, l1, l2);
        self.values.set(cranelift, llvm);
        cranelift
    }
    fn shuffle_mask(&mut self, bytes: &[u8]) -> ir::Immediate {
        let cranelift = self.cranelift.shuffle_mask(bytes);
        let llvm = self.llvm.shuffle_mask(bytes);
        self.immediates.set(cranelift, llvm);
        cranelift
    }
}
