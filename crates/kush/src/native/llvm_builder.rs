//! The typed LLVM builder (FND-LLVM-BUILDER, docs/mir-design.md section 10).
//!
//! An [`Emit`] that writes LLVM IR text as the lowering calls it, instead of
//! building Cranelift IR for the translator (`llvm.rs`) to read back. Every
//! value gets its LLVM type when it is made. Block parameters become `phi`
//! nodes. Variables live in `alloca`s that LLVM's `mem2reg` turns back into
//! SSA, and within one block a variable's value is reused directly. Values
//! with a known pointer origin (stack slots, symbols, exclusive parameters,
//! pointers the runtime returns) keep a pointer form, and addresses are
//! rebuilt as `getelementptr` from it, as the translator does.
//!
//! The handles are Cranelift's entity types, numbered here.
use super::emit::Emit;
use super::llvm::{
    CSignature, MemoryClass, RuntimeInterface, Ty, WORD_THUNK, drop_unused_flags, extension,
    intrinsic_suffix, lanes, return_type, splat_constant, ty_name,
};
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::{
    self, AtomicRmwOp, MemFlagsData, TrapCode,
    condcodes::{FloatCC, IntCC},
    immediates::{Imm64, Offset32, Uimm8},
    types,
};
use cranelift_frontend::Variable;
use cranelift_module::{DataId, FuncId, Linkage, Module};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::rc::Rc;

/// What every function body of one program shares.
#[derive(Clone)]
pub(super) struct Shared {
    pub runtime: Rc<RuntimeInterface>,
    /// Per function name, the parameters that are exclusive pointers.
    pub exclusive: Rc<BTreeMap<String, Vec<usize>>>,
}

/// How a value was made, for the pointer heuristics of [`LlvmBuilder::pointer_at`].
#[derive(Clone, Copy)]
enum Def {
    Iadd(ir::Value, ir::Value),
    Load,
    /// Clearly an offset: a product, shift, mask, quotient or extension.
    Offset,
}

struct Callee {
    name: String,
    signature: ir::Signature,
}

#[derive(Default)]
struct BlockData {
    params: Vec<ir::Value>,
    body: String,
    /// The label code is appended under (a block splits at each trap check).
    label: String,
    filled: bool,
}

struct Edge {
    from_block: ir::Block,
    from: String,
    target: ir::Block,
    values: Vec<String>,
}

/// A function body under construction as LLVM IR.
pub(super) struct LlvmBuilder {
    shared: Shared,
    name: String,
    linkage: Linkage,
    signature: ir::Signature,
    /// Functions whose bodies or addresses this body refers to.
    pub referenced: BTreeSet<FuncId>,
    pub intrinsics: BTreeSet<String>,
    pub address_taken: BTreeSet<String>,
    callees: Vec<Callee>,
    signatures: Vec<ir::Signature>,
    globals: Vec<String>,
    masks: Vec<Vec<u8>>,
    types: Vec<ir::Type>,
    constants: HashMap<ir::Value, i64>,
    flags: HashMap<ir::Value, String>,
    pointers: HashMap<ir::Value, String>,
    defs: HashMap<ir::Value, Def>,
    results: Vec<Vec<ir::Value>>,
    blocks: Vec<BlockData>,
    entry: Option<ir::Block>,
    current: Option<ir::Block>,
    edges: Vec<Edge>,
    variables: Vec<ir::Type>,
    /// Variable values known in the current block.
    local: HashMap<usize, ir::Value>,
    slots: Vec<ir::StackSlotData>,
    class: Option<u32>,
    temporaries: usize,
    splits: usize,
    failure: Option<String>,
}

impl LlvmBuilder {
    pub(super) fn new(
        shared: Shared,
        name: String,
        linkage: Linkage,
        signature: ir::Signature,
    ) -> Self {
        LlvmBuilder {
            shared,
            name,
            linkage,
            signature,
            referenced: BTreeSet::new(),
            intrinsics: BTreeSet::new(),
            address_taken: BTreeSet::new(),
            callees: Vec::new(),
            signatures: Vec::new(),
            globals: Vec::new(),
            masks: Vec::new(),
            types: Vec::new(),
            constants: HashMap::new(),
            flags: HashMap::new(),
            pointers: HashMap::new(),
            defs: HashMap::new(),
            results: Vec::new(),
            blocks: Vec::new(),
            entry: None,
            current: None,
            edges: Vec::new(),
            variables: Vec::new(),
            local: HashMap::new(),
            slots: Vec::new(),
            class: None,
            temporaries: 0,
            splits: 0,
            failure: None,
        }
    }

    fn fail(&mut self, message: impl Into<String>) {
        self.failure.get_or_insert_with(|| message.into());
    }
    fn value(&mut self, ty: ir::Type) -> ir::Value {
        self.types.push(ty);
        ir::Value::new(self.types.len() - 1)
    }
    fn inst(&mut self, results: Vec<ir::Value>) -> ir::Inst {
        self.results.push(results);
        ir::Inst::new(self.results.len() - 1)
    }
    fn ty(&self, value: ir::Value) -> ir::Type {
        self.types[value.index()]
    }
    fn tyn(&mut self, ty: ir::Type) -> &'static str {
        match ty_name(ty) {
            Ok(name) => name,
            Err(message) => {
                self.fail(message);
                "i64"
            }
        }
    }
    fn vtyn(&mut self, value: ir::Value) -> &'static str {
        let ty = self.ty(value);
        self.tyn(ty)
    }
    /// The operand text of a value: a literal or its SSA name.
    fn op(&self, value: ir::Value) -> String {
        match self.constants.get(&value) {
            Some(literal) => literal.to_string(),
            None => name(value),
        }
    }
    fn temp(&mut self) -> String {
        self.temporaries += 1;
        format!("%t{}", self.temporaries)
    }
    fn block(&mut self) -> &mut BlockData {
        let block = self.current.expect("an instruction outside any block");
        &mut self.blocks[block.index()]
    }
    fn line(&mut self, text: impl AsRef<str>) {
        let block = self.block();
        block.body.push_str("  ");
        block.body.push_str(text.as_ref());
        block.body.push('\n');
    }
    fn label(&mut self) -> String {
        self.block().label.clone()
    }
    fn start_label(&mut self, label: String) {
        let block = self.block();
        let _ = writeln!(block.body, "{label}:");
        block.label = label;
    }
    fn intrinsic(&mut self, declaration: &str) {
        if !self.intrinsics.contains(declaration) {
            self.intrinsics.insert(declaration.to_owned());
        }
    }
    fn terminate(&mut self) {
        self.block().filled = true;
        self.local.clear();
    }
    fn trap_now(&mut self) {
        self.intrinsic("declare void @llvm.trap()");
        self.line("call void @llvm.trap()");
        self.line("unreachable");
    }
    /// Trap when `condition` (an `i1`) holds, continuing in a fresh label.
    fn trap_if(&mut self, condition: &str) {
        self.splits += 1;
        let label = self.label();
        let trap = format!("{label}.t{}", self.splits);
        let next = format!("{label}.c{}", self.splits);
        self.line(format!(
            "br i1 {condition}, label %{trap}, label %{next}, !prof !0"
        ));
        self.start_label(trap);
        self.trap_now();
        self.start_label(next);
    }
    /// The `i1` truth of an integer value.
    fn truth(&mut self, value: ir::Value) -> String {
        if let Some(flag) = self.flags.get(&value) {
            return flag.clone();
        }
        if let Some(&constant) = self.constants.get(&value) {
            return (constant != 0).to_string();
        }
        let temp = self.temp();
        let ty = self.vtyn(value);
        let operand = self.op(value);
        self.line(format!("{temp} = icmp ne {ty} {operand}, 0"));
        temp
    }
    /// A new integer value of type `ty` from an `i1`, remembering the flag.
    fn flag_value(&mut self, ty: ir::Type, flag: String) -> ir::Value {
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        self.line(format!("{} = zext i1 {flag} to {tyn}", name(result)));
        self.flags.insert(result, flag);
        result
    }
    /// The `i1` a value is the zero extension of, if it is known to be one.
    fn flag_of(&self, value: ir::Value) -> Option<String> {
        if let Some(flag) = self.flags.get(&value) {
            return Some(flag.clone());
        }
        match self.constants.get(&value) {
            Some(0) => Some("false".into()),
            Some(1) => Some("true".into()),
            _ => None,
        }
    }
    fn loaded(&self, value: ir::Value) -> bool {
        matches!(self.defs.get(&value), Some(Def::Load))
    }
    fn offset_like(&self, value: ir::Value) -> bool {
        self.constants.contains_key(&value) || matches!(self.defs.get(&value), Some(Def::Offset))
    }
    /// The pointer form of an address-valued word, materialized here.
    fn pointer(&mut self, value: ir::Value) -> String {
        self.pointer_at(value, 4)
    }
    fn pointer_at(&mut self, value: ir::Value, depth: usize) -> String {
        if let Some(pointer) = self.pointers.get(&value) {
            return pointer.clone();
        }
        if self.ty(value) != types::I64 {
            self.fail("address is not a 64-bit word");
        }
        if depth > 0
            && let Some(Def::Iadd(left, right)) = self.defs.get(&value).copied()
        {
            let choice = if self.pointers.contains_key(&left) {
                Some((left, right))
            } else if self.pointers.contains_key(&right) {
                Some((right, left))
            } else if self.offset_like(right) && !self.offset_like(left) {
                Some((left, right))
            } else if self.offset_like(left) && !self.offset_like(right) {
                Some((right, left))
            } else if self.loaded(left) && !self.loaded(right) {
                // A loaded word plus anything else is a handle plus an index
                // far more often than the reverse (see the translator).
                Some((left, right))
            } else if self.loaded(right) && !self.loaded(left) {
                Some((right, left))
            } else {
                None
            };
            if let Some((base, offset)) = choice {
                let base = self.pointer_at(base, depth - 1);
                let offset = self.op(offset);
                let temp = self.temp();
                self.line(format!(
                    "{temp} = getelementptr i8, ptr {base}, i64 {offset}"
                ));
                return temp;
            }
        }
        let temp = self.temp();
        let operand = self.op(value);
        self.line(format!("{temp} = inttoptr i64 {operand} to ptr"));
        temp
    }
    fn address(&mut self, base: ir::Value, offset: i64) -> String {
        let pointer = self.pointer(base);
        if offset == 0 {
            return pointer;
        }
        let temp = self.temp();
        self.line(format!(
            "{temp} = getelementptr i8, ptr {pointer}, i64 {offset}"
        ));
        temp
    }
    /// A new word with both forms from a freshly produced pointer.
    fn pointer_value(&mut self, pointer: String) -> ir::Value {
        let result = self.value(types::I64);
        self.line(format!("{} = ptrtoint ptr {pointer} to i64", name(result)));
        self.pointers.insert(result, pointer);
        result
    }
    /// The symbol to use for a function's address: its word-signature thunk
    /// when the function itself takes pointer parameters.
    fn address_of(&mut self, name: &str) -> String {
        if self.shared.exclusive.contains_key(name) {
            self.address_taken.insert(name.to_owned());
            format!("@{name}{WORD_THUNK}")
        } else {
            format!("@{name}")
        }
    }
    fn memory_class(&self) -> &'static str {
        match self.class {
            Some(class) if class == MemoryClass::BufferHeader as u32 => ", !tbaa !4",
            Some(class) if class == MemoryClass::BufferElements as u32 => ", !tbaa !5",
            _ => "",
        }
    }
    fn binary(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let (left, right) = (self.op(x), self.op(y));
        self.line(format!(
            "{} = {operation} {tyn} {left}, {right}",
            name(result)
        ));
        result
    }
    fn offset_binary(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let result = self.binary(operation, x, y);
        self.defs.insert(result, Def::Offset);
        result
    }
    /// Bitwise logic, kept in `i1` when both sides are flags.
    fn logical(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let (Some(left), Some(right)) = (self.flag_of(x), self.flag_of(y)) else {
            return self.binary(operation, x, y);
        };
        let flag = match (operation, left.as_str(), right.as_str()) {
            ("or", "false", other) | ("or", other, "false") => other.to_owned(),
            ("and", "true", other) | ("and", other, "true") => other.to_owned(),
            ("xor", "false", other) | ("xor", other, "false") => other.to_owned(),
            _ => {
                let temp = self.temp();
                self.line(format!("{temp} = {operation} i1 {left}, {right}"));
                temp
            }
        };
        let ty = self.ty(x);
        self.flag_value(ty, flag)
    }
    fn overflow(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        let ty = self.ty(x);
        let tyn = self.tyn(ty);
        self.intrinsic(&format!(
            "declare {{ {tyn}, i1 }} @llvm.{operation}.with.overflow.{tyn}({tyn}, {tyn})"
        ));
        let pair = self.temp();
        let (left, right) = (self.op(x), self.op(y));
        self.line(format!(
            "{pair} = call {{ {tyn}, i1 }} @llvm.{operation}.with.overflow.{tyn}({tyn} {left}, {tyn} {right})"
        ));
        let result = self.value(ty);
        self.line(format!(
            "{} = extractvalue {{ {tyn}, i1 }} {pair}, 0",
            name(result)
        ));
        let flag = self.temp();
        self.line(format!("{flag} = extractvalue {{ {tyn}, i1 }} {pair}, 1"));
        (result, self.flag_value(types::I8, flag))
    }
    fn unary_intrinsic(&mut self, base: &str, x: ir::Value, extra: &str) -> ir::Value {
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let suffix = intrinsic_suffix(tyn);
        let extra_types = if extra.is_empty() { "" } else { ", i1" };
        self.intrinsic(&format!(
            "declare {tyn} @llvm.{base}.{suffix}({tyn}{extra_types})"
        ));
        let operand = self.op(x);
        self.line(format!(
            "{} = call {tyn} @llvm.{base}.{suffix}({tyn} {operand}{extra})",
            name(result)
        ));
        result
    }
    fn binary_intrinsic(&mut self, base: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let suffix = intrinsic_suffix(tyn);
        self.intrinsic(&format!(
            "declare {tyn} @llvm.{base}.{suffix}({tyn}, {tyn})"
        ));
        let (left, right) = (self.op(x), self.op(y));
        self.line(format!(
            "{} = call {tyn} @llvm.{base}.{suffix}({tyn} {left}, {tyn} {right})",
            name(result)
        ));
        result
    }
    fn convert(&mut self, operation: &str, ty: ir::Type, x: ir::Value) -> ir::Value {
        let result = self.value(ty);
        let (from, to) = (self.vtyn(x), self.tyn(ty));
        let operand = self.op(x);
        self.line(format!(
            "{} = {operation} {from} {operand} to {to}",
            name(result)
        ));
        result
    }
    /// A shift amount reduced modulo the width and converted to the shifted
    /// type, which is Cranelift's defined behaviour for every amount.
    fn shift_amount(&mut self, x: ir::Value, amount: ir::Value) -> String {
        let (Some(to), Some(from)) = (Ty::of(self.ty(x)), Ty::of(self.ty(amount))) else {
            self.fail("shift type");
            return "0".into();
        };
        let mut operand = self.op(amount);
        if from.bits() != to.bits() {
            let temp = self.temp();
            let operation = if from.bits() > to.bits() {
                "trunc"
            } else {
                "zext"
            };
            self.line(format!(
                "{temp} = {operation} {} {operand} to {}",
                from.name(),
                to.name()
            ));
            operand = temp;
        }
        let masked = self.temp();
        self.line(format!(
            "{masked} = and {} {operand}, {}",
            to.name(),
            to.bits() - 1
        ));
        masked
    }
    fn shift(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let tyn = self.tyn(ty);
        let amount = if let Some((count, lane)) = lanes(ty) {
            // A vector shifted by a scalar: the amount is reduced modulo the
            // lane width, then every lane shifts.
            let bits = ty.lane_type().bits();
            let from = self.vtyn(y);
            let mut amount = self.op(y);
            if from != lane {
                let temp = self.temp();
                self.line(format!("{temp} = trunc {from} {amount} to {lane}"));
                amount = temp;
            }
            let masked = self.temp();
            self.line(format!("{masked} = and {lane} {amount}, {}", bits - 1));
            let single = self.temp();
            self.line(format!(
                "{single} = insertelement {tyn} poison, {lane} {masked}, i32 0"
            ));
            let splat = self.temp();
            self.line(format!(
                "{splat} = shufflevector {tyn} {single}, {tyn} poison, <{count} x i32> zeroinitializer"
            ));
            splat
        } else {
            self.shift_amount(x, y)
        };
        let result = self.value(ty);
        let left = self.op(x);
        self.line(format!(
            "{} = {operation} {tyn} {left}, {amount}",
            name(result)
        ));
        self.defs.insert(result, Def::Offset);
        result
    }
    fn division(&mut self, operation: &str, x: ir::Value, y: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let tyn = self.tyn(ty);
        let bits = ty.bits();
        let (left, right) = (self.op(x), self.op(y));
        // Cranelift traps where LLVM has undefined behaviour.
        let zero = self.temp();
        self.line(format!("{zero} = icmp eq {tyn} {right}, 0"));
        self.trap_if(&zero);
        let result = self.value(ty);
        let named = name(result);
        let minimum = i128::from(-1i64) << (bits - 1);
        match operation {
            "sdiv" => {
                let (a, b, both) = (self.temp(), self.temp(), self.temp());
                self.line(format!("{a} = icmp eq {tyn} {left}, {minimum}"));
                self.line(format!("{b} = icmp eq {tyn} {right}, -1"));
                self.line(format!("{both} = and i1 {a}, {b}"));
                self.trap_if(&both);
                self.line(format!("{named} = sdiv {tyn} {left}, {right}"));
            }
            "srem" => {
                // `MIN % -1` is 0 in Cranelift; any `x % 1` is also 0.
                let (b, divisor) = (self.temp(), self.temp());
                self.line(format!("{b} = icmp eq {tyn} {right}, -1"));
                self.line(format!("{divisor} = select i1 {b}, {tyn} 1, {tyn} {right}"));
                self.line(format!("{named} = srem {tyn} {left}, {divisor}"));
            }
            _ => self.line(format!("{named} = {operation} {tyn} {left}, {right}")),
        }
        self.defs.insert(result, Def::Offset);
        result
    }
    fn load_as(
        &mut self,
        ty: ir::Type,
        memory: Option<(&str, &str)>,
        pointer: ir::Value,
        offset: Offset32,
    ) -> ir::Value {
        let address = self.address(pointer, i64::from(offset));
        let class = self.memory_class();
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        match memory {
            None => self.line(format!(
                "{} = load {tyn}, ptr {address}, align 1{class}",
                name(result)
            )),
            Some((memory, extend)) => {
                let temp = self.temp();
                self.line(format!(
                    "{temp} = load {memory}, ptr {address}, align 1{class}"
                ));
                self.line(format!(
                    "{} = {extend} {memory} {temp} to {tyn}",
                    name(result)
                ));
            }
        }
        self.defs.insert(result, Def::Load);
        result
    }
    fn store_as(
        &mut self,
        memory: Option<&str>,
        value: ir::Value,
        pointer: ir::Value,
        offset: Offset32,
    ) -> ir::Inst {
        let class = self.memory_class();
        let address = self.address(pointer, i64::from(offset));
        let ty = self.vtyn(value);
        let operand = self.op(value);
        match memory {
            Some(memory) if memory != ty => {
                let temp = self.temp();
                self.line(format!("{temp} = trunc {ty} {operand} to {memory}"));
                self.line(format!(
                    "store {memory} {temp}, ptr {address}, align 1{class}"
                ));
            }
            _ => self.line(format!(
                "store {ty} {operand}, ptr {address}, align 1{class}"
            )),
        }
        self.inst(Vec::new())
    }
    fn edge(&self, args: &[ir::Value]) -> Vec<String> {
        args.iter().map(|value| self.op(*value)).collect()
    }
    fn push_edge(&mut self, target: ir::Block, values: Vec<String>) {
        let from_block = self.current.expect("a branch outside any block");
        let from = self.label();
        self.edges.push(Edge {
            from_block,
            from,
            target,
            values,
        });
    }
    /// A call to `callee` with the Cranelift signature `signature`, using the
    /// runtime's exact C signature when every word converts to it.
    fn call_with(
        &mut self,
        callee: &str,
        signature: &ir::Signature,
        args: &[ir::Value],
        runtime: Option<&CSignature>,
    ) -> ir::Inst {
        let returns: Vec<ir::Type> = signature.returns.iter().map(|p| p.value_type).collect();
        if let Some(c) = runtime
            && c.params.len() == args.len()
            && returns.len() <= 1
            && args.iter().zip(&c.params).all(|(value, to)| {
                let from = Ty::of(self.ty(*value));
                from == Some(*to) || (from == Some(Ty::I64) && *to == Ty::Ptr)
            })
            && match returns.first().map(|ty| Ty::of(*ty)) {
                None => true,
                Some(Some(Ty::I64)) => matches!(c.ret, Ty::I64 | Ty::Ptr),
                Some(other) => other == Some(c.ret),
            }
        {
            let mut rendered = Vec::new();
            for (value, to) in args.iter().zip(&c.params) {
                let operand = if *to == Ty::Ptr && self.ty(*value) == types::I64 {
                    self.pointer(*value)
                } else {
                    self.op(*value)
                };
                rendered.push(format!("{} {operand}", to.name()));
            }
            let arguments = rendered.join(", ");
            let results = match returns.first() {
                None => {
                    self.line(format!("call {} {callee}({arguments})", c.ret.name()));
                    Vec::new()
                }
                Some(_) if c.ret == Ty::Ptr => {
                    let temp = self.temp();
                    self.line(format!("{temp} = call ptr {callee}({arguments})"));
                    vec![self.pointer_value(temp)]
                }
                Some(ty) => {
                    let result = self.value(*ty);
                    self.line(format!(
                        "{} = call {} {callee}({arguments})",
                        name(result),
                        c.ret.name()
                    ));
                    vec![result]
                }
            };
            return self.inst(results);
        }
        let exclusive: Vec<usize> = callee
            .strip_prefix('@')
            .and_then(|name| self.shared.exclusive.get(name))
            .cloned()
            .unwrap_or_default();
        let mut rendered = Vec::new();
        for (index, (value, param)) in args.iter().zip(&signature.params).enumerate() {
            if exclusive.contains(&index) {
                let pointer = self.pointer(*value);
                rendered.push(format!("ptr {pointer}"));
                continue;
            }
            let ty = self.vtyn(*value);
            rendered.push(format!("{ty}{} {}", extension(param), self.op(*value)));
        }
        let arguments = rendered.join(", ");
        let ret = match return_type(signature) {
            Ok(ret) => ret,
            Err(message) => {
                self.fail(message);
                "void".into()
            }
        };
        let results = match returns.as_slice() {
            [] => {
                self.line(format!("call {ret} {callee}({arguments})"));
                Vec::new()
            }
            [ty] => {
                let result = self.value(*ty);
                self.line(format!(
                    "{} = call {ret} {callee}({arguments})",
                    name(result)
                ));
                vec![result]
            }
            many => {
                let temp = self.temp();
                self.line(format!("{temp} = call {ret} {callee}({arguments})"));
                let mut results = Vec::new();
                for (index, ty) in many.iter().enumerate() {
                    let result = self.value(*ty);
                    self.line(format!(
                        "{} = extractvalue {ret} {temp}, {index}",
                        name(result)
                    ));
                    results.push(result);
                }
                results
            }
        };
        self.inst(results)
    }

    /// The finished function text, or why it could not be built.
    pub(super) fn finish(self) -> std::result::Result<String, String> {
        if let Some(failure) = self.failure {
            return Err(failure);
        }
        let entry = self.entry.ok_or("function has no entry")?;
        if self.edges.iter().any(|edge| edge.target == entry) {
            return Err("the entry block is a branch target".into());
        }
        // Only blocks reachable from the entry are emitted, and only their
        // edges feed phis.
        let mut successors: BTreeMap<ir::Block, Vec<ir::Block>> = BTreeMap::new();
        for edge in &self.edges {
            successors
                .entry(edge.from_block)
                .or_default()
                .push(edge.target);
        }
        let mut reachable = BTreeSet::new();
        let mut work = vec![entry];
        while let Some(block) = work.pop() {
            if reachable.insert(block) {
                work.extend(successors.get(&block).into_iter().flatten().copied());
            }
        }
        let exclusive: &[usize] = self
            .shared
            .exclusive
            .get(&self.name)
            .map_or(&[], Vec::as_slice);
        let ret = return_type(&self.signature)?;
        let entry_params = &self.blocks[entry.index()].params;
        let mut params = Vec::new();
        let mut prologue = String::new();
        for (index, (value, param)) in entry_params.iter().zip(&self.signature.params).enumerate() {
            if exclusive.contains(&index) {
                // Exclusive parameters arrive as pointers. Everything derived
                // from one stays based on it, which is what `noalias` needs.
                params.push(format!("ptr noalias {}.p", name(*value)));
                let _ = writeln!(
                    prologue,
                    "  {} = ptrtoint ptr {}.p to i64",
                    name(*value),
                    name(*value)
                );
            } else {
                params.push(format!(
                    "{}{} {}",
                    ty_name(param.value_type)?,
                    extension(param),
                    name(*value)
                ));
            }
        }
        for (slot, data) in self.slots.iter().enumerate() {
            let align = (1u64 << data.align_shift).max(8);
            let _ = writeln!(
                prologue,
                "  %ss{slot} = alloca [{} x i8], align {align}",
                data.size.max(1)
            );
        }
        for (variable, ty) in self.variables.iter().enumerate() {
            let tyn = ty_name(*ty)?;
            let _ = writeln!(prologue, "  %x{variable} = alloca {tyn}");
            let _ = writeln!(prologue, "  store {tyn} zeroinitializer, ptr %x{variable}");
        }
        let linkage = match self.linkage {
            Linkage::Local | Linkage::Hidden => "internal ",
            _ => "",
        };
        let mut out = String::new();
        let _ = writeln!(
            out,
            "define {linkage}{ret} @{}({}) #0 {{",
            self.name,
            params.join(", ")
        );
        let mut order: Vec<ir::Block> = vec![entry];
        order.extend(
            (0..self.blocks.len())
                .map(ir::Block::new)
                .filter(|block| *block != entry && reachable.contains(block)),
        );
        for block in order {
            let data = &self.blocks[block.index()];
            let _ = writeln!(out, "b{}:", block.index());
            if block == entry {
                out.push_str(&prologue);
            } else {
                for (index, param) in data.params.iter().enumerate() {
                    let incoming = self
                        .edges
                        .iter()
                        .filter(|edge| edge.target == block && reachable.contains(&edge.from_block))
                        .map(|edge| format!("[ {}, %{} ]", edge.values[index], edge.from))
                        .collect::<Vec<_>>();
                    let _ = writeln!(
                        out,
                        "  {} = phi {} {}",
                        name(*param),
                        ty_name(self.types[param.index()])?,
                        incoming.join(", ")
                    );
                }
            }
            out.push_str(&data.body);
            if !data.filled {
                out.push_str("  unreachable\n");
            }
        }
        out.push_str("}\n");
        Ok(drop_unused_flags(out))
    }
}

fn name(value: ir::Value) -> String {
    format!("%v{}", value.index())
}

/// The literal of an integer constant of type `ty`: sign-extended from its
/// width, as LLVM prints it.
fn literal(ty: ir::Type, raw: i64) -> i64 {
    let bits = ty.bits();
    if bits >= 64 {
        raw
    } else {
        (raw << (64 - bits)) >> (64 - bits)
    }
}

impl Emit for LlvmBuilder {
    fn create_block(&mut self) -> ir::Block {
        self.blocks.push(BlockData::default());
        let block = ir::Block::new(self.blocks.len() - 1);
        self.blocks[block.index()].label = format!("b{}", block.index());
        block
    }
    fn switch_to_block(&mut self, block: ir::Block) {
        if self.entry.is_none() {
            self.entry = Some(block);
        }
        self.current = Some(block);
        self.local.clear();
    }
    fn append_block_param(&mut self, block: ir::Block, ty: ir::Type) -> ir::Value {
        let value = self.value(ty);
        self.blocks[block.index()].params.push(value);
        value
    }
    fn append_block_params_for_function_params(&mut self, block: ir::Block) {
        let types: Vec<ir::Type> = self.signature.params.iter().map(|p| p.value_type).collect();
        let exclusive = self.shared.exclusive.get(&self.name).cloned();
        for (index, ty) in types.into_iter().enumerate() {
            let value = self.append_block_param(block, ty);
            if exclusive.as_ref().is_some_and(|e| e.contains(&index)) {
                self.pointers.insert(value, format!("{}.p", name(value)));
            }
        }
        self.entry = Some(block);
    }
    fn block_params(&self, block: ir::Block) -> &[ir::Value] {
        &self.blocks[block.index()].params
    }
    fn seal_all_blocks(&mut self) {}
    fn declare_var(&mut self, ty: ir::Type) -> Variable {
        self.variables.push(ty);
        Variable::new(self.variables.len() - 1)
    }
    fn def_var(&mut self, var: Variable, value: ir::Value) {
        let ty = self.variables[var.index()];
        let tyn = self.tyn(ty);
        let operand = self.op(value);
        self.line(format!("store {tyn} {operand}, ptr %x{}", var.index()));
        self.local.insert(var.index(), value);
    }
    fn use_var(&mut self, var: Variable) -> ir::Value {
        if let Some(&value) = self.local.get(&var.index()) {
            return value;
        }
        let ty = self.variables[var.index()];
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        self.line(format!(
            "{} = load {tyn}, ptr %x{}",
            name(result),
            var.index()
        ));
        self.local.insert(var.index(), result);
        result
    }
    fn create_sized_stack_slot(&mut self, data: ir::StackSlotData) -> ir::StackSlot {
        self.slots.push(data);
        ir::StackSlot::new(self.slots.len() - 1)
    }
    fn import_signature(&mut self, signature: ir::Signature) -> ir::SigRef {
        self.signatures.push(signature);
        ir::SigRef::new(self.signatures.len() - 1)
    }
    fn declare_func(&mut self, module: &mut impl Module, id: FuncId) -> ir::FuncRef {
        let declaration = module.declarations().get_function_decl(id);
        self.callees.push(Callee {
            name: declaration.linkage_name(id).into_owned(),
            signature: declaration.signature.clone(),
        });
        self.referenced.insert(id);
        ir::FuncRef::new(self.callees.len() - 1)
    }
    fn declare_data(&mut self, module: &mut impl Module, id: DataId) -> ir::GlobalValue {
        let declaration = module.declarations().get_data_decl(id);
        self.globals.push(declaration.linkage_name(id).into_owned());
        ir::GlobalValue::new(self.globals.len() - 1)
    }
    fn inst_results(&self, inst: ir::Inst) -> &[ir::Value] {
        &self.results[inst.index()]
    }
    fn constant_of(&self, value: ir::Value) -> Option<i64> {
        self.constants.get(&value).copied()
    }
    fn value_type(&self, value: ir::Value) -> ir::Type {
        self.ty(value)
    }
    fn set_memory_class(&mut self, class: Option<u32>) -> Option<u32> {
        std::mem::replace(&mut self.class, class)
    }

    fn jump(&mut self, block: ir::Block, args: &[ir::Value]) -> ir::Inst {
        let values = self.edge(args);
        self.line(format!("br label %b{}", block.index()));
        self.push_edge(block, values);
        self.terminate();
        self.inst(Vec::new())
    }
    fn brif(
        &mut self,
        condition: ir::Value,
        then: ir::Block,
        then_args: &[ir::Value],
        otherwise: ir::Block,
        otherwise_args: &[ir::Value],
    ) -> ir::Inst {
        let flag = self.truth(condition);
        let then_values = self.edge(then_args);
        let else_values = self.edge(otherwise_args);
        if then == otherwise {
            // One predecessor edge: merge the two argument lists.
            let params = self.blocks[then.index()].params.clone();
            let mut values = Vec::new();
            for ((yes, no), param) in then_values.iter().zip(&else_values).zip(params) {
                if yes == no {
                    values.push(yes.clone());
                } else {
                    let ty = self.vtyn(param);
                    let temp = self.temp();
                    self.line(format!("{temp} = select i1 {flag}, {ty} {yes}, {ty} {no}"));
                    values.push(temp);
                }
            }
            self.line(format!("br label %b{}", then.index()));
            self.push_edge(then, values);
        } else {
            self.line(format!(
                "br i1 {flag}, label %b{}, label %b{}",
                then.index(),
                otherwise.index()
            ));
            self.push_edge(then, then_values);
            self.push_edge(otherwise, else_values);
        }
        self.terminate();
        self.inst(Vec::new())
    }
    fn return_(&mut self, values: &[ir::Value]) -> ir::Inst {
        match values {
            [] => self.line("ret void"),
            [value] => {
                let (ty, operand) = (self.vtyn(*value), self.op(*value));
                self.line(format!("ret {ty} {operand}"));
            }
            many => {
                let ret = match return_type(&self.signature) {
                    Ok(ret) => ret,
                    Err(message) => {
                        self.fail(message);
                        "void".into()
                    }
                };
                let mut aggregate = "poison".to_owned();
                for (index, value) in many.iter().enumerate() {
                    let (ty, operand) = (self.vtyn(*value), self.op(*value));
                    let temp = self.temp();
                    self.line(format!(
                        "{temp} = insertvalue {ret} {aggregate}, {ty} {operand}, {index}"
                    ));
                    aggregate = temp;
                }
                self.line(format!("ret {ret} {aggregate}"));
            }
        }
        self.terminate();
        self.inst(Vec::new())
    }
    fn trap(&mut self, code: impl Into<TrapCode>) -> ir::Inst {
        let _ = code.into();
        self.trap_now();
        self.terminate();
        self.inst(Vec::new())
    }
    fn call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        let Callee {
            name: symbol,
            signature,
        } = &self.callees[callee.index()];
        let (symbol, signature) = (symbol.clone(), signature.clone());
        let shared = self.shared.clone();
        let runtime = shared.runtime.signatures.get(&symbol);
        self.call_with(&format!("@{symbol}"), &signature, args, runtime)
    }
    fn call_indirect(
        &mut self,
        signature: ir::SigRef,
        callee: ir::Value,
        args: &[ir::Value],
    ) -> ir::Inst {
        let signature = self.signatures[signature.index()].clone();
        let callee = self.pointer_at(callee, 0);
        self.call_with(&callee, &signature, args, None)
    }

    fn iconst(&mut self, ty: ir::Type, value: impl Into<Imm64>) -> ir::Value {
        let result = self.value(ty);
        self.constants
            .insert(result, literal(ty, value.into().bits()));
        result
    }
    fn stack_addr(
        &mut self,
        _ty: ir::Type,
        slot: ir::StackSlot,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        let offset = i64::from(offset.into());
        let pointer = if offset == 0 {
            format!("%ss{}", slot.index())
        } else {
            let temp = self.temp();
            self.line(format!(
                "{temp} = getelementptr inbounds i8, ptr %ss{}, i64 {offset}",
                slot.index()
            ));
            temp
        };
        self.pointer_value(pointer)
    }
    fn func_addr(&mut self, _ty: ir::Type, callee: ir::FuncRef) -> ir::Value {
        let name = self.callees[callee.index()].name.clone();
        let symbol = self.address_of(&name);
        self.pointer_value(symbol)
    }
    fn symbol_value(&mut self, _ty: ir::Type, global: ir::GlobalValue) -> ir::Value {
        let symbol = format!("@{}", self.globals[global.index()]);
        self.pointer_value(symbol)
    }

    fn load(
        &mut self,
        ty: ir::Type,
        _flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        self.load_as(ty, None, pointer, offset.into())
    }
    fn uload8(
        &mut self,
        ty: ir::Type,
        _flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Value {
        self.load_as(ty, Some(("i8", "zext")), pointer, offset.into())
    }
    fn store(
        &mut self,
        _flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        self.store_as(None, value, pointer, offset.into())
    }
    fn istore8(
        &mut self,
        _flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
        offset: impl Into<Offset32>,
    ) -> ir::Inst {
        self.store_as(Some("i8"), value, pointer, offset.into())
    }
    // Cranelift's atomics are sequentially consistent and need the natural
    // alignment LLVM requires of an atomic access.
    fn atomic_load(
        &mut self,
        ty: ir::Type,
        _flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
    ) -> ir::Value {
        let address = self.address(pointer, 0);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        self.line(format!(
            "{} = load atomic {tyn}, ptr {address} seq_cst, align {}",
            name(result),
            ty.bytes()
        ));
        result
    }
    fn atomic_store(
        &mut self,
        _flags: impl Into<MemFlagsData>,
        value: ir::Value,
        pointer: ir::Value,
    ) -> ir::Inst {
        let address = self.address(pointer, 0);
        let ty = self.ty(value);
        let (tyn, operand) = (self.tyn(ty), self.op(value));
        self.line(format!(
            "store atomic {tyn} {operand}, ptr {address} seq_cst, align {}",
            ty.bytes()
        ));
        self.inst(Vec::new())
    }
    fn atomic_rmw(
        &mut self,
        ty: ir::Type,
        _flags: impl Into<MemFlagsData>,
        op: impl Into<AtomicRmwOp>,
        pointer: ir::Value,
        value: ir::Value,
    ) -> ir::Value {
        let operation = match op.into() {
            AtomicRmwOp::Add => "add",
            AtomicRmwOp::Sub => "sub",
            AtomicRmwOp::And => "and",
            AtomicRmwOp::Nand => "nand",
            AtomicRmwOp::Or => "or",
            AtomicRmwOp::Xor => "xor",
            AtomicRmwOp::Xchg => "xchg",
            AtomicRmwOp::Umin => "umin",
            AtomicRmwOp::Umax => "umax",
            AtomicRmwOp::Smin => "min",
            AtomicRmwOp::Smax => "max",
        };
        let address = self.address(pointer, 0);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let operand = self.op(value);
        self.line(format!(
            "{} = atomicrmw {operation} ptr {address}, {tyn} {operand} seq_cst, align {}",
            name(result),
            ty.bytes()
        ));
        result
    }
    fn atomic_cas(
        &mut self,
        _flags: impl Into<MemFlagsData>,
        pointer: ir::Value,
        expected: ir::Value,
        replacement: ir::Value,
    ) -> ir::Value {
        let ty = self.ty(expected);
        let address = self.address(pointer, 0);
        let tyn = self.tyn(ty);
        let (old, new) = (self.op(expected), self.op(replacement));
        let pair = self.temp();
        self.line(format!(
            "{pair} = cmpxchg ptr {address}, {tyn} {old}, {tyn} {new} seq_cst seq_cst, align {}",
            ty.bytes()
        ));
        let result = self.value(ty);
        self.line(format!(
            "{} = extractvalue {{ {tyn}, i1 }} {pair}, 0",
            name(result)
        ));
        result
    }

    fn iadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let result = self.binary("add", x, y);
        self.defs.insert(result, Def::Iadd(x, y));
        result
    }
    fn isub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary("sub", x, y)
    }
    fn imul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.offset_binary("mul", x, y)
    }
    fn udiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.division("udiv", x, y)
    }
    fn sdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.division("sdiv", x, y)
    }
    fn urem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.division("urem", x, y)
    }
    fn srem(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.division("srem", x, y)
    }
    fn band(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let result = self.logical("and", x, y);
        if !self.flags.contains_key(&result) {
            self.defs.insert(result, Def::Offset);
        }
        result
    }
    fn bor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.logical("or", x, y)
    }
    fn bxor(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.logical("xor", x, y)
    }
    fn band_not(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        let not = self.bnot(y);
        self.band(x, not)
    }
    fn bnot(&mut self, x: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let operand = self.op(x);
        let ones = splat_constant(ty, "-1").unwrap_or_else(|| "-1".into());
        self.line(format!("{} = xor {tyn} {operand}, {ones}", name(result)));
        result
    }
    fn ineg(&mut self, x: ir::Value) -> ir::Value {
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let operand = self.op(x);
        self.line(format!("{} = sub {tyn} 0, {operand}", name(result)));
        self.defs.insert(result, Def::Offset);
        result
    }
    fn ishl(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.shift("shl", x, y)
    }
    fn ushr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.shift("lshr", x, y)
    }
    fn sshr(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.shift("ashr", x, y)
    }
    fn umax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary_intrinsic("umax", x, y)
    }
    fn umin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary_intrinsic("umin", x, y)
    }
    fn smax(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary_intrinsic("smax", x, y)
    }
    fn smin(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary_intrinsic("smin", x, y)
    }
    fn clz(&mut self, x: ir::Value) -> ir::Value {
        self.unary_intrinsic("ctlz", x, ", i1 false")
    }
    fn iadd_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.iadd(x, y)
    }
    fn imul_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.imul(x, y)
    }
    fn band_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.band(x, y)
    }
    fn bor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.bor(x, y)
    }
    fn bxor_imm_s(&mut self, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.bxor(x, y)
    }
    fn icmp(&mut self, cond: impl Into<IntCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        let predicate = match cond.into() {
            IntCC::Equal => "eq",
            IntCC::NotEqual => "ne",
            IntCC::SignedLessThan => "slt",
            IntCC::SignedGreaterThanOrEqual => "sge",
            IntCC::SignedGreaterThan => "sgt",
            IntCC::SignedLessThanOrEqual => "sle",
            IntCC::UnsignedLessThan => "ult",
            IntCC::UnsignedGreaterThanOrEqual => "uge",
            IntCC::UnsignedGreaterThan => "ugt",
            IntCC::UnsignedLessThanOrEqual => "ule",
        };
        let ty = self.ty(x);
        let tyn = self.tyn(ty);
        let (left, right) = (self.op(x), self.op(y));
        let flag = self.temp();
        self.line(format!("{flag} = icmp {predicate} {tyn} {left}, {right}"));
        if let Some((count, _)) = lanes(ty) {
            // A vector comparison is a lane mask: all ones or zero.
            let result = self.value(ty);
            self.line(format!(
                "{} = sext <{count} x i1> {flag} to {tyn}",
                name(result)
            ));
            result
        } else {
            self.flag_value(types::I8, flag)
        }
    }
    fn icmp_imm_s(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.icmp(cond, x, y)
    }
    fn icmp_imm_u(&mut self, cond: IntCC, x: ir::Value, y: impl Into<Imm64>) -> ir::Value {
        let y = self.iconst(self.ty(x), y);
        self.icmp(cond, x, y)
    }
    fn select(&mut self, c: ir::Value, x: ir::Value, y: ir::Value) -> ir::Value {
        let flag = self.truth(c);
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let (yes, no) = (self.op(x), self.op(y));
        self.line(format!(
            "{} = select i1 {flag}, {tyn} {yes}, {tyn} {no}",
            name(result)
        ));
        result
    }
    fn uextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let result = match self.flag_of(x) {
            // Still a zero-extended flag: keep the `i1` form.
            Some(flag) => self.flag_value(ty, flag),
            None => self.convert("zext", ty, x),
        };
        self.defs.insert(result, Def::Offset);
        result
    }
    fn sextend(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let result = self.convert("sext", ty, x);
        self.defs.insert(result, Def::Offset);
        result
    }
    fn ireduce(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.convert("trunc", ty, x)
    }
    fn sadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("sadd", x, y)
    }
    fn ssub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("ssub", x, y)
    }
    fn smul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("smul", x, y)
    }
    fn uadd_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("uadd", x, y)
    }
    fn usub_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("usub", x, y)
    }
    fn umul_overflow(&mut self, x: ir::Value, y: ir::Value) -> (ir::Value, ir::Value) {
        self.overflow("umul", x, y)
    }

    fn fadd(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary("fadd", x, y)
    }
    fn fsub(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary("fsub", x, y)
    }
    fn fmul(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary("fmul", x, y)
    }
    fn fdiv(&mut self, x: ir::Value, y: ir::Value) -> ir::Value {
        self.binary("fdiv", x, y)
    }
    fn sqrt(&mut self, x: ir::Value) -> ir::Value {
        self.unary_intrinsic("sqrt", x, "")
    }
    fn fcmp(&mut self, cond: impl Into<FloatCC>, x: ir::Value, y: ir::Value) -> ir::Value {
        let predicate = match cond.into() {
            FloatCC::Ordered => "ord",
            FloatCC::Unordered => "uno",
            FloatCC::Equal => "oeq",
            FloatCC::NotEqual => "une",
            FloatCC::OrderedNotEqual => "one",
            FloatCC::UnorderedOrEqual => "ueq",
            FloatCC::LessThan => "olt",
            FloatCC::LessThanOrEqual => "ole",
            FloatCC::GreaterThan => "ogt",
            FloatCC::GreaterThanOrEqual => "oge",
            FloatCC::UnorderedOrLessThan => "ult",
            FloatCC::UnorderedOrLessThanOrEqual => "ule",
            FloatCC::UnorderedOrGreaterThan => "ugt",
            FloatCC::UnorderedOrGreaterThanOrEqual => "uge",
        };
        let tyn = self.vtyn(x);
        let (left, right) = (self.op(x), self.op(y));
        let flag = self.temp();
        self.line(format!("{flag} = fcmp {predicate} {tyn} {left}, {right}"));
        self.flag_value(types::I8, flag)
    }
    fn fpromote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.convert("fpext", ty, x)
    }
    fn fdemote(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        self.convert("fptrunc", ty, x)
    }
    fn bitcast(
        &mut self,
        ty: ir::Type,
        _flags: impl Into<MemFlagsData>,
        x: ir::Value,
    ) -> ir::Value {
        self.convert("bitcast", ty, x)
    }
    fn extractlane(&mut self, x: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        let lane: u8 = lane.into();
        let ty = self.ty(x);
        let result = self.value(ty.lane_type());
        let tyn = self.tyn(ty);
        let operand = self.op(x);
        self.line(format!(
            "{} = extractelement {tyn} {operand}, i32 {lane}",
            name(result)
        ));
        result
    }
    fn insertlane(&mut self, x: ir::Value, y: ir::Value, lane: impl Into<Uimm8>) -> ir::Value {
        let lane: u8 = lane.into();
        let ty = self.ty(x);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let lane_ty = self.vtyn(y);
        let (vector, scalar) = (self.op(x), self.op(y));
        self.line(format!(
            "{} = insertelement {tyn} {vector}, {lane_ty} {scalar}, i32 {lane}",
            name(result)
        ));
        result
    }
    fn scalar_to_vector(&mut self, ty: ir::Type, x: ir::Value) -> ir::Value {
        let result = self.value(ty);
        let (tyn, from) = (self.tyn(ty), self.vtyn(x));
        let operand = self.op(x);
        // The scalar in lane 0, the other lanes zero.
        self.line(format!(
            "{} = insertelement {tyn} zeroinitializer, {from} {operand}, i32 0",
            name(result)
        ));
        result
    }
    fn shuffle(&mut self, a: ir::Value, b: ir::Value, mask: ir::Immediate) -> ir::Value {
        let ty = self.ty(a);
        let result = self.value(ty);
        let tyn = self.tyn(ty);
        let mask = self.masks[mask.index()]
            .iter()
            .map(|byte| format!("i32 {byte}"))
            .collect::<Vec<_>>();
        let (left, right) = (self.op(a), self.op(b));
        self.line(format!(
            "{} = shufflevector {tyn} {left}, {tyn} {right}, <{} x i32> <{}>",
            name(result),
            mask.len(),
            mask.join(", ")
        ));
        result
    }
    fn shuffle_mask(&mut self, bytes: &[u8]) -> ir::Immediate {
        self.masks.push(bytes.to_vec());
        ir::Immediate::new(self.masks.len() - 1)
    }
}
