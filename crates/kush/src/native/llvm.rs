//! LLVM release backend.
//!
//! The checked executable IR is lowered exactly once, by `Generator`, into
//! verified Cranelift IR. The default backend hands that IR to Cranelift's
//! code generator. This module is the second consumer: it translates the same
//! verified functions into textual LLVM IR, which `clang` optimizes together
//! with the C runtime. Both backends therefore share every lowering decision
//! (evaluation order, checks, layouts, drops, task and handler protocols);
//! only instruction selection and optimization differ.
//!
//! No LLVM library is linked into the compiler and no `unsafe` is needed: the
//! output is a `.ll` file.
//!
//! Value model. Cranelift values are untyped machine words; LLVM optimizes
//! far better when addresses are real pointers. Every translated value keeps
//! its integer form, and values with a known pointer origin (stack slots,
//! symbols, pointers returned by the runtime) additionally keep a pointer
//! form. Address computations are rebuilt as `getelementptr` from the pointer
//! form at each memory access, so stack slots are promoted to registers and
//! array accesses are visible to the loop optimizer.
use super::Result;
use super::error;
use cranelift_codegen::ir::{
    self, Block, ExternalName, InstructionData, Opcode, Value, ValueDef,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_module::{DataId, FuncId, Linkage, ModuleDeclarations};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// A first-class LLVM type used at a C ABI boundary.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Ty {
    Void,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Ptr,
}
impl Ty {
    fn name(self) -> &'static str {
        match self {
            Ty::Void => "void",
            Ty::I8 => "i8",
            Ty::I16 => "i16",
            Ty::I32 => "i32",
            Ty::I64 => "i64",
            Ty::F32 => "float",
            Ty::F64 => "double",
            Ty::Ptr => "ptr",
        }
    }
    fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "void" => Ty::Void,
            "i8" => Ty::I8,
            "i16" => Ty::I16,
            "i32" => Ty::I32,
            "i64" => Ty::I64,
            "float" => Ty::F32,
            "double" => Ty::F64,
            "ptr" => Ty::Ptr,
            _ => return None,
        })
    }
    fn of(ty: ir::Type) -> Option<Self> {
        Some(match ty {
            types::I8 => Ty::I8,
            types::I16 => Ty::I16,
            types::I32 => Ty::I32,
            types::I64 => Ty::I64,
            types::F32 => Ty::F32,
            types::F64 => Ty::F64,
            _ => return None,
        })
    }
    fn bits(self) -> u32 {
        match self {
            Ty::I8 => 8,
            Ty::I16 => 16,
            Ty::I32 | Ty::F32 => 32,
            Ty::I64 | Ty::F64 | Ty::Ptr => 64,
            Ty::Void => 0,
        }
    }
}

/// The exact LLVM signature `clang` gave one runtime function.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(super) struct CSignature {
    pub ret: Ty,
    pub params: Vec<Ty>,
}

/// What the translator needs from the runtime's own LLVM IR: the target
/// description, and each exported function's real signature so calls match it
/// exactly (a call through a mismatched type is never inlined).
#[derive(Default, Debug)]
pub(super) struct RuntimeInterface {
    pub header: String,
    pub signatures: BTreeMap<String, CSignature>,
}
impl RuntimeInterface {
    /// Whether the runtime was compiled to be internalized into the program
    /// module, which then owns `main`.
    fn whole_program(&self) -> bool {
        self.signatures.get(RUNTIME_MAIN).is_some_and(|signature| {
            signature.ret == Ty::I32 && signature.params == [Ty::I32, Ty::Ptr, Ty::Ptr]
        })
    }
    pub fn parse(ir: &str) -> Self {
        let mut interface = Self::default();
        for line in ir.lines() {
            if line.starts_with("target datalayout") || line.starts_with("target triple") {
                interface.header.push_str(line);
                interface.header.push('\n');
            } else if let Some(rest) = line.strip_prefix("define ")
                && let Some((name, signature)) = parse_define(rest)
            {
                interface.signatures.insert(name, signature);
            }
        }
        interface
    }
}
/// Parse `[attrs] RET @name(TYPE [attrs] %n, ...) ...`. Anything outside the
/// first-class scalar subset (aggregates, varargs, internal functions) yields
/// `None`, and calls to that symbol keep the Cranelift signature.
fn parse_define(rest: &str) -> Option<(String, CSignature)> {
    let at = rest.find('@')?;
    let prefix = &rest[..at];
    if prefix.split_whitespace().any(|word| word == "internal") {
        return None;
    }
    let ret = Ty::parse(prefix.split_whitespace().next_back()?)?;
    let open = at + rest[at..].find('(')?;
    let name = rest[at + 1..open].to_owned();
    let mut depth = 0usize;
    let mut close = None;
    for (offset, character) in rest[open..].char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(open + offset);
                    break;
                }
            }
            _ => {}
        }
    }
    let inside = rest[open + 1..close?].trim();
    let mut params = Vec::new();
    if !inside.is_empty() {
        let mut depth = 0usize;
        let mut start = 0;
        let mut pieces = Vec::new();
        for (offset, character) in inside.char_indices() {
            match character {
                '(' | '{' | '[' | '<' => depth += 1,
                ')' | '}' | ']' | '>' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => {
                    pieces.push(&inside[start..offset]);
                    start = offset + 1;
                }
                _ => {}
            }
        }
        pieces.push(&inside[start..]);
        for piece in pieces {
            let piece = piece.trim();
            if piece.contains("byval") || piece.contains("sret") {
                return None;
            }
            params.push(Ty::parse(piece.split_whitespace().next()?)?);
        }
    }
    Some((name, CSignature { ret, params }))
}

/// The runtime's entry point when it is compiled for whole-program linking
/// (`KUSH_WHOLE_PROGRAM`). The program module then defines `main`, which
/// passes the program's entry function to it.
const RUNTIME_MAIN: &str = "kush_runtime_main";
const PROGRAM_ENTRY: &str = "kush_entry";

/// The program's LLVM module under construction.
pub(super) struct LlvmModule {
    runtime: RuntimeInterface,
    functions: Vec<String>,
    defined: BTreeSet<FuncId>,
    data: BTreeMap<DataId, Vec<u8>>,
    intrinsics: BTreeSet<String>,
}
impl LlvmModule {
    pub fn new(runtime: RuntimeInterface) -> Self {
        Self {
            runtime,
            functions: Vec::new(),
            defined: BTreeSet::new(),
            data: BTreeMap::new(),
            intrinsics: BTreeSet::new(),
        }
    }
    pub fn define_data(&mut self, id: DataId, bytes: Vec<u8>) {
        self.data.insert(id, bytes);
    }
    pub fn define_function(
        &mut self,
        id: FuncId,
        func: &ir::Function,
        declarations: &ModuleDeclarations,
    ) -> Result<()> {
        let declaration = declarations.get_function_decl(id);
        let name = declaration.linkage_name(id).into_owned();
        // In a whole-program build only `main` is visible; the entry function
        // is reached through the pointer `main` passes to the runtime.
        let linkage = if name == PROGRAM_ENTRY && self.runtime.whole_program() {
            Linkage::Local
        } else {
            declaration.linkage
        };
        let text = Translator::new(func, declarations, &self.runtime, &mut self.intrinsics)
            .function(&name, linkage)
            .map_err(|message| error(format!("LLVM backend: in {name}: {message}")))?;
        self.functions.push(text);
        self.defined.insert(id);
        Ok(())
    }
    /// The complete textual module.
    pub fn finish(self, declarations: &ModuleDeclarations) -> Result<String> {
        let mut out = String::new();
        out.push_str("; Kush program module (LLVM release backend)\n");
        out.push_str(&self.runtime.header);
        out.push('\n');
        for (id, declaration) in declarations.get_data_objects() {
            let name = declaration.linkage_name(id);
            match self.data.get(&id) {
                Some(bytes) => {
                    let linkage = match declaration.linkage {
                        Linkage::Local | Linkage::Hidden => "internal ",
                        _ => "",
                    };
                    let kind = if declaration.writable {
                        "global"
                    } else {
                        "constant"
                    };
                    let _ = write!(out, "@{name} = {linkage}{kind} [{} x i8] c\"", bytes.len());
                    for byte in bytes {
                        let _ = write!(out, "\\{byte:02X}");
                    }
                    out.push_str("\", align 8\n");
                }
                None => {
                    let _ = writeln!(out, "@{name} = external global i8");
                }
            }
        }
        out.push('\n');
        for (id, declaration) in declarations.get_functions() {
            if self.defined.contains(&id) {
                continue;
            }
            let name = declaration.linkage_name(id);
            match self.runtime.signatures.get(name.as_ref()) {
                Some(signature) if signature.params.len() == declaration.signature.params.len() => {
                    let params = signature
                        .params
                        .iter()
                        .map(|ty| ty.name())
                        .collect::<Vec<_>>()
                        .join(", ");
                    let _ = writeln!(out, "declare {} @{name}({params})", signature.ret.name());
                }
                _ => {
                    let (ret, params) = clif_signature(&declaration.signature)
                        .map_err(|message| error(format!("LLVM backend: {name}: {message}")))?;
                    let _ = writeln!(out, "declare {ret} @{name}({})", params.join(", "));
                }
            }
        }
        for intrinsic in &self.intrinsics {
            out.push_str(intrinsic);
            out.push('\n');
        }
        out.push('\n');
        for function in &self.functions {
            out.push_str(function);
            out.push('\n');
        }
        // Whole-program builds internalize the runtime, which would hide its
        // `main`; the real entry point lives here and forwards to it.
        if self.runtime.whole_program() {
            let _ = writeln!(
                out,
                "declare i32 @{RUNTIME_MAIN}(i32, ptr, ptr)\n\
                 define i32 @main(i32 %argc, ptr %argv) #0 {{\n  \
                 %status = tail call i32 @{RUNTIME_MAIN}(i32 %argc, ptr %argv, ptr @{PROGRAM_ENTRY})\n  \
                 ret i32 %status\n}}\n"
            );
        }
        out.push_str("attributes #0 = { nounwind }\n");
        out.push_str(MODULE_METADATA);
        Ok(out)
    }
}

type Tx<T> = std::result::Result<T, String>;

fn ty_name(ty: ir::Type) -> Tx<&'static str> {
    Ty::of(ty)
        .map(Ty::name)
        .ok_or_else(|| format!("unsupported value type {ty}"))
}
fn extension(param: &ir::AbiParam) -> &'static str {
    match param.extension {
        ir::ArgumentExtension::Uext => " zeroext",
        ir::ArgumentExtension::Sext => " signext",
        ir::ArgumentExtension::None => "",
    }
}
fn return_type(signature: &ir::Signature) -> Tx<String> {
    Ok(match signature.returns.as_slice() {
        [] => "void".to_owned(),
        [one] => ty_name(one.value_type)?.to_owned(),
        many => {
            let parts = many
                .iter()
                .map(|param| ty_name(param.value_type))
                .collect::<Tx<Vec<_>>>()?;
            format!("{{ {} }}", parts.join(", "))
        }
    })
}
fn clif_signature(signature: &ir::Signature) -> Tx<(String, Vec<String>)> {
    let params = signature
        .params
        .iter()
        .map(|param| {
            Ok(format!(
                "{}{}",
                ty_name(param.value_type)?,
                extension(param)
            ))
        })
        .collect::<Tx<Vec<_>>>()?;
    Ok((return_type(signature)?, params))
}

struct Edge {
    from: String,
    target: Block,
    values: Vec<String>,
}

struct Translator<'a> {
    func: &'a ir::Function,
    declarations: &'a ModuleDeclarations,
    runtime: &'a RuntimeInterface,
    intrinsics: &'a mut BTreeSet<String>,
    /// Values that are plain literals and never get an SSA name.
    constants: BTreeMap<Value, String>,
    /// Pointer form of a value, valid wherever the value itself is.
    pointers: BTreeMap<Value, String>,
    /// `i1` form of a comparison or overflow flag.
    flags: BTreeMap<Value, String>,
    body: String,
    label: String,
    temporaries: usize,
    splits: usize,
    edges: Vec<Edge>,
}

impl<'a> Translator<'a> {
    fn new(
        func: &'a ir::Function,
        declarations: &'a ModuleDeclarations,
        runtime: &'a RuntimeInterface,
        intrinsics: &'a mut BTreeSet<String>,
    ) -> Self {
        Self {
            func,
            declarations,
            runtime,
            intrinsics,
            constants: BTreeMap::new(),
            pointers: BTreeMap::new(),
            flags: BTreeMap::new(),
            body: String::new(),
            label: String::new(),
            temporaries: 0,
            splits: 0,
            edges: Vec::new(),
        }
    }
    fn resolve(&self, value: Value) -> Value {
        self.func.dfg.resolve_aliases(value)
    }
    fn ty(&self, value: Value) -> ir::Type {
        self.func.dfg.value_type(value)
    }
    fn tyn(&self, value: Value) -> Tx<&'static str> {
        ty_name(self.ty(value))
    }
    /// The operand text of a value: a literal or its SSA name.
    fn op(&self, value: Value) -> String {
        let value = self.resolve(value);
        match self.constants.get(&value) {
            Some(literal) => literal.clone(),
            None => format!("%v{}", value.as_u32()),
        }
    }
    fn name(&self, value: Value) -> String {
        format!("%v{}", value.as_u32())
    }
    fn temp(&mut self) -> String {
        self.temporaries += 1;
        format!("%t{}", self.temporaries)
    }
    fn line(&mut self, text: impl AsRef<str>) {
        self.body.push_str("  ");
        self.body.push_str(text.as_ref());
        self.body.push('\n');
    }
    fn intrinsic(&mut self, declaration: &str) {
        if !self.intrinsics.contains(declaration) {
            self.intrinsics.insert(declaration.to_owned());
        }
    }
    fn start_block(&mut self, label: String) {
        let _ = writeln!(self.body, "{label}:");
        self.label = label;
    }
    fn trap(&mut self) {
        self.intrinsic("declare void @llvm.trap()");
        self.line("call void @llvm.trap()");
        self.line("unreachable");
    }
    /// Trap when `condition` (an `i1`) holds, continuing in a fresh block.
    fn trap_if(&mut self, condition: &str) {
        self.splits += 1;
        let trap = format!("{}.t{}", self.label, self.splits);
        let next = format!("{}.c{}", self.label, self.splits);
        self.line(format!(
            "br i1 {condition}, label %{trap}, label %{next}, !prof !0"
        ));
        self.start_block(trap);
        self.trap();
        self.start_block(next);
    }
    /// The `i1` truth of an integer value.
    fn truth(&mut self, value: Value) -> Tx<String> {
        let value = self.resolve(value);
        if let Some(flag) = self.flags.get(&value) {
            return Ok(flag.clone());
        }
        let temp = self.temp();
        let ty = self.tyn(value)?;
        let operand = self.op(value);
        self.line(format!("{temp} = icmp ne {ty} {operand}, 0"));
        Ok(temp)
    }
    /// Define `result` (an integer value) from an `i1`, remembering the flag.
    fn define_flag(&mut self, result: Value, flag: String) -> Tx<()> {
        let ty = self.tyn(result)?;
        let name = self.name(result);
        self.line(format!("{name} = zext i1 {flag} to {ty}"));
        self.flags.insert(result, flag);
        Ok(())
    }
    fn defining(&self, value: Value) -> Option<&InstructionData> {
        match self.func.dfg.value_def(value) {
            ValueDef::Result(inst, 0) => Some(&self.func.dfg.insts[inst]),
            _ => None,
        }
    }
    /// Whether a value is clearly an offset rather than an address.
    fn offset_like(&self, value: Value) -> bool {
        let value = self.resolve(value);
        if self.constants.contains_key(&value) {
            return true;
        }
        match self.defining(value) {
            Some(InstructionData::Binary { opcode, .. }) => matches!(
                opcode,
                Opcode::Imul
                    | Opcode::Ishl
                    | Opcode::Ushr
                    | Opcode::Sshr
                    | Opcode::Band
                    | Opcode::Udiv
                    | Opcode::Sdiv
                    | Opcode::Urem
                    | Opcode::Srem
            ),
            Some(InstructionData::Unary { opcode, .. }) => {
                matches!(opcode, Opcode::Uextend | Opcode::Sextend | Opcode::Ineg)
            }
            _ => false,
        }
    }
    /// The pointer form of an address-valued word, materialized here.
    fn pointer(&mut self, value: Value) -> Tx<String> {
        self.pointer_at(value, 4)
    }
    fn pointer_at(&mut self, value: Value, depth: usize) -> Tx<String> {
        let value = self.resolve(value);
        if let Some(pointer) = self.pointers.get(&value) {
            return Ok(pointer.clone());
        }
        if self.ty(value) != types::I64 {
            return Err("address is not a 64-bit word".into());
        }
        if depth > 0
            && let Some(InstructionData::Binary {
                opcode: Opcode::Iadd,
                args,
            }) = self.defining(value)
        {
            let (left, right) = (self.resolve(args[0]), self.resolve(args[1]));
            let choice = if self.pointers.contains_key(&left) {
                Some((left, right))
            } else if self.pointers.contains_key(&right) {
                Some((right, left))
            } else if self.offset_like(right) && !self.offset_like(left) {
                Some((left, right))
            } else if self.offset_like(left) && !self.offset_like(right) {
                Some((right, left))
            } else {
                None
            };
            if let Some((base, offset)) = choice {
                let base = self.pointer_at(base, depth - 1)?;
                let offset = self.op(offset);
                let temp = self.temp();
                self.line(format!(
                    "{temp} = getelementptr i8, ptr {base}, i64 {offset}"
                ));
                return Ok(temp);
            }
        }
        let temp = self.temp();
        let operand = self.op(value);
        self.line(format!("{temp} = inttoptr i64 {operand} to ptr"));
        Ok(temp)
    }
    fn address(&mut self, base: Value, offset: i64) -> Tx<String> {
        let pointer = self.pointer(base)?;
        if offset == 0 {
            return Ok(pointer);
        }
        let temp = self.temp();
        self.line(format!(
            "{temp} = getelementptr i8, ptr {pointer}, i64 {offset}"
        ));
        Ok(temp)
    }
    /// Give `result` both forms from a freshly produced pointer.
    fn define_pointer(&mut self, result: Value, pointer: String) {
        let name = self.name(result);
        self.line(format!("{name} = ptrtoint ptr {pointer} to i64"));
        self.pointers.insert(result, pointer);
    }
    fn function_name(&self, func_ref: ir::FuncRef) -> Tx<(String, &'a ir::Signature)> {
        let data = &self.func.dfg.ext_funcs[func_ref];
        let signature = &self.func.dfg.signatures[data.signature];
        let ExternalName::User(reference) = data.name else {
            return Err(format!("unsupported callee {:?}", data.name));
        };
        let user = &self.func.params.user_named_funcs()[reference];
        if user.namespace != 0 {
            return Err("callee is not a function".into());
        }
        let id = FuncId::from_u32(user.index);
        Ok((
            self.declarations
                .get_function_decl(id)
                .linkage_name(id)
                .into_owned(),
            signature,
        ))
    }
    fn convert_argument(&mut self, value: Value, to: Ty) -> Tx<Option<String>> {
        let from = Ty::of(self.ty(value)).ok_or("unsupported argument type")?;
        if from == to {
            return Ok(Some(self.op(value)));
        }
        if from == Ty::I64 && to == Ty::Ptr {
            return Ok(Some(self.pointer(value)?));
        }
        Ok(None)
    }
    fn call(
        &mut self,
        inst: ir::Inst,
        callee: &str,
        signature: &ir::Signature,
        arguments: &[Value],
        runtime: Option<&CSignature>,
    ) -> Tx<()> {
        let results = self.func.dfg.inst_results(inst).to_vec();
        // Use the runtime's exact signature when every word converts to it.
        if let Some(c) = runtime
            && c.params.len() == arguments.len()
            && results.len() <= 1
            && arguments.iter().zip(&c.params).all(|(value, to)| {
                let from = Ty::of(self.ty(*value));
                from == Some(*to) || (from == Some(Ty::I64) && *to == Ty::Ptr)
            })
            && match results.first().map(|value| Ty::of(self.ty(*value))) {
                None => true,
                Some(Some(Ty::I64)) => matches!(c.ret, Ty::I64 | Ty::Ptr),
                Some(other) => other == Some(c.ret),
            }
        {
            let mut rendered = Vec::new();
            for (value, to) in arguments.iter().zip(&c.params) {
                let operand = self
                    .convert_argument(*value, *to)?
                    .ok_or("argument conversion")?;
                rendered.push(format!("{} {operand}", to.name()));
            }
            let arguments = rendered.join(", ");
            match results.first() {
                None => self.line(format!("call {} {callee}({arguments})", c.ret.name())),
                Some(result) if c.ret == Ty::Ptr => {
                    let temp = self.temp();
                    self.line(format!("{temp} = call ptr {callee}({arguments})"));
                    self.define_pointer(*result, temp);
                }
                Some(result) => {
                    let name = self.name(*result);
                    self.line(format!(
                        "{name} = call {} {callee}({arguments})",
                        c.ret.name()
                    ));
                }
            }
            return Ok(());
        }
        let mut rendered = Vec::new();
        for (value, param) in arguments.iter().zip(&signature.params) {
            rendered.push(format!(
                "{}{} {}",
                self.tyn(*value)?,
                extension(param),
                self.op(*value)
            ));
        }
        let arguments = rendered.join(", ");
        let ret = return_type(signature)?;
        match results.as_slice() {
            [] => self.line(format!("call {ret} {callee}({arguments})")),
            [result] => {
                let name = self.name(*result);
                self.line(format!("{name} = call {ret} {callee}({arguments})"));
            }
            many => {
                let temp = self.temp();
                self.line(format!("{temp} = call {ret} {callee}({arguments})"));
                for (index, result) in many.iter().enumerate() {
                    let name = self.name(*result);
                    self.line(format!("{name} = extractvalue {ret} {temp}, {index}"));
                }
            }
        }
        Ok(())
    }
    fn edge(&mut self, call: ir::BlockCall) -> Tx<(Block, Vec<String>)> {
        let pool = &self.func.dfg.value_lists;
        let target = call.block(pool);
        let mut values = Vec::new();
        for argument in call.args(pool) {
            let value = argument
                .as_value()
                .ok_or("exception block arguments are unsupported")?;
            values.push(self.op(value));
        }
        Ok((target, values))
    }
    fn binary(&mut self, inst: ir::Inst, operation: &str, args: [Value; 2]) -> Tx<()> {
        let result = self.func.dfg.first_result(inst);
        let (name, ty) = (self.name(result), self.tyn(result)?);
        let (left, right) = (self.op(args[0]), self.op(args[1]));
        self.line(format!("{name} = {operation} {ty} {left}, {right}"));
        Ok(())
    }
    fn overflow(&mut self, inst: ir::Inst, operation: &str, args: [Value; 2]) -> Tx<()> {
        let results = self.func.dfg.inst_results(inst).to_vec();
        let ty = self.tyn(results[0])?;
        self.intrinsic(&format!(
            "declare {{ {ty}, i1 }} @llvm.{operation}.with.overflow.{ty}({ty}, {ty})"
        ));
        let pair = self.temp();
        let (left, right) = (self.op(args[0]), self.op(args[1]));
        self.line(format!(
            "{pair} = call {{ {ty}, i1 }} @llvm.{operation}.with.overflow.{ty}({ty} {left}, {ty} {right})"
        ));
        let name = self.name(results[0]);
        self.line(format!("{name} = extractvalue {{ {ty}, i1 }} {pair}, 0"));
        let flag = self.temp();
        self.line(format!("{flag} = extractvalue {{ {ty}, i1 }} {pair}, 1"));
        self.define_flag(results[1], flag)
    }
    fn unary_intrinsic(&mut self, inst: ir::Inst, base: &str, arg: Value, extra: &str) -> Tx<()> {
        let result = self.func.dfg.first_result(inst);
        let (name, ty) = (self.name(result), self.tyn(result)?);
        let extra_types = if extra.is_empty() { "" } else { ", i1" };
        self.intrinsic(&format!(
            "declare {ty} @llvm.{base}.{suffix}({ty}{extra_types})",
            suffix = intrinsic_suffix(ty)
        ));
        let operand = self.op(arg);
        self.line(format!(
            "{name} = call {ty} @llvm.{base}.{suffix}({ty} {operand}{extra})",
            suffix = intrinsic_suffix(ty)
        ));
        Ok(())
    }
    fn binary_intrinsic(&mut self, inst: ir::Inst, base: &str, args: [Value; 2]) -> Tx<()> {
        let result = self.func.dfg.first_result(inst);
        let (name, ty) = (self.name(result), self.tyn(result)?);
        let suffix = intrinsic_suffix(ty);
        self.intrinsic(&format!("declare {ty} @llvm.{base}.{suffix}({ty}, {ty})"));
        let (left, right) = (self.op(args[0]), self.op(args[1]));
        self.line(format!(
            "{name} = call {ty} @llvm.{base}.{suffix}({ty} {left}, {ty} {right})"
        ));
        Ok(())
    }
    /// A shift amount reduced modulo the width and converted to the shifted
    /// type, which is Cranelift's defined behaviour for every amount.
    fn shift_amount(&mut self, value: Value, amount: Value) -> Tx<String> {
        let to = Ty::of(self.ty(value)).ok_or("shift type")?;
        let from = Ty::of(self.ty(amount)).ok_or("shift amount type")?;
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
        Ok(masked)
    }
    fn load(&mut self, inst: ir::Inst, opcode: Opcode, base: Value, offset: i64) -> Tx<()> {
        let result = self.func.dfg.first_result(inst);
        let (name, ty) = (self.name(result), self.tyn(result)?);
        let address = self.address(base, offset)?;
        let narrow = match opcode {
            Opcode::Load => None,
            Opcode::Uload8 => Some(("i8", "zext")),
            Opcode::Sload8 => Some(("i8", "sext")),
            Opcode::Uload16 => Some(("i16", "zext")),
            Opcode::Sload16 => Some(("i16", "sext")),
            Opcode::Uload32 => Some(("i32", "zext")),
            Opcode::Sload32 => Some(("i32", "sext")),
            _ => return Err(format!("unsupported load {opcode}")),
        };
        match narrow {
            None => self.line(format!("{name} = load {ty}, ptr {address}, align 1")),
            Some((memory, extend)) => {
                let temp = self.temp();
                self.line(format!("{temp} = load {memory}, ptr {address}, align 1"));
                self.line(format!("{name} = {extend} {memory} {temp} to {ty}"));
            }
        }
        Ok(())
    }
    fn store(&mut self, opcode: Opcode, value: Value, base: Value, offset: i64) -> Tx<()> {
        let address = self.address(base, offset)?;
        let ty = self.tyn(value)?;
        let operand = self.op(value);
        let memory = match opcode {
            Opcode::Store => None,
            Opcode::Istore8 => Some("i8"),
            Opcode::Istore16 => Some("i16"),
            Opcode::Istore32 => Some("i32"),
            _ => return Err(format!("unsupported store {opcode}")),
        };
        match memory {
            Some(memory) if memory != ty => {
                let temp = self.temp();
                self.line(format!("{temp} = trunc {ty} {operand} to {memory}"));
                self.line(format!("store {memory} {temp}, ptr {address}, align 1"));
            }
            _ => self.line(format!("store {ty} {operand}, ptr {address}, align 1")),
        }
        Ok(())
    }
    fn division(&mut self, inst: ir::Inst, opcode: Opcode, args: [Value; 2]) -> Tx<()> {
        let result = self.func.dfg.first_result(inst);
        let (name, ty) = (self.name(result), self.tyn(result)?);
        let bits = Ty::of(self.ty(result)).ok_or("division type")?.bits();
        let (left, right) = (self.op(args[0]), self.op(args[1]));
        // Cranelift traps where LLVM has undefined behaviour.
        let zero = self.temp();
        self.line(format!("{zero} = icmp eq {ty} {right}, 0"));
        self.trap_if(&zero);
        let minimum = i128::from(-1i64) << (bits - 1);
        match opcode {
            Opcode::Udiv => self.line(format!("{name} = udiv {ty} {left}, {right}")),
            Opcode::Urem => self.line(format!("{name} = urem {ty} {left}, {right}")),
            Opcode::Sdiv => {
                let (a, b, both) = (self.temp(), self.temp(), self.temp());
                self.line(format!("{a} = icmp eq {ty} {left}, {minimum}"));
                self.line(format!("{b} = icmp eq {ty} {right}, -1"));
                self.line(format!("{both} = and i1 {a}, {b}"));
                self.trap_if(&both);
                self.line(format!("{name} = sdiv {ty} {left}, {right}"));
            }
            Opcode::Srem => {
                // `MIN % -1` is 0 in Cranelift; any `x % 1` is also 0.
                let (b, divisor) = (self.temp(), self.temp());
                self.line(format!("{b} = icmp eq {ty} {right}, -1"));
                self.line(format!("{divisor} = select i1 {b}, {ty} 1, {ty} {right}"));
                self.line(format!("{name} = srem {ty} {left}, {divisor}"));
            }
            _ => unreachable!(),
        }
        Ok(())
    }
    fn instruction(&mut self, inst: ir::Inst) -> Tx<()> {
        let func = self.func;
        let dfg = &func.dfg;
        let data = dfg.insts[inst];
        let opcode = data.opcode();
        match data {
            InstructionData::UnaryImm { imm, .. } => {
                let result = dfg.first_result(inst);
                let bits = Ty::of(self.ty(result)).ok_or("constant type")?.bits();
                let raw = imm.bits();
                let value = if bits == 64 {
                    raw
                } else {
                    (raw << (64 - bits)) >> (64 - bits)
                };
                self.constants.insert(result, value.to_string());
            }
            InstructionData::UnaryIeee32 { imm, .. } => {
                let name = self.name(dfg.first_result(inst));
                self.line(format!("{name} = bitcast i32 {} to float", imm.bits()));
            }
            InstructionData::UnaryIeee64 { imm, .. } => {
                let name = self.name(dfg.first_result(inst));
                self.line(format!("{name} = bitcast i64 {} to double", imm.bits()));
            }
            InstructionData::NullAry { .. } if opcode == Opcode::Nop => {}
            InstructionData::Binary { args, .. } => match opcode {
                Opcode::Iadd => self.binary(inst, "add", args)?,
                Opcode::Isub => self.binary(inst, "sub", args)?,
                Opcode::Imul => self.binary(inst, "mul", args)?,
                Opcode::Band => self.binary(inst, "and", args)?,
                Opcode::Bor => self.binary(inst, "or", args)?,
                Opcode::Bxor => self.binary(inst, "xor", args)?,
                Opcode::Udiv | Opcode::Sdiv | Opcode::Urem | Opcode::Srem => {
                    self.division(inst, opcode, args)?;
                }
                Opcode::Ishl | Opcode::Ushr | Opcode::Sshr => {
                    let result = dfg.first_result(inst);
                    let (name, ty) = (self.name(result), self.tyn(result)?);
                    let amount = self.shift_amount(args[0], args[1])?;
                    let left = self.op(args[0]);
                    let operation = match opcode {
                        Opcode::Ishl => "shl",
                        Opcode::Ushr => "lshr",
                        _ => "ashr",
                    };
                    self.line(format!("{name} = {operation} {ty} {left}, {amount}"));
                }
                Opcode::Rotl | Opcode::Rotr => {
                    let result = dfg.first_result(inst);
                    let (name, ty) = (self.name(result), self.tyn(result)?);
                    let amount = self.shift_amount(args[0], args[1])?;
                    let left = self.op(args[0]);
                    let base = if opcode == Opcode::Rotl {
                        "fshl"
                    } else {
                        "fshr"
                    };
                    self.intrinsic(&format!("declare {ty} @llvm.{base}.{ty}({ty}, {ty}, {ty})"));
                    self.line(format!(
                        "{name} = call {ty} @llvm.{base}.{ty}({ty} {left}, {ty} {left}, {ty} {amount})"
                    ));
                }
                Opcode::Smin => self.binary_intrinsic(inst, "smin", args)?,
                Opcode::Smax => self.binary_intrinsic(inst, "smax", args)?,
                Opcode::Umin => self.binary_intrinsic(inst, "umin", args)?,
                Opcode::Umax => self.binary_intrinsic(inst, "umax", args)?,
                Opcode::SaddOverflow => self.overflow(inst, "sadd", args)?,
                Opcode::SsubOverflow => self.overflow(inst, "ssub", args)?,
                Opcode::SmulOverflow => self.overflow(inst, "smul", args)?,
                Opcode::UaddOverflow => self.overflow(inst, "uadd", args)?,
                Opcode::UsubOverflow => self.overflow(inst, "usub", args)?,
                Opcode::UmulOverflow => self.overflow(inst, "umul", args)?,
                Opcode::Fadd => self.binary(inst, "fadd", args)?,
                Opcode::Fsub => self.binary(inst, "fsub", args)?,
                Opcode::Fmul => self.binary(inst, "fmul", args)?,
                Opcode::Fdiv => self.binary(inst, "fdiv", args)?,
                Opcode::Fmin => self.binary_intrinsic(inst, "minimum", args)?,
                Opcode::Fmax => self.binary_intrinsic(inst, "maximum", args)?,
                Opcode::Fcopysign => self.binary_intrinsic(inst, "copysign", args)?,
                _ => return Err(format!("unsupported instruction {opcode}")),
            },
            InstructionData::Unary { arg, .. } => {
                let result = dfg.first_result(inst);
                let (name, ty) = (self.name(result), self.tyn(result)?);
                let (from, operand) = (self.tyn(arg)?, self.op(arg));
                match opcode {
                    Opcode::Uextend => self.line(format!("{name} = zext {from} {operand} to {ty}")),
                    Opcode::Sextend => self.line(format!("{name} = sext {from} {operand} to {ty}")),
                    Opcode::Ireduce => {
                        self.line(format!("{name} = trunc {from} {operand} to {ty}"));
                    }
                    Opcode::Bnot => self.line(format!("{name} = xor {ty} {operand}, -1")),
                    Opcode::Ineg => self.line(format!("{name} = sub {ty} 0, {operand}")),
                    Opcode::Bmask => {
                        let flag = self.truth(arg)?;
                        self.line(format!("{name} = sext i1 {flag} to {ty}"));
                    }
                    Opcode::Fpromote => {
                        self.line(format!("{name} = fpext {from} {operand} to {ty}"))
                    }
                    Opcode::Fdemote => {
                        self.line(format!("{name} = fptrunc {from} {operand} to {ty}"));
                    }
                    Opcode::Fneg => self.line(format!("{name} = fneg {ty} {operand}")),
                    Opcode::FcvtFromSint => {
                        self.line(format!("{name} = sitofp {from} {operand} to {ty}"));
                    }
                    Opcode::FcvtFromUint => {
                        self.line(format!("{name} = uitofp {from} {operand} to {ty}"));
                    }
                    Opcode::FcvtToSintSat | Opcode::FcvtToUintSat => {
                        let base = if opcode == Opcode::FcvtToSintSat {
                            "fptosi"
                        } else {
                            "fptoui"
                        };
                        let suffix = intrinsic_suffix(from);
                        self.intrinsic(&format!(
                            "declare {ty} @llvm.{base}.sat.{ty}.{suffix}({from})"
                        ));
                        self.line(format!(
                            "{name} = call {ty} @llvm.{base}.sat.{ty}.{suffix}({from} {operand})"
                        ));
                    }
                    Opcode::Sqrt => self.unary_intrinsic(inst, "sqrt", arg, "")?,
                    Opcode::Fabs => self.unary_intrinsic(inst, "fabs", arg, "")?,
                    Opcode::Ceil => self.unary_intrinsic(inst, "ceil", arg, "")?,
                    Opcode::Floor => self.unary_intrinsic(inst, "floor", arg, "")?,
                    Opcode::Trunc => self.unary_intrinsic(inst, "trunc", arg, "")?,
                    Opcode::Nearest => self.unary_intrinsic(inst, "roundeven", arg, "")?,
                    Opcode::Clz => self.unary_intrinsic(inst, "ctlz", arg, ", i1 false")?,
                    Opcode::Ctz => self.unary_intrinsic(inst, "cttz", arg, ", i1 false")?,
                    Opcode::Popcnt => self.unary_intrinsic(inst, "ctpop", arg, "")?,
                    Opcode::Bswap => self.unary_intrinsic(inst, "bswap", arg, "")?,
                    Opcode::Iabs => self.unary_intrinsic(inst, "abs", arg, ", i1 false")?,
                    _ => return Err(format!("unsupported instruction {opcode}")),
                }
            }
            InstructionData::LoadNoOffset { arg, .. } if opcode == Opcode::Bitcast => {
                let result = dfg.first_result(inst);
                let (name, ty) = (self.name(result), self.tyn(result)?);
                let (from, operand) = (self.tyn(arg)?, self.op(arg));
                self.line(format!("{name} = bitcast {from} {operand} to {ty}"));
            }
            InstructionData::IntCompare { args, cond, .. } => {
                let predicate = match cond {
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
                let ty = self.tyn(args[0])?;
                let (left, right) = (self.op(args[0]), self.op(args[1]));
                let flag = self.temp();
                self.line(format!("{flag} = icmp {predicate} {ty} {left}, {right}"));
                self.define_flag(dfg.first_result(inst), flag)?;
            }
            InstructionData::FloatCompare { args, cond, .. } => {
                let predicate = match cond {
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
                let ty = self.tyn(args[0])?;
                let (left, right) = (self.op(args[0]), self.op(args[1]));
                let flag = self.temp();
                self.line(format!("{flag} = fcmp {predicate} {ty} {left}, {right}"));
                self.define_flag(dfg.first_result(inst), flag)?;
            }
            InstructionData::Ternary { args, .. }
                if matches!(opcode, Opcode::Select | Opcode::SelectSpectreGuard) =>
            {
                let result = dfg.first_result(inst);
                let (name, ty) = (self.name(result), self.tyn(result)?);
                let flag = self.truth(args[0])?;
                let (yes, no) = (self.op(args[1]), self.op(args[2]));
                self.line(format!("{name} = select i1 {flag}, {ty} {yes}, {ty} {no}"));
            }
            InstructionData::Ternary { args, .. } if opcode == Opcode::Fma => {
                let result = dfg.first_result(inst);
                let (name, ty) = (self.name(result), self.tyn(result)?);
                let suffix = intrinsic_suffix(ty);
                self.intrinsic(&format!(
                    "declare {ty} @llvm.fma.{suffix}({ty}, {ty}, {ty})"
                ));
                let (a, b, c) = (self.op(args[0]), self.op(args[1]), self.op(args[2]));
                self.line(format!(
                    "{name} = call {ty} @llvm.fma.{suffix}({ty} {a}, {ty} {b}, {ty} {c})"
                ));
            }
            InstructionData::Load { arg, offset, .. } => {
                self.load(inst, opcode, arg, i64::from(offset))?;
            }
            InstructionData::LoadNoOffset { arg, .. } => self.load(inst, Opcode::Load, arg, 0)?,
            InstructionData::Store { args, offset, .. } => {
                self.store(opcode, args[0], args[1], i64::from(offset))?;
            }
            InstructionData::StoreNoOffset { args, .. } => {
                self.store(Opcode::Store, args[0], args[1], 0)?;
            }
            InstructionData::StackAddr {
                stack_slot, offset, ..
            } => {
                let slot = format!("%ss{}", stack_slot.as_u32());
                let offset = i64::from(offset);
                let pointer = if offset == 0 {
                    slot
                } else {
                    let temp = self.temp();
                    self.line(format!(
                        "{temp} = getelementptr inbounds i8, ptr {slot}, i64 {offset}"
                    ));
                    temp
                };
                self.define_pointer(dfg.first_result(inst), pointer);
            }
            InstructionData::UnaryGlobalValue { global_value, .. }
                if opcode == Opcode::SymbolValue =>
            {
                let ir::GlobalValueData::Symbol { name, offset, .. } =
                    &self.func.global_values[global_value]
                else {
                    return Err("unsupported global value".into());
                };
                let ExternalName::User(reference) = name else {
                    return Err("unsupported symbol".into());
                };
                let user = &self.func.params.user_named_funcs()[*reference];
                let symbol = if user.namespace == 0 {
                    let id = FuncId::from_u32(user.index);
                    self.declarations
                        .get_function_decl(id)
                        .linkage_name(id)
                        .into_owned()
                } else {
                    let id = DataId::from_u32(user.index);
                    self.declarations
                        .get_data_decl(id)
                        .linkage_name(id)
                        .into_owned()
                };
                let offset = offset.bits();
                let pointer = if offset == 0 {
                    format!("@{symbol}")
                } else {
                    let temp = self.temp();
                    self.line(format!(
                        "{temp} = getelementptr i8, ptr @{symbol}, i64 {offset}"
                    ));
                    temp
                };
                self.define_pointer(dfg.first_result(inst), pointer);
            }
            InstructionData::FuncAddr { func_ref, .. } => {
                let (callee, _) = self.function_name(func_ref)?;
                self.define_pointer(dfg.first_result(inst), format!("@{callee}"));
            }
            InstructionData::Call { args, func_ref, .. } => {
                let arguments = args.as_slice(&dfg.value_lists).to_vec();
                let (callee, signature) = self.function_name(func_ref)?;
                let interface = self.runtime;
                let runtime = interface.signatures.get(&callee);
                self.call(inst, &format!("@{callee}"), signature, &arguments, runtime)?;
            }
            InstructionData::CallIndirect { args, sig_ref, .. } => {
                let arguments = args.as_slice(&dfg.value_lists).to_vec();
                let signature = &self.func.dfg.signatures[sig_ref];
                let callee = self.pointer_at(arguments[0], 0)?;
                self.call(inst, &callee, signature, &arguments[1..], None)?;
            }
            InstructionData::Trap { .. } => self.trap(),
            InstructionData::CondTrap { arg, .. } => {
                let flag = self.truth(arg)?;
                let flag = if opcode == Opcode::Trapz {
                    let inverted = self.temp();
                    self.line(format!("{inverted} = xor i1 {flag}, true"));
                    inverted
                } else {
                    flag
                };
                self.trap_if(&flag);
            }
            InstructionData::Jump { destination, .. } => {
                let (target, values) = self.edge(destination)?;
                self.line(format!("br label %b{}", target.as_u32()));
                self.edges.push(Edge {
                    from: self.label.clone(),
                    target,
                    values,
                });
            }
            InstructionData::Brif { arg, blocks, .. } => {
                let flag = self.truth(arg)?;
                let (then_target, then_values) = self.edge(blocks[0])?;
                let (else_target, else_values) = self.edge(blocks[1])?;
                if then_target == else_target {
                    // One predecessor edge: merge the two argument lists.
                    let params = self.func.dfg.block_params(then_target).to_vec();
                    let mut values = Vec::new();
                    for ((yes, no), param) in then_values.iter().zip(&else_values).zip(params) {
                        if yes == no {
                            values.push(yes.clone());
                        } else {
                            let ty = self.tyn(param)?;
                            let temp = self.temp();
                            self.line(format!("{temp} = select i1 {flag}, {ty} {yes}, {ty} {no}"));
                            values.push(temp);
                        }
                    }
                    self.line(format!("br label %b{}", then_target.as_u32()));
                    self.edges.push(Edge {
                        from: self.label.clone(),
                        target: then_target,
                        values,
                    });
                } else {
                    self.line(format!(
                        "br i1 {flag}, label %b{}, label %b{}",
                        then_target.as_u32(),
                        else_target.as_u32()
                    ));
                    for (target, values) in [(then_target, then_values), (else_target, else_values)]
                    {
                        self.edges.push(Edge {
                            from: self.label.clone(),
                            target,
                            values,
                        });
                    }
                }
            }
            InstructionData::BranchTable { arg, table, .. } => {
                let table = &self.func.dfg.jump_tables[table];
                let ty = self.tyn(arg)?;
                let operand = self.op(arg);
                let (default, default_values) = self.edge(table.default_block())?;
                let mut seen: BTreeMap<Block, Vec<String>> = BTreeMap::new();
                seen.insert(default, default_values);
                let mut cases = String::new();
                for (index, call) in table.as_slice().iter().enumerate() {
                    let (target, values) = self.edge(*call)?;
                    if let Some(previous) = seen.get(&target) {
                        if *previous != values {
                            return Err("jump table passes different arguments to one block".into());
                        }
                    } else {
                        seen.insert(target, values);
                    }
                    let _ = write!(cases, " {ty} {index}, label %b{}", target.as_u32());
                }
                self.line(format!(
                    "switch {ty} {operand}, label %b{} [{cases} ]",
                    default.as_u32()
                ));
                for (target, values) in seen {
                    self.edges.push(Edge {
                        from: self.label.clone(),
                        target,
                        values,
                    });
                }
            }
            InstructionData::MultiAry { args, .. } if opcode == Opcode::Return => {
                let values = args.as_slice(&dfg.value_lists).to_vec();
                match values.as_slice() {
                    [] => self.line("ret void"),
                    [value] => {
                        let (ty, operand) = (self.tyn(*value)?, self.op(*value));
                        self.line(format!("ret {ty} {operand}"));
                    }
                    many => {
                        let ret = return_type(&self.func.signature)?;
                        let mut aggregate = "poison".to_owned();
                        for (index, value) in many.iter().enumerate() {
                            let (ty, operand) = (self.tyn(*value)?, self.op(*value));
                            let temp = self.temp();
                            self.line(format!(
                                "{temp} = insertvalue {ret} {aggregate}, {ty} {operand}, {index}"
                            ));
                            aggregate = temp;
                        }
                        self.line(format!("ret {ret} {aggregate}"));
                    }
                }
            }
            _ => return Err(format!("unsupported instruction {opcode}")),
        }
        Ok(())
    }
    fn reachable(&self) -> BTreeSet<Block> {
        let mut seen = BTreeSet::new();
        let Some(entry) = self.func.layout.entry_block() else {
            return seen;
        };
        let mut work = vec![entry];
        while let Some(block) = work.pop() {
            if !seen.insert(block) {
                continue;
            }
            if let Some(last) = self.func.layout.last_inst(block) {
                for call in self.func.dfg.insts[last]
                    .branch_destination(&self.func.dfg.jump_tables, &self.func.dfg.exception_tables)
                {
                    work.push(call.block(&self.func.dfg.value_lists));
                }
            }
        }
        seen
    }
    fn function(mut self, name: &str, linkage: Linkage) -> Tx<String> {
        let func = self.func;
        let entry = func.layout.entry_block().ok_or("function has no entry")?;
        let reachable = self.reachable();
        let mut bodies: Vec<(Block, String)> = Vec::new();
        for block in func.layout.blocks() {
            if !reachable.contains(&block) {
                continue;
            }
            self.body = String::new();
            self.label = format!("b{}", block.as_u32());
            if block == entry {
                for (slot, data) in func.sized_stack_slots.iter() {
                    let align = (1u64 << data.align_shift).max(8);
                    let _ = writeln!(
                        self.body,
                        "  %ss{} = alloca [{} x i8], align {align}",
                        slot.as_u32(),
                        data.size.max(1)
                    );
                }
            }
            for inst in func.layout.block_insts(block) {
                self.instruction(inst)?;
            }
            bodies.push((block, std::mem::take(&mut self.body)));
        }
        if self.edges.iter().any(|edge| edge.target == entry) {
            return Err("the entry block is a branch target".into());
        }
        let mut out = String::new();
        let ret = return_type(&func.signature)?;
        let mut params = Vec::new();
        for (value, param) in func
            .dfg
            .block_params(entry)
            .iter()
            .zip(&func.signature.params)
        {
            params.push(format!(
                "{}{} %v{}",
                ty_name(param.value_type)?,
                extension(param),
                value.as_u32()
            ));
        }
        let linkage = match linkage {
            Linkage::Local | Linkage::Hidden => "internal ",
            _ => "",
        };
        let _ = writeln!(
            out,
            "define {linkage}{ret} @{name}({}) #0 {{",
            params.join(", ")
        );
        for (block, body) in bodies {
            let _ = writeln!(out, "b{}:", block.as_u32());
            if block != entry {
                for (index, param) in func.dfg.block_params(block).iter().enumerate() {
                    let incoming = self
                        .edges
                        .iter()
                        .filter(|edge| edge.target == block)
                        .map(|edge| format!("[ {}, %{} ]", edge.values[index], edge.from))
                        .collect::<Vec<_>>();
                    let _ = writeln!(
                        out,
                        "  %v{} = phi {} {}",
                        param.as_u32(),
                        ty_name(func.dfg.value_type(*param))?,
                        incoming.join(", ")
                    );
                }
            }
            out.push_str(&body);
        }
        out.push_str("}\n");
        Ok(out)
    }
}

fn intrinsic_suffix(ty: &str) -> &str {
    match ty {
        "float" => "f32",
        "double" => "f64",
        other => other,
    }
}

/// Branch weights marking trap edges as never taken.
const MODULE_METADATA: &str = "!0 = !{!\"branch_weights\", i32 1, i32 2000000}\n";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_signatures_are_read_from_clang_output() {
        let interface = RuntimeInterface::parse(
            "target triple = \"x86_64-pc-linux-gnu\"\n\
             define dso_local noalias ptr @kush_grow(ptr noundef %0, i64 noundef %1) #3 {\n\
             define dso_local void @kush_panic() local_unnamed_addr #0 {\n\
             define internal fastcc i64 @helper(i64 %0) {\n\
             define dso_local i64 @kush_buffer_alloc(i64 noundef %0, i64 noundef %1, i32 noundef %2) {\n\
             define dso_local { i64, i64 } @pair(i64 %0) {\n",
        );
        assert_eq!(
            interface.header,
            "target triple = \"x86_64-pc-linux-gnu\"\n"
        );
        assert_eq!(
            interface.signatures["kush_grow"],
            CSignature {
                ret: Ty::Ptr,
                params: vec![Ty::Ptr, Ty::I64]
            }
        );
        assert_eq!(interface.signatures["kush_panic"].params, Vec::new());
        assert_eq!(
            interface.signatures["kush_buffer_alloc"].params,
            vec![Ty::I64, Ty::I64, Ty::I32]
        );
        assert!(!interface.signatures.contains_key("helper"));
        assert!(!interface.signatures.contains_key("pair"));
    }
}
