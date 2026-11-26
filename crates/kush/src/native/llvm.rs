//! LLVM release backend: the program's LLVM module.
//!
//! The checked executable IR is lowered exactly once, by `Generator`, through
//! the `Emit` trait. Under this backend the typed LLVM builder
//! (`llvm_builder.rs`) writes each function as textual LLVM IR; this module
//! collects those functions with the program's data, thunks and runtime
//! declarations into modules (split into partitions) that `clang` optimizes
//! together with the C runtime. Both backends therefore share every lowering
//! decision (evaluation order, checks, layouts, drops, task and handler
//! protocols); only instruction selection and optimization differ.
//!
//! No LLVM library is linked into the compiler and no `unsafe` is needed: the
//! output is a `.ll` file.
use super::Result;
use super::error;
use cranelift_codegen::ir::{self, types};
use cranelift_module::{DataId, FuncId, Linkage, ModuleDeclarations};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::rc::Rc;

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
    pub(super) fn name(self) -> &'static str {
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
    pub(super) fn of(ty: ir::Type) -> Option<Self> {
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
    pub(super) fn bits(self) -> u32 {
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

/// What the LLVM builder needs from the runtime's own LLVM IR: the target
/// description, and each exported function's real signature so calls match it
/// exactly (a call through a mismatched type is never inlined).
#[derive(Default, Debug)]
pub(super) struct RuntimeInterface {
    pub header: String,
    pub signatures: BTreeMap<String, CSignature>,
}
impl RuntimeInterface {
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
    if prefix
        .split_whitespace()
        .any(|word| word == "internal" || word == "hidden")
    {
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

/// The runtime's LLVM module, split for separate compilation.
pub(super) struct RuntimeSplit {
    /// The module to compile into the runtime object: unchanged, except that
    /// internal functions and variables are hidden instead, i.e. visible to
    /// the program object but not outside the executable.
    pub exported: String,
    /// The same module with every definition `available_externally`: LLVM may
    /// inline these bodies into the program and then discards them. State
    /// stays single because variables are `available_externally` too and
    /// resolve to the runtime object's.
    pub inlinable: String,
    /// The target description and every function signature line, which is
    /// all the LLVM builder needs to call the runtime with exact types.
    pub interface: String,
}

/// Runtime functions whose bodies LLVM may inline into program code: reads,
/// in-place writes and bookkeeping that never allocate, free or grow.
pub(super) const INLINABLE: [&str; 23] = [
    "kush_vec_len",
    "kush_vec_get",
    "kush_vec_set",
    "kush_vec_element",
    "kush_bytes_len",
    "kush_bytes_capacity",
    "kush_bytes_get",
    "kush_alloc_vec_len",
    "kush_alloc_vec_get",
    "kush_alloc_vec_data",
    "kush_alloc_block_data",
    "kush_alloc_box_payload",
    "kush_utf8_scalar_len",
    "kush_utf8_scalar_at",
    "kush_str_scalar_len",
    "kush_str_byte_at",
    "kush_str_scalar_at",
    "kush_float_from_int",
    "kush_float_to_int",
    "kush_float_int_present",
    "kush_int_exact_in_float",
    "kush_handler_depth",
    "kush_note_reuse",
];

/// Rewrite the linkage of each top-level definition of the runtime module.
/// Returns `None` for constructs the scheme does not cover (aliases, special
/// `@llvm.` variables, common storage), so the caller can report it instead
/// of producing a module that links but misbehaves. Thread-local variables
/// (the per-thread abort word and catch depth under `KUSH_HAS_THREADS`) split
/// like any other: the object defines each one, and program code that
/// inlined a runtime body reaches it through the ordinary TLS sequence.
pub(super) fn split_runtime(ir: &str) -> Option<RuntimeSplit> {
    let mut split = RuntimeSplit {
        exported: String::with_capacity(ir.len()),
        inlinable: String::with_capacity(ir.len() + ir.len() / 16),
        interface: String::new(),
    };
    for line in ir.lines() {
        let (exported, inlinable);
        if let Some(rest) = line.strip_prefix("define ") {
            // Only plain accessors may be inlined into program code. The
            // allocator in particular must stay an opaque call: the alias
            // facts the program module states (`noalias` parameters, memory
            // classes) are about objects, and a recycled block is a new
            // object only as long as LLVM cannot see through the recycling.
            let name = rest.split_once('@')?.1.split('(').next()?;
            let body = rest.strip_suffix('{')?;
            let opaque = if INLINABLE.contains(&name) {
                ""
            } else {
                "noinline "
            };
            (exported, inlinable) = match rest.strip_prefix("internal ") {
                Some(_) => (
                    format!("define hidden {}", &rest["internal ".len()..]),
                    format!(
                        "define available_externally hidden {}{opaque}{{",
                        &body["internal ".len()..]
                    ),
                ),
                None => (
                    line.to_owned(),
                    format!("define available_externally {body}{opaque}{{"),
                ),
            };
            split.interface.push_str(&exported);
            split.interface.push('\n');
        } else if line.starts_with('@')
            && let Some((name, rest)) = line.split_once(" = ")
        {
            let first = rest.split_whitespace().next()?;
            if name.starts_with("@llvm.")
                || matches!(
                    first,
                    "alias"
                        | "ifunc"
                        | "common"
                        | "weak"
                        | "weak_odr"
                        | "linkonce"
                        | "linkonce_odr"
                        | "appending"
                )
            {
                return None;
            }
            (exported, inlinable) = if let Some(rest) = rest.strip_prefix("internal ") {
                (
                    format!("{name} = hidden {rest}"),
                    format!("{name} = available_externally hidden {rest}"),
                )
            } else if matches!(first, "private" | "external" | "extern_weak") {
                (line.to_owned(), line.to_owned())
            } else {
                (
                    line.to_owned(),
                    format!("{name} = available_externally {rest}"),
                )
            };
        } else {
            if line.starts_with("target datalayout") || line.starts_with("target triple") {
                split.interface.push_str(line);
                split.interface.push('\n');
            }
            (exported, inlinable) = (line.to_owned(), line.to_owned());
        }
        split.exported.push_str(&exported);
        split.exported.push('\n');
        split.inlinable.push_str(&inlinable);
        split.inlinable.push('\n');
    }
    Some(split)
}

/// What kind of memory a load or store touches, when the generator knows.
/// Accesses of different classes never overlap: a buffer's header words
/// (length, capacity) are never an element of any buffer. The generator
/// records the class as the instruction's source location.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u32)]
pub(super) enum MemoryClass {
    BufferHeader = 1,
    BufferElements = 2,
}

/// A defined function whose address-taking callers need the plain word
/// signature: return type, parameter types with extensions, and which
/// parameters are exclusive pointers.
struct Typed {
    ret: String,
    params: Vec<String>,
    exclusive: Vec<bool>,
}

/// The program's LLVM module under construction.
pub(super) struct LlvmModule {
    runtime: Rc<RuntimeInterface>,
    /// Ownership facts: per function name, the parameters that are owning
    /// handles or exclusive borrows. They become `ptr noalias` parameters.
    exclusive: Rc<BTreeMap<String, Vec<usize>>>,
    typed: BTreeMap<String, Typed>,
    /// Functions whose address is taken; each gets a word-typed thunk.
    address_taken: BTreeSet<String>,
    /// Defined functions: name and text, in definition order.
    functions: Vec<(String, String)>,
    defined: BTreeSet<FuncId>,
    data: BTreeMap<DataId, Vec<u8>>,
    /// Per data object, the addresses stored in it, by byte offset.
    pointers: BTreeMap<DataId, Vec<(usize, DataPointer)>>,
    intrinsics: BTreeSet<String>,
}

/// An address written into a data object.
#[derive(Clone, Copy, Debug)]
pub(super) enum DataPointer {
    Function(FuncId),
    Data(DataId, i64),
}
impl LlvmModule {
    pub fn new(runtime: RuntimeInterface) -> Self {
        Self {
            runtime: Rc::new(runtime),
            exclusive: Rc::new(BTreeMap::new()),
            typed: BTreeMap::new(),
            address_taken: BTreeSet::new(),
            functions: Vec::new(),
            defined: BTreeSet::new(),
            data: BTreeMap::new(),
            pointers: BTreeMap::new(),
            intrinsics: BTreeSet::new(),
        }
    }
    /// Record which parameters of a function the program owns exclusively.
    /// Must be called before any function body is built.
    pub fn exclusive_parameters(&mut self, name: &str, parameters: Vec<usize>) {
        if !parameters.is_empty() {
            Rc::make_mut(&mut self.exclusive).insert(name.to_owned(), parameters);
        }
    }
    /// What the typed builder shares across bodies (FND-LLVM-BUILDER).
    pub fn shared(&self) -> super::llvm_builder::Shared {
        super::llvm_builder::Shared {
            runtime: self.runtime.clone(),
            exclusive: self.exclusive.clone(),
        }
    }
    /// Define a function from the typed builder's finished text.
    pub fn define_built(
        &mut self,
        id: FuncId,
        built: super::llvm_builder::LlvmBuilder,
        declarations: &ModuleDeclarations,
    ) -> Result<()> {
        let declaration = declarations.get_function_decl(id);
        let name = declaration.linkage_name(id).into_owned();
        let signature = &declaration.signature;
        self.intrinsics.extend(built.intrinsics.iter().cloned());
        self.address_taken
            .extend(built.address_taken.iter().cloned());
        let text = built
            .finish()
            .map_err(|message| error(format!("LLVM backend: in {name}: {message}")))?;
        self.record(id, name, signature, text)
    }
    fn record(
        &mut self,
        id: FuncId,
        name: String,
        signature: &ir::Signature,
        text: String,
    ) -> Result<()> {
        if let Some(exclusive) = self.exclusive.get(&name) {
            let (ret, params) = clif_signature(signature)
                .map_err(|message| error(format!("LLVM backend: {name}: {message}")))?;
            let exclusive = (0..params.len()).map(|i| exclusive.contains(&i)).collect();
            self.typed.insert(
                name.clone(),
                Typed {
                    ret,
                    params,
                    exclusive,
                },
            );
        }
        self.functions.push((name, text));
        self.defined.insert(id);
        Ok(())
    }
    /// Define a data object. Each pointer replaces the eight bytes at its
    /// offset with an address the linker fills in.
    pub fn define_data(
        &mut self,
        id: DataId,
        bytes: Vec<u8>,
        mut pointers: Vec<(usize, DataPointer)>,
    ) {
        if !pointers.is_empty() {
            pointers.sort_by_key(|(offset, _)| *offset);
            self.pointers.insert(id, pointers);
        }
        self.data.insert(id, bytes);
    }
    /// The LLVM initializer of a data object: its bytes, with each pointer
    /// as a `ptr` field of a packed struct.
    fn initializer(
        &self,
        id: DataId,
        bytes: &[u8],
        declarations: &ModuleDeclarations,
    ) -> (String, String) {
        fn array(bytes: &[u8]) -> (String, String) {
            let mut value = String::from("c\"");
            for byte in bytes {
                let _ = write!(value, "\\{byte:02X}");
            }
            value.push('"');
            (format!("[{} x i8]", bytes.len()), value)
        }
        let Some(pointers) = self.pointers.get(&id) else {
            return array(bytes);
        };
        let mut types = Vec::new();
        let mut values = Vec::new();
        let mut at = 0;
        for &(offset, pointer) in pointers {
            if offset > at {
                let (ty, value) = array(&bytes[at..offset]);
                values.push(format!("{ty} {value}"));
                types.push(ty);
            }
            let target = match pointer {
                DataPointer::Function(function) => format!(
                    "@{}",
                    declarations
                        .get_function_decl(function)
                        .linkage_name(function)
                ),
                DataPointer::Data(data, 0) => {
                    format!("@{}", declarations.get_data_decl(data).linkage_name(data))
                }
                DataPointer::Data(data, addend) => format!(
                    "getelementptr (i8, ptr @{}, i64 {addend})",
                    declarations.get_data_decl(data).linkage_name(data)
                ),
            };
            types.push("ptr".to_owned());
            values.push(format!("ptr {target}"));
            at = offset + 8;
        }
        if at < bytes.len() {
            let (ty, value) = array(&bytes[at..]);
            values.push(format!("{ty} {value}"));
            types.push(ty);
        }
        (
            format!("<{{ {} }}>", types.join(", ")),
            format!("<{{ {} }}>", values.join(", ")),
        )
    }
    /// The program as LLVM modules, each compiled on its own (see
    /// [`partition`] and [`super::Split`]). One partition is exactly the
    /// whole program.
    pub fn finish(
        self,
        declarations: &ModuleDeclarations,
        split: super::Split,
    ) -> Result<Vec<String>> {
        // Thunks are functions like any other: a function with pointer
        // parameters is reached through a function pointer by a thunk with
        // the plain word signature, so an indirect call always has exactly
        // the type of what it calls.
        let mut functions = self.functions.clone();
        for name in &self.address_taken {
            let Some(typed) = self.typed.get(name) else {
                continue;
            };
            functions.push((format!("{name}{WORD_THUNK}"), thunk(name, typed)));
        }
        let total: usize = functions.iter().map(|(_, text)| text.lines().count()).sum();
        let wanted = match total.checked_div(split.minimum) {
            Some(most) => split.cores.max(total.div_ceil(split.target)).min(most),
            None => split.cores,
        }
        .max(1);
        let mut plan = partition(&functions, wanted);
        // Data lives in the first partition. A function whose address it
        // holds is declared there and visible to the linker.
        if plan.count > 1 {
            let index_of: BTreeMap<&str, usize> = functions
                .iter()
                .enumerate()
                .map(|(index, (name, _))| (name.as_str(), index))
                .collect();
            for pointers in self.pointers.values() {
                for (_, pointer) in pointers {
                    let DataPointer::Function(function) = *pointer else {
                        continue;
                    };
                    let name = declarations
                        .get_function_decl(function)
                        .linkage_name(function);
                    if let Some(&index) = index_of.get(name.as_ref())
                        && plan.home[index] != 0
                    {
                        plan.exported.insert(index);
                        plan.declared[0].insert(index);
                    }
                }
            }
        }
        let mut modules = Vec::new();
        for part in 0..plan.count {
            modules.push(self.module(declarations, &functions, &plan, part)?);
        }
        Ok(modules)
    }
    /// One partition's module text.
    fn module(
        &self,
        declarations: &ModuleDeclarations,
        functions: &[(String, String)],
        plan: &Partitioning,
        part: usize,
    ) -> Result<String> {
        let split = plan.count > 1;
        let mut out = String::new();
        out.push_str("; Kush program module (LLVM release backend)\n");
        out.push_str(&self.runtime.header);
        out.push('\n');
        // Data lives in the first partition; the others refer to it.
        for (id, declaration) in declarations.get_data_objects() {
            let name = declaration.linkage_name(id);
            match self.data.get(&id) {
                Some(bytes) if split && part != 0 => {
                    let _ = writeln!(
                        out,
                        "@{name} = external hidden global [{} x i8], align 8",
                        bytes.len()
                    );
                }
                Some(bytes) => {
                    let linkage = match declaration.linkage {
                        Linkage::Local | Linkage::Hidden if split => "hidden ",
                        Linkage::Local | Linkage::Hidden => "internal ",
                        _ => "",
                    };
                    let kind = if declaration.writable {
                        "global"
                    } else {
                        "constant"
                    };
                    let (ty, value) = self.initializer(id, bytes, declarations);
                    let _ = writeln!(out, "@{name} = {linkage}{kind} {ty} {value}, align 8");
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
        // Functions defined in another partition and used here.
        for (index, (_, text)) in functions.iter().enumerate() {
            if plan.declared[part].contains(&index) {
                let _ = writeln!(out, "{}", declaration_of(text));
            }
        }
        for intrinsic in &self.intrinsics {
            out.push_str(intrinsic);
            out.push('\n');
        }
        out.push('\n');
        for (index, (_, text)) in functions.iter().enumerate() {
            let text = if plan.home[index] == part {
                if plan.exported.contains(&index) {
                    // Called from another partition: visible to the linker,
                    // but not outside the program.
                    text.replacen("define internal ", "define hidden ", 1)
                } else {
                    text.clone()
                }
            } else if plan.copied[part].contains(&index) {
                // A small function used here and defined elsewhere: a copy
                // LLVM may inline, never emitted.
                text.replacen("define internal ", "define available_externally ", 1)
            } else {
                continue;
            };
            out.push_str(&text);
            out.push('\n');
        }
        // Probe every page of a large frame so it cannot step over the
        // guard below the stack (see the runtime's fault handler).
        // And keep every call a call: turning a recursion into a loop would
        // make the depth a program can reach, and whether a runaway
        // recursion panics or spins, depend on the backend.
        out.push_str(
            "attributes #0 = { nounwind \"probe-stack\"=\"inline-asm\" \"disable-tail-calls\"=\"true\" }\n",
        );
        out.push_str(MODULE_METADATA);
        Ok(out)
    }
}

/// The word-signature thunk of a function with pointer parameters.
fn thunk(name: &str, typed: &Typed) -> String {
    let mut out = String::new();
    let params = typed
        .params
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("{ty} %a{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        out,
        "define internal {} @{name}{WORD_THUNK}({params}) #0 {{",
        typed.ret
    );
    let mut arguments = Vec::new();
    for (index, ty) in typed.params.iter().enumerate() {
        if typed.exclusive[index] {
            let _ = writeln!(out, "  %p{index} = inttoptr i64 %a{index} to ptr");
            arguments.push(format!("ptr %p{index}"));
        } else {
            arguments.push(format!("{ty} %a{index}"));
        }
    }
    let arguments = arguments.join(", ");
    if typed.ret == "void" {
        let _ = writeln!(out, "  tail call void @{name}({arguments})\n  ret void\n}}");
    } else {
        let _ = writeln!(
            out,
            "  %r = tail call {ret} @{name}({arguments})\n  ret {ret} %r\n}}",
            ret = typed.ret
        );
    }
    out
}

/// `declare hidden RET @name(TYPES)` for a function whose text starts
/// `define LINKAGE RET @name(TYPE %v, ...) #0 {`.
fn declaration_of(text: &str) -> String {
    let header = text.lines().next().unwrap_or_default();
    let header = header
        .strip_prefix("define ")
        .unwrap_or(header)
        .trim_start_matches("internal ")
        .trim_start_matches("hidden ");
    let open = header.find('(').unwrap_or(header.len());
    let close = header.rfind(')').unwrap_or(header.len());
    let params = header[open + 1..close]
        .split(", ")
        .filter(|param| !param.is_empty())
        .map(|param| match param.rfind(" %") {
            Some(at) => &param[..at],
            None => param,
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("declare hidden {}({params})", &header[..open])
}

/// Where each function of a split program goes.
struct Partitioning {
    count: usize,
    /// The partition each function is defined in.
    home: Vec<usize>,
    /// Functions defined in one partition and called from another.
    exported: BTreeSet<usize>,
    /// Per partition, small functions defined elsewhere that it gets a copy
    /// of for inlining.
    copied: Vec<BTreeSet<usize>>,
    /// Per partition, functions defined elsewhere that it refers to.
    declared: Vec<BTreeSet<usize>>,
}

/// A function at most this many lines is copied into every partition that
/// calls it, as C++ inline functions are, so splitting the program does not
/// stop LLVM from inlining it.
const SHARED_SMALL: usize = 80;

/// Split the program's functions into at most `wanted` partitions that LLVM
/// can optimize and compile in parallel, losing as little inlining as it
/// can. A function with one caller joins its caller's group, where LLVM
/// would have inlined it, until a group reaches a share of the program; a
/// small function with several callers is copied into each partition that
/// calls it (see [`SHARED_SMALL`]). Groups are then packed into partitions
/// of about equal size. Deterministic: the same program splits the same way.
fn partition(functions: &[(String, String)], wanted: usize) -> Partitioning {
    let count = functions.len();
    let index: BTreeMap<&str, usize> = functions
        .iter()
        .enumerate()
        .map(|(at, (name, _))| (name.as_str(), at))
        .collect();
    let sizes: Vec<usize> = functions
        .iter()
        .map(|(_, text)| text.lines().count().max(1))
        .collect();
    // Which defined functions each function refers to (calls, addresses).
    let references: Vec<BTreeSet<usize>> = functions
        .iter()
        .enumerate()
        .map(|(at, (_, text))| {
            let mut found = BTreeSet::new();
            let bytes = text.as_bytes();
            let mut position = 0;
            while let Some(offset) = text[position..].find('@') {
                let start = position + offset + 1;
                let mut end = start;
                while end < bytes.len()
                    && (bytes[end].is_ascii_alphanumeric()
                        || matches!(bytes[end], b'_' | b'.' | b'$'))
                {
                    end += 1;
                }
                if let Some(&callee) = index.get(&text[start..end])
                    && callee != at
                {
                    found.insert(callee);
                }
                position = end.max(start);
            }
            found
        })
        .collect();
    if wanted <= 1 || count <= 1 {
        return Partitioning {
            count: 1,
            home: vec![0; count],
            exported: BTreeSet::new(),
            copied: vec![BTreeSet::new()],
            declared: vec![BTreeSet::new()],
        };
    }
    let mut callers: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
    for (caller, callees) in references.iter().enumerate() {
        for callee in callees {
            callers[*callee].insert(caller);
        }
    }
    let total: usize = sizes.iter().sum();
    let cap = (total / (wanted * 2)).max(1);
    // Union-find over groups, with each group's size.
    let mut parent: Vec<usize> = (0..count).collect();
    let mut group_size = sizes.clone();
    fn root(parent: &mut [usize], mut at: usize) -> usize {
        while parent[at] != at {
            parent[at] = parent[parent[at]];
            at = parent[at];
        }
        at
    }
    let mut order: Vec<usize> = (0..count).collect();
    order.sort_by_key(|at| (sizes[*at], *at));
    for callee in order {
        let [caller] = callers[callee].iter().copied().collect::<Vec<_>>()[..] else {
            continue;
        };
        let (a, b) = (root(&mut parent, caller), root(&mut parent, callee));
        if a != b && group_size[a] + group_size[b] <= cap {
            parent[b] = a;
            group_size[a] += group_size[b];
        }
    }
    // Pack groups, largest first, into the lightest partition.
    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for at in 0..count {
        let group = root(&mut parent, at);
        groups.entry(group).or_default().push(at);
    }
    let mut groups: Vec<(usize, Vec<usize>)> = groups
        .into_values()
        .map(|members| (members.iter().map(|at| sizes[*at]).sum(), members))
        .collect();
    groups.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(&right.1)));
    let mut loads = vec![0usize; wanted];
    let mut home = vec![0; count];
    for (size, members) in groups {
        let lightest = (0..wanted)
            .min_by_key(|part| (loads[*part], *part))
            .unwrap_or(0);
        loads[lightest] += size;
        for at in members {
            home[at] = lightest;
        }
    }
    // Number the partitions that received anything, in order.
    let mut used: Vec<usize> = home.clone();
    used.sort_unstable();
    used.dedup();
    for at in home.iter_mut() {
        *at = used.binary_search(at).unwrap_or(0);
    }
    let parts = used.len();
    let mut copied = vec![BTreeSet::new(); parts];
    let mut declared = vec![BTreeSet::new(); parts];
    let mut exported = BTreeSet::new();
    for (caller, callees) in references.iter().enumerate() {
        for callee in callees {
            let part = home[caller];
            if home[*callee] == part {
                continue;
            }
            exported.insert(*callee);
            if sizes[*callee] <= SHARED_SMALL && callers[*callee].len() > 1 {
                copied[part].insert(*callee);
            } else {
                declared[part].insert(*callee);
            }
        }
    }
    // A copy's own references must be visible where it is copied.
    for part in 0..parts {
        let copies: Vec<usize> = copied[part].iter().copied().collect();
        for copy in copies {
            for callee in &references[copy] {
                if home[*callee] != part && !copied[part].contains(callee) {
                    exported.insert(*callee);
                    declared[part].insert(*callee);
                }
            }
        }
    }
    Partitioning {
        count: parts,
        home,
        exported,
        copied,
        declared,
    }
}

type Tx<T> = std::result::Result<T, String>;

/// Lane count and LLVM lane type of a 128-bit vector type.
pub(super) fn lanes(ty: ir::Type) -> Option<(u32, &'static str)> {
    match ty {
        types::I8X16 => Some((16, "i8")),
        types::I16X8 => Some((8, "i16")),
        types::I32X4 => Some((4, "i32")),
        types::I64X2 => Some((2, "i64")),
        _ => None,
    }
}
/// A vector constant with `value` in every lane.
pub(super) fn splat_constant(ty: ir::Type, value: &str) -> Option<String> {
    let (count, lane) = lanes(ty)?;
    let items = (0..count)
        .map(|_| format!("{lane} {value}"))
        .collect::<Vec<_>>();
    Some(format!("<{}>", items.join(", ")))
}

pub(super) fn ty_name(ty: ir::Type) -> Tx<&'static str> {
    // SIMD-LLVM: the 128-bit vectors of std.simd's native lowering.
    match ty {
        types::I8X16 => return Ok("<16 x i8>"),
        types::I16X8 => return Ok("<8 x i16>"),
        types::I32X4 => return Ok("<4 x i32>"),
        types::I64X2 => return Ok("<2 x i64>"),
        _ => {}
    }
    Ty::of(ty)
        .map(Ty::name)
        .ok_or_else(|| format!("unsupported value type {ty}"))
}
pub(super) fn extension(param: &ir::AbiParam) -> &'static str {
    match param.extension {
        ir::ArgumentExtension::Uext => " zeroext",
        ir::ArgumentExtension::Sext => " signext",
        ir::ArgumentExtension::None => "",
    }
}
pub(super) fn return_type(signature: &ir::Signature) -> Tx<String> {
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

/// Remove `%vN = zext i1 ...` lines whose value is never used: flags reach
/// branches and logic as `i1`, so most widened copies are dead. Nothing else
/// is removed, and a zext has no effects.
pub(super) fn drop_unused_flags(text: String) -> String {
    let mut uses: BTreeMap<&str, usize> = BTreeMap::new();
    let bytes = text.as_bytes();
    let mut at = 0;
    while let Some(found) = text[at..].find("%v") {
        let start = at + found;
        let mut end = start + 2;
        while end < bytes.len() && bytes[end].is_ascii_digit() {
            end += 1;
        }
        let whole = end > start + 2
            && !(end < bytes.len() && (bytes[end] == b'.' || bytes[end].is_ascii_alphanumeric()));
        if whole {
            *uses.entry(&text[start..end]).or_default() += 1;
        }
        at = end.max(start + 2);
    }
    let dead = |line: &str| {
        let Some(rest) = line.strip_prefix("  %v") else {
            return false;
        };
        let Some((name, definition)) = rest.split_once(" = ") else {
            return false;
        };
        definition.starts_with("zext i1 ")
            && name.bytes().all(|byte| byte.is_ascii_digit())
            && uses.get(&line[2..4 + name.len()]) == Some(&1)
    };
    if !text.lines().any(dead) {
        return text;
    }
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        if !dead(line) {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

pub(super) fn intrinsic_suffix(ty: &str) -> &str {
    match ty {
        "float" => "f32",
        "double" => "f64",
        other => other,
    }
}

/// Branch weights marking trap edges as never taken, then type-based alias
/// tags for [`MemoryClass`]: a root of their own (so they say nothing about
/// the C runtime's accesses), one scalar type per class, and one access tag
/// per type (`!4` header, `!5` elements).
const MODULE_METADATA: &str = "!0 = !{!\"branch_weights\", i32 1, i32 2000000}\n\
!1 = !{!\"kush memory classes\"}\n\
!2 = !{!\"buffer header\", !1, i64 0}\n\
!3 = !{!\"buffer elements\", !1, i64 0}\n\
!4 = !{!2, !2, i64 0}\n\
!5 = !{!3, !3, i64 0}\n";

/// Suffix of the word-signature thunk of a function with pointer parameters.
pub(super) const WORD_THUNK: &str = ".words";

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

    #[test]
    fn widened_flags_nothing_reads_are_dropped() {
        let text = [
            "define i64 @f(i64 %v0) {",
            "b0:",
            "  %t1 = icmp slt i64 %v0, 0",
            "  %v1 = zext i1 %t1 to i8",
            "  %t2 = icmp sgt i64 %v0, 9",
            "  %v2 = zext i1 %t2 to i64",
            "  %v12 = zext i1 %t1 to i64",
            "  br i1 %t1, label %b1, label %b2",
            "b1:",
            "  ret i64 %v2",
            "b2:",
            "  ret i64 0",
            "}",
            "",
        ]
        .join("\n");
        let kept = drop_unused_flags(text);
        // `%v1` and `%v12` are read nowhere; `%v2` is returned. `%v1` is not
        // mistaken for a use of `%v12`'s prefix, nor the other way round.
        assert!(!kept.contains("%v1 = "), "{kept}");
        assert!(!kept.contains("%v12 = "), "{kept}");
        assert!(kept.contains("%v2 = zext i1 %t2 to i64"), "{kept}");
        assert!(kept.contains("icmp slt"), "{kept}");
    }

    #[test]
    fn the_runtime_module_splits_into_an_object_and_inlinable_bodies() {
        let split = split_runtime(
            "target triple = \"x86_64-pc-linux-gnu\"\n\
             @.str = private unnamed_addr constant [2 x i8] c\"a\\00\", align 1\n\
             @kush_pool = internal unnamed_addr global i64 0, align 8\n\
             @kush_abort_word = local_unnamed_addr global i64 0, align 8\n\
             @environ = external local_unnamed_addr global ptr, align 8\n\
             define internal fastcc void @kush_claim(i64 %0) unnamed_addr #1 {\n\
             }\n\
             define i64 @kush_alloc(i64 noundef %0) local_unnamed_addr #2 {\n\
             }\n\
             define i64 @kush_vec_len(i64 noundef %0) local_unnamed_addr #2 {\n\
             }\n",
        )
        .unwrap();
        // The object exports former internals as hidden symbols.
        assert!(
            split
                .exported
                .contains("@kush_pool = hidden unnamed_addr global i64 0")
        );
        assert!(
            split
                .exported
                .contains("define hidden fastcc void @kush_claim(i64 %0)")
        );
        assert!(split.exported.contains("\ndefine i64 @kush_alloc("));
        // The inlinable copy defines nothing for real, shares all state, and
        // keeps the allocator opaque.
        assert!(
            split
                .inlinable
                .contains("@kush_pool = available_externally hidden unnamed_addr global i64 0")
        );
        assert!(
            split.inlinable.contains(
                "@kush_abort_word = available_externally local_unnamed_addr global i64 0"
            )
        );
        assert!(
            split
                .inlinable
                .contains("@.str = private unnamed_addr constant")
        );
        assert!(
            split
                .inlinable
                .contains("@environ = external local_unnamed_addr")
        );
        assert!(split.inlinable.contains(
            "define available_externally hidden fastcc void @kush_claim(i64 %0) unnamed_addr #1 noinline {"
        ));
        assert!(split.inlinable.contains(
            "define available_externally i64 @kush_alloc(i64 noundef %0) local_unnamed_addr #2 noinline {"
        ));
        assert!(split.inlinable.contains(
            "define available_externally i64 @kush_vec_len(i64 noundef %0) local_unnamed_addr #2 {"
        ));
        let interface = RuntimeInterface::parse(&split.interface);
        assert!(interface.signatures.contains_key("kush_alloc"));
        assert!(!interface.signatures.contains_key("kush_claim"));
        // Constructs the scheme does not cover are refused, not guessed.
        assert!(split_runtime("@a = alias i64, ptr @b\n").is_none());
        let tls = split_runtime("@t = internal thread_local global i64 0, align 8\n").unwrap();
        assert!(
            tls.exported
                .contains("@t = hidden thread_local global i64 0")
        );
        assert!(
            tls.inlinable
                .contains("@t = available_externally hidden thread_local global i64 0")
        );
        assert!(split_runtime("@llvm.used = appending global [1 x ptr] [ptr @a]\n").is_none());
    }
}
