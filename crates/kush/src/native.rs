//! Cranelift AOT code generation for the checked scalar IR. The C shim only
//! supplies process entry, standard-stream I/O, allocation, byte operations, and abort;
//! user functions are CLIF.
use crate::float::FloatKind;
use crate::grades::Grade;
use crate::int::IntKind;
use crate::{
    Diagnostic, Span,
    executable::{
        self as ex, AllocVecOp, BytesOp, Coercion, DynArrayOp, Executable, Expr, ExprKind, HostOp,
        IoOp, Pattern, ReceiverMode, SliceOp, StrOp, StringOp, Target, Type, VecOp,
    },
    lexer::Kind,
};
use cranelift_codegen::{
    ir::{
        self, AbiParam, InstBuilder, TrapCode, Value, condcodes::FloatCC, condcodes::IntCC,
        types::I64,
    },
    settings::{self, Configurable},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

mod deferred;
mod from_mir;
mod llvm;
mod runtime_cache;
mod staging;
/// Every native stack slot is word aligned (`1 << 3` bytes). References to
/// locals point into these slots, so with the runtime's allocation contract
/// (`KUSH_POINTER_ALIGN` in the C runtime) every `Box`, `&T` and `&mut T` is a
/// nonzero multiple of 8. Pointer niches (unboxing-certificates.md section 6)
/// rely on this; change it only together with the certificate value sets.
pub(crate) const STACK_SLOT_ALIGN_SHIFT: u8 = 3;
/// The pointer alignment every native allocation path and stack reference
/// guarantees, in bytes.
pub(crate) const POINTER_ALIGN: u64 = 1 << STACK_SLOT_ALIGN_SHIFT;
/// The Cranelift comparison for a certificate decoder.
fn decoder_test(decoder: crate::layout_cert::Decoder) -> (IntCC, i64) {
    match decoder {
        crate::layout_cert::Decoder::Equal(constant) => (IntCC::Equal, constant),
        crate::layout_cert::Decoder::NotEqual(constant) => (IntCC::NotEqual, constant),
    }
}

type Result<T> = std::result::Result<T, Diagnostic>;
fn error(message: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::new(Span::default(), message.to_string())
}
/// The C runtime linked into every native executable (FND-RUNTIME-C).
const RUNTIME: &str = include_str!("../runtime/kush.c");

/// The vector locals a loop touches through `v = Vec.push(v, e)` and
/// read-only length or element reads alone, so that nothing else in the loop
/// can change their length or capacity. Loops containing an expression kind
/// this does not know the shape of yield nothing.
fn push_only_vectors(condition: &Expr, body: &ex::Block) -> Vec<usize> {
    #[derive(Default)]
    struct Uses {
        pushed: std::collections::BTreeSet<usize>,
        /// Mentioned some other way, or declared inside the loop.
        other: std::collections::BTreeSet<usize>,
        unknown: bool,
    }
    fn slot_of(expr: &Expr) -> Option<usize> {
        match expr.kind {
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Peek(slot) => Some(slot),
            _ => None,
        }
    }
    fn block(block: &ex::Block, uses: &mut Uses) {
        for statement in &block.statements {
            match statement {
                ex::Statement::Let(slot, value) => {
                    uses.other.insert(*slot);
                    expr(value, uses);
                }
                ex::Statement::Expr(value) => expr(value, uses),
                ex::Statement::Declare(slot) => {
                    uses.other.insert(*slot);
                }
            }
        }
        if let Some(tail) = &block.tail {
            expr(tail, uses);
        }
    }
    fn expr(e: &Expr, uses: &mut Uses) {
        match &e.kind {
            ExprKind::Constant(_) => {}
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Peek(slot) => {
                uses.other.insert(*slot);
            }
            ExprKind::Assign(slot, value) => {
                if let ExprKind::Call(Target::Vec(VecOp::Push, _), arguments) = &value.kind
                    && let [vector, item] = arguments.as_slice()
                    && matches!(vector.kind, ExprKind::Move(moved) | ExprKind::Local(moved) if moved == *slot)
                {
                    uses.pushed.insert(*slot);
                    expr(item, uses);
                } else {
                    uses.other.insert(*slot);
                    expr(value, uses);
                }
            }
            ExprKind::Call(target, arguments) => {
                let reads = matches!(target, Target::Vec(VecOp::Len | VecOp::Get, _));
                for (index, argument) in arguments.iter().enumerate() {
                    if reads && index == 0 && slot_of(argument).is_some() {
                        continue;
                    }
                    expr(argument, uses);
                }
            }
            ExprKind::Unary(_, operand) => expr(operand, uses),
            ExprKind::Binary(_, left, right) => {
                expr(left, uses);
                expr(right, uses);
            }
            ExprKind::If(test, then_block, else_block) => {
                expr(test, uses);
                block(then_block, uses);
                block(else_block, uses);
            }
            ExprKind::Block(inner) => block(inner, uses),
            ExprKind::While(test, inner) => {
                expr(test, uses);
                block(inner, uses);
            }
            ExprKind::Break(None, _) | ExprKind::Continue(_) => {}
            _ => uses.unknown = true,
        }
    }
    let mut uses = Uses::default();
    expr(condition, &mut uses);
    block(body, &mut uses);
    if uses.unknown {
        return Vec::new();
    }
    uses.pushed.difference(&uses.other).copied().collect()
}

/// Extra inputs for the native link step. Every path is passed to `cc` as one
/// argument (no shell interpolation); library names are validated identifiers
/// for `cc -l<name>`.
///
/// The compiler never invents search paths. Explicit Cargo adapters may resolve
/// their declared dependencies through Cargo. A project
/// manifest should turn its declared native dependencies into one of these
/// values and pass it to [`build_with_options`].
#[derive(Debug, Clone, Default)]
pub struct LinkSpec {
    /// Additional object files or static archives, linked before libraries.
    pub objects: Vec<PathBuf>,
    /// Static/shared libraries by absolute or caller-relative path.
    pub libraries: Vec<PathBuf>,
    /// Additional `-L` search directories.
    pub library_dirs: Vec<PathBuf>,
    /// Additional `-l` names (for example `pthread`), each a bare identifier.
    pub system_libraries: Vec<String>,
}
impl LinkSpec {
    /// Validate link inputs without touching the filesystem. Paths may not be
    /// empty and library names cannot smuggle flags or shell syntax.
    pub fn validate(&self) -> Result<()> {
        for path in self.objects.iter().chain(&self.libraries) {
            if path.as_os_str().is_empty() {
                return Err(error("a native link input path must not be empty"));
            }
            if path.to_string_lossy().starts_with(['-', '@']) {
                return Err(error(format!(
                    "native link input '{}' must not start with '-' or '@'; write an explicit path",
                    path.display()
                )));
            }
        }
        for path in &self.library_dirs {
            if path.as_os_str().is_empty() {
                return Err(error("a native library search directory must not be empty"));
            }
        }
        for name in &self.system_libraries {
            let valid = !name.is_empty()
                && !name.starts_with('-')
                && name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '+' | '.'));
            if !valid {
                return Err(error(format!(
                    "native library name '{name}' must be a bare -l name without flags or path separators"
                )));
            }
        }
        Ok(())
    }
    /// Map the reserved project manifest fields to concrete link inputs.
    ///
    /// * `libraries` entries that look like a path (contain a separator or end
    ///   in `.a`/`.o`/`.so`/`.dylib`) become explicit paths, resolved against
    ///   `root` when relative. Other entries are bare `-l` names.
    /// * `library_paths` become `-L` directories.
    /// * every `cargo_manifests` entry is built as a release static library
    ///   with `cargo build --release --lib --message-format=json`; the emitted
    ///   `.a` is linked explicitly. Rust std static libraries also need
    ///   `pthread` and `dl` on the Linux backend, so those are added once.
    ///
    /// This is deliberately a pure mapping/validation step plus the explicit
    /// Cargo subprocess for manifests the project author opted into. It never
    /// searches the host for libraries, downloads crates implicitly, or shells
    /// out through a command string.
    pub fn from_project_native(
        root: &Path,
        libraries: &[String],
        library_paths: &[PathBuf],
        cargo_manifests: &[PathBuf],
    ) -> Result<Self> {
        let mut spec = Self {
            library_dirs: library_paths.to_vec(),
            ..Self::default()
        };
        for library in libraries {
            if library.is_empty() || library.contains('\0') {
                return Err(error("a native library entry must not be empty"));
            }
            if library.starts_with('-') {
                return Err(error(format!(
                    "native library entry '{library}' must not start with '-'; write a bare name or an explicit path"
                )));
            }
            let path_like = library.contains('/')
                || library.contains('\\')
                || library.ends_with(".a")
                || library.ends_with(".o")
                || library.ends_with(".so")
                || library.contains(".so.")
                || library.ends_with(".dylib");
            if path_like {
                let path = Path::new(library);
                if path.is_absolute()
                    || path
                        .components()
                        .any(|part| matches!(part, std::path::Component::ParentDir))
                {
                    return Err(error(
                        "native library paths must be relative to their package and may not contain '..'",
                    ));
                }
                spec.libraries.push(root.join(library));
            } else {
                spec.system_libraries.push(library.clone());
            }
        }
        for manifest in cargo_manifests {
            spec.libraries.push(build_cargo_static_library(manifest)?);
            for library in ["pthread", "dl"] {
                if !spec.system_libraries.iter().any(|name| name == library) {
                    spec.system_libraries.push(library.to_owned());
                }
            }
        }
        spec.validate()?;
        Ok(spec)
    }
}

/// Build one Cargo adapter crate as a release static library and return the
/// emitted `.a` path. The manifest must set `crate-type = ["staticlib"]`.
/// Cargo's JSON artifact stream is the source of truth, so workspaces and custom
/// target directories work without guessing paths.
pub fn build_cargo_static_library(manifest: &Path) -> Result<PathBuf> {
    let manifest = manifest.canonicalize().map_err(error)?;
    let adapter_target = manifest
        .parent()
        .expect("manifest parent")
        .join("target/kush-adapter");
    let output = Command::new("cargo")
        // Adapter Cargo outputs must never overwrite mbx's read-only compiler cache.
        .env("CARGO_TARGET_DIR", adapter_target)
        .arg("build")
        .arg("--jobs")
        .arg("2")
        .arg("--release")
        .arg("--lib")
        .arg("--message-format=json")
        .arg("--manifest-path")
        .arg(&manifest)
        .output()
        .map_err(|e| {
            error(format!(
                "cannot start cargo for '{}': {e}",
                manifest.display()
            ))
        })?;
    if !output.status.success() {
        return Err(error(format!(
            "cargo build failed for native adapter '{}': {}",
            manifest.display(),
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        let Ok(message) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if message["reason"] != "compiler-artifact" {
            continue;
        }
        let Some(path) = message["manifest_path"].as_str() else {
            continue;
        };
        if Path::new(path) != manifest {
            continue;
        }
        if !message["target"]["crate_types"]
            .as_array()
            .is_some_and(|types| types.iter().any(|ty| ty == "staticlib"))
        {
            continue;
        }
        if let Some(archive) = message["filenames"].as_array().and_then(|files| {
            files
                .iter()
                .filter_map(|file| file.as_str())
                .find(|file| Path::new(file).extension().is_some_and(|ext| ext == "a"))
        }) {
            return Ok(PathBuf::from(archive));
        }
    }
    Err(error(format!(
        "native adapter '{}' did not emit a static library; set `crate-type = [\"staticlib\"]` in its [lib] section",
        manifest.display()
    )))
}

/// Compile and link atomically in the output's directory. No shell expansion or
/// user-supplied flags; a failed build leaves the previous output intact.
/// Native optimization controls. Defaults preserve the existing fast-build path.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Optimization {
    #[default]
    None,
    Speed,
}

/// Which code generator consumes the lowered program. Both receive the same
/// verified Cranelift IR from the one lowering in this module.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Backend {
    /// Cranelift machine code: fast builds, the default.
    #[default]
    Cranelift,
    /// LLVM IR optimized by `clang`, with runtime accessors inlined into
    /// user code: slower builds, fastest programs. Requires `clang`;
    /// `llvm-link` from the same LLVM enables the inlining.
    Llvm,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CodegenOptions {
    pub optimization: Optimization,
    pub inline_scalar_callbacks: bool,
    /// NATIVE-INLINE: inline small, non-recursive direct calls between Kush
    /// functions (Cranelift's library inliner).
    pub inline_calls: bool,
    pub backend: Backend,
    /// Defer overflow panics of side-effect-free loop arithmetic to the end
    /// of a bounded chunk of iterations so LLVM can vectorize it. Observable
    /// behaviour is unchanged: the program still panics exactly when checked
    /// arithmetic would. `None` follows the backend: on for LLVM, off for
    /// Cranelift.
    pub deferred_overflow: Option<bool>,
    /// Use the build machine's CPU features: `-march=native` on LLVM, and the
    /// host's ISA flags on Cranelift (SIMD-CRANELIFT-FEATURES). The program
    /// then needs a CPU with the same features.
    pub native_cpu: bool,
    /// PROOF-FUZZ: instrument every obligation site (a run-time check the
    /// prover left in place) for `kush fuzz`; see docs/proof-fuzz.md.
    /// Cranelift only. Turns deferred overflow off, so a check fails where
    /// it is written.
    pub fuzz: bool,
    /// FND-MIR: lower each function the CFG IR covers from its MIR body
    /// instead of the checked tree (`KUSH_MIR=1`).
    pub mir: bool,
}
impl CodegenOptions {
    /// Cranelift with explicit, independent controls.
    pub const fn cranelift(optimization: Optimization, inline_scalar_callbacks: bool) -> Self {
        Self {
            optimization,
            inline_scalar_callbacks,
            backend: Backend::Cranelift,
            deferred_overflow: None,
            native_cpu: false,
            inline_calls: false,
            fuzz: false,
            mir: false,
        }
    }
    pub const fn release() -> Self {
        Self {
            optimization: Optimization::Speed,
            inline_scalar_callbacks: true,
            backend: Backend::Cranelift,
            deferred_overflow: None,
            native_cpu: false,
            inline_calls: true,
            fuzz: false,
            mir: false,
        }
    }
    /// `KUSH_BACKEND=llvm|cranelift` overrides the backend of every native
    /// build in this process, so an entire test suite can be replayed on the
    /// other backend without changing its sources.
    fn with_environment(mut self) -> Result<Self> {
        match std::env::var("KUSH_BACKEND").ok().as_deref() {
            None | Some("") => {}
            Some("cranelift") => self.backend = Backend::Cranelift,
            Some("llvm") => self.backend = Backend::Llvm,
            // Also at release settings, whatever the build asked for.
            Some("llvm-release") => {
                self.backend = Backend::Llvm;
                self.optimization = Optimization::Speed;
                self.inline_scalar_callbacks = true;
            }
            Some(other) => {
                return Err(error(format!(
                    "KUSH_BACKEND must be 'cranelift', 'llvm' or 'llvm-release', not '{other}'"
                )));
            }
        }
        // FND-MIR: replay any native build through the CFG IR.
        match std::env::var("KUSH_MIR").ok().as_deref() {
            None | Some("" | "0") => {}
            Some("1") => self.mir = true,
            Some(other) => {
                return Err(error(format!("KUSH_MIR must be '0' or '1', not '{other}'")));
            }
        }
        Ok(self)
    }
    /// Whether loops are lowered with deferred overflow checks.
    fn defers_overflow(self) -> bool {
        !self.fuzz
            && self
                .deferred_overflow
                .unwrap_or(self.backend == Backend::Llvm)
    }
    /// The backend a build with these options uses, for messages. Honours
    /// the `KUSH_BACKEND` override.
    pub fn backend_name(self) -> &'static str {
        match self.with_environment().map(|options| options.backend) {
            Ok(Backend::Llvm) => "LLVM",
            _ => "Cranelift",
        }
    }
    /// Whether generated code may assume a native 64-bit vector multiply:
    /// only when tuning for this machine and it has AVX-512DQ.
    fn wide_multiply(self) -> bool {
        #[cfg(target_arch = "x86_64")]
        {
            self.native_cpu && std::arch::is_x86_feature_detected!("avx512dq")
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            false
        }
    }
    /// Release settings on the LLVM backend.
    pub const fn release_llvm() -> Self {
        Self {
            optimization: Optimization::Speed,
            inline_scalar_callbacks: true,
            backend: Backend::Llvm,
            deferred_overflow: None,
            native_cpu: false,
            // NATIVE-INLINE is a Cranelift pass; clang inlines for LLVM.
            inline_calls: false,
            fuzz: false,
            mir: false,
        }
    }
}

/// Largest callee (in CLIF instructions) that NATIVE-INLINE copies into a
/// caller, and how many calls one caller may absorb.
const INLINE_CALLEE_LIMIT: usize = 96;
const INLINE_CALLS_PER_CALLER: usize = 64;

/// Directs Cranelift's inliner: a direct call to another Kush function whose
/// body is small and does not call itself is replaced by that body.
struct Inliner<'a> {
    /// Cranelift function id (as `u32`) to Kush function index.
    by_id: &'a std::collections::HashMap<u32, usize>,
    bodies: &'a [Option<ir::Function>],
    caller: usize,
    budget: usize,
}
impl cranelift_codegen::inline::Inline for Inliner<'_> {
    fn inline(
        &mut self,
        caller: &ir::Function,
        _call_inst: ir::Inst,
        call_opcode: ir::Opcode,
        callee: ir::FuncRef,
        _call_args: &[ir::Value],
    ) -> cranelift_codegen::inline::InlineCommand<'_> {
        use cranelift_codegen::inline::InlineCommand;
        if call_opcode != ir::Opcode::Call || self.budget == 0 {
            return InlineCommand::KeepCall;
        }
        let Some(index) = callee_index(caller, callee, self.by_id) else {
            return InlineCommand::KeepCall;
        };
        if index == self.caller {
            return InlineCommand::KeepCall;
        }
        match self.bodies.get(index).and_then(Option::as_ref) {
            Some(body) => {
                self.budget -= 1;
                InlineCommand::Inline {
                    callee: std::borrow::Cow::Borrowed(body),
                    visit_callee: true,
                }
            }
            None => InlineCommand::KeepCall,
        }
    }
}
/// The Kush function a direct call names, if any.
fn callee_index(
    function: &ir::Function,
    callee: ir::FuncRef,
    by_id: &std::collections::HashMap<u32, usize>,
) -> Option<usize> {
    let ir::ExternalName::User(name) = &function.dfg.ext_funcs[callee].name else {
        return None;
    };
    let name = function.params.user_named_funcs().get(*name)?;
    (name.namespace == 0).then_some(())?;
    by_id.get(&name.index).copied()
}
/// The candidate bodies a caller may absorb (directly or through inlined
/// callees), with their data symbols renamed into the caller's name table.
///
/// Cranelift 0.135's inliner remaps the callee's call targets into the
/// caller's `user_named_funcs` table but copies `GlobalValueData::Symbol`
/// names verbatim, so a callee's data reference (such as the abort word)
/// would name an unrelated entry of the caller. Each symbol is declared in
/// the caller and the callee copy refers to the caller's entry instead.
fn inline_bodies_for(
    caller: &mut ir::Function,
    caller_index: usize,
    candidates: &[Option<ir::Function>],
    by_id: &std::collections::HashMap<u32, usize>,
) -> Vec<Option<ir::Function>> {
    let mut bodies = vec![None; candidates.len()];
    let mut pending = direct_callees(caller, by_id);
    while let Some(index) = pending.pop() {
        if index == caller_index || bodies[index].is_some() {
            continue;
        }
        let Some(candidate) = candidates.get(index).and_then(Option::as_ref) else {
            continue;
        };
        let mut body = candidate.clone();
        let names = body.params.user_named_funcs().clone();
        for data in body.global_values.values_mut() {
            if let ir::GlobalValueData::Symbol {
                name: ir::ExternalName::User(name),
                ..
            } = data
            {
                *name = caller.declare_imported_user_function(names[*name].clone());
            }
        }
        pending.extend(direct_callees(candidate, by_id));
        bodies[index] = Some(body);
    }
    bodies
}
/// The Kush functions a body calls directly.
fn direct_callees(
    function: &ir::Function,
    by_id: &std::collections::HashMap<u32, usize>,
) -> Vec<usize> {
    let mut out = Vec::new();
    for block in function.layout.blocks() {
        for inst in function.layout.block_insts(block) {
            if let ir::InstructionData::Call { func_ref, .. } = function.dfg.insts[inst]
                && let Some(index) = callee_index(function, func_ref, by_id)
            {
                out.push(index);
            }
        }
    }
    out
}
/// Whether a finished function body is small enough to inline and never
/// calls itself directly.
fn inlinable(
    function: &ir::Function,
    index: usize,
    by_id: &std::collections::HashMap<u32, usize>,
) -> bool {
    let mut count = 0;
    for block in function.layout.blocks() {
        for inst in function.layout.block_insts(block) {
            count += 1;
            if count > INLINE_CALLEE_LIMIT {
                return false;
            }
            match function.dfg.insts[inst] {
                ir::InstructionData::Call { func_ref, .. } => {
                    if callee_index(function, func_ref, by_id) == Some(index) {
                        return false;
                    }
                }
                ir::InstructionData::TryCall { .. }
                | ir::InstructionData::TryCallIndirect { .. } => {
                    return false;
                }
                _ => {}
            }
        }
    }
    true
}

pub fn build(program: &Executable, output: &Path) -> Result<()> {
    build_with_options(program, output, false, &LinkSpec::default())
}

thread_local! {
    /// Set by `build_with_clif`: the Cranelift IR of every defined function.
    static CLIF_DUMP: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// Build like [`build`] and also return the Cranelift IR of every function as
/// it is defined (after inlining), for tests and debugging.
pub fn build_with_clif(program: &Executable, output: &Path) -> Result<String> {
    CLIF_DUMP.with(|dump| *dump.borrow_mut() = Some(String::new()));
    let result = build(program, output);
    let text = CLIF_DUMP
        .with(|dump| dump.borrow_mut().take())
        .unwrap_or_default();
    result.map(|()| text)
}

/// Build an executable that reports allocation diagnostics to stderr on a
/// normal exit. The program's own stdout and exit status are unchanged.
pub fn build_with_stats(program: &Executable, output: &Path, stats: bool) -> Result<()> {
    build_with_options(program, output, stats, &LinkSpec::default())
}

/// Build with explicit native link inputs. `LinkSpec::validate` runs before any
/// file is written or `cc` is started.
pub fn build_with_options(
    program: &Executable,
    output: &Path,
    stats: bool,
    links: &LinkSpec,
) -> Result<()> {
    build_with_codegen(program, output, stats, links, CodegenOptions::default())
}

/// Build with explicit, independently selectable optimization controls.
pub fn build_with_codegen(
    program: &Executable,
    output: &Path,
    stats: bool,
    links: &LinkSpec,
    codegen: CodegenOptions,
) -> Result<()> {
    links.validate()?;
    let codegen = codegen.with_environment()?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let scratch = Scratch::new(parent)?;
    let mut defines = Vec::new();
    if program.uses_tasks {
        defines.push("-DKUSH_HAS_TASKS=1".to_owned());
    }
    if program.uses_threads {
        defines.push("-DKUSH_HAS_THREADS=1".to_owned());
    }
    if program.uses_unwinding {
        defines.push("-DKUSH_UNWIND=1".to_owned());
    }
    if let Some(bytes) = program.main_stack {
        defines.push(format!("-DKUSH_MAIN_STACK={bytes}ULL"));
    }
    if stats {
        defines.push("-DKUSH_STATS=1".to_owned());
        defines.push(format!("-DKUSH_FUSION_COUNT={}", program.fusion_count()));
    }
    if codegen.fuzz {
        if codegen.backend != Backend::Cranelift {
            return Err(error("fuzz builds use the Cranelift backend"));
        }
        defines.push("-DKUSH_FUZZ=1".to_owned());
        defines.push(format!(
            "-DKUSH_FUZZ_SITES={}",
            program.obligation_sites().len()
        ));
    }
    let objects = match codegen.backend {
        Backend::Cranelift => {
            let object = crate::timing::time("lower", || object(program, codegen))?;
            let object_path = scratch.path.join("program.o");
            let runtime_object = crate::timing::time("runtime (cached)", || {
                runtime_cache::compile(RUNTIME, &defines, &scratch)
            })?;
            fs::write(&object_path, object).map_err(error)?;
            vec![object_path, runtime_object]
        }
        Backend::Llvm => llvm_objects(program, codegen, &defines, &scratch)?,
    };
    let binary_path = scratch.path.join("program");
    let mut command = Command::new("cc");
    command.arg("-std=c11").arg("-O2").args(&objects);
    for path in &links.objects {
        command.arg(path);
    }
    for path in &links.libraries {
        command.arg(path);
    }
    for dir in &links.library_dirs {
        command.arg("-L").arg(dir);
    }
    for name in &links.system_libraries {
        command.arg(format!("-l{name}"));
    }
    command.arg("-o").arg(&binary_path).arg("-lm");
    if program.uses_threads || program.main_stack.is_some() {
        command.arg("-pthread");
    }
    let result = crate::timing::time("link", || command.output())
        .map_err(|e| error(format!("could not start the native linker 'cc': {e}")))?;
    if !result.status.success() {
        return Err(error(format!(
            "native link failed: {}",
            String::from_utf8_lossy(&result.stderr)
        )));
    }
    fs::rename(binary_path, output).map_err(|e| {
        error(format!(
            "cannot install executable '{}': {e}",
            output.display()
        ))
    })
}

/// The LLVM toolchain used by the release backend. `clang` comes from
/// `KUSH_CLANG` or `PATH`; `llvm-link` is the one that same `clang` reports,
/// so the IR versions always agree.
struct LlvmTools {
    clang: PathBuf,
    /// `llvm-link`, when whole-program optimization is available.
    link: Option<PathBuf>,
}
impl LlvmTools {
    fn find() -> Result<Self> {
        let clang = PathBuf::from(
            std::env::var_os("KUSH_CLANG").unwrap_or_else(|| std::ffi::OsString::from("clang")),
        );
        // The companion normally sits beside the real clang binary; finding
        // it there avoids starting clang just to ask.
        let resolved = if clang.components().count() > 1 {
            Some(clang.clone())
        } else {
            std::env::var_os("PATH").and_then(|path| {
                std::env::split_paths(&path)
                    .map(|directory| directory.join(&clang))
                    .find(|candidate| candidate.is_file())
            })
        };
        // Only beside a binary that is itself clang: a compiler wrapper
        // (ccache and the like) lives elsewhere than the LLVM it runs.
        let sibling = resolved
            .and_then(|path| fs::canonicalize(path).ok())
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("clang"))
            })
            .and_then(|path| Some(path.parent()?.join("llvm-link")))
            .filter(|path| path.is_file());
        let link = match sibling {
            Some(link) => link,
            None => {
                let probe = Command::new(&clang)
                    .arg("-print-prog-name=llvm-link")
                    .output()
                    .map_err(|e| {
                        error(format!(
                            "the LLVM backend needs clang (install it or set KUSH_CLANG): {e}"
                        ))
                    })?;
                if !probe.status.success() {
                    return Err(error(format!(
                        "the LLVM backend could not run '{}'",
                        clang.display()
                    )));
                }
                PathBuf::from(String::from_utf8_lossy(&probe.stdout).trim())
            }
        };
        let link = (std::env::var_os("KUSH_LLVM_NO_WHOLE_PROGRAM").is_none()
            && link.is_absolute()
            && link.is_file())
        .then_some(link);
        Ok(Self { clang, link })
    }
}

fn run_tool(command: &mut Command, what: &str) -> Result<()> {
    let output = command
        .output()
        .map_err(|e| error(format!("could not start {what}: {e}")))?;
    if !output.status.success() {
        return Err(error(format!(
            "{what} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(())
}

/// The program's own LLVM module as text, before it is merged with the
/// runtime and optimized. Needs `clang` to learn the runtime's signatures.
pub fn emit_llvm_ir(program: &Executable, codegen: CodegenOptions) -> Result<String> {
    let tools = LlvmTools::find()?;
    let scratch = Scratch::new(&std::env::temp_dir())?;
    let mut defines = Vec::new();
    if program.uses_tasks {
        defines.push("-DKUSH_HAS_TASKS=1".to_owned());
    }
    let runtime = runtime_cache::compile_llvm(RUNTIME, &defines, &scratch, &tools.clang)?;
    let interface = llvm::RuntimeInterface::parse(&runtime.interface);
    match lower(program, codegen, Some((interface, Split::WHOLE)), false)? {
        Lowered::Llvm(mut modules) => Ok(modules.remove(0)),
        Lowered::Object(_) => unreachable!("the LLVM backend lowers to LLVM IR"),
    }
}

/// Lower through the LLVM backend and return the objects to link.
///
/// The runtime is compiled once (and cached) into an ordinary object plus a
/// bitcode file of the same definitions marked `available_externally`. Each
/// build links the definitions the program reaches into the program module,
/// where LLVM may inline them into user code and then discards them; anything
/// not inlined is called in the runtime object. Only program code is
/// optimized and compiled per build, like a Rust program against its
/// precompiled standard library. Without `llvm-link` the program module is
/// compiled alone and runtime operations stay calls.
fn llvm_objects(
    program: &Executable,
    codegen: CodegenOptions,
    defines: &[String],
    scratch: &Scratch,
) -> Result<Vec<PathBuf>> {
    let tools = crate::timing::time("find clang", LlvmTools::find)?;
    let runtime = crate::timing::time("runtime (cached)", || {
        runtime_cache::compile_llvm(RUNTIME, defines, scratch, &tools.clang)
    })?;
    let interface = llvm::RuntimeInterface::parse(&runtime.interface);
    let Lowered::Llvm(modules) = crate::timing::time("lower", || {
        lower(
            program,
            codegen,
            Some((interface, Split::for_build())),
            false,
        )
    })?
    else {
        unreachable!("the LLVM backend lowers to LLVM IR")
    };
    let level = match codegen.optimization {
        Optimization::None => "-O1",
        Optimization::Speed => "-O3",
    };
    // Each partition is merged with the runtime's inlinable functions and
    // compiled by its own clang, all at once.
    let compile = |part: usize, text: &String| -> Result<PathBuf> {
        let program_ir = scratch.path.join(format!("program{part}.ll"));
        fs::write(&program_ir, text).map_err(error)?;
        if let Some(path) = std::env::var_os("KUSH_EMIT_LLVM") {
            let mut path = PathBuf::from(path);
            if part > 0 {
                path.as_mut_os_string().push(format!(".{part}"));
            }
            fs::copy(&program_ir, path).map_err(error)?;
        }
        let object = scratch.path.join(format!("program{part}.o"));
        let input = match &tools.link {
            Some(link) => {
                let linked = scratch.path.join(format!("linked{part}.bc"));
                // A linker from another LLVM cannot read this clang's
                // bitcode. Inlining the runtime is an optimization; do
                // without it.
                match run_tool(
                    Command::new(link)
                        .arg(&program_ir)
                        .arg(&runtime.inline)
                        .arg("--only-needed")
                        .arg("-o")
                        .arg(&linked),
                    "llvm-link",
                ) {
                    Ok(()) => linked,
                    Err(_) => program_ir,
                }
            }
            None => program_ir,
        };
        let mut command = Command::new(&tools.clang);
        command.arg(level).arg("-fPIC").arg("-c");
        if codegen.native_cpu {
            command.arg("-march=native");
        }
        // The module is generated; clang's note about overriding its
        // target triple is not a user diagnostic.
        command.arg("-Wno-override-module");
        command.arg(&input).arg("-o").arg(&object);
        run_tool(&mut command, "clang (LLVM backend)")?;
        Ok(object)
    };
    let mut objects = crate::timing::time("clang", || {
        std::thread::scope(|scope| {
            let workers: Vec<_> = modules
                .iter()
                .enumerate()
                .map(|(part, text)| scope.spawn(move || compile(part, text)))
                .collect();
            workers
                .into_iter()
                .map(|worker| {
                    worker
                        .join()
                        .unwrap_or_else(|_| Err(error("a clang worker thread failed")))
                })
                .collect::<Result<Vec<_>>>()
        })
    })?;
    objects.push(runtime.object);
    Ok(objects)
}

/// Scratch ownership is local to this process. Existing directories are never
/// reused or deleted; create_dir is the atomic collision check.
pub struct Scratch {
    path: PathBuf,
}
impl Scratch {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn new(parent: &Path) -> Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let path = parent.join(format!(
                ".kush-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut directory = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                directory.mode(0o700);
            }
            match directory.create(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(error(format!("cannot create build directory: {e}"))),
            }
        }
        Err(error("could not create a unique build directory"))
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

/// Only HandlerPush changes the local dynamic-handler depth. The exhaustive
/// child walker includes guards, initializers, conditions and capture operands;
/// separately compiled callback bodies perform their own analysis.
/// Whether a body contains a `while` loop anywhere.
fn block_has_while(block: &ex::Block) -> bool {
    fn expression(expr: &Expr) -> bool {
        let mut found = matches!(expr.kind, ExprKind::While(..));
        expr.for_each_child(&mut |child| found = found || expression(child));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ex::Statement::Let(_, expr) | ex::Statement::Expr(expr) => expression(expr),
        ex::Statement::Declare(_) => false,
    }) || block.tail.as_deref().is_some_and(expression)
}

fn block_installs_handler(block: &ex::Block) -> bool {
    fn expression(expr: &Expr) -> bool {
        if matches!(
            expr.kind,
            ExprKind::HandlerPush { .. }
                | ExprKind::HandlerRedirect { .. }
                | ExprKind::AbortScope {
                    operation: Some(_),
                    ..
                }
        ) {
            return true;
        }
        let mut found = false;
        expr.for_each_child(&mut |child| found |= expression(child));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ex::Statement::Let(_, value) | ex::Statement::Expr(value) => expression(value),
        ex::Statement::Declare(_) => false,
    }) || block.tail.as_ref().is_some_and(|value| expression(value))
}

/// What one lowering produced.
enum Lowered {
    Object(Vec<u8>),
    /// One module per partition (see `llvm::LlvmModule::finish`).
    Llvm(Vec<String>),
}

/// How the LLVM backend splits a program for parallel compilation; see
/// `llvm::LlvmModule::finish`.
#[derive(Clone, Copy)]
pub(crate) struct Split {
    /// Split into at least this many partitions (the available cores)...
    pub cores: usize,
    /// ...and into partitions of about this many lines of IR when that
    /// gives more: LLVM's work grows faster than the size of a function,
    /// so on 2 cores, 4 partitions of a 113,000-line program did 21% less
    /// work than 1 and finished 2.5 times sooner. More than that measured
    /// slower again.
    pub target: usize,
    /// ...but no partition smaller than this: below it, starting another
    /// clang and merging the runtime into it costs more than it saves, and
    /// a smaller program keeps every inlining opportunity. 0 means exactly
    /// `cores` partitions where possible.
    pub minimum: usize,
}
impl Split {
    pub const WHOLE: Split = Split {
        cores: 1,
        target: usize::MAX,
        minimum: usize::MAX,
    };
    /// `KUSH_LLVM_PARTITIONS=N` forces `N`.
    fn for_build() -> Split {
        if let Some(forced) = std::env::var("KUSH_LLVM_PARTITIONS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|count| *count > 0)
        {
            return Split {
                cores: forced,
                target: usize::MAX,
                minimum: 0,
            };
        }
        Split {
            cores: std::thread::available_parallelism().map_or(1, |cores| cores.get()),
            target: 30_000,
            // About 900 lines of Kush. A function called across partitions
            // is not inlined into its caller: forcing the small
            // checked-loops benchmark into 4 partitions cost up to 19% of
            // its run time. `KUSH_LLVM_PARTITIONS=1` keeps any program
            // whole.
            minimum: 8_000,
        }
    }
}

/// The module `Generator` lowers into. Declarations, signatures and function
/// bodies are always built with Cranelift's module and IR builders. With the
/// LLVM backend selected, each verified function body is translated to LLVM
/// IR instead of being compiled by Cranelift.
struct CodeModule {
    object: ObjectModule,
    llvm: Option<llvm::LlvmModule>,
    failure: Option<Diagnostic>,
    /// Functions referred to by the bodies defined so far.
    referenced: std::collections::BTreeSet<FuncId>,
    stage_bodies: BTreeMap<FuncId, staging::Body>,
    stage_recipes: std::collections::BTreeSet<FuncId>,
    literals: BTreeMap<Vec<u8>, DataId>,
}
impl CodeModule {
    fn literal(&mut self, bytes: &[u8]) -> Result<DataId> {
        if let Some(&id) = self.literals.get(bytes) {
            return Ok(id);
        }
        // A generated literal can share its source span with both the
        // quotation graph and other specializations. Intern the actual bytes.
        let id = self
            .declare_data(
                &format!("kush_literal_{}", self.literals.len()),
                Linkage::Local,
                false,
                false,
            )
            .map_err(error)?;
        let mut desc = DataDescription::new();
        desc.define(if bytes.is_empty() {
            Box::new([0])
        } else {
            bytes.into()
        });
        self.define_data(id, &desc).map_err(error)?;
        self.literals.insert(bytes.to_vec(), id);
        Ok(id)
    }
}
impl Module for CodeModule {
    fn isa(&self) -> &dyn cranelift_codegen::isa::TargetIsa {
        self.object.isa()
    }
    fn declarations(&self) -> &cranelift_module::ModuleDeclarations {
        self.object.declarations()
    }
    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> cranelift_module::ModuleResult<FuncId> {
        self.object.declare_function(name, linkage, signature)
    }
    fn declare_anonymous_function(
        &mut self,
        signature: &ir::Signature,
    ) -> cranelift_module::ModuleResult<FuncId> {
        self.object.declare_anonymous_function(signature)
    }
    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> cranelift_module::ModuleResult<DataId> {
        self.object.declare_data(name, linkage, writable, tls)
    }
    fn declare_anonymous_data(
        &mut self,
        writable: bool,
        tls: bool,
    ) -> cranelift_module::ModuleResult<DataId> {
        self.object.declare_anonymous_data(writable, tls)
    }
    fn define_function_with_control_plane(
        &mut self,
        func: FuncId,
        ctx: &mut cranelift_codegen::Context,
        ctrl_plane: &mut cranelift_codegen::control::ControlPlane,
    ) -> cranelift_module::ModuleResult<()> {
        for (_, name) in ctx.func.params.user_named_funcs().iter() {
            if name.namespace == 0 {
                self.referenced.insert(FuncId::from_u32(name.index));
            }
        }
        let Some(llvm) = &mut self.llvm else {
            let result = self
                .object
                .define_function_with_control_plane(func, ctx, ctrl_plane);
            if result.is_ok() && self.stage_recipes.contains(&func) {
                let compiled = ctx.compiled_code().unwrap();
                self.stage_bodies.insert(
                    func,
                    staging::Body {
                        bytes: compiled.buffer.data().to_vec(),
                        relocs: compiled
                            .buffer
                            .relocs()
                            .iter()
                            .map(|relocation| {
                                cranelift_module::ModuleReloc::from_mach_reloc(
                                    relocation, &ctx.func, func,
                                )
                            })
                            .collect(),
                    },
                );
            }
            return result;
        };
        // Same acceptance rule as the Cranelift backend: only verified IR.
        cranelift_codegen::verify_function(&ctx.func, self.object.isa()).map_err(|errors| {
            cranelift_module::ModuleError::Compilation(cranelift_codegen::CodegenError::Verifier(
                errors,
            ))
        })?;
        if let Err(diagnostic) = llvm.define_function(func, &ctx.func, self.object.declarations()) {
            self.failure.get_or_insert(diagnostic);
        }
        if self.stage_recipes.contains(&func) {
            // A runtime recipe is copied and linked by the staging runtime,
            // so it needs machine code and relocations in the image. Kush
            // functions take and return machine words in the platform C
            // convention under both backends, so Cranelift's code for the
            // recipe can call the LLVM-compiled program and be called by it.
            ctx.compile(self.object.isa(), ctrl_plane)
                .map_err(|error| cranelift_module::ModuleError::Compilation(error.inner))?;
            let compiled = ctx.compiled_code().unwrap();
            let body = staging::Body {
                bytes: compiled.buffer.data().to_vec(),
                relocs: compiled
                    .buffer
                    .relocs()
                    .iter()
                    .map(|relocation| {
                        cranelift_module::ModuleReloc::from_mach_reloc(relocation, &ctx.func, func)
                    })
                    .collect(),
            };
            self.stage_bodies.insert(func, body);
        }
        Ok(())
    }
    fn define_function_bytes(
        &mut self,
        func_id: FuncId,
        alignment: u64,
        bytes: &[u8],
        relocs: &[cranelift_module::ModuleReloc],
    ) -> cranelift_module::ModuleResult<()> {
        self.object
            .define_function_bytes(func_id, alignment, bytes, relocs)
    }
    fn define_data(
        &mut self,
        data_id: DataId,
        data: &DataDescription,
    ) -> cranelift_module::ModuleResult<()> {
        let Some(llvm) = &mut self.llvm else {
            return self.object.define_data(data_id, data);
        };
        let bytes = match &data.init {
            cranelift_module::Init::Bytes { contents } => contents.to_vec(),
            cranelift_module::Init::Zeros { size } => vec![0; *size],
            cranelift_module::Init::Uninitialized => Vec::new(),
        };
        let mut pointers = Vec::new();
        for relocation in data.all_relocs(cranelift_codegen::binemit::Reloc::Abs8) {
            let pointer = match relocation.name {
                cranelift_module::ModuleRelocTarget::User {
                    namespace: 0,
                    index,
                } if relocation.addend == 0 => llvm::DataPointer::Function(FuncId::from_u32(index)),
                cranelift_module::ModuleRelocTarget::User {
                    namespace: 1,
                    index,
                } => llvm::DataPointer::Data(DataId::from_u32(index), relocation.addend),
                _ => {
                    self.failure
                        .get_or_insert(error("LLVM backend: unsupported address in data"));
                    return Ok(());
                }
            };
            pointers.push((relocation.offset as usize, pointer));
        }
        llvm.define_data(data_id, bytes, pointers);
        Ok(())
    }
}

/// The local symbol of a Kush function. With `KUSH_SYMBOL_NAMES` set, a
/// profiling aid, it also carries the declaration's name.
fn function_symbol(program: &Executable, index: usize) -> String {
    if std::env::var_os("KUSH_SYMBOL_NAMES").is_none() {
        return format!("kush_fn_{index}");
    }
    let readable: String = program.functions[index]
        .name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    format!("kush_fn_{index}_{readable}")
}

fn object(program: &Executable, codegen: CodegenOptions) -> Result<Vec<u8>> {
    object_for(program, codegen, false)
}
/// The Cranelift object for an executable, or (`library`) for a static
/// library: then `main` is optional and every `export "symbol" fn` gets a C
/// ABI entry point (KUSH-RUST-EXPORT).
fn object_for(program: &Executable, codegen: CodegenOptions, library: bool) -> Result<Vec<u8>> {
    match lower(program, codegen, None, library)? {
        Lowered::Object(bytes) => Ok(bytes),
        Lowered::Llvm(_) => unreachable!("no LLVM runtime interface was supplied"),
    }
}

fn lower(
    program: &Executable,
    codegen: CodegenOptions,
    llvm: Option<(llvm::RuntimeInterface, Split)>,
    library: bool,
) -> Result<Lowered> {
    let staged = staging::prepare(program);
    let recipes = staged
        .as_ref()
        .map(|p| p.recipes.clone())
        .unwrap_or_default();
    let program = staged.as_ref().map_or(program, |p| &p.program);
    let split = llvm.as_ref().map_or(Split::WHOLE, |(_, split)| *split);
    let llvm = llvm.map(|(interface, _)| interface);
    if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        return Err(error(
            "the first native backend supports Linux x86-64 hosts only",
        ));
    }
    let entry = if library {
        program.entry.unwrap_or(usize::MAX)
    } else {
        program.entry()?
    };
    let mut flags = settings::builder();
    flags.set("is_pic", "true").map_err(error)?;
    // A frame larger than a page must touch every page on the way down, or
    // it could step over the guard below the stack.
    flags.set("enable_probestack", "true").map_err(error)?;
    flags.set("probestack_strategy", "inline").map_err(error)?;
    flags
        .set(
            "opt_level",
            match codegen.optimization {
                Optimization::None => "none",
                Optimization::Speed => "speed",
            },
        )
        .map_err(error)?;
    // SIMD-CRANELIFT-FEATURES: `--target-cpu native` lets Cranelift use the
    // build machine's CPU features (SSSE3 byte shuffles, SSE4.1, AVX2, ...);
    // the default stays the portable x86-64 baseline.
    let isa = cranelift_native::builder_with_options(codegen.native_cpu)
        .map_err(error)?
        .finish(settings::Flags::new(flags))
        .map_err(error)?;
    let mut module = CodeModule {
        object: ObjectModule::new(
            ObjectBuilder::new(isa, "kush", default_libcall_names()).map_err(error)?,
        ),
        llvm: llvm.map(llvm::LlvmModule::new),
        failure: None,
        referenced: std::collections::BTreeSet::new(),
        stage_bodies: BTreeMap::new(),
        stage_recipes: Default::default(),
        literals: BTreeMap::new(),
    };
    let capture_data = staging::capture_data(&mut module, &recipes)?;
    let mut print_sig = module.make_signature();
    print_sig.params.push(AbiParam::new(I64));
    print_sig.returns.push(AbiParam::new(I64));
    let print = module
        .declare_function("kush_print_i64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let mut stage_compile_sig = module.make_signature();
    stage_compile_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    stage_compile_sig.returns.push(AbiParam::new(I64));
    let stage_compile = module
        .declare_function("kush_stage_compile", Linkage::Import, &stage_compile_sig)
        .map_err(error)?;
    let print_u64 = module
        .declare_function("kush_print_u64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let print_f64 = module
        .declare_function("kush_print_f64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let print_f32 = module
        .declare_function("kush_print_f32", Linkage::Import, &print_sig)
        .map_err(error)?;
    let mut two_sig = module.make_signature();
    two_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    two_sig.returns.push(AbiParam::new(I64));
    let float_from_int = module
        .declare_function("kush_float_from_int", Linkage::Import, &two_sig)
        .map_err(error)?;
    let float_to_int = module
        .declare_function("kush_float_to_int", Linkage::Import, &two_sig)
        .map_err(error)?;
    let float_int_present = module
        .declare_function("kush_float_int_present", Linkage::Import, &two_sig)
        .map_err(error)?;
    let mut rem_sig = module.make_signature();
    rem_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    rem_sig.returns.push(AbiParam::new(I64));
    let float_rem = module
        .declare_function("kush_float_rem", Linkage::Import, &rem_sig)
        .map_err(error)?;
    let mut three_sig = module.make_signature();
    three_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    three_sig.returns.push(AbiParam::new(I64));
    let int_exact_in_float = module
        .declare_function("kush_int_exact_in_float", Linkage::Import, &three_sig)
        .map_err(error)?;
    let panic_sig = module.make_signature();
    let panic = module
        .declare_function("kush_panic", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let unwind_panic = module
        .declare_function("kush_unwind_panic", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let unwind_rethrow = module
        .declare_function("kush_unwind_rethrow", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let catch_enter = module
        .declare_function("kush_catch_enter", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let catch_leave = module
        .declare_function("kush_catch_leave", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let fuzz = if codegen.fuzz {
        let mut enter_sig = module.make_signature();
        enter_sig.params.push(AbiParam::new(I64));
        let mut arith_sig = module.make_signature();
        arith_sig.params.extend([AbiParam::new(I64); 4]);
        let sites = program
            .obligation_sites()
            .iter()
            .enumerate()
            .map(|(id, o)| ((o.span.start, o.span.end, fuzz_kind(o.kind)), id as i64))
            .collect();
        Some(FuzzHooks {
            enter: module
                .declare_function("kush_fuzz_enter", Linkage::Import, &enter_sig)
                .map_err(error)?,
            leave: module
                .declare_function("kush_fuzz_leave", Linkage::Import, &panic_sig)
                .map_err(error)?,
            arith: module
                .declare_function("kush_fuzz_arith", Linkage::Import, &arith_sig)
                .map_err(error)?,
            sites: std::rc::Rc::new(sites),
        })
    } else {
        None
    };
    let mut alloc_sig = module.make_signature();
    alloc_sig.params.push(AbiParam::new(I64));
    alloc_sig.returns.push(AbiParam::new(I64));
    let allocate = module
        .declare_function("kush_alloc", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let try_allocate = module
        .declare_function("kush_try_alloc", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let mut grow_sig = module.make_signature();
    grow_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    grow_sig.returns.push(AbiParam::new(I64));
    let grow = module
        .declare_function("kush_grow", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let try_grow = module
        .declare_function("kush_try_grow", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let try_bytes_with_capacity = module
        .declare_function("kush_try_bytes_with_capacity", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let mut free_sig = module.make_signature();
    free_sig.params.push(AbiParam::new(I64));
    let free = module
        .declare_function("kush_free", Linkage::Import, &free_sig)
        .map_err(error)?;
    let bytes_free = module
        .declare_function("kush_bytes_free", Linkage::Import, &free_sig)
        .map_err(error)?;
    let buffer_free = module
        .declare_function("kush_buffer_free", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut arena_new_sig = module.make_signature();
    arena_new_sig.returns.push(AbiParam::new(I64));
    let arena_new = module
        .declare_function("kush_arena_new", Linkage::Import, &arena_new_sig)
        .map_err(error)?;
    let arena_new_with_strategy = module
        .declare_function("kush_arena_new_with_strategy", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let arena_alloc = module
        .declare_function("kush_arena_alloc", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let arena_try_alloc = module
        .declare_function("kush_arena_try_alloc", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let arena_release = module
        .declare_function("kush_arena_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let arena_box_release = module
        .declare_function("kush_arena_box_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut alloc_block_sig = module.make_signature();
    alloc_block_sig
        .params
        .extend((0..4).map(|_| AbiParam::new(I64)));
    alloc_block_sig.returns.push(AbiParam::new(I64));
    let alloc_block = module
        .declare_function("kush_alloc_block", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let alloc_block_try = module
        .declare_function("kush_alloc_block_try", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let mut alloc_unary_sig = module.make_signature();
    alloc_unary_sig.params.push(AbiParam::new(I64));
    alloc_unary_sig.returns.push(AbiParam::new(I64));
    let alloc_block_data = module
        .declare_function("kush_alloc_block_data", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_box_create = module
        .declare_function("kush_alloc_box_create", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let alloc_box_payload = module
        .declare_function("kush_alloc_box_payload", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_box_release = module
        .declare_function("kush_alloc_box_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut alloc_vec_create_sig = module.make_signature();
    alloc_vec_create_sig
        .params
        .extend((0..6).map(|_| AbiParam::new(I64)));
    alloc_vec_create_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_create = module
        .declare_function(
            "kush_alloc_vec_create",
            Linkage::Import,
            &alloc_vec_create_sig,
        )
        .map_err(error)?;
    let mut alloc_context_new_sig = module.make_signature();
    alloc_context_new_sig
        .params
        .extend((0..5).map(|_| AbiParam::new(I64)));
    alloc_context_new_sig.returns.push(AbiParam::new(I64));
    let alloc_context_new = module
        .declare_function(
            "kush_alloc_context_new",
            Linkage::Import,
            &alloc_context_new_sig,
        )
        .map_err(error)?;
    let alloc_context_share = module
        .declare_function(
            "kush_alloc_context_share",
            Linkage::Import,
            &alloc_unary_sig,
        )
        .map_err(error)?;
    let alloc_context_release = module
        .declare_function("kush_alloc_context_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut alloc_vec_push_sig = module.make_signature();
    alloc_vec_push_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    alloc_vec_push_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_push = module
        .declare_function("kush_alloc_vec_push", Linkage::Import, &alloc_vec_push_sig)
        .map_err(error)?;
    let alloc_vec_len = module
        .declare_function("kush_alloc_vec_len", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_vec_try_push = module
        .declare_function(
            "kush_alloc_vec_try_push",
            Linkage::Import,
            &alloc_vec_push_sig,
        )
        .map_err(error)?;
    let mut alloc_vec_pop_sig = module.make_signature();
    alloc_vec_pop_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    let alloc_vec_pop = module
        .declare_function("kush_alloc_vec_pop", Linkage::Import, &alloc_vec_pop_sig)
        .map_err(error)?;
    let mut alloc_vec_get_sig = module.make_signature();
    alloc_vec_get_sig
        .params
        .extend((0..3).map(|_| AbiParam::new(I64)));
    let alloc_vec_get = module
        .declare_function("kush_alloc_vec_get", Linkage::Import, &alloc_vec_get_sig)
        .map_err(error)?;
    let mut alloc_vec_set_sig = module.make_signature();
    alloc_vec_set_sig
        .params
        .extend((0..4).map(|_| AbiParam::new(I64)));
    alloc_vec_set_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_set = module
        .declare_function("kush_alloc_vec_set", Linkage::Import, &alloc_vec_set_sig)
        .map_err(error)?;
    let alloc_vec_clear = module
        .declare_function("kush_alloc_vec_clear", Linkage::Import, &free_sig)
        .map_err(error)?;
    let alloc_vec_data = module
        .declare_function("kush_alloc_vec_data", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_vec_release = module
        .declare_function("kush_alloc_vec_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let alloc_ops = AllocOps {
        block: alloc_block,
        block_try: alloc_block_try,
        context_new: alloc_context_new,
        context_share: alloc_context_share,
        context_release: alloc_context_release,
        block_data: alloc_block_data,
        box_create: alloc_box_create,
        box_payload: alloc_box_payload,
        box_release: alloc_box_release,
        vec_create: alloc_vec_create,
        vec_push: alloc_vec_push,
        vec_try_push: alloc_vec_try_push,
        vec_pop: alloc_vec_pop,
        vec_len: alloc_vec_len,
        vec_get: alloc_vec_get,
        vec_set: alloc_vec_set,
        vec_clear: alloc_vec_clear,
        vec_data: alloc_vec_data,
        vec_release: alloc_vec_release,
    };
    let mut restride_sig = module.make_signature();
    restride_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    restride_sig.returns.push(AbiParam::new(I64));
    let vec_restride = module
        .declare_function("kush_vec_restride", Linkage::Import, &restride_sig)
        .map_err(error)?;
    let mut reuse_sig = module.make_signature();
    reuse_sig.returns.push(AbiParam::new(I64));
    let note_reuse = module
        .declare_function("kush_note_reuse", Linkage::Import, &reuse_sig)
        .map_err(error)?;
    let mut from_sig = module.make_signature();
    from_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    from_sig.returns.push(AbiParam::new(I64));
    let bytes_from = module
        .declare_function("kush_bytes_from", Linkage::Import, &from_sig)
        .map_err(error)?;
    let mut bytes_ops = BTreeMap::new();
    for op in BytesOp::ALL {
        let count = if matches!(op, BytesOp::Get | BytesOp::Push | BytesOp::PushReserved) {
            2
        } else {
            1
        };
        let mut sig = module.make_signature();
        sig.params.extend((0..count).map(|_| AbiParam::new(I64)));
        sig.returns.push(AbiParam::new(I64));
        bytes_ops.insert(
            op,
            module
                .declare_function(op.symbol(), Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
    let mut string_sig = module.make_signature();
    string_sig.params.push(AbiParam::new(I64));
    string_sig.returns.push(AbiParam::new(I64));
    let string_validate = module
        .declare_function("kush_utf8_validate", Linkage::Import, &string_sig)
        .map_err(error)?;
    let string_scalar_len = module
        .declare_function("kush_utf8_scalar_len", Linkage::Import, &string_sig)
        .map_err(error)?;
    let mut scalar_at_sig = module.make_signature();
    scalar_at_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    scalar_at_sig.returns.push(AbiParam::new(I64));
    let string_scalar_at = module
        .declare_function("kush_utf8_scalar_at", Linkage::Import, &scalar_at_sig)
        .map_err(error)?;
    let mut str_range_sig = module.make_signature();
    str_range_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    str_range_sig.returns.push(AbiParam::new(I64));
    let str_scalar_len = module
        .declare_function("kush_str_scalar_len", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let str_to_string = module
        .declare_function("kush_str_to_string", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let str_ascii_upper = module
        .declare_function("kush_str_ascii_upper", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let str_ascii_lower = module
        .declare_function("kush_str_ascii_lower", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let mut str_set_sig = module.make_signature();
    str_set_sig.params.extend([
        AbiParam::new(I64),
        AbiParam::new(I64),
        AbiParam::new(I64),
        AbiParam::new(I64),
    ]);
    str_set_sig.returns.push(AbiParam::new(I64));
    let str_set_scalar = module
        .declare_function("kush_str_set_scalar", Linkage::Import, &str_set_sig)
        .map_err(error)?;
    let mut str_index_sig = module.make_signature();
    str_index_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    str_index_sig.returns.push(AbiParam::new(I64));
    let str_byte_at = module
        .declare_function("kush_str_byte_at", Linkage::Import, &str_index_sig)
        .map_err(error)?;
    let str_scalar_at = module
        .declare_function("kush_str_scalar_at", Linkage::Import, &str_index_sig)
        .map_err(error)?;
    let mut vec_element_sig = module.make_signature();
    vec_element_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    vec_element_sig.returns.push(AbiParam::new(I64));
    let vec_element = module
        .declare_function("kush_vec_element", Linkage::Import, &vec_element_sig)
        .map_err(error)?;
    let mut vec_ops = BTreeMap::new();
    for (op, name, params, returns) in [
        (VecOp::WithCapacity, "kush_vec_with_capacity", 2, true),
        (VecOp::Reserve, "kush_vec_reserve", 3, true),
        (
            VecOp::TryReserve {
                ok_tag: 0,
                err_tag: 0,
            },
            "kush_vec_try_reserve",
            3,
            true,
        ),
        (VecOp::Len, "kush_vec_len", 1, true),
        (VecOp::Get, "kush_vec_get", 4, false),
        (VecOp::Push, "kush_vec_push", 3, true),
        (VecOp::Set, "kush_vec_set", 5, true),
        (VecOp::PushBorrowed, "kush_vec_push", 3, true),
        (VecOp::SetBorrowed, "kush_vec_set", 5, true),
        (VecOp::ReserveBorrowed, "kush_vec_reserve", 3, true),
    ] {
        let mut sig = module.make_signature();
        sig.params.extend((0..params).map(|_| AbiParam::new(I64)));
        if returns {
            sig.returns.push(AbiParam::new(I64));
        }
        vec_ops.insert(
            op,
            module
                .declare_function(name, Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
    let mut io_sig = module.make_signature();
    io_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    io_sig.returns.push(AbiParam::new(I64));
    let read_all = module
        .declare_function("kush_io_read_all", Linkage::Import, &io_sig)
        .map_err(error)?;
    let read_line = module
        .declare_function("kush_io_read_line", Linkage::Import, &io_sig)
        .map_err(error)?;
    let read_chunk = module
        .declare_function("kush_io_read_chunk", Linkage::Import, &io_sig)
        .map_err(error)?;
    let write = module
        .declare_function("kush_io_write", Linkage::Import, &io_sig)
        .map_err(error)?;
    // Every checked host operation takes its source arguments plus one out
    // pointer and returns zero or a positive errno.
    let host_symbols = [
        HostOp::FsRead,
        HostOp::FsWrite,
        HostOp::FsWriteExclusive,
        HostOp::FsAppend,
        HostOp::FsRemove,
        HostOp::FsRename,
        HostOp::FsMkdir,
        HostOp::FsRemoveDir,
        HostOp::FsList,
        HostOp::FsIsFile,
        HostOp::FsIsDir,
        HostOp::FsSize,
        HostOp::FsExists,
        HostOp::FsOpen,
        HostOp::FsReadAt,
        HostOp::FsWriteAt,
        HostOp::FsSync,
        HostOp::FsTruncate,
        HostOp::FsFileSize,
        HostOp::FsClose,
        HostOp::FsSyncDir,
        HostOp::EnvArgCount,
        HostOp::EnvArg,
        HostOp::EnvVarCount,
        HostOp::EnvVar,
        HostOp::TimeUnixSeconds,
        HostOp::TimeMonotonicNs,
        HostOp::TimeSleepMs,
        HostOp::ProcRun,
        HostOp::NetTcpExchange,
        HostOp::OsStrerror,
    ];
    let mut host_ops = BTreeMap::new();
    for op in host_symbols {
        let mut sig = module.make_signature();
        sig.params
            .extend((0..=op.arity()).map(|_| AbiParam::new(I64)));
        sig.returns.push(AbiParam::new(I64));
        host_ops.insert(
            op,
            module
                .declare_function(op.symbol(), Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
    let mut task_spawn_sig = module.make_signature();
    task_spawn_sig
        .params
        .extend((0..6).map(|_| AbiParam::new(I64)));
    task_spawn_sig.returns.push(AbiParam::new(I64));
    let task_spawn = module
        .declare_function("kush_task_spawn", Linkage::Import, &task_spawn_sig)
        .map_err(error)?;
    let mut task_join_sig = module.make_signature();
    task_join_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    task_join_sig.returns.push(AbiParam::new(I64));
    let task_join = module
        .declare_function("kush_task_join", Linkage::Import, &task_join_sig)
        .map_err(error)?;
    let mut task_cancel_sig = module.make_signature();
    task_cancel_sig.params.push(AbiParam::new(I64));
    task_cancel_sig.returns.push(AbiParam::new(I64));
    let task_cancel = module
        .declare_function("kush_task_cancel", Linkage::Import, &task_cancel_sig)
        .map_err(error)?;
    let mut task_unary_sig = module.make_signature();
    task_unary_sig.returns.push(AbiParam::new(I64));
    let task_yield = module
        .declare_function("kush_task_yield", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_check_cancel = module
        .declare_function("kush_task_check_cancel", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_scope_begin = module
        .declare_function("kush_task_scope_begin", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_cancel_scope = module
        .declare_function("kush_task_cancel_scope", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_scope_end = module
        .declare_function("kush_task_scope_end", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    // THREAD-SCOPE runtime entry points (defined when built with threads).
    let thread_spawn = module
        .declare_function("kush_thread_spawn", Linkage::Import, &task_spawn_sig)
        .map_err(error)?;
    let thread_join = module
        .declare_function("kush_thread_join", Linkage::Import, &task_join_sig)
        .map_err(error)?;
    let mut thread_void_sig = module.make_signature();
    thread_void_sig.params.clear();
    let thread_scope_begin = module
        .declare_function("kush_thread_scope_begin", Linkage::Import, &thread_void_sig)
        .map_err(error)?;
    let thread_scope_end = module
        .declare_function("kush_thread_scope_end", Linkage::Import, &thread_void_sig)
        .map_err(error)?;
    let abort_word_local = module
        .declare_function("kush_abort_word_address", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    // THREAD-CHANNELS runtime entry points.
    let mut channel_two_sig = module.make_signature();
    channel_two_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    channel_two_sig.returns.push(AbiParam::new(I64));
    let channel_new = module
        .declare_function("kush_channel_new", Linkage::Import, &channel_two_sig)
        .map_err(error)?;
    let channel_recv = module
        .declare_function("kush_channel_recv", Linkage::Import, &channel_two_sig)
        .map_err(error)?;
    let mut channel_void_sig = module.make_signature();
    channel_void_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    let channel_send = module
        .declare_function("kush_channel_send", Linkage::Import, &channel_void_sig)
        .map_err(error)?;
    let mut channel_one_sig = module.make_signature();
    channel_one_sig.params.push(AbiParam::new(I64));
    let channel_close = module
        .declare_function("kush_channel_close", Linkage::Import, &channel_one_sig)
        .map_err(error)?;
    let mut handler_depth_sig = module.make_signature();
    handler_depth_sig.returns.push(AbiParam::new(I64));
    let handler_depth = module
        .declare_function("kush_handler_depth", Linkage::Import, &handler_depth_sig)
        .map_err(error)?;
    let mut kstack_push_sig = module.make_signature();
    kstack_push_sig.params.push(AbiParam::new(I64));
    kstack_push_sig.returns.push(AbiParam::new(I64));
    let kstack_push = module
        .declare_function("kush_kstack_push", Linkage::Import, &kstack_push_sig)
        .map_err(error)?;
    let kstack_mark = module
        .declare_function("kush_kstack_mark", Linkage::Import, &handler_depth_sig)
        .map_err(error)?;
    let mut handler_restore_sig = module.make_signature();
    handler_restore_sig.params.push(AbiParam::new(I64));
    let handler_restore = module
        .declare_function(
            "kush_handler_restore",
            Linkage::Import,
            &handler_restore_sig,
        )
        .map_err(error)?;
    let kstack_restore = module
        .declare_function("kush_kstack_restore", Linkage::Import, &handler_restore_sig)
        .map_err(error)?;
    let mut handler_push_sig = module.make_signature();
    handler_push_sig
        .params
        .extend((0..4).map(|_| AbiParam::new(I64)));
    let handler_push = module
        .declare_function("kush_handler_push", Linkage::Import, &handler_push_sig)
        .map_err(error)?;
    let handler_pop = module
        .declare_function("kush_handler_pop", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let mut handler_lookup_sig = module.make_signature();
    handler_lookup_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    handler_lookup_sig.returns.push(AbiParam::new(I64));
    let handler_lookup = module
        .declare_function("kush_handler_lookup", Linkage::Import, &handler_lookup_sig)
        .map_err(error)?;
    let mut handler_redirect_sig = module.make_signature();
    handler_redirect_sig.params.push(AbiParam::new(I64));
    handler_redirect_sig.returns.push(AbiParam::new(I64));
    let handler_redirect = module
        .declare_function(
            "kush_handler_redirect",
            Linkage::Import,
            &handler_redirect_sig,
        )
        .map_err(error)?;
    let abort_word = module
        .declare_data("kush_abort_word", Linkage::Import, true, false)
        .map_err(error)?;
    let (drops, closure_drops) = synthesize_drops(
        &mut module,
        program,
        free,
        (buffer_free, bytes_free),
        arena_release,
        arena_box_release,
        &alloc_ops,
    )?;
    let context_drops = synthesize_context_drops(&mut module, program, &drops, free)?;
    let task_types = collect_task_types(program);
    let (task_wrappers, task_pointer_drops) =
        synthesize_task_wrappers(&mut module, program, &task_types, &drops)?;
    let mut ids = Vec::new();
    let mut foreign_ids = Vec::new();
    for (index, f) in program.functions.iter().enumerate() {
        if let Some(Some(foreign)) = program.foreign_functions.get(index) {
            let sig = foreign_abi_signature(&mut module, program, foreign);
            let id = module
                .declare_function(&foreign.symbol, Linkage::Import, &sig)
                .map_err(error)?;
            ids.push(id);
            foreign_ids.push(Some(id));
            continue;
        }
        foreign_ids.push(None);
        let mut sig = module.make_signature();
        let mut exclusive_params = Vec::new();
        let erased_result = f.result_grade.is_some_and(Grade::is_zero);
        if erased_result {
            // A copyable `@[0]` result has no payload and no ABI return slot.
        } else if aggregate_result(program, f.result) {
            sig.params.push(AbiParam::new(I64));
        } else {
            sig.returns.push(AbiParam::new(I64));
        }
        let captures = f.closure.unwrap_or(0);
        if f.closure.is_some() {
            sig.params.push(AbiParam::new(I64));
        }
        for position in captures..f.parameters {
            let slot = position;
            let local = &f.locals[f
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position])];
            if f.parameter_grades
                .get(slot)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                // Grade-zero parameter: the argument is evaluated at the call
                // site but has no physical ABI slot.
                continue;
            }
            // The first word of an owning handle or exclusive borrow is a
            // pointer nothing else may use while the callee runs.
            let exclusive = matches!(
                local.ty,
                Type::Box(_)
                    | Type::RefMut(_)
                    | Type::Vec(_)
                    | Type::Bytes
                    | Type::String
                    | Type::SliceMut(_)
                    | Type::StrMut
            );
            for word in 0..program.width(local.ty) {
                if exclusive && word == 0 {
                    exclusive_params.push(sig.params.len());
                }
                sig.params.push(AbiParam::new(I64));
            }
        }
        let name = if index == entry {
            "kush_entry".to_owned()
        } else {
            function_symbol(program, index)
        };
        let id = module
            .declare_function(
                &name,
                if index == entry {
                    Linkage::Export
                } else {
                    Linkage::Local
                },
                &sig,
            )
            .map_err(error)?;
        if let Some(llvm) = &mut module.llvm {
            llvm.exclusive_parameters(&name, exclusive_params);
        }
        ids.push(id);
    }
    module
        .stage_recipes
        .extend(recipes.keys().map(|&index| ids[index]));
    // Lower only what the program can reach. Every reference to a function,
    // whether a call, a function value or a closure, goes through a
    // declaration in the referring body, and `CodeModule` records those as
    // bodies are defined; so the set grows from the entry point and from the
    // glue synthesized above until nothing new turns up. Library functions
    // the program never uses are neither lowered nor compiled.
    let index_of: BTreeMap<FuncId, usize> = ids
        .iter()
        .enumerate()
        .map(|(index, id)| (*id, index))
        .collect();
    let mut lowered = vec![false; program.functions.len()];
    // A library has no entry point of its own: its exports are the roots.
    let mut pending: Vec<usize> = if library {
        program
            .exports
            .iter()
            .map(|export| export.index)
            .chain((entry != usize::MAX).then_some(entry))
            .collect()
    } else {
        vec![entry]
    };
    // A recipe is reachable only through a quotation in a reachable body.
    // Compile-time-only templates stay out of the executable.
    let recipes_of: BTreeMap<usize, usize> = recipes
        .iter()
        .map(|(&recipe, &(schema, _))| (schema, recipe))
        .collect();
    // NATIVE-INLINE: bodies are built first and defined after, so a
    // caller can absorb any small reachable callee.
    let mut bodies: Vec<Option<ir::Function>> = vec![None; program.functions.len()];
    // FND-MIR: the functions the CFG IR covers are lowered from it.
    // The tree path's loop optimizations (deferred overflow checks, vector
    // push shadows) are not ported yet (FND-MIR-DEFAULT): when one is on, a
    // function with a `while` loop keeps the tree path.
    let loop_optimized = codegen.defers_overflow()
        || (codegen.optimization == Optimization::Speed && codegen.backend == Backend::Llvm);
    let mir_bodies: Vec<Option<crate::mir::Body>> = if codegen.mir {
        (0..program.functions.len())
            .map(|index| {
                let body = &program.functions[index].body;
                if loop_optimized && block_has_while(body) {
                    return None;
                }
                crate::mir::build(program, index).ok()
            })
            .collect()
    } else {
        Vec::new()
    };
    loop {
        for id in std::mem::take(&mut module.referenced) {
            if let Some(index) = index_of.get(&id)
                && !lowered[*index]
            {
                pending.push(*index);
            }
        }
        let Some(index) = pending.pop() else {
            break;
        };
        if std::mem::replace(&mut lowered[index], true) {
            continue;
        }
        let f = &program.functions[index];
        staging::quoted_schemas(f, |schema| {
            if let Some(&recipe) = recipes_of.get(&schema) {
                pending.push(recipe);
            }
        });
        if program
            .foreign_functions
            .get(index)
            .is_some_and(Option::is_some)
        {
            // The C import was declared above; there is no Kush body to define.
            continue;
        }
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(ids[index])
            .signature
            .clone();
        let mut function_context = FunctionBuilderContext::new();
        let failing = if program.uses_unwinding {
            module
                .declarations()
                .get_functions()
                .filter(|(_, declaration)| {
                    declaration
                        .name
                        .as_deref()
                        .is_some_and(|name| FAILING_RUNTIME.contains(&name))
                })
                .map(|(id, _)| id)
                .collect()
        } else {
            std::collections::BTreeSet::new()
        };
        let builder = FunctionBuilder::new(&mut context.func, &mut function_context);
        let mut g = Generator {
            builder,
            module: &mut module,
            ids: &ids,
            foreign_ids: &foreign_ids,
            program,
            codegen,
            print,
            stage_compile,
            print_u64,
            print_f64,
            print_f32,
            float_from_int,
            int_exact_in_float,
            float_to_int,
            float_int_present,
            float_rem,
            panic,
            unwind_panic,
            unwind_rethrow,
            catch_enter,
            catch_leave,
            failing,
            unwind_emitting: false,
            fuzz: fuzz.clone(),
            fuzz_depth: 0,
            variables: Vec::new(),
            locations: Vec::new(),
            result: f.result,
            return_pointer: None,
            allocate,
            try_allocate,
            grow,
            try_grow,
            try_bytes_with_capacity,
            free,
            arena_new,
            arena_new_with_strategy,
            arena_alloc,
            arena_try_alloc,
            arena_box_release,
            alloc_ops: &alloc_ops,
            vec_restride,
            note_reuse,
            drops: &drops,
            context_drops: &context_drops,
            tracked: vec![],
            function_index: index,
            deferred: None,
            bytes_from,
            read_all,
            read_line,
            read_chunk,
            write,
            host_ops: &host_ops,
            bytes_ops: &bytes_ops,
            string_validate,
            string_scalar_len,
            string_scalar_at,
            str_scalar_len,
            str_byte_at,
            str_scalar_at,
            str_to_string,
            str_writes: [str_ascii_upper, str_ascii_lower, str_set_scalar],
            vec_ops: &vec_ops,
            vec_element,
            abort_word,
            closure_drops: &closure_drops,
            task_spawn,
            task_join,
            task_cancel,
            task_yield,
            task_check_cancel,
            task_scope_begin,
            task_cancel_scope,
            task_scope_end,
            thread_spawn,
            thread_join,
            thread_scope_begin,
            thread_scope_end,
            abort_word_local,
            channel_new,
            channel_send,
            channel_recv,
            channel_close,
            handler_depth,
            handler_restore,
            kstack_push,
            kstack_mark,
            kstack_restore,
            handler_push,
            handler_pop,
            handler_lookup,
            handler_redirect,
            handler_base: None,
            task_wrappers: &task_wrappers,
            task_pointer_drops: &task_pointer_drops,
            loops: Vec::new(),
            regions: Vec::new(),
            aborts: Vec::new(),
            slice_layouts: BTreeMap::new(),
            proved_accesses: std::collections::BTreeSet::new(),
            store_proved: false,
            upper_bounds: Vec::new(),
            vec_shadows: BTreeMap::new(),
            pending_pushes: Vec::new(),
            push_shadow: None,
            mir_unwind: None,
        };
        let entry = g.builder.create_block();
        g.builder.append_block_params_for_function_params(entry);
        g.builder.switch_to_block(entry);
        if block_installs_handler(&f.body) {
            let handler_base = g.builder.declare_var(I64);
            g.handler_base = Some(handler_base);
            let base = g.runtime_call(g.handler_depth, &[]);
            g.builder.def_var(handler_base, base);
        }
        for local in &f.locals {
            let variables = (0..program.width(local.ty))
                .map(|_| g.builder.declare_var(I64))
                .collect();
            g.variables.push(variables);
        }
        // INLINE-RECORD-PARAMS: a record of scalars whose address is never
        // taken stays in SSA variables, so copies of by-value records (for
        // example after inlining) cost no stack traffic.
        let addressed = addressed_slots(&f.body);
        for (slot, local) in f.locals.iter().enumerate() {
            let array = local
                .ty
                .layout()
                .is_some_and(|id| program.enums[id].array.is_some());
            // Nominal records are pinned for the whole function so a
            // call-scoped `&Record`/`&mut Record` can point at the same storage
            // the local reads and writes. Inline arrays keep their existing
            // pinning rule.
            let record = local.ty.layout().is_some_and(|id| program.enums[id].record)
                && !(scalar_record(program, local.ty, 0) && !addressed.contains(&slot));
            let object = matches!(local.ty, Type::Union(_) | Type::DynObj(_));
            // Owning handles are pinned too so an exclusive `&mut Box`/`&mut
            // Vec` can update the caller's slot in place, including after a
            // vector growth moves the allocation.
            let owner_handle = matches!(
                local.ty,
                Type::Box(_)
                    | Type::ArenaBox(_)
                    | Type::Arena
                    | Type::Bytes
                    | Type::String
                    | Type::Vec(_)
            );
            if array || record || object || owner_handle || local.pinned {
                let width = program.width(local.ty);
                let slot = g.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (width * 8) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let pointer = g.builder.ins().stack_addr(I64, slot, 0);
                for index in 0..width {
                    let zero = g.constant(0);
                    g.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                g.locations.push(Some(pointer));
            } else {
                g.locations.push(None);
            }
        }
        for ty in &f.resources {
            let active = g.builder.declare_var(ir::types::I8);
            let zero = g.builder.ins().iconst(ir::types::I8, 0);
            g.builder.def_var(active, zero);
            let mut words = Vec::new();
            for _ in 0..program.width(*ty) {
                let v = g.builder.declare_var(I64);
                let zero = g.constant(0);
                g.builder.def_var(v, zero);
                words.push(v);
            }
            g.tracked.push(Tracked {
                active,
                words,
                ty: *ty,
                location: None,
            });
        }
        let mut offset = 0;
        let erased_result = f.result_grade.is_some_and(Grade::is_zero);
        if !erased_result && aggregate_result(program, f.result) {
            g.return_pointer = Some(g.builder.block_params(entry)[0]);
            offset = 1;
        }
        let captures = f.closure.unwrap_or(0);
        if let Some(&(_, count)) = recipes.get(&index) {
            for slot in 0..count {
                let id = capture_data[&(index, slot)];
                let global = g.module.declare_data_in_func(id, g.builder.func);
                let address = g.builder.ins().symbol_value(I64, global);
                let value = g
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), address, 0);
                g.assign(slot, &[value]);
                // Captures borrow immutable artifact storage. They are not
                // activated as resources owned by an individual invocation.
            }
        }
        if f.closure.is_some() {
            let environment = g.builder.block_params(entry)[offset];
            offset += 1;
            if captures != 0 {
                let mut capture_offset = 8i32;
                for position in 0..captures {
                    let i = f
                        .parameter_slots
                        .as_ref()
                        .map_or(position, |slots| slots[position]);
                    let width = g.variables[i].len();
                    if f.capture_refs.get(position).copied().unwrap_or(false) {
                        // The environment stores the caller's stack address.
                        // Reads and writes of this capture go through it.
                        let pointer = g.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            environment,
                            capture_offset,
                        );
                        g.locations[i] = Some(pointer);
                        let zero = g.constant(0);
                        for variable in &g.variables[i] {
                            g.builder.def_var(*variable, zero);
                        }
                        capture_offset += 8;
                        g.activate_local(i);
                        continue;
                    }
                    let values = g.load_words(environment, capture_offset, width);
                    capture_offset += (width * 8) as i32;
                    g.assign(i, &values);
                    g.activate_local(i);
                }
                // A `multi fn` environment stays on the continuation stack
                // for later resumptions.
                if !f.shared_environment {
                    emit_drop(&mut g.builder, g.module, free, &[environment]);
                }
            }
        }
        for position in captures..f.parameters {
            let i = f
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position]);
            if f.parameter_grades
                .get(position)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                continue;
            }
            let width = g.variables[i].len();
            let values = g.builder.block_params(entry)[offset..offset + width].to_vec();
            g.assign(i, &values);
            g.activate_local(i);
            offset += width;
        }
        if let Some(body) = mir_bodies.get(index).and_then(Option::as_ref) {
            g.mir_body(body);
        } else if let Some(value) = g.block(&f.body) {
            g.cleanup_all();
            if erased_result {
                // Preserve actual cleanup for a copyable erased result, then
                // return without an ABI payload.
                g.drop_value(f.result, &value);
                g.return_value(&[]);
            } else {
                g.return_value(&value);
            }
        }
        g.builder.seal_all_blocks();
        g.builder.finalize(g.module.target_config());
        // Reachability reads the references of each body as it is built,
        // since bodies are defined only after inlining.
        for (_, name) in context.func.params.user_named_funcs().iter() {
            if name.namespace == 0 {
                module.referenced.insert(FuncId::from_u32(name.index));
            }
        }
        bodies[index] = Some(context.func);
    }
    // NATIVE-INLINE (Cranelift only): every reachable body is built, so a
    // caller can absorb any small callee; then each function is defined.
    let inline_calls = codegen.inline_calls && module.llvm.is_none() && staged.is_none();
    let by_id = ids
        .iter()
        .enumerate()
        .map(|(index, id)| (id.as_u32(), index))
        .collect::<std::collections::HashMap<_, _>>();
    let candidates = if inline_calls {
        bodies
            .iter()
            .enumerate()
            .map(|(index, body)| {
                body.as_ref()
                    .filter(|body| inlinable(body, index, &by_id))
                    .cloned()
            })
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    for (index, f) in program.functions.iter().enumerate() {
        let Some(body) = bodies[index].take() else {
            continue;
        };
        let failed = |e: &dyn std::fmt::Debug| {
            Diagnostic::new(
                f.span,
                format!(
                    "Cranelift verification/code generation failed in {}: {e:?}",
                    f.name
                ),
            )
        };
        let mut context = module.make_context();
        context.func = body;
        if module.stage_recipes.contains(&ids[index]) {
            // The copied body may live more than 2 GiB from the AOT image.
            // The runtime linker gives data and function addresses nearby GOT
            // entries, including the body and drop glue of a nested closure.
            for (_, global) in context.func.global_values.iter_mut() {
                if let ir::GlobalValueData::Symbol { colocated, .. } = global {
                    *colocated = false;
                }
            }
            for (_, function) in context.func.dfg.ext_funcs.iter_mut() {
                function.colocated = false;
            }
        }
        let dump_clif = CLIF_DUMP.with(|dump| dump.borrow().is_some());
        if inline_calls {
            let bodies = inline_bodies_for(&mut context.func, index, &candidates, &by_id);
            context
                .inline(Inliner {
                    by_id: &by_id,
                    bodies: &bodies,
                    caller: index,
                    budget: INLINE_CALLS_PER_CALLER,
                })
                .map_err(|e| failed(&e))?;
        }
        if dump_clif {
            // Cranelift prints callees by index; name them for the reader.
            let mut text = format!("; {}\n", f.name);
            for (_, name) in context.func.params.user_named_funcs().iter() {
                if name.namespace == 0 {
                    let id = FuncId::from_u32(name.index);
                    let declaration = module.declarations().get_function_decl(id);
                    if let Some(symbol) = &declaration.name {
                        text.push_str(&format!("; calls {symbol}\n"));
                    }
                }
            }
            text.push_str(&format!("{}\n", context.func.display()));
            CLIF_DUMP.with(|dump| {
                if let Some(dump) = dump.borrow_mut().as_mut() {
                    dump.push_str(&text);
                }
            });
        }
        let started = std::time::Instant::now();
        let defined = module.define_function(ids[index], &mut context);
        crate::timing::add("Cranelift codegen or LLVM IR text", started.elapsed());
        defined.map_err(|e| failed(&e))?;
    }
    if library {
        define_exports(&mut module.object, program, &ids)?;
    }
    // An object file must define every local symbol it declares, so the
    // functions that were not reached get a body that only traps. (The LLVM
    // module simply omits them.)
    if module.llvm.is_none() {
        for (index, id) in ids.iter().enumerate() {
            // Imports have no body here whether or not they are reached.
            if lowered[index] || foreign_ids[index].is_some() {
                continue;
            }
            let mut context = module.make_context();
            context.func.signature = module
                .declarations()
                .get_function_decl(*id)
                .signature
                .clone();
            let mut function_context = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut function_context);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.ins().trap(TrapCode::unwrap_user(2));
            builder.seal_all_blocks();
            builder.finalize(module.target_config());
            module.define_function(*id, &mut context).map_err(error)?;
        }
    }
    if let Some(failure) = module.failure {
        return Err(failure);
    }
    if staged.is_some() {
        staging::emit(&mut module, &ids, &recipes, &capture_data)?;
    }
    match module.llvm {
        Some(llvm) => Ok(Lowered::Llvm(
            llvm.finish(module.object.declarations(), split)?,
        )),
        None => Ok(Lowered::Object(
            module.object.finish().emit().map_err(error)?,
        )),
    }
}

/// KUSH-RUST-EXPORT: one exported C ABI function per `export "symbol" fn`,
/// converting C scalars to Kush words and back around a call of the Kush
/// function. `Bool` crosses as `int32_t` (any non-zero is `true`), narrow
/// integers at their width, floats as `float`/`double`.
fn define_exports(module: &mut ObjectModule, program: &Executable, ids: &[FuncId]) -> Result<()> {
    let mut word_sig = module.make_signature();
    word_sig.params.push(AbiParam::new(I64));
    let bytes_free = module
        .declare_function("kush_bytes_free", Linkage::Import, &word_sig)
        .map_err(error)?;
    let mut from_sig = module.make_signature();
    from_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    from_sig.returns.push(AbiParam::new(I64));
    let bytes_from = module
        .declare_function("kush_bytes_from", Linkage::Import, &from_sig)
        .map_err(error)?;
    for export in &program.exports {
        let record_result = c_record(program, export.result).is_some();
        let mut sig = module.make_signature();
        for (_, ty) in &export.parameters {
            if is_bytes_ref(program, *ty) {
                sig.params.extend([AbiParam::new(I64), AbiParam::new(I64)]);
            } else if c_record(program, *ty).is_some() {
                sig.params.push(AbiParam::new(I64));
            } else {
                sig.params.push(AbiParam::new(abi_value_type(*ty)));
            }
        }
        if record_result {
            sig.params.push(AbiParam::new(I64));
        } else if export.result != Type::Unit {
            sig.returns
                .push(AbiParam::new(abi_value_type(export.result)));
        }
        let id = module
            .declare_function(&export.symbol, Linkage::Export, &sig)
            .map_err(error)?;
        let inner_sig = module
            .declarations()
            .get_function_decl(ids[export.index])
            .signature
            .clone();
        let expected_words = usize::from(record_result)
            + export
                .parameters
                .iter()
                .map(|(_, ty)| {
                    if is_bytes_ref(program, *ty) {
                        1
                    } else {
                        program.width(*ty)
                    }
                })
                .sum::<usize>();
        if inner_sig.params.len() != expected_words
            || inner_sig.params.iter().any(|p| p.value_type != I64)
        {
            return Err(error(format!(
                "internal error: export '{}' does not have a word-per-field body",
                export.symbol
            )));
        }
        let mut context = module.make_context();
        context.func.signature = sig;
        let mut fc = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut context.func, &mut fc);
        let block = b.create_block();
        b.append_block_params_for_function_params(block);
        b.switch_to_block(block);
        let mut params = b.block_params(block).to_vec().into_iter();
        let mut words = Vec::new();
        let result_slot = record_result.then(|| {
            let slot = b.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (program.width(export.result) * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
            ));
            b.ins().stack_addr(I64, slot, 0)
        });
        if let Some(pointer) = result_slot {
            words.push(pointer);
        }
        let mut temporaries = Vec::new();
        for (_, ty) in &export.parameters {
            if is_bytes_ref(program, *ty) {
                // A borrowed buffer: copy the bytes into a temporary Kush
                // buffer for the call and free it after.
                let data = params.next().expect("data pointer");
                let length = params.next().expect("length");
                let from = module.declare_func_in_func(bytes_from, b.func);
                let call = b.ins().call(from, &[data, length]);
                let handle = b.inst_results(call)[0];
                let slot = b.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    8,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let address = b.ins().stack_addr(I64, slot, 0);
                b.ins().store(ir::MemFlagsData::new(), handle, address, 0);
                temporaries.push(handle);
                words.push(address);
            } else if let Some(layout) = c_record(program, *ty) {
                let pointer = params.next().expect("record pointer");
                for (leaf, offset) in layout.leaves {
                    let value = b.ins().load(
                        c_scalar_type(leaf),
                        ir::MemFlagsData::new(),
                        pointer,
                        offset as i32,
                    );
                    words.push(c_to_word(&mut b, leaf, value));
                }
            } else {
                let value = params.next().expect("scalar parameter");
                words.push(abi_to_word(&mut b, *ty, value));
            }
        }
        let out = record_result.then(|| params.next().expect("result pointer"));
        let callee = module.declare_func_in_func(ids[export.index], b.func);
        let call = b.ins().call(callee, &words);
        let returned = b.inst_results(call).to_vec();
        for handle in temporaries {
            let free = module.declare_func_in_func(bytes_free, b.func);
            b.ins().call(free, &[handle]);
        }
        if let (Some(source), Some(out)) = (result_slot, out) {
            let layout = c_record(program, export.result).expect("record result");
            for (index, (leaf, offset)) in layout.leaves.into_iter().enumerate() {
                let word = b
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), source, (index * 8) as i32);
                let value = word_to_c(&mut b, leaf, word);
                b.ins()
                    .store(ir::MemFlagsData::new(), value, out, offset as i32);
            }
            b.ins().return_(&[]);
        } else if export.result == Type::Unit {
            b.ins().return_(&[]);
        } else {
            let word = returned[0];
            let value = match export.result {
                Type::Bool => b.ins().ireduce(ir::types::I32, word),
                Type::Int(kind) if !matches!(kind, IntKind::I64 | IntKind::U64) => {
                    b.ins().ireduce(abi_value_type(export.result), word)
                }
                Type::Float(FloatKind::F64) => {
                    b.ins()
                        .bitcast(ir::types::F64, ir::MemFlagsData::new(), word)
                }
                Type::Float(FloatKind::F32) => {
                    let bits = b.ins().ireduce(ir::types::I32, word);
                    b.ins()
                        .bitcast(ir::types::F32, ir::MemFlagsData::new(), bits)
                }
                _ => word,
            };
            b.ins().return_(&[value]);
        }
        b.seal_all_blocks();
        b.finalize(module.target_config());
        module
            .define_function(id, &mut context)
            .map_err(|e| error(format!("export '{}': {e:?}", export.symbol)))?;
    }
    Ok(())
}

/// EXPORT-RECORDS: whether `ty` is `&Bytes`.
fn is_bytes_ref(program: &Executable, ty: Type) -> bool {
    matches!(ty, Type::Ref(pointer) if program.pointees[pointer] == Type::Bytes)
}
/// C layout of an exported record of scalars: its leaves in Kush word order
/// with their byte offsets, and the struct's size and alignment. Nested
/// records are nested C structs (`#[repr(C)]` in the Rust bindings).
struct CRecord {
    leaves: Vec<(Type, u32)>,
    size: u32,
    align: u32,
}
fn c_record(program: &Executable, ty: Type) -> Option<CRecord> {
    let id = ty.layout()?;
    let layout = &program.enums[id];
    if !layout.record || layout.variants.len() != 1 {
        return None;
    }
    let mut leaves = Vec::new();
    let (mut offset, mut align) = (0u32, 1u32);
    for field in &layout.variants[0].fields {
        let (size, field_align, inner) = match field {
            Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) => {
                let size = c_scalar_size(*field);
                (size, size, vec![(*field, 0)])
            }
            other => {
                let nested = c_record(program, *other)?;
                (nested.size, nested.align, nested.leaves)
            }
        };
        offset = offset.div_ceil(field_align) * field_align;
        leaves.extend(inner.into_iter().map(|(leaf, at)| (leaf, offset + at)));
        offset += size;
        align = align.max(field_align);
    }
    Some(CRecord {
        leaves,
        size: offset.div_ceil(align) * align,
        align,
    })
}
fn c_scalar_size(ty: Type) -> u32 {
    match ty {
        Type::Bool => 1,
        Type::Int(kind) => match kind {
            IntKind::I8 | IntKind::U8 => 1,
            IntKind::I16 | IntKind::U16 => 2,
            IntKind::I32 | IntKind::U32 => 4,
            IntKind::I64 | IntKind::U64 => 8,
        },
        Type::Float(FloatKind::F32) => 4,
        _ => 8,
    }
}
/// A record field's C type: `bool` is one byte (`u8`) inside structs.
fn c_scalar_type(ty: Type) -> ir::Type {
    match ty {
        Type::Bool => ir::types::I8,
        other => abi_value_type(other),
    }
}
fn c_to_word(b: &mut FunctionBuilder, ty: Type, value: Value) -> Value {
    match ty {
        Type::Bool => {
            let set = b.ins().icmp_imm_u(IntCC::NotEqual, value, 0);
            b.ins().uextend(I64, set)
        }
        other => abi_to_word(b, other, value),
    }
}
fn abi_to_word(b: &mut FunctionBuilder, ty: Type, value: Value) -> Value {
    match ty {
        Type::Bool => {
            let set = b.ins().icmp_imm_u(IntCC::NotEqual, value, 0);
            b.ins().uextend(I64, set)
        }
        Type::Int(kind) if !matches!(kind, IntKind::I64 | IntKind::U64) => {
            if kind.signed() {
                b.ins().sextend(I64, value)
            } else {
                b.ins().uextend(I64, value)
            }
        }
        Type::Float(FloatKind::F64) => b.ins().bitcast(I64, ir::MemFlagsData::new(), value),
        Type::Float(FloatKind::F32) => {
            let bits = b
                .ins()
                .bitcast(ir::types::I32, ir::MemFlagsData::new(), value);
            b.ins().uextend(I64, bits)
        }
        _ => value,
    }
}
fn word_to_c(b: &mut FunctionBuilder, ty: Type, word: Value) -> Value {
    match ty {
        Type::Bool => b.ins().ireduce(ir::types::I8, word),
        Type::Int(kind) if !matches!(kind, IntKind::I64 | IntKind::U64) => {
            b.ins().ireduce(abi_value_type(ty), word)
        }
        Type::Float(FloatKind::F64) => {
            b.ins()
                .bitcast(ir::types::F64, ir::MemFlagsData::new(), word)
        }
        Type::Float(FloatKind::F32) => {
            let bits = b.ins().ireduce(ir::types::I32, word);
            b.ins()
                .bitcast(ir::types::F32, ir::MemFlagsData::new(), bits)
        }
        _ => word,
    }
}

/// KUSH-RUST-EXPORT: build a static library (`.a`) holding the program's
/// code, the runtime (without `main`) and one C ABI entry point per
/// `export "symbol" fn`. Link it into a C or Rust program; see
/// [`rust_bindings`] for the Rust side.
pub fn build_library(program: &Executable, output: &Path, codegen: CodegenOptions) -> Result<()> {
    if program.exports.is_empty() {
        return Err(error(
            "a library needs at least one 'export \"symbol\" fn' declaration",
        ));
    }
    // std.sys stubs (`kush_sys_*`) live in the runtime that ships in the archive.
    if program
        .foreign_functions
        .iter()
        .flatten()
        .any(|foreign| !foreign.symbol.starts_with("kush_sys_"))
    {
        return Err(error(
            "a library cannot import foreign functions yet; link them into the final program instead",
        ));
    }
    let object = object_for(program, codegen, true)?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let scratch = Scratch::new(parent)?;
    let object_path = scratch.path.join("program.o");
    fs::write(&object_path, object).map_err(error)?;
    let mut defines = vec!["-DKUSH_NO_MAIN=1".to_owned()];
    if program.uses_tasks {
        defines.push("-DKUSH_HAS_TASKS=1".to_owned());
    }
    let runtime_object = runtime_cache::compile(RUNTIME, &defines, &scratch)?;
    let archive = scratch.path.join("library.a");
    let result = Command::new("ar")
        .arg("rcs")
        .arg(&archive)
        .arg(&object_path)
        .arg(&runtime_object)
        .output()
        .map_err(|e| error(format!("could not start the archiver 'ar': {e}")))?;
    if !result.status.success() {
        return Err(error(format!(
            "archiving the library failed: {}",
            String::from_utf8_lossy(&result.stderr)
        )));
    }
    fs::rename(&archive, output).map_err(|e| {
        error(format!(
            "cannot install library '{}': {e}",
            output.display()
        ))
    })
}

/// KUSH-RUST-EXPORT: `kush build --lib lib<name>.a`: the static library and,
/// next to it, `lib<name>.rs` with its Rust bindings. Returns the bindings path.
pub fn build_library_and_bindings(
    program: &Executable,
    output: &Path,
    codegen: CodegenOptions,
) -> Result<PathBuf> {
    let file = output
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    let Some(name) = file
        .strip_prefix("lib")
        .and_then(|rest| rest.strip_suffix(".a"))
        .filter(|name| {
            !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
    else {
        return Err(error(format!(
            "a library output must be named lib<name>.a with a name of letters, digits and '_', found '{}'",
            output.display()
        )));
    };
    build_library(program, output, codegen)?;
    let bindings = output.with_extension("rs");
    fs::write(&bindings, rust_bindings(program, name)).map_err(|e| {
        error(format!(
            "cannot write Rust bindings '{}': {e}",
            bindings.display()
        ))
    })?;
    Ok(bindings)
}

/// KUSH-RUST-EXPORT: a Rust module declaring the library's exports. The raw
/// `extern "C"` items are in `ffi`; the safe wrappers are methods of
/// `Library`, a token of which exactly one exists per process
/// (`Library::take`). The Kush runtime keeps global state (handler stack,
/// abort word), so calls must not overlap: the token is `Send` but not
/// `Sync`, which lets one thread at a time use it without a lock.
pub fn rust_bindings(program: &Executable, library_name: &str) -> String {
    // Kush names that are Rust keywords become raw identifiers.
    let ident = |name: &str| {
        const KEYWORDS: &[&str] = &[
            "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
            "extern", "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match",
            "mod", "move", "mut", "pub", "ref", "return", "static", "struct", "trait", "true",
            "type", "unsafe", "use", "where", "while", "abstract", "become", "box", "do", "final",
            "macro", "override", "priv", "try", "typeof", "unsized", "virtual", "yield", "self",
            "Self", "super",
        ];
        if KEYWORDS.contains(&name) {
            format!("r#{name}")
        } else {
            name.to_owned()
        }
    };
    // EXPORT-RECORDS: one `#[repr(C)]` struct per exported record type.
    let mut structs: Vec<(usize, String)> = Vec::new();
    fn collect(program: &Executable, ty: Type, structs: &mut Vec<(usize, String)>) {
        let Some(id) = ty.layout() else { return };
        if c_record(program, ty).is_none() || structs.iter().any(|(seen, _)| *seen == id) {
            return;
        }
        for field in &program.enums[id].variants[0].fields {
            collect(program, *field, structs);
        }
        let full = program.type_name(ty);
        let base: String = full
            .rsplit('.')
            .next()
            .unwrap_or(&full)
            .chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect();
        let mut name = base.clone();
        let mut counter = 2;
        while structs.iter().any(|(_, existing)| *existing == name) {
            name = format!("{base}{counter}");
            counter += 1;
        }
        structs.push((id, name));
    }
    for export in &program.exports {
        for (_, ty) in &export.parameters {
            collect(program, *ty, &mut structs);
        }
        collect(program, export.result, &mut structs);
    }
    let struct_name = |ty: Type| {
        ty.layout()
            .and_then(|id| structs.iter().find(|(seen, _)| *seen == id))
            .map(|(_, name)| name.clone())
    };
    let scalar = |ty: Type| -> String {
        match ty {
            Type::Bool => "bool".into(),
            Type::I64 => "i64".into(),
            Type::Int(kind) => match kind {
                IntKind::I8 => "i8",
                IntKind::I16 => "i16",
                IntKind::I32 => "i32",
                IntKind::I64 => "i64",
                IntKind::U8 => "u8",
                IntKind::U16 => "u16",
                IntKind::U32 => "u32",
                IntKind::U64 => "u64",
            }
            .into(),
            Type::Float(FloatKind::F32) => "f32".into(),
            Type::Float(FloatKind::F64) => "f64".into(),
            Type::Unit => "()".into(),
            other => struct_name(other).unwrap_or_else(|| "i64".into()),
        }
    };
    let ffi_scalar = |ty: Type| {
        if ty == Type::Bool {
            "i32".to_owned()
        } else {
            scalar(ty)
        }
    };
    let mut out = String::new();
    out.push_str(&format!(
        "// Generated by `kush build --lib`: Rust bindings for the Kush library `{library_name}`.\n\
         // Link with `-l static={library_name}` (and `-lm`). Do not edit.\n\n\
         #![allow(dead_code)]\n\n"
    ));
    for (id, name) in &structs {
        let layout = &program.enums[*id];
        out.push_str(&format!(
            "/// Kush `{}` (C layout).\n#[repr(C)]\n#[derive(Clone, Copy, Debug, PartialEq)]\npub struct {name} {{\n",
            program.type_name(Type::Enum(*id))
        ));
        for (field, ty) in layout.variants[0]
            .names
            .iter()
            .zip(&layout.variants[0].fields)
        {
            out.push_str(&format!("    pub {}: {},\n", ident(field), scalar(*ty)));
        }
        out.push_str("}\n\n");
    }
    out.push_str(&format!(
        "pub mod ffi {{\n    #![allow(unused_imports)]\n    use super::*;\n\n    // The Kush runtime uses libm.\n    #[link(name = \"m\")]\n    unsafe extern \"C\" {{}}\n\n    #[link(name = \"{library_name}\", kind = \"static\")]\n    unsafe extern \"C\" {{\n"
    ));
    for export in &program.exports {
        let name = &program.functions[export.index].name;
        let mut params = Vec::new();
        for (n, ty) in &export.parameters {
            if is_bytes_ref(program, *ty) {
                params.push(format!("{}: *const u8", ident(n)));
                params.push(format!("{n}_len: i64"));
            } else if struct_name(*ty).is_some() {
                params.push(format!("{}: *const {}", ident(n), scalar(*ty)));
            } else {
                params.push(format!("{}: {}", ident(n), ffi_scalar(*ty)));
            }
        }
        let result = if struct_name(export.result).is_some() {
            params.push(format!("out: *mut {}", scalar(export.result)));
            String::new()
        } else if export.result == Type::Unit {
            String::new()
        } else {
            format!(" -> {}", ffi_scalar(export.result))
        };
        out.push_str(&format!(
            "        /// Kush `{name}`. Calls must not overlap (see `super::Library`).\n        pub fn {}({}){result};\n",
            export.symbol,
            params.join(", ")
        ));
    }
    out.push_str("    }\n}\n\n");
    out.push_str(
        "/// The right to call into the Kush library: one per process, `Send` but\n\
         /// not `Sync`, so calls never overlap.\n\
         pub struct Library(core::marker::PhantomData<core::cell::Cell<()>>);\n\n\
         static TAKEN: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);\n\n\
         impl Library {\n    /// The process's only token; `None` after the first call.\n    pub fn take() -> Option<Library> {\n        (!TAKEN.swap(true, core::sync::atomic::Ordering::AcqRel))\n            .then(|| Library(core::marker::PhantomData))\n    }\n",
    );
    for export in &program.exports {
        let name = &program.functions[export.index].name;
        let mut params = String::new();
        let mut args = Vec::new();
        for (n, ty) in &export.parameters {
            let id = ident(n);
            if is_bytes_ref(program, *ty) {
                params.push_str(&format!(", {id}: &[u8]"));
                args.push(format!("{id}.as_ptr()"));
                args.push(format!("{id}.len() as i64"));
            } else if struct_name(*ty).is_some() {
                params.push_str(&format!(", {id}: {}", scalar(*ty)));
                args.push(format!("&{id}"));
            } else if *ty == Type::Bool {
                params.push_str(&format!(", {id}: bool"));
                args.push(format!("i32::from({id})"));
            } else {
                params.push_str(&format!(", {id}: {}", scalar(*ty)));
                args.push(id);
            }
        }
        let (result, body) = if let Some(record) = struct_name(export.result) {
            args.push("out.as_mut_ptr()".into());
            (
                format!(" -> {record}"),
                format!(
                    "let mut out = core::mem::MaybeUninit::<{record}>::uninit();\n        unsafe {{\n            ffi::{}({});\n            out.assume_init()\n        }}",
                    export.symbol,
                    args.join(", ")
                ),
            )
        } else {
            let call = format!("unsafe {{ ffi::{}({}) }}", export.symbol, args.join(", "));
            match export.result {
                Type::Unit => (String::new(), call),
                Type::Bool => (" -> bool".to_owned(), format!("({call}) != 0")),
                other => (format!(" -> {}", scalar(other)), call),
            }
        };
        out.push_str(&format!(
            "    /// Kush `{name}` (`{}`).\n    pub fn {}(&self{params}){result} {{\n        {body}\n    }}\n",
            export.symbol,
            ident(name)
        ));
    }
    out.push_str("}\n");
    out
}
/// Locals whose storage address an expression may take: `&local`, a
/// borrowed temporary owner, and the root of a field or element place.
fn addressed_slots(body: &crate::executable::Block) -> std::collections::BTreeSet<usize> {
    fn root(expr: &Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => Some(*slot),
            ExprKind::Project(base, _)
            | ExprKind::PlaceIndex { base, .. }
            | ExprKind::Coerce { value: base, .. } => root(base),
            _ => None,
        }
    }
    fn walk(expr: &Expr, out: &mut std::collections::BTreeSet<usize>) {
        match &expr.kind {
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. } => {
                out.insert(*slot);
            }
            ExprKind::BorrowPlace(place) | ExprKind::PlaceIndex { base: place, .. } => {
                if let Some(slot) = root(place) {
                    out.insert(slot);
                }
            }
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, out));
    }
    let mut out = std::collections::BTreeSet::new();
    for statement in &body.statements {
        match statement {
            crate::executable::Statement::Let(_, value)
            | crate::executable::Statement::Expr(value) => walk(value, &mut out),
            crate::executable::Statement::Declare(slot) => {
                out.insert(*slot);
            }
        }
    }
    if let Some(tail) = &body.tail {
        walk(tail, &mut out);
    }
    out
}
/// A record whose fields are scalars or such records (no arrays, owned
/// storage, borrows or unions).
fn scalar_record(program: &Executable, ty: Type, depth: usize) -> bool {
    let Some(id) = ty.layout() else {
        return false;
    };
    let layout = &program.enums[id];
    depth < 8
        && layout.record
        && layout.array.is_none()
        && layout.dynamic_array.is_none()
        && layout.variants.len() == 1
        && layout.variants[0].fields.iter().all(|field| match field {
            Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Unit => {
                true
            }
            other => scalar_record(program, *other, depth + 1),
        })
}
fn aggregate_result(program: &Executable, ty: Type) -> bool {
    ty.layout().is_some() || program.width(ty) > 1
}
/// Exact C ABI scalar type for a supported bridge value. Narrow integers use
/// their real width so `cc`/C and Cranelift agree; the backend canonicalizes
/// them back to a checked Kush word at the call boundary.
fn abi_value_type(ty: Type) -> ir::Type {
    match ty {
        Type::Bool => ir::types::I32,
        Type::I64 => I64,
        Type::Int(kind) => match kind {
            IntKind::I8 => ir::types::I8,
            IntKind::I16 => ir::types::I16,
            IntKind::I32 => ir::types::I32,
            IntKind::I64 => I64,
            IntKind::U8 => ir::types::I8,
            IntKind::U16 => ir::types::I16,
            IntKind::U32 => ir::types::I32,
            IntKind::U64 => I64,
        },
        Type::Float(kind) => match kind {
            FloatKind::F32 => ir::types::F32,
            FloatKind::F64 => ir::types::F64,
        },
        // Foreign resources are opaque `void *` handles. Every other admitted
        // type is rejected by the checker before reaching the backend.
        Type::Enum(_) => I64,
        _ => I64,
    }
}
/// C ABI signature of one checked foreign import. Slices and `&str` become
/// `(const uint8_t *, int64_t)`. A fallible result becomes
/// `int64_t symbol(..., T *out)`: zero status means success and the out slot
/// holds `T`; any non-zero status is the checked `Err(i64)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PointeeKind {
    Buffer,
    Resource,
}
/// References admitted at the foreign boundary are either buffer handles
/// (`&Bytes`/`&String`/`&mut Bytes`) or opaque resource handles. The backend
/// needs the distinction to know whether to pass `(pointer, length)` or one
/// handle word.
fn foreign_pointee_kind(program: &Executable, pointer: usize) -> PointeeKind {
    match program.pointees[pointer] {
        Type::Bytes | Type::String => PointeeKind::Buffer,
        _ => PointeeKind::Resource,
    }
}
fn foreign_abi_signature(
    module: &mut CodeModule,
    program: &Executable,
    foreign: &ex::ForeignFunction,
) -> ir::Signature {
    let mut sig = module.make_signature();
    for ty in &foreign.parameters {
        match ty {
            Type::Str => {
                sig.params.push(AbiParam::new(I64));
                sig.params.push(AbiParam::new(I64));
            }
            Type::Ref(pointer) | Type::RefMut(pointer)
                if matches!(foreign_pointee_kind(program, *pointer), PointeeKind::Buffer) =>
            {
                sig.params.push(AbiParam::new(I64));
                sig.params.push(AbiParam::new(I64));
            }
            // The C ABI on x86-64 lets a callee assume that an argument
            // narrower than 32 bits arrives extended to 32; say how, so both
            // backends pass the canonical value and not a raw register.
            Type::Int(IntKind::I8 | IntKind::I16) => {
                sig.params.push(AbiParam::new(abi_value_type(*ty)).sext())
            }
            Type::Int(IntKind::U8 | IntKind::U16) => {
                sig.params.push(AbiParam::new(abi_value_type(*ty)).uext())
            }
            _ => sig.params.push(AbiParam::new(abi_value_type(*ty))),
        }
    }
    match foreign.fallible {
        Some(shape) => {
            sig.returns.push(AbiParam::new(I64));
            if shape.ok != Type::Unit {
                sig.params.push(AbiParam::new(I64));
            }
        }
        None if foreign.result == Type::Unit => {}
        None => sig
            .returns
            .push(AbiParam::new(abi_value_type(foreign.result))),
    }
    sig
}
fn emit_drop(
    builder: &mut FunctionBuilder<'_>,
    module: &mut CodeModule,
    id: FuncId,
    values: &[Value],
) {
    let reference = module.declare_func_in_func(id, builder.func);
    builder.ins().call(reference, values);
}
/// Environment capture types introduced by checked coercions. A callable
/// field adapter stores its source callable in an owned environment exactly
/// like a capturing `FnValue`, so the native backend must synthesize the same
/// environment drop function for it.
fn collect_coercion_captures(coercion: &ex::Coercion, out: &mut Vec<Vec<Type>>) {
    match coercion {
        ex::Coercion::Callable {
            capture: Some(capture),
            ..
        } => out.push(vec![capture.full()]),
        ex::Coercion::Struct { kept, .. } => {
            for (_, _, nested) in kept {
                if let Some(nested) = nested {
                    collect_coercion_captures(nested, out);
                }
            }
        }
        _ => {}
    }
}
fn collect_closure_types(program: &Executable) -> Vec<Vec<Type>> {
    // Every expression position is visited through the exhaustive child walk,
    // so a capturing closure or callable adapter nested anywhere gets its
    // environment-drop function.
    fn walk(node: &Expr, out: &mut Vec<Vec<Type>>) {
        match &node.kind {
            ExprKind::FnValue { captures, .. } if !captures.is_empty() => out.push(
                captures
                    .iter()
                    .map(|capture| capture.ty.full())
                    .collect::<Vec<_>>(),
            ),
            // A callable field adapter owns its source callable in an
            // environment; record that capture type too.
            ExprKind::Coerce { coercion, .. } => collect_coercion_captures(coercion, out),
            _ => {}
        }
        node.for_each_child(&mut |child| walk(child, out));
    }
    let mut all = Vec::new();
    for function in &program.functions {
        for statement in &function.body.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => walk(value, &mut all),
                ex::Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, &mut all);
        }
    }
    all.sort();
    all.dedup();
    all
}
/// Imported runtime helpers for checked user-allocator containers.
#[derive(Clone, Copy)]
struct AllocOps {
    block: FuncId,
    block_try: FuncId,
    context_new: FuncId,
    context_share: FuncId,
    context_release: FuncId,
    block_data: FuncId,
    box_create: FuncId,
    box_payload: FuncId,
    box_release: FuncId,
    vec_create: FuncId,
    vec_push: FuncId,
    vec_try_push: FuncId,
    vec_pop: FuncId,
    vec_len: FuncId,
    vec_get: FuncId,
    vec_set: FuncId,
    vec_clear: FuncId,
    vec_data: FuncId,
    vec_release: FuncId,
}
type DropTables = (BTreeMap<Type, FuncId>, BTreeMap<Vec<Type>, FuncId>);
/// One drop thunk per allocator-context shape. The thunk receives the state
/// block address, runs the concrete instance's checked drop glue (if any), and
/// releases the block. It is called only when the final context reference goes
/// away, after every container block has been released.
fn synthesize_context_drops(
    module: &mut CodeModule,
    program: &Executable,
    drops: &BTreeMap<Type, FuncId>,
    free: FuncId,
) -> Result<Vec<FuncId>> {
    let mut ids = Vec::new();
    for (index, spec) in program.allocator_contexts.iter().enumerate() {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(I64));
        ids.push(
            module
                .declare_function(
                    &format!("kush_context_drop_{index}"),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?,
        );
        let _ = spec;
    }
    for (index, spec) in program.allocator_contexts.iter().enumerate() {
        let id = ids[index];
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let state = builder.block_params(entry)[0];
        if program.owns(spec.state) {
            let words = (0..program.width(spec.state))
                .map(|word| {
                    builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), state, (word * 8) as i32)
                })
                .collect::<Vec<_>>();
            emit_drop(&mut builder, module, drops[&spec.state.full()], &words);
        }
        emit_drop(&mut builder, module, free, &[state]);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    Ok(ids)
}
fn synthesize_drops(
    module: &mut CodeModule,
    program: &Executable,
    free: FuncId,
    buffer_frees: (FuncId, FuncId),
    arena_release: FuncId,
    arena_box_release: FuncId,
    alloc_ops: &AllocOps,
) -> Result<DropTables> {
    let (buffer_free, bytes_free) = buffer_frees;
    let mut types = (0..program.pointees.len())
        .map(Type::Box)
        .chain((0..program.pointees.len()).map(Type::ArenaBox))
        .chain((0..program.pointees.len()).map(Type::AllocBox))
        .chain((0..program.pointees.len()).map(Type::AllocVec))
        .chain((0..program.pointees.len()).map(Type::Vec))
        .chain((0..program.pointees.len()).map(Type::Task))
        .chain((0..program.pointees.len()).map(Type::Thread))
        // Channel drop glue needs the threaded runtime.
        .chain(
            (0..program.pointees.len())
                .map(Type::Channel)
                .filter(|_| program.uses_threads),
        )
        .chain((0..program.pointees.len()).map(Type::GpuBuf))
        .chain([Type::Arena, Type::AllocatorContext])
        .chain((0..program.enums.len()).map(Type::Enum))
        .chain((0..program.unions.len()).map(Type::Union))
        .chain((0..program.dyn_object_names.len()).map(Type::DynObj))
        .chain(
            (0..program.function_types.len())
                .filter(|id| program.function_types[*id].once)
                .map(Type::Once),
        )
        .chain([Type::Bytes, Type::String])
        .filter(|ty| program.owns(*ty))
        .collect::<Vec<_>>();
    types.sort();
    types.dedup();
    let mut ids = BTreeMap::new();
    for (i, ty) in types.iter().enumerate() {
        let mut signature = module.make_signature();
        signature
            .params
            .extend((0..program.width(*ty)).map(|_| AbiParam::new(I64)));
        ids.insert(
            *ty,
            module
                .declare_function(&format!("kush_drop_{i}"), Linkage::Local, &signature)
                .map_err(error)?,
        );
    }
    // One environment drop function per distinct captured-type list. The
    // environment header stores this address, so an owning closure type does
    // not need capture metadata after checking.
    let closure_types = collect_closure_types(program);
    let mut closure_ids = BTreeMap::new();
    for (i, captures) in closure_types.iter().enumerate() {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(I64));
        closure_ids.insert(
            captures.clone(),
            module
                .declare_function(
                    &format!("kush_closure_drop_{i}"),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?,
        );
    }
    for ty in types {
        let id = ids[&ty];
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let args = builder.block_params(entry).to_vec();
        match ty {
            Type::Bytes | Type::String => {
                emit_drop(&mut builder, module, bytes_free, &args);
                builder.ins().return_(&[]);
            }
            Type::GpuBuf(_) => {
                // GPU-SUBSET: no CPU code creates a buffer yet; GPU-RUNTIME
                // replaces this with the device release.
                builder.ins().return_(&[]);
            }
            Type::Channel(_) => {
                // THREAD-CHANNELS: messages are plain data; free the channel.
                let mut signature = module.make_signature();
                signature.params.push(AbiParam::new(I64));
                let channel_free = module
                    .declare_function("kush_channel_free", Linkage::Import, &signature)
                    .map_err(error)?;
                emit_drop(&mut builder, module, channel_free, &args);
                builder.ins().return_(&[]);
            }
            Type::Box(index) | Type::ArenaBox(index) => {
                let pointee = program.pointees[index];
                if program.owns(pointee) {
                    let fields = (0..program.width(pointee))
                        .map(|i| {
                            builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                args[0],
                                (i * 8) as i32,
                            )
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&pointee.full()], &fields);
                }
                if matches!(ty, Type::ArenaBox(_)) {
                    emit_drop(&mut builder, module, arena_box_release, &args);
                } else {
                    emit_drop(&mut builder, module, free, &args);
                }
                builder.ins().return_(&[]);
            }
            Type::Arena => {
                emit_drop(&mut builder, module, arena_release, &args);
                builder.ins().return_(&[]);
            }
            Type::AllocatorContext => {
                emit_drop(&mut builder, module, alloc_ops.context_release, &args);
                builder.ins().return_(&[]);
            }
            Type::DynObj(object) => {
                // args = [member identifier, payload pointer]. The identifier
                // selects the concrete payload type; its drop runs in place,
                // then the payload allocation is released exactly once.
                let members = program.dyn_members.get(object).cloned().unwrap_or_default();
                for (index, entry) in members.iter().enumerate() {
                    let hit = builder.create_block();
                    let next = builder.create_block();
                    let condition = builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, args[0], index as i64);
                    builder.ins().brif(condition, hit, &[], next, &[]);
                    builder.switch_to_block(hit);
                    if program.owns(entry.member) {
                        let fields = (0..program.width(entry.member))
                            .map(|i| {
                                builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    args[1],
                                    (i * 8) as i32,
                                )
                            })
                            .collect::<Vec<_>>();
                        emit_drop(&mut builder, module, ids[&entry.member.full()], &fields);
                    }
                    emit_drop(&mut builder, module, free, &[args[1]]);
                    builder.ins().return_(&[]);
                    builder.switch_to_block(next);
                }
                // No registered member can reach here, but release the
                // payload allocation defensively rather than leaking it.
                emit_drop(&mut builder, module, free, &[args[1]]);
                builder.ins().return_(&[]);
            }
            Type::AllocBox(index) => {
                let pointee = program.pointees[index];
                let payload_function =
                    module.declare_func_in_func(alloc_ops.box_payload, builder.func);
                let payload_call = builder.ins().call(payload_function, &[args[0]]);
                let data = builder.inst_results(payload_call)[0];
                if program.owns(pointee) {
                    let fields = (0..program.width(pointee))
                        .map(|i| {
                            builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), data, (i * 8) as i32)
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&pointee.full()], &fields);
                }
                emit_drop(&mut builder, module, alloc_ops.box_release, &args);
                builder.ins().return_(&[]);
            }
            Type::AllocVec(index) => {
                let element = program.pointees[index];
                if program.owns(element) {
                    let width = program.width(element);
                    let length = builder.ins().load(I64, ir::MemFlagsData::new(), args[0], 0);
                    let data_function =
                        module.declare_func_in_func(alloc_ops.vec_data, builder.func);
                    let data_call = builder.ins().call(data_function, &[args[0]]);
                    let data = builder.inst_results(data_call)[0];
                    let head = builder.create_block();
                    let body = builder.create_block();
                    let done = builder.create_block();
                    builder.append_block_param(head, I64);
                    let zero = builder.ins().iconst(I64, 0);
                    builder.ins().jump(head, &[zero.into()]);
                    builder.switch_to_block(head);
                    let i = builder.block_params(head)[0];
                    let more = builder.ins().icmp(IntCC::UnsignedLessThan, i, length);
                    builder.ins().brif(more, body, &[], done, &[]);
                    builder.switch_to_block(body);
                    let stride = builder.ins().imul_imm_s(i, (width * 8) as i64);
                    let base = builder.ins().iadd(data, stride);
                    let fields = (0..width)
                        .map(|j| {
                            builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), base, (j * 8) as i32)
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&element.full()], &fields);
                    let next = builder.ins().iadd_imm_s(i, 1);
                    builder.ins().jump(head, &[next.into()]);
                    builder.switch_to_block(done);
                }
                emit_drop(&mut builder, module, alloc_ops.vec_release, &args);
                builder.ins().return_(&[]);
            }
            Type::Vec(index) => {
                let element = program.pointees[index];
                if program.owns(element) {
                    // for (i = 0; i < length; i++) drop(data[i])
                    let width = program.width(element);
                    let length = builder.ins().load(I64, ir::MemFlagsData::new(), args[0], 0);
                    let head = builder.create_block();
                    let body = builder.create_block();
                    let done = builder.create_block();
                    builder.append_block_param(head, I64);
                    let zero = builder.ins().iconst(I64, 0);
                    builder.ins().jump(head, &[zero.into()]);
                    builder.switch_to_block(head);
                    let i = builder.block_params(head)[0];
                    let more = builder.ins().icmp(IntCC::UnsignedLessThan, i, length);
                    builder.ins().brif(more, body, &[], done, &[]);
                    builder.switch_to_block(body);
                    let stride = builder.ins().imul_imm_s(i, (width * 8) as i64);
                    let base = builder.ins().iadd(args[0], stride);
                    let fields = (0..width)
                        .map(|k| {
                            builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                base,
                                (16 + k * 8) as i32,
                            )
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&element.full()], &fields);
                    let next = builder.ins().iadd_imm_s(i, 1);
                    builder.ins().jump(head, &[next.into()]);
                    builder.switch_to_block(done);
                }
                emit_drop(&mut builder, module, buffer_free, &args);
                builder.ins().return_(&[]);
            }
            Type::Enum(index) if program.unwind_functions.contains_key(&index) => {
                // PANIC-LINEAR-CLEANUP: only a panic unwinding leaves a live
                // value of this linear type to drop: its unwind function
                // takes it, with the panic word held clear meanwhile.
                let function = program.unwind_functions[&index];
                let mut signature = module.make_signature();
                signature
                    .params
                    .extend((0..program.width(Type::Enum(index))).map(|_| AbiParam::new(I64)));
                signature.returns.push(AbiParam::new(I64));
                let cleanup = module
                    .declare_function(
                        &function_symbol(program, function),
                        Linkage::Local,
                        &signature,
                    )
                    .map_err(error)?;
                let mut hold_signature = module.make_signature();
                hold_signature.returns.push(AbiParam::new(I64));
                let hold = module
                    .declare_function("kush_unwind_hold", Linkage::Import, &hold_signature)
                    .map_err(error)?;
                let mut restore_signature = module.make_signature();
                restore_signature.params.push(AbiParam::new(I64));
                let restore = module
                    .declare_function("kush_unwind_restore", Linkage::Import, &restore_signature)
                    .map_err(error)?;
                let hold = module.declare_func_in_func(hold, builder.func);
                let call = builder.ins().call(hold, &[]);
                let held = builder.inst_results(call)[0];
                let cleanup = module.declare_func_in_func(cleanup, builder.func);
                builder.ins().call(cleanup, &args);
                emit_drop(&mut builder, module, restore, &[held]);
                builder.ins().return_(&[]);
            }
            Type::Enum(index) => {
                if let Some(foreign) = program.enums[index].foreign.clone() {
                    // The one-word handle is released by the trusted foreign
                    // contract exactly once. Linear foreign resources cannot be
                    // implicitly dropped, so this path only runs for affine
                    // resources (or when a linear value is explicitly consumed
                    // by a compiled drop after a checked transfer).
                    let mut signature = module.make_signature();
                    signature.params.push(AbiParam::new(I64));
                    let release = module
                        .declare_function(&foreign.release, Linkage::Import, &signature)
                        .map_err(error)?;
                    emit_drop(&mut builder, module, release, &[args[0]]);
                    builder.ins().return_(&[]);
                } else if let Some((element, capacity)) = program.enums[index].dynamic_array {
                    if program.owns(element) {
                        // The runtime length is word zero; fields at or beyond
                        // it are uninitialized and must never be interpreted.
                        // Words arrive as function arguments, so the capacity
                        // bound is expanded into a guard per slot instead of a
                        // dynamic index into SSA values.
                        let width = program.width(element);
                        let length = args[0];
                        for slot in (0..capacity).rev() {
                            let active = builder.ins().icmp_imm_s(
                                IntCC::UnsignedGreaterThan,
                                length,
                                slot as i64,
                            );
                            let body = builder.create_block();
                            let next = builder.create_block();
                            builder.ins().brif(active, body, &[], next, &[]);
                            builder.switch_to_block(body);
                            emit_drop(
                                &mut builder,
                                module,
                                ids[&element.full()],
                                &args[1 + slot * width..1 + (slot + 1) * width],
                            );
                            builder.ins().jump(next, &[]);
                            builder.switch_to_block(next);
                        }
                    }
                    builder.ins().return_(&[]);
                } else {
                    for (tag, variant) in program.enums[index].variants.iter().enumerate() {
                        let hit = builder.create_block();
                        let next = builder.create_block();
                        let condition = if let Some(niche) = program.enums[index].niche() {
                            let (cc, constant) = decoder_test(niche.decoder(tag));
                            builder.ins().icmp_imm_s(cc, args[0], constant)
                        } else if program.enums[index].tag_words() == 0 {
                            builder.ins().iconst(ir::types::I8, 1)
                        } else {
                            builder.ins().icmp_imm_s(IntCC::Equal, args[0], tag as i64)
                        };
                        builder.ins().brif(condition, hit, &[], next, &[]);
                        builder.switch_to_block(hit);
                        let mut offset = program.enums[index].tag_words();
                        let mut fields = Vec::new();
                        for ty in &variant.fields {
                            fields.push((*ty, offset));
                            offset += program.width(*ty);
                        }
                        for (ty, offset) in fields.into_iter().rev() {
                            if program.owns(ty) {
                                emit_drop(
                                    &mut builder,
                                    module,
                                    ids[&ty.full()],
                                    &args[offset..offset + program.width(ty)],
                                );
                            }
                        }
                        builder.ins().return_(&[]);
                        builder.switch_to_block(next);
                    }
                    builder.ins().trap(TrapCode::unwrap_user(2));
                }
            }
            Type::Union(index) => {
                for (tag, member) in program.unions[index].members.iter().enumerate() {
                    let hit = builder.create_block();
                    let next = builder.create_block();
                    let condition = builder.ins().icmp_imm_s(IntCC::Equal, args[0], tag as i64);
                    builder.ins().brif(condition, hit, &[], next, &[]);
                    builder.switch_to_block(hit);
                    if program.owns(*member) {
                        emit_drop(
                            &mut builder,
                            module,
                            ids[&member.full()],
                            &args[1..1 + program.width(*member)],
                        );
                    }
                    builder.ins().return_(&[]);
                    builder.switch_to_block(next);
                }
                builder.ins().trap(TrapCode::unwrap_user(2));
            }
            Type::Once(_) => {
                // args = [code, environment]. A noncapturing function coerced to
                // once has a null environment and owns nothing.
                let environment = args[1];
                let present = builder.ins().icmp_imm_s(IntCC::NotEqual, environment, 0);
                let close = builder.create_block();
                let done = builder.create_block();
                builder.ins().brif(present, close, &[], done, &[]);
                builder.switch_to_block(close);
                let drop = builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), environment, 0);
                let signature = {
                    let mut signature = module.make_signature();
                    signature.params.push(AbiParam::new(I64));
                    signature
                };
                let signature = builder.import_signature(signature);
                builder.ins().call_indirect(signature, drop, &[environment]);
                builder.ins().return_(&[]);
                builder.switch_to_block(done);
                builder.ins().return_(&[]);
            }
            Type::Task(_) | Type::Thread(_) => {
                // A task handle owns no heap cell. Scope completion joins it.
                builder.ins().return_(&[]);
            }
            _ => unreachable!(),
        }
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    for (captures, id) in closure_ids.clone() {
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let environment = builder.block_params(entry)[0];
        let mut positions = Vec::with_capacity(captures.len());
        let mut offset = 8;
        for ty in &captures {
            positions.push((*ty, offset));
            offset += (program.width(*ty) * 8) as i32;
        }
        for (ty, offset) in positions.into_iter().rev() {
            if program.owns(ty) {
                let values = (0..program.width(ty))
                    .map(|i| {
                        builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            environment,
                            offset + (i * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                emit_drop(&mut builder, module, ids[&ty.full()], &values);
            }
        }
        emit_drop(&mut builder, module, free, &[environment]);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    Ok((ids, closure_ids))
}
fn collect_task_types(program: &Executable) -> Vec<usize> {
    fn walk(node: &Expr, out: &mut Vec<usize>) {
        if let ExprKind::TaskSpawn { body, .. } = &node.kind
            && let Type::Once(id) = body.ty
        {
            out.push(id);
        }
        node.for_each_child(&mut |child| walk(child, out));
    }
    let mut ids = Vec::new();
    for function in &program.functions {
        for statement in &function.body.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => walk(value, &mut ids),
                ex::Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, &mut ids);
        }
    }
    ids.sort_unstable();
    ids.dedup();
    ids
}
/// Build the native task entry wrappers. A wrapper always has the C ABI
/// `(code, env, result_ptr) -> ()`, so the runtime can call a statically or
/// dynamically selected once callable without knowing its signature.
fn synthesize_task_wrappers(
    module: &mut CodeModule,
    program: &Executable,
    types: &[usize],
    drops: &BTreeMap<Type, FuncId>,
) -> Result<(BTreeMap<usize, FuncId>, BTreeMap<Type, FuncId>)> {
    let mut pointer_drops = BTreeMap::new();
    for id in types {
        let result = program.function_types[*id].result;
        if program.owns(result) && !pointer_drops.contains_key(&result.full()) {
            let mut signature = module.make_signature();
            signature.params.push(AbiParam::new(I64));
            let function = module
                .declare_function(
                    &format!("kush_task_drop_{}", pointer_drops.len()),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?;
            let mut context = module.make_context();
            context.func.signature = module
                .declarations()
                .get_function_decl(function)
                .signature
                .clone();
            let mut fc = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            let pointer = builder.block_params(entry)[0];
            let width = program.width(result);
            let words = (0..width)
                .map(|i| {
                    builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect::<Vec<_>>();
            emit_drop(&mut builder, module, drops[&result.full()], &words);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize(module.target_config());
            module
                .define_function(function, &mut context)
                .map_err(error)?;
            pointer_drops.insert(result.full(), function);
        }
    }
    let mut wrappers = BTreeMap::new();
    for id in types {
        let signature = &program.function_types[*id];
        let result = signature.result;
        let aggregate = aggregate_result(program, result);
        let mut wrapper_signature = module.make_signature();
        wrapper_signature
            .params
            .extend((0..3).map(|_| AbiParam::new(I64)));
        let wrapper = module
            .declare_function(
                &format!("kush_task_wrapper_{id}"),
                Linkage::Local,
                &wrapper_signature,
            )
            .map_err(error)?;
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(wrapper)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let params = builder.block_params(entry).to_vec();
        let (code, env, result_pointer) = (params[0], params[1], params[2]);
        let mut body_signature = module.make_signature();
        if aggregate {
            body_signature.params.push(AbiParam::new(I64));
        }
        body_signature.params.push(AbiParam::new(I64));
        if !aggregate {
            body_signature.returns.push(AbiParam::new(I64));
        }
        let body_signature = builder.import_signature(body_signature);
        let mut arguments = Vec::new();
        if aggregate {
            arguments.push(result_pointer);
        }
        arguments.push(env);
        let call = builder
            .ins()
            .call_indirect(body_signature, code, &arguments);
        if !aggregate {
            let value = builder.inst_results(call)[0];
            builder
                .ins()
                .store(ir::MemFlagsData::new(), value, result_pointer, 0);
        }
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module
            .define_function(wrapper, &mut context)
            .map_err(error)?;
        wrappers.insert(*id, wrapper);
    }
    Ok((wrappers, pointer_drops))
}
struct Tracked {
    active: Variable,
    words: Vec<Variable>,
    ty: Type,
    /// Stack storage for a pinned owning local. Reads of the tracked value at
    /// cleanup go through this location so an in-place `&mut` mutation is
    /// observed exactly once.
    location: Option<Value>,
}
type Words = Vec<Value>;
#[derive(Debug)]
enum ScalarCallback {
    Input,
    Constant(i64),
    Bitwise(Kind, Box<Self>, Box<Self>),
}
impl ScalarCallback {
    fn expression(expr: &Expr, budget: &mut usize) -> Option<Self> {
        if *budget == 0 || expr.ty != Type::I64 || expr.resource.is_some() {
            return None;
        }
        *budget -= 1;
        match &expr.kind {
            ExprKind::Local(0) | ExprKind::Peek(0) => Some(Self::Input),
            ExprKind::Constant(value) => Some(Self::Constant(*value)),
            ExprKind::Binary(op @ (Kind::Amp | Kind::Pipe | Kind::Caret), left, right) => {
                Some(Self::Bitwise(
                    op.clone(),
                    Box::new(Self::expression(left, budget)?),
                    Box::new(Self::expression(right, budget)?),
                ))
            }
            _ => None,
        }
    }
    fn callback(program: &Executable, callback: &Expr) -> Option<Self> {
        let ExprKind::FnValue { function, captures } = &callback.kind else {
            return None;
        };
        let Type::Fn(signature) = callback.ty else {
            return None;
        };
        let signature = &program.function_types[signature];
        let function = &program.functions[*function];
        if !captures.is_empty()
            || signature.effects != 0
            || signature.parameters != [Type::I64]
            || signature.result != Type::I64
            || signature.once
            || signature.linear
            || signature.parameter_erased(0)
            || signature.result_erased()
            || function.closure.is_some()
            || function.parameters != 1
            || function.locals.len() != 1
            || function.locals[0].ty != Type::I64
            || function.locals[0].grade.is_some_and(Grade::is_zero)
            || function.result_grade.is_some_and(Grade::is_zero)
            || function.locals[0].pinned
            || function.locals[0].mutable
            || function.result != Type::I64
            || !function.resources.is_empty()
            || !function.body.statements.is_empty()
        {
            return None;
        }
        Self::expression(function.body.tail.as_deref()?, &mut 32)
    }
    fn emit(&self, builder: &mut FunctionBuilder<'_>, input: Value) -> Value {
        match self {
            Self::Input => input,
            Self::Constant(value) => builder.ins().iconst(I64, *value),
            Self::Bitwise(op, left, right) => {
                let left = left.emit(builder, input);
                let right = right.emit(builder, input);
                match op {
                    Kind::Amp => builder.ins().band(left, right),
                    Kind::Pipe => builder.ins().bor(left, right),
                    Kind::Caret => builder.ins().bxor(left, right),
                    _ => unreachable!("validated scalar callback operator"),
                }
            }
        }
    }
}

/// PANIC-UNWIND-NATIVE: runtime functions whose failed preconditions return
/// with the panic word set (KUSH_FAIL in the runtime) when a catch boundary
/// is active; generated code tests the word after calling them.
const FAILING_RUNTIME: &[&str] = &[
    "kush_bytes_get",
    "kush_bytes_push",
    "kush_bytes_push_reserved",
    "kush_bytes_with_capacity",
    "kush_vec_get",
    "kush_vec_set",
    "kush_vec_element",
    "kush_vec_with_capacity",
    "kush_str_byte_at",
    "kush_utf8_scalar_at",
    "kush_utf8_scalar_len",
    "kush_str_set_scalar",
    "kush_alloc_vec_set",
    "kush_alloc_vec_pop",
    "kush_task_scope_begin",
    "kush_print_i64",
    "kush_print_u64",
    "kush_print_f64",
    "kush_print_f32",
];
struct Generator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    module: &'b mut CodeModule,
    ids: &'b [FuncId],
    foreign_ids: &'b [Option<FuncId>],
    program: &'b Executable,
    codegen: CodegenOptions,
    // Runtime-guarded descriptor facts, scoped to one versioned loop.
    /// Slice locals whose layout a specialized copy of a loop assumes:
    /// slot to (stride in bytes, byte flag).
    slice_layouts: BTreeMap<usize, (i64, i64)>,
    /// Element accesses (by [`deferred::key`]) a deferred chunk has proved
    /// in range; they are emitted without checks.
    proved_accesses: std::collections::BTreeSet<usize>,
    /// The `Slice.set` being lowered is one of `proved_accesses`.
    store_proved: bool,
    // Dominating signed `index < length` tests, identified by SSA value.
    upper_bounds: Vec<(Value, Value)>,
    /// Vector locals whose length and capacity a loop keeps in variables:
    /// slot to (length, capacity). See [`Generator::lower_while`].
    vec_shadows: BTreeMap<usize, (Variable, Variable)>,
    /// Push expressions (by address) registered for a shadowed slot, and the
    /// shadow of the push being lowered right now.
    pending_pushes: Vec<(usize, usize)>,
    push_shadow: Option<(Variable, Variable)>,
    print: FuncId,
    stage_compile: FuncId,
    print_u64: FuncId,
    print_f64: FuncId,
    print_f32: FuncId,
    float_from_int: FuncId,
    int_exact_in_float: FuncId,
    float_to_int: FuncId,
    float_int_present: FuncId,
    float_rem: FuncId,
    panic: FuncId,
    /// PANIC-UNWIND-NATIVE: `kush_unwind_panic`, and the runtime imports
    /// that may return with the panic word set (docs/panic-unwinding.md).
    unwind_panic: FuncId,
    /// PANIC-UNWIND-USE: raise again the panic of a joined task or thread,
    /// and the `Task.catch` depth counter.
    unwind_rethrow: FuncId,
    catch_enter: FuncId,
    catch_leave: FuncId,
    failing: std::collections::BTreeSet<FuncId>,
    /// Set while an unwind exit is emitted: its own runtime calls are not
    /// tested again.
    unwind_emitting: bool,
    /// PROOF-FUZZ hooks, in fuzz builds only.
    fuzz: Option<FuzzHooks>,
    /// Obligation sites entered by the expression being lowered; `expr`
    /// leaves them once the checked operation is done.
    fuzz_depth: usize,
    variables: Vec<Vec<Variable>>,
    /// Stack storage for inline-array locals so slice views can alias the real
    /// local storage (needed for `&mut [T]` write-back).
    locations: Vec<Option<Value>>,
    result: Type,
    return_pointer: Option<Value>,
    bytes_from: FuncId,
    read_all: FuncId,
    read_line: FuncId,
    read_chunk: FuncId,
    write: FuncId,
    host_ops: &'b BTreeMap<HostOp, FuncId>,
    bytes_ops: &'b BTreeMap<BytesOp, FuncId>,
    string_validate: FuncId,
    string_scalar_len: FuncId,
    string_scalar_at: FuncId,
    str_scalar_len: FuncId,
    str_byte_at: FuncId,
    str_scalar_at: FuncId,
    str_to_string: FuncId,
    /// `&mut str` writes: ASCII upper case, ASCII lower case, set_scalar.
    str_writes: [FuncId; 3],
    vec_ops: &'b BTreeMap<VecOp, FuncId>,
    vec_element: FuncId,
    /// (continue target, break target, break carries a value, handler depth at
    /// loop entry). Break/continue restore the handler depth so a dynamic
    /// handler frame inside the body cannot survive an early loop exit.
    loops: Vec<(ir::Block, ir::Block, bool, Option<Variable>)>,
    /// (exit join, finish block, handler depth at entry) of each enclosing
    /// lowered suspendable region; `RegionExit` leaves the innermost one.
    regions: Vec<(Option<ir::Block>, Option<ir::Block>, Option<Variable>)>,
    /// Enclosing `AbortScope`s: label, the block receiving the payload, and
    /// the handler-stack depth at entry.
    aborts: Vec<AbortTarget>,
    /// The runtime's `kush_abort_word`.
    abort_word: DataId,
    allocate: FuncId,
    try_allocate: FuncId,
    grow: FuncId,
    try_grow: FuncId,
    try_bytes_with_capacity: FuncId,
    free: FuncId,
    arena_new: FuncId,
    arena_new_with_strategy: FuncId,
    arena_alloc: FuncId,
    arena_try_alloc: FuncId,
    arena_box_release: FuncId,
    alloc_ops: &'b AllocOps,
    vec_restride: FuncId,
    note_reuse: FuncId,
    drops: &'b BTreeMap<Type, FuncId>,
    context_drops: &'b [FuncId],
    closure_drops: &'b BTreeMap<Vec<Type>, FuncId>,
    task_spawn: FuncId,
    task_join: FuncId,
    task_cancel: FuncId,
    task_yield: FuncId,
    task_check_cancel: FuncId,
    task_scope_begin: FuncId,
    task_cancel_scope: FuncId,
    task_scope_end: FuncId,
    thread_spawn: FuncId,
    thread_join: FuncId,
    thread_scope_begin: FuncId,
    thread_scope_end: FuncId,
    /// `kush_abort_word_address`: the calling thread's abort word.
    abort_word_local: FuncId,
    channel_new: FuncId,
    channel_send: FuncId,
    channel_recv: FuncId,
    channel_close: FuncId,
    handler_depth: FuncId,
    /// Continuation stack of multishot tokens (`kush_kstack_*`).
    kstack_push: FuncId,
    kstack_mark: FuncId,
    kstack_restore: FuncId,
    handler_restore: FuncId,
    handler_push: FuncId,
    handler_pop: FuncId,
    handler_lookup: FuncId,
    handler_redirect: FuncId,
    /// Entry handler-stack depth for this function; every return restores it so
    /// an early `return` cannot leave a dynamic handler frame visible.
    handler_base: Option<Variable>,
    task_wrappers: &'b BTreeMap<usize, FuncId>,
    task_pointer_drops: &'b BTreeMap<Type, FuncId>,
    tracked: Vec<Tracked>,
    function_index: usize,
    /// The innermost loop whose overflow panics are deferred to its exit.
    deferred: Option<DeferredLoop>,
    /// FND-MIR: the cleanup block a panic at the current MIR statement or
    /// terminator unwinds to; `None` leaves the function directly.
    mir_unwind: Option<ir::Block>,
}
/// State of one loop lowered with deferred overflow checks; see
/// [`deferred`] for the conditions and the argument that this is unobservable.
struct DeferredLoop {
    plan: deferred::Plan,
    /// Sign bit set once any `Exact` operation has overflowed.
    sticky: Variable,
    /// OR of the magnitude words of each tracked operand.
    leaves: BTreeMap<usize, Variable>,
    /// The chunk's loop test: counter slot, comparison, limit.
    limit: (usize, IntCC, Value),
}
/// An enclosing `AbortScope` during code generation.
#[derive(Clone, Copy)]
struct AbortTarget {
    label: usize,
    /// Receives the payload words and runs the handler.
    aborted: ir::Block,
    /// Handler-stack depth before the scope pushed anything.
    depth: Option<Variable>,
    /// Payload buffer of a declared operation's activation; its address is
    /// the activation's abort word.
    buffer: Option<Value>,
    width: usize,
}
macro_rules! lower {
    ($e:expr) => {
        match $e {
            Some(v) => v,
            None => return None,
        }
    };
}
impl Generator<'_, '_> {
    fn track(&mut self, id: Option<usize>, values: &[Value]) {
        if let Some(id) = id {
            for (v, value) in self.tracked[id].words.iter().zip(values) {
                self.builder.def_var(*v, *value);
            }
            let one = self.builder.ins().iconst(ir::types::I8, 1);
            self.builder.def_var(self.tracked[id].active, one);
        }
    }
    fn deactivate(&mut self, id: Option<usize>) {
        if let Some(id) = id {
            let zero = self.builder.ins().iconst(ir::types::I8, 0);
            self.builder.def_var(self.tracked[id].active, zero);
        }
    }
    fn consume(&mut self, expr: &Expr) {
        self.deactivate(expr.resource);
    }
    /// A grade-zero binding is not materialized at runtime. Its initializer is
    /// still evaluated for strict effects, but no store, local resource, or
    /// read is emitted for the binding.
    fn erased_local(&self, slot: usize) -> bool {
        self.program.functions[self.function_index].locals[slot]
            .grade
            .is_some_and(Grade::is_zero)
    }
    fn activate_local(&mut self, slot: usize) {
        let location = self.locations[slot];
        let values = if let Some(pointer) = location {
            let width = self.variables[slot].len();
            self.load_words(pointer, 0, width)
        } else {
            self.variables[slot]
                .iter()
                .map(|v| self.builder.use_var(*v))
                .collect::<Vec<_>>()
        };
        let id = self.program.functions[self.function_index].local_resources[slot];
        self.track(id, &values);
        if let Some(id) = id {
            self.tracked[id].location = location;
        }
    }
    fn drop_value(&mut self, ty: Type, values: &[Value]) {
        if self.program.owns(ty) {
            emit_drop(
                &mut self.builder,
                self.module,
                self.drops[&ty.full()],
                &values[..self.program.width(ty)],
            );
        }
    }
    fn cleanup(&mut self, id: Option<usize>) {
        if let Some(id) = id {
            let active = self.builder.use_var(self.tracked[id].active);
            let yes = self.builder.create_block();
            let no = self.builder.create_block();
            self.builder.ins().brif(active, yes, &[], no, &[]);
            self.builder.switch_to_block(yes);
            self.deactivate(Some(id));
            let values = if let Some(pointer) = self.tracked[id].location {
                let width = self.program.width(self.tracked[id].ty);
                self.load_words(pointer, 0, width)
            } else {
                self.tracked[id]
                    .words
                    .iter()
                    .map(|v| self.builder.use_var(*v))
                    .collect::<Vec<_>>()
            };
            // A linear type with an unwind cleanup is owned: its drop glue
            // calls the cleanup (PANIC-LINEAR-CLEANUP).
            self.drop_value(self.tracked[id].ty, &values);
            self.jump(no, &[]);
            self.builder.switch_to_block(no);
        }
    }
    fn abort_target(&self, label: usize) -> AbortTarget {
        *self
            .aborts
            .iter()
            .rev()
            .find(|target| target.label == label)
            .expect("an abort exit is inside its scope")
    }
    fn abort_word_address(&mut self) -> Value {
        if self.program.uses_threads {
            return self.runtime_call(self.abort_word_local, &[]);
        }
        let data = self
            .module
            .declare_data_in_func(self.abort_word, self.builder.func);
        self.builder.ins().symbol_value(I64, data)
    }
    /// Leave the function on an abort path: the caller ignores the result.
    fn return_dummy(&mut self) {
        let function = &self.program.functions[self.function_index];
        let width = if function.result_grade.is_some_and(Grade::is_zero) {
            0
        } else {
            self.program.width(function.result)
        };
        let words = (0..width).map(|_| self.constant(0)).collect::<Vec<_>>();
        self.return_value(&words);
    }
    fn cleanup_all(&mut self) {
        for id in (0..self.tracked.len()).rev() {
            self.cleanup(Some(id));
        }
    }
    fn constant(&mut self, n: i64) -> Value {
        self.builder.ins().iconst(I64, n)
    }
    fn scalar(&mut self, expr: &Expr) -> Option<Value> {
        self.expr(expr).map(|values| values[0])
    }
    /// Interpret a one-word float representation as a hardware float value.
    fn float_value(&mut self, kind: FloatKind, bits: Value) -> Value {
        match kind {
            FloatKind::F32 => {
                let low = self.builder.ins().ireduce(ir::types::I32, bits);
                self.builder
                    .ins()
                    .bitcast(ir::types::F32, ir::MemFlagsData::new(), low)
            }
            FloatKind::F64 => {
                self.builder
                    .ins()
                    .bitcast(ir::types::F64, ir::MemFlagsData::new(), bits)
            }
        }
    }
    /// Store a hardware float back into its canonical one-word bit form.
    fn float_bits(&mut self, kind: FloatKind, value: Value) -> Value {
        match kind {
            FloatKind::F32 => {
                let low =
                    self.builder
                        .ins()
                        .bitcast(ir::types::I32, ir::MemFlagsData::new(), value);
                self.builder.ins().uextend(I64, low)
            }
            FloatKind::F64 => self
                .builder
                .ins()
                .bitcast(I64, ir::MemFlagsData::new(), value),
        }
    }
    fn float_binary(&mut self, kind: FloatKind, op: &Kind, a: Value, b: Value) -> Value {
        let comparison = match op {
            Kind::Lt => Some(FloatCC::LessThan),
            Kind::Le => Some(FloatCC::LessThanOrEqual),
            Kind::Gt => Some(FloatCC::GreaterThan),
            Kind::Ge => Some(FloatCC::GreaterThanOrEqual),
            Kind::EqEq => Some(FloatCC::Equal),
            Kind::Ne => Some(FloatCC::NotEqual),
            _ => None,
        };
        if let Some(condition) = comparison {
            let value = self.builder.ins().fcmp(condition, a, b);
            return self.builder.ins().uextend(I64, value);
        }
        let result = match op {
            Kind::Plus => self.builder.ins().fadd(a, b),
            Kind::Minus => self.builder.ins().fsub(a, b),
            Kind::Star => self.builder.ins().fmul(a, b),
            Kind::Slash => self.builder.ins().fdiv(a, b),
            Kind::Percent => {
                let is_f32 = self.constant(i64::from(matches!(kind, FloatKind::F32)));
                let a = self.float_bits(kind, a);
                let b = self.float_bits(kind, b);
                return self.runtime_call(self.float_rem, &[a, b, is_f32]);
            }
            _ => unreachable!("checked float operator"),
        };
        self.float_bits(kind, result)
    }
    /// Integer -> float payload bits, rounding to nearest-even.
    fn float_from_integer(&mut self, source: IntKind, target: FloatKind, value: Value) -> Value {
        let signed = self.constant(i64::from(source.signed()));
        let wide = self.runtime_call(self.float_from_int, &[value, signed]);
        match target {
            FloatKind::F64 => wide,
            FloatKind::F32 => {
                let wide = self.float_value(FloatKind::F64, wide);
                let narrow = self.builder.ins().fdemote(ir::types::F32, wide);
                self.float_bits(FloatKind::F32, narrow)
            }
        }
    }
    fn float_builtin(&mut self, op: crate::float::FloatOp, values: &[Value], ty: Type) -> Words {
        use crate::float::FloatOp;
        let word = values[0];
        let option =
            |g: &mut Self, present: Value, payload: Value, some: usize, none: usize| -> Words {
                g.optional_words(ty, present, &[payload], some, none)
            };
        match op {
            FloatOp::Abs(kind) => {
                let mask = match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                };
                let mask = self.constant(mask);
                vec![self.builder.ins().band(word, mask)]
            }
            FloatOp::Sqrt(kind) => {
                let value = self.float_value(kind, word);
                let result = self.builder.ins().sqrt(value);
                vec![self.float_bits(kind, result)]
            }
            FloatOp::IsNan(kind) => {
                let value = self.float_value(kind, word);
                let result = self.builder.ins().fcmp(FloatCC::Unordered, value, value);
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::IsInfinite(kind) => {
                let mask = self.constant(match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                });
                let magnitude = self.builder.ins().band(word, mask);
                let result = self.builder.ins().icmp_imm_u(
                    IntCC::Equal,
                    magnitude,
                    kind.infinity_bits() as i64,
                );
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::IsFinite(kind) => {
                let mask = self.constant(match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                });
                let magnitude = self.builder.ins().band(word, mask);
                let result = self.builder.ins().icmp_imm_u(
                    IntCC::UnsignedLessThan,
                    magnitude,
                    kind.infinity_bits() as i64,
                );
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::FromInt { source, target } | FloatOp::FromIntRounded { source, target } => {
                vec![self.float_from_integer(source, target, word)]
            }
            FloatOp::TryFromInt {
                source,
                target,
                some_tag,
                none_tag,
            } => {
                let payload = self.float_from_integer(source, target, word);
                let signed = self.constant(i64::from(source.signed()));
                let mantissa = self.constant(i64::from(target.mantissa_bits()));
                let exact = self.runtime_call(self.int_exact_in_float, &[word, signed, mantissa]);
                let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, exact, 0);
                option(self, present, payload, some_tag, none_tag)
            }
            FloatOp::ToF64(source) => match source {
                FloatKind::F64 => vec![word],
                FloatKind::F32 => {
                    let value = self.float_value(FloatKind::F32, word);
                    let wide = self.builder.ins().fpromote(ir::types::F64, value);
                    vec![self.float_bits(FloatKind::F64, wide)]
                }
            },
            FloatOp::TryToF32 {
                source,
                some_tag,
                none_tag,
            } => match source {
                FloatKind::F32 => {
                    let one = self.constant(1);
                    let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, one, 0);
                    option(self, present, word, some_tag, none_tag)
                }
                FloatKind::F64 => {
                    let wide = self.float_value(FloatKind::F64, word);
                    let narrow = self.builder.ins().fdemote(ir::types::F32, wide);
                    let payload = self.float_bits(FloatKind::F32, narrow);
                    let wide_mask = self.constant(i64::MAX);
                    let narrow_mask = self.constant(0x7fff_ffffi64);
                    let wide_magnitude = self.builder.ins().band(word, wide_mask);
                    let narrow_magnitude = self.builder.ins().band(payload, narrow_mask);
                    let wide_finite = self.builder.ins().icmp_imm_u(
                        IntCC::UnsignedLessThan,
                        wide_magnitude,
                        0x7ff0_0000_0000_0000,
                    );
                    let narrow_finite = self.builder.ins().icmp_imm_u(
                        IntCC::UnsignedLessThan,
                        narrow_magnitude,
                        0x7f80_0000,
                    );
                    // Reject only a finite wide value that overflowed to an
                    // f32 infinity. NaN and infinity are representable.
                    let overflowed = self.builder.ins().band_not(wide_finite, narrow_finite);
                    let present = self.builder.ins().icmp_imm_s(IntCC::Equal, overflowed, 0);
                    option(self, present, payload, some_tag, none_tag)
                }
            },
            FloatOp::TryToInt {
                source,
                target,
                some_tag,
                none_tag,
            } => {
                let wide = match source {
                    FloatKind::F64 => word,
                    FloatKind::F32 => {
                        let value = self.float_value(FloatKind::F32, word);
                        let wide = self.builder.ins().fpromote(ir::types::F64, value);
                        self.float_bits(FloatKind::F64, wide)
                    }
                };
                let target_index = self.constant(target.index());
                let present = self.runtime_call(self.float_int_present, &[wide, target_index]);
                let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, present, 0);
                let payload = self.runtime_call(self.float_to_int, &[wide, target_index]);
                option(self, present, payload, some_tag, none_tag)
            }
        }
    }
    fn assign(&mut self, slot: usize, values: &[Value]) {
        for (variable, value) in self.variables[slot].iter().zip(values) {
            self.builder.def_var(*variable, *value);
        }
        if let Some(pointer) = self.locations[slot] {
            for (index, value) in values.iter().enumerate() {
                self.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    pointer,
                    (index * 8) as i32,
                );
            }
        }
    }
    /// Callees restore their own local frames. If this function never installs
    /// a handler, neither its returns nor loop exits can strand a local frame.
    fn capture_handler_depth(&mut self) -> Option<Variable> {
        self.handler_base?;
        let depth = self.builder.declare_var(I64);
        let value = self.runtime_call(self.handler_depth, &[]);
        self.builder.def_var(depth, value);
        Some(depth)
    }
    fn restore_handler_depth(&mut self, depth: Option<Variable>) {
        if let Some(depth) = depth {
            let value = self.builder.use_var(depth);
            self.runtime_void(self.handler_restore, &[value]);
        }
    }
    fn return_value(&mut self, values: &[Value]) {
        self.restore_handler_depth(self.handler_base);
        if let Some(pointer) = self.return_pointer {
            for (index, value) in values.iter().enumerate() {
                self.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    pointer,
                    (index * 8) as i32,
                );
            }
            self.builder.ins().return_(&[]);
        } else {
            self.builder.ins().return_(values);
        }
    }
    fn jump(&mut self, block: ir::Block, values: &[Value]) {
        let values = values.iter().copied().map(Into::into).collect::<Vec<_>>();
        self.builder.ins().jump(block, &values);
    }
    fn join(&mut self, ty: Type) -> Option<ir::Block> {
        if ty == Type::Never {
            return None;
        }
        let block = self.builder.create_block();
        for _ in 0..self.program.width(ty) {
            self.builder.append_block_param(block, I64);
        }
        Some(block)
    }
    fn runtime_call(&mut self, id: FuncId, values: &[Value]) -> Value {
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(callee, values);
        let result = self.builder.inst_results(call)[0];
        if self.failing.contains(&id) {
            self.test_panic();
        }
        result
    }
    fn runtime_void(&mut self, id: FuncId, values: &[Value]) {
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        self.builder.ins().call(callee, values);
        if self.failing.contains(&id) {
            self.test_panic();
        }
    }
    /// Resolve a dynamic-object member identifier and call the checked method
    /// selected for that member. Owned dispatch loads the payload and releases
    /// its allocation before the call; borrowed dispatch passes the payload
    /// pointer directly so an owning/linear member is never copied.
    /// Map an owned object's member identifier from `from`'s member table to
    /// `to`'s through a compare-and-select chain. The payload pointer word is
    /// kept, so nothing is allocated, copied, or released.
    fn dyn_upcast(&mut self, from: usize, to: usize, values: &[Value]) -> Words {
        let source = self
            .program
            .dyn_members
            .get(from)
            .cloned()
            .unwrap_or_default();
        let target = self
            .program
            .dyn_members
            .get(to)
            .cloned()
            .unwrap_or_default();
        let mut mapped = self.constant(0);
        for (index, entry) in source.iter().enumerate() {
            let position = target
                .iter()
                .position(|candidate| candidate.member == entry.member)
                .expect("the checker registers every upcast member in the target object");
            let hit = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, values[0], index as i64);
            let value = self.constant(position as i64);
            mapped = self.builder.ins().select(hit, value, mapped);
        }
        vec![mapped, values[1]]
    }
    fn dyn_call(&mut self, spec_index: usize, values: Words) -> Words {
        let spec = self.program.dyn_calls[spec_index].clone();
        let members = self
            .program
            .dyn_members
            .get(spec.object)
            .cloned()
            .unwrap_or_default();
        let result_ty = if spec.result_grade.is_some_and(Grade::is_zero) {
            Type::Unit
        } else {
            spec.result
        };
        let join = self.join(result_ty);
        let owned = spec.mode == ReceiverMode::Owned;
        let member_id = if owned {
            values[0]
        } else {
            self.builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), values[0], 0)
        };
        let argument_start = if owned { 2 } else { 1 };
        for (index, entry) in members.iter().enumerate() {
            let hit = self.builder.create_block();
            let next = self.builder.create_block();
            let condition = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, member_id, index as i64);
            self.builder.ins().brif(condition, hit, &[], next, &[]);
            self.builder.switch_to_block(hit);
            let mut arguments = if owned {
                let pointer = values[1];
                let payload = (0..self.program.width(entry.member))
                    .map(|word| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (word * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                emit_drop(&mut self.builder, self.module, self.free, &[pointer]);
                payload
            } else {
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 8);
                vec![pointer]
            };
            arguments.extend(
                self.physical_dyn_arguments(&spec.parameter_grades, &values[argument_start..]),
            );
            let function = *entry
                .methods
                .get(&spec.key)
                .expect("checked dynamic member registers every object-safe trait method");
            let out = self.function_call(function, arguments);
            if let Some(join) = join {
                self.jump(join, &out);
            }
            self.builder.switch_to_block(next);
        }
        // No registered member can reach this point; a trait object value is
        // always created by a coercion that registered its member.
        self.abort();
        let join = join.expect("a dynamic call always has a value result");
        self.builder.switch_to_block(join);
        self.builder.block_params(join).to_vec()
    }
    /// Drop grade-zero logical arguments; they have no physical ABI slot but
    /// were still evaluated in source order by the call expression.
    fn physical_dyn_arguments(&self, grades: &[Option<Grade>], values: &[Value]) -> Vec<Value> {
        values
            .iter()
            .enumerate()
            .filter(|(index, _)| {
                !grades
                    .get(*index)
                    .copied()
                    .flatten()
                    .is_some_and(Grade::is_zero)
            })
            .map(|(_, value)| *value)
            .collect()
    }
    /// Dispatch a borrowed closed-world object in place. `values[0]` is a
    /// pointer to the inline union; the payload starts one word after the tag,
    /// so the selected member method receives that address as its borrowed
    /// receiver and no payload is copied or dropped.
    fn union_borrow_call(&mut self, spec_index: usize, values: Words) -> Words {
        let spec = self.program.union_calls[spec_index].clone();
        let result_ty = if spec.result_grade.is_some_and(Grade::is_zero) {
            Type::Unit
        } else {
            spec.result
        };
        let join = self.join(result_ty);
        let pointer = values[0];
        let tag = self
            .builder
            .ins()
            .load(I64, ir::MemFlagsData::new(), pointer, 0);
        let payload = self.builder.ins().iadd_imm_s(pointer, 8);
        for (member_tag, _member, function) in &spec.members {
            let hit = self.builder.create_block();
            let next = self.builder.create_block();
            let condition = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, tag, *member_tag as i64);
            self.builder.ins().brif(condition, hit, &[], next, &[]);
            self.builder.switch_to_block(hit);
            let mut arguments = vec![payload];
            arguments.extend(self.physical_dyn_arguments(&spec.parameter_grades, &values[1..]));
            let out = self.function_call(*function, arguments);
            if let Some(join) = join {
                self.jump(join, &out);
            }
            self.builder.switch_to_block(next);
        }
        self.abort();
        let join = join.expect("a borrowed dynamic call always has a value result");
        self.builder.switch_to_block(join);
        self.builder.block_params(join).to_vec()
    }
    /// Lower one checked foreign import. `values` is the flattened internal
    /// word list: slice/text parameters occupy their normal four-word
    /// descriptor, from which only `(pointer, length)` reaches the C ABI.
    fn foreign_call(&mut self, index: usize, values: &[Value]) -> Option<Words> {
        let foreign = self.program.foreign_functions[index]
            .as_ref()
            .expect("checked foreign target")
            .clone();
        let id = self.foreign_ids[index].expect("foreign import declared");
        let mut arguments = Vec::new();
        let mut position = 0usize;
        for ty in &foreign.parameters {
            match ty {
                Type::Str => {
                    // `&str` is a four-word checked view; only the contiguous
                    // byte pointer and byte length reach C.
                    arguments.push(values[position]);
                    arguments.push(values[position + 1]);
                    position += 4;
                }
                Type::Ref(pointer) | Type::RefMut(pointer) => {
                    let handle =
                        self.builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), values[position], 0);
                    if foreign_pointee_kind(self.program, *pointer) == PointeeKind::Buffer {
                        // KushBytes/KushString: length at +0, capacity at +8,
                        // payload bytes at +16.
                        let data = self.builder.ins().iadd_imm_s(handle, 16);
                        let length = self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            handle,
                            if matches!(ty, Type::RefMut(_)) { 8 } else { 0 },
                        );
                        arguments.push(data);
                        arguments.push(length);
                    } else {
                        arguments.push(handle);
                    }
                    position += 1;
                }
                _ => {
                    let word = values[position];
                    position += 1;
                    match ty {
                        Type::Bool => {
                            arguments.push(self.builder.ins().ireduce(ir::types::I32, word))
                        }
                        Type::Int(kind) if !matches!(kind, IntKind::I64 | IntKind::U64) => {
                            arguments.push(self.builder.ins().ireduce(abi_value_type(*ty), word))
                        }
                        Type::Float(FloatKind::F64) => arguments.push(self.builder.ins().bitcast(
                            ir::types::F64,
                            ir::MemFlagsData::new(),
                            word,
                        )),
                        Type::Float(FloatKind::F32) => {
                            let bits = self.builder.ins().ireduce(ir::types::I32, word);
                            arguments.push(self.builder.ins().bitcast(
                                ir::types::F32,
                                ir::MemFlagsData::new(),
                                bits,
                            ));
                        }
                        _ => arguments.push(word),
                    }
                }
            }
        }
        let mut out = None;
        if let Some(shape) = foreign.fallible
            && shape.ok != Type::Unit
        {
            let width = self.program.width(shape.ok).max(1);
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (width * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
            ));
            let pointer = self.builder.ins().stack_addr(I64, slot, 0);
            arguments.push(pointer);
            out = Some((pointer, width));
        }
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(callee, &arguments);
        let returned = self.builder.inst_results(call).to_vec();
        if let Some(shape) = foreign.fallible {
            let status = returned[0];
            let join = self.join(foreign.result).unwrap();
            let success = self.builder.create_block();
            let failure = self.builder.create_block();
            let ok = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
            self.builder.ins().brif(ok, success, &[], failure, &[]);
            self.builder.switch_to_block(success);
            let mut values = vec![self.constant(shape.ok_tag as i64)];
            if let Some((pointer, width)) = out {
                values.extend(self.load_words(pointer, 0, width));
            }
            while values.len() < self.program.width(foreign.result) {
                values.push(self.constant(0));
            }
            self.jump(join, &values);
            self.builder.switch_to_block(failure);
            let mut values = vec![self.constant(shape.err_tag as i64)];
            if self.program.width(shape.error) == 1 {
                values.push(status);
            }
            while values.len() < self.program.width(foreign.result) {
                values.push(self.constant(0));
            }
            self.jump(join, &values);
            self.builder.switch_to_block(join);
            return Some(self.builder.block_params(join).to_vec());
        }
        if foreign.result == Type::Unit {
            return Some(vec![self.constant(0)]);
        }
        let value = returned[0];
        Some(vec![match foreign.result {
            Type::Float(FloatKind::F64) => {
                self.builder
                    .ins()
                    .bitcast(I64, ir::MemFlagsData::new(), value)
            }
            Type::Float(FloatKind::F32) => {
                let low =
                    self.builder
                        .ins()
                        .bitcast(ir::types::I32, ir::MemFlagsData::new(), value);
                self.builder.ins().uextend(I64, low)
            }
            // A foreign `int32_t` Bool may be any nonzero value; the proof
            // fragment relies on 0 or 1.
            Type::Bool => {
                let truth = self.builder.ins().icmp_imm_s(IntCC::NotEqual, value, 0);
                self.builder.ins().uextend(I64, truth)
            }
            Type::Int(IntKind::I64 | IntKind::U64) => value,
            Type::Int(kind) if kind.signed() => self.builder.ins().sextend(I64, value),
            Type::Int(_) => self.builder.ins().uextend(I64, value),
            _ => value,
        }])
    }
    fn function_call(&mut self, index: usize, mut values: Words) -> Words {
        // SIMD-NATIVE: vector instructions for recognised std.simd functions,
        // on both backends (the LLVM translator knows vector types, SIMD-LLVM).
        if let Some(Some((ty, op))) = self.program.simd_functions.get(index).cloned()
            && let Some(words) = self.simd_lowering(&ty, &op, &values)
        {
            return words;
        }
        let function = &self.program.functions[index];
        let result = function.result;
        let erased_result = function.result_grade.is_some_and(Grade::is_zero);
        let pointer = if !erased_result && aggregate_result(self.program, result) {
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (self.program.width(result) * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
            ));
            let pointer = self.builder.ins().stack_addr(I64, slot, 0);
            values.insert(0, pointer);
            Some(pointer)
        } else {
            None
        };
        let callee = self
            .module
            .declare_func_in_func(self.ids[index], self.builder.func);
        let call = self.builder.ins().call(callee, &values);
        // The callee's row is not kept on executable functions; a call
        // that cannot panic never sets the word, so testing it is only code.
        self.test_panic();
        if erased_result {
            return vec![self.constant(0)];
        }
        if let Some(pointer) = pointer {
            (0..self.program.width(result))
                .map(|i| {
                    self.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect()
        } else {
            self.builder.inst_results(call).to_vec()
        }
    }
    /// Emit an indirect call whose physical argument words (return pointer,
    /// environment, and arguments) are already assembled.
    fn finish_indirect_call(
        &mut self,
        id: usize,
        code: Value,
        pointer: Option<Value>,
        values: Vec<Value>,
    ) -> Words {
        let once = self.program.function_types[id].once;
        self.finish_indirect_call_mode(id, code, pointer, values, once)
    }
    /// An indirect call whose environment word is part of the ABI when
    /// `environment` is set (`once fn` and `multi fn` values).
    fn finish_indirect_call_mode(
        &mut self,
        id: usize,
        code: Value,
        pointer: Option<Value>,
        values: Vec<Value>,
        environment: bool,
    ) -> Words {
        let signature = self.program.function_types[id].clone();
        let result = signature.result;
        let result_erased = signature.result_erased();
        let ir_signature = self.indirect_signature_mode(id, environment);
        let ir_signature = self.builder.import_signature(ir_signature);
        let call = self
            .builder
            .ins()
            .call_indirect(ir_signature, code, &values);
        // FND-ROWS-PANIC: any callee may panic; rows no longer say otherwise.
        self.test_panic();
        if result_erased {
            return vec![self.constant(0)];
        }
        if let Some(pointer) = pointer {
            return (0..self.program.width(result))
                .map(|i| {
                    self.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect();
        }
        self.builder.inst_results(call).to_vec()
    }
    fn indirect_signature(&self, id: usize) -> ir::Signature {
        let once = self.program.function_types[id].once;
        self.indirect_signature_mode(id, once)
    }
    /// Build the indirect call ABI for a callable signature, overriding whether
    /// the environment word is part of the call. A dynamic handler frame picks
    /// the copyable `fn` shape or the owning `once` shape at run time.
    fn indirect_signature_mode(&self, id: usize, once: bool) -> ir::Signature {
        let signature = &self.program.function_types[id];
        let mut result = self.module.make_signature();
        let aggregate =
            !signature.result_erased() && aggregate_result(self.program, signature.result);
        if aggregate {
            result.params.push(AbiParam::new(I64));
        }
        if once {
            result.params.push(AbiParam::new(I64));
        }
        for (index, parameter) in signature.parameters.iter().enumerate() {
            if signature.parameter_erased(index) {
                continue;
            }
            result
                .params
                .extend((0..self.program.width(*parameter)).map(|_| AbiParam::new(I64)));
        }
        if !aggregate && !signature.result_erased() {
            result
                .returns
                .extend((0..self.program.width(signature.result)).map(|_| AbiParam::new(I64)));
        }
        result
    }
    fn abort(&mut self) {
        if self.program.uses_unwinding && !self.unwind_emitting {
            // `kush_unwind_panic` aborts unless a catch boundary is active;
            // then it sets the panic word, and this frame unwinds.
            let unwind = self
                .module
                .declare_func_in_func(self.unwind_panic, self.builder.func);
            self.builder.ins().call(unwind, &[]);
            self.unwind_exit();
            return;
        }
        let panic = self
            .module
            .declare_func_in_func(self.panic, self.builder.func);
        self.builder.ins().call(panic, &[]);
        self.builder.ins().trap(TrapCode::unwrap_user(1));
    }
    /// Leave the function while a panic unwinds: drop every live value and
    /// return a dummy result; the caller tests the word in turn.
    fn unwind_exit(&mut self) {
        if let Some(cleanup) = self.mir_unwind {
            self.jump(cleanup, &[]);
            return;
        }
        let emitting = std::mem::replace(&mut self.unwind_emitting, true);
        self.cleanup_all();
        self.return_dummy();
        self.unwind_emitting = emitting;
    }
    /// After a join: status 2 means the task or thread panicked; raise the
    /// panic here (`kush_unwind_rethrow` aborts when nothing can stop it)
    /// and unwind (PANIC-UNWIND-USE).
    fn rethrow_if_panicked(&mut self, status: Value) {
        if !self.program.uses_unwinding {
            return;
        }
        let panicked = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 2);
        let rethrow = self.builder.create_block();
        let normal = self.builder.create_block();
        self.builder.ins().brif(panicked, rethrow, &[], normal, &[]);
        self.builder.switch_to_block(rethrow);
        self.runtime_void_raw(self.unwind_rethrow, &[]);
        self.unwind_exit();
        self.builder.switch_to_block(normal);
    }
    /// A runtime call that is never followed by a panic test.
    fn runtime_void_raw(&mut self, id: FuncId, values: &[Value]) {
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        self.builder.ins().call(callee, values);
    }
    /// After a call that may panic: unwind when the panic word is set.
    fn test_panic(&mut self) {
        if !self.program.uses_unwinding || self.unwind_emitting {
            return;
        }
        let emitting = std::mem::replace(&mut self.unwind_emitting, true);
        let address = self.abort_word_address();
        self.unwind_emitting = emitting;
        let word = self
            .builder
            .ins()
            .load(I64, ir::MemFlagsData::new(), address, 0);
        let panicked = self.builder.ins().icmp_imm_s(IntCC::Equal, word, 1);
        let unwind = self.builder.create_block();
        let normal = self.builder.create_block();
        self.builder.ins().brif(panicked, unwind, &[], normal, &[]);
        self.builder.switch_to_block(unwind);
        self.unwind_exit();
        self.builder.switch_to_block(normal);
    }
    /// Trap when a runtime index is negative or outside `0..length`.
    fn check_index(&mut self, index: Value, length: i64) {
        let limit = self.constant(length);
        let negative = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, index, 0);
        let beyond = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, index, limit);
        let invalid = self.builder.ins().bor(negative, beyond);
        self.guard(invalid);
    }
    /// PROOF-FUZZ: mark the start of the checked operation of an obligation
    /// site (`kind` as in [`fuzz_kind`]), if this build is instrumented and
    /// the site exists.
    fn fuzz_site(&self, span: crate::Span, kind: u8) -> Option<(FuncId, FuncId, i64)> {
        let hooks = self.fuzz.as_ref()?;
        let id = *hooks.sites.get(&(span.start, span.end, kind))?;
        Some((hooks.enter, hooks.arith, id))
    }
    fn fuzz_enter(&mut self, span: crate::Span, kind: u8) {
        if let Some((enter, _, id)) = self.fuzz_site(span, kind) {
            let id = self.constant(id);
            self.runtime_void(enter, &[id]);
            self.fuzz_depth += 1;
        }
    }
    /// An integer operation of an obligation site: enter it and record how
    /// close these operands come to failing it. `Kind::Bang` stands for
    /// unary minus (`left` is the operand).
    fn fuzz_arith(
        &mut self,
        span: crate::Span,
        op: &Kind,
        left: Option<IntKind>,
        right: Option<IntKind>,
        a: Value,
        b: Value,
    ) {
        let (code, kind) = match op {
            Kind::Plus => (0, 1),
            Kind::Minus => (1, 1),
            Kind::Star => (2, 1),
            Kind::Slash => (3, 2),
            Kind::Percent => (4, 2),
            Kind::Shl => (5, 3),
            Kind::Shr => (6, 3),
            Kind::Bang => (7, 1),
            _ => return,
        };
        let Some((_, arith, id)) = self.fuzz_site(span, kind) else {
            return;
        };
        let left = left.unwrap_or(IntKind::I64);
        let right_signed = right.is_none_or(IntKind::signed);
        let code = code
            | (i64::from(left.bits()) << 8)
            | (i64::from(left.signed()) << 16)
            | (i64::from(right_signed) << 17);
        let id = self.constant(id);
        let code = self.constant(code);
        self.runtime_void(arith, &[id, code, a, b]);
        self.fuzz_depth += 1;
    }
    fn guard(&mut self, fail: Value) {
        let bad = self.builder.create_block();
        let good = self.builder.create_block();
        self.builder.ins().brif(fail, bad, &[], good, &[]);
        self.builder.switch_to_block(bad);
        self.abort();
        self.builder.switch_to_block(good);
    }
    fn block(&mut self, block: &ex::Block) -> Option<Words> {
        let mut slots = Vec::new();
        for statement in &block.statements {
            match statement {
                ex::Statement::Declare(slot) => {
                    // Backing storage for a temporary owner. The initializer
                    // runs at its source position; cleanup is guarded by the
                    // resource's activation flag.
                    slots.push(*slot);
                }
                ex::Statement::Let(slot, expr) => {
                    let value = lower!(self.expr(expr));
                    self.consume(expr);
                    if self.erased_local(*slot) {
                        if self.program.owns(expr.ty) {
                            self.drop_value(expr.ty, &value);
                        }
                        continue;
                    }
                    self.assign(*slot, &value);
                    self.activate_local(*slot);
                    slots.push(*slot);
                }
                ex::Statement::Expr(expr) => {
                    lower!(self.expr(expr));
                    self.cleanup(expr.resource);
                }
            }
        }
        let value = if let Some(tail) = &block.tail {
            let value = lower!(self.expr(tail));
            self.consume(tail);
            value
        } else {
            vec![self.constant(0)]
        };
        for slot in slots.into_iter().rev() {
            self.cleanup(self.program.functions[self.function_index].local_resources[slot]);
        }
        Some(value)
    }
    fn expr(&mut self, expr: &Expr) -> Option<Words> {
        let depth = self.fuzz_depth;
        let values = self.expression(expr);
        if self.fuzz_depth > depth {
            self.fuzz_depth = depth;
            if values.is_some()
                && let Some(leave) = self.fuzz.as_ref().map(|f| f.leave)
            {
                self.runtime_void(leave, &[]);
            }
        }
        let values = values?;
        self.track(expr.resource, &values);
        Some(values)
    }
    fn expression(&mut self, expr: &Expr) -> Option<Words> {
        let scalar = match &expr.kind {
            ExprKind::Constant(n) => self.constant(*n),
            // Synthesized adapter placeholder for a physically erased
            // parameter position. The call's ABI drops these words.
            ExprKind::Erased(ty) => {
                let width = self.program.width(*ty);
                return Some(vec![self.constant(0); width]);
            }
            ExprKind::FnValue { function, captures } => {
                let reference = self
                    .module
                    .declare_func_in_func(self.ids[*function], self.builder.func);
                let code = self.builder.ins().func_addr(I64, reference);
                if captures.is_empty() {
                    if matches!(expr.ty, Type::Once(_) | Type::Multi(_)) {
                        let zero = self.constant(0);
                        return Some(vec![code, zero]);
                    }
                    code
                } else if matches!(expr.ty, Type::Multi(_)) {
                    // A multishot token: the captures go on the continuation
                    // stack, after a word holding the environment size.
                    let bytes = 8 + captures
                        .iter()
                        .map(|capture| self.program.width(capture.ty) * 8)
                        .sum::<usize>();
                    let size = self.constant(bytes as i64);
                    let environment = self.runtime_call(self.kstack_push, &[size]);
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), size, environment, 0);
                    let mut offset: i32 = 8;
                    for capture in captures {
                        let values = lower!(self.expr(capture));
                        self.consume(capture);
                        for value in values.iter().take(self.program.width(capture.ty)) {
                            self.builder.ins().store(
                                ir::MemFlagsData::new(),
                                *value,
                                environment,
                                offset,
                            );
                            offset += 8;
                        }
                    }
                    return Some(vec![code, environment]);
                } else {
                    let types = captures
                        .iter()
                        .map(|capture| capture.ty.full())
                        .collect::<Vec<_>>();
                    let bytes = 8 + types
                        .iter()
                        .map(|ty| self.program.width(*ty) * 8)
                        .sum::<usize>();
                    let size = self.constant(bytes as i64);
                    let environment = self.runtime_call(self.allocate, &[size]);
                    let drop = self.closure_drops[&types];
                    let drop = self.module.declare_func_in_func(drop, self.builder.func);
                    let drop = self.builder.ins().func_addr(I64, drop);
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), drop, environment, 0);
                    let capture_refs = self.program.functions[*function].capture_refs.clone();
                    let mut offset = 8;
                    for (index, capture) in captures.iter().enumerate() {
                        if capture_refs.get(index).copied().unwrap_or(false) {
                            let slot = match &capture.kind {
                                ExprKind::Local(slot)
                                | ExprKind::Peek(slot)
                                | ExprKind::Move(slot) => *slot,
                                _ => unreachable!("checked by-reference scalar capture"),
                            };
                            let pointer = self.local_address(slot);
                            self.builder.ins().store(
                                ir::MemFlagsData::new(),
                                pointer,
                                environment,
                                offset as i32,
                            );
                            self.consume(capture);
                            offset += 8;
                            continue;
                        }
                        let values = lower!(self.expr(capture));
                        self.consume(capture);
                        let width = self.program.width(capture.ty);
                        let mut position = offset;
                        for value in values.iter().take(width) {
                            self.builder.ins().store(
                                ir::MemFlagsData::new(),
                                *value,
                                environment,
                                position as i32,
                            );
                            position += 8;
                        }
                        offset += width * 8;
                    }
                    return Some(vec![code, environment]);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                let callable = lower!(self.expr(callee));
                let Some((id, once)) = (match callee.ty {
                    Type::Fn(id) => Some((id, false)),
                    Type::Once(id) | Type::Multi(id) => Some((id, true)),
                    _ => None,
                }) else {
                    unreachable!("checked indirect callee")
                };
                let multi = matches!(callee.ty, Type::Multi(_));
                let signature = self.program.function_types[id].clone();
                let result = signature.result;
                let result_erased = signature.result_erased();
                let pointer = if !result_erased && aggregate_result(self.program, result) {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    let pointer = self.builder.ins().stack_addr(I64, slot, 0);
                    Some(pointer)
                } else {
                    None
                };
                let mut values = Vec::new();
                if let Some(pointer) = pointer {
                    values.push(pointer);
                }
                if once {
                    values.push(callable[1]);
                }
                for (index, argument) in arguments.iter().enumerate() {
                    let words = lower!(self.expr(argument));
                    if !signature.parameter_erased(index) {
                        values.extend(words);
                    }
                }
                self.consume(callee);
                for argument in arguments {
                    self.consume(argument);
                }
                if multi {
                    // Everything the token call pushes is released when it
                    // returns (docs/multishot-capabilities.md section 5).
                    let mark = self.runtime_call(self.kstack_mark, &[]);
                    let words =
                        self.finish_indirect_call_mode(id, callable[0], pointer, values, true);
                    self.runtime_void(self.kstack_restore, &[mark]);
                    return Some(words);
                }
                return Some(self.finish_indirect_call(id, callable[0], pointer, values));
            }
            ExprKind::Region { body, finish, .. } => {
                let exit = self.join(expr.ty);
                // The finish block receives the finish callable's argument:
                // the body value on completion, or a returned value from a
                // `RegionExit`/`TryExit`, even when the body itself never
                // completes (type Never).
                let finish_block = match finish {
                    Some(finish) => {
                        let input = match finish.ty {
                            Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                                self.program.function_types[id].parameters[0]
                            }
                            _ => unreachable!("checked region finish callable"),
                        };
                        let block = self.builder.create_block();
                        for _ in 0..self.program.width(input) {
                            self.builder.append_block_param(block, I64);
                        }
                        Some(block)
                    }
                    None => None,
                };
                let depth = self.capture_handler_depth();
                self.regions.push((exit, finish_block, depth));
                let finished = self.block(body);
                self.regions.pop();
                if let Some(values) = finished {
                    match (finish_block, exit) {
                        (Some(block), _) => self.jump(block, &values),
                        (None, Some(exit)) => self.jump(exit, &values),
                        (None, None) => unreachable!("a completing region has a value"),
                    }
                }
                if let (Some(block), Some(finish)) = (finish_block, finish) {
                    self.builder.switch_to_block(block);
                    let arguments = self.builder.block_params(block).to_vec();
                    if let Some(callable) = self.expr(finish) {
                        self.consume(finish);
                        let Some((id, once)) = (match finish.ty {
                            Type::Fn(id) => Some((id, false)),
                            Type::Once(id) | Type::Multi(id) => Some((id, true)),
                            _ => None,
                        }) else {
                            unreachable!("checked region finish callable")
                        };
                        let multi = matches!(finish.ty, Type::Multi(_));
                        let result = self.program.function_types[id].result;
                        let pointer = aggregate_result(self.program, result).then(|| {
                            let slot =
                                self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                                    ir::StackSlotKind::ExplicitSlot,
                                    (self.program.width(result) * 8) as u32,
                                    STACK_SLOT_ALIGN_SHIFT,
                                ));
                            self.builder.ins().stack_addr(I64, slot, 0)
                        });
                        let mut values = Vec::new();
                        if let Some(pointer) = pointer {
                            values.push(pointer);
                        }
                        if once {
                            values.push(callable[1]);
                        }
                        values.extend(arguments);
                        let words = if multi {
                            let mark = self.runtime_call(self.kstack_mark, &[]);
                            let words = self.finish_indirect_call_mode(
                                id,
                                callable[0],
                                pointer,
                                values,
                                true,
                            );
                            self.runtime_void(self.kstack_restore, &[mark]);
                            words
                        } else {
                            self.finish_indirect_call(id, callable[0], pointer, values)
                        };
                        match exit {
                            Some(exit) => self.jump(exit, &words),
                            None => {
                                self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                            }
                        }
                    }
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::AbortScope {
                label,
                body,
                handler,
                operation,
            } => {
                let exit = self.join(expr.ty);
                let Some((id, once)) = (match handler.ty {
                    Type::Fn(id) => Some((id, false)),
                    Type::Once(id) => Some((id, true)),
                    _ => None,
                }) else {
                    unreachable!("checked abortive handler callable")
                };
                let payload = self.program.function_types[id].parameters[0];
                let aborted = self.builder.create_block();
                for _ in 0..self.program.width(payload) {
                    self.builder.append_block_param(aborted, I64);
                }
                let depth = self.capture_handler_depth();
                // An abort can leave a multishot `handle` without its
                // continuation-stack restore; the landing restores instead.
                let kstack_mark = self
                    .program
                    .functions
                    .iter()
                    .any(|function| function.shared_environment)
                    .then(|| self.runtime_call(self.kstack_mark, &[]));
                let width = self.program.width(payload);
                let buffer = operation.map(|operation| {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (width.max(1) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    let buffer = self.builder.ins().stack_addr(I64, slot, 0);
                    let op = self.constant(operation as i64);
                    let zero = self.constant(0);
                    self.runtime_void(self.handler_push, &[op, buffer, zero, zero]);
                    buffer
                });
                self.aborts.push(AbortTarget {
                    label: *label,
                    aborted,
                    depth,
                    buffer,
                    width,
                });
                let finished = self.block(body);
                self.aborts.pop();
                if let (Some(values), Some(exit)) = (finished, exit) {
                    if buffer.is_some() {
                        self.runtime_void(self.handler_pop, &[]);
                    }
                    self.jump(exit, &values);
                }
                self.builder.switch_to_block(aborted);
                let arguments = self.builder.block_params(aborted).to_vec();
                if let Some(mark) = kstack_mark {
                    self.runtime_void(self.kstack_restore, &[mark]);
                }
                if let Some(callable) = self.expr(handler) {
                    self.consume(handler);
                    let result = self.program.function_types[id].result;
                    let pointer = aggregate_result(self.program, result).then(|| {
                        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                            ir::StackSlotKind::ExplicitSlot,
                            (self.program.width(result) * 8) as u32,
                            STACK_SLOT_ALIGN_SHIFT,
                        ));
                        self.builder.ins().stack_addr(I64, slot, 0)
                    });
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    if once {
                        values.push(callable[1]);
                    }
                    values.extend(arguments);
                    let words = self.finish_indirect_call(id, callable[0], pointer, values);
                    match exit {
                        Some(exit) => self.jump(exit, &words),
                        None => {
                            self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                        }
                    }
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::AbortExit {
                label,
                value,
                cleanup,
                ..
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let target = self.abort_target(*label);
                self.restore_handler_depth(target.depth);
                self.jump(target.aborted, &values);
                return None;
            }
            ExprKind::AbortPerform { operation, value } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let out = self.stack_words(3);
                let op = self.constant(*operation as i64);
                let found = self.runtime_call(self.handler_lookup, &[op, out]);
                let missing = self.builder.ins().icmp_imm_s(IntCC::Equal, found, 0);
                self.guard(missing);
                let buffer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                for (index, word) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        buffer,
                        (index * 8) as i32,
                    );
                }
                let word = self.abort_word_address();
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), buffer, word, 0);
                self.cleanup_all();
                self.return_dummy();
                return None;
            }
            ExprKind::AbortCall {
                call,
                exits,
                propagates,
            } => {
                let values = lower!(self.expr(call));
                let address = self.abort_word_address();
                let word = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), address, 0);
                let dispatch = self.builder.create_block();
                let normal = self.builder.create_block();
                self.builder.ins().brif(word, dispatch, &[], normal, &[]);
                self.builder.switch_to_block(dispatch);
                // The call's result words are meaningless on this path.
                self.consume(call);
                for (label, cleanup) in exits {
                    let target = self.abort_target(*label);
                    let Some(buffer) = target.buffer else {
                        continue;
                    };
                    let hit = self.builder.create_block();
                    let miss = self.builder.create_block();
                    let same = self.builder.ins().icmp(IntCC::Equal, word, buffer);
                    self.builder.ins().brif(same, hit, &[], miss, &[]);
                    self.builder.switch_to_block(hit);
                    let zero = self.constant(0);
                    let address = self.abort_word_address();
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), zero, address, 0);
                    for id in cleanup {
                        self.cleanup(Some(*id));
                    }
                    self.restore_handler_depth(target.depth);
                    let payload = self.load_words(buffer, 0, target.width);
                    self.jump(target.aborted, &payload);
                    self.builder.switch_to_block(miss);
                }
                if *propagates || self.program.uses_unwinding {
                    // A foreign abort, or a panic unwinding through.
                    self.cleanup_all();
                    self.return_dummy();
                } else {
                    self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                }
                self.builder.switch_to_block(normal);
                return Some(values);
            }
            ExprKind::RegionExit {
                value,
                finish,
                cleanup,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let (exit, finish_block, depth) = *self.regions.last().unwrap();
                self.restore_handler_depth(depth);
                let target = if *finish { finish_block } else { exit };
                match target {
                    Some(target) => self.jump(target, &values),
                    None => {
                        self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                    }
                }
                return None;
            }
            ExprKind::TryExit {
                value,
                input,
                output,
                cleanup,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let condition =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], input.ok_tag as i64);
                let success = self.builder.create_block();
                let failure = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(condition, success, &[], failure, &[]);
                self.builder.switch_to_block(failure);
                let (_, finish_block, depth) = *self.regions.last().unwrap();
                let finish_block = finish_block.expect("a resumable entry region has a finish");
                let width = self.builder.block_params(finish_block).len();
                let mut error = vec![self.constant(output.err_tag as i64)];
                error.extend_from_slice(&values[1..1 + self.program.width(input.error)]);
                while error.len() < width {
                    error.push(self.constant(0));
                }
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                self.restore_handler_depth(depth);
                self.jump(finish_block, &error);
                self.builder.switch_to_block(success);
                return Some(values[1..1 + self.program.width(input.ok)].to_vec());
            }
            ExprKind::HandlerDepth => self.runtime_call(self.handler_depth, &[]),
            ExprKind::ContinuationScope { body } => {
                let mark = self.runtime_call(self.kstack_mark, &[]);
                let values = self.block(body)?;
                self.runtime_void(self.kstack_restore, &[mark]);
                return Some(values);
            }
            ExprKind::HandlerRedirect { depth, body } => {
                let target = lower!(self.scalar(depth));
                let before = self.runtime_call(self.handler_redirect, &[target]);
                let values = self.block(body)?;
                self.runtime_void(self.handler_restore, &[before]);
                return Some(values);
            }
            ExprKind::Suspendable(_) | ExprKind::Suspend { .. } => {
                unreachable!("suspendable bodies are lowered before code generation")
            }
            ExprKind::HandlerPush {
                operation,
                handler,
                body,
                reusable,
            } => {
                let values = lower!(self.expr(handler));
                let code = values[0];
                let (environment, once) = if matches!(handler.ty, Type::Once(_)) {
                    let environment = values.get(1).copied().unwrap_or_else(|| self.constant(0));
                    (environment, self.constant(if *reusable { 2 } else { 1 }))
                } else {
                    (self.constant(0), self.constant(0))
                };
                self.consume(handler);
                let op = self.constant(*operation as i64);
                self.runtime_void(self.handler_push, &[op, code, environment, once]);
                if let Some(values) = self.block(body) {
                    self.runtime_void(self.handler_pop, &[]);
                    return Some(values);
                }
                return None;
            }
            ExprKind::DynamicPerform {
                operation,
                payload,
                resume,
                handler,
            } => {
                let payload_values = lower!(self.expr(payload));
                let resume_values = lower!(self.expr(resume));
                self.consume(payload);
                self.consume(resume);
                let out = self.stack_words(3);
                let op = self.constant(*operation as i64);
                let found = self.runtime_call(self.handler_lookup, &[op, out]);
                let missing = self.builder.ins().icmp_imm_s(IntCC::Equal, found, 0);
                self.guard(missing);
                let code = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                let environment = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 8);
                let once = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 16);
                let signature = self.program.function_types[*handler].clone();
                let result = signature.result;
                let pointer = if aggregate_result(self.program, result) {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    Some(self.builder.ins().stack_addr(I64, slot, 0))
                } else {
                    None
                };
                // A dynamic frame may hold either a copyable noncapturing `fn`
                // (no environment word in its ABI) or an owning `once` handler
                // (an environment word). The runtime frame records which, so
                // generate both checked call shapes and select at run time.
                let once_block = self.builder.create_block();
                let fn_block = self.builder.create_block();
                let Some(join) = self.join(result) else {
                    unreachable!("a declared effect result is never Never")
                };
                self.builder
                    .ins()
                    .brif(once, once_block, &[], fn_block, &[]);
                for (call_once, block) in [(false, fn_block), (true, once_block)] {
                    self.builder.switch_to_block(block);
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    if call_once {
                        values.push(environment);
                    }
                    values.extend(payload_values.iter().copied());
                    values.extend(resume_values.iter().copied());
                    let signature = self.indirect_signature_mode(*handler, call_once);
                    let signature = self.builder.import_signature(signature);
                    let call = self.builder.ins().call_indirect(signature, code, &values);
                    self.test_panic();
                    let results = match pointer {
                        Some(pointer) => (0..self.program.width(result))
                            .map(|i| {
                                self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    pointer,
                                    (i * 8) as i32,
                                )
                            })
                            .collect::<Vec<_>>(),
                        None => self.builder.inst_results(call).to_vec(),
                    };
                    self.jump(join, &results);
                }
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::BytesLiteral(bytes) => {
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
                self.runtime_call(self.bytes_from, &[address, length])
            }
            ExprKind::Move(slot) => {
                self.deactivate(self.program.functions[self.function_index].local_resources[*slot]);
                if let Some(pointer) = self.locations[*slot] {
                    let width = self.variables[*slot].len();
                    return Some(self.load_words(pointer, 0, width));
                }
                return Some(
                    self.variables[*slot]
                        .iter()
                        .map(|v| self.builder.use_var(*v))
                        .collect(),
                );
            }
            ExprKind::Borrow(slot) => return Some(self.borrow_local_value(*slot)),
            ExprKind::InitOwner { slot, value: init } => {
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                return Some(self.local_words(*slot));
            }
            ExprKind::BorrowInit { slot, value: init } => {
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                return Some(self.borrow_local_value(*slot));
            }
            ExprKind::BorrowPlace(place) => {
                return Some(vec![lower!(self.place_address(place))]);
            }
            ExprKind::PlaceIndex { .. } => {
                unreachable!("a checked place index appears only inside a borrow")
            }
            ExprKind::DerefWrite(reference, replacement) => {
                let pointer = lower!(self.scalar(reference));
                let value = lower!(self.expr(replacement));
                let pointer_ty = reference
                    .ty
                    .ref_pointee()
                    .expect("checked dereference write");
                let pointee = self.program.pointees[pointer_ty];
                if self.program.owns(pointee) {
                    let width = self.program.width(pointee);
                    let old = self.load_words(pointer, 0, width);
                    self.drop_value(pointee, &old);
                }
                for (index, word) in value.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                self.consume(replacement);
                self.constant(0)
            }
            ExprKind::BoxNew(arg) => {
                let values = lower!(self.expr(arg));
                let bytes = self.constant((self.program.width(arg.ty) * 8) as i64);
                let pointer = self.runtime_call(self.allocate, &[bytes]);
                self.consume(arg);
                for (i, value) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (i * 8) as i32,
                    );
                }
                pointer
            }
            ExprKind::BoxTake(arg) => {
                let pointer = lower!(self.scalar(arg));
                let values = (0..self.program.width(expr.ty))
                    .map(|i| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (i * 8) as i32,
                        )
                    })
                    .collect();
                self.consume(arg);
                emit_drop(&mut self.builder, self.module, self.free, &[pointer]);
                return Some(values);
            }
            ExprKind::BoxRead(arg) => {
                let reference = lower!(self.scalar(arg));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|i| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                pointer,
                                (i * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BoxWrite(reference, value) => {
                let reference = lower!(self.scalar(reference));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let words = lower!(self.expr(value));
                for (index, word) in words.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                self.consume(value);
                return Some(vec![self.constant(0)]);
            }
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                let allocator = lower!(self.expr(alloc));
                let release = lower!(self.expr(free));
                let grow = match realloc {
                    Some(realloc) => {
                        let realloc = lower!(self.expr(realloc));
                        realloc[0]
                    }
                    None => self.constant(0),
                };
                return Some(vec![allocator[0], release[0], grow]);
            }
            ExprKind::AllocatorContextNew { value, spec } => {
                let spec_index =
                    (*spec < self.program.allocator_contexts.len()).then_some(*spec)?;
                let checked = self.program.allocator_contexts[spec_index];
                let instance = lower!(self.expr(value));
                self.consume(value);
                let state_bytes =
                    self.constant((self.program.width(checked.state).max(1) * 8) as i64);
                let state = self.runtime_call(self.allocate, &[state_bytes]);
                for (index, word) in instance.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        state,
                        (index * 8) as i32,
                    );
                }
                let drop = self
                    .module
                    .declare_func_in_func(self.context_drops[spec_index], self.builder.func);
                let drop = self.builder.ins().func_addr(I64, drop);
                let alloc = self
                    .module
                    .declare_func_in_func(self.ids[checked.alloc], self.builder.func);
                let alloc = self.builder.ins().func_addr(I64, alloc);
                let release = self
                    .module
                    .declare_func_in_func(self.ids[checked.free], self.builder.func);
                let release = self.builder.ins().func_addr(I64, release);
                let grow = self
                    .module
                    .declare_func_in_func(self.ids[checked.grow], self.builder.func);
                let grow = self.builder.ins().func_addr(I64, grow);
                let context = self.runtime_call(
                    self.alloc_ops.context_new,
                    &[state, drop, alloc, release, grow],
                );
                return Some(vec![context]);
            }
            ExprKind::AllocatorContextShare(argument) => {
                let reference = lower!(self.scalar(argument));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let shared = self.runtime_call(self.alloc_ops.context_share, &[handle]);
                return Some(vec![shared]);
            }
            ExprKind::AllocBoxNew { allocator, value } => {
                let pair = self.allocator_words(allocator)?;
                let payload = lower!(self.expr(value));
                self.consume(allocator);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                self.consume(value);
                let block =
                    self.runtime_call(self.alloc_ops.block, &[pair[0], pair[1], pair[3], bytes]);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        data,
                        (index * 8) as i32,
                    );
                }
                let handle = self.runtime_call(
                    self.alloc_ops.box_create,
                    &[pair[0], pair[1], block, pair[3]],
                );
                return Some(vec![handle]);
            }
            ExprKind::AllocBoxTryNew {
                allocator,
                value,
                shape,
            } => {
                let pair = self.allocator_words(allocator)?;
                let payload = lower!(self.expr(value));
                self.consume(allocator);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let block = self.runtime_call(
                    self.alloc_ops.block_try,
                    &[pair[0], pair[1], pair[3], bytes],
                );
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, block, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        data,
                        (index * 8) as i32,
                    );
                }
                let owner = self.runtime_call(
                    self.alloc_ops.box_create,
                    &[pair[0], pair[1], block, pair[3]],
                );
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), owner, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                // Nothing retained the context on refusal; drop the operation's
                // reference before returning the untouched payload.
                self.runtime_void(self.alloc_ops.context_release, &[pair[3]]);
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::AllocBoxRead(argument) => {
                let reference = lower!(self.scalar(argument));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                data,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::AllocBoxTake(argument) => {
                let handle = lower!(self.scalar(argument));
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                let payload = (0..self.program.width(expr.ty))
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            data,
                            (index * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                self.consume(argument);
                self.runtime_void(self.alloc_ops.box_release, &[handle]);
                return Some(payload);
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                element,
            } => {
                let pair = self.allocator_words(allocator)?;
                let capacity = match capacity {
                    Some(capacity) => lower!(self.scalar(capacity)),
                    None => self.constant(0),
                };
                self.consume(allocator);
                let width = self.constant(self.program.width(*element) as i64);
                let handle = self.runtime_call(
                    self.alloc_ops.vec_create,
                    &[pair[0], pair[1], pair[2], pair[3], capacity, width],
                );
                return Some(vec![handle]);
            }
            ExprKind::BoxReuse { owner, payload } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.reuse owner"),
                };
                let old_width = self.program.width(old);
                // Both arguments are evaluated before the old payload is
                // destroyed. If the payload diverges, the owner's tracked
                // resource is still live and cleanup reclaims the box.
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                self.drop_value(old, &previous);
                for (index, value) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                pointer
            }
            ExprKind::BoxReuseGrow { owner, payload } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.reuse_grow owner"),
                };
                let old_width = self.program.width(old);
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                self.drop_value(old, &previous);
                let new_width = self.program.width(payload.ty);
                let pointer = if new_width > old_width {
                    let bytes = self.constant((new_width * 8) as i64);
                    self.runtime_call(self.grow, &[pointer, bytes])
                } else {
                    pointer
                };
                for (index, value) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                pointer
            }
            ExprKind::ArenaNew => self.runtime_call(self.arena_new, &[]),
            ExprKind::ArenaNewWith { strategy } => {
                let code = lower!(self.scalar(strategy));
                self.consume(strategy);
                self.runtime_call(self.arena_new_with_strategy, &[code])
            }
            ExprKind::ArenaAlloc { arena, value } => {
                let reference = lower!(self.scalar(arena));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let payload = lower!(self.expr(value));
                self.consume(arena);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let pointer = self.runtime_call(self.arena_alloc, &[handle, bytes]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                pointer
            }
            ExprKind::ArenaTryAlloc {
                arena,
                value,
                shape,
            } => {
                let reference = lower!(self.scalar(arena));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let payload = lower!(self.expr(value));
                self.consume(arena);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let pointer = self.runtime_call(self.arena_try_alloc, &[handle, bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, pointer, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), pointer, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::ArenaBoxRead(argument) => {
                let reference = lower!(self.scalar(argument));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                pointer,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::ArenaBoxTake(argument) => {
                let pointer = lower!(self.scalar(argument));
                self.consume(argument);
                let values = (0..self.program.width(expr.ty))
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (index * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                self.runtime_void(self.arena_box_release, &[pointer]);
                return Some(values);
            }
            ExprKind::BoxTryNew { value, shape } => {
                let payload = lower!(self.expr(value));
                self.consume(value);
                let width = self.program.width(value.ty);
                let bytes = self.constant((width * 8) as i64);
                let handle = self.runtime_call(self.try_allocate, &[bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, handle, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        handle,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), handle, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BoxTryReuse {
                owner,
                payload,
                shape,
            } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.try_reuse owner"),
                };
                let old_width = self.program.width(old);
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                let new_width = self.program.width(payload.ty);
                let bytes = self.constant((new_width * 8) as i64);
                let grown = self.runtime_call(self.try_grow, &[pointer, bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, grown, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                self.drop_value(old, &previous);
                for (index, word) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        grown,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), pointer, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BytesTryWithCapacity { capacity, shape } => {
                let requested = lower!(self.scalar(capacity));
                self.consume(capacity);
                let handle = self.runtime_call(self.try_bytes_with_capacity, &[requested]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, handle, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), handle, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), requested, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::Drop(arg) => {
                let value = lower!(self.expr(arg));
                self.consume(arg);
                self.drop_value(arg.ty, &value);
                self.constant(0)
            }
            ExprKind::Coerce {
                value,
                to,
                coercion,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                return self.coerce_values(values, *to, coercion);
            }
            ExprKind::DynArrayNew { element, capacity } => {
                let width = self.program.width(*element);
                return Some(vec![self.constant(0); 1 + width * capacity]);
            }
            ExprKind::DynArrayPush {
                array,
                value,
                element,
                capacity,
            } => {
                let values = lower!(self.expr(array));
                self.consume(array);
                let item = lower!(self.expr(value));
                self.consume(value);
                let element_width = self.program.width(*element);
                let length = values[0];
                let full = self.builder.ins().icmp_imm_s(
                    IntCC::UnsignedGreaterThanOrEqual,
                    length,
                    *capacity as i64,
                );
                self.guard(full);
                let mut out = values.clone();
                let next = self.builder.ins().iadd_imm_s(length, 1);
                out[0] = next;
                // The inline storage is represented as SSA words, not memory.
                // Select the active capacity slot without a runtime index into
                // the value vector: each slot compares the length once.
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, length, slot as i64);
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        out[index] = self.builder.ins().select(active, *value, out[index]);
                    }
                }
                return Some(out);
            }
            ExprKind::DynArrayFill {
                length: length_expr,
                value,
                element,
                capacity,
                ..
            } => {
                let length = lower!(self.scalar(length_expr));
                self.consume(length_expr);
                let item = lower!(self.expr(value));
                self.consume(value);
                // A checked fill traps on a length outside 0..=capacity. A
                // proved fill keeps the same trap as a defensive check that
                // cannot fire (the unsigned compare also rejects negatives).
                let bad = self.builder.ins().icmp_imm_s(
                    IntCC::UnsignedGreaterThan,
                    length,
                    *capacity as i64,
                );
                self.guard(bad);
                let element_width = self.program.width(*element);
                let zero = self.constant(0);
                let mut out = vec![zero; 1 + element_width * capacity];
                out[0] = length;
                for slot in 0..*capacity {
                    let active = self.builder.ins().icmp_imm_s(
                        IntCC::SignedGreaterThan,
                        length,
                        slot as i64,
                    );
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        out[index] = self.builder.ins().select(active, *value, zero);
                    }
                }
                return Some(out);
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                element,
                capacity,
            } => {
                let mut values = lower!(self.expr(array));
                self.consume(array);
                let position = lower!(self.scalar(index));
                self.consume(index);
                let item = lower!(self.expr(value));
                self.consume(value);
                let length = values[0];
                let bad =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, position, length);
                self.guard(bad);
                let element_width = self.program.width(*element);
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, position, slot as i64);
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        values[index] = self.builder.ins().select(active, *value, values[index]);
                    }
                }
                return Some(values);
            }
            ExprKind::DynArrayPop {
                array,
                element,
                capacity,
            } => {
                let mut values = lower!(self.expr(array));
                self.consume(array);
                let length = values[0];
                let empty = self.builder.ins().icmp_imm_s(IntCC::Equal, length, 0);
                self.guard(empty);
                let next = self.builder.ins().iadd_imm_s(length, -1);
                let zero = self.constant(0);
                // The result type is the checked tuple layout, whose first
                // word is the single (always zero) constructor tag.
                values.insert(0, zero);
                values[1] = next;
                let element_width = self.program.width(*element);
                let mut item = vec![zero; element_width];
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, next, slot as i64);
                    for (word, item_word) in item.iter_mut().enumerate() {
                        let index = 2 + slot * element_width + word;
                        *item_word = self.builder.ins().select(active, values[index], *item_word);
                        values[index] = self.builder.ins().select(active, zero, values[index]);
                    }
                }
                values.extend(item);
                return Some(values);
            }
            ExprKind::DynArrayEqual {
                left,
                right,
                element,
                capacity,
                negate,
            } => {
                let left = lower!(self.expr(left));
                let right = lower!(self.expr(right));
                let width = self.program.width(*element);
                let one = self.constant(1);
                let length_equal = self.builder.ins().icmp(IntCC::Equal, left[0], right[0]);
                let mut equal = self.builder.ins().uextend(I64, length_equal);
                for slot in 0..*capacity {
                    // A slot participates only while it is inside the live
                    // length of both arrays; equal lengths make one test enough.
                    let active = self.builder.ins().icmp_imm_s(
                        IntCC::UnsignedGreaterThan,
                        left[0],
                        slot as i64,
                    );
                    let mut slot_equal = one;
                    for word in 0..width {
                        let a = left[1 + slot * width + word];
                        let b = right[1 + slot * width + word];
                        let comparison = if let Some(kind) = element.float_kind() {
                            let a = self.float_value(kind, a);
                            let b = self.float_value(kind, b);
                            self.float_binary(kind, &crate::lexer::Kind::EqEq, a, b)
                        } else {
                            let value = self.builder.ins().icmp(IntCC::Equal, a, b);
                            self.builder.ins().uextend(I64, value)
                        };
                        slot_equal = self.builder.ins().band(slot_equal, comparison);
                    }
                    let contribution = self.builder.ins().select(active, slot_equal, one);
                    equal = self.builder.ins().band(equal, contribution);
                }
                let result = if *negate {
                    let value = self.builder.ins().icmp_imm_s(IntCC::Equal, equal, 0);
                    self.builder.ins().uextend(I64, value)
                } else {
                    equal
                };
                return Some(vec![result]);
            }
            ExprKind::Project(base, offset) => {
                let values = lower!(self.expr(base));
                let width = self.program.width(expr.ty);
                if base.ty.is_ref() {
                    let pointer = values[0];
                    return Some(self.load_words(pointer, (*offset * 8) as i32, width));
                }
                return Some(values[*offset..*offset + width].to_vec());
            }
            ExprKind::BytesAt(bytes, index) => {
                let reference = lower!(self.scalar(bytes));
                let index = lower!(self.scalar(index));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                // Proved in bounds: no check. Data follows the 16-byte header.
                let address = self.builder.ins().iadd(handle, index);
                self.builder
                    .ins()
                    .uload8(I64, ir::MemFlagsData::new(), address, 16)
            }
            ExprKind::Slice {
                base,
                start,
                end,
                element,
                check,
                split: _,
                text,
                field,
            } => {
                if *text {
                    let base_values = lower!(self.expr(base));
                    let (pointer, length) = self.text_view_source(base.ty, &base_values);
                    let start = match start {
                        Some(start) => lower!(self.scalar(start)),
                        None => self.constant(0),
                    };
                    let end = match end {
                        Some(end) => lower!(self.scalar(end)),
                        None => length,
                    };
                    return Some(self.finish_text_view(pointer, length, start, end, *check));
                }
                let element_width = self.program.width(*element);
                let array_location = match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot)
                        if base
                            .ty
                            .layout()
                            .is_some_and(|id| self.program.enums[id].array.is_some()) =>
                    {
                        self.locations[*slot]
                    }
                    _ => None,
                };
                // A checked DynArray view borrows the pinned record storage, so
                // the descriptor points at the live inline slots. The length is
                // the runtime length word, and the capacity is the static bound.
                // A view over a record field points at the field's word offset
                // inside the pinned record storage.
                let dynamic_array_location = match &base.kind {
                    ExprKind::Borrow(slot)
                        if base
                            .ty
                            .ref_pointee()
                            .and_then(|pointee| self.program.pointees.get(pointee).copied())
                            .and_then(|pointee| pointee.layout())
                            .is_some_and(|id| self.program.enums[id].dynamic_array.is_some()) =>
                    {
                        self.locations[*slot].map(|location| (location, 0))
                    }
                    _ if field.is_some() => {
                        let (slot, offset) = projection_offset(base)
                            .expect("checked record-field DynArray view root");
                        let mut root = base.as_ref();
                        while let ExprKind::Project(inner, _) = &root.kind {
                            root = inner;
                        }
                        if root.ty.is_ref() {
                            // Through a record reference: the record lives at
                            // the reference's pointer, not in this frame.
                            let pointer = self.local_words(slot)[0];
                            Some((pointer, offset))
                        } else {
                            if let Some((slot, init)) = projection_root_init(base) {
                                // A temporary record root is initialized at the
                                // view's source position into its hidden slot.
                                let values = lower!(self.expr(init));
                                self.consume(init);
                                self.store_initialized_owner(slot, &values);
                            }
                            self.locations[slot].map(|location| (location, offset))
                        }
                    }
                    _ => None,
                };
                let base_values = if array_location.is_some() || dynamic_array_location.is_some() {
                    Vec::new()
                } else {
                    lower!(self.expr(base))
                };
                let (pointer, length, stride, bytes) = self.view_source(
                    base.ty,
                    element_width,
                    array_location,
                    dynamic_array_location,
                    &base_values,
                );
                let start = match start {
                    Some(start) => lower!(self.scalar(start)),
                    None => self.constant(0),
                };
                let end = match end {
                    Some(end) => lower!(self.scalar(end)),
                    None => length,
                };
                return Some(self.finish_view(pointer, length, stride, bytes, start, end, *check));
            }
            ExprKind::While(condition, body) => {
                self.lower_while(condition, body);
                self.constant(0)
            }
            ExprKind::Loop(body) => {
                let head = self.builder.create_block();
                let exit = self.join(expr.ty);
                let depth = self.capture_handler_depth();
                self.jump(head, &[]);
                self.builder.switch_to_block(head);
                // A loop without break has type Never; its exit is never targeted.
                let target = exit.unwrap_or(head);
                self.loops.push((head, target, true, depth));
                let finished = self.block(body);
                self.loops.pop();
                if finished.is_some() {
                    self.jump(head, &[]);
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::Break(value, cleanup) => {
                let (_, exit, carries, depth) = *self.loops.last().unwrap();
                let values = match value {
                    Some(value) => {
                        let values = lower!(self.expr(value));
                        self.consume(value);
                        values
                    }
                    None if carries => vec![self.constant(0)],
                    None => vec![],
                };
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                self.restore_handler_depth(depth);
                self.jump(exit, &values);
                return None;
            }
            ExprKind::Continue(cleanup) => {
                let (head, _, _, depth) = *self.loops.last().unwrap();
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                self.restore_handler_depth(depth);
                self.jump(head, &[]);
                return None;
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                return Some(self.local_words(*slot));
            }
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Construct {
                enum_id,
                tag,
                fields,
            } => {
                let mut payload = Vec::new();
                for field in fields {
                    payload.extend(lower!(self.expr(field)));
                }
                for field in fields {
                    self.consume(field);
                }
                return Some(self.encode_variant(Type::Enum(*enum_id), *tag, &payload));
            }
            ExprKind::Try {
                value,
                input,
                output,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let condition =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], input.ok_tag as i64);
                let success = self.builder.create_block();
                let failure = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(condition, success, &[], failure, &[]);
                self.builder.switch_to_block(failure);
                let mut error = vec![self.constant(output.err_tag as i64)];
                error.extend_from_slice(&values[1..1 + self.program.width(input.error)]);
                while error.len() < self.program.width(self.result) {
                    error.push(self.constant(0));
                }
                self.cleanup_all();
                self.return_value(&error);
                self.builder.switch_to_block(success);
                return Some(values[1..1 + self.program.width(input.ok)].to_vec());
            }
            ExprKind::Unary(op, operand) => {
                let value = lower!(self.scalar(operand));
                let deferral = self.deferral(expr);
                return self
                    .unary_value(
                        expr.span,
                        op,
                        operand.ty,
                        value,
                        deferral,
                        deferred::key(operand),
                    )
                    .map(|value| vec![value]);
            }
            ExprKind::Assign(slot, replacement) => {
                if self.vec_shadows.contains_key(slot) {
                    // By construction of the shadow, this is `v = push(v, e)`.
                    self.pending_pushes
                        .push((std::ptr::from_ref::<Expr>(replacement) as usize, *slot));
                }
                let value = lower!(self.expr(replacement));
                self.consume(replacement);
                if !self.erased_local(*slot) {
                    self.cleanup(
                        self.program.functions[self.function_index].local_resources[*slot],
                    );
                    self.assign(*slot, &value);
                    self.activate_local(*slot);
                } else if self.program.owns(replacement.ty) {
                    self.drop_value(replacement.ty, &value);
                }
                self.constant(0)
            }
            ExprKind::RefRead(reference) => {
                let pointer = lower!(self.scalar(reference));
                return Some(self.load_words(pointer, 0, self.program.width(expr.ty)));
            }
            ExprKind::RefAssign(reference, offset, replacement) => {
                let pointer = lower!(self.scalar(reference));
                let value = lower!(self.expr(replacement));
                for (index, word) in value.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        ((offset + index) * 8) as i32,
                    );
                }
                self.consume(replacement);
                self.constant(0)
            }
            ExprKind::StructEq {
                left,
                right,
                negated,
            } => {
                let ty = left.ty;
                let left = lower!(self.expr(left));
                let right = lower!(self.expr(right));
                let equal = self.struct_eq_words(ty, &left, &right);
                let value = if *negated {
                    self.builder.ins().bxor_imm_s(equal, 1)
                } else {
                    equal
                };
                return Some(vec![self.builder.ins().uextend(I64, value)]);
            }
            ExprKind::Binary(op, left, right_expr) => {
                let left_ty = left.ty;
                let left_kind = left.ty.int_kind();
                let left_key = deferred::key(left);
                let left = lower!(self.scalar(left));
                if matches!(op, Kind::AmpAmp | Kind::PipePipe) {
                    return self.short_circuit(op, left, right_expr);
                }
                let right_kind = right_expr.ty.int_kind();
                let right = lower!(self.scalar(right_expr));
                self.fuzz_arith(expr.span, op, left_kind, right_kind, left, right);
                if let Some(kind) = left_ty.float_kind() {
                    let left = self.float_value(kind, left);
                    let right = self.float_value(kind, right);
                    return Some(vec![self.float_binary(kind, op, left, right)]);
                }
                let deferral = self.deferral(expr);
                if matches!(
                    deferral,
                    Some(deferred::Mode::Certified | deferred::Mode::Accumulate)
                ) {
                    self.track_leaf(left_key, left);
                    self.track_leaf(deferred::key(right_expr), right);
                }
                return Some(vec![
                    self.scalar_binary(op, left_kind, right_kind, left, right, deferral),
                ]);
            }
            ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
                grow,
            } => {
                let mut handle = lower!(self.scalar(vector));
                let plans = callbacks
                    .iter()
                    .map(|callback| {
                        self.codegen
                            .inline_scalar_callbacks
                            .then(|| ScalarCallback::callback(self.program, callback))
                            .flatten()
                    })
                    .collect::<Vec<_>>();
                let mut codes = Vec::with_capacity(callbacks.len());
                for callback in callbacks {
                    codes.push(lower!(self.scalar(callback)));
                }
                self.consume(vector);
                for callback in callbacks {
                    self.consume(callback);
                }
                let source_width = self.program.width(*source);
                let target_width = self.program.width(*target);
                let element_width = if *grow {
                    // Grow or compact storage once, move elements safely, and
                    // update the header before any callback runs. The loop then
                    // reads and writes at the final stride in source order.
                    let source_words = self.constant(source_width as i64);
                    let target_words = self.constant(target_width as i64);
                    handle =
                        self.runtime_call(self.vec_restride, &[handle, source_words, target_words]);
                    target_width
                } else {
                    source_width
                };
                let length = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0);
                let head = self.builder.create_block();
                let body = self.builder.create_block();
                let done = self.builder.create_block();
                self.builder.append_block_param(head, I64);
                let zero = self.constant(0);
                self.jump(head, &[zero]);
                self.builder.switch_to_block(head);
                let index = self.builder.block_params(head)[0];
                let more = self
                    .builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, index, length);
                self.builder.ins().brif(more, body, &[], done, &[]);
                self.builder.switch_to_block(body);
                // Elements are transferred to the callback by value; storage is
                // overwritten only with the callback's result.
                let stride = self
                    .builder
                    .ins()
                    .imul_imm_s(index, (element_width * 8) as i64);
                let address = self.builder.ins().iadd(handle, stride);
                // The destination stride is the final width, but the value
                // currently in the slot still has the source width until the
                // first callback consumes it.
                let mut current = self.load_words(address, 16, source_width);
                for ((code, callback), plan) in codes.iter().zip(callbacks.iter()).zip(&plans) {
                    if let Some(plan) = plan
                        && current.len() == 1
                    {
                        current = vec![plan.emit(&mut self.builder, current[0])];
                        continue;
                    }
                    let Type::Fn(id) = callback.ty else {
                        unreachable!("checked map callback")
                    };
                    let signature = self.program.function_types[id].clone();
                    let result = signature.result;
                    let pointer = if aggregate_result(self.program, result) {
                        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                            ir::StackSlotKind::ExplicitSlot,
                            (self.program.width(result) * 8).max(1) as u32,
                            STACK_SLOT_ALIGN_SHIFT,
                        ));
                        Some(self.builder.ins().stack_addr(I64, slot, 0))
                    } else {
                        None
                    };
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    values.extend(current.iter().copied());
                    let signature = self.indirect_signature(id);
                    let signature = self.builder.import_signature(signature);
                    let call = self.builder.ins().call_indirect(signature, *code, &values);
                    self.test_panic();
                    current = if let Some(pointer) = pointer {
                        self.load_words(pointer, 0, self.program.width(result))
                    } else {
                        self.builder.inst_results(call).to_vec()
                    };
                }
                let destination_stride = self
                    .builder
                    .ins()
                    .imul_imm_s(index, (target_width * 8) as i64);
                let destination = self.builder.ins().iadd(handle, destination_stride);
                for (word, value) in current.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        destination,
                        (16 + word * 8) as i32,
                    );
                }
                let next = self.builder.ins().iadd_imm_s(index, 1);
                self.jump(head, &[next]);
                self.builder.switch_to_block(done);
                // Subsequent monomorphized operations use the result's static width.
                handle
            }
            ExprKind::TaskSpawn {
                body,
                result,
                obligation,
                parallel,
            } => {
                let values = lower!(self.expr(body));
                let Type::Once(id) = body.ty else {
                    unreachable!("checked task body is once")
                };
                self.consume(body);
                let wrapper = self.task_wrappers[&id];
                let wrapper = self.module.declare_func_in_func(wrapper, self.builder.func);
                let wrapper = self.builder.ins().func_addr(I64, wrapper);
                let bytes = self.constant((self.program.width(*result).max(1) * 8) as i64);
                let drop = if self.program.owns(*result) {
                    let drop = self.task_pointer_drops[&result.full()];
                    let drop = self.module.declare_func_in_func(drop, self.builder.func);
                    self.builder.ins().func_addr(I64, drop)
                } else {
                    self.constant(0)
                };
                let preserve = self.constant(i64::from(*obligation));
                let spawn = if *parallel {
                    self.thread_spawn
                } else {
                    self.task_spawn
                };
                self.runtime_call(
                    spawn,
                    &[wrapper, values[0], values[1], bytes, drop, preserve],
                )
            }
            ExprKind::TaskScope {
                body,
                result,
                failure,
                catch,
                parallel,
                ..
            } => {
                let (scope_begin, scope_end) = if *parallel {
                    (self.thread_scope_begin, self.thread_scope_end)
                } else {
                    (self.task_scope_begin, self.task_scope_end)
                };
                let values = lower!(self.expr(body));
                let Type::Once(id) = body.ty else {
                    unreachable!("checked scope body is once")
                };
                self.consume(body);
                let result_ty = self.program.function_types[id].result;
                let aggregate = aggregate_result(self.program, result_ty);
                let pointer = if aggregate {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result_ty).max(1) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    Some(self.builder.ins().stack_addr(I64, slot, 0))
                } else {
                    None
                };
                // PANIC-UNWIND-USE: `Task.catch` is a scope that is also a
                // catch boundary; its value is `Result<T, Panic>`.
                let caught = catch.map(|shape| (shape, self.join(expr.ty).unwrap()));
                if caught.is_some() {
                    self.runtime_void(self.catch_enter, &[]);
                }
                self.runtime_void(scope_begin, &[]);
                let mut arguments = Vec::new();
                if let Some(pointer) = pointer {
                    arguments.push(pointer);
                }
                arguments.push(values[1]);
                let signature = self.indirect_signature(id);
                let signature = self.builder.import_signature(signature);
                let call = self
                    .builder
                    .ins()
                    .call_indirect(signature, values[0], &arguments);
                if self.program.uses_unwinding {
                    // A panic unwinding out of the body: cancel and join the
                    // children with the word clear (other tasks run during
                    // the join), then stop here (a catch) or go on unwinding.
                    let address = self.abort_word_address();
                    let word = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), address, 0);
                    let panicked = self.builder.ins().icmp_imm_s(IntCC::Equal, word, 1);
                    let unwind = self.builder.create_block();
                    let normal = self.builder.create_block();
                    self.builder.ins().brif(panicked, unwind, &[], normal, &[]);
                    self.builder.switch_to_block(unwind);
                    let zero = self.constant(0);
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), zero, address, 0);
                    if !*parallel {
                        self.runtime_void(self.task_cancel_scope, &[]);
                    }
                    self.runtime_void_raw(scope_end, &[]);
                    let address = self.abort_word_address();
                    if let Some((shape, join)) = caught {
                        let zero = self.constant(0);
                        self.builder
                            .ins()
                            .store(ir::MemFlagsData::new(), zero, address, 0);
                        self.runtime_void(self.catch_leave, &[]);
                        let values = self.encode_variant(expr.ty, shape.err_tag, &[]);
                        self.jump(join, &values);
                    } else {
                        let one = self.constant(1);
                        self.builder
                            .ins()
                            .store(ir::MemFlagsData::new(), one, address, 0);
                        self.unwind_exit();
                    }
                    self.builder.switch_to_block(normal);
                }
                let result_values = if let Some(pointer) = pointer {
                    self.load_words(pointer, 0, self.program.width(result_ty))
                } else {
                    self.builder.inst_results(call).to_vec()
                };
                if result_ty == Type::Never {
                    self.runtime_void_raw(scope_end, &[]);
                    if let Some((_, join)) = caught {
                        self.builder.ins().trap(TrapCode::unwrap_user(1));
                        self.builder.switch_to_block(join);
                        return Some(self.builder.block_params(join).to_vec());
                    }
                    self.test_panic();
                    return None;
                }
                if let Some(shape) = *failure {
                    let failed = self.builder.create_block();
                    let succeeded = self.builder.create_block();
                    let done = self.builder.create_block();
                    let condition = self.builder.ins().icmp_imm_s(
                        IntCC::Equal,
                        result_values[0],
                        shape.err_tag as i64,
                    );
                    self.builder
                        .ins()
                        .brif(condition, failed, &[], succeeded, &[]);
                    self.builder.switch_to_block(failed);
                    self.runtime_void(self.task_cancel_scope, &[]);
                    self.jump(done, &[]);
                    self.builder.switch_to_block(succeeded);
                    self.jump(done, &[]);
                    self.builder.switch_to_block(done);
                }
                // The epilogue raises the panic of a child it joined.
                self.runtime_void_raw(scope_end, &[]);
                let _ = result;
                let Some((shape, join)) = caught else {
                    self.test_panic();
                    return Some(result_values);
                };
                let address = self.abort_word_address();
                let word = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), address, 0);
                let panicked = self.builder.ins().icmp_imm_s(IntCC::Equal, word, 1);
                let child = self.builder.create_block();
                let fine = self.builder.create_block();
                self.builder.ins().brif(panicked, child, &[], fine, &[]);
                self.builder.switch_to_block(child);
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, address, 0);
                // The body's result is dropped: the catch answers Err.
                self.drop_value(result_ty, &result_values);
                self.runtime_void(self.catch_leave, &[]);
                let values = self.encode_variant(expr.ty, shape.err_tag, &[]);
                self.jump(join, &values);
                self.builder.switch_to_block(fine);
                self.runtime_void(self.catch_leave, &[]);
                let values = self.encode_variant(expr.ty, shape.ok_tag, &result_values);
                self.jump(join, &values);
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::TaskYield => self.runtime_call(self.task_yield, &[]),
            ExprKind::TaskCheckCancel => self.runtime_call(self.task_check_cancel, &[]),
            ExprKind::TaskCancel(reference) => {
                let pointer = lower!(self.scalar(reference));
                self.runtime_void(self.task_cancel, &[pointer]);
                self.constant(0)
            }
            ExprKind::TaskJoin {
                task,
                exit,
                parallel: true,
                ..
            } => {
                // A thread always completes: its join yields the payload.
                let handle = lower!(self.scalar(task));
                self.consume(task);
                let width = self.program.width(exit.payload).max(1);
                let out = self.stack_words(width);
                let status = self.runtime_call(self.thread_join, &[handle, out]);
                self.rethrow_if_panicked(status);
                return Some(self.load_words(out, 0, self.program.width(exit.payload)));
            }
            ExprKind::TaskJoin { task, exit, .. } => {
                let handle = lower!(self.scalar(task));
                self.consume(task);
                let width = self.program.width(exit.payload).max(1);
                let out = self.stack_words(width);
                let status = self.runtime_call(self.task_join, &[handle, out]);
                self.rethrow_if_panicked(status);
                let completed = self.builder.create_block();
                let cancelled = self.builder.create_block();
                let join = self.join(exit.result).unwrap();
                let condition = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                self.builder
                    .ins()
                    .brif(condition, completed, &[], cancelled, &[]);
                self.builder.switch_to_block(completed);
                let payload = self.load_words(out, 0, width);
                let values = self.encode_variant(exit.result, exit.completed_tag, &payload);
                self.jump(join, &values);
                self.builder.switch_to_block(cancelled);
                let payload = self.load_words(out, 0, width);
                self.drop_value(exit.payload, &payload);
                let values = self.encode_variant(exit.result, exit.cancelled_tag, &[]);
                self.jump(join, &values);
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::Call(target, args) => {
                let erased_parameters = match target {
                    Target::Function(index) => {
                        let function = &self.program.functions[*index];
                        (0..args.len())
                            .map(|position| {
                                function
                                    .parameter_grades
                                    .get(position)
                                    .copied()
                                    .flatten()
                                    .is_some_and(Grade::is_zero)
                            })
                            .collect::<Vec<_>>()
                    }
                    _ => Vec::new(),
                };
                let mut values = Vec::new();
                for (position, arg) in args.iter().enumerate() {
                    let words = lower!(self.expr(arg));
                    if erased_parameters.get(position).copied() != Some(true) {
                        values.extend(words);
                    }
                }
                for arg in args {
                    self.consume(arg);
                }
                let site = (std::ptr::from_ref(expr) as usize, deferred::key(expr));
                return self.call_target(target, values, expr.ty, expr.span, Some(site));
            }
            ExprKind::Return(arg) => {
                let value = lower!(self.expr(arg));
                self.consume(arg);
                self.cleanup_all();
                let erased_result = self.program.functions[self.function_index]
                    .result_grade
                    .is_some_and(Grade::is_zero);
                if erased_result {
                    self.drop_value(arg.ty, &value);
                    self.return_value(&[]);
                } else {
                    self.return_value(&value);
                }
                return None;
            }
            ExprKind::If(condition, yes, no) => {
                let condition = lower!(self.scalar(condition));
                let hit = self.builder.create_block();
                let miss = self.builder.create_block();
                let join = self.join(expr.ty);
                self.builder.ins().brif(condition, hit, &[], miss, &[]);
                self.builder.switch_to_block(hit);
                if let Some(values) = self.block(yes) {
                    self.jump(join.unwrap(), &values);
                }
                self.builder.switch_to_block(miss);
                if let Some(values) = self.block(no) {
                    self.jump(join.unwrap(), &values);
                }
                let join = join?;
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::Match(value, arms) => {
                let input = value;
                let value = lower!(self.expr(input));
                // A borrowed DynArray scrutinee is a pointer: patterns test the
                // loaded words, and element names bind slot addresses.
                let borrowed = match input.ty {
                    Type::Ref(pointer) | Type::RefMut(pointer) => {
                        let pointee = self.program.pointees[pointer];
                        let words = self.program.width(pointee);
                        Some((value[0], self.load_words(value[0], 0, words)))
                    }
                    _ => None,
                };
                let tested = borrowed
                    .as_ref()
                    .map(|(_, words)| words.clone())
                    .unwrap_or_else(|| value.clone());
                let join = self.join(expr.ty);
                for arm in arms {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition = self.pattern(&arm.pattern, &tested);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    match &borrowed {
                        Some((pointer, words)) => {
                            self.bind_borrowed_dyn(&arm.pattern, *pointer, words)
                        }
                        None => self.bind_pattern(&arm.pattern, &value),
                    }
                    let mut body_reachable = true;
                    if let Some(guard) = &arm.guard {
                        if let Some(guard) = self.scalar(guard) {
                            let body = self.builder.create_block();
                            self.builder.ins().brif(guard, body, &[], next, &[]);
                            self.builder.switch_to_block(body);
                        } else {
                            body_reachable = false;
                        }
                    }
                    if body_reachable {
                        self.consume(input);
                        if borrowed.is_none() {
                            self.dispose_pattern(&arm.pattern, input.ty, &value);
                        }
                        if let Some(body) = self.expr(&arm.body) {
                            self.consume(&arm.body);
                            let mut slots = std::collections::BTreeSet::new();
                            crate::ownership::pattern_bindings(&arm.pattern, &mut slots);
                            for slot in slots.into_iter().rev() {
                                self.cleanup(
                                    self.program.functions[self.function_index].local_resources
                                        [slot],
                                );
                            }
                            self.jump(join.unwrap(), &body);
                        }
                    }
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                let join = join?;
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
        };
        Some(vec![scalar])
    }
    /// Evaluate one allocator operand into `(alloc, release, realloc,
    /// context)`. The legacy value supplies three code pointers and no
    /// context; an instance context supplies one retained handle and selects
    /// its thunks inside the runtime helpers.
    fn allocator_words(&mut self, allocator: &Expr) -> Option<[Value; 4]> {
        let values = self.expr(allocator)?;
        let zero = self.constant(0);
        match allocator.ty {
            Type::Allocator => Some([values[0], values[1], values[2], zero]),
            Type::AllocatorContext => Some([zero, zero, zero, values[0]]),
            _ => unreachable!("checked allocator operand"),
        }
    }
    /// Allocate one owned dynamic-object payload and copy the concrete member
    /// words into it. The corresponding `free` happens in `drop_value` for an
    /// owned object or immediately before an owning method consumes it.
    fn allocate_dyn_payload(&mut self, ty: Type, values: &[Value]) -> Value {
        let bytes = self.constant((self.program.width(ty) * 8) as i64);
        let pointer = self.runtime_call(self.allocate, &[bytes]);
        for (index, value) in values.iter().enumerate() {
            self.builder
                .ins()
                .store(ir::MemFlagsData::new(), *value, pointer, (index * 8) as i32);
        }
        pointer
    }
    fn stack_words(&mut self, words: usize) -> Value {
        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            (words.max(1) * 8) as u32,
            STACK_SLOT_ALIGN_SHIFT,
        ));
        self.builder.ins().stack_addr(I64, slot, 0)
    }
    /// Read one local's words without moving it.
    fn local_words(&mut self, slot: usize) -> Words {
        if let Some(pointer) = self.locations[slot] {
            let width = self.variables[slot].len();
            return self.load_words(pointer, 0, width);
        }
        let mut words: Words = self.variables[slot]
            .iter()
            .map(|v| self.builder.use_var(*v))
            .collect();
        if let Some((stride, bytes)) = self.slice_layouts.get(&slot).copied() {
            words[2] = self.constant(stride);
            words[3] = self.constant(bytes);
        }
        words
    }
    /// Store a temporary-owner initializer in its already-declared hidden
    /// slot, releasing any previous value from an earlier loop evaluation.
    #[inline(never)]
    fn store_initialized_owner(&mut self, slot: usize, values: &[Value]) {
        let id = self.program.functions[self.function_index].local_resources[slot];
        self.cleanup(id);
        self.assign(slot, values);
        self.activate_local(slot);
    }
    /// Borrow one direct local binding, giving inline aggregates and owning
    /// handles their pinned address.
    fn borrow_local_value(&mut self, slot: usize) -> Words {
        let local = &self.program.functions[self.function_index].locals[slot];
        let record = local
            .ty
            .layout()
            .is_some_and(|id| self.program.enums[id].record);
        if record || local.pinned || matches!(local.ty, Type::Union(_) | Type::DynObj(_)) {
            let pointer = self.locations[slot]
                .expect("checked inline object borrow is pinned to stack storage");
            return vec![pointer];
        }
        if matches!(
            local.ty,
            Type::Box(_)
                | Type::ArenaBox(_)
                | Type::Arena
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
        ) {
            let pointer =
                self.locations[slot].expect("checked owner borrow is pinned to stack storage");
            return vec![pointer];
        }
        let variable = self.builder.use_var(self.variables[slot][0]);
        let stack = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            8,
            STACK_SLOT_ALIGN_SHIFT,
        ));
        let pointer = self.builder.ins().stack_addr(I64, stack, 0);
        self.builder
            .ins()
            .store(ir::MemFlagsData::new(), variable, pointer, 0);
        vec![pointer]
    }
    /// Address of one local's pinned storage, materializing an explicit stack
    /// slot for a scalar or enum that was never pinned.
    fn local_address(&mut self, slot: usize) -> Value {
        if let Some(pointer) = self.locations[slot] {
            return pointer;
        }
        let variable = self.builder.use_var(self.variables[slot][0]);
        let stack = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            (self.variables[slot].len().max(1) * 8) as u32,
            STACK_SLOT_ALIGN_SHIFT,
        ));
        let pointer = self.builder.ins().stack_addr(I64, stack, 0);
        self.builder
            .ins()
            .store(ir::MemFlagsData::new(), variable, pointer, 0);
        pointer
    }
    /// Address of a checked place expression: a pinned local or a chain of
    /// aggregate field projections over one. Only read-only projected dispatch
    /// uses this, so no relocation or ownership transfer happens here.
    /// `None` means evaluating a temporary initializer transferred control, so
    /// the surrounding expression lowering must stop emitting straight-line
    /// code.
    fn place_address(&mut self, expr: &Expr) -> Option<Value> {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Peek(slot) => Some(self.local_address(*slot)),
            ExprKind::InitOwner { slot, value: init } => {
                // Initialize temporary backing storage at the place's source
                // position, then address that stable slot.
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                Some(self.local_address(*slot))
            }
            ExprKind::Project(base, offset) => {
                let base_pointer = if base.ty.is_ref() {
                    lower!(self.expr(base))[0]
                } else {
                    lower!(self.place_address(base))
                };
                Some(
                    self.builder
                        .ins()
                        .iadd_imm_s(base_pointer, (*offset * 8) as i64),
                )
            }
            ExprKind::PlaceIndex { base, index, .. } if base.ty.is_slice() => {
                // A slice view is a `(data, length, stride, byte)` descriptor.
                // The element address is `data + index * stride` after the
                // bound check; a byte-backed view has no word-sized element
                // and traps instead.
                let descriptor = lower!(self.expr(base));
                let index = lower!(self.scalar(index));
                let negative = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, index, 0);
                let beyond =
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedGreaterThanOrEqual, index, descriptor[1]);
                let bytes = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::NotEqual, descriptor[3], 0);
                let invalid = self.builder.ins().bor(negative, beyond);
                let invalid = self.builder.ins().bor(invalid, bytes);
                self.guard(invalid);
                let offset = self.builder.ins().imul(index, descriptor[2]);
                Some(self.builder.ins().iadd(descriptor[0], offset))
            }
            ExprKind::PlaceIndex { base, index, .. } => {
                let location = lower!(self.place_address(base));
                let index = lower!(self.scalar(index));
                if let Type::Vec(element) = base.ty {
                    let handle = self.load_words(location, 0, 1)[0];
                    let width =
                        self.constant(self.program.width(self.program.pointees[element]) as i64);
                    return Some(self.runtime_call(self.vec_element, &[handle, index, width]));
                }
                let (element, length) = base
                    .ty
                    .layout()
                    .and_then(|id| self.program.enums[id].array)
                    .expect("checked array index place");
                self.check_index(index, length as i64);
                let stride = (self.program.width(element) * 8) as i64;
                let offset = self.builder.ins().imul_imm_s(index, stride);
                let data = self.builder.ins().iadd_imm_s(location, 8);
                Some(self.builder.ins().iadd(data, offset))
            }
            _ => unreachable!("checked projected borrow has a place expression"),
        }
    }
    fn store_words(&mut self, pointer: Value, values: &[Value]) {
        for (i, v) in values.iter().enumerate() {
            self.builder
                .ins()
                .store(ir::MemFlagsData::new(), *v, pointer, (i * 8) as i32);
        }
    }
    fn load_words(&mut self, pointer: Value, offset: i32, words: usize) -> Words {
        (0..words)
            .map(|i| {
                self.builder.ins().load(
                    I64,
                    ir::MemFlagsData::new(),
                    pointer,
                    offset + (i * 8) as i32,
                )
            })
            .collect()
    }
    /// Reject a text range endpoint that falls inside a UTF-8 continuation
    /// sequence. `index` must already be in `0..=length`; `index == length` is
    /// always a boundary and is not dereferenced.
    fn check_text_boundary(&mut self, pointer: Value, index: Value, length: Value) {
        let at_end = self.builder.ins().icmp(IntCC::Equal, index, length);
        let check = self.builder.create_block();
        let good = self.builder.create_block();
        self.builder.ins().brif(at_end, good, &[], check, &[]);
        self.builder.switch_to_block(check);
        let address = self.builder.ins().iadd(pointer, index);
        let byte = self
            .builder
            .ins()
            .uload8(I64, ir::MemFlagsData::new(), address, 0);
        let masked = self.builder.ins().band_imm_s(byte, 0xC0);
        let continuation = self.builder.ins().icmp_imm_s(IntCC::Equal, masked, 0x80);
        let bad = self.builder.create_block();
        let ok = self.builder.create_block();
        self.builder.ins().brif(continuation, bad, &[], ok, &[]);
        self.builder.switch_to_block(bad);
        self.abort();
        self.builder.switch_to_block(ok);
        self.jump(good, &[]);
        self.builder.switch_to_block(good);
    }
    fn check_range(&mut self, start: Value, end: Value, length: Value) {
        let negative = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, start, 0);
        let reversed = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThan, start, end);
        let beyond = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThan, end, length);
        let invalid = self.builder.ins().bor(negative, reversed);
        let invalid = self.builder.ins().bor(invalid, beyond);
        self.guard(invalid);
    }
    fn encode_variant(&mut self, ty: Type, tag: usize, payload: &[Value]) -> Words {
        let layout = ty.layout().expect("enum constructor layout");
        let definition = &self.program.enums[layout];
        if let Some(niche) = definition.niche() {
            // Encoding is the inverse of the certificate's decoder: an empty
            // variant stores its constant, the payload keeps its own words.
            return match niche.decoder(tag) {
                crate::layout_cert::Decoder::Equal(constant) => vec![self.constant(constant)],
                crate::layout_cert::Decoder::NotEqual(_) => {
                    debug_assert_eq!(payload.len(), 1);
                    payload.to_vec()
                }
            };
        }
        let mut words = Vec::with_capacity(definition.words);
        if definition.tag_words() != 0 {
            words.push(self.constant(tag as i64));
        }
        words.extend_from_slice(payload);
        while words.len() < self.program.width(ty) {
            words.push(self.constant(0));
        }
        words
    }
    fn optional_words(
        &mut self,
        ty: Type,
        present: Value,
        payload: &[Value],
        some: usize,
        none: usize,
    ) -> Words {
        let some = self.encode_variant(ty, some, payload);
        let none = self.encode_variant(ty, none, &[]);
        some.into_iter()
            .zip(none)
            .map(|(some, none)| self.builder.ins().select(present, some, none))
            .collect()
    }
    fn str_call(&mut self, op: StrOp, values: Words, ty: Type) -> Words {
        let (pointer, length) = (values[0], values[1]);
        match op {
            StrOp::Len => vec![length],
            StrOp::ScalarLen => vec![self.runtime_call(self.str_scalar_len, &[pointer, length])],
            StrOp::ByteAt => {
                vec![self.runtime_call(self.str_byte_at, &[pointer, length, values[4]])]
            }
            StrOp::ScalarAt { some_tag, none_tag } => {
                let codepoint =
                    self.runtime_call(self.str_scalar_at, &[pointer, length, values[4]]);
                let present =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, codepoint, 0);
                self.optional_words(ty, present, &[codepoint], some_tag, none_tag)
            }
            StrOp::ToString => {
                vec![self.runtime_call(self.str_to_string, &[pointer, length])]
            }
            StrOp::AsciiUpper => {
                self.runtime_call(self.str_writes[0], &[pointer, length]);
                vec![]
            }
            StrOp::AsciiLower => {
                self.runtime_call(self.str_writes[1], &[pointer, length]);
                vec![]
            }
            StrOp::SetScalar => {
                self.runtime_call(self.str_writes[2], &[pointer, length, values[4], values[5]]);
                vec![]
            }
        }
    }
    /// Compare the words of two structural records field by field. The checker
    /// admits only scalar leaves and nested structural rows, so every compared
    /// word is a copyable representation word.
    fn struct_eq_words(&mut self, ty: Type, left: &[Value], right: &[Value]) -> Value {
        let layout = ty
            .layout()
            .expect("checked structural equality has a layout");
        let types = self.program.enums[layout].variants[0].fields.clone();
        let mut result: Option<Value> = None;
        let mut offset = self.program.enums[layout].tag_words();
        for field in types {
            let width = self.program.width(field);
            if width > 0 {
                let equal = if field.layout().is_some() {
                    self.struct_eq_words(
                        field,
                        &left[offset..offset + width],
                        &right[offset..offset + width],
                    )
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::Equal, left[offset], right[offset])
                };
                result = Some(match result {
                    Some(previous) => self.builder.ins().band(previous, equal),
                    None => equal,
                });
            }
            offset += width;
        }
        match result {
            Some(value) => value,
            None => {
                let zero = self.constant(0);
                self.builder.ins().icmp_imm_s(IntCC::Equal, zero, 0i64)
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn struct_coercion_words(
        &mut self,
        source: Type,
        target_fields: &[Type],
        kept: &[(usize, usize, Option<Coercion>)],
        drops: &[(usize, Type)],
        values: &[Value],
        out: &mut Vec<Value>,
    ) {
        let source_id = source.layout().expect("checked structural source layout");
        let source_fields = self.program.enums[source_id].variants[0].fields.clone();
        let mut offsets = Vec::with_capacity(source_fields.len());
        let mut offset = self.program.enums[source_id].tag_words();
        for field in &source_fields {
            offsets.push(offset);
            offset += self.program.width(*field);
        }
        for (target_index, source_index, coercion) in kept {
            let start = offsets[*source_index];
            let field_width = self.program.width(source_fields[*source_index]);
            let field = &values[start..start + field_width];
            match coercion {
                Some(coercion) => out.extend(self.nested_coercion_words(
                    coercion,
                    target_fields[*target_index],
                    field,
                )),
                None => out.extend(field.iter().copied()),
            }
        }
        for (source_index, ty) in drops {
            let start = offsets[*source_index];
            let field_width = self.program.width(*ty);
            self.drop_value(*ty, &values[start..start + field_width]);
        }
    }
    fn nested_coercion_words(&mut self, coercion: &Coercion, to: Type, values: &[Value]) -> Words {
        let width = self.program.width(to);
        match coercion {
            Coercion::Inject { tag } => {
                let mut out = Vec::with_capacity(width);
                out.push(self.constant(*tag as i64));
                out.extend(values.iter().copied().take(width.saturating_sub(1)));
                while out.len() < width {
                    out.push(self.constant(0));
                }
                out
            }
            Coercion::Struct {
                source,
                kept,
                drops,
            } => {
                let target_id = to.layout().expect("checked nested structural target");
                let target_fields = self.program.enums[target_id].variants[0].fields.clone();
                let mut out = vec![self.constant(0)];
                self.struct_coercion_words(*source, &target_fields, kept, drops, values, &mut out);
                while out.len() < width {
                    out.push(self.constant(0));
                }
                out
            }
            Coercion::Repack { map } => {
                let exit = self.join(to).expect("nested repack target is not Never");
                for (source_tag, target_tag) in map.iter().enumerate() {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition =
                        self.builder
                            .ins()
                            .icmp_imm_s(IntCC::Equal, values[0], source_tag as i64);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    let mut out = Vec::with_capacity(width);
                    out.push(self.constant(*target_tag as i64));
                    out.extend(values.iter().copied().skip(1).take(width.saturating_sub(1)));
                    while out.len() < width {
                        out.push(self.constant(0));
                    }
                    self.jump(exit, &out);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(exit);
                self.builder.block_params(exit).to_vec()
            }
            Coercion::DynBox {
                member,
                member_type,
                ..
            } => {
                let pointer = self.allocate_dyn_payload(*member_type, values);
                vec![self.constant(*member as i64), pointer]
            }
            Coercion::DynUpcast { from, to } => self.dyn_upcast(*from, *to, values),
            Coercion::Callable {
                function,
                capture,
                target,
            } => {
                let reference = self
                    .module
                    .declare_func_in_func(self.ids[*function], self.builder.func);
                let code = self.builder.ins().func_addr(I64, reference);
                if !matches!(target, Type::Once(_)) {
                    return vec![code];
                }
                let Some(capture_ty) = capture else {
                    return vec![code, self.constant(0)];
                };
                let types = vec![capture_ty.full()];
                let bytes = 8 + self.program.width(*capture_ty) * 8;
                let size = self.constant(bytes as i64);
                let environment = self.runtime_call(self.allocate, &[size]);
                let drop = self.closure_drops[&types];
                let drop = self.module.declare_func_in_func(drop, self.builder.func);
                let drop = self.builder.ins().func_addr(I64, drop);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), drop, environment, 0);
                let width = self.program.width(*capture_ty);
                for (index, value) in values.iter().take(width).enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        environment,
                        8 + (index * 8) as i32,
                    );
                }
                vec![code, environment]
            }
        }
    }
    fn dyn_array_call(&mut self, op: DynArrayOp, element: Type, values: Words) -> Words {
        let pointer = values[0];
        let length = self
            .builder
            .ins()
            .load(I64, ir::MemFlagsData::new(), pointer, 0);
        match op {
            DynArrayOp::Len => vec![length],
            DynArrayOp::Get => {
                let index = values[1];
                let negative = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, index, 0);
                let past_end =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
                let bad = self.builder.ins().bor(negative, past_end);
                self.guard(bad);
                let width = self.program.width(element);
                let stride = self.builder.ins().imul_imm_s(index, (width * 8) as i64);
                let base = self.builder.ins().iadd(pointer, stride);
                (0..width)
                    .map(|word| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            base,
                            (8 + word * 8) as i32,
                        )
                    })
                    .collect()
            }
        }
    }
    /// Lower small byte-buffer operations directly so hot loops can keep their
    /// length loads and bounds checks visible to Cranelift's optimizer. The
    /// unsigned comparison rejects negative indices as well as the upper bound.
    fn bytes_access(&mut self, op: BytesOp, values: &[Value]) -> Value {
        let handle = values[0];
        match op {
            BytesOp::Len => self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 0),
            BytesOp::Capacity => self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 8),
            BytesOp::Get => {
                let length = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0);
                let invalid =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, values[1], length);
                self.guard(invalid);
                let address = self.builder.ins().iadd(handle, values[1]);
                self.builder
                    .ins()
                    .uload8(I64, ir::MemFlagsData::new(), address, 16)
            }
            BytesOp::Clear => {
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                handle
            }
            _ => unreachable!("checked byte-buffer access"),
        }
    }
    /// Decode ordinary buffer capacity. Headerless buffers have at most 1008
    /// data bytes, so their logical capacity fits in 16 bits. Header-bearing
    /// buffers retain the complete positive word, including large capacities.
    /// Build memory accesses of one class. The class travels as the
    /// instructions' source location, which Cranelift's code generator
    /// ignores and the LLVM backend turns into alias metadata.
    fn memory_class<T>(
        &mut self,
        class: llvm::MemoryClass,
        build: impl FnOnce(&mut Self) -> T,
    ) -> T {
        // Locations are stored relative to a base; fix it at zero so that no
        // class can coincide with "no location".
        self.builder
            .func
            .params
            .ensure_base_srcloc(ir::SourceLoc::new(0));
        let previous = self.builder.srcloc();
        self.builder.set_srcloc(ir::SourceLoc::new(class as u32));
        let built = build(self);
        self.builder.set_srcloc(previous);
        built
    }
    fn buffer_capacity(&mut self, handle: Value) -> Value {
        let word = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 8)
        });
        let raw = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, word, 0);
        let decoded = self.builder.ins().band_imm_s(word, 0xffff);
        self.builder.ins().select(raw, decoded, word)
    }
    /// Release-mode byte append avoids a C call when capacity is available.
    /// The unsigned range check also rejects negative values. The cold helper
    /// keeps all existing growth, overflow and reserved-capacity failures.
    fn push_bytes(&mut self, handle: Value, value: Value, op: BytesOp) -> Value {
        let invalid = self
            .builder
            .ins()
            .icmp_imm_u(IntCC::UnsignedGreaterThan, value, 255);
        if self.program.uses_unwinding {
            // The buffer was moved into the push: let the runtime free it
            // when the byte is invalid, then unwind.
            let slow_invalid = self.builder.create_block();
            let valid = self.builder.create_block();
            self.builder
                .ins()
                .brif(invalid, slow_invalid, &[], valid, &[]);
            self.builder.switch_to_block(slow_invalid);
            let _ = self.runtime_call(self.bytes_ops[&op], &[handle, value]);
            self.unwind_exit();
            self.builder.switch_to_block(valid);
        } else {
            self.guard(invalid);
        }
        let (length, capacity) = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            (
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0),
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 8),
            )
        });
        let room = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, length, capacity);
        let fast = self.builder.create_block();
        let slow = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(room, fast, &[], slow, &[]);
        self.builder.switch_to_block(fast);
        let address = self.builder.ins().iadd(handle, length);
        self.memory_class(llvm::MemoryClass::BufferElements, |g| {
            g.builder
                .ins()
                .istore8(ir::MemFlagsData::new(), value, address, 16);
        });
        let next = self.builder.ins().iadd_imm_s(length, 1);
        self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .store(ir::MemFlagsData::new(), next, handle, 0);
        });
        self.jump(join, &[handle]);
        self.builder.switch_to_block(slow);
        let grown = self.runtime_call(self.bytes_ops[&op], &[handle, value]);
        self.jump(join, &[grown]);
        self.builder.switch_to_block(join);
        self.builder.block_params(join)[0]
    }
    /// A checked vector has `length <= capacity` and an allocation large
    /// enough for every capacity slot. The fast arm neither grows nor changes
    /// ownership; the original helper handles all capacity/overflow cases.
    fn push_vector(&mut self, handle: Value, words: &[Value]) -> Value {
        let callee = self
            .module
            .declare_func_in_func(self.vec_ops[&VecOp::Push], self.builder.func);
        let width = self.constant(words.len() as i64);
        if self.codegen.optimization != Optimization::Speed {
            let item = self.stack_words(words.len());
            self.store_words(item, words);
            let call = self.builder.ins().call(callee, &[handle, item, width]);
            return self.builder.inst_results(call)[0];
        }
        let shadow = self.push_shadow.take();
        let (length, capacity) = match shadow {
            Some((length, capacity)) => {
                (self.builder.use_var(length), self.builder.use_var(capacity))
            }
            None => {
                let length = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                    g.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0)
                });
                (length, self.buffer_capacity(handle))
            }
        };
        let room = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, length, capacity);
        let next = self.builder.ins().iadd_imm_s(length, 1);
        let fast = self.builder.create_block();
        let slow = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(room, fast, &[], slow, &[]);
        self.builder.switch_to_block(fast);
        let offset = self
            .builder
            .ins()
            .imul_imm_s(length, (words.len() * 8) as i64);
        let address = self.builder.ins().iadd(handle, offset);
        self.memory_class(llvm::MemoryClass::BufferElements, |g| {
            for (word, value) in words.iter().enumerate() {
                g.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    address,
                    (16 + word * 8) as i32,
                );
            }
        });
        self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .store(ir::MemFlagsData::new(), next, handle, 0);
        });
        self.jump(join, &[handle]);
        self.builder.switch_to_block(slow);
        let item = self.stack_words(words.len());
        self.store_words(item, words);
        let call = self.builder.ins().call(callee, &[handle, item, width]);
        let grown = self.builder.inst_results(call)[0];
        if let Some((_, capacity)) = shadow {
            // The push succeeded or panicked, so the length is one more
            // either way; the capacity is whatever the new block has.
            let grown_capacity = self.buffer_capacity(grown);
            self.builder.def_var(capacity, grown_capacity);
        }
        self.jump(join, &[grown]);
        self.builder.switch_to_block(join);
        if let Some((length_var, _)) = shadow {
            self.builder.def_var(length_var, next);
        }
        self.builder.block_params(join)[0]
    }

    fn slice_out_of_bounds(&mut self, index: Value, length: Value) -> Value {
        if self.codegen.optimization == Optimization::Speed
            && self.upper_bounds.iter().any(|(known_index, known_length)| {
                self.builder.func.dfg.resolve_aliases(*known_index)
                    == self.builder.func.dfg.resolve_aliases(index)
                    && self.builder.func.dfg.resolve_aliases(*known_length)
                        == self.builder.func.dfg.resolve_aliases(length)
            })
        {
            // The exact SSA pair already passed `index < length`. A negative
            // index can still pass a signed loop condition, so retain its check
            // at the original access site, after all preceding effects.
            self.builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, index, 0)
        } else {
            // Length is always nonnegative; unsigned comparison rejects both
            // negative indices and indices at/above length in one test.
            self.builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length)
        }
    }

    fn loop_slice(&self, condition: &Expr) -> Option<(usize, usize, usize)> {
        let ExprKind::Binary(Kind::Lt, index, length) = &condition.kind else {
            return None;
        };
        let (ExprKind::Local(index_slot) | ExprKind::Peek(index_slot)) = index.kind else {
            return None;
        };
        let ExprKind::Call(Target::Slice(SliceOp::Len, element), arguments) = &length.kind else {
            return None;
        };
        let [view] = arguments.as_slice() else {
            return None;
        };
        let (ExprKind::Local(view_slot) | ExprKind::Peek(view_slot)) = view.kind else {
            return None;
        };
        let locals = &self.program.functions[self.function_index].locals;
        if locals[index_slot].ty != Type::I64
            || locals[index_slot].pinned
            || locals[view_slot].mutable
            || locals[view_slot].pinned
        {
            return None;
        }
        Some((index_slot, view_slot, self.program.width(*element)))
    }

    fn lower_while(&mut self, condition: &Expr, body: &ex::Block) {
        // A loop that appends to a vector reloads its length and capacity
        // from the heap block on every `Vec.push`, and decodes the capacity,
        // because the growth call in the same loop may have changed both.
        // Where the loop touches the vector's header through nothing but
        // those pushes, keep the two in variables instead: load them once,
        // update them at each push (the length is still stored, so memory
        // is never stale), and reload the capacity only after a growth.
        // Only for LLVM: Cranelift's code for the same loop measured 15 to
        // 20% slower with the two extra loop-carried values than with the
        // reloads.
        let shadowed: Vec<usize> = if self.codegen.optimization == Optimization::Speed
            && self.codegen.backend == Backend::Llvm
        {
            push_only_vectors(condition, body)
                .into_iter()
                .filter(|slot| {
                    !self.vec_shadows.contains_key(slot)
                        && !self.erased_local(*slot)
                        && self.variables[*slot].len() == 1
                })
                .collect()
        } else {
            Vec::new()
        };
        if !shadowed.is_empty() && std::env::var_os("KUSH_TRACE_SHADOWS").is_some() {
            eprintln!(
                "vector shadows: a loop in {} keeps {} vector(s) in variables",
                self.program.functions[self.function_index].name,
                shadowed.len()
            );
        }
        for slot in &shadowed {
            let handle = self.local_words(*slot)[0];
            let length = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0)
            });
            let capacity = self.buffer_capacity(handle);
            let length_var = self.builder.declare_var(I64);
            let capacity_var = self.builder.declare_var(I64);
            self.builder.def_var(length_var, length);
            self.builder.def_var(capacity_var, capacity);
            self.vec_shadows.insert(*slot, (length_var, capacity_var));
        }
        self.lower_while_checks(condition, body);
        for slot in &shadowed {
            self.vec_shadows.remove(slot);
        }
        if self.vec_shadows.is_empty() {
            self.pending_pushes.clear();
        }
    }
    fn lower_while_checks(&mut self, condition: &Expr, body: &ex::Block) {
        if self.codegen.defers_overflow()
            && self.deferred.is_none()
            && let Some((plan, accesses)) = deferred::plan(
                &self.program.functions[self.function_index],
                condition,
                body,
                self.codegen.wide_multiply(),
                self.codegen.native_cpu,
            )
        {
            self.lower_deferred_while(plan, &accesses, condition, body);
        } else {
            self.lower_checked_while(condition, body);
        }
    }
    fn lower_checked_while(&mut self, condition: &Expr, body: &ex::Block) {
        let candidate = self.loop_slice(condition);
        // Bound code growth and avoid recursively duplicating nested loops.
        fn eligible(expr: &Expr, budget: &mut usize) -> bool {
            if *budget == 0 || matches!(expr.kind, ExprKind::While(..) | ExprKind::Loop(..)) {
                return false;
            }
            *budget -= 1;
            let mut safe = true;
            expr.for_each_child(&mut |child| safe &= eligible(child, budget));
            safe
        }
        let mut budget = 96;
        let small = body.statements.iter().all(|statement| match statement {
            ex::Statement::Let(_, expr) | ex::Statement::Expr(expr) => eligible(expr, &mut budget),
            ex::Statement::Declare(_) => false,
        }) && body
            .tail
            .as_ref()
            .is_none_or(|expr| eligible(expr, &mut budget));
        if self.codegen.optimization == Optimization::Speed
            && self.slice_layouts.is_empty()
            && small
            && let Some((_, slot, width)) = candidate
        {
            let words = self.local_words(slot);
            let stride = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, words[2], (width * 8) as i64);
            let normal = self.builder.ins().icmp_imm_s(IntCC::Equal, words[3], 0);
            let matches = self.builder.ins().band(stride, normal);
            let fast = self.builder.create_block();
            let generic = self.builder.create_block();
            let join = self.builder.create_block();
            self.builder.ins().brif(matches, fast, &[], generic, &[]);
            self.builder.switch_to_block(fast);
            self.slice_layouts.insert(slot, ((width * 8) as i64, 0));
            self.while_body(condition, body, candidate);
            self.slice_layouts.remove(&slot);
            self.jump(join, &[]);
            self.builder.switch_to_block(generic);
            self.while_body(condition, body, candidate);
            self.jump(join, &[]);
            self.builder.switch_to_block(join);
        } else {
            self.while_body(condition, body, candidate);
        }
    }

    fn while_body(
        &mut self,
        condition: &Expr,
        body: &ex::Block,
        candidate: Option<(usize, usize, usize)>,
    ) {
        let head = self.builder.create_block();
        let enter = self.builder.create_block();
        let exit = self.builder.create_block();
        let depth = self.capture_handler_depth();
        self.jump(head, &[]);
        self.builder.switch_to_block(head);
        // A deferred chunk runs to its own limit, which implies the
        // condition (see `lower_deferred_while`).
        let chunk_test =
            self.deferred
                .as_ref()
                .map(|state| state.limit)
                .map(|(counter, compare, limit)| {
                    let value = self.local_words(counter)[0];
                    self.builder.ins().icmp(compare, value, limit)
                });
        if let Some(test) = chunk_test.or_else(|| self.scalar(condition)) {
            let fact = candidate
                .map(|(index, view, _)| (self.local_words(index)[0], self.local_words(view)[1]));
            self.builder.ins().brif(test, enter, &[], exit, &[]);
            self.builder.seal_block(enter);
            self.builder.switch_to_block(enter);
            let saved = self.upper_bounds.len();
            if let Some(fact) = fact {
                self.upper_bounds.push(fact);
            }
            self.loops.push((head, exit, false, depth));
            let finished = self.block(body);
            self.loops.pop();
            self.upper_bounds.truncate(saved);
            if finished.is_some() {
                self.jump(head, &[]);
            }
        }
        self.builder.switch_to_block(exit);
    }

    fn slice_call(&mut self, op: SliceOp, element: Type, values: Words) -> Words {
        let element_width = self.program.width(element);
        let (pointer, length, stride, bytes) = (values[0], values[1], values[2], values[3]);
        if op == SliceOp::Len {
            return vec![length];
        }
        let index = values[4];
        // THREAD-CHANNELS: the element is the channel handle.
        if matches!(
            op,
            SliceOp::ChannelSend | SliceOp::ChannelRecv { .. } | SliceOp::ChannelClose
        ) {
            let invalid = self.slice_out_of_bounds(index, length);
            self.guard(invalid);
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let handle = self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), address, 0);
            let Type::Channel(message) = element else {
                unreachable!("checked channel view")
            };
            let message = self.program.pointees[message];
            let width = self.program.width(message);
            match op {
                SliceOp::ChannelSend => {
                    let slot = self.stack_words(width.max(1));
                    for (word, value) in values[5..5 + width].iter().enumerate() {
                        self.builder.ins().store(
                            ir::MemFlagsData::new(),
                            *value,
                            slot,
                            (word * 8) as i32,
                        );
                    }
                    self.runtime_void(self.channel_send, &[handle, slot]);
                    return vec![self.constant(0)];
                }
                SliceOp::ChannelClose => {
                    self.runtime_void(self.channel_close, &[handle]);
                    return vec![self.constant(0)];
                }
                SliceOp::ChannelRecv {
                    some_tag,
                    none_tag,
                    option,
                } => {
                    let slot = self.stack_words(width.max(1));
                    let got = self.runtime_call(self.channel_recv, &[handle, slot]);
                    let some = self.builder.create_block();
                    let none = self.builder.create_block();
                    let join = self.builder.create_block();
                    for _ in 0..self.program.enums[option].words {
                        self.builder.append_block_param(join, I64);
                    }
                    self.builder.ins().brif(got, some, &[], none, &[]);
                    self.builder.switch_to_block(some);
                    let payload = self.load_words(slot, 0, width);
                    let some_values = self.encode_variant(Type::Enum(option), some_tag, &payload);
                    self.jump(join, &some_values);
                    self.builder.switch_to_block(none);
                    let none_values = self.encode_variant(Type::Enum(option), none_tag, &[]);
                    self.jump(join, &none_values);
                    self.builder.switch_to_block(join);
                    return self.builder.block_params(join).to_vec();
                }
                _ => unreachable!(),
            }
        }
        // THREAD-ATOMICS: sequentially consistent operations on one word of a
        // view of atomics (never byte-backed).
        if matches!(
            op,
            SliceOp::AtomicLoad
                | SliceOp::AtomicStore
                | SliceOp::AtomicFetchAdd
                | SliceOp::AtomicSwap
                | SliceOp::AtomicCompareExchange
        ) {
            let _ = bytes;
            let invalid = self.slice_out_of_bounds(index, length);
            self.guard(invalid);
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let flags = ir::MemFlagsData::trusted();
            return vec![match op {
                SliceOp::AtomicLoad => self.builder.ins().atomic_load(I64, flags, address),
                SliceOp::AtomicStore => {
                    self.builder.ins().atomic_store(flags, values[5], address);
                    self.constant(0)
                }
                SliceOp::AtomicFetchAdd => self.builder.ins().atomic_rmw(
                    I64,
                    flags,
                    ir::AtomicRmwOp::Add,
                    address,
                    values[5],
                ),
                SliceOp::AtomicSwap => self.builder.ins().atomic_rmw(
                    I64,
                    flags,
                    ir::AtomicRmwOp::Xchg,
                    address,
                    values[5],
                ),
                _ => {
                    let old = self
                        .builder
                        .ins()
                        .atomic_cas(flags, address, values[5], values[6]);
                    let hit = self.builder.ins().icmp(IntCC::Equal, old, values[5]);
                    self.builder.ins().uextend(I64, hit)
                }
            }];
        }
        if op == SliceOp::Set {
            if !self.store_proved {
                let invalid = self.slice_out_of_bounds(index, length);
                self.guard(invalid);
            }
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let value = values[5];
            if element_width != 1 {
                for word in 0..element_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        values[5 + word],
                        address,
                        (word * 8) as i32,
                    );
                }
            } else {
                let store_byte = |this: &mut Self| {
                    let negative = this
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, value, 0);
                    let too_large =
                        this.builder
                            .ins()
                            .icmp_imm_s(IntCC::SignedGreaterThan, value, 255);
                    let invalid = this.builder.ins().bor(negative, too_large);
                    this.guard(invalid);
                    this.builder
                        .ins()
                        .istore8(ir::MemFlagsData::new(), value, address, 0);
                };
                match self.byte_layout(bytes) {
                    Some(true) => store_byte(self),
                    Some(false) => {
                        self.builder
                            .ins()
                            .store(ir::MemFlagsData::new(), value, address, 0);
                    }
                    None => {
                        let byte = self.builder.ins().icmp_imm_s(IntCC::NotEqual, bytes, 0);
                        let scalar = self.builder.create_block();
                        let words = self.builder.create_block();
                        let join = self.builder.create_block();
                        self.builder.ins().brif(byte, scalar, &[], words, &[]);
                        self.builder.switch_to_block(scalar);
                        store_byte(self);
                        self.jump(join, &[]);
                        self.builder.switch_to_block(words);
                        self.builder
                            .ins()
                            .store(ir::MemFlagsData::new(), value, address, 0);
                        self.jump(join, &[]);
                        self.builder.switch_to_block(join);
                    }
                }
            }
            return vec![self.constant(0)];
        }
        if let SliceOp::TryGet {
            some_tag,
            none_tag,
            option,
        } = op
        {
            let invalid = self.slice_out_of_bounds(index, length);
            let valid = self.builder.ins().icmp_imm_s(IntCC::Equal, invalid, 0);
            // Use the real instantiated enum layout rather than deriving it
            // from the element width, so aggregate and union payloads keep
            // the exact ABI of `Option<T>`.
            let option_width = self.program.enums[option].words;
            let some = self.builder.create_block();
            let none = self.builder.create_block();
            let join = self.builder.create_block();
            for _ in 0..option_width {
                self.builder.append_block_param(join, I64);
            }
            self.builder.ins().brif(valid, some, &[], none, &[]);
            self.builder.switch_to_block(some);
            // The element is only read on the in-bounds branch; nothing is
            // loaded from the view before the bounds test.
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let payload: Vec<Value> = if element_width != 1 {
                self.load_words(address, 0, element_width)
            } else {
                vec![self.load_element(address, bytes)]
            };
            let some_values = self.encode_variant(Type::Enum(option), some_tag, &payload);
            self.jump(join, &some_values);
            self.builder.switch_to_block(none);
            let none_values = self.encode_variant(Type::Enum(option), none_tag, &[]);
            self.jump(join, &none_values);
            self.builder.switch_to_block(join);
            return self.builder.block_params(join).to_vec();
        }
        if op == SliceOp::Get {
            let invalid = self.slice_out_of_bounds(index, length);
            self.guard(invalid);
        }
        let offset = self.builder.ins().imul(index, stride);
        let address = self.builder.ins().iadd(pointer, offset);
        // Only byte-backed slices (`&[i64]` over Bytes) can set the flag, and
        // their elements are one word wide. Wider elements always use word loads.
        if element_width != 1 {
            return self.load_words(address, 0, element_width);
        }
        vec![self.load_element(address, bytes)]
    }
    /// The value of an `iconst`, if `value` is one.
    fn constant_value(&self, value: Value) -> Option<i64> {
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
    /// Two words (low first) as one 128-bit vector of `lanes`.
    fn simd_pack(&mut self, low: Value, high: Value, lanes: ir::Type) -> Value {
        let vector = self.builder.ins().scalar_to_vector(ir::types::I64X2, low);
        let vector = self.builder.ins().insertlane(vector, high, 1);
        self.simd_cast(vector, lanes)
    }
    /// A 128-bit vector back to its two words (low first).
    fn simd_unpack(&mut self, vector: Value) -> Words {
        let vector = self.simd_cast(vector, ir::types::I64X2);
        vec![
            self.builder.ins().extractlane(vector, 0),
            self.builder.ins().extractlane(vector, 1),
        ]
    }
    /// Reinterpret a 128-bit vector (x86 lane order on both sides).
    fn simd_cast(&mut self, vector: Value, lanes: ir::Type) -> Value {
        if self.builder.func.dfg.value_type(vector) == lanes {
            return vector;
        }
        let flags = ir::MemFlagsData::new().with_endianness(ir::Endianness::Little);
        self.builder.ins().bitcast(lanes, flags, vector)
    }
    /// A byte shuffle of `a` then `b` (indices 16 and up select `b`).
    fn simd_shuffle(&mut self, a: Value, b: Value, bytes: &[u8]) -> Value {
        let a = self.simd_cast(a, ir::types::I8X16);
        let b = self.simd_cast(b, ir::types::I8X16);
        let mask = self
            .builder
            .func
            .dfg
            .immediates
            .push(ir::ConstantData::from(bytes.to_vec()));
        self.builder.ins().shuffle(a, b, mask)
    }
    /// SIMD-X86-SHA: an intrinsic of std.x86 as a call to the runtime routine
    /// that runs the instruction (`kush_x86_*`, compiled with
    /// `target("sha")`). The first argument is the `cpu.Sha` token, which
    /// proves the CPU has the instruction; the vectors follow as two words
    /// each. `sha1rnds4` needs a constant function index (one routine each).
    fn x86_intrinsic(&mut self, op: &str, values: &[Value]) -> Option<Words> {
        let (symbol, vectors) = match op {
            "sha256rnds2" if values.len() == 7 => ("kush_x86_sha256rnds2".to_owned(), 3),
            "sha256msg1" | "sha256msg2" | "sha1nexte" | "sha1msg1" | "sha1msg2"
                if values.len() == 5 =>
            {
                (format!("kush_x86_{op}"), 2)
            }
            "sha1rnds4" if values.len() == 6 => {
                let func = self
                    .constant_value(values[5])
                    .filter(|f| (0..=3).contains(f))?;
                (format!("kush_x86_sha1rnds4_{func}"), 2)
            }
            _ => return None,
        };
        let mut signature = self.module.make_signature();
        for _ in 0..vectors {
            signature.params.push(AbiParam::new(ir::types::I64X2));
        }
        signature.returns.push(AbiParam::new(ir::types::I64X2));
        let id = self
            .module
            .declare_function(&symbol, Linkage::Import, &signature)
            .ok()?;
        let arguments = (0..vectors)
            .map(|k| self.simd_pack(values[1 + 2 * k], values[2 + 2 * k], ir::types::I64X2))
            .collect::<Vec<_>>();
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(callee, &arguments);
        let result = self.builder.inst_results(call)[0];
        Some(self.simd_unpack(result))
    }
    /// SIMD-NATIVE: the vector form of a std.simd function on a vector type,
    /// or `None` to keep the call (an operation without a vector form, or a
    /// shuffle index that is not a constant). Each result is exactly the
    /// function's Kush specification; `crates/kush/tests/simd_ops.rs`
    /// compares every lane against the evaluator.
    fn simd_lowering(&mut self, ty: &str, op: &str, values: &[Value]) -> Option<Words> {
        use ir::types::{I8X16, I16X8, I32X4, I64X2};
        if ty == "x86" {
            return self.x86_intrinsic(op, values);
        }
        // 256-bit types (SIMD-256) are two 128-bit halves: each lane-wise
        // operation runs once per half.
        let (lanes, size, halves) = match ty {
            "u8x16" | "i8x16" => (I8X16, 1usize, 1usize),
            "u16x8" | "i16x8" => (I16X8, 2, 1),
            "u32x4" | "i32x4" => (I32X4, 4, 1),
            "u64x2" | "i64x2" => (I64X2, 8, 1),
            "u8x32" | "i8x32" => (I8X16, 1, 2),
            "u16x16" | "i16x16" => (I16X8, 2, 2),
            "u32x8" | "i32x8" => (I32X4, 4, 2),
            "u64x4" | "i64x4" => (I64X2, 8, 2),
            _ => return None,
        };
        let count = 16 / size;
        let signed = ty.starts_with('i');
        let words = 2 * halves;
        // Lane-wise operations, per 128-bit half.
        let lane_wise = match op {
            "and" | "or" | "xor" | "wrapping_add" | "wrapping_sub" | "eq_lanes" => {
                (values.len() == 2 * words).then_some(2)
            }
            "not" => (values.len() == words).then_some(1),
            "shl" | "shr" => (values.len() == words + 1).then_some(1),
            _ => None,
        };
        if let Some(operands) = lane_wise {
            let mut result = Vec::with_capacity(words);
            for half in 0..halves {
                let a = self.simd_pack(values[2 * half], values[2 * half + 1], lanes);
                let vector = if operands == 2 {
                    let b = self.simd_pack(
                        values[words + 2 * half],
                        values[words + 2 * half + 1],
                        lanes,
                    );
                    match op {
                        "and" => self.builder.ins().band(a, b),
                        "or" => self.builder.ins().bor(a, b),
                        "xor" => self.builder.ins().bxor(a, b),
                        "wrapping_add" => self.builder.ins().iadd(a, b),
                        "wrapping_sub" => self.builder.ins().isub(a, b),
                        _ => self.builder.ins().icmp(IntCC::Equal, a, b),
                    }
                } else {
                    // The amount was proved below the lane width.
                    match (op, signed) {
                        ("not", _) => self.builder.ins().bnot(a),
                        ("shl", _) => self.builder.ins().ishl(a, values[words]),
                        (_, true) => self.builder.ins().sshr(a, values[words]),
                        _ => self.builder.ins().ushr(a, values[words]),
                    }
                };
                result.extend(self.simd_unpack(vector));
            }
            return Some(result);
        }
        if halves != 1 {
            return None;
        }
        // Byte mask for a lane permutation: output lane k is input lane index[k].
        let lane_bytes = |index: &[i64]| -> Option<Vec<u8>> {
            let mut bytes = Vec::with_capacity(16);
            for &lane in index {
                let lane = usize::try_from(lane).ok()?;
                if lane >= 2 * count {
                    return None;
                }
                for byte in 0..size {
                    bytes.push(u8::try_from(lane * size + byte).ok()?);
                }
            }
            Some(bytes)
        };
        let result = match op {
            "shuffle" if values.len() == 2 + count => {
                let index = values[2..]
                    .iter()
                    .map(|value| self.constant_value(*value))
                    .collect::<Option<Vec<_>>>()?;
                let bytes = lane_bytes(&index)?;
                let a = self.simd_pack(values[0], values[1], lanes);
                self.simd_shuffle(a, a, &bytes)
            }
            "shuffle2" if values.len() == 4 + count => {
                let index = values[4..]
                    .iter()
                    .map(|value| self.constant_value(*value))
                    .collect::<Option<Vec<_>>>()?;
                let bytes = lane_bytes(&index)?;
                let a = self.simd_pack(values[0], values[1], lanes);
                let b = self.simd_pack(values[2], values[3], lanes);
                self.simd_shuffle(a, b, &bytes)
            }
            // `align_right(hi, lo, k)`: bytes k.. of `lo` then `hi`.
            "align_right" if size == 1 && values.len() == 5 => {
                let k = u8::try_from(self.constant_value(values[4])?)
                    .ok()
                    .filter(|k| *k <= 16)?;
                let bytes = (0..16).map(|j| k + j).collect::<Vec<u8>>();
                let hi = self.simd_pack(values[0], values[1], lanes);
                let lo = self.simd_pack(values[2], values[3], lanes);
                self.simd_shuffle(lo, hi, &bytes)
            }
            "swap_bytes" if size > 1 && values.len() == 2 => {
                let bytes = (0..16)
                    .map(|j| u8::try_from((j / size) * size + (size - 1 - j % size)).unwrap())
                    .collect::<Vec<u8>>();
                let a = self.simd_pack(values[0], values[1], lanes);
                self.simd_shuffle(a, a, &bytes)
            }
            _ => return None,
        };
        Some(self.simd_unpack(result))
    }
    /// Whether a slice's byte flag is a known constant: `Some(true)` for a
    /// byte-backed view, `Some(false)` for a word-backed one.
    fn byte_layout(&self, bytes: Value) -> Option<bool> {
        let ir::ValueDef::Result(inst, _) = self.builder.func.dfg.value_def(bytes) else {
            return None;
        };
        match self.builder.func.dfg.insts[inst] {
            ir::InstructionData::UnaryImm {
                opcode: ir::Opcode::Iconst,
                imm,
            } => Some(imm.bits() != 0),
            _ => None,
        }
    }
    /// Load a one-word slice element, as a byte when the view is byte-backed.
    fn load_element(&mut self, address: Value, bytes: Value) -> Value {
        let load_byte = |this: &mut Self| {
            this.builder
                .ins()
                .uload8(I64, ir::MemFlagsData::new(), address, 0)
        };
        match self.byte_layout(bytes) {
            Some(true) => return load_byte(self),
            Some(false) => return self.load_words(address, 0, 1)[0],
            None => {}
        }
        let byte = self.builder.ins().icmp_imm_s(IntCC::NotEqual, bytes, 0);
        let scalar = self.builder.create_block();
        let words = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(byte, scalar, &[], words, &[]);
        self.builder.switch_to_block(scalar);
        let value = load_byte(self);
        self.jump(join, &[value]);
        self.builder.switch_to_block(words);
        let loaded = self.load_words(address, 0, 1);
        self.jump(join, &loaded);
        self.builder.switch_to_block(join);
        self.builder.block_params(join)[0]
    }
    /// Lower allocator-backed vector operations. Metadata is one stable
    /// handle; element storage is a user-allocator block reached through the
    /// imported helpers, so growth and release always use the recorded pair.
    fn alloc_vec_call(
        &mut self,
        op: AllocVecOp,
        element: Type,
        values: Words,
        result: Type,
    ) -> Words {
        let width = self.program.width(element);
        match op {
            AllocVecOp::Len => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                vec![self.runtime_call(self.alloc_ops.vec_len, &[handle])]
            }
            AllocVecOp::Get => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let out = self.stack_words(width);
                self.runtime_void(self.alloc_ops.vec_get, &[handle, values[1], out]);
                self.load_words(out, 0, width)
            }
            AllocVecOp::Push => {
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                let handle = self.runtime_call(self.alloc_ops.vec_push, &[values[0], item]);
                vec![handle]
            }
            AllocVecOp::TryPush => {
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                let success = self.runtime_call(self.alloc_ops.vec_try_push, &[values[0], item]);
                let shape = result
                    .layout()
                    .and_then(|id| self.program.enums[id].result)
                    .expect("checked AllocVec.try_push result");
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, success, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(result);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                let zero = self.constant(0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for index in 0..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), values[0], destination, 8);
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, destination, 8);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), values[0], destination, 16);
                for index in 0..width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        values[1 + index],
                        destination,
                        ((index + 3) * 8) as i32,
                    );
                }
                for index in (3 + width)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                (0..result_width)
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            destination,
                            (index * 8) as i32,
                        )
                    })
                    .collect()
            }
            AllocVecOp::Pop => {
                let item = self.stack_words(width);
                self.runtime_void(self.alloc_ops.vec_pop, &[values[0], item]);
                let zero = self.constant(0);
                let mut out = vec![zero, values[0]];
                out.extend(self.load_words(item, 0, width));
                out
            }
            AllocVecOp::Set => {
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                let handle =
                    self.runtime_call(self.alloc_ops.vec_set, &[values[0], values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                vec![handle]
            }
            AllocVecOp::Clear => {
                let handle = values[0];
                if self.program.owns(element) {
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let data = self.runtime_call(self.alloc_ops.vec_data, &[handle]);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(data, stride);
                    let fields = self.load_words(slot, 0, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                self.runtime_void(self.alloc_ops.vec_clear, &[handle]);
                vec![handle]
            }
        }
    }
    fn vec_call(&mut self, op: VecOp, element: Type, values: Words) -> Words {
        let width = self.program.width(element);
        let call = |g: &mut Self, op: VecOp, args: &[Value]| {
            let callee = g
                .module
                .declare_func_in_func(g.vec_ops[&op], g.builder.func);
            let mut args = args.to_vec();
            if !matches!(op, VecOp::WithCapacity | VecOp::Len) {
                args.push(g.constant(width as i64));
            }
            let call = g.builder.ins().call(callee, &args);
            g.builder.inst_results(call).to_vec()
        };
        match op {
            VecOp::WithCapacity => {
                let w = self.constant(width as i64);
                call(self, op, &[values[0], w])
            }
            VecOp::Reserve => call(self, op, &[values[0], values[1]]),
            VecOp::TryReserve { ok_tag, err_tag } => {
                let grown = call(
                    self,
                    VecOp::TryReserve {
                        ok_tag: 0,
                        err_tag: 0,
                    },
                    &[values[0], values[1]],
                )[0];
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, grown, 0);
                let ok = self.constant(ok_tag as i64);
                let error = self.constant(err_tag as i64);
                let tag = self.builder.ins().select(failed, error, ok);
                let owner = self.builder.ins().select(failed, values[0], grown);
                vec![tag, owner]
            }
            VecOp::ReplaceBorrowed => {
                let reference = values[0];
                let old = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), values[1], reference, 0);
                vec![old]
            }
            VecOp::ClearBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                if self.program.owns(element) {
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(handle, stride);
                    let fields = self.load_words(slot, 16, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                vec![self.constant(0)]
            }
            VecOp::ReserveBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let grown = call(self, VecOp::Reserve, &[handle, values[1]])[0];
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, reference, 0);
                vec![self.constant(0)]
            }
            VecOp::PushBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let grown = self.push_vector(handle, &values[1..1 + width]);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, reference, 0);
                vec![self.constant(0)]
            }
            VecOp::SetBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                call(self, VecOp::Set, &[handle, values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                vec![self.constant(0)]
            }
            VecOp::SetProved => {
                // Proved in bounds, copyable element: a direct store after the
                // 16-byte header, nothing to drop.
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let stride = self.builder.ins().imul_imm_s(values[1], (width * 8) as i64);
                let base = self.builder.ins().iadd(handle, stride);
                let slot = self.builder.ins().iadd_imm_s(base, 16);
                self.store_words(slot, &values[2..2 + width]);
                vec![self.constant(0)]
            }
            VecOp::Clear => {
                let handle = values[0];
                if self.program.owns(element) {
                    // Release elements from the end. Each slot is dropped
                    // exactly once; the vector header and storage stay alive.
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(handle, stride);
                    let fields = self.load_words(slot, 16, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                vec![handle]
            }
            // Length, checked reads and copyable writes are inline: the header
            // is `{length, capacity}` followed by the elements (`KushVec`).
            // With speed optimization the length is an inline load (the header
            // is `{length, capacity}`, `KushVec`). Checked reads and writes stay
            // runtime calls: inlining them cost ~5-6% on the JSON benchmark
            // (2026-11-06). Proved reads (`Vec.at`) are inline loads.
            VecOp::Len => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                if self.codegen.optimization == Optimization::Speed {
                    vec![
                        self.builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), handle, 0),
                    ]
                } else {
                    call(self, op, &[handle])
                }
            }
            VecOp::Get => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let out = self.stack_words(width);
                call(self, op, &[handle, values[1], out]);
                self.load_words(out, 0, width)
            }
            VecOp::At => {
                // Proved in bounds: direct load after the 16-byte header.
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let stride = self.builder.ins().imul_imm_s(values[1], (width * 8) as i64);
                let base = self.builder.ins().iadd(handle, stride);
                self.load_words(base, 16, width)
            }
            VecOp::Push => {
                vec![self.push_vector(values[0], &values[1..1 + width])]
            }
            VecOp::Set => {
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                let handle = call(self, op, &[values[0], values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                handle
            }
        }
    }
    /// Panic unless `value` (a 64-bit result) is in range for `kind`.
    /// How this checked operation is lowered inside a deferred loop.
    fn deferral(&self, expr: &Expr) -> Option<deferred::Mode> {
        self.deferred
            .as_ref()?
            .plan
            .modes
            .get(&deferred::key(expr))
            .copied()
    }
    /// Record a deferred overflow whose indicator is the word's sign bit.
    fn defer_sign(&mut self, word: Value) {
        let sticky = self.deferred.as_ref().expect("deferred loop").sticky;
        let previous = self.builder.use_var(sticky);
        let merged = self.builder.ins().bor(previous, word);
        self.builder.def_var(sticky, merged);
    }
    /// Record a deferred overflow from a 0/1 flag.
    fn defer_flag(&mut self, flag: Value) {
        let wide = self.builder.ins().uextend(I64, flag);
        let word = self.builder.ins().ineg(wide);
        self.defer_sign(word);
    }
    fn defer_int_range(&mut self, kind: IntKind, value: Value) -> Value {
        let canonical = self.canonical(kind, value);
        let wrong = self.builder.ins().icmp(IntCC::NotEqual, canonical, value);
        self.defer_flag(wrong);
        // The wrapped result, not the raw word: the rest of the lowering
        // relies on narrow values being in canonical form (for instance, a
        // narrow signed division has no `MIN / -1` guard).
        canonical
    }
    /// OR an operand's magnitude word into its tracker, if it has one.
    fn track_leaf(&mut self, key: usize, value: Value) {
        let Some(tracker) = self
            .deferred
            .as_ref()
            .and_then(|state| state.leaves.get(&key).copied())
        else {
            return;
        };
        let folded = self.magnitude(value);
        let previous = self.builder.use_var(tracker);
        let merged = self.builder.ins().bor(previous, folded);
        self.builder.def_var(tracker, merged);
    }
    /// Wrapping signed 64-bit `+`, `-`, `*` with its check deferred. Exact
    /// add/sub tests are plain bit operations so the loop stays vectorizable;
    /// certified operations have no test at all.
    fn deferred_i64(
        &mut self,
        op: &Kind,
        left: Value,
        right: Value,
        mode: deferred::Mode,
    ) -> Value {
        if mode != deferred::Mode::Exact {
            return match op {
                Kind::Plus => self.builder.ins().iadd(left, right),
                Kind::Minus => self.builder.ins().isub(left, right),
                _ => self.builder.ins().imul(left, right),
            };
        }
        match op {
            Kind::Plus => {
                let sum = self.builder.ins().iadd(left, right);
                let a = self.builder.ins().bxor(left, sum);
                let b = self.builder.ins().bxor(right, sum);
                let overflow = self.builder.ins().band(a, b);
                self.defer_sign(overflow);
                sum
            }
            Kind::Minus => {
                let difference = self.builder.ins().isub(left, right);
                let a = self.builder.ins().bxor(left, right);
                let b = self.builder.ins().bxor(left, difference);
                let overflow = self.builder.ins().band(a, b);
                self.defer_sign(overflow);
                difference
            }
            _ => {
                let (product, overflow) = self.builder.ins().smul_overflow(left, right);
                self.defer_flag(overflow);
                product
            }
        }
    }
    /// `v ^ (v << 1)`: a word of bit length `b` (0 for zero) such that
    /// `|v| <= 2^(b - 1)`. Its highest set bit is one above the highest bit
    /// where `v` differs from its sign. Two cheap vector operations.
    fn magnitude(&mut self, value: Value) -> Value {
        let doubled = self.builder.ins().iadd(value, value);
        self.builder.ins().bxor(value, doubled)
    }
    /// Leading zeros of a word, counting zero itself as one (63).
    ///
    /// Where they are used the two give the same bound, and the operand is
    /// then visibly non-zero. Without that, a target that has no cheap
    /// count-leading-zeros gets a branch around each one late in LLVM's
    /// code generation, and each such split rescans the whole function:
    /// build time grew with the square of the number of deferred loops
    /// inlined into one function.
    fn leading_zeros(&mut self, word: Value) -> Value {
        let nonzero = self.builder.ins().bor_imm_s(word, 1);
        self.builder.ins().clz(nonzero)
    }
    /// The least tracked `u` with `|v| <= 2^u` for a magnitude word.
    fn magnitude_bound(&mut self, word: Value) -> Value {
        let zeros = self.leading_zeros(word);
        let sixty_four = self.constant(64);
        let bits = self.builder.ins().isub(sixty_four, zeros);
        let one = self.constant(1);
        let floor = self.builder.ins().umax(bits, one);
        self.builder.ins().iadd_imm_s(floor, -1)
    }
    /// Evaluate a certificate bound after the loop.
    fn bound_value(
        &mut self,
        bound: &deferred::Bound,
        leaves: &BTreeMap<usize, Variable>,
        entry: &BTreeMap<usize, Value>,
        count: Variable,
    ) -> Value {
        use deferred::Bound;
        match bound {
            Bound::Constant(bits) => self.constant(i64::from(*bits)),
            Bound::Leaf(key) => {
                let word = self.builder.use_var(leaves[key]);
                self.magnitude_bound(word)
            }
            Bound::Sum(left, right) => {
                let left = self.bound_value(left, leaves, entry, count);
                let right = self.bound_value(right, leaves, entry, count);
                let larger = self.builder.ins().umax(left, right);
                self.builder.ins().iadd_imm_s(larger, 1)
            }
            Bound::Product(left, right) => {
                let left = self.bound_value(left, leaves, entry, count);
                let right = self.bound_value(right, leaves, entry, count);
                self.builder.ins().iadd(left, right)
            }
            Bound::Accumulated { local, operands } => {
                let mut largest = self.magnitude_bound(entry[local]);
                for operand in operands {
                    let operand = self.bound_value(operand, leaves, entry, count);
                    largest = self.builder.ins().umax(largest, operand);
                }
                // At least one: the loop has an accumulating operation.
                let steps = self.builder.use_var(count);
                let zeros = self.leading_zeros(steps);
                let sixty_four = self.constant(64);
                let bits = self.builder.ins().isub(sixty_four, zeros);
                self.builder.ins().iadd(largest, bits)
            }
        }
    }
    /// Lower an innermost counted loop with its overflow panics deferred to
    /// the exit. `deferred` documents why the result is indistinguishable
    /// from checking every operation.
    /// The loop body is lowered twice, as an ordinary loop over a slice is:
    /// once as the deferred chunk, specialized to the plain layout of the
    /// slices it touches and with its element accesses proved in range, and
    /// once as the rest of the loop with ordinary checks. The second serves
    /// everything rare: views that overlap or a slice with another layout
    /// (the whole loop), accesses not provably in range (from that chunk
    /// on), and a chunk whose certificate failed (from its entry state).
    /// After one of those the loop does not go back to chunks: data large
    /// enough to fail a certificate is usually large throughout, and
    /// replaying every chunk would do the work twice. Every further copy
    /// measured about 5 ms of LLVM time per loop.
    fn lower_deferred_while(
        &mut self,
        plan: deferred::Plan,
        accesses: &[deferred::Access<'_>],
        condition: &Expr,
        body: &ex::Block,
    ) {
        let zero = self.constant(0);
        let sticky = self.builder.declare_var(I64);
        let count = self.builder.declare_var(I64);
        let mut leaves = BTreeMap::new();
        for key in &plan.leaves {
            leaves.insert(*key, self.builder.declare_var(I64));
        }
        let done = self.builder.create_block();
        // The loop runs in chunks of at most `CHUNK` iterations, each checked
        // on its own, so an overflow is reported after a bounded amount of
        // further work no matter how long the loop would have run, or what
        // the wrapped values do to it in the meantime.
        let chunk = self.builder.create_block();
        // The rest of the loop with ordinary checks; see the doc comment.
        let checked = self.builder.create_block();
        let mut unsuitable = self.constant(0);
        // A replay re-reads what the first attempt read, so nothing the loop
        // reads may be something it wrote. The borrow rules already say so
        // of two distinct views; compare the address ranges anyway, once.
        for (stored, loaded) in &plan.disjoint {
            let (stored_start, stored_end) = self.view_range(*stored);
            let (loaded_start, loaded_end) = self.view_range(*loaded);
            let before = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, stored_start, loaded_end);
            let after = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, loaded_start, stored_end);
            let both = self.builder.ins().band(before, after);
            let both = self.builder.ins().uextend(I64, both);
            unsuitable = self.builder.ins().bor(unsuitable, both);
        }
        // The deferred chunk is specialized to every slice the loop reads or
        // writes being consecutive whole elements; nothing else would
        // vectorize. (A byte buffer viewed as `&[i64]` is not.)
        let candidate = self.loop_slice(condition);
        let mut layouts: BTreeMap<usize, (i64, i64)> = BTreeMap::new();
        if self.codegen.optimization == Optimization::Speed && self.slice_layouts.is_empty() {
            if let Some((_, slot, width)) = candidate {
                layouts.insert(slot, ((width * 8) as i64, 0));
            }
            for access in accesses {
                if let deferred::Container::Slice(element) = access.container
                    && let ExprKind::Local(slot) | ExprKind::Peek(slot) = access.receiver.kind
                {
                    let width = self.program.width(element);
                    layouts.insert(slot, ((width * 8) as i64, 0));
                }
            }
        }
        for (slot, (stride, bytes)) in &layouts {
            let words = self.local_words(*slot);
            let stride = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::NotEqual, words[2], *stride);
            let stride = self.builder.ins().uextend(I64, stride);
            let flag = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::NotEqual, words[3], *bytes);
            let flag = self.builder.ins().uextend(I64, flag);
            unsuitable = self.builder.ins().bor(unsuitable, stride);
            unsuitable = self.builder.ins().bor(unsuitable, flag);
        }
        self.builder
            .ins()
            .brif(unsuitable, checked, &[], chunk, &[]);
        self.builder.switch_to_block(chunk);
        self.builder.def_var(sticky, zero);
        self.builder.def_var(count, zero);
        for tracker in leaves.values() {
            self.builder.def_var(*tracker, zero);
        }
        let ExprKind::Binary(comparison, _, bound) = &condition.kind else {
            unreachable!("a counted loop compares its counter");
        };
        let comparison = comparison.clone();
        let unsigned = self.program.functions[self.function_index].locals[plan.counter]
            .ty
            .int_kind()
            .is_some_and(|kind| !kind.signed());
        let start = self.local_words(plan.counter)[0];
        // The planner's bound has no effects and cannot change in the loop;
        // evaluating it here makes the checks the condition would make on
        // its next test, at the same point.
        let bound = self
            .scalar(bound)
            .expect("a loop bound always produces a value");
        // Prove every element access of this chunk in range, so the chunk
        // needs no per-element checks: every index is the counter plus a
        // constant, and the counter, the bound and the lengths are exact
        // (none of them is ever deferred). A chunk where that fails runs the
        // rest of the loop with ordinary checks, which panic where they
        // should.
        if !accesses.is_empty() {
            let outside = self.accesses_outside(accesses, &comparison, start, bound);
            let proved = self.builder.create_block();
            self.builder.ins().brif(outside, checked, &[], proved, &[]);
            self.builder.switch_to_block(proved);
        }
        // The chunk runs while the counter is short of a limit: the bound,
        // or `CHUNK` steps from here if that comes first. One counted exit,
        // which is what LLVM vectorizes most cheaply.
        let limit = self.chunk_limit(&comparison, unsigned, start, bound, plan.step);
        let compare = self.counter_comparison(&comparison, unsigned);
        let mut entry_magnitudes = BTreeMap::new();
        for slot in &plan.accumulators {
            let value = self.local_words(*slot)[0];
            let word = self.magnitude(value);
            entry_magnitudes.insert(*slot, word);
        }
        let entry: Vec<(usize, Words)> = plan
            .replay
            .iter()
            .map(|slot| (*slot, self.local_words(*slot)))
            .collect();
        let counter = plan.counter;
        let step = plan.step;
        self.deferred = Some(DeferredLoop {
            plan,
            sticky,
            leaves,
            limit: (counter, compare, limit),
        });
        self.slice_layouts
            .extend(layouts.iter().map(|(slot, layout)| (*slot, *layout)));
        self.proved_accesses = accesses.iter().map(|access| access.call).collect();
        self.while_body(condition, body, candidate);
        self.proved_accesses.clear();
        for slot in layouts.keys() {
            self.slice_layouts.remove(slot);
        }
        let state = self.deferred.take().expect("deferred loop");
        let end = self.local_words(counter)[0];
        if !state.plan.obligations.is_empty() {
            // How many terms the reductions took in, at most: each
            // accumulating operation runs at most once per iteration, and
            // the counter moved by its step once per iteration (a deferred
            // loop has no `break`, and a panic ends the process). One more
            // is a margin. Counting in the loop would be exact but costs a
            // vector reduction of its own.
            let accumulating = state
                .plan
                .modes
                .values()
                .filter(|mode| **mode == deferred::Mode::Accumulate)
                .count() as i64;
            let distance = match comparison {
                Kind::Lt | Kind::Le => self.builder.ins().isub(end, start),
                _ => self.builder.ins().isub(start, end),
            };
            let iterations = if step == 1 {
                distance
            } else {
                let step = self.constant(step);
                self.builder.ins().udiv(distance, step)
            };
            let started = self.builder.ins().iadd_imm_s(iterations, 1);
            let terms = self.builder.ins().imul_imm_s(started, accumulating);
            self.builder.def_var(count, terms);
            // The certificate: every bound is within the limit.
            let mut worst = self.constant(0);
            for obligation in &state.plan.obligations {
                let value = self.bound_value(obligation, &state.leaves, &entry_magnitudes, count);
                worst = self.builder.ins().umax(worst, value);
            }
            let proved = self.builder.ins().icmp_imm_u(
                IntCC::UnsignedLessThanOrEqual,
                worst,
                deferred::LIMIT,
            );
            let certified = self.builder.create_block();
            let replay = self.builder.create_block();
            self.builder.ins().brif(proved, certified, &[], replay, &[]);
            // Without it nothing is known: go back to this chunk's entry
            // state and run the rest of the loop with ordinary checks.
            self.builder.switch_to_block(replay);
            for (slot, words) in entry {
                self.assign(slot, &words);
            }
            self.jump(checked, &[]);
            // With it, every value was exact, so the sticky word of the
            // remaining exact tests is exact too.
            self.builder.switch_to_block(certified);
        }
        let overflowed = self.builder.use_var(sticky);
        let overflowed = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, overflowed, 0);
        self.guard(overflowed);
        // The chunk stopped at its limit or at the loop's own end; the
        // condition, with the bound evaluated at the chunk's start, says
        // which.
        let more = self.builder.ins().icmp(compare, end, bound);
        self.builder.ins().brif(more, chunk, &[], done, &[]);
        // The rest of the loop with ordinary checks. Every way in arrives
        // with the locals of a checked execution: untouched, or a chunk's
        // entry state restored, or the result of chunks that passed.
        self.builder.switch_to_block(checked);
        self.while_body(condition, body, candidate);
        self.jump(done, &[]);
        self.builder.switch_to_block(done);
    }
    /// Whether some element access of a chunk starting at the counter's
    /// current value could fall outside its container. Every iteration of
    /// the chunk has its counter between the current value and the bound
    /// (the loop condition holds at the top of each), so each index lies in
    /// a range computed here; an overflow while computing one counts as
    /// outside.
    fn accesses_outside(
        &mut self,
        accesses: &[deferred::Access<'_>],
        comparison: &Kind,
        start: Value,
        bound: Value,
    ) -> Value {
        // The counter's extremes: [low, high].
        let (low, high, mut outside) = match comparison {
            Kind::Lt | Kind::Le => {
                let (high, overflow) = if *comparison == Kind::Lt {
                    let one = self.constant(1);
                    self.builder.ins().ssub_overflow(bound, one)
                } else {
                    (bound, self.builder.ins().iconst(ir::types::I8, 0))
                };
                (start, high, overflow)
            }
            _ => {
                let (low, overflow) = if *comparison == Kind::Gt {
                    let one = self.constant(1);
                    self.builder.ins().sadd_overflow(bound, one)
                } else {
                    (bound, self.builder.ins().iconst(ir::types::I8, 0))
                };
                (low, start, overflow)
            }
        };
        // Every access to one receiver lies between its smallest and largest
        // offset, so those two bound all the others.
        let mut ranges: Vec<(usize, &deferred::Access<'_>, i64, i64)> = Vec::new();
        for access in accesses {
            let receiver = deferred::key(access.receiver);
            match ranges.iter_mut().find(|(known, ..)| *known == receiver) {
                Some((_, _, least, most)) => {
                    *least = (*least).min(access.offset);
                    *most = (*most).max(access.offset);
                }
                None => ranges.push((receiver, access, access.offset, access.offset)),
            }
        }
        for (_, access, least, most) in ranges {
            let length = self.container_length(access);
            let mut flags = Vec::with_capacity(4);
            let first = if least == 0 {
                low
            } else {
                let offset = self.constant(least);
                let (first, below) = self.builder.ins().sadd_overflow(low, offset);
                flags.push(below);
                first
            };
            let last = if most == 0 {
                high
            } else {
                let offset = self.constant(most);
                let (last, above) = self.builder.ins().sadd_overflow(high, offset);
                flags.push(above);
                last
            };
            flags.push(
                self.builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, first, 0),
            );
            flags.push(
                self.builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, last, length),
            );
            for flag in flags {
                outside = self.builder.ins().bor(outside, flag);
            }
        }
        outside
    }
    /// Where a deferred chunk starting at `start` stops: `bound`, or `CHUNK`
    /// steps on if that comes first (saturating at the end of the range).
    fn chunk_limit(
        &mut self,
        comparison: &Kind,
        unsigned: bool,
        start: Value,
        bound: Value,
        step: i64,
    ) -> Value {
        // `i < limit` admits `CHUNK` steps from `start`, `i <= limit` one
        // fewer step and the same number of iterations.
        let steps = match comparison {
            Kind::Lt | Kind::Gt => deferred::CHUNK,
            _ => deferred::CHUNK - 1,
        };
        let ascending = matches!(comparison, Kind::Lt | Kind::Le);
        let far = match step.checked_mul(steps) {
            Some(span) => {
                let span = self.constant(span);
                let (moved, overflow) = match (ascending, unsigned) {
                    (true, false) => self.builder.ins().sadd_overflow(start, span),
                    (true, true) => self.builder.ins().uadd_overflow(start, span),
                    (false, false) => self.builder.ins().ssub_overflow(start, span),
                    (false, true) => self.builder.ins().usub_overflow(start, span),
                };
                let end = match (ascending, unsigned) {
                    (true, false) => i64::MAX,
                    (true, true) => -1,
                    (false, false) => i64::MIN,
                    (false, true) => 0,
                };
                let end = self.constant(end);
                self.builder.ins().select(overflow, end, moved)
            }
            // So many steps that the bound always comes first.
            None => bound,
        };
        match (ascending, unsigned) {
            (true, false) => self.builder.ins().smin(bound, far),
            (true, true) => self.builder.ins().umin(bound, far),
            (false, false) => self.builder.ins().smax(bound, far),
            (false, true) => self.builder.ins().umax(bound, far),
        }
    }
    /// The comparison a loop condition makes on its counter.
    fn counter_comparison(&self, comparison: &Kind, unsigned: bool) -> IntCC {
        match (comparison, unsigned) {
            (Kind::Lt, false) => IntCC::SignedLessThan,
            (Kind::Lt, true) => IntCC::UnsignedLessThan,
            (Kind::Le, false) => IntCC::SignedLessThanOrEqual,
            (Kind::Le, true) => IntCC::UnsignedLessThanOrEqual,
            (Kind::Gt, false) => IntCC::SignedGreaterThan,
            (Kind::Gt, true) => IntCC::UnsignedGreaterThan,
            (Kind::Ge, false) => IntCC::SignedGreaterThanOrEqual,
            (_, true) => IntCC::UnsignedGreaterThanOrEqual,
            (_, false) => IntCC::SignedGreaterThanOrEqual,
        }
    }
    /// The element count of an access's container, read without effects.
    fn container_length(&mut self, access: &deferred::Access<'_>) -> Value {
        let values = self
            .expr(access.receiver)
            .expect("a container operand always produces a value");
        match access.container {
            deferred::Container::Slice(_) => values[1],
            deferred::Container::Vec(element) => self.vec_call(VecOp::Len, element, values)[0],
            deferred::Container::Bytes => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                    g.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0)
                })
            }
        }
    }
    /// The address range `[start, end)` of a slice local's elements.
    fn view_range(&mut self, slot: usize) -> (Value, Value) {
        let words = self.local_words(slot);
        let bytes = self.builder.ins().imul(words[1], words[2]);
        let end = self.builder.ins().iadd(words[0], bytes);
        (words[0], end)
    }
    fn check_int_range(&mut self, kind: IntKind, value: Value) -> Value {
        if kind.bits() == 64 {
            return value;
        }
        let canonical = self.canonical(kind, value);
        let wrong = self.builder.ins().icmp(IntCC::NotEqual, canonical, value);
        self.guard(wrong);
        value
    }
    /// Re-extend the low `bits` of a word into the kind's canonical form.
    fn canonical(&mut self, kind: IntKind, value: Value) -> Value {
        let narrow = match kind.bits() {
            8 => ir::types::I8,
            16 => ir::types::I16,
            32 => ir::types::I32,
            _ => return value,
        };
        let low = self.builder.ins().ireduce(narrow, value);
        if kind.signed() {
            self.builder.ins().sextend(I64, low)
        } else {
            self.builder.ins().uextend(I64, low)
        }
    }
    fn int_binary(
        &mut self,
        kind: IntKind,
        op: &Kind,
        left: Value,
        right: Value,
        right_kind: Option<IntKind>,
        deferral: Option<deferred::Mode>,
    ) -> Value {
        let signed = kind.signed();
        let wide = kind.bits() == 64;
        match op {
            Kind::Plus | Kind::Minus | Kind::Star if deferral.is_some() => {
                if !wide {
                    // Canonical narrow operands combine exactly in 64 bits
                    // (a `u32` product modulo 2^64 is still the exact
                    // product), so the range test alone decides.
                    let value = match op {
                        Kind::Plus => self.builder.ins().iadd(left, right),
                        Kind::Minus => self.builder.ins().isub(left, right),
                        _ => self.builder.ins().imul(left, right),
                    };
                    return self.defer_int_range(kind, value);
                }
                if signed {
                    return self.deferred_i64(op, left, right, deferral.unwrap());
                }
                let (value, overflow) = match op {
                    Kind::Plus => {
                        let sum = self.builder.ins().iadd(left, right);
                        let carry = self.builder.ins().icmp(IntCC::UnsignedLessThan, sum, left);
                        (sum, carry)
                    }
                    Kind::Minus => {
                        let difference = self.builder.ins().isub(left, right);
                        let borrow = self
                            .builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThan, left, right);
                        (difference, borrow)
                    }
                    _ => self.builder.ins().umul_overflow(left, right),
                };
                self.defer_flag(overflow);
                value
            }
            Kind::Plus | Kind::Minus | Kind::Star => {
                let (value, overflow) = match (op, signed || !wide) {
                    // Narrow kinds compute exactly in 64 bits, then range-check.
                    (Kind::Plus, true) => self.builder.ins().sadd_overflow(left, right),
                    (Kind::Minus, true) => self.builder.ins().ssub_overflow(left, right),
                    (Kind::Star, true) => self.builder.ins().smul_overflow(left, right),
                    (Kind::Plus, false) => self.builder.ins().uadd_overflow(left, right),
                    (Kind::Minus, false) => self.builder.ins().usub_overflow(left, right),
                    (Kind::Star, false) => self.builder.ins().umul_overflow(left, right),
                    _ => unreachable!(),
                };
                self.guard(overflow);
                self.check_int_range(kind, value)
            }
            Kind::Slash | Kind::Percent => {
                let zero = self.builder.ins().icmp_imm_s(IntCC::Equal, right, 0);
                self.guard(zero);
                if signed {
                    if wide || *op == Kind::Percent {
                        let min_value = kind.encode(kind.min()).unwrap();
                        let min = self.builder.ins().icmp_imm_s(IntCC::Equal, left, min_value);
                        let neg = self.builder.ins().icmp_imm_s(IntCC::Equal, right, -1);
                        let invalid = self.builder.ins().band(min, neg);
                        self.guard(invalid);
                    }
                    let value = if *op == Kind::Slash {
                        self.builder.ins().sdiv(left, right)
                    } else {
                        self.builder.ins().srem(left, right)
                    };
                    self.check_int_range(kind, value)
                } else if *op == Kind::Slash {
                    self.builder.ins().udiv(left, right)
                } else {
                    self.builder.ins().urem(left, right)
                }
            }
            Kind::Amp => self.builder.ins().band(left, right),
            Kind::Pipe => self.builder.ins().bor(left, right),
            Kind::Caret => self.builder.ins().bxor(left, right),
            Kind::Shl | Kind::Shr => {
                // The amount is checked against 0..bits in its own kind.
                let amount_signed = right_kind.is_some_and(IntKind::signed);
                if amount_signed {
                    let negative = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, right, 0);
                    self.guard(negative);
                }
                let too_far = self.builder.ins().icmp_imm_u(
                    IntCC::UnsignedGreaterThanOrEqual,
                    right,
                    i64::from(kind.bits()),
                );
                self.guard(too_far);
                let value = if *op == Kind::Shl {
                    self.builder.ins().ishl(left, right)
                } else if signed {
                    self.builder.ins().sshr(left, right)
                } else {
                    self.builder.ins().ushr(left, right)
                };
                self.canonical(kind, value)
            }
            _ => {
                let condition = match (op, signed) {
                    (Kind::Lt, true) => IntCC::SignedLessThan,
                    (Kind::Le, true) => IntCC::SignedLessThanOrEqual,
                    (Kind::Gt, true) => IntCC::SignedGreaterThan,
                    (Kind::Ge, true) => IntCC::SignedGreaterThanOrEqual,
                    (Kind::Lt, false) => IntCC::UnsignedLessThan,
                    (Kind::Le, false) => IntCC::UnsignedLessThanOrEqual,
                    (Kind::Gt, false) => IntCC::UnsignedGreaterThan,
                    (Kind::Ge, false) => IntCC::UnsignedGreaterThanOrEqual,
                    (Kind::EqEq, _) => IntCC::Equal,
                    (Kind::Ne, _) => IntCC::NotEqual,
                    _ => unreachable!(),
                };
                let value = self.builder.ins().icmp(condition, left, right);
                self.builder.ins().uextend(I64, value)
            }
        }
    }
    /// Explicit conversions and wrapping/saturating/checked arithmetic.
    fn int_builtin(
        &mut self,
        op: crate::int::IntOp,
        source: IntKind,
        target: IntKind,
        values: &[Value],
        ty: Type,
    ) -> Words {
        use crate::int::{ArithOp, IntOp};
        // `in_range(v)` for a 64-bit word that holds an exact mathematical
        // value interpreted in `source`'s signedness.
        let in_target = |g: &mut Self, value: Value, value_signed: bool| -> Value {
            // value fits target  <=>  target.min <= v <= target.max
            let lo = target.min();
            let hi = target.max();
            let (lt_min, gt_max) = if value_signed {
                let lt = if lo <= i128::from(i64::MIN) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, value, lo as i64)
                };
                let gt = if hi >= i128::from(i64::MAX) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedGreaterThan, value, hi as i64)
                };
                (lt, gt)
            } else {
                let lt = g.builder.ins().iconst(ir::types::I8, 0);
                let gt = if hi >= i128::from(u64::MAX) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_u(IntCC::UnsignedGreaterThan, value, hi as u64 as i64)
                };
                (lt, gt)
            };
            let bad = g.builder.ins().bor(lt_min, gt_max);
            g.builder.ins().icmp_imm_s(IntCC::Equal, bad, 0)
        };
        let option =
            |g: &mut Self, present: Value, payload: Value, some: usize, none: usize| -> Words {
                g.optional_words(ty, present, &[payload], some, none)
            };
        let a = values[0];
        match op {
            IntOp::Convert => vec![a],
            IntOp::Truncate => vec![self.canonical(target, a)],
            IntOp::TryConvert { some_tag, none_tag } => {
                // u64 values above i64::MAX are negative words; reject them for
                // any signed target and for any narrower unsigned target.
                let ok = in_target(self, a, source.signed());
                let high_half =
                    (!source.signed() && source == IntKind::U64 && target != IntKind::U64)
                        || (source.signed() && !target.signed());
                let ok = if high_half {
                    let small =
                        self.builder
                            .ins()
                            .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, a, 0);
                    self.builder.ins().band(ok, small)
                } else {
                    ok
                };
                option(self, ok, a, some_tag, none_tag)
            }
            IntOp::CharFromCode { some_tag, none_tag } => {
                let max =
                    self.builder
                        .ins()
                        .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, a, 0x10FFFF);
                let below = self
                    .builder
                    .ins()
                    .icmp_imm_u(IntCC::UnsignedLessThan, a, 0xD800);
                let above = self
                    .builder
                    .ins()
                    .icmp_imm_u(IntCC::UnsignedGreaterThan, a, 0xDFFF);
                let not_surrogate = self.builder.ins().bor(below, above);
                let ok = self.builder.ins().band(max, not_surrogate);
                option(self, ok, a, some_tag, none_tag)
            }
            // Proved in range: the exact result is the machine result and is
            // already in canonical (sign- or zero-extended) form.
            IntOp::Unchecked(arith) => {
                let b = values[1];
                let value = match arith {
                    ArithOp::Add => self.builder.ins().iadd(a, b),
                    ArithOp::Sub => self.builder.ins().isub(a, b),
                    ArithOp::Mul => self.builder.ins().imul(a, b),
                };
                // The proof may rest on an operation whose overflow panic a
                // deferred loop has not reported yet. Until it is, keep the
                // value in canonical form like every other narrow value.
                vec![if self.deferred.is_some() && source.bits() < 64 {
                    self.canonical(source, value)
                } else {
                    value
                }]
            }
            // Amount proved in 0..bits (SHIFT-ELIDE).
            IntOp::UncheckedShift(shift) => {
                let b = values[1];
                let value = match shift {
                    crate::int::Shift::Left => self.builder.ins().ishl(a, b),
                    crate::int::Shift::Right if source.signed() => self.builder.ins().sshr(a, b),
                    crate::int::Shift::Right => self.builder.ins().ushr(a, b),
                };
                vec![self.canonical(source, value)]
            }
            IntOp::Wrapping(arith) | IntOp::Saturating(arith) | IntOp::Checked(arith, _, _) => {
                let b = values[1];
                let kind = source;
                let signed = kind.signed();
                let wide = kind.bits() == 64;
                let (value, overflow) = match (arith, signed || !wide) {
                    (ArithOp::Add, true) => self.builder.ins().sadd_overflow(a, b),
                    (ArithOp::Sub, true) => self.builder.ins().ssub_overflow(a, b),
                    (ArithOp::Mul, true) => self.builder.ins().smul_overflow(a, b),
                    (ArithOp::Add, false) => self.builder.ins().uadd_overflow(a, b),
                    (ArithOp::Sub, false) => self.builder.ins().usub_overflow(a, b),
                    (ArithOp::Mul, false) => self.builder.ins().umul_overflow(a, b),
                };
                // Exact result fits the kind: no 64-bit overflow and in range.
                let canonical = self.canonical(kind, value);
                let same = self.builder.ins().icmp(IntCC::Equal, canonical, value);
                let no_overflow = self.builder.ins().icmp_imm_s(IntCC::Equal, overflow, 0);
                let fits = self.builder.ins().band(same, no_overflow);
                match op {
                    IntOp::Wrapping(_) => vec![canonical],
                    IntOp::Checked(_, some, none) => option(self, fits, value, some, none),
                    _ => {
                        // Saturate toward the bound in the direction of the
                        // true result: for unsigned, sub underflows to 0 and
                        // add/mul overflow to max; for signed, the sign of
                        // the exact result decides.
                        let max = self.constant(kind.encode(kind.max()).unwrap());
                        let min = self.constant(kind.encode(kind.min()).unwrap());
                        let bound = if !signed {
                            if arith == ArithOp::Sub { min } else { max }
                        } else {
                            let negative = match arith {
                                ArithOp::Add => {
                                    self.builder.ins().icmp_imm_s(IntCC::SignedLessThan, b, 0)
                                }
                                ArithOp::Sub => {
                                    self.builder
                                        .ins()
                                        .icmp_imm_s(IntCC::SignedGreaterThan, b, 0)
                                }
                                ArithOp::Mul => {
                                    let x = self.builder.ins().bxor(a, b);
                                    self.builder.ins().icmp_imm_s(IntCC::SignedLessThan, x, 0)
                                }
                            };
                            self.builder.ins().select(negative, min, max)
                        };
                        vec![self.builder.ins().select(fits, value, bound)]
                    }
                }
            }
        }
    }
    /// Apply a representation-changing coercion to lowered words.
    fn coerce_values(&mut self, values: Words, to: Type, coercion: &Coercion) -> Option<Words> {
        let to = &to;
        let width = self.program.width(*to);
        match coercion {
            Coercion::Inject { tag } => {
                let mut out = Vec::with_capacity(width);
                out.push(self.constant(*tag as i64));
                out.extend(values.iter().copied().take(width.saturating_sub(1)));
                while out.len() < width {
                    out.push(self.constant(0));
                }
                Some(out)
            }
            Coercion::Struct {
                source,
                kept,
                drops,
            } => {
                let target_id = to.layout().expect("checked structural target layout");
                let target_fields = self.program.enums[target_id].variants[0].fields.clone();
                let mut out: Vec<Value> = vec![self.constant(0)];
                self.struct_coercion_words(*source, &target_fields, kept, drops, &values, &mut out);
                while out.len() < width {
                    out.push(self.constant(0));
                }
                Some(out)
            }
            Coercion::Repack { map } => {
                let exit = self.join(*to)?;
                for (source_tag, target_tag) in map.iter().enumerate() {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition =
                        self.builder
                            .ins()
                            .icmp_imm_s(IntCC::Equal, values[0], source_tag as i64);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    let mut out = Vec::with_capacity(width);
                    out.push(self.constant(*target_tag as i64));
                    out.extend(values[1..].iter().copied().take(width.saturating_sub(1)));
                    while out.len() < width {
                        out.push(self.constant(0));
                    }
                    self.jump(exit, &out);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(exit);
                Some(self.builder.block_params(exit).to_vec())
            }
            Coercion::Callable { .. } => Some(self.nested_coercion_words(coercion, *to, &values)),
            Coercion::DynBox {
                member,
                member_type,
                ..
            } => {
                let pointer = self.allocate_dyn_payload(*member_type, &values);
                Some(vec![self.constant(*member as i64), pointer])
            }
            Coercion::DynUpcast { from, to } => Some(self.dyn_upcast(*from, *to, &values)),
        }
    }
    /// Lower a call to `target` on its lowered argument words; `ty` is the
    /// result type. `site` is the tree path's call expression (its address
    /// and deferred key), which the loop optimizations of the tree path key
    /// their facts on; the MIR path has none.
    fn call_target(
        &mut self,
        target: &Target,
        mut values: Words,
        ty: Type,
        span: crate::Span,
        site: Option<(usize, usize)>,
    ) -> Option<Words> {
        if matches!(
            target,
            Target::Vec(..)
                | Target::AllocVec(..)
                | Target::Slice(..)
                | Target::DynArray(..)
                | Target::Bytes(..)
        ) {
            self.fuzz_enter(span, 0);
        }
        let scalar = match target {
            Target::Io(op, shape) => match op {
                IoOp::Stdin => self.constant(0),
                IoOp::Stdout => self.constant(1),
                IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk | IoOp::Write => {
                    let ok_value = if matches!(op, IoOp::Write) {
                        values[1] =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), values[1], 0);
                        self.constant(0)
                    } else {
                        values[1]
                    };
                    let callee = if matches!(op, IoOp::ReadAll) {
                        self.read_all
                    } else if matches!(op, IoOp::ReadLine) {
                        self.read_line
                    } else if matches!(op, IoOp::ReadChunk) {
                        self.read_chunk
                    } else {
                        self.write
                    };
                    let status = self.runtime_call(callee, &values);
                    let success = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                    let shape = shape.expect("checked I/O result shape");
                    let ok_tag = self.constant(shape.ok_tag as i64);
                    let err_tag = self.constant(shape.err_tag as i64);
                    let tag = self.builder.ins().select(success, ok_tag, err_tag);
                    let payload = self.builder.ins().select(success, ok_value, status);
                    return Some(vec![tag, payload]);
                }
            },
            Target::Host(op, shape) => {
                let mut arguments = values.clone();
                for (index, borrowed) in op.borrowed().iter().enumerate() {
                    if *borrowed {
                        arguments[index] = self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            arguments[index],
                            0,
                        );
                    }
                }
                let out = self.stack_words(1);
                arguments.push(out);
                let status = self.runtime_call(self.host_ops[op], &arguments);
                let success = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                let value = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                let ok_tag = self.constant(shape.ok_tag as i64);
                let err_tag = self.constant(shape.err_tag as i64);
                let tag = self.builder.ins().select(success, ok_tag, err_tag);
                let payload = self.builder.ins().select(success, value, status);
                return Some(vec![tag, payload]);
            }
            Target::Bytes(op) => {
                if op.borrowed() {
                    values[0] = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), values[0], 0);
                }
                if *op == BytesOp::Get
                    && site.is_some_and(|(_, key)| self.proved_accesses.contains(&key))
                {
                    // A deferred chunk proved it in range. Data
                    // follows the 16-byte header.
                    let address = self.builder.ins().iadd(values[0], values[1]);
                    return Some(vec![self.builder.ins().uload8(
                        I64,
                        ir::MemFlagsData::new(),
                        address,
                        16,
                    )]);
                }
                if matches!(op, BytesOp::Push | BytesOp::PushReserved)
                    && self.codegen.optimization == Optimization::Speed
                {
                    self.push_bytes(values[0], values[1], *op)
                } else if self.codegen.optimization == Optimization::Speed
                    // Checked indexed reads stay a runtime call. Inlining
                    // them moved the JSON benchmark's hot loop and cost
                    // ~6% on an older Zen 3 laptop for ~1% on Zen 5;
                    // see the plain-byte-capacity benchmark analysis.
                    && matches!(op, BytesOp::Len | BytesOp::Capacity | BytesOp::Clear)
                {
                    self.bytes_access(*op, &values)
                } else {
                    self.runtime_call(self.bytes_ops[op], &values)
                }
            }
            Target::String(op) => {
                if op.borrowed() {
                    values[0] = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), values[0], 0);
                }
                match op {
                    StringOp::Len if self.codegen.optimization == Optimization::Speed => {
                        self.bytes_access(BytesOp::Len, &values)
                    }
                    StringOp::Len => self.runtime_call(self.bytes_ops[&BytesOp::Len], &values),
                    StringOp::ScalarLen => self.runtime_call(self.string_scalar_len, &values),
                    StringOp::ByteAt => self.runtime_call(self.bytes_ops[&BytesOp::Get], &values),
                    StringOp::AsBytes => self.runtime_call(self.bytes_ops[&BytesOp::Copy], &values),
                    StringOp::IntoBytes => values[0],
                    StringOp::ScalarAt { some_tag, none_tag } => {
                        let codepoint = self.runtime_call(self.string_scalar_at, &values);
                        let present = self.builder.ins().icmp_imm_s(
                            IntCC::SignedGreaterThanOrEqual,
                            codepoint,
                            0,
                        );
                        return Some(self.optional_words(
                            ty,
                            present,
                            &[codepoint],
                            *some_tag,
                            *none_tag,
                        ));
                    }
                    StringOp::FromUtf8 { ok_tag, err_tag } => {
                        let valid = self.runtime_call(self.string_validate, &values);
                        let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, valid, 0);
                        let ok = self.constant(*ok_tag as i64);
                        let err = self.constant(*err_tag as i64);
                        let tag = self.builder.ins().select(present, ok, err);
                        let width = self.program.width(ty);
                        let mut words = vec![tag, values[0]];
                        while words.len() < width {
                            words.push(self.constant(0));
                        }
                        return Some(words);
                    }
                }
            }
            Target::Str(op) => return Some(self.str_call(*op, values, ty)),
            Target::Foreign(index) => return self.foreign_call(*index, &values),
            Target::Function(index) => return Some(self.function_call(*index, values)),
            Target::DynCall { spec, .. } => return Some(self.dyn_call(*spec, values)),
            Target::UnionBorrowCall { spec, .. } => {
                return Some(self.union_borrow_call(*spec, values));
            }
            Target::Vec(op, element) => {
                // The push a loop registered for one of its
                // shadowed vectors is this very expression.
                let address = site.map(|(address, _)| address);
                self.push_shadow = match self
                    .pending_pushes
                    .iter()
                    .position(|(pending, _)| Some(*pending) == address)
                {
                    Some(at) if *op == VecOp::Push => {
                        let (_, slot) = self.pending_pushes.remove(at);
                        self.vec_shadows.get(&slot).copied()
                    }
                    _ => None,
                };
                let op = match op {
                    VecOp::Get
                        if site.is_some_and(|(_, key)| self.proved_accesses.contains(&key)) =>
                    {
                        VecOp::At
                    }
                    other => *other,
                };
                let result = self.vec_call(op, *element, values);
                self.push_shadow = None;
                return Some(result);
            }
            Target::AllocVec(op, element) => {
                return Some(self.alloc_vec_call(*op, *element, values, ty));
            }
            Target::Slice(op, element) => {
                // A deferred chunk proved this access in range.
                let proved = site.is_some_and(|(_, key)| self.proved_accesses.contains(&key));
                let op = match op {
                    SliceOp::Get if proved => SliceOp::At,
                    other => *other,
                };
                self.store_proved = proved && op == SliceOp::Set;
                let result = self.slice_call(op, *element, values);
                self.store_proved = false;
                return Some(result);
            }
            Target::ChannelNew => {
                let Type::Channel(pointer) = ty else {
                    unreachable!("checked Channel.new has a channel type")
                };
                let width = self.program.width(self.program.pointees[pointer]);
                let width = self.constant(width as i64);
                self.runtime_call(self.channel_new, &[values[0], width])
            }
            Target::DynArray(op, element) => {
                return Some(self.dyn_array_call(*op, *element, values));
            }
            Target::Print => self.runtime_call(self.print, &values),
            Target::PrintInt(kind) => {
                let callee = if *kind == IntKind::U64 {
                    self.print_u64
                } else {
                    self.print
                };
                self.runtime_call(callee, &values)
            }
            Target::PrintFloat(kind) => {
                let callee = match kind {
                    FloatKind::F32 => self.print_f32,
                    FloatKind::F64 => self.print_f64,
                };
                self.runtime_call(callee, &values)
            }
            Target::Float(op) => {
                return Some(self.float_builtin(*op, &values, ty));
            }
            Target::Int(op, source, target) => {
                return Some(self.int_builtin(*op, *source, *target, &values, ty));
            }
            Target::Panic => {
                self.abort();
                return None;
            }
            Target::StageCompile(shape) => {
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    8,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let pointer = self.builder.ins().stack_addr(I64, slot, 0);
                let status = self.runtime_call(self.stage_compile, &[values[0], pointer]);
                let owner = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), pointer, 0);
                let success = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                let ok = self.encode_variant(ty, shape.ok_tag, &[owner]);
                let err = self.encode_variant(ty, shape.err_tag, &[status]);
                return Some(
                    ok.into_iter()
                        .zip(err)
                        .map(|(ok, err)| self.builder.ins().select(success, ok, err))
                        .collect(),
                );
            }
            Target::StageEntry(signature) => {
                debug_assert_eq!(ty, Type::Fn(*signature));
                let owner = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                self.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), owner, 16)
            }
            // GPU-SUBSET: `#[gpu]` bodies are compiled for the CPU
            // only as unreachable code; no CPU call reaches them.
            Target::Gpu(..) => {
                self.abort();
                return None;
            }
        };
        Some(vec![scalar])
    }
    /// The data pointer and byte length of a text view's source: a
    /// `&String` or another text view (`values` are its lowered words).
    fn text_view_source(&mut self, base_ty: Type, values: &[Value]) -> (Value, Value) {
        match base_ty {
            Type::Ref(p) | Type::RefMut(p) => match self.program.pointees[p] {
                Type::String => {
                    let handle =
                        self.builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), values[0], 0);
                    let data = self.builder.ins().iadd_imm_s(handle, 16);
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    (data, length)
                }
                _ => unreachable!("checked text view source"),
            },
            Type::Str | Type::StrMut => (values[0], values[1]),
            _ => unreachable!("checked text view source"),
        }
    }
    /// Check a text view's range and build its descriptor.
    fn finish_text_view(
        &mut self,
        pointer: Value,
        length: Value,
        start: Value,
        end: Value,
        check: bool,
    ) -> Words {
        if check {
            self.check_range(start, end, length);
            self.check_text_boundary(pointer, start, length);
            self.check_text_boundary(pointer, end, length);
        }
        let pointer = self.builder.ins().iadd(pointer, start);
        let length = self.builder.ins().isub(end, start);
        vec![pointer, length, self.constant(1), self.constant(1)]
    }
    /// `(data, length, stride, byte flag)` of an element view's source: a
    /// dynamic array or inline array in pinned storage, or lowered `values`
    /// of an array, `&Bytes`, `&Vec` or slice.
    fn view_source(
        &mut self,
        base_ty: Type,
        element_width: usize,
        array_location: Option<Value>,
        dynamic_array_location: Option<(Value, usize)>,
        values: &[Value],
    ) -> (Value, Value, Value, Value) {
        if let Some((location, word_offset)) = dynamic_array_location {
            // Word 0 is the runtime length; elements follow it.
            let base_address = if word_offset == 0 {
                location
            } else {
                self.builder
                    .ins()
                    .iadd_imm_s(location, (word_offset * 8) as i64)
            };
            let data = self.builder.ins().iadd_imm_s(base_address, 8);
            let length = self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), base_address, 0);
            (
                data,
                length,
                self.constant((element_width * 8) as i64),
                self.constant(0),
            )
        } else if let Some(location) = array_location {
            let (_, length) = base_ty
                .layout()
                .and_then(|id| self.program.enums[id].array)
                .expect("checked array slice source");
            // Word 0 is the private array tag; elements follow it.
            let data = self.builder.ins().iadd_imm_s(location, 8);
            (
                data,
                self.constant(length as i64),
                self.constant((element_width * 8) as i64),
                self.constant(0),
            )
        } else if let Some((_, length)) =
            base_ty.layout().and_then(|id| self.program.enums[id].array)
        {
            let slot = self.stack_words(values.len());
            self.store_words(slot, values);
            // Word 0 is the private array tag; elements follow it.
            let data = self.builder.ins().iadd_imm_s(slot, 8);
            (
                data,
                self.constant(length as i64),
                self.constant((element_width * 8) as i64),
                self.constant(0),
            )
        } else {
            match base_ty {
                Type::Ref(p) => match self.program.pointees[p] {
                    Type::Bytes => {
                        let handle =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        let data = self.builder.ins().iadd_imm_s(handle, 16);
                        let length =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), handle, 0);
                        (data, length, self.constant(1), self.constant(1))
                    }
                    Type::Vec(_) => {
                        let handle =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        let data = self.builder.ins().iadd_imm_s(handle, 16);
                        let length =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), handle, 0);
                        (
                            data,
                            length,
                            self.constant((element_width * 8) as i64),
                            self.constant(0),
                        )
                    }
                    _ => unreachable!("checked slice source"),
                },
                Type::Slice(_) | Type::SliceMut(_) => (values[0], values[1], values[2], values[3]),
                _ => unreachable!("checked slice source"),
            }
        }
    }
    /// Check an element view's range and build its descriptor.
    #[allow(clippy::too_many_arguments)]
    fn finish_view(
        &mut self,
        pointer: Value,
        length: Value,
        stride: Value,
        bytes: Value,
        start: Value,
        end: Value,
        check: bool,
    ) -> Words {
        if check {
            self.check_range(start, end, length);
        }
        let offset = self.builder.ins().imul(start, stride);
        let pointer = self.builder.ins().iadd(pointer, offset);
        let length = self.builder.ins().isub(end, start);
        vec![pointer, length, stride, bytes]
    }
    /// A binary operation (not `&&`/`||`) on lowered non-float scalars.
    fn scalar_binary(
        &mut self,
        op: &Kind,
        left_kind: Option<IntKind>,
        right_kind: Option<IntKind>,
        left: Value,
        right: Value,
        deferral: Option<deferred::Mode>,
    ) -> Value {
        if let Some(kind) = left_kind {
            return self.int_binary(kind, op, left, right, right_kind, deferral);
        }
        match op {
            Kind::Plus | Kind::Minus | Kind::Star if deferral.is_some() => {
                self.deferred_i64(op, left, right, deferral.unwrap())
            }
            Kind::Plus | Kind::Minus | Kind::Star => {
                let (value, overflow) = match op {
                    Kind::Plus => self.builder.ins().sadd_overflow(left, right),
                    Kind::Minus => self.builder.ins().ssub_overflow(left, right),
                    Kind::Star => self.builder.ins().smul_overflow(left, right),
                    _ => unreachable!(),
                };
                self.guard(overflow);
                value
            }
            Kind::Slash | Kind::Percent => {
                let zero = self.builder.ins().icmp_imm_s(IntCC::Equal, right, 0);
                self.guard(zero);
                let min = self.builder.ins().icmp_imm_s(IntCC::Equal, left, i64::MIN);
                let neg = self.builder.ins().icmp_imm_s(IntCC::Equal, right, -1);
                let invalid = self.builder.ins().band(min, neg);
                self.guard(invalid);
                if *op == Kind::Slash {
                    self.builder.ins().sdiv(left, right)
                } else {
                    self.builder.ins().srem(left, right)
                }
            }
            _ => {
                let condition = match op {
                    Kind::Lt => IntCC::SignedLessThan,
                    Kind::Le => IntCC::SignedLessThanOrEqual,
                    Kind::Gt => IntCC::SignedGreaterThan,
                    Kind::Ge => IntCC::SignedGreaterThanOrEqual,
                    Kind::EqEq => IntCC::Equal,
                    Kind::Ne => IntCC::NotEqual,
                    _ => unreachable!(),
                };
                let value = self.builder.ins().icmp(condition, left, right);
                self.builder.ins().uextend(I64, value)
            }
        }
    }
    /// A unary operation on a lowered scalar operand. `None` when it always
    /// panics (`!` on a float). `leaf` identifies the operand for deferred
    /// overflow tracking.
    fn unary_value(
        &mut self,
        span: crate::Span,
        op: &Kind,
        operand_ty: Type,
        value: Value,
        deferral: Option<deferred::Mode>,
        leaf: usize,
    ) -> Option<Value> {
        if *op == Kind::Minus && operand_ty.float_kind().is_none() {
            let zero = self.constant(0);
            self.fuzz_arith(span, &Kind::Bang, operand_ty.int_kind(), None, value, zero);
        }
        let value = if let Some(kind) = operand_ty.float_kind() {
            if *op != Kind::Minus {
                self.abort();
                return None;
            }
            let mask = match kind {
                FloatKind::F32 => 1i64 << 31,
                FloatKind::F64 => i64::MIN,
            };
            let mask = self.constant(mask);
            self.builder.ins().bxor(value, mask)
        } else if let Some(kind) = operand_ty.int_kind().filter(|k| *k != IntKind::I64) {
            if *op == Kind::Minus {
                let zero = self.constant(0);
                if deferral.is_some() {
                    // A narrow value negates exactly in 64 bits.
                    let negated = self.builder.ins().isub(zero, value);
                    self.defer_int_range(kind, negated)
                } else {
                    let (negated, overflow) = self.builder.ins().ssub_overflow(zero, value);
                    self.guard(overflow);
                    self.check_int_range(kind, negated)
                }
            } else {
                let inverted = self.builder.ins().bnot(value);
                self.canonical(kind, inverted)
            }
        } else if *op == Kind::Bang && operand_ty == Type::I64 {
            self.builder.ins().bnot(value)
        } else if *op == Kind::Minus {
            let zero = self.constant(0);
            if let Some(mode) = deferral {
                let negated = self.builder.ins().isub(zero, value);
                if mode == deferred::Mode::Exact {
                    // `0 - v` overflows exactly when `v` and the
                    // result are both negative (`v == i64::MIN`).
                    let overflow = self.builder.ins().band(value, negated);
                    self.defer_sign(overflow);
                } else {
                    self.track_leaf(leaf, value);
                }
                negated
            } else {
                let (value, overflow) = self.builder.ins().ssub_overflow(zero, value);
                self.guard(overflow);
                value
            }
        } else {
            let comparison = self.builder.ins().icmp_imm_s(IntCC::Equal, value, 0);
            self.builder.ins().uextend(I64, comparison)
        };
        Some(value)
    }
    fn short_circuit(&mut self, op: &Kind, left: Value, right: &Expr) -> Option<Words> {
        let rhs = self.builder.create_block();
        let shortcut = self.builder.create_block();
        let join = self.join(Type::Bool).unwrap();
        if *op == Kind::AmpAmp {
            self.builder.ins().brif(left, rhs, &[], shortcut, &[]);
        } else {
            self.builder.ins().brif(left, shortcut, &[], rhs, &[]);
        }
        self.builder.switch_to_block(shortcut);
        let value = self.constant(i64::from(*op == Kind::PipePipe));
        self.jump(join, &[value]);
        self.builder.switch_to_block(rhs);
        if let Some(value) = self.scalar(right) {
            self.jump(join, &[value]);
        }
        self.builder.switch_to_block(join);
        Some(self.builder.block_params(join).to_vec())
    }
    fn pattern(&mut self, pattern: &Pattern, values: &[Value]) -> Value {
        match pattern {
            Pattern::Any | Pattern::Bind(_) => self.builder.ins().iconst(ir::types::I8, 1),
            Pattern::Literal(n) => self.builder.ins().icmp_imm_s(IntCC::Equal, values[0], *n),
            Pattern::Variant {
                tag,
                fields,
                tagged,
                niche,
            } => {
                let mut result = if let Some(niche) = niche {
                    let (cc, constant) = decoder_test(niche.decoder(*tag));
                    self.builder.ins().icmp_imm_s(cc, values[0], constant)
                } else if *tagged {
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], *tag as i64)
                } else {
                    self.builder.ins().iconst(ir::types::I8, 1)
                };
                for (offset, p) in fields {
                    let field = self.pattern(p, &values[*offset..]);
                    result = self.builder.ins().band(result, field);
                }
                result
            }
            Pattern::Type { tag, inner, .. } => {
                let result = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::Equal, values[0], *tag as i64);
                let narrowed = self.pattern(inner, &values[1..]);
                self.builder.ins().band(result, narrowed)
            }
            Pattern::Or(ps) => {
                let mut result = self.builder.ins().iconst(ir::types::I8, 0);
                for p in ps {
                    let p = self.pattern(p, values);
                    result = self.builder.ins().bor(result, p);
                }
                result
            }
            Pattern::DynArray {
                element,
                capacity,
                prefix,
                suffix,
                rest,
                ..
            } => {
                let width = self.program.width(*element);
                let length = values[0];
                let required = (prefix.len() + suffix.len()) as i64;
                let mut result = if *rest {
                    self.builder.ins().icmp_imm_s(
                        IntCC::UnsignedGreaterThanOrEqual,
                        length,
                        required,
                    )
                } else {
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, length, required)
                };
                for (index, pattern) in prefix.iter().enumerate() {
                    let field = self.pattern(pattern, &values[1 + index * width..]);
                    result = self.builder.ins().band(result, field);
                }
                for (index, pattern) in suffix.iter().enumerate() {
                    let words = self.dyn_suffix_element(
                        values,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    let field = self.pattern(pattern, &words);
                    result = self.builder.ins().band(result, field);
                }
                result
            }
        }
    }
    /// Bind a borrowed DynArray pattern over the array at `pointer`. Element
    /// names receive slot addresses, the rest a `&[T]` descriptor, and
    /// by-value element patterns bind copies from the loaded `words`.
    fn bind_borrowed_dyn(&mut self, pattern: &Pattern, pointer: Value, words: &[Value]) {
        let Pattern::DynArray {
            element,
            capacity,
            prefix,
            suffix,
            rest_binding,
            ..
        } = pattern
        else {
            return;
        };
        let width = self.program.width(*element);
        let stride = (width * 8) as i64;
        let length = words[0];
        let data = self.builder.ins().iadd_imm_s(pointer, 8);
        for (index, pattern) in prefix.iter().enumerate() {
            match pattern {
                Pattern::Bind(slot) => {
                    let address = self.builder.ins().iadd_imm_s(data, index as i64 * stride);
                    self.assign(*slot, &[address]);
                }
                pattern => self.bind_pattern(pattern, &words[1 + index * width..]),
            }
        }
        for (index, pattern) in suffix.iter().enumerate() {
            match pattern {
                Pattern::Bind(slot) => {
                    // Slot `length - suffix + index`, computed at run time.
                    let position = self
                        .builder
                        .ins()
                        .iadd_imm_s(length, index as i64 - suffix.len() as i64);
                    let offset = self.builder.ins().imul_imm_s(position, stride);
                    let address = self.builder.ins().iadd(data, offset);
                    self.assign(*slot, &[address]);
                }
                pattern => {
                    let element_words = self.dyn_suffix_element(
                        words,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    self.bind_pattern(pattern, &element_words);
                }
            }
        }
        if let Some(slot) = rest_binding {
            let start = self
                .builder
                .ins()
                .iadd_imm_s(data, prefix.len() as i64 * stride);
            let middle = self
                .builder
                .ins()
                .iadd_imm_s(length, -((prefix.len() + suffix.len()) as i64));
            let stride = self.constant(stride);
            let bytes = self.constant(0);
            self.assign(*slot, &[start, middle, stride, bytes]);
        }
    }
    /// The words of suffix element `index` of a DynArray pattern: the slot at
    /// `length - suffix + index`, selected over the SSA slots it may occupy
    /// (from `prefix + index` up to `capacity - suffix + index`). When the
    /// length guard fails the selected words are unused.
    fn dyn_suffix_element(
        &mut self,
        values: &[Value],
        width: usize,
        capacity: usize,
        prefix: usize,
        suffix: usize,
        index: usize,
    ) -> Vec<Value> {
        let length = values[0];
        let mut words = vec![self.constant(0); width];
        for slot in prefix + index..=capacity - suffix + index {
            let here =
                self.builder
                    .ins()
                    .icmp_imm_s(IntCC::Equal, length, (slot + suffix - index) as i64);
            for (word, out) in words.iter_mut().enumerate() {
                *out = self
                    .builder
                    .ins()
                    .select(here, values[1 + slot * width + word], *out);
            }
        }
        words
    }
    fn dispose_pattern(&mut self, pattern: &Pattern, ty: Type, values: &[Value]) {
        match pattern {
            Pattern::Any => self.drop_value(ty, values),
            Pattern::Bind(slot) => self.activate_local(*slot),
            Pattern::Variant { tag, fields, .. } => {
                let Some(id) = ty.layout() else {
                    unreachable!()
                };
                for ((offset, p), ty) in fields
                    .iter()
                    .zip(self.program.enums[id].variants[*tag].fields.clone())
                    .rev()
                {
                    self.dispose_pattern(p, ty, &values[*offset..]);
                }
            }
            Pattern::Type { member, inner, .. } => {
                self.dispose_pattern(inner, *member, &values[1..]);
            }
            Pattern::DynArray { .. } => {}
            Pattern::Or(ps) => {
                let join = self.builder.create_block();
                for p in ps {
                    let condition = self.pattern(p, values);
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    self.dispose_pattern(p, ty, values);
                    self.jump(join, &[]);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(join);
            }
            _ => {}
        }
    }
    fn bind_pattern(&mut self, pattern: &Pattern, values: &[Value]) {
        match pattern {
            Pattern::Bind(slot) => {
                let width = self.variables[*slot].len();
                self.assign(*slot, &values[..width]);
            }
            Pattern::Variant { fields, .. } => {
                for (offset, p) in fields {
                    self.bind_pattern(p, &values[*offset..]);
                }
            }
            Pattern::Type { inner, .. } => self.bind_pattern(inner, &values[1..]),
            Pattern::DynArray {
                element,
                capacity,
                prefix,
                suffix,
                rest_binding,
                ..
            } => {
                let width = self.program.width(*element);
                for (index, pattern) in prefix.iter().enumerate() {
                    self.bind_pattern(pattern, &values[1 + index * width..]);
                }
                for (index, pattern) in suffix.iter().enumerate() {
                    let words = self.dyn_suffix_element(
                        values,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    self.bind_pattern(pattern, &words);
                }
                if let Some(slot) = rest_binding {
                    let zero = self.constant(0);
                    let length = values[0];
                    let mut tail = vec![zero; 1 + width * *capacity];
                    let rest_length = self
                        .builder
                        .ins()
                        .iadd_imm_s(length, -((prefix.len() + suffix.len()) as i64));
                    tail[0] = rest_length;
                    for position in 0..capacity.saturating_sub(prefix.len() + suffix.len()) {
                        let source = prefix.len() + position;
                        // The middle slot `source` is live when it is before
                        // the suffix: `length > source + suffix`.
                        let active = self.builder.ins().icmp_imm_s(
                            IntCC::UnsignedGreaterThan,
                            length,
                            (source + suffix.len()) as i64,
                        );
                        for word in 0..width {
                            let value = values[1 + source * width + word];
                            tail[1 + position * width + word] =
                                self.builder.ins().select(active, value, zero);
                        }
                    }
                    self.assign(*slot, &tail);
                }
            }
            Pattern::Or(ps) if ps.iter().any(has_bindings) => {
                let join = self.builder.create_block();
                for p in ps {
                    let condition = self.pattern(p, values);
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    self.bind_pattern(p, values);
                    self.jump(join, &[]);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(join);
            }
            _ => {}
        }
    }
}
/// Root local and total word offset of a record-field projection chain.
fn projection_offset(expr: &Expr) -> Option<(usize, usize)> {
    let mut offset = 0usize;
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, field) => {
                offset += field;
                current = base;
            }
            ExprKind::Peek(slot)
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::InitOwner { slot, .. } => {
                return Some((*slot, offset));
            }
            _ => return None,
        }
    }
}
/// The temporary-owner initializer at the root of a field projection chain.
fn projection_root_init(expr: &Expr) -> Option<(usize, &Expr)> {
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, _) => current = base,
            ExprKind::InitOwner { slot, value } => return Some((*slot, value)),
            _ => return None,
        }
    }
}
fn has_bindings(p: &Pattern) -> bool {
    match p {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| has_bindings(p)),
        Pattern::Type { inner, .. } => has_bindings(inner),
        Pattern::Or(ps) => ps.iter().any(has_bindings),
        Pattern::DynArray {
            prefix,
            suffix,
            rest_binding,
            ..
        } => {
            rest_binding.is_some()
                || prefix.iter().any(has_bindings)
                || suffix.iter().any(has_bindings)
        }
        _ => false,
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod scalar_inline_codegen_tests {
    use super::*;

    #[test]
    fn depth_guards_exist_only_in_functions_that_install_handlers() {
        if Command::new("objdump").arg("--version").output().is_err() {
            return;
        }
        let program=ex::check(r#"
            effect Op:i64->i64;
            fn leaf(n:i64)->i64 ! {} {let mut i=0;while i<n {i=i+1;if i==2 {continue;}if i==4 {break;}}loop {break i;}}
            fn install()->i64 ! {} {
                handle Op:i64->i64 with fn(x:i64,r:linear once fn(i64)->i64 ! {})->i64 ! {} {r(x)} {leaf(8)}
            }
            fn main()->i64 ! {} {install()}
        "#).unwrap();
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        for options in [CodegenOptions::default(), CodegenOptions::release()] {
            let path = scratch.path().join("guards.o");
            fs::write(&path, object(&program, options).unwrap()).unwrap();
            for name in ["leaf", "install", "main"] {
                let index = program
                    .functions
                    .iter()
                    .position(|f| f.name.rsplit('.').next() == Some(name))
                    .unwrap();
                let output = Command::new("objdump")
                    .args([
                        "-dr",
                        "--no-show-raw-insn",
                        &format!("--disassemble=kush_fn_{index}"),
                    ])
                    .arg(&path)
                    .output()
                    .unwrap();
                assert!(output.status.success());
                let assembly = String::from_utf8(output.stdout).unwrap();
                assert_eq!(
                    assembly.contains("kush_handler_depth"),
                    name == "install",
                    "{name}: {assembly}"
                );
                assert_eq!(
                    assembly.contains("kush_handler_restore"),
                    name == "install",
                    "{name}: {assembly}"
                );
            }
        }
    }

    #[test]
    fn map_callback_inlining_removes_machine_calls_without_backend_optimization() {
        if Command::new("objdump").arg("--version").output().is_err() {
            eprintln!("objdump unavailable; machine-code inspection skipped");
            return;
        }
        let program = ex::check("fn first(x:i64)->i64 ! {} {x & 255} fn second(x:i64)->i64 ! {} {x ^ 7} fn mapped(v:Vec<i64>)->Vec<i64> ! {} {Vec.map_in_place(Vec.map_in_place(v,first),second)} fn main()->i64 ! {alloc} {let v:Vec<i64> = [1];Vec.get(&mapped(v),0)}").unwrap();
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some("mapped"))
            .unwrap();
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let mut calls = Vec::new();
        for enabled in [false, true] {
            let path = scratch.path().join(format!("inline-{enabled}.o"));
            fs::write(
                &path,
                object(
                    &program,
                    CodegenOptions::cranelift(Optimization::None, enabled),
                )
                .unwrap(),
            )
            .unwrap();
            let output = Command::new("objdump")
                .args([
                    "-dr",
                    "--no-show-raw-insn",
                    &format!("--disassemble=kush_fn_{index}"),
                ])
                .arg(&path)
                .output()
                .unwrap();
            assert!(output.status.success());
            let assembly = String::from_utf8(output.stdout).unwrap();
            assert!(
                assembly.contains(&format!("<kush_fn_{index}>:")),
                "{assembly}"
            );
            calls.push(
                assembly
                    .lines()
                    .filter(|line| {
                        line.split_whitespace()
                            .nth(1)
                            .is_some_and(|word| word.starts_with("call"))
                    })
                    .count(),
            );
        }
        assert!(
            calls[0] >= calls[1] + 2,
            "callback calls were not removed: {calls:?}"
        );
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod allocator_runtime_tests {
    use super::*;

    /// References to locals point into native stack slots; every slot must be
    /// created with the contract alignment, never a literal.
    #[test]
    fn every_stack_slot_uses_the_pointer_alignment_contract() {
        let source = include_str!("native.rs");
        let marker = ["StackSlotData", "::new("].concat();
        let mut slots = 0;
        for (start, _) in source.match_indices(&marker) {
            let call = &source[start..start + source[start..].find("));").unwrap()];
            assert!(
                call.contains("STACK_SLOT_ALIGN_SHIFT"),
                "stack slot without the alignment contract: {call}"
            );
            slots += 1;
        }
        assert!(slots >= 17, "{slots}");
        assert_eq!(1u64 << STACK_SLOT_ALIGN_SHIFT, POINTER_ALIGN);
    }

    /// UNBOX-ALIGN-CONTRACT: every allocation path returns a nonzero pointer
    /// that is a multiple of `POINTER_ALIGN`, including pool reuse, growth,
    /// fallible paths, arenas (with and without fresh chunks), allocator
    /// blocks and vector/byte element storage.
    #[test]
    fn every_allocation_path_returns_nonzero_pointer_aligned_storage() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("alignment-test.c");
        let binary = scratch.path().join("alignment-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
static uint64_t checked = 0;
static void aligned(uint64_t pointer, uint64_t align) {
    assert(pointer != 0);
    assert(pointer % KUSH_POINTER_ALIGN == 0);
    assert(pointer % align == 0);
    ++checked;
}
int main(int argc, char **argv) {
    (void)argc; (void)argv;
    uint64_t live[64];
    for (int round = 0; round < 3; ++round) {
        /* Ordinary boxes: every pool class, the system path, and reuse. */
        for (uint64_t bytes = 0; bytes <= 2 * KUSH_POOL_MAX; bytes += 8) {
            uint64_t p = kush_alloc(bytes);
            aligned(p, KUSH_ALLOC_ALIGN);
            kush_free(p);
        }
        for (int i = 0; i < 64; ++i) { live[i] = kush_alloc((uint64_t)(i * 24)); aligned(live[i], KUSH_ALLOC_ALIGN); }
        for (int i = 0; i < 64; ++i) kush_free(live[i]);
        /* Fallible allocation and growth. */
        uint64_t t = kush_try_alloc(40);
        aligned(t, KUSH_ALLOC_ALIGN);
        void *g = kush_grow((void *)(uintptr_t)t, 5000);
        aligned((uint64_t)(uintptr_t)g, KUSH_ALLOC_ALIGN);
        g = kush_try_grow(g, 9000);
        aligned((uint64_t)(uintptr_t)g, KUSH_ALLOC_ALIGN);
        kush_free((uint64_t)(uintptr_t)g);
        /* Headerless buffers, bytes and vectors (element data included). */
        for (uint64_t bytes = 16; bytes <= 2 * KUSH_POOL_MAX; bytes += 16) {
            uint64_t b = kush_buffer_alloc(bytes, bytes - 16, 0);
            aligned(b, KUSH_ALLOC_ALIGN);
            kush_buffer_free(b);
        }
        for (int64_t capacity = 0; capacity < 3000; capacity += 97) {
            uint64_t b = kush_bytes_with_capacity(capacity);
            aligned(b, KUSH_ALLOC_ALIGN);
            aligned((uint64_t)(uintptr_t)kush_alloc_block_data(b), KUSH_POINTER_ALIGN);
            kush_bytes_free(b);
            uint64_t tb = kush_try_bytes_with_capacity(capacity);
            aligned(tb, KUSH_ALLOC_ALIGN);
            kush_bytes_free(tb);
        }
        uint64_t v = kush_vec_with_capacity(1, 3);
        for (int64_t i = 0; i < 200; ++i) {
            uint64_t words[3] = {(uint64_t)i, 0, 0};
            v = kush_vec_push(v, words, 3);
            KushVec *vec = (KushVec *)(uintptr_t)v;
            aligned(v, KUSH_ALLOC_ALIGN);
            aligned((uint64_t)(uintptr_t)&vec->data[i * 3], KUSH_POINTER_ALIGN);
        }
        kush_buffer_free(v);
        /* Arenas: odd sizes, fresh chunks and the fallible path. */
        uint64_t arena = kush_arena_new();
        aligned(arena, KUSH_ALLOC_ALIGN);
        for (uint64_t bytes = 1; bytes < 3000; bytes += 37) {
            uint64_t a = kush_arena_alloc(arena, bytes);
            aligned(a, KUSH_POINTER_ALIGN);
            uint64_t b = kush_arena_try_alloc(arena, bytes + 3);
            aligned(b, KUSH_POINTER_ALIGN);
            kush_arena_box_release(a);
            kush_arena_box_release(b);
        }
        kush_arena_release(arena);
    }
    kush_pool_drain();
    assert(kush_live_allocations == 0);
    assert(checked > 3000);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(POINTER_ALIGN, 8);
        assert!(
            RUNTIME.contains("#define KUSH_POINTER_ALIGN ((uint64_t)8)"),
            "the C runtime and POINTER_ALIGN must agree"
        );
    }

    #[test]
    fn headerless_buffers_preserve_growth_capacity_and_typed_release() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("headerless-test.c");
        let binary = scratch.path().join("headerless-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
int main(int argc, char **argv) {
    if (argc > 1) {
        uint64_t handle=kush_bytes_with_capacity(0), guard=kush_alloc(8);
        (void)argv; (void)guard;
        kush_bytes_free(handle);
        kush_bytes_free(handle);
        return 90;
    }
    assert(sizeof(KushBytes)==16 && sizeof(KushVec)==16);
    uint64_t ordinary[2]={0,UINT64_C(0x7fffffffffffffef)};
    assert(kush_buffer_capacity(ordinary)==UINT64_C(0x7fffffffffffffef));
    kush_buffer_set_capacity(ordinary,UINT64_C(0x7fffffffffffffff));
    assert(kush_buffer_capacity(ordinary)==UINT64_C(0x7fffffffffffffff));
    for (int64_t capacity=0;capacity<=1100;capacity++) {
        uint64_t handle=kush_bytes_with_capacity(capacity);
        KushBytes *b=(KushBytes *)(uintptr_t)handle;
        assert(((uintptr_t)b & 15)==0);
        assert(kush_bytes_capacity(handle)==capacity);
        assert(b->capacity==(uint64_t)capacity);
        for (int64_t i=0;i<capacity;i++) handle=kush_bytes_push(handle,i%256);
        assert(kush_bytes_len(handle)==capacity);
        for (int64_t i=0;i<capacity;i++) assert(kush_bytes_get(handle,i)==i%256);
        handle=kush_bytes_push(handle,42);
        assert(kush_bytes_get(handle,capacity)==42);
        kush_bytes_free(handle);
    }
    kush_pool_drain();
    for(size_t i=0;i<KUSH_POOL_CLASSES;i++) assert(kush_pool_counts[i]==0);
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    uint64_t v=kush_vec_with_capacity(4,4);
    for(int64_t i=0;i<4;i++) {uint64_t words[4]={(uint64_t)i,2,3,4};v=kush_vec_push(v,words,4);}
    /* Emulate a checked narrowing map's compacted slots without changing its
       physical class; logical capacity remains four elements. */
    KushVec *vec=(KushVec *)(uintptr_t)v;
    for(int64_t i=0;i<4;i++) vec->data[i]=(uint64_t)i;
    kush_try_fail_after=0;kush_try_attempts=0;kush_try_probe_initialized=1;
    assert(kush_vec_try_reserve(v,8,1)==v);
    assert(kush_buffer_capacity(vec)==12 && kush_try_attempts==0);
    assert(kush_vec_try_reserve(v,1000,1)==0);
    assert(kush_buffer_capacity(vec)==12);
    kush_try_fail_after=UINT64_MAX;
    uint64_t grown=kush_vec_try_reserve(v,1000,1);
    assert(grown!=0);
    vec=(KushVec *)(uintptr_t)grown;
    assert(!(vec->capacity & KUSH_BUFFER_RAW));
    for(int64_t i=0;i<4;i++) assert(vec->data[i]==(uint64_t)i);
    kush_buffer_free(grown);
    kush_pool_drain();
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary).arg("double").output().unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
    }

    #[test]
    fn compact_headers_preserve_alignment_markers_growth_and_class_counts() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("runtime-test.c");
        let binary = scratch.path().join("runtime-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
int main(int argc, char **argv) {
    if (argc > 1) {
        uint64_t first=kush_alloc(8), guard=kush_alloc(8);
        (void)guard;
        if (strcmp(argv[1], "double") == 0) kush_free(first);
        else ((KushAllocHeader *)(uintptr_t)first-1)->magic=0;
        kush_free(first);
        return 90;
    }
    assert(sizeof(KushAllocHeader)==16);
    const uint64_t sizes[]={0,1,16,17,1024,1025};
    for (size_t i=0;i<sizeof(sizes)/sizeof(sizes[0]);i++) {
        uint64_t handle=kush_alloc(sizes[i]);
        assert((handle & 15)==0);
        KushAllocHeader *header=(KushAllocHeader *)(uintptr_t)handle-1;
        assert(kush_block_live(header));
        assert(header->magic==(sizes[i]<=1024 ? KUSH_ALLOC_MAGIC : KUSH_ALLOC_UNPOOLED));
        memset((void *)(uintptr_t)handle,0x5a,(size_t)sizes[i]);
        void *grown=kush_grow((void *)(uintptr_t)handle,sizes[i]+2048);
        assert(((uintptr_t)grown & 15)==0);
        for (uint64_t j=0;j<sizes[i];j++) assert(((unsigned char *)grown)[j]==0x5a);
        kush_free((uint64_t)(uintptr_t)grown);
    }
    kush_pool_drain();
    uint64_t owner=kush_alloc(17);
    KushAllocHeader *header=(KushAllocHeader *)(uintptr_t)owner-1;
    header->magic=0;
    assert(kush_try_grow((void *)(uintptr_t)owner,64)==NULL);
    header->magic=KUSH_ALLOC_MAGIC;
    kush_free(owner);
    owner=kush_try_alloc(17);
    assert(owner!=0 && ((KushAllocHeader *)(uintptr_t)owner-1)->magic==KUSH_ALLOC_MAGIC);
    kush_free(owner);
    kush_pool_drain();
    uint64_t blocks[128];
    for (size_t i=0;i<128;i++) blocks[i]=kush_alloc(1);
    for (size_t i=0;i<128;i++) kush_free(blocks[i]);
    assert(kush_pool_counts[0]==KUSH_POOL_CLASS_CAP);
    assert(kush_pool_retained==KUSH_POOL_CLASS_CAP*32);
    for (size_t i=0;i<64;i++) blocks[i]=kush_try_alloc(1);
    assert(kush_pool_counts[0]==0 && kush_pool_retained==0);
    for (size_t i=0;i<64;i++) kush_free(blocks[i]);
    kush_pool_drain();
    for (size_t i=0;i<KUSH_POOL_CLASSES;i++) assert(kush_pool_counts[i]==0);
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        for argument in ["double", "corrupt"] {
            let output = Command::new(&binary).arg(argument).output().unwrap();
            assert!(!output.status.success());
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}

/// PROOF-FUZZ: the runtime hooks of an instrumented build and the site id of
/// each obligation, keyed by span and [`fuzz_kind`].
#[derive(Clone)]
struct FuzzHooks {
    enter: FuncId,
    leave: FuncId,
    arith: FuncId,
    sites: std::rc::Rc<BTreeMap<(usize, usize, u8), i64>>,
}
/// The kind of an obligation as one byte: 0 bounds, 1 overflow, 2 division,
/// 3 shift.
fn fuzz_kind(kind: crate::executable::ObligationKind) -> u8 {
    use crate::executable::ObligationKind;
    match kind {
        ObligationKind::Bounds { .. } => 0,
        ObligationKind::Overflow => 1,
        ObligationKind::Division => 2,
        ObligationKind::Shift => 3,
    }
}
