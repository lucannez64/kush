//! Machine-code recipes for the in-process staging linker. Recipe entry ABIs
//! match F directly; captured values are read from artifact-local constants.
use super::*;
use cranelift_module::{ModuleReloc, ModuleRelocTarget};

pub(super) struct Prepared {
    pub program: Executable,
    /// Native recipe index -> (quotation schema index, capture count).
    pub recipes: BTreeMap<usize, (usize, usize)>,
}

fn expressions(block: &ex::Block, f: &mut impl FnMut(&Expr)) {
    fn visit(e: &Expr, f: &mut impl FnMut(&Expr)) {
        f(e);
        e.for_each_child(&mut |child| visit(child, f));
    }
    for statement in &block.statements {
        match statement {
            ex::Statement::Let(_, e) | ex::Statement::Expr(e) => visit(e, f),
            ex::Statement::Declare(_) => {}
        }
    }
    if let Some(e) = &block.tail {
        visit(e, f);
    }
}

pub(super) fn prepare(program: &Executable) -> Option<Prepared> {
    let needed = program.functions.iter().any(|function| {
        let mut compiles = false;
        expressions(&function.body, &mut |e| {
            compiles |= matches!(e.kind, ExprKind::Call(Target::StageCompile(_), _));
        });
        compiles
    });
    if !needed {
        return None;
    }
    let mut program = program.clone();
    let mut recipes = BTreeMap::new();
    for &schema in &program.stage_templates {
        let mut function = program.functions[schema].clone();
        if !crate::staging::runtime_template_supported(&program, schema) {
            continue;
        }
        let captures = function.closure.unwrap_or(0);
        if captures == 0 {
            recipes.insert(schema, (schema, 0));
            continue;
        }
        function.name = format!("staging recipe {schema}");
        function.closure = None;
        function.capture_refs.clear();
        function.capture_writes.clear();
        function.parameter_slots = Some(match function.parameter_slots.take() {
            Some(slots) => slots[captures..].to_vec(),
            None => (captures..function.parameters).collect(),
        });
        function.parameters -= captures;
        function.parameter_grades = function.parameter_grades[captures..].to_vec();
        function.parameter_lifetimes = function.parameter_lifetimes[captures..].to_vec();
        let recipe = program.functions.len();
        recipes.insert(recipe, (schema, captures));
        program.functions.push(function);
        program.foreign_functions.push(None);
    }
    Some(Prepared { program, recipes })
}

#[derive(Clone)]
pub(super) struct Body {
    pub bytes: Vec<u8>,
    pub relocs: Vec<ModuleReloc>,
}

pub(super) fn capture_data(
    module: &mut CodeModule,
    recipes: &BTreeMap<usize, (usize, usize)>,
) -> Result<BTreeMap<(usize, usize), DataId>> {
    let mut result = BTreeMap::new();
    for (&recipe, &(_, captures)) in recipes {
        for capture in 0..captures {
            let id = module.declare_anonymous_data(false, false).map_err(error)?;
            let mut data = DataDescription::new();
            data.define_zeroinit(8);
            module.define_data(id, &data).map_err(error)?;
            result.insert((recipe, capture), id);
        }
    }
    Ok(result)
}

fn words(values: &[u64]) -> Vec<u8> {
    values.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn blob(module: &mut CodeModule, bytes: Vec<u8>) -> Result<DataId> {
    let id = module.declare_anonymous_data(false, false).map_err(error)?;
    let mut data = DataDescription::new();
    data.set_align(8);
    data.define(bytes.into_boxed_slice());
    module.define_data(id, &data).map_err(error)?;
    Ok(id)
}

fn data_pointer(module: &mut CodeModule, data: &mut DataDescription, at: usize, id: DataId) {
    let imported = module.declare_data_in_data(id, data);
    data.write_data_addr(at as u32, imported, 0);
}

fn function_pointer(module: &mut CodeModule, data: &mut DataDescription, at: usize, id: FuncId) {
    let imported = module.declare_func_in_data(id, data);
    data.write_function_addr(at as u32, imported);
}

pub(super) fn emit(
    module: &mut CodeModule,
    ids: &[FuncId],
    recipes: &BTreeMap<usize, (usize, usize)>,
    captures: &BTreeMap<(usize, usize), DataId>,
) -> Result<()> {
    // The table is linked into the executable. Its addresses can name local
    // Kush functions without exporting private declarations as public C APIs.
    let bodies = std::mem::take(&mut module.stage_bodies);
    let capture_ids: BTreeMap<_, _> = captures
        .iter()
        .map(|(&(recipe, slot), id)| (*id, (ids[recipe], slot)))
        .collect();
    let mut body_data = DataDescription::new();
    body_data.define_zeroinit(bodies.len() * 48);
    let mut body_bytes = Vec::new();
    for (position, (id, body)) in bodies.iter().enumerate() {
        let code = blob(module, body.bytes.clone())?;
        let mut reloc_data = DataDescription::new();
        reloc_data.set_align(8);
        let mut reloc_bytes = Vec::new();
        let mut addresses = Vec::new();
        for relocation in &body.relocs {
            use cranelift_codegen::binemit::Reloc;
            let kind = match relocation.kind {
                Reloc::Abs8 => 0,
                Reloc::X86PCRel4 => 1,
                Reloc::X86CallPCRel4 | Reloc::X86CallPLTRel4 => 2,
                Reloc::X86GOTPCRel4 => 3,
                _ => 255,
            };
            let (target_kind, target, address) = match relocation.name {
                ModuleRelocTarget::User {
                    namespace: 0,
                    index,
                } => (0, index as u64, Some((true, index))),
                ModuleRelocTarget::User {
                    namespace: 1,
                    index,
                } => {
                    let id = DataId::from_u32(index);
                    if let Some(&(recipe, slot)) = capture_ids.get(&id) {
                        (3, ((recipe.as_u32() as u64) << 32) | slot as u64, None)
                    } else {
                        (1, index as u64, Some((false, index)))
                    }
                }
                ModuleRelocTarget::FunctionOffset(function, offset) => {
                    (2, function.as_u32() as u64, Some((true, offset)))
                }
                _ => (255, 0, None),
            };
            let offset = reloc_bytes.len();
            reloc_bytes.extend(words(&[
                relocation.offset as u64,
                kind,
                target_kind,
                target,
                relocation.addend as u64,
                0,
            ]));
            addresses.push((offset + 40, target_kind, address));
        }
        reloc_data.define(reloc_bytes.into_boxed_slice());
        for (offset, kind, address) in addresses {
            if let Some((function, index)) = address {
                if kind == 2 {
                    // A function-relative offset is data, not a symbol address.
                    // Store it in the address word verbatim below instead.
                    continue;
                }
                if function {
                    function_pointer(module, &mut reloc_data, offset, FuncId::from_u32(index));
                } else {
                    data_pointer(module, &mut reloc_data, offset, DataId::from_u32(index));
                }
            }
        }
        // FunctionOffset's local label offset shares the final word with the
        // external-symbol address in the serialized relocation record.
        if let cranelift_module::Init::Bytes { contents } = &mut reloc_data.init {
            for (position, relocation) in body.relocs.iter().enumerate() {
                if let ModuleRelocTarget::FunctionOffset(_, offset) = relocation.name {
                    contents[position * 48 + 40..position * 48 + 48]
                        .copy_from_slice(&(offset as u64).to_le_bytes());
                }
            }
        }
        let reloc_id = module.declare_anonymous_data(false, false).map_err(error)?;
        module.define_data(reloc_id, &reloc_data).map_err(error)?;
        body_bytes.extend(words(&[
            id.as_u32() as u64,
            body.bytes.len() as u64,
            0,
            body.relocs.len() as u64,
            0,
            0,
        ]));
        data_pointer(module, &mut body_data, position * 48 + 16, code);
        data_pointer(module, &mut body_data, position * 48 + 32, reloc_id);
        function_pointer(module, &mut body_data, position * 48 + 40, *id);
    }
    body_data.init = cranelift_module::Init::Bytes {
        contents: body_bytes.into_boxed_slice(),
    };
    body_data.set_align(8);
    let bodies_id = module.declare_anonymous_data(false, false).map_err(error)?;
    module.define_data(bodies_id, &body_data).map_err(error)?;
    let mut schemas = Vec::new();
    for (&recipe, &(schema, count)) in recipes {
        schemas.extend(words(&[
            schema as u64,
            ids[recipe].as_u32() as u64,
            count as u64,
        ]));
    }
    let schemas_id = blob(module, schemas)?;
    let function_ids = blob(
        module,
        words(&ids.iter().map(|id| id.as_u32() as u64).collect::<Vec<_>>()),
    )?;
    let image = module
        .declare_data("kush_stage_image", Linkage::Export, false, false)
        .map_err(error)?;
    let mut image_data = DataDescription::new();
    image_data.set_align(8);
    image_data.define(
        words(&[
            bodies.len() as u64,
            recipes.len() as u64,
            0,
            0,
            ids.len() as u64,
            0,
        ])
        .into_boxed_slice(),
    );
    data_pointer(module, &mut image_data, 16, bodies_id);
    data_pointer(module, &mut image_data, 24, schemas_id);
    data_pointer(module, &mut image_data, 40, function_ids);
    module.define_data(image, &image_data).map_err(error)?;
    Ok(())
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod tests {
    use super::*;

    #[test]
    fn rejected_relocation_releases_the_unpublished_mapping() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("staging-relocation.c");
        let binary = scratch.path().join("staging-relocation");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }

static const unsigned char code[] = {0};
/* An eight-byte relocation cannot fit in the one-byte body. */
static const KushStageReloc reloc = {.kind = 0, .target_kind = 1};
static const KushStageBody body = {.size = sizeof(code), .code = code, .reloc_count = 1, .relocs = &reloc};
static const KushStageSchema schema = {0};
const KushStageImage kush_stage_image = {.body_count = 1, .schema_count = 1, .bodies = &body, .schemas = &schema};

static void *mapping;
static unsigned releases;
extern void *__real_mmap(void *, size_t, int, int, int, off_t);
extern int __real_munmap(void *, size_t);
void *__wrap_mmap(void *address, size_t size, int prot, int flags, int fd, off_t offset) {
    assert(size == KUSH_STAGE_LIMIT && prot == (PROT_READ | PROT_WRITE));
    mapping = __real_mmap(address, size, prot, flags, fd, offset);
    assert(mapping != MAP_FAILED);
    return mapping;
}
int __wrap_mprotect(void *address, size_t size, int prot) {
    (void)address; (void)size; (void)prot;
    assert(!"a failed relocation must never be published");
    return -1;
}
int __wrap_munmap(void *address, size_t size) {
    assert(address == mapping && size == KUSH_STAGE_LIMIT && releases++ == 0);
    return __real_munmap(address, size);
}
int main(void) {
    const unsigned char graph[16] = "KUSHCD01";
    uint64_t owner = 1;
    assert(kush_stage_compile(kush_bytes_from(graph, sizeof(graph)), &owner) == ENOTSUP);
    assert(owner == 0 && releases == 1 && kush_live_allocations == 0);
    return 0;
}
"#;
        fs::write(&source, format!("#define main kush_original_main\n{RUNTIME}\n{test}")).unwrap();
        let output = Command::new("cc")
            .args(["-std=c11", "-O2", "-DKUSH_STATS=1", "-DKUSH_FUSION_COUNT=0"])
            .args(["-Wl,--wrap=mmap,--wrap=mprotect,--wrap=munmap", "-o"])
            .arg(&binary)
            .arg(&source)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let output = Command::new(&binary).env_remove("KUSH_ALLOC_FAIL_AFTER").output().unwrap();
        assert!(output.status.success(), "{output:?}");
    }
}
