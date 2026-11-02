//! Restricted elaboration into the independent logical kernel, including the
//! checked boundary shared with the executable subset.
use crate::{
    Diagnostic, Span,
    ast::*,
    kernel::{Kernel, Scalar, Term},
    lexer::Kind,
    parse,
    resolve::{self, BindingId, BindingKind, Resolution},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, Diagnostic>;
#[derive(Debug)]
pub struct CheckedModule {
    pub resolution: Resolution,
    pub kernel: Kernel,
    pub definitions: Vec<String>,
}

/// The checked logical half of a program that also contains executable code.
/// Names map source bindings to the unique kernel globals they elaborate to.
#[derive(Debug)]
pub(crate) struct LogicalEnvironment {
    pub kernel: Kernel,
    pub names: BTreeMap<BindingId, String>,
    /// Admitted logical data families and their constructor globals.
    pub data: BTreeMap<BindingId, String>,
    pub constructors: BTreeMap<BindingId, String>,
    /// Number of constructors per admitted logical data family.
    pub constructor_counts: BTreeMap<BindingId, usize>,
    pub nullary: BTreeMap<BindingId, usize>,
    pub definitions: Vec<String>,
}

pub fn check(source: &str) -> Result<CheckedModule> {
    let module = parse(source)?;
    let resolution = resolve::resolve(&module)?;
    // Reject unimplemented features before admitting *any* source definitions.
    let mut selected = BTreeSet::new();
    let mut declarations = BTreeMap::new();
    for declaration in &module.items {
        if matches!(declaration.item.kind, ItemKind::Module(_)) {
            continue;
        }
        if matches!(
            declaration.item.kind,
            ItemKind::Trait { .. } | ItemKind::Impl { .. }
        ) {
            return Err(Diagnostic::new(
                declaration.item.span,
                "traits and impls are executable declarations; use the executable checker ('kush check/run' on a program)",
            ));
        }
        validate(declaration)?;
        let id = resolution.declarations[&declaration.item.span.start];
        selected.insert(id);
        declarations.insert(id, declaration);
    }
    let environment = check_selected(&resolution, &selected, &declarations, false)?;
    Ok(CheckedModule {
        resolution,
        kernel: environment.kernel,
        definitions: environment.definitions,
    })
}

/// Check every total function and type alias of a program through the logical
/// kernel. Executable (non-total) functions are left to the executable checker.
/// Dependencies are audited: a logical definition may only use other checked
/// logical definitions, never runtime/data declarations.
pub(crate) fn check_program(
    module: &Module,
    resolution: &Resolution,
) -> Result<LogicalEnvironment> {
    let executable_aliases = executable_alias_ids(module, resolution)?;
    let mut selected = BTreeSet::new();
    let mut declarations = BTreeMap::new();
    for declaration in &module.items {
        match &declaration.item.kind {
            ItemKind::Module(_)
            | ItemKind::Use(_)
            | ItemKind::Struct { .. }
            | ItemKind::Trait { .. }
            | ItemKind::Impl { .. }
            | ItemKind::GradeAlgebra(_)
            | ItemKind::Enum { total: false, .. } => continue,
            ItemKind::Function(f) if !f.total => continue,
            ItemKind::Function(_)
            | ItemKind::Alias { .. }
            | ItemKind::Enum { total: true, .. }
            | ItemKind::Prop { .. } => {}
        }
        let id = resolution.declarations[&declaration.item.span.start];
        if matches!(declaration.item.kind, ItemKind::Alias { .. })
            && executable_aliases.contains(&id)
        {
            continue;
        }
        validate(declaration)?;
        selected.insert(id);
        declarations.insert(id, declaration);
    }
    check_selected(resolution, &selected, &declarations, true)
}

/// Aliases whose right-hand side is outside the trusted logical fragment.
/// They are still checked for resolution and are elaborated by the executable
/// type checker, but they are *not* silently admitted as logical definitions:
/// a total logical function that depends on one still fails the dependency
/// audit, and an erased proof type that names one still fails elaboration.
///
/// Classification is syntactic and conservative. A cycle is routed through the
/// logical path so the kernel's existing cycle rejection reports it instead of
/// this pass guessing a meaning.
pub(crate) fn executable_alias_ids(
    module: &Module,
    resolution: &Resolution,
) -> Result<BTreeSet<BindingId>> {
    let mut aliases: BTreeMap<BindingId, (&[Generic], &Type)> = BTreeMap::new();
    for declaration in &module.items {
        if let ItemKind::Alias { generics, ty, .. } = &declaration.item.kind {
            let id = resolution.declarations[&declaration.item.span.start];
            aliases.insert(id, (generics.as_slice(), ty));
        }
    }
    detect_alias_cycles(&aliases, resolution)?;
    let data = logical_data_ids(module, resolution);
    let mut cache = BTreeMap::new();
    let mut runtime_capable = BTreeSet::new();
    for id in aliases.keys() {
        let logical = alias_is_logical(
            resolution,
            &data,
            &aliases,
            *id,
            &mut cache,
            &mut BTreeSet::new(),
        );
        if !logical {
            runtime_capable.insert(*id);
        }
    }
    // A runtime alias participates in the executable alias elaboration only if
    // a runtime declaration actually reaches it. Otherwise it stays on the
    // logical side of the boundary and must be a valid logical definition. This
    // keeps unused declarations from acquiring an unchecked runtime meaning.
    let mut reachable = runtime_alias_roots(module, resolution);
    let mut queue = reachable.iter().copied().collect::<Vec<_>>();
    while let Some(id) = queue.pop() {
        let Some((_, ty)) = aliases.get(&id) else {
            continue;
        };
        let mut used = BTreeSet::new();
        alias_refs_in_type(resolution, ty, &mut used);
        for used in used {
            if runtime_capable.contains(&used) && reachable.insert(used) {
                queue.push(used);
            }
        }
    }
    let executable = runtime_capable
        .into_iter()
        .filter(|id| {
            reachable.contains(id)
                || alias_is_structured(resolution, &aliases, *id, &mut BTreeSet::new())
        })
        .collect::<BTreeSet<_>>();
    for id in &executable {
        let (generics, ty) = aliases[id];
        crate::executable::validate_type_templates_for(resolution, generics, &[ty])?;
    }
    Ok(executable)
}

/// A runtime alias whose body contains actual runtime structure (arrays,
/// unions, containers, nominal data, borrows) is always elaborated by the
/// executable type checker, even if no current use reaches it. A plain alias to
/// a scalar is only an executable alias when runtime code uses it; otherwise it
/// remains a logical alias and must satisfy the kernel.
fn alias_is_structured(
    resolution: &Resolution,
    aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
    id: BindingId,
    visiting: &mut BTreeSet<BindingId>,
) -> bool {
    if !visiting.insert(id) {
        return true;
    }
    let result = structured_type(resolution, aliases, aliases[&id].1, visiting);
    visiting.remove(&id);
    result
}

fn structured_type(
    resolution: &Resolution,
    aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
    ty: &Type,
    visiting: &mut BTreeSet<BindingId>,
) -> bool {
    match &ty.kind {
        TypeKind::Array(_, _)
        | TypeKind::Slice(_)
        | TypeKind::Borrow { .. }
        | TypeKind::Tuple(_)
        | TypeKind::Binary { .. }
        | TypeKind::Graded { .. }
        | TypeKind::Predicate(_) => true,
        TypeKind::Named { arguments, .. } => {
            if arguments
                .iter()
                .any(|argument| structured_type(resolution, aliases, argument, visiting))
            {
                return true;
            }
            let Some(id) = resolution.reference(ty.span) else {
                return false;
            };
            let binding = &resolution.bindings[id];
            match binding.kind {
                BindingKind::Alias if aliases.contains_key(&id) => {
                    alias_is_structured(resolution, aliases, id, visiting)
                }
                BindingKind::Data | BindingKind::Constructor => true,
                BindingKind::Builtin => matches!(
                    binding.name.as_str(),
                    "Box" | "Vec" | "Bytes" | "Stdin" | "Stdout"
                ),
                _ => false,
            }
        }
        TypeKind::Function {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .any(|parameter| structured_type(resolution, aliases, &parameter.ty, visiting))
                || structured_type(resolution, aliases, result, visiting)
        }
        _ => false,
    }
}

/// Reject recursive type aliases explicitly. This covers both aliases that
/// participate in runtime types and aliases that would otherwise reach the
/// logical cycle check, so every cycle gets the same clear diagnostic.
fn detect_alias_cycles(
    aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
    resolution: &Resolution,
) -> Result<()> {
    fn visit(
        id: BindingId,
        aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
        resolution: &Resolution,
        state: &mut BTreeMap<BindingId, u8>,
    ) -> Result<()> {
        match state.get(&id).copied().unwrap_or(0) {
            1 => {
                return Err(Diagnostic::new(
                    resolution.bindings[id].span,
                    format!(
                        "cyclic type alias '{}' is not allowed; aliases are transparent and must elaborate to a finite type",
                        resolution.bindings[id].name
                    ),
                ));
            }
            2 => return Ok(()),
            _ => {}
        }
        state.insert(id, 1);
        let mut used = BTreeSet::new();
        alias_refs_in_type(resolution, aliases[&id].1, &mut used);
        for used in used {
            if aliases.contains_key(&used) {
                visit(used, aliases, resolution, state)?;
            }
        }
        state.insert(id, 2);
        Ok(())
    }
    let mut state = BTreeMap::new();
    for id in aliases.keys() {
        visit(*id, aliases, resolution, &mut state)?;
    }
    Ok(())
}

/// Aliases referenced from a runtime type position: executable function
/// signatures and annotations, and record/enum layouts. Aliases mentioned only
/// by logical definitions are deliberately excluded.
fn runtime_alias_roots(module: &Module, resolution: &Resolution) -> BTreeSet<BindingId> {
    let mut roots = BTreeSet::new();
    for declaration in &module.items {
        match &declaration.item.kind {
            ItemKind::Function(f) if !f.total => {
                for generic in &f.generics {
                    if let Some(bound) = &generic.bound {
                        alias_refs_in_type(resolution, bound, &mut roots);
                    }
                }
                for parameter in f.parameters.iter().filter(|p| !p.erased) {
                    alias_refs_in_type(resolution, &parameter.ty, &mut roots);
                }
                alias_refs_in_type(resolution, &f.result, &mut roots);
                if let Some(body) = &f.body {
                    alias_refs_in_block(resolution, body, &mut roots);
                }
            }
            ItemKind::Struct {
                generics, fields, ..
            } => {
                for generic in generics {
                    if let Some(bound) = &generic.bound {
                        alias_refs_in_type(resolution, bound, &mut roots);
                    }
                }
                for field in fields {
                    alias_refs_in_type(resolution, &field.ty, &mut roots);
                }
            }
            ItemKind::Enum {
                generics, variants, ..
            } => {
                for generic in generics {
                    if let Some(bound) = &generic.bound {
                        alias_refs_in_type(resolution, bound, &mut roots);
                    }
                }
                for variant in variants {
                    match &variant.payload {
                        Payload::Unit => {}
                        Payload::Tuple(types) => {
                            for ty in types {
                                alias_refs_in_type(resolution, ty, &mut roots);
                            }
                        }
                        Payload::Fields(fields) | Payload::Record(fields) => {
                            for field in fields {
                                alias_refs_in_type(resolution, &field.ty, &mut roots);
                            }
                        }
                    }
                    if let Some(result) = &variant.result {
                        alias_refs_in_type(resolution, result, &mut roots);
                    }
                }
            }
            _ => {}
        }
    }
    roots
}

fn alias_refs_in_type(resolution: &Resolution, ty: &Type, out: &mut BTreeSet<BindingId>) {
    match &ty.kind {
        TypeKind::Named { arguments, .. } => {
            if let Some(id) = resolution.reference(ty.span) {
                out.insert(id);
            }
            for argument in arguments {
                alias_refs_in_type(resolution, argument, out);
            }
        }
        TypeKind::Tuple(items) => {
            for item in items {
                alias_refs_in_type(resolution, item, out);
            }
        }
        TypeKind::Slice(inner)
        | TypeKind::Borrow { inner, .. }
        | TypeKind::Graded { inner, .. } => alias_refs_in_type(resolution, inner, out),
        TypeKind::Array(element, length) => {
            alias_refs_in_type(resolution, element, out);
            alias_refs_in_type(resolution, length, out);
        }
        TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                alias_refs_in_type(resolution, &parameter.ty, out);
            }
            alias_refs_in_type(resolution, result, out);
            for effect in effects {
                alias_refs_in_type(resolution, effect, out);
            }
        }
        TypeKind::Binary { left, right, .. } => {
            alias_refs_in_type(resolution, left, out);
            alias_refs_in_type(resolution, right, out);
        }
        TypeKind::Predicate(expr) => alias_refs_in_expr(resolution, expr, out),
        TypeKind::Integer(_) | TypeKind::Bool(_) | TypeKind::Lifetime(_) | TypeKind::SelfType => {}
    }
}

fn alias_refs_in_block(resolution: &Resolution, block: &Block, out: &mut BTreeSet<BindingId>) {
    for statement in &block.statements {
        match statement {
            Statement::Let {
                pattern, ty, value, ..
            } => {
                if let Some(ty) = ty {
                    alias_refs_in_type(resolution, ty, out);
                }
                alias_refs_in_pattern(resolution, pattern, out);
                alias_refs_in_expr(resolution, value, out);
            }
            Statement::Expr(expr) => alias_refs_in_expr(resolution, expr, out),
        }
    }
    if let Some(tail) = &block.tail {
        alias_refs_in_expr(resolution, tail, out);
    }
}

fn alias_refs_in_expr(resolution: &Resolution, expr: &Expr, out: &mut BTreeSet<BindingId>) {
    match &expr.kind {
        ExprKind::Specialize { callee, arguments } => {
            alias_refs_in_expr(resolution, callee, out);
            for argument in arguments {
                alias_refs_in_type(resolution, argument, out);
            }
        }
        ExprKind::Tuple(values) | ExprKind::Array(values) => {
            for value in values {
                alias_refs_in_expr(resolution, value, out);
            }
        }
        ExprKind::Block(block) | ExprKind::Loop(block) => {
            alias_refs_in_block(resolution, block, out)
        }
        ExprKind::Unary { operand, .. } | ExprKind::Try(operand) => {
            alias_refs_in_expr(resolution, operand, out)
        }
        ExprKind::Binary { left, right, .. } => {
            alias_refs_in_expr(resolution, left, out);
            alias_refs_in_expr(resolution, right, out);
        }
        ExprKind::Call { callee, arguments } => {
            alias_refs_in_expr(resolution, callee, out);
            for argument in arguments {
                alias_refs_in_expr(resolution, argument, out);
            }
        }
        ExprKind::Field { value, .. } => alias_refs_in_expr(resolution, value, out),
        ExprKind::Index { value, index } => {
            alias_refs_in_expr(resolution, value, out);
            alias_refs_in_expr(resolution, index, out);
        }
        ExprKind::Slice { value, start, end } => {
            alias_refs_in_expr(resolution, value, out);
            if let Some(start) = start {
                alias_refs_in_expr(resolution, start, out);
            }
            if let Some(end) = end {
                alias_refs_in_expr(resolution, end, out);
            }
        }
        ExprKind::Return(Some(value)) | ExprKind::Break(Some(value)) => {
            alias_refs_in_expr(resolution, value, out)
        }
        ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            alias_refs_in_expr(resolution, condition, out);
            alias_refs_in_block(resolution, then, out);
            if let Some(otherwise) = otherwise {
                alias_refs_in_expr(resolution, otherwise, out);
            }
        }
        ExprKind::Match { value, arms } => {
            alias_refs_in_expr(resolution, value, out);
            for arm in arms {
                alias_refs_in_pattern(resolution, &arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    alias_refs_in_expr(resolution, guard, out);
                }
                alias_refs_in_expr(resolution, &arm.body, out);
            }
        }
        ExprKind::While { condition, body } => {
            alias_refs_in_expr(resolution, condition, out);
            alias_refs_in_block(resolution, body, out);
        }
        ExprKind::Record { fields, .. } => {
            for (_, value) in fields {
                alias_refs_in_expr(resolution, value, out);
            }
        }
        _ => {}
    }
}

fn alias_refs_in_pattern(
    resolution: &Resolution,
    pattern: &Pattern,
    out: &mut BTreeSet<BindingId>,
) {
    match &pattern.kind {
        PatternKind::Type { ty, inner } => {
            alias_refs_in_type(resolution, ty, out);
            alias_refs_in_pattern(resolution, inner, out);
        }
        PatternKind::Tuple(patterns) | PatternKind::Slice(patterns) => {
            for pattern in patterns {
                alias_refs_in_pattern(resolution, pattern, out);
            }
        }
        PatternKind::Constructor { fields, .. } => {
            for field in fields {
                alias_refs_in_pattern(resolution, field, out);
            }
        }
        PatternKind::Record { fields, .. } => {
            for (_, field) in fields {
                alias_refs_in_pattern(resolution, field, out);
            }
        }
        PatternKind::Or(alternatives) => {
            for alternative in alternatives {
                alias_refs_in_pattern(resolution, alternative, out);
            }
        }
        _ => {}
    }
}

fn alias_is_logical(
    resolution: &Resolution,
    data: &BTreeSet<BindingId>,
    aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
    id: BindingId,
    cache: &mut BTreeMap<BindingId, bool>,
    active: &mut BTreeSet<BindingId>,
) -> bool {
    if let Some(cached) = cache.get(&id) {
        return *cached;
    }
    if !active.insert(id) {
        // Cycles are rejected by the kernel (logical) or by executable alias
        // elaboration. Treating a revisited alias as logical keeps every such
        // cycle on the checked side instead of silently erasing it.
        return true;
    }
    let (generics, ty) = aliases[&id];
    let generic_ok = generics.iter().all(|generic| match &generic.bound {
        None => true,
        // The bound is itself a logical type. This keeps the fragment
        // conservative while allowing proposition and function-type bounds
        // such as `P: fn(x: T) -> Prop`.
        Some(bound) => logical_type(resolution, data, aliases, bound, cache, active),
    });
    let logical = generic_ok && logical_type(resolution, data, aliases, ty, cache, active);
    active.remove(&id);
    cache.insert(id, logical);
    logical
}

fn logical_type(
    resolution: &Resolution,
    data: &BTreeSet<BindingId>,
    aliases: &BTreeMap<BindingId, (&[Generic], &Type)>,
    ty: &Type,
    cache: &mut BTreeMap<BindingId, bool>,
    active: &mut BTreeSet<BindingId>,
) -> bool {
    match &ty.kind {
        TypeKind::Named { arguments, .. } => {
            let Some(id) = resolution.reference(ty.span) else {
                return false;
            };
            let binding = &resolution.bindings[id];
            let head = match binding.kind {
                BindingKind::Builtin => {
                    matches!(
                        binding.name.as_str(),
                        "Type" | "Nat" | "Eq" | "Prop" | "i64" | "Bool" | "Unit"
                    )
                }
                BindingKind::Generic => true,
                BindingKind::Alias if aliases.contains_key(&id) => {
                    alias_is_logical(resolution, data, aliases, id, cache, active)
                }
                BindingKind::Data => data.contains(&id),
                BindingKind::Constructor => {
                    binding.owner.is_some_and(|owner| data.contains(&owner))
                }
                _ => false,
            };
            head && arguments
                .iter()
                .all(|argument| logical_type(resolution, data, aliases, argument, cache, active))
        }
        TypeKind::Integer(_) => true,
        TypeKind::Bool(_) => true,
        TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            effects.is_empty()
                && parameters.iter().all(|parameter| {
                    logical_type(resolution, data, aliases, &parameter.ty, cache, active)
                })
                && logical_type(resolution, data, aliases, result, cache, active)
        }
        _ => false,
    }
}

/// Binding IDs of `total enum` declarations: the logical data currently
/// admitted by the kernel.
fn logical_data_ids(module: &Module, resolution: &Resolution) -> BTreeSet<BindingId> {
    module
        .items
        .iter()
        .filter_map(|declaration| match &declaration.item.kind {
            ItemKind::Enum { total: true, .. } | ItemKind::Prop { .. } => resolution
                .declarations
                .get(&declaration.item.span.start)
                .copied(),
            _ => None,
        })
        .collect()
}

/// Reject declarations that are not part of the trusted logical fragment.
fn validate(declaration: &Declaration) -> Result<()> {
    if !declaration.attributes.is_empty() {
        return Err(Diagnostic::new(
            declaration.attributes[0].span,
            "attributes/resource contracts are not supported by logical checking yet",
        ));
    }
    match &declaration.item.kind {
        ItemKind::Module(_) => Ok(()),
        ItemKind::Function(f) if !f.total => Err(Diagnostic::new(
            declaration.item.span,
            "only total fn definitions are supported by logical checking; executable functions are not proof evidence",
        )),
        ItemKind::Function(f) if f.body.is_none() => Err(Diagnostic::new(
            declaration.item.span,
            "logical definitions require a body; unchecked axioms are not supported",
        )),
        ItemKind::Function(f) if !f.effects.is_empty() => Err(Diagnostic::new(
            declaration.item.span,
            "logical definitions require an empty effect row",
        )),
        ItemKind::Function(_)
        | ItemKind::Alias { .. }
        | ItemKind::Enum { total: true, .. }
        | ItemKind::Prop { .. } => Ok(()),
        ItemKind::Enum { total: false, .. } | ItemKind::Struct { .. } => Err(Diagnostic::new(
            declaration.item.span,
            "ordinary owning data declarations require positivity and executable elimination rules; only 'total enum' declarations enter the logical kernel",
        )),
        ItemKind::Trait { .. } | ItemKind::Impl { .. } => Err(Diagnostic::new(
            declaration.item.span,
            "traits and impls are executable declarations; only total functions, type aliases, and total logical data declarations enter the logical kernel",
        )),
        _ => Err(Diagnostic::new(
            declaration.item.span,
            "logical checking supports total functions, type aliases, and total logical data declarations only",
        )),
    }
}

fn check_selected(
    resolution: &Resolution,
    selected: &BTreeSet<BindingId>,
    declarations: &BTreeMap<BindingId, &Declaration>,
    unique_names: bool,
) -> Result<LogicalEnvironment> {
    if selected.len() > 256 {
        return Err(Diagnostic::new(
            Span::default(),
            "logical module exceeds the initial 256-definition limit",
        ));
    }
    // Total logical data declarations are themselves checked by the kernel.
    // Their constructors are owned bindings, not separate source declarations.
    let data_ids = selected
        .iter()
        .copied()
        .filter(|id| {
            matches!(
                declarations.get(id).map(|d| &d.item.kind),
                Some(ItemKind::Enum { total: true, .. }) | Some(ItemKind::Prop { .. })
            )
        })
        .collect::<BTreeSet<_>>();
    let is_logical_constructor = |dependency: BindingId| {
        resolution.bindings[dependency].kind == BindingKind::Constructor
            && resolution.bindings[dependency]
                .owner
                .is_some_and(|owner| data_ids.contains(&owner))
    };
    // Audit dependencies instead of silently dropping non-logical ones.
    for id in selected {
        let binding = &resolution.bindings[*id];
        for dependency in resolution.dependencies.get(id).into_iter().flatten() {
            if selected.contains(dependency) || is_logical_constructor(*dependency) {
                continue;
            }
            let target = &resolution.bindings[*dependency];
            let category = match target.kind {
                BindingKind::Data | BindingKind::Constructor => "data declaration",
                BindingKind::Function => "executable or effectful function",
                BindingKind::Alias => "unchecked alias",
                _ => "runtime declaration",
            };
            return Err(Diagnostic::new(
                binding.span,
                format!(
                    "logical definition '{}' depends on {category} '{}', which is not checked by the logical kernel; runtime values cannot enter erased proofs",
                    binding.name, target.name
                ),
            ));
        }
    }
    // Deterministic Kahn ordering, accepting forward references but no
    // recursion. A data declaration's self-dependency is its own recursive
    // occurrence, which the positivity and elimination checks handle; any
    // other cycle (including mutual data recursion) remains an error.
    let depends = |id: BindingId, dependency: BindingId, done: &BTreeSet<BindingId>| {
        done.contains(&dependency) || (data_ids.contains(&id) && dependency == id)
    };
    let mut remaining = selected.clone();
    let mut done = BTreeSet::new();
    let mut order = Vec::new();
    while !remaining.is_empty() {
        let next = remaining.iter().copied().find(|id| {
            resolution
                .dependencies
                .get(id)
                .is_none_or(|deps| deps.iter().all(|dep| depends(*id, *dep, &done)))
        });
        let Some(id) = next else {
            let id = *remaining.first().unwrap();
            return Err(Diagnostic::new(
                resolution.bindings[id].span,
                "cyclic logical definitions are not supported; mutual data recursion and total recursion need a checked termination argument",
            ));
        };
        remaining.remove(&id);
        done.insert(id);
        order.push(id);
    }
    let nullary = selected
        .iter()
        .filter_map(|id| match declarations.get(id).map(|d| &d.item.kind) {
            Some(ItemKind::Function(f)) if f.parameters.is_empty() => Some((*id, f.generics.len())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let names = assign_names(resolution, selected, unique_names);
    let mut data = BTreeMap::new();
    let mut constructors = BTreeMap::new();
    let mut constructor_counts = BTreeMap::new();
    for id in &data_ids {
        data.insert(*id, names[id].clone());
        let mut count = 0;
        for (constructor, binding) in resolution.bindings.iter().enumerate() {
            if binding.kind == BindingKind::Constructor && binding.owner == Some(*id) {
                let short = binding
                    .name
                    .rsplit('.')
                    .next()
                    .unwrap_or(binding.name.as_str());
                constructors.insert(constructor, format!("{}::{short}", names[id]));
                count += 1;
            }
        }
        constructor_counts.insert(*id, count);
    }
    let mut kernel = Kernel::default();
    let mut definitions = Vec::new();
    for id in order {
        let declaration = declarations[&id];
        let mut elaborator = Elaborator {
            resolution,
            kernel: &kernel,
            names: &names,
            data: &data,
            constructors: &constructors,
            constructor_counts: &constructor_counts,
            nullary: &nullary,
            locals: Vec::new(),
            local_types: Vec::new(),
            depth: 0,
        };
        let name = names[&id].clone();
        match &declaration.item.kind {
            ItemKind::Enum {
                total: true,
                generics,
                variants,
                ..
            } => {
                debug_assert_eq!(name, data[&id]);
                let spec = elaborator.data(id, &name, generics, variants, false)?;
                kernel.define_indexed_data(spec).map_err(|e| {
                    Diagnostic::new(
                        declaration.item.span,
                        format!("in logical data '{name}': {e}"),
                    )
                })?;
                definitions.push(name);
                continue;
            }
            ItemKind::Prop {
                generics, variants, ..
            } => {
                debug_assert_eq!(name, data[&id]);
                let spec = elaborator.data(id, &name, generics, variants, true)?;
                kernel.define_indexed_data(spec).map_err(|e| {
                    Diagnostic::new(
                        declaration.item.span,
                        format!("in proposition '{name}': {e}"),
                    )
                })?;
                definitions.push(name);
                continue;
            }
            ItemKind::Enum { total: false, .. } => unreachable!("non-total enums are not selected"),
            _ => {}
        }
        let (ty, value) = match &declaration.item.kind {
            ItemKind::Function(f) => elaborator.function(f)?,
            ItemKind::Alias { generics, ty, .. } => {
                let domains = elaborator.generics(generics)?;
                let mut value = elaborator.ty(ty)?;
                for domain in domains.iter().rev() {
                    value = Term::lam(domain.clone(), value);
                }
                let inferred = kernel
                    .infer_closed(&value)
                    .map_err(|e| Diagnostic::new(ty.span, e.to_string()))?;
                let mut result = &inferred;
                for _ in &domains {
                    let Term::Pi { codomain, .. } = result else {
                        return Err(Diagnostic::new(ty.span, "invalid alias binders"));
                    };
                    result = codomain;
                }
                if !matches!(result, Term::Universe(_) | Term::Prop) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "a type alias must return a type or proposition, not a runtime value",
                    ));
                }
                (inferred, value)
            }
            _ => unreachable!(),
        };
        kernel
            .define(name.clone(), ty, value)
            .map_err(|e| Diagnostic::new(declaration.item.span, format!("in '{name}': {e}")))?;
        definitions.push(name);
    }
    Ok(LogicalEnvironment {
        kernel,
        names,
        data,
        constructors,
        constructor_counts,
        nullary,
        definitions,
    })
}

fn assign_names(
    resolution: &Resolution,
    selected: &BTreeSet<BindingId>,
    unique_names: bool,
) -> BTreeMap<BindingId, String> {
    if !unique_names {
        return selected
            .iter()
            .map(|id| (*id, resolution.bindings[*id].name.clone()))
            .collect();
    }
    let mut counts = BTreeMap::new();
    for id in selected {
        *counts
            .entry(resolution.bindings[*id].name.clone())
            .or_insert(0usize) += 1;
    }
    let mut used = BTreeSet::new();
    let mut names = BTreeMap::new();
    for id in selected {
        let binding = &resolution.bindings[*id];
        let base = &binding.name;
        let mut name = if counts[base] == 1 {
            base.clone()
        } else {
            let path = resolution
                .unit_of
                .get(id)
                .and_then(|unit| resolution.units.get(*unit))
                .filter(|path| !path.is_empty());
            match path {
                Some(path) => format!("{}::{}", path.join("."), base),
                None => format!("{base}#{id}"),
            }
        };
        let mut counter = 1;
        while used.contains(&name) {
            name = format!("{base}#{id}_{counter}");
            counter += 1;
        }
        used.insert(name.clone());
        names.insert(*id, name);
    }
    names
}

struct Elaborator<'a> {
    resolution: &'a Resolution,
    kernel: &'a Kernel,
    names: &'a BTreeMap<BindingId, String>,
    data: &'a BTreeMap<BindingId, String>,
    constructors: &'a BTreeMap<BindingId, String>,
    constructor_counts: &'a BTreeMap<BindingId, usize>,
    nullary: &'a BTreeMap<BindingId, usize>,
    locals: Vec<Option<BindingId>>,
    /// Kernel type of every binder in `locals`, in the same order. These are
    /// hypothesis types, so a symbolic runtime scalar `n : i64` contributes
    /// `Scalar(I64)` and an erased proof contributes its proposition.
    local_types: Vec<Term>,
    depth: usize,
}
impl Elaborator<'_> {
    fn nested<T>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                span,
                "elaboration nesting budget exceeded (128)",
            ));
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    /// Introduce the binder recorded at `span` with its kernel type.
    fn bind_ty(&mut self, span: Span, ty: Term) -> Result<()> {
        let id = self
            .resolution
            .binder(span)
            .ok_or_else(|| Diagnostic::new(span, "internal error: unresolved binder"))?;
        self.locals.push(Some(id));
        self.local_types.push(ty);
        Ok(())
    }
    /// Introduce an anonymous binder, such as an unnamed constructor field.
    fn bind_anonymous(&mut self, ty: Term) {
        self.locals.push(None);
        self.local_types.push(ty);
    }
    /// Expected type of the next argument of a function-valued kernel term, if
    /// it is a function. This is a checked inference in the current open context.
    fn application_domain(&mut self, term: &Term) -> Result<Option<Term>> {
        let ty = match self.kernel.infer_open(term, &self.local_types) {
            Ok(ty) => ty,
            Err(_) => return Ok(None),
        };
        Ok(match ty {
            Term::Pi { domain, .. } => Some(*domain),
            _ => None,
        })
    }
    fn reference(&self, span: Span) -> Result<Term> {
        let id = self.resolution.reference(span).ok_or_else(|| {
            Diagnostic::new(
                span,
                "dependent member projection is not supported by logical checking yet",
            )
        })?;
        if let Some(index) = self
            .locals
            .iter()
            .rev()
            .position(|local| *local == Some(id))
        {
            // `Unit` has one value. Encoding an admitted Unit hypothesis by its
            // canonical literal is a checked singleton encoding, not an
            // observation of runtime state.
            let position = self.local_types.len() - 1 - index;
            if matches!(
                self.local_types.get(position),
                Some(Term::Scalar(Scalar::Unit))
            ) || self.local_types.get(position).and_then(|ty| {
                self.kernel
                    .scalar_open(ty, &self.local_types[..position])
                    .ok()
                    .flatten()
            }) == Some(Scalar::Unit)
            {
                return Ok(Term::unit());
            }
            return Ok(Term::Var(index));
        }
        let binding = &self.resolution.bindings[id];
        match binding.kind {
            BindingKind::Function | BindingKind::Alias => self
                .names
                .get(&id)
                .map(|name| Term::Global(name.clone()))
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "'{}' is not a checked logical definition; runtime values and executable functions cannot enter erased proofs",
                            binding.name
                        ),
                    )
                }),
            BindingKind::Builtin => match binding.name.as_str() {
                "Type" => Ok(Term::Universe(0)),
                "Prop" => Ok(Term::Prop),
                "Nat" => Ok(Term::Nat),
                "i64" => Ok(Term::i64_type()),
                "Bool" => Ok(Term::bool_type()),
                "Unit" => Ok(Term::unit_type()),
                "Nat.zero" => Ok(Term::Zero),
                "Nat.succ" => Ok(Term::lam(Term::Nat, Term::succ(Term::Var(0)))),
                "Eq" => Ok(Term::lam(
                    Term::Universe(0),
                    Term::lam(
                        Term::Var(0),
                        Term::lam(
                            Term::Var(1),
                            Term::eq(Term::Var(2), Term::Var(1), Term::Var(0)),
                        ),
                    ),
                )),
                "refl" => Ok(Term::lam(
                    Term::Universe(0),
                    Term::lam(Term::Var(0), Term::refl(Term::Var(1), Term::Var(0))),
                )),
                "Nat.induct" | "Eq.transport" | "Eq.elim" | "Data.elim" => Err(Diagnostic::new(
                    span,
                    "logical eliminators must be fully applied in a call",
                )),
                _ => Err(Diagnostic::new(
                    span,
                    format!(
                        "'{}' is not supported by the logical subset yet",
                        binding.name
                    ),
                )),
            },
            BindingKind::Data => self
                .data
                .get(&id)
                .map(|name| Term::Global(name.clone()))
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "data declaration '{}' is not a checked total logical data type; owning runtime data cannot enter erased proofs",
                            binding.name
                        ),
                    )
                }),
            BindingKind::Constructor => self
                .constructors
                .get(&id)
                .map(|name| Term::Global(name.clone()))
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "constructor '{}' belongs to runtime data, which cannot enter erased proofs; only constructors of a 'total enum' are logical evidence",
                            binding.name
                        ),
                    )
                }),
            BindingKind::Generic
            | BindingKind::Parameter
            | BindingKind::Local
            | BindingKind::Trait
            | BindingKind::GradeAlgebra => Err(Diagnostic::new(
                span,
                format!(
                    "runtime or generic binding '{}' cannot appear in an erased logical term; only checked logical definitions and erased logical parameters are relevant",
                    binding.name
                ),
            )),
        }
    }
    fn natural(value: &str, span: Span) -> Result<Term> {
        value
            .parse()
            .map(Term::natural)
            .map_err(|e: crate::natural::Error| Diagnostic::new(span, e.to_string()))
    }
    fn generics(&mut self, generics: &[Generic]) -> Result<Vec<Term>> {
        let mut domains = Vec::new();
        for generic in generics {
            if let Some(excludes) = &generic.excludes {
                return Err(Diagnostic::new(
                    excludes.span,
                    "logical declarations cannot carry effect-exclusion constraints; bind '<e: Effects - alloc>' only on an executable function or method effect row",
                ));
            }
            let domain = match &generic.bound {
                Some(bound) => self.ty(bound)?,
                None => Term::Universe(0),
            };
            domains.push(domain.clone());
            self.bind_ty(generic.span, domain)?;
        }
        Ok(domains)
    }
    fn function(&mut self, f: &Function) -> Result<(Term, Term)> {
        let mut domains = self.generics(&f.generics)?;
        for parameter in &f.parameters {
            let domain = self.ty(&parameter.ty)?;
            domains.push(domain.clone());
            self.bind_ty(parameter.span, domain)?;
        }
        let mut ty = self.ty(&f.result)?;
        let mut value = self.block(f.body.as_ref().expect("validated body"))?;
        for domain in domains.into_iter().rev() {
            ty = Term::pi(domain.clone(), ty);
            value = Term::lam(domain, value);
        }
        Ok((ty, value))
    }
    fn constructor_name(&self, owner: BindingId, variant: &str) -> Option<String> {
        self.constructors.iter().find_map(|(id, name)| {
            let binding = &self.resolution.bindings[*id];
            (binding.owner == Some(owner) && binding.name.rsplit('.').next() == Some(variant))
                .then(|| name.clone())
        })
    }
    /// Bind a named constructor field. The resolver recorded the binder at the
    /// field's span; the kernel telescope order is params, constructor locals,
    /// then fields.
    fn bind_field(&mut self, span: Span, ty: Term) -> Result<()> {
        let id = self
            .resolution
            .binder(span)
            .ok_or_else(|| Diagnostic::new(span, "internal error: unresolved constructor field"))?;
        self.locals.push(Some(id));
        self.local_types.push(ty);
        Ok(())
    }
    /// Elaborate a field of a logical data declaration. A direct recursive
    /// occurrence of the family is built with its declared index carriers, so a
    /// literal such as `T<0>` is read as `i64` when the family is indexed by
    /// `i64` even before the family is admitted to the kernel.
    fn data_field(
        &mut self,
        id: BindingId,
        name: &str,
        arity: usize,
        carriers: &[Option<Term>],
        ty: &Type,
    ) -> Result<Term> {
        if let TypeKind::Named { arguments, .. } = &ty.kind
            && self.resolution.reference(ty.span) == Some(id)
            && arguments.len() == arity
        {
            let mut term = Term::Global(name.to_owned());
            for (argument, carrier) in arguments.iter().zip(carriers) {
                term = Term::app(term, self.ty_expected(argument, carrier.as_ref())?);
            }
            return Ok(term);
        }
        self.ty(ty)
    }
    /// Elaborate a `total enum` or `prop` into the kernel's positive data
    /// specification. Every declaration generic becomes a kernel index
    /// parameter; constructors add their own local binders and fields, and
    /// return the declared family at their result indices.
    fn data(
        &mut self,
        id: BindingId,
        name: &str,
        generics: &[Generic],
        variants: &[Variant],
        prop: bool,
    ) -> Result<crate::kernel::IndexedDataSpec> {
        let param_base = self.locals.len();
        let params = self.generics(generics)?;
        let arity = generics.len();
        // The declared carrier of each family index, when it is an admitted
        // machine scalar. Constructor result indices use it to interpret
        // literals such as `IsZeroI<0>` as `i64` rather than mathematical `Nat`.
        let mut param_carriers = Vec::with_capacity(arity);
        for (index, param) in params.iter().enumerate() {
            let context = self.local_types[..param_base + index].to_vec();
            let scalar = self.kernel.scalar_open(param, &context).unwrap_or(None);
            param_carriers.push(scalar.map(Term::Scalar));
        }
        let mut constructors = Vec::with_capacity(variants.len());
        for variant in variants {
            let base = self.locals.len();
            let locals = self.generics(&variant.locals)?;
            let mut fields = Vec::new();
            match &variant.payload {
                Payload::Unit => {}
                Payload::Tuple(types) => {
                    for ty in types {
                        let field = self.data_field(id, name, arity, &param_carriers, ty)?;
                        fields.push(field.clone());
                        // Later field types and result indices live under the
                        // kernel's field binders. Unnamed fields are anonymous.
                        self.bind_anonymous(field);
                    }
                }
                Payload::Fields(named) => {
                    for field in named {
                        let ty = self.data_field(id, name, arity, &param_carriers, &field.ty)?;
                        fields.push(ty.clone());
                        self.bind_field(field.span, ty)?;
                    }
                }
                Payload::Record(_) => {
                    return Err(Diagnostic::new(
                        variant.span,
                        "logical data constructors require unit, tuple, or named tuple fields; record payloads belong to runtime enums",
                    ));
                }
            }
            let constructor = self.constructor_name(id, &variant.name).ok_or_else(|| {
                Diagnostic::new(
                    variant.span,
                    "internal error: unresolved logical data constructor",
                )
            })?;
            let result = match &variant.result {
                Some(ty) => {
                    let TypeKind::Named { arguments, .. } = &ty.kind else {
                        return Err(Diagnostic::new(
                            ty.span,
                            "a constructor result must be the declared data family or proposition applied to its index arguments",
                        ));
                    };
                    let target = self.resolution.reference(ty.span).ok_or_else(|| {
                        Diagnostic::new(ty.span, "internal error: unresolved data family")
                    })?;
                    if target != id {
                        return Err(Diagnostic::new(
                            ty.span,
                            "a constructor result must name its own declared total data family or proposition",
                        ));
                    }
                    if arguments.len() != arity {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "constructor result for '{}' expects {arity} index arguments, found {}",
                                variant.name,
                                arguments.len()
                            ),
                        ));
                    }
                    let mut result = Vec::with_capacity(arguments.len());
                    for (index, argument) in arguments.iter().enumerate() {
                        result.push(self.ty_expected(argument, param_carriers[index].as_ref())?);
                    }
                    result
                }
                None => {
                    let depth = self.locals.len();
                    (0..arity)
                        .map(|index| Term::Var(depth - 1 - (param_base + index)))
                        .collect()
                }
            };
            self.locals.truncate(base);
            self.local_types.truncate(base);
            constructors.push(crate::kernel::IndexedConstructorSpec {
                name: constructor,
                locals,
                fields,
                result,
            });
        }
        Ok(crate::kernel::IndexedDataSpec {
            name: name.to_owned(),
            params,
            constructors,
            prop,
        })
    }
    /// The machine carrier an expected kernel type denotes, if any. A literal
    /// `Scalar` term needs no context; aliases and other forms are normalized in
    /// the current checked context.
    fn expected_scalar(&self, expected: Option<&Term>) -> Option<Scalar> {
        let expected = expected?;
        if let Term::Scalar(scalar) = expected {
            return Some(*scalar);
        }
        self.kernel
            .scalar_open(expected, &self.local_types)
            .ok()
            .flatten()
    }
    fn machine_i64(text: &str, span: Span) -> Result<Term> {
        text.parse::<i64>()
            .map(Term::i64)
            .map_err(|_| Diagnostic::new(span, "machine integer literal is outside the i64 range"))
    }
    /// The machine carrier a data family's index parameter denotes, if any.
    /// Parameters that depend on earlier parameters are not closed and are
    /// conservatively treated as non-scalar.
    fn data_param_carrier(&self, param: &Term) -> Option<Scalar> {
        if let Term::Scalar(scalar) = param {
            return Some(*scalar);
        }
        self.kernel.scalar_open(param, &[]).ok().flatten()
    }
    fn ty(&mut self, ty: &Type) -> Result<Term> {
        self.ty_expected(ty, None)
    }
    /// Elaborate a type or index. `expected` comes from a checked function
    /// domain (for example `refl`'s carrier or a data family's index carrier),
    /// so a literal such as `0` can be read as `i64` in `Eq<i64, 0, 0>` while
    /// remaining the mathematical natural `0` elsewhere.
    fn ty_expected(&mut self, ty: &Type, expected: Option<&Term>) -> Result<Term> {
        self.nested(ty.span, |e| match &ty.kind {
            TypeKind::Named { arguments, .. } => {
                let id = e.resolution.reference(ty.span).ok_or_else(|| Diagnostic::new(ty.span, "internal error: unresolved type"))?;
                let binding = &e.resolution.bindings[id];
                if binding.kind == BindingKind::Builtin {
                    match binding.name.as_str() {
                        "Type" if !arguments.is_empty() => {
                            if let [Node { kind: TypeKind::Integer(level), .. }] = arguments.as_slice() {
                                let level = level.parse::<u32>().ok().filter(|level| *level <= 255)
                                    .ok_or_else(|| Diagnostic::new(ty.span, "surface universe levels must be in 0..255"))?;
                                return Ok(Term::Universe(level));
                            }
                            return Err(Diagnostic::new(ty.span, "Type expects one literal universe level"));
                        }
                        // Equality is built directly so the carrier may be a
                        // Type at any level, a proposition, or an admitted
                        // machine carrier. The kernel checks the carrier's sort.
                        "Eq" => {
                            let [carrier, left, right] = arguments.as_slice() else {
                                return Err(Diagnostic::new(
                                    ty.span,
                                    "Eq expects a carrier type and two values",
                                ));
                            };
                            let carrier = e.ty(carrier)?;
                            return Ok(Term::eq(
                                carrier.clone(),
                                e.ty_expected(left, Some(&carrier))?,
                                e.ty_expected(right, Some(&carrier))?,
                            ));
                        }
                        _ => {}
                    }
                }
                let mut term = e.reference(ty.span)?;
                // A fully applied data family's parameter carriers are known
                // from its admitted declaration. This avoids needing the whole
                // surrounding context to be admitted while the current family
                // is still being defined, and keeps literals correctly typed
                // after a recursive field.
                if let Term::Global(name) = &term
                    && let Some(info) = e.kernel.data(name).cloned()
                    && info.params.len() == arguments.len()
                {
                    for (index, argument) in arguments.iter().enumerate() {
                        let carrier = e.data_param_carrier(&info.params[index]);
                        let value =
                            e.ty_expected(argument, carrier.map(Term::Scalar).as_ref())?;
                        term = Term::app(term, value);
                    }
                    return Ok(term);
                }
                for argument in arguments {
                    let domain = e.application_domain(&term)?;
                    let value = e.ty_expected(argument, domain.as_ref())?;
                    term = Term::app(term, value);
                }
                Ok(term)
            }
            TypeKind::Integer(value) => match e.expected_scalar(expected) {
                Some(Scalar::I64) => Self::machine_i64(value, ty.span),
                Some(Scalar::Bool | Scalar::Unit) => Err(Diagnostic::new(
                    ty.span,
                    "a machine integer literal cannot index a Bool or Unit carrier",
                )),
                None => Self::natural(value, ty.span),
            },
            TypeKind::Bool(value) => Ok(Term::boolean(*value)),
            TypeKind::Tuple(items) if items.is_empty() => Ok(Term::unit()),
            TypeKind::Function { parameters, result, effects, .. } => {
                if !effects.is_empty() {
                    return Err(Diagnostic::new(ty.span, "logical function types require an empty effect row"));
                }
                if parameters.is_empty() {
                    return Err(Diagnostic::new(ty.span, "nullary function-type syntax is not supported by logical checking yet"));
                }
                let old_len = e.locals.len();
                let mut domains = Vec::new();
                for parameter in parameters {
                    let domain = e.ty(&parameter.ty)?;
                    domains.push(domain.clone());
                    if parameter.name.is_some() { e.bind_ty(parameter.span, domain)?; }
                    else { e.bind_anonymous(domain); }
                }
                let mut term = e.ty(result)?;
                for domain in domains.into_iter().rev() { term = Term::pi(domain, term); }
                e.locals.truncate(old_len);
                e.local_types.truncate(old_len);
                Ok(term)
            }
            _ => Err(Diagnostic::new(ty.span, "this type form is not supported by logical checking yet (borrows, grades, unions, tuples, and slices are deferred)")),
        })
    }
    fn block(&mut self, block: &Block) -> Result<Term> {
        self.nested(block.span, |e| {
            let old_len = e.locals.len();
            let mut bindings = Vec::new();
            for statement in &block.statements {
                let Statement::Let { mutable: false, pattern, ty: Some(ty), value, .. } = statement else {
                    return Err(Diagnostic::new(block.span, "logical blocks support only immutable, explicitly typed let bindings followed by a tail expression"));
                };
                if !matches!(&pattern.kind, PatternKind::Name(path) if path.len() == 1) {
                    return Err(Diagnostic::new(pattern.span, "logical let bindings require a single name"));
                }
                let domain = e.ty(ty)?;
                let value = e.expr(value)?;
                e.bind_ty(pattern.span, domain.clone())?;
                bindings.push((domain, value));
            }
            let tail = block.tail.as_ref().ok_or_else(|| Diagnostic::new(block.span, "logical blocks require a tail expression"))?;
            let mut term = e.expr(tail)?;
            for (domain, value) in bindings.into_iter().rev() { term = Term::app(Term::lam(domain, term), value); }
            e.locals.truncate(old_len);
            e.local_types.truncate(old_len);
            Ok(term)
        })
    }
    fn nullary_target(&self, expr: &Expr) -> Option<(BindingId, usize)> {
        match &expr.kind {
            ExprKind::Name(_) | ExprKind::Field { .. } => {
                self.resolution.reference(expr.span).map(|id| (id, 0))
            }
            ExprKind::Specialize { callee, arguments } => {
                let (id, count) = self.nullary_target(callee)?;
                Some((id, count.checked_add(arguments.len())?))
            }
            _ => None,
        }
    }
    fn eliminator(
        &mut self,
        callee: &Expr,
        arguments: &[Expr],
        span: Span,
    ) -> Result<Option<Term>> {
        let (base, types) = match &callee.kind {
            ExprKind::Specialize { callee, arguments } => (callee.as_ref(), arguments.as_slice()),
            _ => (callee, &[][..]),
        };
        let Some(id) = self.resolution.reference(base.span) else {
            return Ok(None);
        };
        let binding = &self.resolution.bindings[id];
        if binding.kind != BindingKind::Builtin {
            return Ok(None);
        }
        match binding.name.as_str() {
            "refl" => {
                if types.len() != 1 || arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "refl::<T> expects exactly one carrier type and one value",
                    ));
                }
                let carrier = self.ty(&types[0])?;
                Ok(Some(Term::refl(
                    carrier.clone(),
                    self.expr_expected(&arguments[0], Some(&carrier))?,
                )))
            }
            "Nat.induct" => {
                if !types.is_empty() || arguments.len() != 4 {
                    return Err(Diagnostic::new(
                        span,
                        "Nat.induct expects no generic arguments and exactly four values: motive, zero, step, value",
                    ));
                }
                Ok(Some(Term::NatElim {
                    motive: Box::new(self.expr(&arguments[0])?),
                    zero: Box::new(self.expr(&arguments[1])?),
                    step: Box::new(self.expr(&arguments[2])?),
                    value: Box::new(self.expr(&arguments[3])?),
                }))
            }
            "Eq.transport" => {
                if types.len() != 1 || arguments.len() != 5 {
                    return Err(Diagnostic::new(
                        span,
                        "Eq.transport::<T> expects one carrier type and exactly five values: from, to, motive, proof, value",
                    ));
                }
                let carrier = self.ty(&types[0])?;
                Ok(Some(Term::Transport {
                    ty: Box::new(carrier.clone()),
                    from: Box::new(self.expr_expected(&arguments[0], Some(&carrier))?),
                    to: Box::new(self.expr_expected(&arguments[1], Some(&carrier))?),
                    motive: Box::new(self.expr(&arguments[2])?),
                    proof: Box::new(self.expr(&arguments[3])?),
                    value: Box::new(self.expr(&arguments[4])?),
                }))
            }
            "Eq.elim" => {
                if types.len() != 1 || arguments.len() != 5 {
                    return Err(Diagnostic::new(
                        span,
                        "Eq.elim::<T> expects one carrier type and exactly five values: left, right, motive, refl_case, proof",
                    ));
                }
                let carrier = self.ty(&types[0])?;
                Ok(Some(Term::eq_elim(
                    carrier.clone(),
                    self.expr_expected(&arguments[0], Some(&carrier))?,
                    self.expr_expected(&arguments[1], Some(&carrier))?,
                    self.expr(&arguments[2])?,
                    self.expr(&arguments[3])?,
                    self.expr(&arguments[4])?,
                )))
            }
            "Data.elim" => {
                if types.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Data.elim expects exactly one type argument naming a total logical data family",
                    ));
                }
                let TypeKind::Named {
                    arguments: indices, ..
                } = &types[0].kind
                else {
                    return Err(Diagnostic::new(
                        types[0].span,
                        "Data.elim's type argument must name a declared total logical data family",
                    ));
                };
                if !indices.is_empty() {
                    return Err(Diagnostic::new(
                        types[0].span,
                        "Data.elim's type argument is the bare data family name without index arguments",
                    ));
                }
                let id = self.resolution.reference(types[0].span).ok_or_else(|| {
                    Diagnostic::new(types[0].span, "internal error: unresolved data family")
                })?;
                let name = self.data.get(&id).cloned().ok_or_else(|| {
                    Diagnostic::new(
                        types[0].span,
                        "Data.elim requires a checked total logical data family",
                    )
                })?;
                let count = self.constructor_counts.get(&id).copied().unwrap_or(0);
                if arguments.len() != count + 2 {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Data.elim expects a motive, {count} constructor branch(es) in declaration order, and a scrutinee ({} values total)",
                            count + 2
                        ),
                    ));
                }
                let motive = self.expr(&arguments[0])?;
                let branches = arguments[1..1 + count]
                    .iter()
                    .map(|branch| self.expr(branch))
                    .collect::<Result<Vec<_>>>()?;
                let scrutinee = self.expr(&arguments[1 + count])?;
                Ok(Some(Term::elim(name, motive, branches, scrutinee)))
            }
            _ => Ok(None),
        }
    }
    fn apply_expression(&mut self, mut term: Term, arguments: &[Expr]) -> Result<Term> {
        for argument in arguments {
            let domain = self.application_domain(&term)?;
            let value = self.expr_expected(argument, domain.as_ref())?;
            term = Term::app(term, value);
        }
        Ok(term)
    }
    fn expr(&mut self, expr: &Expr) -> Result<Term> {
        self.expr_expected(expr, None)
    }
    fn expr_expected(&mut self, expr: &Expr, expected: Option<&Term>) -> Result<Term> {
        self.nested(expr.span, |e| match &expr.kind {
            ExprKind::Name(_) | ExprKind::Field { .. } => e.reference(expr.span),
            ExprKind::Integer(value) => match e.expected_scalar(expected) {
                Some(Scalar::I64) => Self::machine_i64(value, expr.span),
                Some(Scalar::Bool | Scalar::Unit) => Err(Diagnostic::new(
                    expr.span,
                    "a machine integer literal cannot have a Bool or Unit carrier",
                )),
                None => Self::natural(value, expr.span),
            },
            ExprKind::Unary { op: Kind::Minus, operand, .. }
                if matches!(operand.kind, ExprKind::Integer(_)) =>
            {
                let ExprKind::Integer(value) = &operand.kind else { unreachable!() };
                match e.expected_scalar(expected) {
                    Some(Scalar::I64) => Self::machine_i64(&format!("-{value}"), expr.span),
                    _ => Err(Diagnostic::new(
                        expr.span,
                        "a negative machine literal needs an i64-carried index position",
                    )),
                }
            }
            ExprKind::Bool(value) => Ok(Term::boolean(*value)),
            ExprKind::Tuple(items) if items.is_empty() => Ok(Term::unit()),
            ExprKind::Call { callee, arguments } => {
                if let Some(term) = e.eliminator(callee, arguments, expr.span)? { return Ok(term); }
                if arguments.is_empty() && !e.nullary_target(callee).is_some_and(|(id, count)| e.nullary.get(&id) == Some(&count)) {
                    return Err(Diagnostic::new(expr.span, "an empty call requires a fully specialized nullary total function"));
                }
                let term = e.expr(callee)?;
                e.apply_expression(term, arguments)
            }
            ExprKind::Specialize { callee, arguments } => {
                let mut term = e.expr(callee)?;
                for argument in arguments {
                    let domain = e.application_domain(&term)?;
                    let value = e.ty_expected(argument, domain.as_ref())?;
                    term = Term::app(term, value);
                }
                Ok(term)
            }
            ExprKind::Block(block) => e.block(block),
            _ => Err(Diagnostic::new(expr.span, "this expression is not supported by logical checking yet; use names, natural literals, calls, specialization, or typed immutable lets")),
        })
    }
}

/// Elaborate a logical type. `locals` pairs each erased or symbolic runtime
/// binder with its kernel hypothesis type, outermost first.
pub(crate) fn elaborate_type(
    resolution: &Resolution,
    environment: &LogicalEnvironment,
    locals: &[(BindingId, Term)],
    ty: &Type,
) -> Result<Term> {
    let mut elaborator = Elaborator {
        resolution,
        kernel: &environment.kernel,
        names: &environment.names,
        data: &environment.data,
        constructors: &environment.constructors,
        constructor_counts: &environment.constructor_counts,
        nullary: &environment.nullary,
        locals: locals.iter().map(|(id, _)| Some(*id)).collect(),
        local_types: locals.iter().map(|(_, ty)| ty.clone()).collect(),
        depth: 0,
    };
    elaborator.ty(ty)
}

/// Elaborate a logical proof/value expression. Runtime bindings are absent from
/// `locals`, so references to them fail relevance checking.
pub(crate) fn elaborate_value(
    resolution: &Resolution,
    environment: &LogicalEnvironment,
    locals: &[(BindingId, Term)],
    expr: &Expr,
) -> Result<Term> {
    let mut elaborator = Elaborator {
        resolution,
        kernel: &environment.kernel,
        names: &environment.names,
        data: &environment.data,
        constructors: &environment.constructors,
        constructor_counts: &environment.constructor_counts,
        nullary: &environment.nullary,
        locals: locals.iter().map(|(id, _)| Some(*id)).collect(),
        local_types: locals.iter().map(|(_, ty)| ty.clone()).collect(),
        depth: 0,
    };
    elaborator.expr(expr)
}
