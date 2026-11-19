//! Typed staging orchestration. Templates are checked by the normal executable
//! pipeline; generation runs only after that check, with no host capabilities.
use crate::{Diagnostic, Span, ast, executable as ex, program::Program};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, Diagnostic>;
pub(crate) const UNSUPPORTED_RUNTIME_TEMPLATE: &str =
    "runtime splice must be called immediately in its quotation";
pub(crate) const INITIALIZER_PREFIX: &str = "$staging_init_";

/// Check a generic result against directly known return types without choosing
/// a type argument. A substitution can make distinct types equal in one
/// specialization, but cannot justify returning one as the other universally.
/// Leave expressions that need inference to the normal instance checker.
pub(crate) fn check_generic_quote_results(
    function: &ast::Function,
    resolution: &crate::resolve::Resolution,
) -> Result<()> {
    use crate::resolve::BindingKind;
    let rigid: BTreeSet<_> = function
        .generics
        .iter()
        .filter(|generic| {
            generic.bound.as_ref().is_none_or(|bound| {
                resolution.reference(bound.span).is_some_and(|id| {
                    let binding = &resolution.bindings[id];
                    binding.kind == BindingKind::Builtin && binding.name == "Type"
                })
            })
        })
        .filter_map(|generic| resolution.binder(generic.span))
        .collect();
    if rigid.is_empty() {
        return Ok(());
    }
    fn named(ty: &ast::Type, resolution: &crate::resolve::Resolution) -> Option<usize> {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } if arguments.is_empty() => {
                resolution.reference(ty.span)
            }
            _ => None,
        }
    }
    fn visit(
        expr: &ast::Expr,
        rigid: &BTreeSet<usize>,
        resolution: &crate::resolve::Resolution,
    ) -> Result<()> {
        if let Some((ast::StagingForm::Quote, operand)) = expr.staging()
            && let ast::ExprKind::Lambda(lambda) = &operand.kind
            && let Some(expected) = named(&lambda.result, resolution)
            && rigid.contains(&expected)
        {
            let check = |tail: &ast::Expr| {
                let actual = match &tail.kind {
                    ast::ExprKind::Name(_) => resolution.reference(tail.span).and_then(|id| {
                        lambda
                            .parameters
                            .iter()
                            .find(|p| resolution.binder(p.span) == Some(id))
                            .and_then(|p| named(&p.ty, resolution))
                            .filter(|id| rigid.contains(id))
                            .map(|id| (Some(id), resolution.bindings[id].name.as_str()))
                    }),
                    ast::ExprKind::Bool(_) => Some((None, "Bool")),
                    ast::ExprKind::Char(_) => Some((None, "Char")),
                    _ => None,
                };
                if let Some((actual_id, actual)) = actual
                    && actual_id != Some(expected)
                {
                    let expected = &resolution.bindings[expected].name;
                    return Err(Diagnostic::new(
                        tail.span,
                        format!(
                            "quotation must return generic type '{expected}' for every specialization, found '{actual}'",
                        ),
                    ));
                }
                Ok(())
            };
            check_quote_result_paths(&lambda.body, &check)?;
        }
        let mut result = Ok(());
        ex::ast_children(expr, &mut |child| {
            if result.is_ok() {
                result = visit(child, rigid, resolution);
            }
        });
        result
    }
    if let Some(body) = &function.body {
        for statement in &body.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                    visit(value, &rigid, resolution)?;
                }
            }
        }
        if let Some(tail) = &body.tail {
            visit(tail, &rigid, resolution)?;
        }
    }
    Ok(())
}

fn check_quote_result_paths(
    body: &ast::Block,
    check: &impl Fn(&ast::Expr) -> Result<()>,
) -> Result<()> {
    fn tail(expr: &ast::Expr, check: &impl Fn(&ast::Expr) -> Result<()>) -> Result<()> {
        match &expr.kind {
            ast::ExprKind::If {
                then, otherwise, ..
            } => {
                if let Some(expr) = then.tail.as_deref() {
                    tail(expr, check)?;
                }
                if let Some(expr) = otherwise.as_deref() {
                    tail(expr, check)?;
                }
                Ok(())
            }
            ast::ExprKind::Block(block) => {
                if let Some(expr) = block.tail.as_deref() {
                    tail(expr, check)?;
                }
                Ok(())
            }
            _ => check(expr),
        }
    }
    fn returns(expr: &ast::Expr, check: &impl Fn(&ast::Expr) -> Result<()>) -> Result<()> {
        // Returns in a nested callable belong to that callable.
        if matches!(expr.kind, ast::ExprKind::Lambda(_)) || expr.staging().is_some() {
            return Ok(());
        }
        if let ast::ExprKind::Return(Some(value)) = &expr.kind {
            tail(value, check)?;
        }
        let mut result = Ok(());
        ex::ast_children(expr, &mut |child| {
            if result.is_ok() {
                result = returns(child, check);
            }
        });
        result
    }
    for statement in &body.statements {
        match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                returns(value, check)?;
            }
        }
    }
    if let Some(expr) = body.tail.as_deref() {
        tail(expr, check)?;
        returns(expr, check)?;
    }
    Ok(())
}

/// Reference-evaluator artifact. The snapshot keeps generated function identities
/// and their checked layouts alive until the compiled owner is released.
#[derive(Debug)]
pub(crate) struct CompiledArtifact {
    pub program: std::sync::Arc<ex::Executable>,
    pub entry: usize,
}

pub(crate) fn runtime_compile(program: &ex::Executable, graph: &[u8]) -> Result<CompiledArtifact> {
    let mut program = program.clone();
    let from = program.functions.len();
    let entry = instantiate(&mut program, graph, 0, true)?;
    crate::ownership::check_generated(&mut program, from)?;
    crate::grades::check_generated(&program, from)?;
    Ok(CompiledArtifact {
        program: std::sync::Arc::new(program),
        entry,
    })
}

/// A splice address belongs to the artifact. Until the type system carries
/// that lifetime on first-class function values, runtime splices can only
/// appear as immediate callees within their own quotation.
pub(crate) fn runtime_template_supported(program: &ex::Executable, root: usize) -> bool {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        let mut immediate = BTreeSet::new();
        each_expression(&program.functions[index], |e| {
            if let ex::ExprKind::CallIndirect { callee, .. } = &e.kind {
                immediate.insert(std::ptr::from_ref(callee.as_ref()));
            }
        });
        let mut supported = true;
        each_expression(&program.functions[index], |e| match e.kind {
            ex::ExprKind::FnValue { function, .. }
                if program.functions[function].name == "splice placeholder" =>
            {
                supported &= index == root && immediate.contains(&std::ptr::from_ref(e));
            }
            ex::ExprKind::Call(ex::Target::Function(function), _)
            | ex::ExprKind::FnValue { function, .. } => pending.push(function),
            _ => {}
        });
        if !supported {
            return false;
        }
    }
    true
}

pub(crate) struct Prepared {
    pub program: Program,
    pub entries: Vec<Entry>,
}
pub(crate) struct Entry {
    pub target: Span,
    pub initializer: Span,
}

pub(crate) fn prepare(program: &Program) -> Result<Option<Prepared>> {
    if !program
        .module
        .items
        .iter()
        .any(|d| d.attributes.iter().any(|a| a.kind == "staged"))
    {
        return Ok(None);
    }
    // Resolve the original stages before introducing an earlier-stage function:
    // a staged definition's runtime parameters are unavailable to its generator.
    crate::resolve::resolve_staged_program(program)?;
    let mut output = program.clone();
    output.module.items.clear();
    let mut entries = Vec::new();
    for (unit_index, unit) in program.units.iter().enumerate() {
        let start = output.module.items.len();
        let mut initializers = Vec::new();
        for declaration in &program.module.items[unit.items.clone()] {
            let mut declaration = declaration.clone();
            if declaration.attributes.iter().any(|a| a.kind == "staged") {
                let ast::ItemKind::Function(function) = &mut declaration.item.kind else {
                    return Err(Diagnostic::new(
                        declaration.item.span,
                        "#[staged] needs a function",
                    ));
                };
                if !function.ensures.is_empty()
                    || function.parameters.iter().any(|p| {
                        // A plain callable may shrink a mutable vector. The
                        // staged declaration would promise it preserves len.
                        p.min_length.is_some()
                            && !matches!(
                                ex::split_grade(&p.ty).0.kind,
                                ast::TypeKind::Borrow { mutable: false, .. }
                            )
                    })
                {
                    return Err(Diagnostic::new(
                        declaration.item.span,
                        "staged declarations with ensures or mutable length refinements are not supported yet",
                    ));
                }
                let generator = function
                    .body
                    .as_ref()
                    .and_then(|b| b.tail.as_deref())
                    .and_then(ast::Expr::staging)
                    .filter(|(form, _)| *form == ast::StagingForm::Definition)
                    .map(|(_, expression)| expression.clone())
                    .ok_or_else(|| {
                        Diagnostic::new(declaration.item.span, "missing staged initializer")
                    })?;
                // These spans do not collide with source or allocator-protocol spans.
                let base = (1usize << 42) + entries.len() * 16;
                let synthetic = Span::new(base, base + 1);
                let callable = ast::Node::new(
                    ast::TypeKind::Function {
                        lifetimes: function.lifetimes.clone(),
                        parameters: function
                            .parameters
                            .iter()
                            .filter(|p| !p.erased)
                            .map(|p| ast::TypeParameter {
                                name: None,
                                ty: p.ty.clone(),
                                span: p.span,
                            })
                            .collect(),
                        result: Box::new(function.result.clone()),
                        effects: function.effects.clone(),
                        call_once: false,
                        call_linear: false,
                        call_multi: false,
                    },
                    Span::new(base + 2, base + 3),
                );
                let result = ast::Node::new(
                    ast::TypeKind::Named {
                        path: vec!["Code".into()],
                        arguments: vec![callable],
                    },
                    Span::new(base + 4, base + 5),
                );
                let effects = ["alloc", "panic"]
                    .into_iter()
                    .enumerate()
                    .map(|(i, name)| {
                        ast::Node::new(
                            ast::TypeKind::Named {
                                path: vec![name.into()],
                                arguments: vec![],
                            },
                            Span::new(base + 6 + i, base + 7 + i),
                        )
                    })
                    .collect();
                let initializer = ast::Function {
                    total: false,
                    name: format!("{INITIALIZER_PREFIX}{}", entries.len()),
                    lifetimes: vec![],
                    generics: function.generics.clone(),
                    parameters: vec![],
                    result,
                    effects,
                    body: Some(ast::Block {
                        statements: vec![],
                        tail: Some(Box::new(generator)),
                        span: synthetic,
                    }),
                    foreign: None,
                    export: None,
                    ensures: vec![],
                    constant: false,
                };
                initializers.push(ast::Declaration {
                    public: false,
                    attributes: vec![],
                    item: ast::Node::new(ast::ItemKind::Function(initializer), synthetic),
                });
                entries.push(Entry {
                    target: declaration.item.span,
                    initializer: synthetic,
                });
                // An unobservable Never body lets the ordinary checker establish
                // the exported signature. It is replaced before a program is returned.
                let body = ast::Block {
                    statements: vec![],
                    tail: None,
                    span: declaration.item.span,
                };
                function.body = Some(ast::Block {
                    statements: vec![],
                    tail: Some(Box::new(ast::Node::new(
                        ast::ExprKind::Loop(body),
                        declaration.item.span,
                    ))),
                    span: declaration.item.span,
                });
                declaration.attributes.retain(|a| a.kind != "staged");
            }
            output.module.items.push(declaration);
        }
        output.module.items.extend(initializers);
        output.units[unit_index].items = start..output.module.items.len();
    }
    Ok(Some(Prepared {
        program: output,
        entries,
    }))
}

pub(crate) fn materialize(
    mut program: ex::Executable,
    initializers: BTreeMap<usize, usize>,
) -> Result<ex::Executable> {
    let mut active = BTreeSet::new();
    let mut complete = BTreeSet::new();
    for target in initializers.keys().copied() {
        finish(
            &mut program,
            target,
            &initializers,
            &mut active,
            &mut complete,
        )?;
    }
    Ok(program)
}

fn generation_dependencies(program: &ex::Executable, root: usize) -> Result<BTreeSet<usize>> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(function) = pending.pop() {
        if !seen.insert(function) {
            continue;
        }
        let function = &program.functions[function];
        let mut expressions = Vec::new();
        for statement in &function.body.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => {
                    expressions.push(value)
                }
                ex::Statement::Declare(_) => {}
            }
        }
        expressions.extend(function.body.tail.as_deref());
        while let Some(expression) = expressions.pop() {
            match &expression.kind {
                ex::ExprKind::Call(ex::Target::Function(index), _)
                | ex::ExprKind::FnValue {
                    function: index, ..
                } => pending.push(*index),
                ex::ExprKind::Call(ex::Target::StageCompile(_) | ex::Target::StageEntry(_), _) => {
                    return Err(Diagnostic::new(
                        expression.span,
                        "runtime compilation is unavailable during compile-time generation",
                    ));
                }
                ex::ExprKind::Call(
                    ex::Target::Io(..)
                    | ex::Target::Host(..)
                    | ex::Target::Foreign(..)
                    | ex::Target::Print
                    | ex::Target::PrintInt(..)
                    | ex::Target::PrintFloat(..)
                    | ex::Target::ChannelNew
                    | ex::Target::Gpu(..),
                    _,
                ) => {
                    return Err(Diagnostic::new(
                        expression.span,
                        "a compile-time generator cannot perform host I/O, foreign calls, channels or GPU operations",
                    ));
                }
                ex::ExprKind::TaskScope { .. }
                | ex::ExprKind::TaskSpawn { .. }
                | ex::ExprKind::HandlerPush { .. }
                | ex::ExprKind::ArenaNew
                | ex::ExprKind::ArenaNewWith { .. }
                | ex::ExprKind::AllocatorContextNew { .. } => {
                    return Err(Diagnostic::new(
                        expression.span,
                        "tasks, effect handlers, arenas and custom allocator contexts are unavailable during compile-time generation",
                    ));
                }
                _ => {}
            }
            expression.for_each_child(&mut |child| expressions.push(child));
        }
    }
    Ok(seen)
}

fn finish(
    program: &mut ex::Executable,
    target: usize,
    initializers: &BTreeMap<usize, usize>,
    active: &mut BTreeSet<usize>,
    complete: &mut BTreeSet<usize>,
) -> Result<()> {
    if complete.contains(&target) {
        return Ok(());
    }
    if !active.insert(target) {
        return Err(Diagnostic::new(
            program.functions[target].span,
            "cyclic staged declaration dependency",
        ));
    }
    let init = initializers[&target];
    loop {
        let dependencies = generation_dependencies(program, init)?;
        let dependencies = dependencies
            .into_iter()
            .filter(|dependency| {
                initializers.contains_key(dependency) && !complete.contains(dependency)
            })
            .collect::<Vec<_>>();
        if dependencies.is_empty() {
            break;
        }
        for dependency in dependencies {
            finish(program, dependency, initializers, active, complete)?;
        }
    }
    let encoded = program.evaluate_staged_code(init)?;
    let instance = instantiate(program, &encoded, 0, false)?;
    let source = &program.functions[instance];
    let original = program.functions[target].clone();
    if source.parameters != original.parameters
        || source.result != original.result
        || source.locals[..source.parameters]
            .iter()
            .map(|l| l.ty)
            .ne(original.locals[..original.parameters].iter().map(|l| l.ty))
    {
        return Err(Diagnostic::new(
            original.span,
            "generated callable does not match its declared signature",
        ));
    }
    let mut generated = source.clone();
    generated.name = original.name;
    generated.span = original.span;
    program.functions[target] = generated;
    // A dependent generator can call this function immediately. Its new
    // helpers therefore need complete cleanup and abort metadata now, rather
    // than waiting until every staged declaration has been materialized.
    crate::suspend::mark_abort_calls(program)?;
    crate::ownership::check(program)?;
    crate::grades::check(program)?;
    active.remove(&target);
    complete.insert(target);
    Ok(())
}

struct GraphReader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl GraphReader<'_> {
    fn take(&mut self, count: usize) -> Result<&[u8]> {
        let end = self
            .at
            .checked_add(count)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| Diagnostic::new(Span::default(), "truncated code graph"))?;
        let value = &self.bytes[self.at..end];
        self.at = end;
        Ok(value)
    }
    fn word(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
}

fn append_function(program: &mut ex::Executable, function: ex::Function) -> Result<usize> {
    if program.functions.len() >= 8192 {
        return Err(Diagnostic::new(
            function.span,
            "staged function materialization budget exhausted",
        ));
    }
    let mut bytes = 0usize;
    let mut nodes = 0usize;
    for function in program.functions.iter().chain(std::iter::once(&function)) {
        each_expression(function, |e| {
            nodes = nodes.saturating_add(1);
            if let ex::ExprKind::BytesLiteral(data) = &e.kind {
                bytes = bytes.saturating_add(data.len());
            }
        });
    }
    if bytes > 64 * 1024 * 1024 || nodes > 1_000_000 {
        return Err(Diagnostic::new(
            function.span,
            "staged code materialization size budget exhausted",
        ));
    }
    let index = program.functions.len();
    program.functions.push(function);
    program.foreign_functions.push(None);
    Ok(index)
}

fn instantiate(
    program: &mut ex::Executable,
    encoded: &[u8],
    depth: usize,
    runtime: bool,
) -> Result<usize> {
    if depth >= 128 || encoded.len() > 16 * 1024 * 1024 {
        return Err(Diagnostic::new(
            Span::default(),
            "code graph nesting or size budget exhausted",
        ));
    }
    let mut reader = GraphReader {
        bytes: encoded,
        at: 0,
    };
    let version = reader.take(8)?.to_vec();
    if version != b"KUSHCD01" && version != b"KUSHCD02" && version != b"KUSHCD03" {
        return Err(Diagnostic::new(
            Span::default(),
            "invalid generated code graph",
        ));
    }
    let source_index = usize::try_from(reader.word()?)
        .ok()
        .filter(|id| program.stage_templates.contains(id))
        .ok_or_else(|| Diagnostic::new(Span::default(), "invalid template identity"))?;
    let source = program.functions[source_index].clone();
    if runtime && !runtime_template_supported(program, source_index) {
        return Err(Diagnostic::new(source.span, UNSUPPORTED_RUNTIME_TEMPLATE));
    }
    let captures = source.closure.unwrap_or(0);
    if captures == 0 {
        if reader.at != encoded.len() {
            return Err(Diagnostic::new(source.span, "invalid closed graph"));
        }
        return Ok(source_index);
    }
    if reader.word()? != captures as u64 {
        return Err(Diagnostic::new(source.span, "invalid captured code graph"));
    }
    let mut direct = source.clone();
    direct.closure = None;
    direct.capture_refs.clear();
    direct.capture_writes.clear();
    let mut arguments = Vec::new();
    let mut splices = BTreeMap::new();
    let mut literals = BTreeMap::new();
    for (index, local) in source.locals[..captures].iter().enumerate() {
        let tag = if version == b"KUSHCD03" {
            reader.take(1)?[0]
        } else {
            0
        };
        let (ty, word) = match tag {
            0 if ex::is_live_scalar(local.ty) => (local.ty, reader.word()? as i64),
            1 => {
                let stub = usize::try_from(reader.word()?)
                    .map_err(|_| Diagnostic::new(source.span, "invalid splice identity"))?;
                let length = usize::try_from(reader.word()?)
                    .map_err(|_| Diagnostic::new(source.span, "invalid splice size"))?;
                let bytes = reader.take(length)?.to_vec();
                if !program
                    .functions
                    .get(stub)
                    .is_some_and(|f| f.name == "splice placeholder")
                {
                    return Err(Diagnostic::new(source.span, "invalid splice placeholder"));
                }
                let nested = instantiate(program, &bytes, depth + 1, runtime)?;
                let ex::Type::Enum(layout) = local.ty else {
                    return Err(Diagnostic::new(source.span, "splice capture is not code"));
                };
                let Some(ex::Type::Fn(signature)) = program.enums[layout].arguments.first() else {
                    return Err(Diagnostic::new(
                        source.span,
                        "splice capture has no callable signature",
                    ));
                };
                let f = &program.function_types[*signature];
                let instance = &program.functions[nested];
                if instance.result != f.result
                    || instance.parameters != f.parameters.len()
                    || instance.locals[..instance.parameters]
                        .iter()
                        .map(|l| l.ty)
                        .ne(f.parameters.iter().copied())
                {
                    return Err(Diagnostic::new(source.span, "splice signature mismatch"));
                }
                splices.insert(stub, nested);
                (ex::Type::Unit, 0)
            }
            2 if matches!(local.ty, ex::Type::Bytes | ex::Type::String) => {
                let length = usize::try_from(reader.word()?)
                    .map_err(|_| Diagnostic::new(source.span, "invalid lifted text size"))?;
                let bytes = reader.take(length)?.to_vec();
                if local.ty == ex::Type::String && std::str::from_utf8(&bytes).is_err() {
                    return Err(Diagnostic::new(
                        source.span,
                        "invalid UTF-8 in lifted String",
                    ));
                }
                literals.insert(index, bytes);
                (ex::Type::Unit, 0)
            }
            _ => return Err(Diagnostic::new(source.span, "invalid captured value kind")),
        };
        if tag != 0 {
            direct.locals[index].ty = ex::Type::Unit;
            direct.locals[index].grade = None;
            direct.locals[index].linear = false;
            direct.local_copyable[index] = true;
            direct.local_borrowed[index] = false;
            direct.parameter_grades[index] = None;
            direct.parameter_lifetimes[index] = None;
        }
        arguments.push(ex::Expr {
            kind: ex::ExprKind::Constant(word),
            ty,
            span: source.span,
            resource: None,
        });
    }
    if reader.at != encoded.len() {
        return Err(Diagnostic::new(source.span, "trailing code graph bytes"));
    }
    let mut generated = source.clone();
    generated.parameters -= captures;
    generated.closure = None;
    generated.capture_refs.clear();
    generated.capture_writes.clear();
    generated.locals = source.locals[captures..source.parameters].to_vec();
    generated.parameter_grades = source.parameter_grades[captures..].to_vec();
    generated.parameter_lifetimes = source.parameter_lifetimes[captures..].to_vec();
    generated.local_borrowed = source.local_borrowed[captures..source.parameters].to_vec();
    generated.local_copyable = source.local_copyable[captures..source.parameters].to_vec();
    generated.resources.clear();
    generated.local_resources.clear();
    generated.parameter_slots = None;
    generated.index_relations.clear();
    for (slot, local) in generated.locals.iter().enumerate() {
        arguments.push(ex::Expr {
            kind: if crate::runtime_types::grade_erases(generated.parameter_grades[slot]) {
                ex::ExprKind::Erased(local.ty)
            } else {
                ex::ExprKind::Local(slot)
            },
            ty: local.ty,
            span: source.span,
            resource: None,
        });
    }
    let direct = append_function(program, direct)?;
    let mut memo = BTreeMap::from([(source_index, direct)]);
    let mut body = program.functions[direct].body.clone();
    rewrite_block(program, &mut body, &splices, &literals, &mut memo)?;
    program.functions[direct].body = body;
    let call = ex::Expr {
        kind: ex::ExprKind::Call(ex::Target::Function(direct), arguments),
        ty: source.result,
        span: source.span,
        resource: None,
    };
    generated.body = ex::Block {
        statements: vec![],
        tail: Some(Box::new(call)),
        ty: source.result,
    };
    append_function(program, generated)
}

fn each_expression(function: &ex::Function, mut f: impl FnMut(&ex::Expr)) {
    fn visit(expression: &ex::Expr, f: &mut dyn FnMut(&ex::Expr)) {
        f(expression);
        expression.for_each_child(&mut |child| visit(child, f));
    }
    for statement in &function.body.statements {
        match statement {
            ex::Statement::Let(_, value) | ex::Statement::Expr(value) => visit(value, &mut f),
            ex::Statement::Declare(_) => {}
        }
    }
    if let Some(tail) = &function.body.tail {
        visit(tail, &mut f);
    }
}

fn references_splice(
    program: &ex::Executable,
    root: usize,
    splices: &BTreeMap<usize, usize>,
) -> bool {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(index) = pending.pop() {
        if splices.contains_key(&index) {
            return true;
        }
        if !seen.insert(index) {
            continue;
        }
        each_expression(&program.functions[index], |e| match e.kind {
            ex::ExprKind::Call(ex::Target::Function(index), _)
            | ex::ExprKind::FnValue {
                function: index, ..
            } => pending.push(index),
            _ => {}
        });
    }
    false
}

fn mapped_function(
    program: &mut ex::Executable,
    index: usize,
    splices: &BTreeMap<usize, usize>,
    memo: &mut BTreeMap<usize, usize>,
) -> Result<usize> {
    if let Some(mapped) = splices.get(&index).or_else(|| memo.get(&index)) {
        return Ok(*mapped);
    }
    if !references_splice(program, index, splices) {
        return Ok(index);
    }
    let function = program.functions[index].clone();
    let mapped = append_function(program, function)?;
    memo.insert(index, mapped);
    let mut body = program.functions[mapped].body.clone();
    rewrite_block(program, &mut body, splices, &BTreeMap::new(), memo)?;
    program.functions[mapped].body = body;
    Ok(mapped)
}

fn rewrite_block(
    program: &mut ex::Executable,
    block: &mut ex::Block,
    splices: &BTreeMap<usize, usize>,
    literals: &BTreeMap<usize, Vec<u8>>,
    memo: &mut BTreeMap<usize, usize>,
) -> Result<()> {
    fn expression(
        program: &mut ex::Executable,
        e: &mut ex::Expr,
        splices: &BTreeMap<usize, usize>,
        literals: &BTreeMap<usize, Vec<u8>>,
        memo: &mut BTreeMap<usize, usize>,
    ) -> Result<()> {
        if let ex::ExprKind::Call(ex::Target::Bytes(ex::BytesOp::Copy), arguments) = &e.kind
            && arguments.len() == 1
            && let ex::ExprKind::Borrow(slot) = arguments[0].kind
            && let Some(bytes) = literals.get(&slot)
        {
            e.kind = ex::ExprKind::BytesLiteral(bytes.clone());
            e.resource = None;
            return Ok(());
        }
        match &mut e.kind {
            ex::ExprKind::Call(ex::Target::Function(index), _)
            | ex::ExprKind::FnValue {
                function: index, ..
            } => {
                *index = mapped_function(program, *index, splices, memo)?;
            }
            _ => {}
        }
        let mut result = Ok(());
        e.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = expression(program, child, splices, literals, memo);
            }
        });
        result
    }
    for statement in &mut block.statements {
        match statement {
            ex::Statement::Let(_, value) | ex::Statement::Expr(value) => {
                expression(program, value, splices, literals, memo)?
            }
            ex::Statement::Declare(_) => {}
        }
    }
    if let Some(tail) = &mut block.tail {
        expression(program, tail, splices, literals, memo)?;
    }
    Ok(())
}
