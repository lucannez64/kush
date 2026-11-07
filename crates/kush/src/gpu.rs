//! GPU-SUBSET: the checked subset of Kush that `#[gpu]` functions may use
//! (docs/gpu.md). This pass is an allowlist over the checked IR: anything it
//! does not recognise is rejected, so a new IR form never reaches the GPU
//! backend by accident.

use crate::{
    Diagnostic, Span, ast,
    executable::{
        ALLOC, Arm, Block, Executable, Expr, ExprKind, IO, Pattern, SUSPEND, Statement, Target,
        Type,
    },
    float::{FloatKind, FloatOp},
    int::IntKind,
    resolve::BindingId,
};

type Result<T> = std::result::Result<T, Diagnostic>;

/// Signature-level rules, checked when the declaration is registered.
pub(crate) fn check_declaration(
    f: &ast::Function,
    span: Span,
    attributes: &[ast::Attribute],
    fixed_effects: u16,
    effect_variables: &[BindingId],
) -> Result<()> {
    let fail = |message: &str| {
        Err(Diagnostic::new(
            span,
            format!("#[gpu] function '{}' {message}", f.name),
        ))
    };
    if attributes.iter().any(|a| a.kind == "test") {
        return fail("cannot also be a #[test]; test it through Gpu.run");
    }
    if f.name == "main" {
        return fail("cannot be the program entry point");
    }
    if f.foreign.is_some() || f.export.is_some() {
        return fail("cannot be a foreign import or an export");
    }
    if !f.generics.is_empty() {
        return fail("cannot be generic in this version; write one function per element type");
    }
    if fixed_effects & (IO | ALLOC | SUSPEND) != 0 || !effect_variables.is_empty() {
        return fail(
            "may only declare the panic effect: GPU code has no I/O, allocation, or suspension",
        );
    }
    Ok(())
}

/// Whole-program rules, run after every body is checked.
pub(crate) fn check(program: &Executable) -> Result<()> {
    let gpu = |index: usize| program.gpu_functions.get(index).copied().unwrap_or(false);
    for (index, function) in program.functions.iter().enumerate() {
        if gpu(index) {
            Subset {
                program,
                function,
                gpu: &gpu,
            }
            .function()?;
        } else {
            cpu_body(&function.body, &gpu)?;
        }
    }
    no_recursion(program, &gpu)
}

/// WGSL has no recursion: the call graph of `#[gpu]` functions is acyclic.
fn no_recursion(program: &Executable, gpu: &dyn Fn(usize) -> bool) -> Result<()> {
    let calls: Vec<Vec<(usize, Span)>> = program
        .functions
        .iter()
        .enumerate()
        .map(|(index, function)| {
            let mut out = Vec::new();
            if gpu(index) {
                visit_block(&function.body, &mut |expr| {
                    if let ExprKind::Call(Target::Function(callee), _) = &expr.kind {
                        out.push((*callee, expr.span));
                    }
                });
            }
            out
        })
        .collect();
    // 0 = unvisited, 1 = on the current path, 2 = done.
    let mut state = vec![0u8; calls.len()];
    fn dfs(
        node: usize,
        calls: &[Vec<(usize, Span)>],
        state: &mut [u8],
        program: &Executable,
    ) -> Result<()> {
        state[node] = 1;
        for &(callee, span) in &calls[node] {
            match state[callee] {
                1 => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "#[gpu] function '{}' is recursive through '{}': GPU code has no recursion",
                            program.functions[node].name, program.functions[callee].name
                        ),
                    ));
                }
                0 => dfs(callee, calls, state, program)?,
                _ => {}
            }
        }
        state[node] = 2;
        Ok(())
    }
    for node in 0..calls.len() {
        if state[node] == 0 && gpu(node) {
            dfs(node, &calls, &mut state, program)?;
        }
    }
    Ok(())
}

/// A value a `#[gpu]` function may hold: 32-bit scalars, `Bool`, `Unit`,
/// records and tuples of those, and enums without payloads.
fn gpu_value(program: &Executable, ty: Type, depth: usize) -> bool {
    match ty {
        Type::Int(IntKind::I32 | IntKind::U32)
        | Type::Float(FloatKind::F32)
        | Type::Bool
        | Type::Unit
        | Type::Never => true,
        Type::Enum(id) | Type::Variants(id, _) if depth < 32 => {
            let layout = &program.enums[id];
            if layout.linear
                || layout.foreign.is_some()
                || layout.array.is_some()
                || layout.dynamic_array.is_some()
                || layout.borrowed
            {
                return false;
            }
            if layout.record || layout.tuple {
                layout.variants.iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| gpu_value(program, *field, depth + 1))
                })
            } else {
                layout
                    .variants
                    .iter()
                    .all(|variant| variant.fields.is_empty())
            }
        }
        _ => false,
    }
}

/// `&GpuBuf<T>` or `&mut GpuBuf<T>`: the only non-value a `#[gpu]` function
/// may hold, as a parameter.
fn gpu_buffer(program: &Executable, ty: Type) -> bool {
    ty.ref_pointee()
        .is_some_and(|p| matches!(program.pointees[p], Type::GpuBuf(_)))
}

struct Subset<'a, F: Fn(usize) -> bool> {
    program: &'a Executable,
    function: &'a crate::executable::Function,
    gpu: &'a F,
}

impl<F: Fn(usize) -> bool> Subset<'_, F> {
    fn error(&self, span: Span, message: impl std::fmt::Display) -> Diagnostic {
        Diagnostic::new(
            span,
            format!("#[gpu] function '{}' {message}", self.function.name),
        )
    }
    fn name(&self, ty: Type) -> String {
        crate::runtime_types::type_name_in(
            ty,
            &self.program.pointees,
            &self.program.enums,
            &self.program.unions,
            &self.program.function_types,
        )
    }
    fn value_type(&self, ty: Type, span: Span) -> Result<()> {
        if gpu_value(self.program, ty, 0) {
            return Ok(());
        }
        Err(self.error(
            span,
            format!(
                "cannot use a value of type {}: GPU code holds i32, u32, f32, Bool, records and tuples of those, and enums without payloads",
                self.name(ty)
            ),
        ))
    }
    fn function(&self) -> Result<()> {
        let f = self.function;
        if f.closure.is_some() {
            return Err(self.error(f.span, "cannot capture values"));
        }
        for (slot, local) in f.locals.iter().enumerate() {
            if slot < f.parameters && gpu_buffer(self.program, local.ty) {
                continue;
            }
            self.value_type(local.ty, local.span)?;
        }
        self.value_type(f.result, f.span)?;
        self.block(&f.body)
    }
    fn block(&self, block: &Block) -> Result<()> {
        for statement in &block.statements {
            match statement {
                Statement::Let(_, value) | Statement::Expr(value) => self.expr(value)?,
                Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &block.tail {
            self.expr(tail)?;
        }
        Ok(())
    }
    fn arm(&self, arm: &Arm) -> Result<()> {
        self.pattern(&arm.pattern, arm.body.span)?;
        if let Some(guard) = &arm.guard {
            self.expr(guard)?;
        }
        self.expr(&arm.body)
    }
    fn pattern(&self, pattern: &Pattern, span: Span) -> Result<()> {
        match pattern {
            Pattern::Any | Pattern::Bind(_) | Pattern::Literal(_) => Ok(()),
            Pattern::Or(alternatives) => {
                alternatives.iter().try_for_each(|p| self.pattern(p, span))
            }
            Pattern::Variant { fields, .. } => {
                fields.iter().try_for_each(|(_, p)| self.pattern(p, span))
            }
            _ => Err(self.error(span, "cannot use this pattern form")),
        }
    }
    fn expr(&self, expr: &Expr) -> Result<()> {
        // A buffer parameter is checked at its only legal use, below.
        if gpu_buffer(self.program, expr.ty) {
            return Err(self.error(
                expr.span,
                "can only use a buffer as the first argument of GpuBuf.len, GpuBuf.get or GpuBuf.set",
            ));
        }
        self.value_type(expr.ty, expr.span)?;
        match &expr.kind {
            ExprKind::Constant(_)
            | ExprKind::Erased(_)
            | ExprKind::Local(_)
            | ExprKind::Peek(_)
            | ExprKind::Continue(_) => Ok(()),
            ExprKind::Break(value, _) => value.as_deref().map_or(Ok(()), |v| self.expr(v)),
            ExprKind::Unary(_, value)
            | ExprKind::Return(value)
            | ExprKind::Assign(_, value)
            | ExprKind::Project(value, _) => self.expr(value),
            ExprKind::Binary(_, left, right) => {
                self.expr(left)?;
                self.expr(right)
            }
            ExprKind::Construct { fields, .. } => fields.iter().try_for_each(|f| self.expr(f)),
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block),
            ExprKind::While(condition, body) => {
                self.expr(condition)?;
                self.block(body)
            }
            ExprKind::If(condition, then, otherwise) => {
                self.expr(condition)?;
                self.block(then)?;
                self.block(otherwise)
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee)?;
                arms.iter().try_for_each(|arm| self.arm(arm))
            }
            ExprKind::Call(target, arguments) => self.call(target, arguments, expr.span),
            ExprKind::FnValue { .. } | ExprKind::CallIndirect { .. } => {
                Err(self.error(expr.span, "cannot use function values or closures"))
            }
            ExprKind::BytesLiteral(_) => {
                Err(self.error(expr.span, "cannot use text or byte literals"))
            }
            ExprKind::Borrow(_) | ExprKind::BorrowInit { .. } | ExprKind::BorrowPlace(_) => {
                Err(self.error(expr.span, "cannot take references"))
            }
            _ => Err(self.error(expr.span, "cannot use this expression form")),
        }
    }
    fn call(&self, target: &Target, arguments: &[Expr], span: Span) -> Result<()> {
        let rest = match target {
            Target::Gpu(..) => {
                let Some((buffer, rest)) = arguments.split_first() else {
                    return Err(self.error(span, "internal error: buffer call without a buffer"));
                };
                if !(matches!(buffer.kind, ExprKind::Local(slot) if slot < self.function.parameters)
                    && gpu_buffer(self.program, buffer.ty))
                {
                    return Err(self.error(
                        buffer.span,
                        "can only use a buffer parameter of this function directly as a GPU buffer",
                    ));
                }
                rest
            }
            Target::Function(callee) => {
                if !(self.gpu)(*callee) {
                    return Err(self.error(
                        span,
                        format!(
                            "can only call other #[gpu] functions, not '{}'",
                            self.program.functions[*callee].name
                        ),
                    ));
                }
                arguments
            }
            Target::Int(..) | Target::Panic => arguments,
            Target::Float(
                FloatOp::Abs(_)
                | FloatOp::Sqrt(_)
                | FloatOp::FromInt { .. }
                | FloatOp::FromIntRounded { .. },
            ) => arguments,
            Target::Float(FloatOp::IsNan(_) | FloatOp::IsInfinite(_) | FloatOp::IsFinite(_)) => {
                return Err(self.error(
                    span,
                    "cannot test for NaN or infinity: GPU floating point does not preserve them",
                ));
            }
            Target::Foreign(_) => return Err(self.error(span, "cannot call foreign functions")),
            Target::Print
            | Target::PrintInt(_)
            | Target::PrintFloat(_)
            | Target::Io(..)
            | Target::Host(..) => {
                return Err(self.error(span, "cannot do I/O"));
            }
            _ => return Err(self.error(span, "cannot use this builtin operation")),
        };
        rest.iter().try_for_each(|argument| self.expr(argument))
    }
}

/// CPU code may not call `#[gpu]` functions directly, take them as values,
/// or use device-side buffer operations.
fn cpu_body(block: &Block, gpu: &dyn Fn(usize) -> bool) -> Result<()> {
    let mut result = Ok(());
    visit_block(block, &mut |expr| {
        if result.is_err() {
            return;
        }
        match &expr.kind {
            ExprKind::Call(Target::Function(callee), _) if gpu(*callee) => {
                result = Err(Diagnostic::new(
                    expr.span,
                    "a #[gpu] function runs only on the GPU; CPU code cannot call it directly",
                ));
            }
            ExprKind::FnValue { function, .. } if gpu(*function) => {
                result = Err(Diagnostic::new(
                    expr.span,
                    "a #[gpu] function cannot be used as a CPU function value",
                ));
            }
            ExprKind::Call(Target::Gpu(..), _) => {
                result = Err(Diagnostic::new(
                    expr.span,
                    "GpuBuf.len, GpuBuf.get and GpuBuf.set run only inside #[gpu] functions",
                ));
            }
            _ => {}
        }
    });
    result
}

/// Every expression under `block`, including nested blocks and arms, in
/// source order.
fn visit_block(block: &Block, f: &mut dyn FnMut(&Expr)) {
    for statement in &block.statements {
        match statement {
            Statement::Let(_, value) | Statement::Expr(value) => visit(value, f),
            Statement::Declare(_) => {}
        }
    }
    if let Some(tail) = &block.tail {
        visit(tail, f);
    }
}

fn visit(expr: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(expr);
    expr.for_each_child(&mut |child| visit(child, f));
}
