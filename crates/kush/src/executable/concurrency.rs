//! Tasks, channels, GPU buffers, atomics and threads.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Check one of the built-in structured-task operations.
    pub(super) fn task_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.functions.uses_tasks = true;
        // THREAD-SCOPE: `Thread.scope/spawn/join` share the structured task
        // checks; `parallel` selects OS threads and their extra rules.
        let parallel = name.starts_with("Thread.");
        let name = match name {
            "Thread.scope" => "Task.scope",
            "Thread.spawn" => "Task.spawn",
            "Thread.join" => "Task.join",
            other => other,
        };
        if parallel {
            self.functions.uses_threads = true;
        }
        match name {
            // PANIC-UNWIND-USE: `Task.catch(lambda)` is a task scope that is
            // also a catch boundary; its value is `Result<T, Panic>`.
            "Task.scope" | "Task.catch" => {
                let catching = name == "Task.catch";
                if catching && parallel {
                    return Err(Diagnostic::new(
                        span,
                        "there is no Thread.catch; use Task.catch",
                    ));
                }
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "{name} takes no type arguments; its result follows the lambda's result"
                        ),
                    ));
                }
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "{name} expects one lambda, found {} arguments",
                            arguments.len()
                        ),
                    ));
                }
                if catching {
                    self.functions.uses_unwinding = true;
                }
                self.next_scope_parallel = parallel;
                let checked = self.task_callable(&arguments[0], true, false, name, parallel, span);
                self.next_scope_parallel = false;
                let (body, result, effects, result_grade) = checked?;
                if crate::runtime_types::is_reference_container(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "a task scope cannot return a reference element container; keep the container lexical and return the borrowed record it was built from",
                    ));
                }
                if crate::runtime_types::contains_task(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "Task.scope cannot return a task handle; a child handle must not escape its scope",
                    ));
                }
                if result_grade.is_some_and(|grade| !grade.is_one()) {
                    return Err(Diagnostic::new(
                        span,
                        "a task result supports exactly @[1] (owning transfer or copyable must-use) or no grade",
                    ));
                }
                self.apply_closure_writes(self.closure_write_targets(&body).unwrap_or_default());
                self.apply_effect_writes(effects);
                let obligation =
                    self.linear_type(result) || result_grade.is_some_and(Grade::is_one);
                // A failed thread scope still joins its children: threads are
                // never cancelled.
                let failure = if parallel {
                    None
                } else {
                    self.types.result(result, span).ok()
                };
                let (ty, catch) = if catching {
                    let (ty, shape) = self.types.catch_result(result, span)?;
                    (ty, Some(shape))
                } else {
                    (result, None)
                };
                let value = Expr {
                    kind: ExprKind::TaskScope {
                        body: Box::new(body),
                        obligation,
                        failure,
                        catch,
                        parallel,
                    },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "Task.spawn" => {
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Task.spawn expects one task lambda, found {} arguments",
                            arguments.len()
                        ),
                    ));
                }
                if self.scope_depth == 0 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.spawn requires an enclosing Task.scope; detached tasks are not supported",
                    ));
                }
                if self.scope_parallel != parallel {
                    return Err(Diagnostic::new(
                        span,
                        if parallel {
                            "Thread.spawn requires an enclosing Thread.scope lambda"
                        } else {
                            "Task.spawn requires an enclosing Task.scope lambda, not a Thread.scope"
                        },
                    ));
                }
                let (mut body, result, _, result_grade) =
                    self.task_callable(&arguments[0], false, true, "Task.spawn", parallel, span)?;
                if crate::runtime_types::contains_task_exit_borrow(self.types, result)
                    && !crate::runtime_types::is_child_task_exit(self.types, result)
                {
                    return Err(Diagnostic::new(
                        span,
                        "a task may return a borrowed TaskExit<R> only for a borrowed record R joined from its own scope; a nested borrowed TaskExit must be matched in the scope that joined it",
                    ));
                }
                if crate::runtime_types::contains_task(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "a task cannot return a task handle; a child handle must not escape its scope",
                    ));
                }
                if result == Type::Never {
                    return Err(Diagnostic::new(
                        span,
                        "Task<T> cannot use Never as its result type; a task that cannot return cannot be joined",
                    ));
                }
                if result_grade.is_some_and(|grade| !grade.is_one()) {
                    return Err(Diagnostic::new(
                        span,
                        "a task result supports exactly @[1] (owning transfer or copyable must-use) or no grade",
                    ));
                }
                let wanted = match (explicit, expected) {
                    (Some([ty]), _) => {
                        let lowered = self.ty(ty)?;
                        Some(self.types.full(lowered, span)?)
                    }
                    (Some(_), _) => {
                        return Err(Diagnostic::new(
                            span,
                            "Task.spawn accepts at most one result type argument",
                        ));
                    }
                    (None, Some(Type::Task(p) | Type::Thread(p))) => Some(self.types.pointees[p]),
                    (None, Some(other)) => {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "Task.spawn produces Task<T>, but the expected type is {}",
                                self.types.name(other)
                            ),
                        ));
                    }
                    (None, None) => None,
                };
                let result = match wanted {
                    Some(wanted) => {
                        self.expect(result, wanted, span)?;
                        if !self.same_layout(result, wanted) {
                            let (id, _) = Self::function_parts(body.ty).unwrap();
                            let signature = self.types.function_types[id].clone();
                            let target = self.types.function_type_with(
                                vec![],
                                wanted,
                                signature.effects,
                                vec![],
                                signature.result_grade,
                                true,
                                signature.linear,
                                crate::runtime_types::BorrowSig::default(),
                            );
                            body = self.coerce(body, Type::Once(target), span)?;
                        }
                        wanted
                    }
                    None => result,
                };
                let obligation =
                    self.linear_type(result) || result_grade.is_some_and(Grade::is_one);
                let handle = if parallel {
                    Type::Thread(self.types.pointer(result))
                } else {
                    Type::Task(self.types.pointer(result))
                };
                let value = Expr {
                    kind: ExprKind::TaskSpawn {
                        body: Box::new(body),
                        result,
                        obligation,
                        parallel,
                    },
                    ty: handle,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "Task.yield" => {
                if explicit.is_some() || !arguments.is_empty() {
                    return Err(Diagnostic::new(span, "Task.yield takes no arguments"));
                }
                self.require(SUSPEND, span)?;
                Ok(Expr {
                    kind: ExprKind::TaskYield,
                    ty: Type::Bool,
                    span,
                    resource: None,
                })
            }
            "Task.check_cancel" => {
                if explicit.is_some() || !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "Task.check_cancel takes no arguments",
                    ));
                }
                Ok(Expr {
                    kind: ExprKind::TaskCheckCancel,
                    ty: Type::Bool,
                    span,
                    resource: None,
                })
            }
            "Task.cancel" => {
                if explicit.is_some() || arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.cancel expects one '&task' argument",
                    ));
                }
                let ast::ExprKind::Unary {
                    op: Kind::Amp,
                    mutable: false,
                    operand,
                } = &arguments[0].kind
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        "Task.cancel borrows the handle: write Task.cancel(&task)",
                    ));
                };
                let slot = self.slot(operand.span)?;
                let ty = self.locals[slot].ty;
                if !matches!(ty, Type::Task(_)) {
                    return Err(Diagnostic::new(
                        operand.span,
                        format!(
                            "Task.cancel expects &Task<T>, found {}",
                            self.types.name(ty)
                        ),
                    ));
                }
                let reference = Expr {
                    kind: ExprKind::Borrow(slot),
                    ty: Type::Ref(self.types.pointer(ty)),
                    span: operand.span,
                    resource: None,
                };
                Ok(Expr {
                    kind: ExprKind::TaskCancel(Box::new(reference)),
                    ty: Type::Unit,
                    span,
                    resource: None,
                })
            }
            "Task.join" => {
                if explicit.is_some() || arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.join expects one Task<T> handle",
                    ));
                }
                let task = self.expr(&arguments[0])?;
                let p = match (task.ty, parallel) {
                    (Type::Task(p), false) | (Type::Thread(p), true) => p,
                    _ => {
                        return Err(Diagnostic::new(
                            task.span,
                            format!(
                                "{} expects {}<T>, found {}",
                                if parallel { "Thread.join" } else { "Task.join" },
                                if parallel { "Thread" } else { "Task" },
                                self.types.name(task.ty)
                            ),
                        ));
                    }
                };
                let payload = self.types.pointees[p];
                if !parallel {
                    self.require(SUSPEND, span)?;
                }
                // A thread is never cancelled: its join yields the payload,
                // so it needs no `TaskExit` declaration.
                let exit = if parallel {
                    TaskExitShape {
                        completed_tag: 0,
                        cancelled_tag: 0,
                        payload,
                        result: payload,
                    }
                } else {
                    self.types.task_exit(payload, span)?
                };
                let ty = if parallel { payload } else { exit.result };
                let obligation = self.linear_type(payload) || self.value_moves_linear(&task);
                let value = Expr {
                    kind: ExprKind::TaskJoin {
                        task: Box::new(task),
                        exit,
                        obligation,
                        parallel,
                    },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            _ => Err(Diagnostic::new(
                span,
                format!("unsupported task operation '{name}'"),
            )),
        }
    }
    /// THREAD-CHANNELS: `Channel.new(capacity)` (the message type comes from
    /// the expected `Channel<T>`) and `send/recv/close(view, i, ..)`.
    pub(super) fn channel_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.functions.uses_tasks = true;
        self.functions.uses_threads = true;
        let arity = match name {
            "Channel.new" => 1,
            "Channel.send" => 3,
            _ => 2,
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        if name == "Channel.new" {
            let ty = match (explicit, expected) {
                (Some([message]), _) => {
                    let message = self.ty(message)?;
                    let message = self.types.full(message, span)?;
                    if !crate::runtime_types::plain_data(self.types, message, 0) {
                        return Err(Diagnostic::new(
                            span,
                            "a channel carries plain data (integers, floats, Bool, Char, or records of those)",
                        ));
                    }
                    Type::Channel(self.types.pointer(message))
                }
                (None, Some(Type::Channel(p))) => Type::Channel(p),
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "Channel.new needs its message type: write Channel.new.<T>(capacity) or give the expected type Channel<T>",
                    ));
                }
            };
            let capacity = self.expr_expected(&arguments[0], Some(Type::I64))?;
            self.expect(capacity.ty, Type::I64, capacity.span)?;
            self.require(ALLOC | PANIC, span)?;
            return Ok(Expr {
                kind: ExprKind::Call(Target::ChannelNew, vec![capacity]),
                ty,
                span,
                resource: None,
            });
        }
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let view = self.expr(&arguments[0])?;
        let Some(Type::Channel(pointer)) = view
            .ty
            .slice_element()
            .map(|element| self.types.pointees[element])
        else {
            return Err(Diagnostic::new(
                view.span,
                format!(
                    "{name} expects a view of channels '&[Channel<T>]', found {}",
                    self.types.name(view.ty)
                ),
            ));
        };
        let message = self.types.pointees[pointer];
        let channel = Type::Channel(pointer);
        let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        self.require(PANIC, span)?;
        let mut values = vec![view, index];
        let (op, ty) = match name {
            "Channel.send" => {
                let value = self.expr_expected(&arguments[2], Some(message))?;
                self.expect(value.ty, message, value.span)?;
                values.push(value);
                (SliceOp::ChannelSend, Type::Unit)
            }
            "Channel.close" => (SliceOp::ChannelClose, Type::Unit),
            "Channel.recv" => {
                let option = self
                    .resolution
                    .slice_options
                    .get(&(span.start, span.end))
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(span, "Channel.recv requires Option<T> in scope")
                    })?;
                let shape = self.types.option(option, message, span)?;
                (
                    SliceOp::ChannelRecv {
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                        option: shape
                            .result
                            .layout()
                            .expect("the conventional Option is an enum layout"),
                    },
                    shape.result,
                )
            }
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unsupported channel operation '{name}'"),
                ));
            }
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Slice(op, channel), values),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// THREAD-ATOMICS: `Atomic.new(v)`, `Atomic.value(a)` and the view
    /// operations `load/store/fetch_add/swap/compare_exchange(view, i, ..)`.
    /// GPU-SUBSET: `GpuBuf.len(b)`, `GpuBuf.get(b, i)` and
    /// `GpuBuf.set(b, i, v)` on a `&GpuBuf<T>` / `&mut GpuBuf<T>`. Only
    /// `#[gpu]` functions may use them; `crate::gpu::check` enforces that.
    pub(super) fn gpu_buf_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        use crate::int::IntKind;
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let (op, arity) = match name {
            "GpuBuf.len" => (GpuOp::Len, 1),
            "GpuBuf.get" => (GpuOp::Get, 2),
            _ => (GpuOp::Set, 3),
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        let buffer = self.expr(&arguments[0])?;
        let element = buffer
            .ty
            .ref_pointee()
            .and_then(|p| match self.types.pointees[p] {
                Type::GpuBuf(e) => Some(self.types.pointees[e]),
                _ => None,
            });
        let Some(element) = element else {
            return Err(Diagnostic::new(
                buffer.span,
                format!(
                    "{name} expects a GPU buffer '&GpuBuf<T>' or '&mut GpuBuf<T>', found {}",
                    self.types.name(buffer.ty)
                ),
            ));
        };
        if op == GpuOp::Set && !matches!(buffer.ty, Type::RefMut(_)) {
            return Err(Diagnostic::new(
                buffer.span,
                "GpuBuf.set requires a read-write buffer '&mut GpuBuf<T>'; a shared '&GpuBuf<T>' is read-only",
            ));
        }
        let mut values = vec![buffer];
        let ty = match op {
            GpuOp::Len => Type::Int(IntKind::U32),
            GpuOp::Get | GpuOp::Set => {
                // A bare literal index is u32; any other index keeps its type
                // so both u32 and i32 are accepted.
                let index = if matches!(arguments[1].kind, ast::ExprKind::Integer(_)) {
                    self.expr_expected(&arguments[1], Some(Type::Int(IntKind::U32)))?
                } else {
                    self.expr(&arguments[1])?
                };
                if !matches!(
                    index.ty,
                    Type::Int(IntKind::U32 | IntKind::I32) | Type::Never
                ) {
                    return Err(Diagnostic::new(
                        index.span,
                        format!(
                            "a GPU buffer index is u32 or i32, found {}",
                            self.types.name(index.ty)
                        ),
                    ));
                }
                values.push(index);
                if op == GpuOp::Set {
                    let value = self.expr_expected(&arguments[2], Some(element))?;
                    self.expect(value.ty, element, value.span)?;
                    values.push(value);
                }
                self.require(PANIC, span)?;
                if op == GpuOp::Get {
                    element
                } else {
                    Type::Unit
                }
            }
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        Ok(Expr {
            kind: ExprKind::Call(Target::Gpu(op, element), values),
            ty,
            span,
            resource: None,
        })
    }
    pub(super) fn atomic_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let arity = match name {
            "Atomic.new" | "Atomic.value" => 1,
            "Atomic.load" => 2,
            "Atomic.compare_exchange" => 4,
            _ => 3,
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        let value = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let result = match name {
            // The cell holds the integer word: construction and consumption
            // reinterpret it.
            "Atomic.new" => {
                let initial = self.expr_expected(&arguments[0], Some(Type::I64))?;
                self.expect(initial.ty, Type::I64, initial.span)?;
                value(
                    ExprKind::Call(
                        Target::Int(
                            crate::int::IntOp::Truncate,
                            crate::int::IntKind::I64,
                            crate::int::IntKind::I64,
                        ),
                        vec![initial],
                    ),
                    Type::Atomic,
                )
            }
            "Atomic.value" => {
                let cell = self.expr_expected(&arguments[0], Some(Type::Atomic))?;
                self.expect(cell.ty, Type::Atomic, cell.span)?;
                value(
                    ExprKind::Call(
                        Target::Int(
                            crate::int::IntOp::Truncate,
                            crate::int::IntKind::I64,
                            crate::int::IntKind::I64,
                        ),
                        vec![cell],
                    ),
                    Type::I64,
                )
            }
            _ => {
                let view = self.expr(&arguments[0])?;
                let Some(pointer) = view.ty.slice_element() else {
                    return Err(Diagnostic::new(
                        view.span,
                        format!(
                            "{name} expects a view of atomics '&[Atomic]', found {}",
                            self.types.name(view.ty)
                        ),
                    ));
                };
                if self.types.pointees[pointer] != Type::Atomic {
                    return Err(Diagnostic::new(
                        view.span,
                        format!(
                            "{name} expects a view of atomics '&[Atomic]', found {}",
                            self.types.name(view.ty)
                        ),
                    ));
                }
                let mut values = vec![view];
                for argument in &arguments[1..] {
                    let checked = self.expr_expected(argument, Some(Type::I64))?;
                    self.expect(checked.ty, Type::I64, checked.span)?;
                    values.push(checked);
                }
                self.require(PANIC, span)?;
                let (op, ty) = match name {
                    "Atomic.load" => (SliceOp::AtomicLoad, Type::I64),
                    "Atomic.store" => (SliceOp::AtomicStore, Type::Unit),
                    "Atomic.fetch_add" => (SliceOp::AtomicFetchAdd, Type::I64),
                    "Atomic.swap" => (SliceOp::AtomicSwap, Type::I64),
                    "Atomic.compare_exchange" => (SliceOp::AtomicCompareExchange, Type::Bool),
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            format!("unsupported atomic operation '{name}'"),
                        ));
                    }
                };
                value(ExprKind::Call(Target::Slice(op, Type::Atomic), values), ty)
            }
        };
        match expected {
            Some(expected) => self.coerce(result, expected, span),
            None => Ok(result),
        }
    }
    /// THREAD-SCOPE: types a thread may not receive, because they can reach
    /// allocator or environment state that is not thread-safe.
    pub(super) fn thread_unshareable(&self, ty: Type) -> bool {
        self.reaches(ty, &|ty| {
            matches!(
                ty,
                Type::Arena
                    | Type::ArenaBox(_)
                    | Type::AllocatorContext
                    | Type::AllocBox(_)
                    | Type::AllocVec(_)
                    | Type::Once(_)
                    | Type::Multi(_)
                    | Type::DynObj(_)
            ) || self.types.fiber_parts(ty).is_some()
        })
    }
    /// Whether `ty` holds a value of a type `leaf` accepts, through owners,
    /// references, enums and unions.
    fn reaches(&self, ty: Type, leaf: &dyn Fn(Type) -> bool) -> bool {
        let mut pending = vec![ty];
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if leaf(ty) {
                return true;
            }
            match ty {
                Type::Box(p)
                | Type::Vec(p)
                | Type::Ref(p)
                | Type::RefMut(p)
                | Type::Slice(p)
                | Type::SliceMut(p)
                | Type::Annotated(p, _) => pending.push(self.types.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    for variant in &self.types.enums[id].variants {
                        pending.extend(variant.fields.iter().copied());
                    }
                }
                Type::Union(id) => pending.extend(self.types.unions[id].members.iter().copied()),
                _ => {}
            }
        }
        false
    }
    /// Check a task/scope body as an owned once callable with no parameters.
    /// `scope_root` marks the immediate `Task.scope` lambda, whose body may
    /// spawn. Every other function value resets lexical scope depth.
    pub(super) fn task_callable(
        &mut self,
        argument: &ast::Expr,
        scope_root: bool,
        static_body: bool,
        what: &str,
        parallel: bool,
        span: Span,
    ) -> Result<(Expr, Type, u16, Option<Grade>)> {
        let value = if scope_root {
            let ast::ExprKind::Lambda(lambda) = &argument.kind else {
                return Err(Diagnostic::new(
                    argument.span,
                    format!(
                        "{what} requires an inline, explicitly typed lambda so its scope is lexical"
                    ),
                ));
            };
            self.lambda(lambda, argument.span, None, LambdaContext::TaskScope)?
        } else {
            let saved = self.scope_depth;
            self.scope_depth = 0;
            let value = self.expr(argument);
            self.scope_depth = saved;
            value?
        };
        let Some((id, _)) = Self::function_parts(value.ty) else {
            return Err(Diagnostic::new(
                value.span,
                format!(
                    "{what} expects an owned once callable with no parameters, found {}",
                    self.types.name(value.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if !signature.parameters.is_empty() {
            return Err(Diagnostic::new(
                value.span,
                format!("{what} expects a callable with no parameters"),
            ));
        }
        let result = signature.result;
        // THREAD-SCOPE: a thread body runs on its own OS thread with an empty
        // handler stack, so it may only use builtin effects (declared
        // operations must be handled inside it), and it may not hold values
        // whose allocators or environments other threads could reach.
        // THREAD-TASKS: the thread has its own task scheduler, so its body may
        // suspend (run `Task.scope`, yield, wait for I/O); that stays inside
        // the thread and is not an effect of the spawner.
        let effects = if parallel && !scope_root {
            if signature.effects & !(IO | ALLOC | PANIC | SUSPEND) != 0 {
                return Err(Diagnostic::new(
                    value.span,
                    "a thread body may only have the effects {io, alloc, suspend}: a declared operation must be handled inside the thread",
                ));
            }
            if let Some(types) = self.closure_capture_types(&value)
                && let Some(ty) = types.into_iter().find(|ty| self.thread_unshareable(*ty))
            {
                return Err(Diagnostic::new(
                    value.span,
                    format!(
                        "a thread body cannot capture {}: arenas, user allocators, closures, trait objects and fibers may reach state another thread uses",
                        self.types.name(ty)
                    ),
                ));
            }
            // A fiber runs only on the OS thread that made it.
            if self.reaches(result, &|ty| self.types.fiber_parts(ty).is_some()) {
                return Err(Diagnostic::new(
                    value.span,
                    format!(
                        "a thread body cannot return {}: a fiber runs only on the thread that made it",
                        self.types.name(result)
                    ),
                ));
            }
            signature.effects | ALLOC | PANIC
        } else if parallel {
            signature.effects | ALLOC | PANIC
        } else {
            signature.effects | ALLOC | PANIC | SUSPEND
        };
        // A thread's `suspend` runs on the thread's own scheduler: the
        // spawner does not need it.
        let required = if parallel && !scope_root {
            effects & !SUSPEND
        } else {
            effects
        };
        self.require(required, span)?;
        let static_function = Self::callable_function(&value);
        if static_body && static_function.is_none() {
            return Err(Diagnostic::new(
                value.span,
                format!(
                    "{what} requires a statically known function or lambda body so cancellation cleanup can be checked; bind a named function or use an inline lambda"
                ),
            ));
        }
        let target = self.types.function_type_with(
            vec![],
            result,
            effects,
            vec![],
            signature.result_grade,
            true,
            signature.linear,
            signature.borrows.clone(),
        );
        let value = self.coerce(value, Type::Once(target), span)?;
        Ok((value, result, effects, signature.result_grade))
    }
}
