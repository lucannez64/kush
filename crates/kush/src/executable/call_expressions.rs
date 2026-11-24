//! Call expressions: functions, constructors, associated functions and builtins.
//!
//! An arm of `expr_expected_unchecked`, split out (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    #[allow(clippy::ptr_arg, clippy::borrowed_box)]
    pub(super) fn call_expression(
        &mut self,
        expr: &ast::Expr,
        callee: &Box<ast::Expr>,
        arguments: &Vec<ast::Expr>,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let c = self;
        let span = expr.span;
        let (kind, ty) = {
            if c.constructor_target(callee).is_some() {
                return c.construct(callee, Some(arguments), expected, span);
            }
            let (target_expr, explicit) = match &callee.kind {
                ast::ExprKind::Specialize { callee, arguments } => {
                    (callee.as_ref(), Some(arguments.as_slice()))
                }
                _ => (callee.as_ref(), None),
            };
            let Some(id) = c.resolution.reference(target_expr.span) else {
                if let ast::ExprKind::Field { value, name } = &target_expr.kind {
                    // `Type.name(..)`: an associated function.
                    if matches!(value.kind, ast::ExprKind::Name(_))
                        && let Some(type_id) = c.resolution.reference(value.span)
                        && c.resolution.bindings[type_id].kind == BindingKind::Data
                    {
                        let Some(definition) = c
                            .functions
                            .associated_fns
                            .get(&type_id)
                            .and_then(|table| table.get(name))
                            .copied()
                        else {
                            let type_name = &c.resolution.bindings[type_id].name;
                            return Err(Diagnostic::new(
                                target_expr.span,
                                format!("unknown qualified name '{type_name}.{name}'"),
                            ));
                        };
                        c.check_method_visibility(definition, name, span)?;
                        return c.user_call(
                            definition.binding,
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    if let Some((receiver, method, trait_id, trait_arguments)) =
                        c.qualified_method(target_expr)
                    {
                        return c.user_method_call(
                            receiver,
                            method,
                            Some(trait_id),
                            trait_arguments,
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    // `replace` is a Vec method only on a Vec place
                    // (or a `&mut Vec`): the name stays free for user
                    // methods on other types.
                    let vec_replace = name == "replace"
                        && c.place_type(value).is_some_and(|ty| {
                            let ty = match ty {
                                Type::RefMut(pointer) => c.types.pointees[pointer],
                                ty => ty,
                            };
                            matches!(ty, Type::Vec(_))
                        });
                    if Self::builtin_method(name) || vec_replace {
                        return c.method_call(value, name, explicit, arguments, expected, span);
                    }
                    return c.user_method_call(
                        value, name, None, None, explicit, arguments, expected, span,
                    );
                }
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        callee.span,
                        "type arguments apply only to a generic named function",
                    ));
                }
                return c.indirect_call(callee, arguments, expected, span);
            };
            let binding = &c.resolution.bindings[id];
            if c.logical.names.contains_key(&id) {
                return Err(Diagnostic::new(
                    callee.span,
                    format!(
                        "checked logical definition '{}' is erased and cannot be called at runtime; pass it only as an erased proof argument",
                        binding.name
                    ),
                ));
            }
            if c.logical.data.contains_key(&id) || c.logical.constructors.contains_key(&id) {
                return Err(Diagnostic::new(
                    callee.span,
                    format!(
                        "'{}' belongs to a total logical data type and is erased before runtime lowering; pass it only as an erased proof argument",
                        binding.name
                    ),
                ));
            }
            if c.functions.declared.contains_key(&id) {
                return c.user_call(id, explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("AllocatorContext.")
            {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        "allocator context operations take no explicit type arguments",
                    ));
                }
                let name = binding.name.clone();
                return match name.as_str() {
                    "AllocatorContext.new" => {
                        if arguments.len() != 1 {
                            return Err(Diagnostic::new(
                                span,
                                "AllocatorContext.new expects one allocator-protocol instance",
                            ));
                        }
                        c.allocator_context_new(&arguments[0], span)
                    }
                    "AllocatorContext.share" => {
                        if arguments.len() != 1 {
                            return Err(Diagnostic::new(
                                span,
                                "AllocatorContext.share expects one &AllocatorContext",
                            ));
                        }
                        c.allocator_context_share(&arguments[0], span)
                    }
                    _ => Err(Diagnostic::new(
                        span,
                        format!("unsupported allocator context operation '{name}'"),
                    )),
                };
            }
            if binding.kind == BindingKind::Builtin
                && (binding.name.starts_with("Allocator.")
                    || binding.name.starts_with("AllocBox.")
                    || binding.name.starts_with("AllocVec."))
            {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        "allocator operations take no explicit type arguments; annotate the binding instead",
                    ));
                }
                let name = binding.name.clone();
                return match name.as_str() {
                    "Allocator.new" => {
                        if arguments.len() != 2 {
                            return Err(Diagnostic::new(
                                span,
                                "Allocator.new expects an allocation function and a release function",
                            ));
                        }
                        c.allocator_new(&arguments[0], &arguments[1], None, span)
                    }
                    "Allocator.with_realloc" => {
                        if arguments.len() != 3 {
                            return Err(Diagnostic::new(
                                span,
                                "Allocator.with_realloc expects an allocation function, a release function, and a growth function",
                            ));
                        }
                        c.allocator_new(&arguments[0], &arguments[1], Some(&arguments[2]), span)
                    }
                    "AllocBox.new" | "AllocBox.try_new" => {
                        if arguments.len() != 2 {
                            return Err(Diagnostic::new(
                                span,
                                format!("{name} expects an allocator and one payload"),
                            ));
                        }
                        if name == "AllocBox.new" {
                            c.alloc_box_new(&arguments[0], &arguments[1], expected, span)
                        } else {
                            c.alloc_box_try_new(&arguments[0], &arguments[1], expected, span)
                        }
                    }
                    "AllocBox.read" | "AllocBox.take" => {
                        if arguments.len() != 1 {
                            return Err(Diagnostic::new(
                                span,
                                format!("{name} takes exactly one argument"),
                            ));
                        }
                        if name == "AllocBox.read" {
                            c.alloc_box_read(&arguments[0], span)
                        } else {
                            c.alloc_box_take(&arguments[0], span)
                        }
                    }
                    "AllocVec.new" | "AllocVec.with_capacity" => {
                        let wanted = if name == "AllocVec.new" { 1 } else { 2 };
                        if arguments.len() != wanted {
                            return Err(Diagnostic::new(
                                span,
                                format!("{name} expects {wanted} argument(s)"),
                            ));
                        }
                        c.alloc_vec_new(&arguments[0], arguments.get(1), expected, span)
                    }
                    "AllocVec.len" | "AllocVec.get" | "AllocVec.push" | "AllocVec.try_push"
                    | "AllocVec.pop" | "AllocVec.set" | "AllocVec.clear" => {
                        c.alloc_vec_call(&name, arguments, expected, span)
                    }
                    _ => Err(Diagnostic::new(
                        span,
                        format!("unsupported allocator operation '{name}'"),
                    )),
                };
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("Channel.") {
                return c.channel_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("Atomic.") {
                return c.atomic_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("GpuBuf.") {
                return c.gpu_buf_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin
                && (binding.name.starts_with("Task.") || binding.name.starts_with("Thread."))
            {
                return c.task_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin
                && (binding.name.starts_with("DynArray.") || binding.name == "Array.fill")
            {
                return c.dyn_array_call(
                    &binding.name.clone(),
                    explicit,
                    arguments,
                    expected,
                    span,
                );
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("Vec.")
                || binding.name == "Bytes.at"
            {
                return c.vec_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("Slice.") {
                return c.slice_call(&binding.name.clone(), explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("String.") {
                let name = binding.name.clone();
                return c.string_call(&name, explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name.starts_with("Str.") {
                let name = binding.name.clone();
                return c.str_call(&name, explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin
                && (binding.name.starts_with("Int.")
                    || binding.name.starts_with("Char.")
                    || binding.name == "print_int")
            {
                let name = binding.name.clone();
                return c.int_call(&name, explicit, arguments, expected, span);
            }
            if binding.kind == BindingKind::Builtin
                && (binding.name.starts_with("Float.") || binding.name == "print_float")
            {
                let name = binding.name.clone();
                return c.float_call_with(None, &name, explicit, arguments, expected, span);
            }
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    callee.span,
                    "this callee takes no type arguments",
                ));
            }
            if binding.kind == BindingKind::Builtin
                && matches!(
                    binding.name.as_str(),
                    "Arena.new"
                        | "Arena.with_strategy"
                        | "Arena.alloc"
                        | "Arena.try_alloc"
                        | "ArenaBox.read"
                        | "ArenaBox.take"
                )
            {
                let name = binding.name.as_str();
                let arity = match name {
                    "Arena.new" => 0,
                    "Arena.with_strategy" | "ArenaBox.read" | "ArenaBox.take" => 1,
                    _ => 2,
                };
                if arguments.len() != arity {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} requires exactly {arity} argument(s)"),
                    ));
                }
                match name {
                    "Arena.new" => return c.arena_new(span),
                    "Arena.with_strategy" => {
                        return c.arena_new_with(&arguments[0], span);
                    }
                    "Arena.alloc" => {
                        return c.arena_alloc(&arguments[0], &arguments[1], expected, span);
                    }
                    "Arena.try_alloc" => {
                        return c.arena_try_alloc(&arguments[0], &arguments[1], expected, span);
                    }
                    "ArenaBox.read" => {
                        return c.arena_box_read(&arguments[0], span);
                    }
                    _ => return c.arena_box_take(&arguments[0], span),
                }
            }
            if binding.kind == BindingKind::Builtin && binding.name == "Bytes.try_with_capacity" {
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Bytes.try_with_capacity takes exactly one capacity argument",
                    ));
                }
                return c.bytes_try_with_capacity(&arguments[0], expected, span);
            }
            if binding.kind == BindingKind::Builtin && binding.name == "Bytes.from" {
                if let [
                    ast::Node {
                        kind: ast::ExprKind::String(text),
                        ..
                    },
                ] = arguments.as_slice()
                {
                    c.require(ALLOC | PANIC, span)?;
                    let value = Expr {
                        kind: ExprKind::BytesLiteral(text.as_bytes().to_vec()),
                        ty: Type::Bytes,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => c.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                return Err(Diagnostic::new(
                    span,
                    "Bytes.from requires exactly one string literal; general runtime strings are deferred",
                ));
            }
            if binding.kind == BindingKind::Builtin
                && matches!(
                    binding.name.as_str(),
                    "Box.new"
                        | "Box.take"
                        | "Box.read"
                        | "Box.set"
                        | "Box.reuse"
                        | "Box.reuse_grow"
                        | "Box.try_new"
                        | "Box.try_reuse"
                        | "drop"
                )
            {
                let name = binding.name.as_str();
                let arity = if matches!(
                    name,
                    "Box.reuse" | "Box.reuse_grow" | "Box.try_reuse" | "Box.set"
                ) {
                    2
                } else {
                    1
                };
                if arguments.len() != arity {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} requires exactly {arity} argument(s)"),
                    ));
                }
                match name {
                    "Box.reuse" => {
                        return c.box_reuse(&arguments[0], &arguments[1], expected, span);
                    }
                    "Box.reuse_grow" => {
                        return c.box_reuse_grow(&arguments[0], &arguments[1], expected, span);
                    }
                    "Box.try_new" => return c.box_try_new(&arguments[0], expected, span),
                    "Box.try_reuse" => {
                        return c.box_try_reuse(&arguments[0], &arguments[1], expected, span);
                    }
                    _ => {}
                }
                let expected_inner = if name == "Box.new" {
                    expected.and_then(|ty| {
                        if let Type::Box(index) = ty {
                            Some(c.types.pointees[index])
                        } else {
                            None
                        }
                    })
                } else {
                    None
                };
                let arg = c.expr_expected(&arguments[0], expected_inner)?;
                let (kind, ty) = match name {
                    "Box.new" => {
                        c.require(ALLOC | PANIC, span)?;
                        if arg.ty == Type::Never {
                            return Err(Diagnostic::new(
                                span,
                                "Box.new cannot store a divergent value",
                            ));
                        }
                        if crate::runtime_types::has_borrow(c.types, arg.ty)
                            && !arg.ty.is_ref()
                            && arg.ty != Type::Str
                            && !crate::runtime_types::is_borrowed_record(c.types, arg.ty)
                        {
                            return Err(Diagnostic::new(
                                span,
                                "Box.new can store a reference element, a text view, a borrowed record, or an ordinary value, but not a slice view; keep slice views in a lexical record",
                            ));
                        }
                        if crate::runtime_types::contains_task(c.types, arg.ty) {
                            return Err(Diagnostic::new(
                                span,
                                "task handles cannot be stored in Box; join them in the scope that owns them",
                            ));
                        }
                        let pointee = match expected_inner {
                            Some(inner) if matches!(inner, Type::Annotated(..)) => inner,
                            _ => c.types.full(arg.ty, span)?,
                        };
                        let ty = Type::Box(c.types.pointer(pointee));
                        (ExprKind::BoxNew(Box::new(arg)), ty)
                    }
                    "Box.take" => {
                        let Type::Box(index) = arg.ty else {
                            return Err(Diagnostic::new(span, "Box.take requires an owned Box<T>"));
                        };
                        let ty = c.unannotate(c.types.pointees[index]);
                        (ExprKind::BoxTake(Box::new(arg)), ty)
                    }
                    "Box.read" => {
                        let (Type::Ref(index) | Type::RefMut(index)) = arg.ty else {
                            return Err(Diagnostic::new(
                                span,
                                "Box.read requires a &Box<T> or &mut Box<T>",
                            ));
                        };
                        let Type::Box(inner) = c.types.pointees[index] else {
                            return Err(Diagnostic::new(
                                span,
                                "Box.read requires a &Box<T> or &mut Box<T>, not another borrow type",
                            ));
                        };
                        let payload = c.types.pointees[inner];
                        if matches!(c.unannotate(payload), Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                span,
                                "Box.read cannot copy an exclusive reference element; move it out with Box.take",
                            ));
                        }
                        let ty = c.unannotate(payload);
                        (ExprKind::BoxRead(Box::new(arg)), ty)
                    }
                    "Box.set" => {
                        let Type::RefMut(index) = arg.ty else {
                            return Err(Diagnostic::new(
                                span,
                                "Box.set requires an exclusive &mut Box<T>",
                            ));
                        };
                        let Type::Box(inner) = c.types.pointees[index] else {
                            return Err(Diagnostic::new(
                                span,
                                "Box.set requires an exclusive &mut Box<T>",
                            ));
                        };
                        let payload = c.unannotate(c.types.pointees[inner]);
                        let value = c.expr_expected(&arguments[1], Some(payload))?;
                        if value.ty != Type::Never {
                            c.expect(value.ty, payload, value.span)?;
                        }
                        if c.owned_type(value.ty) || c.linear_type(value.ty) {
                            return Err(Diagnostic::new(
                                value.span,
                                "Box.set can replace a reference or copyable payload, but not an owning value; replace an owning Box with Box.reuse",
                            ));
                        }
                        (
                            ExprKind::BoxWrite(Box::new(arg), Box::new(value)),
                            Type::Unit,
                        )
                    }
                    _ => {
                        if matches!(arg.ty, Type::Ref(_) | Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                span,
                                "drop consumes owned/copy values, not borrowed handles",
                            ));
                        }
                        (ExprKind::Drop(Box::new(arg)), Type::Unit)
                    }
                };
                let value = Expr {
                    kind,
                    ty,
                    span,
                    resource: None,
                };
                return match expected {
                    Some(expected) => c.coerce(value, expected, span),
                    None => Ok(value),
                };
            }
            let bytes_op = (binding.kind == BindingKind::Builtin)
                .then(|| BytesOp::named(&binding.name))
                .flatten();
            let io_op = (binding.kind == BindingKind::Builtin)
                .then(|| IoOp::named(&binding.name))
                .flatten();
            let host_op = (binding.kind == BindingKind::Builtin)
                .then(|| HostOp::named(&binding.name))
                .flatten();
            let (target, parameters, result, effects) = if let Some(op) = io_op {
                match op {
                    IoOp::Stdin => (Target::Io(op, None), vec![], Type::Stdin, IO),
                    IoOp::Stdout => (Target::Io(op, None), vec![], Type::Stdout, IO),
                    IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk | IoOp::Write => {
                        let ok = if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) {
                            Type::Bytes
                        } else {
                            Type::Unit
                        };
                        let result = c.types.io_result(ok, span)?;
                        let shape = c.types.result(result, span)?;
                        let parameters =
                            if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) {
                                vec![Type::Stdin, Type::Bytes]
                            } else {
                                vec![Type::Stdout, Type::Ref(c.types.pointer(Type::Bytes))]
                            };
                        (Target::Io(op, Some(shape)), parameters, result, IO)
                    }
                }
            } else if let Some(op) = host_op {
                // RAW-FS-HANDLES: descriptor numbers can be reused once
                // closed, so only std (std.file's linear File) may
                // call the raw handle builtins. A std module is never
                // the root unit (0), which may name itself `std.x`.
                if op.raw_handle()
                    && (c.unit == 0
                        || c.resolution
                            .units
                            .get(c.unit)
                            .is_none_or(|path| path.first().is_none_or(|p| p != "std")))
                {
                    return Err(Diagnostic::new(
                        callee.span,
                        "raw file handle builtins are reserved for std; use std.file (open_read, read_at, write_at, sync, truncate, size, close)",
                    ));
                }
                let bytes = Type::Bytes;
                let borrowed = Type::Ref(c.types.pointer(Type::Bytes));
                let parameters = match op {
                    HostOp::FsRead | HostOp::FsList => vec![borrowed, bytes],
                    HostOp::FsWrite
                    | HostOp::FsWriteExclusive
                    | HostOp::FsAppend
                    | HostOp::FsRename => {
                        vec![borrowed, borrowed]
                    }
                    HostOp::FsRemove
                    | HostOp::FsMkdir
                    | HostOp::FsRemoveDir
                    | HostOp::FsIsFile
                    | HostOp::FsIsDir
                    | HostOp::FsSize
                    | HostOp::FsExists => vec![borrowed],
                    HostOp::EnvArgCount | HostOp::EnvVarCount => vec![],
                    HostOp::EnvArg => vec![Type::I64, bytes],
                    HostOp::EnvVar => vec![borrowed, bytes],
                    HostOp::TimeUnixSeconds | HostOp::TimeMonotonicNs => vec![],
                    HostOp::TimeSleepMs => vec![Type::I64],
                    HostOp::ProcRun => vec![
                        borrowed,
                        borrowed,
                        Type::RefMut(c.types.pointer(bytes)),
                        Type::I64,
                    ],
                    HostOp::NetTcpExchange => vec![
                        borrowed,
                        Type::I64,
                        borrowed,
                        Type::RefMut(c.types.pointer(bytes)),
                        Type::I64,
                    ],
                    HostOp::OsStrerror => vec![Type::I64, bytes],
                    HostOp::FsOpen => vec![borrowed, Type::I64],
                    HostOp::FsReadAt => vec![Type::I64, Type::I64, Type::I64, bytes],
                    HostOp::FsWriteAt => vec![Type::I64, Type::I64, borrowed],
                    HostOp::FsTruncate => vec![Type::I64, Type::I64],
                    HostOp::FsSync | HostOp::FsFileSize | HostOp::FsClose => {
                        vec![Type::I64]
                    }
                    HostOp::FsSyncDir => vec![borrowed],
                };
                let ok = match op.payload() {
                    HostPayload::Bytes => Type::Bytes,
                    HostPayload::Bool => Type::Bool,
                    HostPayload::I64 => Type::I64,
                    HostPayload::Unit => Type::Unit,
                };
                let (result, shape) = c.types.result_type(ok, Type::I64, span)?;
                (Target::Host(op, shape), parameters, result, IO)
            } else if let Some(op) = bytes_op {
                let borrowed = Type::Ref(c.types.pointer(Type::Bytes));
                let parameters = match op {
                    BytesOp::Clear => vec![Type::Bytes],
                    BytesOp::WithCapacity => vec![Type::I64],
                    BytesOp::Len | BytesOp::Capacity | BytesOp::Copy => vec![borrowed],
                    BytesOp::Get => vec![borrowed, Type::I64],
                    BytesOp::Push | BytesOp::PushReserved => vec![Type::Bytes, Type::I64],
                };
                let result = match op {
                    BytesOp::Len | BytesOp::Capacity | BytesOp::Get => Type::I64,
                    _ => Type::Bytes,
                };
                let effects = match op {
                    BytesOp::Len | BytesOp::Capacity | BytesOp::Clear => 0,
                    BytesOp::Get | BytesOp::PushReserved => PANIC,
                    _ => ALLOC | PANIC,
                };
                (Target::Bytes(op), parameters, result, effects)
            } else if binding.kind == BindingKind::Builtin && binding.name == "print_i64" {
                (Target::Print, vec![Type::I64], Type::Unit, IO | PANIC)
            } else if binding.kind == BindingKind::Builtin && binding.name == "panic" {
                (Target::Panic, vec![], Type::Never, PANIC)
            } else {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        callee.span,
                        "this callee takes no type arguments",
                    ));
                }
                return c.indirect_call(callee, arguments, expected, span);
            };
            if parameters.len() != arguments.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "wrong argument count: expected {}, found {}",
                        parameters.len(),
                        arguments.len()
                    ),
                ));
            }
            c.require(effects, span)?;
            let mut args = Vec::new();
            let mut diverges = false;
            for (arg, ty) in arguments.iter().zip(parameters) {
                let arg = c.expr_expected(arg, Some(ty))?;
                c.expect(arg.ty, ty, arg.span)?;
                diverges |= arg.ty == Type::Never;
                args.push(arg);
            }
            (
                ExprKind::Call(target, args),
                if diverges { Type::Never } else { result },
            )
        };
        c.finish_expression(kind, ty, span, expected)
    }
}
