//! Fibers (FIBER-HANDLERS, docs/tasks-on-handlers.md): `Fiber.new`,
//! `Fiber.start` and `Fiber.resume`.
//!
//! `Fiber.new::<Op>(body)` makes an owned `Fiber<A, R, once fn() -> T ! {e}>`
//! that has not started. Its body runs on its own stack when the fiber is
//! started or resumed; a `perform Op(a)` anywhere in it (also in functions it
//! calls) suspends the fiber, and the resumer receives
//! `FiberStep.Performed(a)`. `Fiber.resume(&mut f, r)` continues the fiber
//! with `r` as the perform's result; when the body returns, the resumer
//! receives `FiberStep.Finished(t)`. The capability pass gives the body the
//! fiber's cell as `Op`'s capability.
use super::*;

impl Checker<'_, '_> {
    pub(super) fn fiber_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // Fibers live in the task runtime, and a fiber is an unwinding
        // boundary: a panic in it reaches its resumer, and dropping an
        // unfinished fiber unwinds it.
        self.functions.uses_tasks = true;
        self.functions.uses_unwinding = true;
        let value = match name {
            "Fiber.new" => self.fiber_new(explicit, arguments, span)?,
            "Fiber.start" | "Fiber.resume" => self.fiber_run(name, explicit, arguments, span)?,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unsupported fiber operation '{name}'"),
                ));
            }
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }

    fn fiber_new(
        &mut self,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        span: Span,
    ) -> Result<Expr> {
        let operation = match explicit {
            Some([ty]) => match &ty.kind {
                ast::TypeKind::Named { path, arguments }
                    if path.len() == 1 && arguments.is_empty() =>
                {
                    path[0].clone()
                }
                _ => String::new(),
            },
            _ => String::new(),
        };
        if operation.is_empty() {
            return Err(Diagnostic::new(
                span,
                "Fiber.new names the operation its body suspends with, as in Fiber.new::<Op>(fn() -> T ! {Op} { .. })",
            ));
        }
        let Some(declared) = self.effect_operations.get(&operation).copied() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{operation}' is not a declared effect operation; write 'effect {operation}: P -> R;'"
                ),
            ));
        };
        if declared.result == Type::Never {
            return Err(Diagnostic::new(
                span,
                format!("the abortive operation '{operation}' cannot suspend a fiber"),
            ));
        }
        if arguments.len() != 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Fiber.new expects one body, found {} arguments",
                    arguments.len()
                ),
            ));
        }
        // A fiber's body runs whenever it is resumed, outside any scope of
        // the code that made it.
        let saved = self.scope_depth;
        self.scope_depth = 0;
        let body = self.expr(&arguments[0]);
        self.scope_depth = saved;
        let body = body?;
        let Some((id, _)) = Self::function_parts(body.ty) else {
            return Err(Diagnostic::new(
                body.span,
                format!(
                    "Fiber.new expects a callable with no parameters, found {}",
                    self.types.name(body.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if !signature.parameters.is_empty() {
            return Err(Diagnostic::new(
                body.span,
                "Fiber.new expects a callable with no parameters",
            ));
        }
        if Self::callable_function(&body).is_none() {
            return Err(Diagnostic::new(
                body.span,
                "Fiber.new requires a named function or an inline lambda as its body",
            ));
        }
        let own = self.operation_effect(&operation);
        let declared_operations = signature.effects & !EFFECT_BITS;
        if declared_operations & !own != 0 {
            return Err(Diagnostic::new(
                body.span,
                format!(
                    "a fiber's body may perform only '{operation}' among declared operations: another operation's handler could end before the fiber is resumed"
                ),
            ));
        }
        if let Some(types) = self.closure_capture_types(&body)
            && let Some(ty) = types
                .into_iter()
                .find(|ty| crate::runtime_types::has_borrow(self.types, *ty))
        {
            return Err(Diagnostic::new(
                body.span,
                format!(
                    "a fiber's body cannot capture {}: a fiber may outlive the frame it borrows from",
                    self.types.name(ty)
                ),
            ));
        }
        let result = signature.result;
        let effects = signature.effects & EFFECT_BITS;
        let bare = self.types.function_type_with(
            vec![],
            result,
            effects,
            vec![],
            None,
            true,
            false,
            crate::runtime_types::BorrowSig::default(),
        );
        let fiber =
            self.types
                .fiber_type(declared.parameter, declared.result, Type::Once(bare), span)?;
        // The body as the runtime calls it: once, with its own row.
        let target = self.types.function_type_with(
            vec![],
            result,
            signature.effects,
            vec![],
            signature.result_grade,
            true,
            signature.linear,
            signature.borrows.clone(),
        );
        let body = self.coerce(body, Type::Once(target), span)?;
        // Making the fiber allocates its stack; running it does the rest.
        self.require(ALLOC, span)?;
        // The handler arrow a perform of the operation calls, as in
        // `dynamic_perform`.
        let resume = self.resume_value(declared.result, false, span)?;
        let handler = self.types.function_type_with(
            vec![declared.parameter, resume.ty],
            declared.result,
            0,
            vec![None, None],
            None,
            false,
            false,
            crate::runtime_types::BorrowSig::default(),
        );
        Ok(Expr {
            kind: ExprKind::Fiber {
                op: FiberOp::New {
                    operation: declared.id,
                    handler,
                    result,
                },
                operands: vec![body],
            },
            ty: fiber,
            span,
            resource: None,
        })
    }

    fn fiber_run(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        span: Span,
    ) -> Result<Expr> {
        let resuming = name == "Fiber.resume";
        let count = if resuming { 2 } else { 1 };
        if explicit.is_some() || arguments.len() != count {
            return Err(Diagnostic::new(
                span,
                if resuming {
                    "Fiber.resume expects a &mut Fiber and the reply"
                } else {
                    "Fiber.start expects a &mut Fiber"
                },
            ));
        }
        let fiber = self.expr(&arguments[0])?;
        let parts = match fiber.ty {
            Type::RefMut(pointer) => self.types.fiber_parts(self.types.pointees[pointer]),
            _ => None,
        };
        let Some((request, reply, body)) = parts else {
            return Err(Diagnostic::new(
                fiber.span,
                format!(
                    "{name} expects &mut Fiber<A, R, B>, found {}",
                    self.types.name(fiber.ty)
                ),
            ));
        };
        let Type::Once(body) = body else {
            unreachable!("a fiber's body type is a once callable")
        };
        let signature = self.types.function_types[body].clone();
        // Running the fiber does what its body does.
        self.require(signature.effects, span)?;
        let step = self.types.fiber_step(request, signature.result, span)?;
        let mut operands = vec![fiber];
        let op = if resuming {
            let value = self.expr_expected(&arguments[1], Some(reply))?;
            operands.push(self.coerce_argument(value, reply, span)?);
            FiberOp::Resume { step }
        } else {
            FiberOp::Start { step }
        };
        Ok(Expr {
            kind: ExprKind::Fiber { op, operands },
            ty: step.ty,
            span,
            resource: None,
        })
    }
}
