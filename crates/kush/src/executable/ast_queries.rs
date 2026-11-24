//! Syntactic queries over bodies: allocation, handlers, performs, references and branch labels.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Substitute alias generic binders with argument type expressions. This is
/// structural, span-preserving substitution used only for first-order
/// inference through a generic alias; actual elaboration still goes through
/// `Types::lower`, which applies the full checked substitution.
pub(crate) fn substitute_alias_type(
    resolution: &Resolution,
    ty: &ast::Type,
    map: &BTreeMap<BindingId, &ast::Type>,
) -> ast::Type {
    use ast::TypeKind as K;
    let kind = match &ty.kind {
        K::Named { path, arguments } => {
            if arguments.is_empty()
                && let Some(id) = resolution.reference(ty.span)
                && let Some(replacement) = map.get(&id)
            {
                return (*replacement).clone();
            }
            K::Named {
                path: path.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_alias_type(resolution, argument, map))
                    .collect(),
            }
        }
        K::Dyn(bounds) => K::Dyn(
            bounds
                .iter()
                .map(|bound| ast::DynBound {
                    trait_ref: substitute_alias_type(resolution, &bound.trait_ref, map),
                    bindings: bound
                        .bindings
                        .iter()
                        .map(|(name, value)| {
                            (name.clone(), substitute_alias_type(resolution, value, map))
                        })
                        .collect(),
                })
                .collect(),
        ),
        K::Integer(value) => K::Integer(value.clone()),
        K::Bool(value) => K::Bool(*value),
        K::Lifetime(name) => K::Lifetime(name.clone()),
        K::Tuple(items) => K::Tuple(
            items
                .iter()
                .map(|item| substitute_alias_type(resolution, item, map))
                .collect(),
        ),
        K::Structural { fields, open, row } => K::Structural {
            fields: fields
                .iter()
                .map(|field| ast::Field {
                    name: field.name.clone(),
                    source: field.source.clone(),
                    ty: substitute_alias_type(resolution, &field.ty, map),
                    span: field.span,
                    public: field.public,
                    min_length: None,
                })
                .collect(),
            open: *open,
            row: row
                .as_ref()
                .map(|row| Box::new(substitute_alias_type(resolution, row, map))),
        },
        K::Slice(inner) => K::Slice(Box::new(substitute_alias_type(resolution, inner, map))),
        K::Array(element, length) => K::Array(
            Box::new(substitute_alias_type(resolution, element, map)),
            Box::new(substitute_alias_type(resolution, length, map)),
        ),
        K::Borrow {
            lifetime,
            mutable,
            inner,
        } => K::Borrow {
            lifetime: lifetime.clone(),
            mutable: *mutable,
            inner: Box::new(substitute_alias_type(resolution, inner, map)),
        },
        K::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
            call_multi,
        } => K::Function {
            lifetimes: lifetimes.clone(),
            parameters: parameters
                .iter()
                .map(|parameter| ast::TypeParameter {
                    name: parameter.name.clone(),
                    ty: substitute_alias_type(resolution, &parameter.ty, map),
                    span: parameter.span,
                })
                .collect(),
            result: Box::new(substitute_alias_type(resolution, result, map)),
            effects: effects
                .iter()
                .map(|effect| substitute_alias_type(resolution, effect, map))
                .collect(),
            call_once: *call_once,
            call_linear: *call_linear,
            call_multi: *call_multi,
        },
        K::Binary { op, left, right } => K::Binary {
            op: op.clone(),
            left: Box::new(substitute_alias_type(resolution, left, map)),
            right: Box::new(substitute_alias_type(resolution, right, map)),
        },
        K::Graded { inner, grade } => K::Graded {
            inner: Box::new(substitute_alias_type(resolution, inner, map)),
            grade: Box::new(substitute_alias_type(resolution, grade, map)),
        },
        K::Predicate(expr) => K::Predicate(expr.clone()),
        K::SelfType => K::SelfType,
        K::Infer => K::Infer,
        K::Capability {
            operation,
            effects,
            multi,
        } => K::Capability {
            operation: operation.clone(),
            effects: effects.clone(),
            multi: *multi,
        },
    };
    ast::Type::new(kind, ty.span)
}

/// Whether a synthesized adapter body creates a capturing closure
/// environment. Such a body allocates when the adapter is called, so the
/// adapter's declared effect row must include `alloc` and `panic`.
pub(super) fn block_allocates(block: &Block) -> bool {
    fn expr(node: &Expr) -> bool {
        match &node.kind {
            ExprKind::FnValue { captures, .. } => !captures.is_empty() || captures.iter().any(expr),
            ExprKind::Block(block) => block_allocates(block),
            ExprKind::Unary(_, value)
            | ExprKind::Try { value, .. }
            | ExprKind::Return(value)
            | ExprKind::BoxNew(value)
            | ExprKind::BoxTake(value)
            | ExprKind::BoxRead(value)
            | ExprKind::ArenaBoxRead(value)
            | ExprKind::ArenaBoxTake(value)
            | ExprKind::AllocBoxRead(value)
            | ExprKind::AllocBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Project(value, _)
            | ExprKind::InitOwner { value, .. }
            | ExprKind::BorrowInit { value, .. }
            | ExprKind::Coerce { value, .. }
            | ExprKind::Break(Some(value), _)
            | ExprKind::Assign(_, value) => expr(value),
            ExprKind::BoxWrite(reference, value) => expr(reference) || expr(value),
            ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            }
            | ExprKind::AllocBoxNew {
                allocator: owner,
                value: payload,
            }
            | ExprKind::AllocBoxTryNew {
                allocator: owner,
                value: payload,
                ..
            } => expr(owner) || expr(payload),
            ExprKind::ArenaNew
            | ExprKind::ArenaNewWith { .. }
            | ExprKind::ArenaTryAlloc { .. }
            | ExprKind::BoxTryNew { .. }
            | ExprKind::BytesTryWithCapacity { .. } => true,
            ExprKind::Loop(block) => block_allocates(block),
            ExprKind::While(condition, block) => expr(condition) || block_allocates(block),
            ExprKind::BytesAt(a, b)
            | ExprKind::Binary(_, a, b)
            | ExprKind::StructEq {
                left: a, right: b, ..
            }
            | ExprKind::DynArrayEqual {
                left: a, right: b, ..
            } => expr(a) || expr(b),
            ExprKind::RefAssign(reference, _, value) => expr(reference) || expr(value),
            ExprKind::Slice {
                base, start, end, ..
            } => {
                expr(base) || start.as_deref().is_some_and(expr) || end.as_deref().is_some_and(expr)
            }
            ExprKind::Call(_, arguments)
            | ExprKind::Construct {
                fields: arguments, ..
            } => arguments.iter().any(expr),
            ExprKind::CallIndirect { callee, arguments } => {
                expr(callee) || arguments.iter().any(expr)
            }
            ExprKind::TaskSpawn { .. } | ExprKind::TaskScope { .. } => true,
            ExprKind::TaskCancel(reference) => expr(reference),
            ExprKind::TaskJoin { task, .. } => expr(task),
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => false,
            ExprKind::If(condition, yes, no) => {
                expr(condition) || block_allocates(yes) || block_allocates(no)
            }
            ExprKind::Match(value, arms) => {
                expr(value)
                    || arms
                        .iter()
                        .any(|arm| arm.guard.as_ref().is_some_and(expr) || expr(&arm.body))
            }
            _ => false,
        }
    }
    block.statements.iter().any(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => expr(value),
        Statement::Declare(_) => false,
    }) || block.tail.as_deref().is_some_and(expr)
}

/// Whether an expression contains a direct `perform operation` that targets
/// the currently enclosing lexical handler. Nested handles for the same
/// operation shadow the outer one, and lambdas are separate callables that do
/// not inherit a lexical handler. Used only to classify the handled body before
/// choosing the tail-resumptive or continuation lowering.
/// Whether a handler is a lambda whose resumption token is used only as
/// `resume(e)` in tail position, with `e` and every statement independent of
/// the token. Such a handler computes `h(p, k) = k(e)`, so resuming with the
/// identity token and continuing in place is the same computation.
pub(super) fn tail_resumptive_handler(resolution: &Resolution, handler: &ast::Expr) -> bool {
    let ast::ExprKind::Lambda(lambda) = &handler.kind else {
        return false;
    };
    let Some(token) = lambda
        .parameters
        .get(1)
        .and_then(|parameter| resolution.binder(parameter.span))
    else {
        return false;
    };
    // An early `return` or `?` in the handler would skip the resumption,
    // which the identity token cannot express; count it as a mention.
    let mentions = |expr: &ast::Expr| {
        let mut refs = BTreeSet::new();
        collect_expr_refs(resolution, expr, &mut refs);
        refs.contains(&token) || exits_early(expr)
    };
    fn statement_value(statement: &ast::Statement) -> &ast::Expr {
        match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => value,
        }
    }
    fn tail(
        resolution: &Resolution,
        token: BindingId,
        mentions: &dyn Fn(&ast::Expr) -> bool,
        expr: &ast::Expr,
    ) -> bool {
        match &expr.kind {
            ast::ExprKind::Call { callee, arguments } => {
                resolution.reference(callee.span) == Some(token)
                    && matches!(callee.kind, ast::ExprKind::Name(_))
                    && arguments.len() == 1
                    && !mentions(&arguments[0])
            }
            ast::ExprKind::Block(block) => block_tail(resolution, token, mentions, block),
            ast::ExprKind::If {
                condition,
                then,
                otherwise,
            } => {
                !mentions(condition)
                    && block_tail(resolution, token, mentions, then)
                    && otherwise
                        .as_deref()
                        .is_some_and(|otherwise| tail(resolution, token, mentions, otherwise))
            }
            ast::ExprKind::Match { value, arms } => {
                !mentions(value)
                    && arms.iter().all(|arm| {
                        arm.guard.as_ref().is_none_or(|guard| !mentions(guard))
                            && tail(resolution, token, mentions, &arm.body)
                    })
            }
            ast::ExprKind::Return(Some(value)) => tail(resolution, token, mentions, value),
            _ => false,
        }
    }
    fn block_tail(
        resolution: &Resolution,
        token: BindingId,
        mentions: &dyn Fn(&ast::Expr) -> bool,
        block: &ast::Block,
    ) -> bool {
        block
            .statements
            .iter()
            .all(|statement| !mentions(statement_value(statement)))
            && block
                .tail
                .as_deref()
                .is_some_and(|value| tail(resolution, token, mentions, value))
    }
    block_tail(resolution, token, &mentions, &lambda.body)
}
/// Visit the direct child expressions of an AST expression; blocks are
/// expanded into their statement values and tail. Lambda bodies are
/// children too; callers that must not enter them check for lambdas first.
/// Whether a call in `block` passes the binding by name as an argument
/// (CAP-CAPTURING-LEXICAL: a capability given to a callee).
pub(super) fn block_passes_binding(
    resolution: &Resolution,
    block: &ast::Block,
    id: BindingId,
) -> bool {
    fn expr(resolution: &Resolution, e: &ast::Expr, id: BindingId) -> bool {
        if let ast::ExprKind::Call { arguments, .. } = &e.kind
            && arguments.iter().any(|argument| {
                matches!(argument.kind, ast::ExprKind::Name(_))
                    && resolution.reference(argument.span) == Some(id)
            })
        {
            return true;
        }
        let mut found = false;
        ast_children(e, &mut |child| found = found || expr(resolution, child, id));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            expr(resolution, value, id)
        }
    }) || block
        .tail
        .as_deref()
        .is_some_and(|tail| expr(resolution, tail, id))
}

pub(super) fn block_contains_quote(block: &ast::Block) -> bool {
    fn contains_quote(expr: &ast::Expr) -> bool {
        if matches!(expr.staging(), Some((ast::StagingForm::Quote, _))) {
            return true;
        }
        let mut found = false;
        ast_children(expr, &mut |child| found |= contains_quote(child));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => contains_quote(value),
    }) || block.tail.as_deref().is_some_and(contains_quote)
}

pub(crate) fn ast_children<'a>(expr: &'a ast::Expr, f: &mut dyn FnMut(&'a ast::Expr)) {
    fn block<'a>(block: &'a ast::Block, f: &mut dyn FnMut(&'a ast::Expr)) {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => f(value),
            }
        }
        if let Some(tail) = &block.tail {
            f(tail);
        }
    }
    use ast::ExprKind as E;
    match &expr.kind {
        E::Name(_)
        | E::Integer(_)
        | E::Float(_)
        | E::String(_)
        | E::Char(_)
        | E::Bool(_)
        | E::Continue
        | E::Return(None)
        | E::Break(None) => {}
        E::Tuple(values) | E::Array(values) => values.iter().for_each(f),
        E::StructuralLiteral(fields) => fields.iter().for_each(|(_, value)| f(value)),
        E::Record { ty, fields, base } => {
            f(ty);
            fields.iter().for_each(|(_, value)| f(value));
            if let Some(base) = base {
                f(base);
            }
        }
        E::Block(inner) | E::Loop(inner) => block(inner, f),
        E::Unary { operand, .. }
        | E::Cast { value: operand, .. }
        | E::Is { value: operand, .. }
        | E::Try(operand) => f(operand),
        E::Return(Some(value)) | E::Break(Some(value)) => f(value),
        E::Binary { left, right, .. } => {
            f(left);
            f(right);
        }
        E::Call { callee, arguments } => {
            f(callee);
            arguments.iter().for_each(f);
        }
        E::Handle { handler, body, .. } => {
            f(handler);
            block(body, f);
        }
        E::Perform { value, .. } => f(value),
        E::Lambda(lambda) => block(&lambda.body, f),
        E::Specialize { callee, .. } => f(callee),
        E::Field { value, .. } => f(value),
        E::Index { value, index } => {
            f(value);
            f(index);
        }
        E::Slice { value, start, end } => {
            f(value);
            if let Some(start) = start {
                f(start);
            }
            if let Some(end) = end {
                f(end);
            }
        }
        E::If {
            condition,
            then,
            otherwise,
        } => {
            f(condition);
            block(then, f);
            if let Some(otherwise) = otherwise {
                f(otherwise);
            }
        }
        E::Match { value, arms } => {
            f(value);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    f(guard);
                }
                f(&arm.body);
            }
        }
        E::While {
            condition, body, ..
        } => {
            f(condition);
            block(body, f);
        }
    }
}
/// Whether a block contains (outside lambdas) a `handle` for a declared
/// operation whose effect bit is in `effects`.
pub(super) fn body_handles_any(body: &ast::Block, effects: u16, resolution: &Resolution) -> bool {
    fn handles(expr: &ast::Expr, effects: u16, resolution: &Resolution) -> bool {
        match &expr.kind {
            ast::ExprKind::Handle {
                operation, body, ..
            } => {
                resolution
                    .effect_bits
                    .get(operation)
                    .is_some_and(|bit| effects & bit != 0)
                    || block(body, effects, resolution)
            }
            ast::ExprKind::Lambda(_) => false,
            _ => {
                let mut found = false;
                ast_children(expr, &mut |child| {
                    found |= handles(child, effects, resolution)
                });
                found
            }
        }
    }
    fn block(body: &ast::Block, effects: u16, resolution: &Resolution) -> bool {
        body.statements.iter().any(|statement| match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                handles(value, effects, resolution)
            }
        }) || body
            .tail
            .as_deref()
            .is_some_and(|tail| handles(tail, effects, resolution))
    }
    effects & !(IO | ALLOC | PANIC | SUSPEND) != 0 && block(body, effects, resolution)
}
/// Whether an expression contains `return` or `?` outside nested lambdas.
pub(super) fn exits_early(expr: &ast::Expr) -> bool {
    fn block(block: &ast::Block) -> bool {
        block.statements.iter().any(|statement| match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => exits_early(value),
        }) || block.tail.as_deref().is_some_and(exits_early)
    }
    use ast::ExprKind as E;
    match &expr.kind {
        E::Return(_) | E::Try(_) => true,
        E::Lambda(_) => false,
        E::Name(_)
        | E::Integer(_)
        | E::Float(_)
        | E::String(_)
        | E::Char(_)
        | E::Bool(_)
        | E::Continue => false,
        E::Tuple(values) | E::Array(values) => values.iter().any(exits_early),
        E::StructuralLiteral(fields) | E::Record { fields, .. } => {
            fields.iter().any(|(_, value)| exits_early(value))
                || matches!(&expr.kind, E::Record { ty, base, .. }
                    if exits_early(ty) || base.as_deref().is_some_and(exits_early))
        }
        E::Block(inner) | E::Loop(inner) => block(inner),
        E::Unary { operand, .. }
        | E::Cast { value: operand, .. }
        | E::Is { value: operand, .. } => exits_early(operand),
        E::Binary { left, right, .. } => exits_early(left) || exits_early(right),
        E::Call { callee, arguments } => exits_early(callee) || arguments.iter().any(exits_early),
        E::Handle { handler, body, .. } => exits_early(handler) || block(body),
        E::Perform { value, .. } => exits_early(value),
        E::Specialize { callee, .. } => exits_early(callee),
        E::Field { value, .. } => exits_early(value),
        E::Index { value, index } => exits_early(value) || exits_early(index),
        E::Slice { value, start, end } => {
            exits_early(value)
                || start.as_deref().is_some_and(exits_early)
                || end.as_deref().is_some_and(exits_early)
        }
        E::If {
            condition,
            then,
            otherwise,
        } => exits_early(condition) || block(then) || otherwise.as_deref().is_some_and(exits_early),
        E::Match { value, arms } => {
            exits_early(value)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(exits_early) || exits_early(&arm.body)
                })
        }
        E::While {
            condition, body, ..
        } => exits_early(condition) || block(body),
        E::Break(value) => value.as_deref().is_some_and(exits_early),
    }
}
/// Whether a handled body performs `operation` lexically anywhere other than
/// as the body's whole tail expression (which keeps the identity token).
pub(super) fn body_has_non_tail_perform(body: &ast::Block, operation: &str) -> bool {
    body.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            contains_lexical_perform(value, operation)
        }
    }) || body.tail.as_deref().is_some_and(|tail| match &tail.kind {
        ast::ExprKind::Perform {
            operation: name,
            value,
        } if name == operation => contains_lexical_perform(value, operation),
        _ => contains_lexical_perform(tail, operation),
    })
}
pub(super) fn contains_lexical_perform(expr: &ast::Expr, operation: &str) -> bool {
    match &expr.kind {
        ast::ExprKind::Perform {
            operation: name, ..
        } => name == operation,
        ast::ExprKind::Handle {
            operation: inner,
            handler,
            body,
            ..
        } => {
            contains_lexical_perform(handler, operation)
                || (inner != operation && block_contains_lexical_perform(body, operation))
        }
        ast::ExprKind::Lambda(_) => false,
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Continue => false,
        ast::ExprKind::Tuple(values) | ast::ExprKind::Array(values) => values
            .iter()
            .any(|value| contains_lexical_perform(value, operation)),
        ast::ExprKind::StructuralLiteral(fields) => fields
            .iter()
            .any(|(_, value)| contains_lexical_perform(value, operation)),
        ast::ExprKind::Block(block) => block_contains_lexical_perform(block, operation),
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. } => contains_lexical_perform(operand, operation),
        ast::ExprKind::Binary { left, right, .. } => {
            contains_lexical_perform(left, operation) || contains_lexical_perform(right, operation)
        }
        ast::ExprKind::Call { callee, arguments } => {
            contains_lexical_perform(callee, operation)
                || arguments
                    .iter()
                    .any(|argument| contains_lexical_perform(argument, operation))
        }
        ast::ExprKind::Specialize { callee, .. } | ast::ExprKind::Field { value: callee, .. } => {
            contains_lexical_perform(callee, operation)
        }
        ast::ExprKind::Index { value, index } => {
            contains_lexical_perform(value, operation) || contains_lexical_perform(index, operation)
        }
        ast::ExprKind::Slice { value, start, end } => {
            contains_lexical_perform(value, operation)
                || start
                    .as_deref()
                    .is_some_and(|start| contains_lexical_perform(start, operation))
                || end
                    .as_deref()
                    .is_some_and(|end| contains_lexical_perform(end, operation))
        }
        ast::ExprKind::Return(value) | ast::ExprKind::Break(value) => value
            .as_deref()
            .is_some_and(|value| contains_lexical_perform(value, operation)),
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            contains_lexical_perform(condition, operation)
                || block_contains_lexical_perform(then, operation)
                || otherwise
                    .as_deref()
                    .is_some_and(|otherwise| contains_lexical_perform(otherwise, operation))
        }
        ast::ExprKind::Match { value, arms } => {
            contains_lexical_perform(value, operation)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| contains_lexical_perform(guard, operation))
                        || contains_lexical_perform(&arm.body, operation)
                })
        }
        ast::ExprKind::Record { fields, base, .. } => {
            fields
                .iter()
                .any(|(_, value)| contains_lexical_perform(value, operation))
                || base
                    .as_deref()
                    .is_some_and(|base| contains_lexical_perform(base, operation))
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
            contains_lexical_perform(condition, operation)
                || block_contains_lexical_perform(body, operation)
        }
        ast::ExprKind::Loop(body) => block_contains_lexical_perform(body, operation),
    }
}

pub(super) fn block_contains_lexical_perform(block: &ast::Block, operation: &str) -> bool {
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            contains_lexical_perform(value, operation)
        }
    }) || block
        .tail
        .as_deref()
        .is_some_and(|tail| contains_lexical_perform(tail, operation))
}

/// A one-word scalar value that can be captured by reference without owning
/// or borrowing storage. Mutable bindings of these types become live views.
pub(crate) fn is_live_scalar(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Bool | Type::Unit
    )
}

/// Collect runtime binding references in a lambda body so captures can be
/// moved into the closure environment. Name resolution has already chosen the
/// exact binder, so a reference to an outer local remains distinguishable from
/// lambda parameters and lambda-local bindings.
pub(super) fn collect_lambda_refs(
    resolution: &Resolution,
    block: &ast::Block,
    out: &mut BTreeSet<BindingId>,
) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => collect_expr_refs(resolution, value, out),
            ast::Statement::Expr(expr) => collect_expr_refs(resolution, expr, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_refs(resolution, tail, out);
    }
}

pub(super) fn collect_expr_refs(
    resolution: &Resolution,
    expr: &ast::Expr,
    out: &mut BTreeSet<BindingId>,
) {
    if let Some(id) = resolution.reference(expr.span) {
        out.insert(id);
    }
    match &expr.kind {
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Continue => {}
        ast::ExprKind::Tuple(values) | ast::ExprKind::Array(values) => {
            for value in values {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::StructuralLiteral(fields) => {
            for (_, value) in fields {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::Block(block) => collect_lambda_refs(resolution, block, out),
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. } => collect_expr_refs(resolution, operand, out),
        ast::ExprKind::Binary { left, right, .. } => {
            collect_expr_refs(resolution, left, out);
            collect_expr_refs(resolution, right, out);
        }
        ast::ExprKind::Call { callee, arguments } => {
            collect_expr_refs(resolution, callee, out);
            for argument in arguments {
                collect_expr_refs(resolution, argument, out);
            }
        }
        ast::ExprKind::Handle { handler, body, .. } => {
            collect_expr_refs(resolution, handler, out);
            collect_lambda_refs(resolution, body, out);
        }
        ast::ExprKind::Perform { value, .. } => collect_expr_refs(resolution, value, out),
        ast::ExprKind::Lambda(lambda) => collect_lambda_refs(resolution, &lambda.body, out),
        ast::ExprKind::Specialize { callee, .. } => collect_expr_refs(resolution, callee, out),
        ast::ExprKind::Field { value, .. } => collect_expr_refs(resolution, value, out),
        ast::ExprKind::Index { value, index } => {
            collect_expr_refs(resolution, value, out);
            collect_expr_refs(resolution, index, out);
        }
        ast::ExprKind::Slice { value, start, end } => {
            collect_expr_refs(resolution, value, out);
            if let Some(start) = start {
                collect_expr_refs(resolution, start, out);
            }
            if let Some(end) = end {
                collect_expr_refs(resolution, end, out);
            }
        }
        ast::ExprKind::Return(value) | ast::ExprKind::Break(value) => {
            if let Some(value) = value {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            collect_expr_refs(resolution, condition, out);
            collect_lambda_refs(resolution, then, out);
            if let Some(otherwise) = otherwise {
                collect_expr_refs(resolution, otherwise, out);
            }
        }
        ast::ExprKind::Match { value, arms } => {
            collect_expr_refs(resolution, value, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(resolution, guard, out);
                }
                collect_expr_refs(resolution, &arm.body, out);
            }
        }
        ast::ExprKind::Record { ty, fields, base } => {
            collect_expr_refs(resolution, ty, out);
            for (_, value) in fields {
                collect_expr_refs(resolution, value, out);
            }
            if let Some(base) = base {
                collect_expr_refs(resolution, base, out);
            }
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
            collect_expr_refs(resolution, condition, out);
            collect_lambda_refs(resolution, body, out);
        }
        ast::ExprKind::Loop(body) => collect_lambda_refs(resolution, body, out),
    }
}
