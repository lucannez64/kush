//! Declared operations as hidden capability parameters
//! (FND-HANDLERS-ONE-PARAMS and -VALUES, docs/one-handler-model.md section 2).
//!
//! A function that may perform declared operations it does not handle gets a
//! copy taking one more `cap Op` parameter per such operation, after its
//! written parameters and in operation-id order. In that copy a perform by
//! name with no enclosing `handle Op` of its own calls the parameter, and a
//! direct call passes, per operation of the callee, the innermost enclosing
//! `handle Op` of the caller or the caller's own parameter. Code that has
//! neither (task bodies, entry points) keeps the original function, which
//! still performs through the dynamic stack; so does a handler that is
//! capturing, which is reached through the dynamic frame by a trampoline. An
//! await point under a handler with code after `resume` then resumes the copy
//! through its capability parameter.
//!
//! A function value takes the capabilities its arrow's row names the same
//! way (decision D1: bound at each call): its function is a copy for those
//! operations, the arrow gains the parameters, and every indirect call passes
//! them. Arrows whose values reach code that calls them without capabilities
//! (handlers, task and callback builtins, foreign functions) keep the dynamic
//! stack until HANDLERS-ONE-BUILTINS.
use super::{Result, performs_with};
use crate::executable::{Block, Executable, Expr, ExprKind, Local, Statement, Target, Type};
use std::collections::{BTreeMap, BTreeSet};

/// How the capability for an operation is supplied at a call.
#[derive(Clone, Copy)]
enum Capability {
    /// A local holding a noncapturing handler or a capability parameter.
    Local(usize, Type),
    /// The enclosing handler is capturing: perform through the dynamic stack.
    Dynamic,
}

struct Pass<'a> {
    /// Operations each original function needs a capability for, in id
    /// order; empty for functions that are not copied.
    needs: &'a [Vec<usize>],
    /// Handler arrow of each declared resumptive operation.
    arrows: &'a BTreeMap<usize, usize>,
    function_types: &'a [crate::runtime_types::FunctionType],
    /// Operations whose capabilities a function value of each arrow type
    /// takes; empty for arrows that keep the dynamic stack.
    values: &'a [Vec<usize>],
    /// Operations whose capabilities each trait-object call and each
    /// closed-world union call passes to its members.
    dyn_calls: &'a [Vec<usize>],
    union_calls: &'a [Vec<usize>],
    originals: usize,
    /// Copy index of each copied original and its capability operations,
    /// in request order.
    /// `true` in a key: the copy receives the capabilities as closure
    /// captures instead of parameters.
    copies: BTreeMap<(usize, Vec<usize>, bool), usize>,
    order: Vec<(usize, Vec<usize>, bool)>,
    /// Operations of each arrow's row, also for arrows that keep the
    /// dynamic stack.
    rows: &'a [Vec<usize>],
    /// Functions that can receive capabilities as extra captures: closures
    /// with an ordinary layout.
    capturable: &'a [bool],
    /// Trampolines through the dynamic stack, by operation.
    trampolines: &'a BTreeMap<usize, (usize, Type)>,
}

impl Pass<'_> {
    fn copy_of(&mut self, function: usize, operations: &[usize]) -> usize {
        self.copy_with(function, operations, false)
    }

    fn copy_with(&mut self, function: usize, operations: &[usize], captured: bool) -> usize {
        let key = (function, operations.to_vec(), captured);
        if let Some(copy) = self.copies.get(&key) {
            return *copy;
        }
        let copy = self.originals + self.order.len();
        self.order.push(key.clone());
        self.copies.insert(key, copy);
        copy
    }

    /// The operations whose capabilities a value of callable type `ty`
    /// takes.
    fn value_operations(&self, ty: Type) -> &[usize] {
        match ty {
            Type::Fn(id) | Type::Once(id) | Type::Multi(id) => &self.values[id],
            _ => &[],
        }
    }

    /// The capability arguments for `operations` at this point.
    fn supply(&self, operations: &[usize], scope: &Scope, span: crate::Span) -> Vec<Expr> {
        operations
            .iter()
            .map(|operation| {
                let capability = scope.capabilities.get(operation).copied().or_else(|| {
                    scope
                        .hidden
                        .get(operation)
                        .map(|&slot| Capability::Local(slot, Type::Fn(self.arrows[operation])))
                });
                match capability {
                    Some(Capability::Local(slot, ty)) => Expr {
                        kind: ExprKind::Local(slot),
                        ty,
                        span,
                        resource: None,
                    },
                    Some(Capability::Dynamic) | None => {
                        let (function, ty) = self.trampolines[operation];
                        Expr {
                            kind: ExprKind::FnValue {
                                function,
                                captures: vec![],
                            },
                            ty,
                            span,
                            resource: None,
                        }
                    }
                }
            })
            .collect()
    }

    /// The handler local of a `HandlerPush` as a capability, when it can be
    /// called directly with the operation's arrow.
    fn pushed(&self, handler: &Expr, operation: usize) -> Capability {
        let arrow = self.arrows[&operation];
        match (&handler.kind, handler.ty) {
            (ExprKind::Local(slot), Type::Fn(found))
                if self.function_types[found].parameters
                    == self.function_types[arrow].parameters
                    && self.function_types[found].result == self.function_types[arrow].result =>
            {
                Capability::Local(*slot, Type::Fn(arrow))
            }
            _ => Capability::Dynamic,
        }
    }

    fn block(&mut self, block: &mut Block, scope: &Scope) {
        for statement in &mut block.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                self.expr(value, scope);
            }
        }
        if let Some(tail) = block.tail.as_deref_mut() {
            self.expr(tail, scope);
        }
    }

    fn expr(&mut self, expr: &mut Expr, scope: &Scope) {
        if let ExprKind::HandlerPush {
            operation,
            handler,
            body,
            ..
        } = &mut expr.kind
        {
            self.expr(handler, scope);
            let mut inner = scope.clone();
            if self.arrows.contains_key(operation) {
                let capability = self.pushed(handler, *operation);
                inner.capabilities.insert(*operation, capability);
            }
            self.block(body, &inner);
            return;
        }
        expr.for_each_child_mut(&mut |child| self.expr(child, scope));
        match &mut expr.kind {
            ExprKind::DynamicPerform { operation, .. } => {
                let Some(&slot) = scope.hidden.get(operation) else {
                    return;
                };
                if scope.capabilities.contains_key(operation) {
                    return;
                }
                let arrow = self.arrows[operation];
                let ExprKind::DynamicPerform {
                    payload, resume, ..
                } = std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
                else {
                    unreachable!()
                };
                expr.kind = ExprKind::CallIndirect {
                    callee: Box::new(Expr {
                        kind: ExprKind::Local(slot),
                        ty: Type::Fn(arrow),
                        span: expr.span,
                        resource: None,
                    }),
                    arguments: vec![*payload, *resume],
                };
            }
            ExprKind::Call(Target::Function(callee), arguments)
                if *callee < self.originals && !self.needs[*callee].is_empty() =>
            {
                // Code with no capability for any of them keeps the
                // original, which performs through the dynamic stack.
                let supplied = self.needs[*callee].iter().any(|operation| {
                    scope.capabilities.contains_key(operation)
                        || scope.hidden.contains_key(operation)
                });
                if !supplied {
                    return;
                }
                let operations = self.needs[*callee].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
                *callee = self.copy_of(*callee, &operations);
            }
            // Call-time binding (decision D1): a function value receives the
            // capabilities its arrow's row names from each caller.
            ExprKind::CallIndirect { callee, arguments }
                if !self.value_operations(callee.ty).is_empty() =>
            {
                let operations = self.value_operations(callee.ty).to_vec();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            // Rule 8: a task body runs within the builtin's extent (a scope) or
            // in a task of its own (a spawn); the runtime calls it without
            // capabilities. A lambda written there captures them at the call
            // instead. A spawned task keeps a noncapturing handler's
            // capability; a capturing one stays behind and the trampoline
            // finds no frame in the new task (decision D3).
            ExprKind::TaskScope { body, .. } | ExprKind::TaskSpawn { body, .. } => {
                let operations = match body.ty {
                    Type::Once(id) => self.rows[id].clone(),
                    _ => return,
                };
                if operations.is_empty() {
                    return;
                }
                let span = body.span;
                let supplied = self.supply(&operations, scope, span);
                if let ExprKind::FnValue { function, captures } = &mut body.kind
                    && *function < self.originals
                    && self.capturable[*function]
                {
                    *function = self.copy_with(*function, &operations, true);
                    captures.extend(supplied);
                }
            }
            ExprKind::Call(Target::DynCall { spec }, arguments)
                if !self.dyn_calls[*spec].is_empty() =>
            {
                let operations = self.dyn_calls[*spec].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            ExprKind::Call(Target::UnionBorrowCall { spec }, arguments)
                if !self.union_calls[*spec].is_empty() =>
            {
                let operations = self.union_calls[*spec].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            ExprKind::FnValue { function, .. }
                if *function < self.originals && !self.value_operations(expr.ty).is_empty() =>
            {
                let operations = self.value_operations(expr.ty).to_vec();
                *function = self.copy_of(*function, &operations);
            }
            ExprKind::Suspend {
                call,
                callee: Some(callee),
                ..
            } => {
                // The call was redirected to the copy. An await of the
                // region's operation is keyed by the copy's capability
                // parameter when the lowering finds it performs through it.
                if let ExprKind::Call(Target::Function(target), _) = &call.kind {
                    *callee = *target;
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Default)]
struct Scope {
    /// Hidden capability parameter slot by operation (copies only).
    hidden: BTreeMap<usize, usize>,
    /// Innermost enclosing `handle` of each operation in this function.
    capabilities: BTreeMap<usize, Capability>,
}

/// Hidden capability parameter slot of each copy, by operation.
pub(super) type Hidden = BTreeMap<usize, BTreeMap<usize, usize>>;

/// Add the copies and redirect direct calls and function values to them.
pub(super) fn add(program: &mut Executable) -> Result<Hidden> {
    let mut arrows = BTreeMap::new();
    for function in &program.functions {
        collect_arrows(&function.body, &mut arrows);
    }
    if arrows.is_empty() {
        return Ok(Hidden::new());
    }
    let performs = performs_with(program, true);
    let mut needs = (0..program.functions.len())
        .map(|index| {
            let function = &program.functions[index];
            if function.closure.is_some()
                || function.parameter_slots.is_some()
                || program.foreign_functions[index].is_some()
            {
                return vec![];
            }
            performs[index]
                .iter()
                .copied()
                .filter(|operation| arrows.contains_key(operation))
                .collect()
        })
        .collect::<Vec<Vec<usize>>>();
    let values = value_operations(program, &arrows);
    // Dispatch calls every member directly, so the members of one key take
    // the union of their operations. A member that performs operations but
    // cannot be copied keeps the whole dispatch on the dynamic stack.
    let members = |functions: &mut dyn Iterator<Item = usize>| -> Vec<usize> {
        let mut operations = BTreeSet::new();
        for function in functions {
            if needs[function].is_empty()
                && performs[function]
                    .iter()
                    .any(|operation| arrows.contains_key(operation))
            {
                return vec![];
            }
            operations.extend(needs[function].iter().copied());
        }
        operations.into_iter().collect()
    };
    let dyn_calls = program
        .dyn_calls
        .iter()
        .map(|spec| {
            members(
                &mut program.dyn_members[spec.object]
                    .iter()
                    .filter_map(|member| member.methods.get(&spec.key).copied()),
            )
        })
        .collect::<Vec<_>>();
    let union_calls = program
        .union_calls
        .iter()
        .map(|spec| members(&mut spec.members.iter().map(|member| member.2)))
        .collect::<Vec<_>>();
    if needs.iter().all(Vec::is_empty) && values.iter().all(Vec::is_empty) {
        return Ok(Hidden::new());
    }
    let mut trampolines = BTreeMap::new();
    for (&operation, &arrow) in &arrows {
        trampolines.insert(operation, trampoline(program, operation, arrow));
    }
    let originals = program.functions.len();
    needs.resize(originals, vec![]);
    let rows = (0..program.function_types.len())
        .map(|id| row_operations(program, &arrows, id))
        .collect::<Vec<_>>();
    let capturable = program
        .functions
        .iter()
        .map(|function| function.closure.is_some() && function.parameter_slots.is_none())
        .collect::<Vec<_>>();
    // Copies start from the bodies as checked: the originals' calls get the
    // dynamic trampoline where a copy passes its own parameter.
    let sources = program.functions.clone();
    let function_types = program.function_types.clone();
    let mut pass = Pass {
        needs: &needs,
        arrows: &arrows,
        function_types: &function_types,
        values: &values,
        rows: &rows,
        capturable: &capturable,
        dyn_calls: &dyn_calls,
        union_calls: &union_calls,
        originals,
        copies: BTreeMap::new(),
        order: Vec::new(),
        trampolines: &trampolines,
    };
    for function in &mut program.functions[..originals] {
        pass.block(&mut function.body, &Scope::default());
    }
    for (spec, operations) in program.dyn_calls.iter().zip(&dyn_calls) {
        if operations.is_empty() {
            continue;
        }
        for member in &mut program.dyn_members[spec.object] {
            if let Some(method) = member.methods.get_mut(&spec.key)
                && *method < originals
            {
                *method = pass.copy_of(*method, operations);
            }
        }
    }
    for (spec, operations) in program.union_calls.iter_mut().zip(&union_calls) {
        if operations.is_empty() {
            continue;
        }
        for member in &mut spec.members {
            member.2 = pass.copy_of(member.2, operations);
        }
    }
    let mut copies = Hidden::new();
    let mut next = 0;
    while next < pass.order.len() {
        let (original, operations, captured) = pass.order[next].clone();
        let mut copy = sources[original].clone();
        let mut slots = (0..copy.parameters).collect::<Vec<_>>();
        let mut hidden = BTreeMap::new();
        copy.parameter_grades.resize(copy.parameters, None);
        copy.parameter_lifetimes.resize(copy.parameters, None);
        // Captured capabilities follow the closure's own captures.
        let first = if captured {
            copy.closure.unwrap_or(0)
        } else {
            copy.parameters
        };
        for (offset, &operation) in operations.iter().enumerate() {
            let position = first + offset;
            let slot = copy.locals.len();
            copy.locals.push(Local {
                ty: Type::Fn(arrows[&operation]),
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span: copy.span,
            });
            if copy.local_resources.len() == slot {
                copy.local_resources.push(None);
            }
            if !copy.local_borrowed.is_empty() {
                copy.local_borrowed.push(false);
            }
            if !copy.local_copyable.is_empty() {
                copy.local_copyable.push(true);
            }
            copy.parameter_grades.insert(position, None);
            copy.parameter_lifetimes.insert(position, None);
            copy.capability_parameters.push(slot);
            slots.insert(position, slot);
            copy.parameters += 1;
            if captured {
                copy.closure = Some(copy.closure.unwrap_or(0) + 1);
                copy.capture_refs.push(false);
                copy.capture_writes.push(false);
            }
            hidden.insert(operation, slot);
        }
        copy.parameter_slots = Some(slots);
        copies.insert(originals + next, hidden.clone());
        copy.name = format!("{}::capabilities", copy.name);
        pass.block(
            &mut copy.body,
            &Scope {
                hidden,
                ..Scope::default()
            },
        );
        program.functions.push(copy);
        program.foreign_functions.push(None);
        next += 1;
    }
    // The arrows of function values take the capabilities last.
    for (id, operations) in values.iter().enumerate() {
        let arrow = &mut program.function_types[id];
        let written = arrow.parameters.len();
        for &operation in operations {
            arrow.parameters.push(Type::Fn(arrows[&operation]));
        }
        if arrow.parameter_grades.len() == written {
            arrow.parameter_grades.resize(arrow.parameters.len(), None);
        }
        if arrow.borrows.parameters.len() == written {
            arrow
                .borrows
                .parameters
                .resize(arrow.parameters.len(), None);
        }
        if arrow.borrows.parameter_leaves.len() == written {
            arrow
                .borrows
                .parameter_leaves
                .resize(arrow.parameters.len(), vec![]);
        }
    }
    Ok(copies)
}

/// The resumptive declared operations performed by name somewhere that the
/// row of arrow `id` names, in id order.
fn row_operations(program: &Executable, arrows: &BTreeMap<usize, usize>, id: usize) -> Vec<usize> {
    let effects = program.function_types[id].effects;
    arrows
        .keys()
        .copied()
        .filter(|&operation| {
            program
                .effect_bits
                .get(operation)
                .is_some_and(|bit| *bit != 0 && effects & bit != 0)
        })
        .collect()
}

/// The resumptive declared operations whose capabilities a value of each
/// arrow type takes after its written parameters (rule 4). An arrow keeps the
/// dynamic stack when a value with its set of operations reaches code that
/// calls it without capabilities: a handler, a task or callback builtin, a
/// foreign function, or a function whose layout cannot take more parameters.
/// Coercions between arrows with different sets go through checked adapters,
/// so arrows with one set agree.
fn value_operations(program: &Executable, arrows: &BTreeMap<usize, usize>) -> Vec<Vec<usize>> {
    let operations = |ty: Type| -> Option<Vec<usize>> {
        let (Type::Fn(id) | Type::Once(id) | Type::Multi(id)) = ty else {
            return None;
        };
        let found = row_operations(program, arrows, id);
        (!found.is_empty()).then_some(found)
    };
    let mut pinned = BTreeSet::new();
    let mut pin = |ty: Type| {
        if let Some(found) = operations(ty) {
            pinned.insert(found);
        }
    };
    fn walk(expr: &Expr, program: &Executable, pin: &mut dyn FnMut(Type)) {
        match &expr.kind {
            ExprKind::HandlerPush { handler, .. } | ExprKind::AbortScope { handler, .. } => {
                pin(handler.ty)
            }
            ExprKind::Suspend { call, .. } => {
                if let ExprKind::CallIndirect { callee, .. } = &call.kind {
                    pin(callee.ty);
                }
            }
            ExprKind::VecMap { callbacks, .. } => {
                for callback in callbacks {
                    pin(callback.ty);
                }
            }
            ExprKind::TaskScope { body, .. } | ExprKind::TaskSpawn { body, .. } => pin(body.ty),
            ExprKind::Call(Target::Function(callee), arguments)
                if program.foreign_functions[*callee].is_some() =>
            {
                for argument in arguments {
                    pin(argument.ty);
                }
            }
            ExprKind::Call(
                Target::Function(_) | Target::DynCall { .. } | Target::UnionBorrowCall { .. },
                _,
            ) => {}
            ExprKind::Call(_, arguments) => {
                for argument in arguments {
                    pin(argument.ty);
                }
            }
            ExprKind::FnValue { function, .. } => {
                let source = &program.functions[*function];
                if source.parameter_slots.is_some()
                    || program.foreign_functions[*function].is_some()
                {
                    pin(expr.ty);
                }
            }
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, program, pin));
    }
    for function in &program.functions {
        for statement in &function.body.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                walk(value, program, &mut pin);
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, program, &mut pin);
        }
    }
    (0..program.function_types.len())
        .map(|id| {
            operations(Type::Fn(id))
                .filter(|found| !pinned.contains(found))
                .unwrap_or_default()
        })
        .collect()
}

fn collect_arrows(block: &Block, arrows: &mut BTreeMap<usize, usize>) {
    fn walk(expr: &Expr, arrows: &mut BTreeMap<usize, usize>) {
        if let ExprKind::DynamicPerform {
            operation, handler, ..
        } = &expr.kind
        {
            arrows.entry(*operation).or_insert(*handler);
        }
        expr.for_each_child(&mut |child| walk(child, arrows));
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, arrows);
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, arrows);
    }
}

/// A noncapturing `fn(P, token) -> R` performing `operation` through the
/// dynamic stack: the capability of a handler that lives in its frame.
fn trampoline(program: &mut Executable, operation: usize, arrow: usize) -> (usize, Type) {
    let parameters = program.function_types[arrow].parameters.clone();
    let result = program.function_types[arrow].result;
    let span = program.functions[0].span;
    let local = |slot: usize| Expr {
        kind: ExprKind::Local(slot),
        ty: parameters[slot],
        span,
        resource: None,
    };
    let body = Block {
        statements: vec![],
        tail: Some(Box::new(Expr {
            kind: ExprKind::DynamicPerform {
                operation,
                payload: Box::new(local(0)),
                resume: Box::new(local(1)),
                handler: arrow,
            },
            ty: result,
            span,
            resource: None,
        })),
        ty: result,
    };
    let mut function = program.functions[0].clone();
    function.name = "<capability trampoline>".to_owned();
    function.parameters = parameters.len();
    function.closure = None;
    function.capture_refs = vec![];
    function.capture_writes = vec![];
    function.locals = parameters
        .iter()
        .enumerate()
        .map(|(index, ty)| Local {
            ty: *ty,
            mutable: false,
            linear: index == 1,
            pinned: false,
            grade: None,
            span,
        })
        .collect();
    function.result = result;
    function.body = body;
    function.span = span;
    function.resources = vec![];
    function.local_resources = vec![None; parameters.len()];
    function.parameter_grades = vec![None; parameters.len()];
    function.result_grade = None;
    function.parameter_lifetimes = vec![None; parameters.len()];
    function.result_lifetime = None;
    function.lifetime_bounds = BTreeSet::new();
    function.declared_lifetimes = BTreeSet::new();
    function.index_relations = BTreeSet::new();
    function.parameter_slots = None;
    function.local_borrowed = vec![];
    function.local_copyable = vec![];
    function.capability_parameters = vec![];
    function.shared_environment = false;
    let index = program.functions.len();
    program.functions.push(function);
    program.foreign_functions.push(None);
    (index, Type::Fn(arrow))
}
