//! Declared operations as hidden capability parameters for direct calls
//! (FND-HANDLERS-ONE-PARAMS, docs/one-handler-model.md section 2).
//!
//! A function that may perform declared operations it does not handle gets a
//! copy taking one more `cap Op` parameter per such operation, after its
//! written parameters and in operation-id order. In that copy a perform by
//! name with no enclosing `handle Op` of its own calls the parameter, and a
//! direct call passes, per operation of the callee, the innermost enclosing
//! `handle Op` of the caller or the caller's own parameter. Calls from code
//! that has neither (closures, function values, tasks, entry points) keep the
//! original function, which still performs through the dynamic stack; so
//! does a handler that is capturing, which is reached through the dynamic
//! frame by a trampoline. An await point under a handler with code after
//! `resume` then resumes the copy through its capability parameter.
use super::{Result, performs};
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
    originals: usize,
    /// Copy index of each copied original, in request order.
    copies: BTreeMap<usize, usize>,
    order: Vec<usize>,
    /// Trampolines through the dynamic stack, by operation.
    trampolines: &'a BTreeMap<usize, (usize, Type)>,
}

impl Pass<'_> {
    fn copy_of(&mut self, function: usize) -> usize {
        if let Some(copy) = self.copies.get(&function) {
            return *copy;
        }
        let copy = self.originals + self.order.len();
        self.order.push(function);
        self.copies.insert(function, copy);
        copy
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
                let supplied = self.needs[*callee]
                    .iter()
                    .map(|operation| {
                        scope.capabilities.get(operation).copied().or_else(|| {
                            scope.hidden.get(operation).map(|&slot| {
                                Capability::Local(slot, Type::Fn(self.arrows[operation]))
                            })
                        })
                    })
                    .collect::<Vec<_>>();
                if supplied.iter().all(Option::is_none) {
                    return;
                }
                let span = expr.span;
                for (operation, capability) in self.needs[*callee].iter().zip(supplied) {
                    arguments.push(match capability {
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
                    });
                }
                *callee = self.copy_of(*callee);
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

/// Add the copies and redirect direct calls to them.
pub(super) fn add(program: &mut Executable) -> Result<Hidden> {
    let originals = program.functions.len();
    let mut arrows = BTreeMap::new();
    for function in &program.functions {
        collect_arrows(&function.body, &mut arrows);
    }
    if arrows.is_empty() {
        return Ok(Hidden::new());
    }
    let performs = performs(program);
    let needs = (0..originals)
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
    if needs.iter().all(Vec::is_empty) {
        return Ok(Hidden::new());
    }
    let mut trampolines = BTreeMap::new();
    for (&operation, &arrow) in &arrows {
        trampolines.insert(operation, trampoline(program, operation, arrow));
    }
    let originals = program.functions.len();
    let mut needs = needs;
    needs.resize(originals, vec![]);
    let function_types = program.function_types.clone();
    let mut pass = Pass {
        needs: &needs,
        arrows: &arrows,
        function_types: &function_types,
        originals,
        copies: BTreeMap::new(),
        order: Vec::new(),
        trampolines: &trampolines,
    };
    for function in &mut program.functions[..originals] {
        pass.block(&mut function.body, &Scope::default());
    }
    let mut copies = Hidden::new();
    let mut next = 0;
    while next < pass.order.len() {
        let original = pass.order[next];
        let mut copy = program.functions[original].clone();
        let mut slots = (0..copy.parameters).collect::<Vec<_>>();
        let mut hidden = BTreeMap::new();
        for &operation in &needs[original] {
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
            copy.parameter_grades.resize(copy.parameters, None);
            copy.parameter_lifetimes.resize(copy.parameters, None);
            copy.parameter_grades.push(None);
            copy.parameter_lifetimes.push(None);
            copy.capability_parameters.push(slot);
            slots.push(slot);
            copy.parameters += 1;
            hidden.insert(operation, slot);
        }
        copy.parameter_slots = Some(slots);
        copies.insert(originals + next, hidden.clone());
        copy.name = format!("{}::capabilities", copy.name);
        let mut body = std::mem::replace(&mut copy.body, empty());
        pass.block(
            &mut body,
            &Scope {
                hidden,
                ..Scope::default()
            },
        );
        copy.body = body;
        program.functions.push(copy);
        program.foreign_functions.push(None);
        next += 1;
    }
    Ok(copies)
}

fn empty() -> Block {
    Block {
        statements: vec![],
        tail: None,
        ty: Type::Unit,
    }
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
