//! Second-class rules for multishot resumption tokens (`multi fn`,
//! docs/multishot-capabilities.md section 4).
//!
//! A token's environment lives on the task's continuation stack and is
//! released when the token call or `handle` that pushed it returns. That is
//! sound only if no token outlives such a call, so a token may be a local, a
//! parameter, an argument or a callee, and nothing else: it is never
//! returned, stored in a field, element or union member, captured by a
//! closure, or graded. This pass checks those rules on the checked IR,
//! before ownership and the suspension lowering (which adds its own rule: a
//! token is never live across a `perform`).

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    Diagnostic, Span,
    executable::{Executable, Expr, ExprKind, Statement, Type},
};

type Result<T> = std::result::Result<T, Diagnostic>;

/// Whether `ty` holds a token anywhere a token may not be. A token at the top
/// (`top`) is a local, parameter or argument; inside an arrow it may be a
/// parameter (a handler taking a token) but not the result. `seen` visits
/// each (type, position) once, so recursive types cost linear time.
fn misplaced(program: &Executable, ty: Type, top: bool, seen: &mut BTreeSet<(Type, bool)>) -> bool {
    if !seen.insert((ty, top)) {
        return false;
    }
    match ty {
        Type::Multi(id) => !top || arrow_misplaced(program, id, seen),
        Type::Fn(id) | Type::Once(id) => arrow_misplaced(program, id, seen),
        Type::Enum(id) | Type::Variants(id, _) => program.enums[id]
            .variants
            .iter()
            .flat_map(|variant| variant.fields.iter())
            .any(|field| misplaced(program, *field, false, seen)),
        Type::Union(id) => program.unions[id]
            .members
            .iter()
            .any(|member| misplaced(program, *member, false, seen)),
        Type::Box(p)
        | Type::Vec(p)
        | Type::Ref(p)
        | Type::RefMut(p)
        | Type::Slice(p)
        | Type::SliceMut(p)
        | Type::Annotated(p, _)
        | Type::ArenaBox(p)
        | Type::AllocBox(p)
        | Type::AllocVec(p)
        | Type::Task(p)
        | Type::Thread(p) => misplaced(program, program.pointees[p], false, seen),
        _ => false,
    }
}

fn arrow_misplaced(program: &Executable, id: usize, seen: &mut BTreeSet<(Type, bool)>) -> bool {
    let arrow = &program.function_types[id];
    arrow
        .parameters
        .iter()
        .any(|parameter| misplaced(program, *parameter, true, seen))
        || misplaced(program, arrow.result, false, seen)
}

/// `misplaced` from the top of one value, memoized per type.
struct Checker<'a> {
    program: &'a Executable,
    cache: BTreeMap<(Type, bool), bool>,
}

impl Checker<'_> {
    fn holds(&mut self, ty: Type, top: bool) -> bool {
        let program = self.program;
        *self
            .cache
            .entry((ty, top))
            .or_insert_with(|| misplaced(program, ty, top, &mut BTreeSet::new()))
    }

    fn expr(&mut self, expr: &Expr) -> Result<()> {
        if self.holds(expr.ty, true) {
            return Err(error(
                expr.span,
                &format!(
                    "it cannot be stored in a value of type {}",
                    self.program.type_name(expr.ty)
                ),
            ));
        }
        if let ExprKind::FnValue { captures, .. } = &expr.kind
            && let Some(capture) = captures
                .iter()
                .find(|capture| matches!(capture.ty, Type::Multi(_)))
        {
            return Err(error(capture.span, "a closure cannot capture it"));
        }
        let mut result = Ok(());
        expr.for_each_child(&mut |child| {
            if result.is_ok() {
                result = self.expr(child);
            }
        });
        result
    }
}

fn error(span: Span, what: &str) -> Diagnostic {
    Diagnostic::new(
        span,
        format!(
            "a multishot resumption token ('multi fn') is second-class: {what}. It may only be a local, a parameter, an argument, or called"
        ),
    )
}

pub(crate) fn check(program: &Executable) -> Result<()> {
    // Nothing to check in a program without token types.
    let names_tokens = program.function_types.iter().any(|arrow| {
        arrow
            .parameters
            .iter()
            .chain([&arrow.result])
            .any(|ty| matches!(ty, Type::Multi(_)))
    });
    if !names_tokens {
        return Ok(());
    }
    let mut checker = Checker {
        program,
        cache: BTreeMap::new(),
    };
    for function in &program.functions {
        if checker.holds(function.result, false) {
            return Err(error(function.span, "a function cannot return it"));
        }
        for local in &function.locals {
            if checker.holds(local.ty, true) {
                return Err(error(
                    local.span,
                    &format!(
                        "it cannot be stored in a value of type {}",
                        program.type_name(local.ty)
                    ),
                ));
            }
            if matches!(local.ty, Type::Multi(_)) && local.grade.is_some() {
                return Err(error(
                    local.span,
                    "it cannot carry a usage grade; copying and calling it are free",
                ));
            }
        }
        for statement in &function.body.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                checker.expr(value)?;
            }
        }
        if let Some(tail) = &function.body.tail {
            checker.expr(tail)?;
        }
    }
    Ok(())
}
