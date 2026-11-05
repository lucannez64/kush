//! Checked compile-time natural evaluation for array lengths and constant
//! indices.
//!
//! The evaluator is deliberately tiny and total:
//!
//! - literals, `N: Nat` const parameters in the current specialization, and
//!   nonnegative `+`/`-`/`*`/`/`/`%` over them;
//! - applications of *admitted total logical* definitions (checked by the
//!   trusted kernel) to constant natural arguments, normalized by the kernel;
//! - nothing else. Runtime locals, runtime functions, effectful code, and
//!   generic type parameters are never evaluated. `eval_expr` returns `None`
//!   for a genuinely runtime-dependent index so the caller can lower the
//!   existing checked dynamic read; array lengths instead reject such an
//!   expression because an inline layout needs a static size.
use crate::{
    Diagnostic, Span, ast,
    check::LogicalEnvironment,
    kernel::Term,
    natural::Natural,
    resolve::{BindingId, BindingKind, Resolution},
};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, Diagnostic>;
const MAX_NODES: usize = 256;

#[derive(Clone, Copy)]
pub(crate) enum Mode {
    /// An inline array length: must be statically known.
    Length,
    /// A constant index: `None` means "runtime-dependent, use a checked read".
    Index,
}

struct Evaluator<'a> {
    resolution: &'a Resolution,
    logical: &'a LogicalEnvironment,
    consts: &'a BTreeMap<BindingId, usize>,
    nodes: usize,
}

/// Evaluate a compile-time array length. Every failure is an error: an inline
/// array cannot have a guessed or runtime-dependent size.
pub(crate) fn eval_type(
    resolution: &Resolution,
    logical: &LogicalEnvironment,
    consts: &BTreeMap<BindingId, usize>,
    ty: &ast::Type,
) -> Result<usize> {
    let mut evaluator = Evaluator {
        resolution,
        logical,
        consts,
        nodes: 0,
    };
    evaluator.ty(ty)?.ok_or_else(|| {
        diagnostic(
            ty.span,
            Mode::Length,
            "must be a constant expression of nonnegative integer literals, const parameters, or total logical functions",
        )
    })
}

/// Evaluate a possibly-constant index expression. `Ok(None)` means the
/// expression is not compile-time constant, so the caller must use the
/// bounds-checked dynamic path. `Err` is reserved for an ill-formed,
/// negative, overflowing, or unbound constant expression.
pub(crate) fn eval_expr(
    resolution: &Resolution,
    logical: &LogicalEnvironment,
    consts: &BTreeMap<BindingId, usize>,
    expr: &ast::Expr,
) -> Result<Option<usize>> {
    let mut evaluator = Evaluator {
        resolution,
        logical,
        consts,
        nodes: 0,
    };
    evaluator.expr(expr)
}

impl Evaluator<'_> {
    fn charge(&mut self, span: Span, mode: Mode) -> Result<()> {
        self.nodes += 1;
        if self.nodes > MAX_NODES {
            return Err(diagnostic(
                span,
                mode,
                "exceeds the 256-node compile-time evaluation budget",
            ));
        }
        Ok(())
    }

    fn ty(&mut self, ty: &ast::Type) -> Result<Option<usize>> {
        self.charge(ty.span, Mode::Length)?;
        match &ty.kind {
            ast::TypeKind::Integer(text) => Ok(Some(self.literal(text, ty.span)?)),
            ast::TypeKind::Named { arguments, .. } => {
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    match self.ty(argument)? {
                        Some(value) => values.push(value),
                        None => {
                            return Err(diagnostic(
                                argument.span,
                                Mode::Length,
                                "contains a non-constant argument",
                            ));
                        }
                    }
                }
                self.name(ty.span, values, Mode::Length)
            }
            ast::TypeKind::Binary { op, left, right } => {
                let left = self.ty(left)?;
                let right = self.ty(right)?;
                match (left, right) {
                    (Some(left), Some(right)) => self.binary(op, left, right, ty.span).map(Some),
                    _ => Err(diagnostic(
                        ty.span,
                        Mode::Length,
                        "must be a constant expression of nonnegative integer literals, const parameters, or total logical functions",
                    )),
                }
            }
            _ => Err(diagnostic(
                ty.span,
                Mode::Length,
                "must be a constant expression of nonnegative integer literals, const parameters, or total logical functions",
            )),
        }
    }

    fn expr(&mut self, expr: &ast::Expr) -> Result<Option<usize>> {
        self.charge(expr.span, Mode::Index)?;
        match &expr.kind {
            ast::ExprKind::Integer(text) => Ok(Some(self.literal(text, expr.span)?)),
            ast::ExprKind::Name(_) => self.name(expr.span, Vec::new(), Mode::Index),
            ast::ExprKind::Specialize { callee, arguments } => {
                let Some(id) = self.resolution.reference(callee.span) else {
                    return Ok(None);
                };
                if !self.logical.names.contains_key(&id) {
                    return Ok(None);
                }
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    match self.ty(argument)? {
                        Some(value) => values.push(value),
                        None => return Ok(None),
                    }
                }
                self.apply(id, values, expr.span).map(Some)
            }
            ast::ExprKind::Call { callee, arguments } => {
                let base = match &callee.kind {
                    ast::ExprKind::Specialize { callee, arguments } => {
                        let Some(id) = self.resolution.reference(callee.span) else {
                            return Ok(None);
                        };
                        if !self.logical.names.contains_key(&id) {
                            return Ok(None);
                        }
                        let mut values = Vec::with_capacity(arguments.len());
                        for argument in arguments {
                            match self.ty(argument)? {
                                Some(value) => values.push(value),
                                None => return Ok(None),
                            }
                        }
                        values
                    }
                    _ => Vec::new(),
                };
                let Some(id) = self.resolution.reference(callee.span) else {
                    return Ok(None);
                };
                if !self.logical.names.contains_key(&id) {
                    return Ok(None);
                }
                let mut values = base;
                for argument in arguments {
                    match self.expr(argument)? {
                        Some(value) => values.push(value),
                        None => return Ok(None),
                    }
                }
                self.apply(id, values, expr.span).map(Some)
            }
            ast::ExprKind::Unary {
                op: crate::lexer::Kind::Minus,
                operand,
                ..
            } => match self.expr(operand)? {
                Some(0) => Ok(Some(0)),
                Some(_) => Err(diagnostic(expr.span, Mode::Index, "must be nonnegative")),
                None => Ok(None),
            },
            ast::ExprKind::Binary { op, left, right } => {
                let left = self.expr(left)?;
                let right = self.expr(right)?;
                match (left, right) {
                    (Some(left), Some(right)) => self.binary(op, left, right, expr.span).map(Some),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    fn literal(&self, text: &str, span: Span) -> Result<usize> {
        text.parse::<usize>().map_err(|_| {
            Diagnostic::new(
                span,
                "compile-time natural does not fit a machine size (usize)",
            )
        })
    }

    /// A length expression name: a const parameter in this specialization or
    /// a fully applied logical definition. Runtime bindings and type
    /// parameters are rejected instead of being treated as natural values.
    fn name(&mut self, span: Span, arguments: Vec<usize>, mode: Mode) -> Result<Option<usize>> {
        let Some(id) = self.resolution.reference(span) else {
            return Ok(None);
        };
        if let Some(value) = self.consts.get(&id) {
            if !arguments.is_empty() {
                return Err(Diagnostic::new(
                    span,
                    "a natural const parameter cannot take type arguments",
                ));
            }
            return Ok(Some(*value));
        }
        if self.logical.names.contains_key(&id) {
            return self.apply(id, arguments, span).map(Some);
        }
        let binding = &self.resolution.bindings[id];
        match binding.kind {
            BindingKind::Parameter | BindingKind::Local => match mode {
                Mode::Index => Ok(None),
                Mode::Length => Err(Diagnostic::new(
                    span,
                    "depends on a runtime value; give a runtime-length array an inline capacity as [T; n <= C], or use Vec<T> or a &[T] view",
                )),
            },
            BindingKind::Generic => Err(Diagnostic::new(
                span,
                "names a generic parameter that is not a natural const in this specialization; declare it as '<N: Nat>' and specialize the function or alias",
            )),
            _ => Ok(None),
        }
    }

    /// Apply an admitted total logical definition to already-evaluated natural
    /// arguments and normalize the resulting checked kernel term.
    fn apply(&self, id: BindingId, arguments: Vec<usize>, span: Span) -> Result<usize> {
        let name = self
            .logical
            .names
            .get(&id)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "only admitted total logical definitions may be used at compile time",
                )
            })?
            .clone();
        let mut term = Term::Global(name);
        for argument in arguments {
            let natural = Natural::from(u64::try_from(argument).map_err(|_| {
                Diagnostic::new(span, "compile-time natural does not fit a machine size")
            })?);
            term = Term::app(term, Term::natural(natural));
        }
        let normalized = self
            .logical
            .kernel
            .normalize_closed(&term)
            .map_err(|error| {
                Diagnostic::new(
                    span,
                    format!("compile-time logical normalization failed: {error}"),
                )
            })?;
        match normalized {
            Term::Zero => Ok(0),
            Term::Literal(value) => value.to_usize().ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "logical natural is not representable as a machine size (usize)",
                )
            }),
            _ => Err(Diagnostic::new(
                span,
                "compile-time logical definition did not normalize to a natural number",
            )),
        }
    }

    fn binary(
        &self,
        op: &crate::lexer::Kind,
        left: usize,
        right: usize,
        span: Span,
    ) -> Result<usize> {
        use crate::lexer::Kind;
        let invalid = || {
            Diagnostic::new(
                span,
                "is not a valid constant nonnegative integer expression (negative, division by zero, or arithmetic overflow)",
            )
        };
        match op {
            Kind::Plus => left.checked_add(right).ok_or_else(invalid),
            Kind::Minus => left.checked_sub(right).ok_or_else(invalid),
            Kind::Star => left.checked_mul(right).ok_or_else(invalid),
            Kind::Slash => left.checked_div(right).ok_or_else(invalid),
            Kind::Percent => left.checked_rem(right).ok_or_else(invalid),
            _ => Err(Diagnostic::new(
                span,
                "this operator is not part of the compile-time natural fragment",
            )),
        }
    }
}

fn diagnostic(span: Span, mode: Mode, detail: &str) -> Diagnostic {
    let subject = match mode {
        Mode::Length => "array length",
        Mode::Index => "array index",
    };
    Diagnostic::new(span, format!("{subject} {detail}"))
}
