//! Finite recursive borrow-origin summaries.
//!
//! Lifetime inference for an elided borrowed result is a least fixed point over
//! the direct-call graph of declarations. A function result may derive from
//! parameter leaves (runtime parameter index plus a source field path) through
//! direct static calls. Concrete instances reuse the stable declaration-level
//! leaves and map them onto their own frozen lifetime labels; type substitution
//! does not change the lifetime parameters in this fragment. Summaries only
//! grow by union, so the finite declared fragment terminates; inference never
//! invents a lifetime name, equality, or `Never`.
//!
//! This module deliberately does not inspect the outlives SCC solver in
//! `crate::lifetimes`: those SCCs are lifetime-name equivalence classes. The
//! SCCs computed here are call-graph components over function declarations.
//!
//! Scope limits:
//! - Direct and lexically resolved static calls only. Indirect, dynamic, and
//!   method calls are unsupported boundaries: a summary that needs one keeps
//!   that `unknown` channel and is rejected unless the function has an
//!   explicit result lifetime. A caller of an explicit-result boundary still
//!   sees the preserved `unknown` instead of an empty origin set.
//! - One root result slot (a borrowed slice, text view, or reference) is
//!   summarized. Borrowed-record field results keep their existing declared
//!   field lifetimes; this pass does not infer per-field result binders.
//! - An unseeded cycle is rejected unless every result path is syntactically
//!   returned from an explicit-result boundary. Merely containing an unrelated
//!   explicit-result call is not evidence for the returned value.
//! - This pass computes result-derived may-origins, not an independent
//!   required-precondition set `R[f]`. Bounds are exported only from the
//!   origins a result can actually return; independent caller requirements
//!   still need an explicit contract, and are never invented here.
//! - Aggregate budgets are checked errors, never partial successes:
//!   `MAX_ANALYSIS_STEPS` = 250_000 steps, `MAX_ORIGIN_FACTS` = 16_384 facts,
//!   `MAX_LOCAL_PASSES` = 64 local fixed-point passes.

use super::{Declared, Resolution, borrow_lifetime, type_lifetimes};
use crate::{Diagnostic, Span, ast, lexer::Kind, resolve::BindingId};
use std::collections::{BTreeMap, BTreeSet};

/// A stable borrow leaf: one runtime parameter plus the source field path that
/// reaches the borrowed value. The path is empty for a direct slice/reference
/// parameter. Field paths use source field names, matching
/// `collect_parameter_field_lifetimes`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Origin {
    pub parameter: usize,
    pub path: Vec<String>,
}

/// The result-origin summary of one declaration. `origins` is the union over
/// every normal return path; no alternative is dropped because a scalar
/// condition could prune it. `unknown` preserves an unsupported result channel
/// discovered in the body so a caller cannot read it as an empty (unrestricted)
/// provenance.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct FunctionSummary {
    pub origins: BTreeSet<Origin>,
    unknown: Option<Unsupported>,
}

/// Solved declaration summaries, sorted by binding for deterministic replay.
#[derive(Debug, Clone, Default)]
pub(super) struct Summaries {
    functions: BTreeMap<BindingId, FunctionSummary>,
}

impl Summaries {
    pub(super) fn get(&self, binding: BindingId) -> Option<&FunctionSummary> {
        self.functions.get(&binding)
    }
}

/// Aggregate work bound. The declared fragment is finite, but an unexpected
/// shape must fail with a checked diagnostic instead of looping.
const MAX_ANALYSIS_STEPS: usize = 250_000;
const MAX_ORIGIN_FACTS: usize = 16_384;
const MAX_LOCAL_PASSES: usize = 64;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Flow {
    /// Path-keyed origin sets. A root slice/reference value uses the empty path;
    /// a record value uses the paths of its fields.
    leaves: BTreeMap<Vec<String>, BTreeSet<Origin>>,
    /// A value in result position came from a channel this pass cannot follow.
    /// Carrying it to a result forces an explicit result contract instead of
    /// silently guessing an empty (unrestricted) provenance.
    unknown: Option<Unsupported>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Unsupported {
    span: Span,
    what: String,
}

impl Unsupported {
    fn precedes(&self, other: &Unsupported) -> bool {
        (self.span.start, self.span.end, &self.what)
            < (other.span.start, other.span.end, &other.what)
    }
}

impl Flow {
    fn empty() -> Self {
        Self::default()
    }
    fn root(origins: BTreeSet<Origin>) -> Self {
        let mut leaves = BTreeMap::new();
        if !origins.is_empty() {
            leaves.insert(Vec::new(), origins);
        }
        Self {
            leaves,
            unknown: None,
        }
    }
    fn unknown(span: Span, what: impl Into<String>) -> Self {
        Self {
            leaves: BTreeMap::new(),
            unknown: Some(Unsupported {
                span,
                what: what.into(),
            }),
        }
    }
    /// Construct a record/struct literal: each field value keeps its parameter
    /// origins and gains one relative path component. This does not change
    /// `Origin::path` because the stored value is still the same parameter leaf.
    fn extend(&self, fields: &[String]) -> Self {
        let mut leaves = BTreeMap::new();
        for (path, origins) in &self.leaves {
            let mut key = fields.to_vec();
            key.extend(path.iter().cloned());
            leaves.insert(key, origins.clone());
        }
        Self {
            leaves,
            unknown: self.unknown.clone(),
        }
    }
    /// Project one record field. Relative field keys select the matching
    /// subvalue; a whole-value root origin gains the field on its parameter leaf
    /// path so the instance mapper can see the actual declared lifetime.
    fn project(&self, field: &str) -> Self {
        let mut leaves = BTreeMap::new();
        for (path, origins) in &self.leaves {
            if path.first().is_some_and(|first| first == field) {
                leaves
                    .entry(path[1..].to_vec())
                    .or_insert_with(BTreeSet::new)
                    .extend(origins.iter().cloned());
            } else if path.is_empty() {
                leaves
                    .entry(Vec::new())
                    .or_insert_with(BTreeSet::new)
                    .extend(origins.iter().map(|origin| {
                        Origin {
                            parameter: origin.parameter,
                            path: origin
                                .path
                                .iter()
                                .cloned()
                                .chain(std::iter::once(field.to_owned()))
                                .collect(),
                        }
                    }));
            }
        }
        Self {
            leaves,
            unknown: self.unknown.clone(),
        }
    }
    fn merge(&mut self, other: Flow) {
        for (path, origins) in other.leaves {
            self.leaves.entry(path).or_default().extend(origins);
        }
        if let Some(unknown) = other.unknown {
            self.unknown = Some(match self.unknown.take() {
                Some(current) if current.precedes(&unknown) => current,
                Some(_) | None => unknown,
            });
        }
    }
    /// All origins carried by this flow, regardless of field path. Used when a
    /// callee origin has no field path or when returning a whole value.
    fn all_origins(&self) -> BTreeSet<Origin> {
        self.leaves
            .values()
            .flat_map(|origins| origins.iter().cloned())
            .collect()
    }
    /// Origins selected for a callee parameter leaf path. An actual value with
    /// a matching field leaf supplies it directly; a whole-record actual value
    /// supplies the nested path through its root origin; a more specific actual
    /// subfield still names caller-owned storage inside the requested path.
    ///
    /// A non-empty path that matches no actual leaf is a mismatch, not an empty
    /// provenance: it requests an explicit contract instead of silently
    /// dropping the callee's origin. The work budget is reported separately so
    /// the caller can turn it into a checked diagnostic.
    fn select(
        &self,
        path: &[String],
        out: &mut BTreeSet<Origin>,
        work: &mut usize,
    ) -> Result<(), SelectFailure> {
        if path.is_empty() {
            out.extend(self.all_origins());
            return if self.unknown.is_none() {
                Ok(())
            } else {
                Err(SelectFailure::Missing)
            };
        }
        let mut matched = false;
        for (actual_path, origins) in &self.leaves {
            *work = work.saturating_add(1);
            if *work > MAX_ANALYSIS_STEPS {
                return Err(SelectFailure::Budget);
            }
            if actual_path == path {
                out.extend(origins.iter().cloned());
                matched = true;
            } else if actual_path.is_empty() {
                out.extend(origins.iter().map(|origin| {
                    Origin {
                        parameter: origin.parameter,
                        path: origin
                            .path
                            .iter()
                            .cloned()
                            .chain(path.iter().cloned())
                            .collect(),
                    }
                }));
                matched = true;
            } else if path.starts_with(actual_path) {
                out.extend(origins.iter().map(|origin| {
                    Origin {
                        parameter: origin.parameter,
                        path: origin
                            .path
                            .iter()
                            .cloned()
                            .chain(path[actual_path.len()..].iter().cloned())
                            .collect(),
                    }
                }));
                matched = true;
            } else if actual_path.starts_with(path) {
                out.extend(origins.iter().cloned());
                matched = true;
            }
        }
        if self.unknown.is_some() || !matched {
            Err(SelectFailure::Missing)
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SelectFailure {
    /// The actual value has no leaf for the callee's declared field path.
    Missing,
    /// `MAX_ANALYSIS_STEPS` was exceeded while matching leaves.
    Budget,
}

struct Solver<'a, 'r> {
    resolution: &'r Resolution,
    declared: &'r BTreeMap<BindingId, Declared<'a>>,
    summaries: BTreeMap<BindingId, FunctionSummary>,
    edges: BTreeMap<BindingId, BTreeSet<BindingId>>,
    /// Source offsets of each direct call edge, for diagnostics. `Span` has no
    /// total order, so the stored pair is `(start, end)`.
    edge_sites: BTreeMap<(BindingId, BindingId), BTreeSet<(usize, usize)>>,
    steps: usize,
    facts: usize,
}

impl<'a, 'r> Solver<'a, 'r> {
    fn new(resolution: &'r Resolution, declared: &'r BTreeMap<BindingId, Declared<'a>>) -> Self {
        Self {
            resolution,
            declared,
            summaries: BTreeMap::new(),
            edges: BTreeMap::new(),
            edge_sites: BTreeMap::new(),
            steps: 0,
            facts: 0,
        }
    }
    fn charge(&mut self, span: Span) -> Result<(), Diagnostic> {
        self.steps = self.steps.saturating_add(1);
        if self.steps > MAX_ANALYSIS_STEPS {
            return Err(Diagnostic::new(
                span,
                "recursive lifetime inference exceeded its finite work budget; simplify the recursive lifetime contract or annotate the result lifetime explicitly",
            ));
        }
        Ok(())
    }
    fn charge_fact(&mut self, span: Span) -> Result<(), Diagnostic> {
        self.facts = self.facts.saturating_add(1);
        if self.facts > MAX_ORIGIN_FACTS {
            return Err(Diagnostic::new(
                span,
                "recursive lifetime inference exceeded its finite fact budget; annotate the result lifetime explicitly or reduce the number of borrowed call-graph leaves",
            ));
        }
        Ok(())
    }
    fn runtime_parameters(f: &ast::Function) -> Vec<(usize, &ast::Parameter)> {
        f.parameters
            .iter()
            .filter(|parameter| !parameter.erased)
            .enumerate()
            .collect()
    }
    /// The source argument for one runtime parameter index. Calls keep erased
    /// proof positions in the AST argument list, so a runtime index must skip
    /// those positions instead of indexing the AST list directly. A missing
    /// position is an unsupported call shape, not argument zero.
    fn runtime_argument<'e>(
        declared: &Declared<'a>,
        arguments: &'e [ast::Expr],
        runtime_index: usize,
    ) -> Option<&'e ast::Expr> {
        let mut runtime = 0usize;
        for (position, parameter) in declared.ast.parameters.iter().enumerate() {
            if parameter.erased {
                continue;
            }
            if runtime == runtime_index {
                return arguments.get(position);
            }
            runtime = runtime.saturating_add(1);
        }
        None
    }
    /// Whether the written result is a borrowed slice/text view/reference. Only
    /// these root result slots are summarized here.
    fn has_borrowed_result(f: &ast::Function) -> bool {
        matches!(
            &crate::grades::split(&f.result).0.kind,
            ast::TypeKind::Borrow { .. }
        )
    }
    /// Number of independent direct input borrow lifetimes. Record-field
    /// lifetimes are validated by the ordinary inference: their declared names
    /// may include phantom parameters, so counting names here would reject a
    /// single real leaf as if it were ambiguous. A direct elided borrow counts
    /// once; declared names are deduplicated.
    fn input_lifetime_count(f: &ast::Function) -> usize {
        let mut names = BTreeSet::new();
        let mut elided = 0usize;
        for parameter in f.parameters.iter().filter(|parameter| !parameter.erased) {
            let ty = crate::grades::split(&parameter.ty).0;
            if let ast::TypeKind::Borrow { lifetime, .. } = &ty.kind {
                match lifetime {
                    Some(name) => {
                        names.insert(name.clone());
                    }
                    None => elided += 1,
                }
            }
        }
        names.len() + elided
    }
    /// Whether any runtime input type can carry a borrow at all, including a
    /// borrowed record field. A no-input elided borrowed result is already
    /// rejected by the ordinary "cannot be returned" rule, so an unsupported
    /// channel there must not replace the more precise existing diagnostic.
    fn input_has_borrow_shape(f: &ast::Function) -> bool {
        fn mentioned(ty: &ast::Type) -> bool {
            match &ty.kind {
                ast::TypeKind::Borrow { .. } => true,
                ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
                    arguments.iter().any(mentioned)
                }
                ast::TypeKind::Slice(inner)
                | ast::TypeKind::Array(inner, _)
                | ast::TypeKind::Dyn(inner) => mentioned(inner),
                ast::TypeKind::Structural { fields, .. } => {
                    fields.iter().any(|field| mentioned(&field.ty))
                }
                ast::TypeKind::Graded { inner, .. } => mentioned(inner),
                _ => false,
            }
        }
        f.parameters
            .iter()
            .filter(|parameter| !parameter.erased)
            .any(|parameter| mentioned(crate::grades::split(&parameter.ty).0))
    }
    fn seed_locals(
        &self,
        f: &ast::Function,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) -> Result<(), Diagnostic> {
        for (index, parameter) in Self::runtime_parameters(f) {
            let Some(binding) = self.resolution.binder(parameter.span) else {
                continue;
            };
            let mut origins = BTreeSet::new();
            origins.insert(Origin {
                parameter: index,
                path: Vec::new(),
            });
            locals.insert(binding, Flow::root(origins));
        }
        Ok(())
    }
    fn callee_binding(&self, callee: &ast::Expr) -> Option<BindingId> {
        match &callee.kind {
            ast::ExprKind::Name(_) => self.resolution.reference(callee.span),
            ast::ExprKind::Specialize { callee, .. } => self.callee_binding(callee),
            _ => None,
        }
    }
    /// Flow of one expression in result position.
    fn expr_flow(
        &mut self,
        expr: &ast::Expr,
        locals: &BTreeMap<BindingId, Flow>,
    ) -> Result<Flow, Diagnostic> {
        self.charge(expr.span)?;
        use ast::ExprKind as K;
        match &expr.kind {
            K::Name(_) => Ok(self
                .resolution
                .reference(expr.span)
                .and_then(|binding| locals.get(&binding).cloned())
                .unwrap_or_else(Flow::empty)),
            K::Field { value, name } => {
                let flow = self.expr_flow(value, locals)?;
                Ok(flow.project(name))
            }
            K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. } => self.expr_flow(value, locals),
            K::Block(block) => self.block_flow(block, locals),
            K::If {
                then, otherwise, ..
            } => {
                let mut flow = self.block_flow(then, locals)?;
                if let Some(otherwise) = otherwise {
                    flow.merge(self.expr_flow(otherwise, locals)?);
                }
                Ok(flow)
            }
            K::Match { arms, .. } => {
                let mut flow = Flow::empty();
                for arm in arms {
                    flow.merge(self.expr_flow(&arm.body, locals)?);
                }
                Ok(flow)
            }
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                let mut flow = Flow::empty();
                for (name, value) in fields {
                    flow.merge(
                        self.expr_flow(value, locals)?
                            .extend(std::slice::from_ref(name)),
                    );
                }
                Ok(flow)
            }
            K::Tuple(values) | K::Array(values) => {
                let mut flow = Flow::empty();
                for value in values {
                    flow.merge(self.expr_flow(value, locals)?);
                }
                Ok(flow)
            }
            K::Call { callee, arguments } => self.call_flow(callee, arguments, locals, expr.span),
            K::Return(Some(value)) | K::Break(Some(value)) => self.expr_flow(value, locals),
            K::Return(None) | K::Break(None) | K::Continue => Ok(Flow::empty()),
            K::Lambda(_) | K::Specialize { .. } => Ok(Flow::empty()),
            K::Handle { body, .. } => self.block_flow(body, locals),
            K::While { .. } | K::Loop(_) => Ok(Flow::unknown(
                expr.span,
                "a loop result is not followed by recursive lifetime inference",
            )),
            K::Perform { .. } => Ok(Flow::unknown(
                expr.span,
                "a performed operation result is not followed by recursive lifetime inference",
            )),
            // Scalars, literals, and pure scalar operations cannot carry a
            // borrow origin.
            K::Integer(_)
            | K::Float(_)
            | K::String(_)
            | K::Char(_)
            | K::Bool(_)
            | K::Binary { .. } => Ok(Flow::empty()),
        }
    }
    fn call_flow(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        locals: &BTreeMap<BindingId, Flow>,
        span: Span,
    ) -> Result<Flow, Diagnostic> {
        let Some(binding) = self.callee_binding(callee) else {
            return Ok(Flow::unknown(
                span,
                "an indirect, dynamic, method, or unresolved call in result position requires an explicit checked contract",
            ));
        };
        let Some(declared) = self.declared.get(&binding) else {
            return Ok(Flow::unknown(
                span,
                "a call to a non-function or erased definition in result position requires an explicit checked contract",
            ));
        };
        let Some(summary) = self.summaries.get(&binding).cloned() else {
            // A declaration with a borrowed result is summarized (possibly
            // empty before the first iteration). Anything else can only be a
            // non-borrowed scalar result; a record that carries borrows is an
            // unsupported boundary for this root-slot fragment. The written
            // shape matters here: an elided `&[T]` mentions no named lifetime,
            // but it is still a borrowed shape and must never look scalar.
            let mut mentioned = BTreeSet::new();
            type_lifetimes(crate::grades::split(&declared.ast.result).0, &mut mentioned);
            return Ok(
                if !Self::has_borrowed_result(declared.ast) && mentioned.is_empty() {
                    Flow::empty()
                } else {
                    Flow::unknown(
                        span,
                        "a call returning a borrowed result without a summary is not part of the root-slot recursive fragment; annotate the result lifetime",
                    )
                },
            );
        };
        let callee_name = declared.ast.name.clone();
        let mut out = BTreeSet::new();
        let mut unknown = None;
        for origin in &summary.origins {
            let Some(argument) = Self::runtime_argument(declared, arguments, origin.parameter)
            else {
                unknown = Some(Unsupported {
                    span,
                    what: format!(
                        "a summary origin names runtime parameter {} but the call has no corresponding source argument",
                        origin.parameter
                    ),
                });
                continue;
            };
            let flow = self.expr_flow(argument, locals)?;
            if flow.unknown.is_some() {
                unknown = Some(Unsupported {
                    span: argument.span,
                    what: "a borrowed call argument comes from an unsupported boundary; annotate the result lifetime"
                        .to_owned(),
                });
                continue;
            }
            let mut selected = BTreeSet::new();
            match flow.select(&origin.path, &mut selected, &mut self.steps) {
                Ok(()) => {}
                Err(SelectFailure::Missing) => {
                    unknown = Some(Unsupported {
                        span: argument.span,
                        what: format!(
                            "a borrowed call argument does not expose the callee result's field path '{}'; annotate the result lifetime or route the value through a direct checked function",
                            origin.path.join(".")
                        ),
                    });
                    continue;
                }
                Err(SelectFailure::Budget) => {
                    return Err(Diagnostic::new(
                        span,
                        "recursive lifetime inference exceeded its finite work budget while substituting a call summary",
                    ));
                }
            }
            for selected in selected {
                if out.insert(selected) {
                    self.charge_fact(span)?;
                }
            }
        }
        if let Some(summary_unknown) = &summary.unknown {
            let candidate = Unsupported {
                span,
                what: format!(
                    "a call to '{callee_name}' returns through an unsupported result channel: {}",
                    summary_unknown.what
                ),
            };
            unknown = Some(match unknown.take() {
                Some(current) if current.precedes(&candidate) => current,
                Some(_) | None => candidate,
            });
        }
        let mut flow = Flow::root(out);
        flow.unknown = unknown;
        Ok(flow)
    }
    fn block_flow(
        &mut self,
        block: &ast::Block,
        locals: &BTreeMap<BindingId, Flow>,
    ) -> Result<Flow, Diagnostic> {
        let mut flow = Flow::empty();
        let mut returns = Vec::new();
        block_returns(block, &mut returns);
        for value in returns {
            flow.merge(self.expr_flow(value, locals)?);
        }
        if let Some(tail) = &block.tail {
            flow.merge(self.expr_flow(tail, locals)?);
        }
        Ok(flow)
    }
    /// Bind `let` patterns and record assignments until local origin sets stop
    /// growing. This is the finite local half of the same union lattice. The
    /// pass cap is a checked error: returning the last partial walk as success
    /// would publish a summary that silently dropped a local origin.
    fn analyze_locals(
        &mut self,
        f: &ast::Function,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) -> Result<(), Diagnostic> {
        self.seed_locals(f, locals)?;
        let Some(body) = &f.body else {
            return Ok(());
        };
        let span = f.result.span;
        run_local_fixed_point(MAX_LOCAL_PASSES, span, || {
            let before = locals.clone();
            self.walk_block(body, locals)?;
            Ok(*locals == before)
        })
    }
    fn walk_block(
        &mut self,
        block: &ast::Block,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) -> Result<(), Diagnostic> {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { pattern, value, .. } => {
                    let flow = self.expr_flow(value, locals)?;
                    self.bind_pattern(pattern, &flow, locals);
                    self.walk_expr(value, locals)?;
                }
                ast::Statement::Expr(value) => self.walk_expr(value, locals)?,
            }
        }
        if let Some(tail) = &block.tail {
            self.walk_expr(tail, locals)?;
        }
        Ok(())
    }
    fn walk_expr(
        &mut self,
        expr: &ast::Expr,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) -> Result<(), Diagnostic> {
        self.charge(expr.span)?;
        use ast::ExprKind as K;
        match &expr.kind {
            K::Binary {
                op: Kind::Eq,
                left,
                right,
            } if matches!(left.kind, K::Name(_)) => {
                let flow = self.expr_flow(right, locals)?;
                if let Some(binding) = self.resolution.reference(left.span)
                    && let Some(existing) = locals.get_mut(&binding)
                {
                    existing.merge(flow);
                }
                self.walk_expr(right, locals)
            }
            K::Block(block) => self.walk_block(block, locals),
            K::If {
                then, otherwise, ..
            } => {
                self.walk_block(then, locals)?;
                if let Some(otherwise) = otherwise {
                    self.walk_expr(otherwise, locals)?;
                }
                Ok(())
            }
            K::Match { arms, .. } => {
                for arm in arms {
                    self.walk_expr(&arm.body, locals)?;
                }
                Ok(())
            }
            K::While { body, .. } | K::Loop(body) => self.walk_block(body, locals),
            K::Handle { body, .. } => self.walk_block(body, locals),
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                for (_, value) in fields {
                    self.walk_expr(value, locals)?;
                }
                Ok(())
            }
            K::Tuple(values) | K::Array(values) => {
                for value in values {
                    self.walk_expr(value, locals)?;
                }
                Ok(())
            }
            K::Specialize { callee: value, .. }
            | K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value)) => self.walk_expr(value, locals),
            K::Binary { left, right, .. } => {
                self.walk_expr(left, locals)?;
                self.walk_expr(right, locals)
            }
            K::Call { callee, arguments } => {
                self.walk_expr(callee, locals)?;
                for argument in arguments {
                    self.walk_expr(argument, locals)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    fn bind_pattern(
        &self,
        pattern: &ast::Pattern,
        flow: &Flow,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) {
        use ast::PatternKind as P;
        match &pattern.kind {
            P::Name(_) => {
                if let Some(binding) = self.resolution.binder(pattern.span) {
                    locals.entry(binding).or_default().merge(flow.clone());
                    if let Some(unknown) = &flow.unknown {
                        locals.get_mut(&binding).unwrap().unknown = Some(unknown.clone());
                    }
                }
            }
            P::Record { fields, .. } | P::Structural { fields, .. } => {
                for (name, subpattern) in fields {
                    let field_flow = flow.project(name);
                    self.bind_pattern(subpattern, &field_flow, locals);
                }
            }
            P::Tuple(patterns) => {
                for subpattern in patterns {
                    self.bind_pattern(subpattern, flow, locals);
                }
            }
            P::Type { inner, .. } => self.bind_pattern(inner, flow, locals),
            P::Or(patterns) => {
                for pattern in patterns {
                    self.bind_pattern(pattern, flow, locals);
                }
            }
            _ => {}
        }
    }
    fn collect_edges(&mut self, binding: BindingId, block: &ast::Block) -> Result<(), Diagnostic> {
        let mut found = BTreeSet::new();
        collect_direct_calls(self.resolution, self.declared, block, &mut found);
        for (callee, start, end) in found {
            self.edges.entry(binding).or_default().insert(callee);
            self.edge_sites
                .entry((binding, callee))
                .or_default()
                .insert((start, end));
        }
        Ok(())
    }
    fn solve(&mut self) -> Result<(), Diagnostic> {
        // Seed one summary slot per declaration with a borrowed result. The
        // least fixed point starts empty: a cycle with no base return stays
        // empty and is rejected below instead of bootstrapping "any input".
        for (binding, declared) in self.declared {
            if declared.ast.body.is_some() && Self::has_borrowed_result(declared.ast) {
                self.summaries.insert(*binding, FunctionSummary::default());
            }
        }
        for (binding, declared) in self.declared {
            if let Some(body) = &declared.ast.body {
                self.collect_edges(*binding, body)?;
            }
        }
        // Deterministic order by source name, then binding. The least fixed
        // point is unique; sorting only makes iteration and diagnostics stable.
        let mut order = self.summaries.keys().copied().collect::<Vec<_>>();
        order.sort_by(|a, b| {
            self.declared[a]
                .ast
                .name
                .cmp(&self.declared[b].ast.name)
                .then_with(|| a.cmp(b))
        });
        loop {
            let mut changed = false;
            for binding in &order {
                let declared = self.declared[binding];
                let Some(body) = &declared.ast.body else {
                    continue;
                };
                let mut locals = BTreeMap::new();
                self.analyze_locals(declared.ast, &mut locals)?;
                let flow = self.block_flow(body, &locals)?;
                let origins = flow.all_origins();
                let summary = FunctionSummary {
                    origins,
                    unknown: flow.unknown.clone(),
                };
                let previous = self.summaries[binding].clone();
                if summary != previous {
                    self.summaries.insert(*binding, summary);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        self.diagnose()
    }
    /// Whether a direct call target has an explicit borrowed result contract.
    fn explicit_result_call(&self, callee: &ast::Expr) -> bool {
        self.callee_binding(callee).is_some_and(|binding| {
            self.declared.get(&binding).is_some_and(|declared| {
                Self::has_borrowed_result(declared.ast)
                    && borrow_lifetime(crate::grades::split(&declared.ast.result).0).is_some()
            })
        })
    }
    /// Evidence that a returned value is syntactically a call through an
    /// explicit-result boundary. An unrelated explicit call elsewhere in the
    /// body is not evidence; every result-producing path must carry it. This
    /// only suppresses the unseeded-cycle error, it never invents an origin.
    fn result_evidence(&self, expr: &ast::Expr) -> bool {
        use ast::ExprKind as K;
        match &expr.kind {
            K::Call { callee, .. } => self.explicit_result_call(callee),
            K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value)) => self.result_evidence(value),
            K::Block(block) => self.block_result_evidence(block),
            K::If {
                then, otherwise, ..
            } => {
                self.block_result_evidence(then)
                    && otherwise
                        .as_ref()
                        .is_some_and(|otherwise| self.result_evidence(otherwise))
            }
            K::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|arm| self.result_evidence(&arm.body))
            }
            _ => false,
        }
    }
    fn block_result_evidence(&self, block: &ast::Block) -> bool {
        let mut returns = Vec::new();
        block_returns(block, &mut returns);
        let tail = block
            .tail
            .as_ref()
            .is_some_and(|tail| self.result_evidence(tail));
        let tail_ok = if block.tail.is_some() {
            tail
        } else {
            !returns.is_empty()
        };
        returns.iter().all(|value| self.result_evidence(value)) && tail_ok
    }
    fn diagnose(&mut self) -> Result<(), Diagnostic> {
        let sccs = self.sccs();
        let mut errors = Vec::new();
        for group in &sccs {
            let cyclic = group.len() > 1
                || self
                    .edges
                    .get(&group[0])
                    .is_some_and(|edges| edges.contains(&group[0]));
            // Recompute the same flows once to distinguish a legitimate empty
            // base from an unsupported boundary. Acyclic declarations are
            // checked too: an unsupported channel must not become an empty
            // provenance at their callers just because the declaration does not
            // participate in a cycle.
            for binding in group {
                let declared = self.declared[binding];
                if !Self::has_borrowed_result(declared.ast)
                    || borrow_lifetime(crate::grades::split(&declared.ast.result).0).is_some()
                {
                    // An explicit result contract is parametric forwarding; it
                    // is validated by the ownership pass, not inferred here.
                    continue;
                }
                let Some(body) = &declared.ast.body else {
                    continue;
                };
                let mut locals = BTreeMap::new();
                self.analyze_locals(declared.ast, &mut locals)?;
                let flow = self.block_flow(body, &locals)?;
                if let Some(unknown) = &flow.unknown {
                    // A no-input elided result already has a more precise
                    // "cannot be returned" rejection in the ordinary pass. For
                    // an acyclic declaration a single input lifetime already
                    // fixes the result provenance, so the existing pass keeps
                    // its more specific mutability/escape diagnostic. Multiple
                    // independent inputs are where an empty summary would
                    // silently choose no owner.
                    let report = if cyclic {
                        Self::input_has_borrow_shape(declared.ast)
                    } else {
                        Self::input_lifetime_count(declared.ast) > 1
                    };
                    if report {
                        errors.push((
                            declared.span,
                            self.unsupported_diagnostic(
                                *binding,
                                &unknown.what,
                                unknown.span,
                                group,
                            ),
                        ));
                    }
                } else if cyclic
                    && flow.all_origins().is_empty()
                    && Self::input_lifetime_count(declared.ast) > 1
                    && !self.block_result_evidence(body)
                {
                    // Only returned evidence from an explicit-result boundary
                    // is a parametric seed for the existing syntactic
                    // inference. An unrelated explicit call in the body cannot
                    // justify an otherwise unseeded cycle.
                    errors.push((declared.span, self.no_seed_diagnostic(*binding, group)));
                }
            }
        }
        errors.sort_by_key(|(span, _)| (span.start, span.end));
        if let Some((_, error)) = errors.into_iter().next() {
            return Err(error);
        }
        Ok(())
    }
    fn sccs(&self) -> Vec<Vec<BindingId>> {
        let nodes = self
            .declared
            .keys()
            .copied()
            .filter(|binding| self.declared[binding].ast.body.is_some())
            .collect::<Vec<_>>();
        let reachable = |start: BindingId| {
            let mut seen = BTreeSet::new();
            let mut stack = vec![start];
            while let Some(node) = stack.pop() {
                if !seen.insert(node) {
                    continue;
                }
                if let Some(next) = self.edges.get(&node) {
                    stack.extend(next.iter().rev().copied());
                }
            }
            seen
        };
        let reach = nodes
            .iter()
            .map(|node| (*node, reachable(*node)))
            .collect::<BTreeMap<_, _>>();
        let mut assigned = BTreeSet::new();
        let mut groups = Vec::new();
        let mut sorted = nodes.clone();
        sorted.sort_by(|a, b| {
            self.declared[a]
                .ast
                .name
                .cmp(&self.declared[b].ast.name)
                .then_with(|| a.cmp(b))
        });
        for node in sorted {
            if !assigned.insert(node) {
                continue;
            }
            let mut group = vec![node];
            for other in &nodes {
                if *other != node
                    && reach[&node].contains(other)
                    && reach[other].contains(&node)
                    && assigned.insert(*other)
                {
                    group.push(*other);
                }
            }
            group.sort_by(|a, b| {
                self.declared[a]
                    .ast
                    .name
                    .cmp(&self.declared[b].ast.name)
                    .then_with(|| a.cmp(b))
            });
            groups.push(group);
        }
        groups
    }
    fn cycle_notes(&self, group: &[BindingId]) -> Vec<(Span, String)> {
        let mut notes = Vec::new();
        for from in group {
            let Some(targets) = self.edges.get(from) else {
                continue;
            };
            for to in targets {
                if !group.contains(to) {
                    continue;
                }
                let from_name = &self.declared[from].ast.name;
                let to_name = &self.declared[to].ast.name;
                let sites = self
                    .edge_sites
                    .get(&(*from, *to))
                    .cloned()
                    .unwrap_or_default();
                if sites.is_empty() {
                    notes.push((
                        self.declared[to].span,
                        format!("recursive call edge '{from_name}' -> '{to_name}'"),
                    ));
                } else {
                    for (start, end) in sites {
                        notes.push((
                            Span::new(start, end),
                            format!("recursive call edge '{from_name}' -> '{to_name}'"),
                        ));
                    }
                }
            }
        }
        notes.sort_by(|a, b| (a.0.start, a.0.end, &a.1).cmp(&(b.0.start, b.0.end, &b.1)));
        notes.dedup();
        notes
    }
    fn no_seed_diagnostic(&self, binding: BindingId, group: &[BindingId]) -> Diagnostic {
        let name = &self.declared[&binding].ast.name;
        let mut error = Diagnostic::new(
            self.declared[&binding].span,
            format!(
                "cannot infer a recursive borrowed result lifetime for '{name}': this call-graph cycle has no independently justified result origin. Return a parameter-derived value on some path, or annotate the result lifetime explicitly"
            ),
        );
        for (span, note) in self.cycle_notes(group) {
            error = error.with_note(span, note);
        }
        error
    }
    fn unsupported_diagnostic(
        &self,
        binding: BindingId,
        what: &str,
        span: Span,
        group: &[BindingId],
    ) -> Diagnostic {
        let name = &self.declared[&binding].ast.name;
        let mut error = Diagnostic::new(
            span,
            format!(
                "recursive lifetime inference for '{name}' cannot use this result origin: {what}. Annotate the result lifetime explicitly or route the value through a direct checked function"
            ),
        );
        for (span, note) in self.cycle_notes(group) {
            error = error.with_note(span, note);
        }
        error
    }
}

/// Run one monotone local fixed-point loop. `pass` returns whether the state
/// did not change. Exhausting the exact pass budget is a checked error, never a
/// silent partial result.
fn run_local_fixed_point(
    max_passes: usize,
    span: Span,
    mut pass: impl FnMut() -> Result<bool, Diagnostic>,
) -> Result<(), Diagnostic> {
    for _ in 0..max_passes {
        if pass()? {
            return Ok(());
        }
    }
    Err(Diagnostic::new(
        span,
        format!(
            "recursive lifetime inference exceeded its finite local fixed-point pass budget ({max_passes} passes); annotate the result lifetime explicitly or simplify the local borrow aliases"
        ),
    ))
}

/// Collect every `Return(Some(value))` reachable in a block, including nested
/// control-flow expressions but not lambda bodies.
fn block_returns<'e>(block: &'e ast::Block, out: &mut Vec<&'e ast::Expr>) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                expr_returns(value, out)
            }
        }
    }
    if let Some(tail) = &block.tail {
        expr_returns(tail, out);
    }
}
fn expr_returns<'e>(expr: &'e ast::Expr, out: &mut Vec<&'e ast::Expr>) {
    use ast::ExprKind as K;
    match &expr.kind {
        K::Return(Some(value)) | K::Break(Some(value)) => {
            out.push(value);
            expr_returns(value, out);
        }
        K::Return(None) | K::Break(None) | K::Continue => {}
        K::Block(block) => block_returns(block, out),
        K::If {
            then, otherwise, ..
        } => {
            block_returns(then, out);
            if let Some(otherwise) = otherwise {
                expr_returns(otherwise, out);
            }
        }
        K::Match { arms, .. } => {
            for arm in arms {
                expr_returns(&arm.body, out);
            }
        }
        K::While { condition, body } => {
            expr_returns(condition, out);
            block_returns(body, out);
        }
        K::Loop(body) => block_returns(body, out),
        K::Handle { body, .. } => block_returns(body, out),
        K::Field { value, .. }
        | K::Slice { value, .. }
        | K::Index { value, .. }
        | K::Unary { operand: value, .. }
        | K::Try(value)
        | K::Cast { value, .. } => expr_returns(value, out),
        K::Binary { left, right, .. } => {
            expr_returns(left, out);
            expr_returns(right, out);
        }
        K::Call { callee, arguments } => {
            expr_returns(callee, out);
            for argument in arguments {
                expr_returns(argument, out);
            }
        }
        K::Record { fields, .. } | K::StructuralLiteral(fields) => {
            for (_, value) in fields {
                expr_returns(value, out);
            }
        }
        K::Tuple(values) | K::Array(values) => {
            for value in values {
                expr_returns(value, out);
            }
        }
        K::Perform { value, .. } => expr_returns(value, out),
        K::Name(_) | K::Integer(_) | K::Float(_) | K::String(_) | K::Char(_) | K::Bool(_) => {}
        K::Lambda(_) | K::Specialize { .. } => {}
    }
}
/// Direct static call edges from one function body to declared functions.
fn collect_direct_calls<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    block: &ast::Block,
    out: &mut BTreeSet<(BindingId, usize, usize)>,
) {
    fn visit_expr<'a>(
        resolution: &Resolution,
        declared: &BTreeMap<BindingId, Declared<'a>>,
        expr: &ast::Expr,
        out: &mut BTreeSet<(BindingId, usize, usize)>,
    ) {
        use ast::ExprKind as K;
        match &expr.kind {
            K::Call { callee, arguments } => {
                let target = match &callee.kind {
                    K::Name(_) => resolution.reference(callee.span),
                    K::Specialize { callee, .. } => resolution.reference(callee.span),
                    _ => None,
                };
                if let Some(binding) = target
                    && declared.get(&binding).is_some_and(|d| d.ast.body.is_some())
                {
                    out.insert((binding, callee.span.start, callee.span.end));
                }
                for argument in arguments {
                    visit_expr(resolution, declared, argument, out);
                }
            }
            K::Block(block) => visit_block(resolution, declared, block, out),
            K::If {
                then, otherwise, ..
            } => {
                visit_block(resolution, declared, then, out);
                if let Some(otherwise) = otherwise {
                    visit_expr(resolution, declared, otherwise, out);
                }
            }
            K::Match { arms, .. } => {
                for arm in arms {
                    visit_expr(resolution, declared, &arm.body, out);
                }
            }
            K::While { condition, body } => {
                visit_expr(resolution, declared, condition, out);
                visit_block(resolution, declared, body, out);
            }
            K::Loop(body) => visit_block(resolution, declared, body, out),
            K::Handle { handler, body, .. } => {
                visit_expr(resolution, declared, handler, out);
                visit_block(resolution, declared, body, out);
            }
            K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value))
            | K::Perform { value, .. } => visit_expr(resolution, declared, value, out),
            K::Binary { left, right, .. } => {
                visit_expr(resolution, declared, left, out);
                visit_expr(resolution, declared, right, out);
            }
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                for (_, value) in fields {
                    visit_expr(resolution, declared, value, out);
                }
            }
            K::Tuple(values) | K::Array(values) => {
                for value in values {
                    visit_expr(resolution, declared, value, out);
                }
            }
            _ => {}
        }
    }
    fn visit_block<'a>(
        resolution: &Resolution,
        declared: &BTreeMap<BindingId, Declared<'a>>,
        block: &ast::Block,
        out: &mut BTreeSet<(BindingId, usize, usize)>,
    ) {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                    visit_expr(resolution, declared, value, out)
                }
            }
        }
        if let Some(tail) = &block.tail {
            visit_expr(resolution, declared, tail, out);
        }
    }
    visit_block(resolution, declared, block, out);
}

/// Compute the frozen recursive summaries for every declaration with a
/// borrowed root result. The returned table is complete before any body is
/// checked, so ownership and callable interning never observe a provisional
/// signature.
pub(super) fn solve<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
) -> Result<Summaries, Diagnostic> {
    let mut solver = Solver::new(resolution, declared);
    solver.solve()?;
    Ok(Summaries {
        functions: solver.summaries,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_local_pass_budget_reports_its_exact_limit() {
        let error =
            run_local_fixed_point(MAX_LOCAL_PASSES, Span::new(0, 1), || Ok(false)).unwrap_err();
        assert!(
            error.message.contains("pass budget (64 passes)"),
            "{error:?}"
        );
    }

    #[test]
    fn convergence_on_the_last_allowed_pass_is_not_an_exhaustion() {
        let mut passes = 0usize;
        run_local_fixed_point(MAX_LOCAL_PASSES, Span::new(0, 1), || {
            passes += 1;
            Ok(passes == MAX_LOCAL_PASSES)
        })
        .unwrap();
        assert_eq!(passes, MAX_LOCAL_PASSES);
    }

    fn origin(parameter: usize, path: &[&str]) -> Origin {
        Origin {
            parameter,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    #[test]
    fn a_select_path_mismatch_is_not_an_empty_provenance() {
        let mut leaves = BTreeMap::new();
        leaves.insert(vec!["right".to_owned()], BTreeSet::from([origin(0, &[])]));
        let flow = Flow {
            leaves,
            unknown: None,
        };
        let mut selected = BTreeSet::new();
        let mut work = 0usize;
        assert_eq!(
            flow.select(&["left".to_owned()], &mut selected, &mut work),
            Err(SelectFailure::Missing)
        );
        assert!(selected.is_empty());
    }

    #[test]
    fn a_select_budget_exhaustion_is_reported_separately() {
        let mut leaves = BTreeMap::new();
        leaves.insert(Vec::new(), BTreeSet::from([origin(0, &[])]));
        let flow = Flow {
            leaves,
            unknown: None,
        };
        let mut selected = BTreeSet::new();
        let mut work = MAX_ANALYSIS_STEPS;
        assert_eq!(
            flow.select(&["view".to_owned()], &mut selected, &mut work),
            Err(SelectFailure::Budget)
        );
    }

    #[test]
    fn selecting_through_an_unknown_flow_stays_unknown() {
        let flow = Flow::unknown(Span::new(0, 1), "indirect call");
        let mut selected = BTreeSet::new();
        let mut work = 0usize;
        assert_eq!(
            flow.select(&["view".to_owned()], &mut selected, &mut work),
            Err(SelectFailure::Missing)
        );
    }
}
