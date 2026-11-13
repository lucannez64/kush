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
//! - Direct and statically resolved method calls participate. Indirect calls,
//!   dynamic dispatch, effect operations, loops, and tasks are unsupported
//!   boundaries: a summary that needs one keeps that `unknown` channel and is
//!   rejected unless the function has an explicit result lifetime. A caller of
//!   an explicit-result boundary still sees the preserved `unknown` instead of
//!   an empty origin set.
//! - Root result slots (a borrowed slice, text view, or reference) and
//!   per-field borrowed-record result paths are summarized. A missing field
//!   path is a checked error, never an empty origin set.
//! - An unseeded cycle is rejected unless every result path is syntactically
//!   returned from an explicit-result boundary. Merely containing an unrelated
//!   explicit-result call is not evidence for the returned value.
//! - An independent required-precondition summary `R[f]` unions explicit
//!   callee bounds and container-write requirements through the same call
//!   substitution. Callers missing a newly inferred requirement are rejected;
//!   an explicit trait/arrow/override contract is never strengthened.
//! - Aggregate budgets are checked errors, never partial successes:
//!   `MAX_ANALYSIS_STEPS` = 250_000 steps, `MAX_ORIGIN_FACTS` = 16_384 facts,
//!   `MAX_LOCAL_PASSES` = 64 local fixed-point passes.

use super::{Declared, Resolution, Type, borrow_lifetime, type_lifetimes};
use crate::runtime_types::Types;
use crate::{
    Diagnostic, Span, ast,
    lexer::Kind,
    resolve::{BindingId, BindingKind},
};
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

/// One inferred caller precondition: the borrow leaf `long` must outlive the
/// borrow leaf `short`. Both endpoints are input leaves, so this set never
/// mentions a value the caller cannot control.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Requirement {
    pub long: Origin,
    pub short: Origin,
}

/// The result-origin summary of one declaration. `leaves` is keyed by the
/// normal result field path (empty for a root slice/text/reference result) and
/// each origin set is the union over every normal return path; no alternative
/// is dropped because a scalar condition could prune it. `requirements` is the
/// independent `R[f]` precondition set. `unknown` preserves an unsupported
/// result channel discovered in the body so a caller cannot read it as an empty
/// (unrestricted) provenance.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct FunctionSummary {
    pub leaves: BTreeMap<Vec<String>, BTreeSet<Origin>>,
    pub requirements: BTreeSet<Requirement>,
    /// Whether this declaration participates in, or is reachable from, a
    /// recursive call-graph SCC. Only such declarations may publish newly
    /// inferred record-result bounds or caller preconditions; an acyclic
    /// declaration keeps its existing rigid contract.
    pub inferred_contract: bool,
    unknown: BTreeMap<Vec<String>, Unsupported>,
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
    /// Keys use the same relative field paths as `leaves`, so an unsupported
    /// owned field (for example a box construction) does not contaminate a
    /// borrowed field of the same record. Carrying it to a result forces an
    /// explicit result contract instead of silently guessing an empty
    /// (unrestricted) provenance.
    unknown: BTreeMap<Vec<String>, Unsupported>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Unsupported {
    span: Span,
    what: String,
    /// The fact was carried out of a callee's summary rather than observed
    /// directly. A relayed fact is wrapped at most once and never preferred
    /// over a root cause, so recursive relays cannot keep growing the witness
    /// and the chosen witness does not depend on source order.
    relayed: bool,
}

impl Unsupported {
    fn precedes(&self, other: &Unsupported) -> bool {
        (self.relayed, self.span.start, self.span.end, &self.what)
            < (other.relayed, other.span.start, other.span.end, &other.what)
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
            unknown: BTreeMap::new(),
        }
    }
    fn unknown(span: Span, what: impl Into<String>) -> Self {
        Self {
            leaves: BTreeMap::new(),
            unknown: BTreeMap::from([(
                Vec::new(),
                Unsupported {
                    relayed: false,
                    span,
                    what: what.into(),
                },
            )]),
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
        let mut unknown = BTreeMap::new();
        for (path, fact) in &self.unknown {
            let mut key = fields.to_vec();
            key.extend(path.iter().cloned());
            unknown.insert(key, fact.clone());
        }
        Self { leaves, unknown }
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
        let mut unknown = BTreeMap::new();
        for (path, fact) in &self.unknown {
            if path.is_empty() {
                unknown.insert(Vec::new(), fact.clone());
            } else if path.first().is_some_and(|first| first == field) {
                unknown.insert(path[1..].to_vec(), fact.clone());
            }
        }
        Self { leaves, unknown }
    }
    fn merge(&mut self, other: Flow) {
        for (path, origins) in other.leaves {
            self.leaves.entry(path).or_default().extend(origins);
        }
        for (path, fact) in other.unknown {
            match self.unknown.get(&path) {
                Some(current) if current.precedes(&fact) => {}
                _ => {
                    self.unknown.insert(path, fact);
                }
            }
        }
    }
    fn has_unknown(&self) -> bool {
        !self.unknown.is_empty()
    }
    /// Whether an unsupported fact can affect this result field path. A root
    /// fact affects every path; a fact on an unrelated field does not.
    fn unknown_conflicts(&self, path: &[String]) -> bool {
        self.unknown.keys().any(|key| {
            key.is_empty() || path.is_empty() || key.starts_with(path) || path.starts_with(key)
        })
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
            return if self.unknown.is_empty() {
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
        if self.unknown_conflicts(path) || !matched {
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

#[derive(Debug, Clone, Copy)]
enum CallArguments<'e> {
    Direct(&'e [ast::Expr]),
    Method {
        receiver: &'e ast::Expr,
        arguments: &'e [ast::Expr],
    },
}

impl<'e> CallArguments<'e> {
    /// The AST expression at a source parameter position. A direct call keeps
    /// erased proof holes in place, so the position is the list index. A method
    /// call has its receiver at position zero and shifts explicit arguments by
    /// one.
    fn source(self, position: usize) -> Option<&'e ast::Expr> {
        match self {
            Self::Direct(arguments) => arguments.get(position),
            Self::Method {
                receiver,
                arguments,
            } => {
                if position == 0 {
                    Some(receiver)
                } else {
                    arguments.get(position - 1)
                }
            }
        }
    }
}

struct Solver<'a, 'r> {
    resolution: &'r Resolution,
    declared: &'r BTreeMap<BindingId, Declared<'a>>,
    types: &'r Types<'a>,
    summaries: BTreeMap<BindingId, FunctionSummary>,
    edges: BTreeMap<BindingId, BTreeSet<BindingId>>,
    /// Source offsets of each direct call edge, for diagnostics. `Span` has no
    /// total order, so the stored pair is `(start, end)`.
    edge_sites: BTreeMap<(BindingId, BindingId), BTreeSet<(usize, usize)>>,
    /// Declared methods by method name. Receiver-type dispatch selects one when
    /// the receiver's syntactic type is known; a unique name is otherwise a
    /// static resolution rather than an `unknown` boundary.
    methods_by_name: BTreeMap<String, BTreeSet<BindingId>>,
    /// Concrete receiver type name of each declared method.
    method_receivers: BTreeMap<BindingId, String>,
    /// Syntactic receiver/local type names for the body currently analyzed.
    type_names: BTreeMap<BindingId, String>,
    /// Runtime parameter index of each non-erased parameter binding.
    parameter_bindings: BTreeMap<BindingId, usize>,
    self_type_name: Option<String>,
    steps: usize,
    facts: usize,
}

impl<'a, 'r> Solver<'a, 'r> {
    fn new(
        resolution: &'r Resolution,
        declared: &'r BTreeMap<BindingId, Declared<'a>>,
        types: &'r Types<'a>,
    ) -> Self {
        let mut methods_by_name: BTreeMap<String, BTreeSet<BindingId>> = BTreeMap::new();
        let mut method_receivers = BTreeMap::new();
        for (binding, entry) in declared {
            let Some(self_ty) = entry.self_ty else {
                continue;
            };
            let Type::Enum(id) = self_ty else {
                continue;
            };
            let receiver = types.enums[id].name.clone();
            method_receivers.insert(*binding, receiver.clone());
            methods_by_name
                .entry(entry.ast.name.clone())
                .or_default()
                .insert(*binding);
        }
        Self {
            resolution,
            declared,
            types,
            summaries: BTreeMap::new(),
            edges: BTreeMap::new(),
            edge_sites: BTreeMap::new(),
            methods_by_name,
            method_receivers,
            type_names: BTreeMap::new(),
            parameter_bindings: BTreeMap::new(),
            self_type_name: None,
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
    /// The source arguments of one call, used with source parameter positions.
    /// A direct call keeps erased proof holes in its AST argument list; a
    /// method call instead has an implicit receiver at source position zero.
    fn source_argument<'e>(
        declared: &Declared<'a>,
        call: CallArguments<'e>,
        runtime_index: usize,
    ) -> Option<&'e ast::Expr> {
        let mut runtime = 0usize;
        for (position, parameter) in declared.ast.parameters.iter().enumerate() {
            if parameter.erased {
                continue;
            }
            if runtime == runtime_index {
                return call.source(position);
            }
            runtime = runtime.saturating_add(1);
        }
        None
    }
    /// Whether the written result can carry a borrowed value: a root borrowed
    /// slice/text/reference, a borrowed record, or a container with borrowed
    /// elements. The written shape matters because an elided `&[T]` mentions no
    /// named lifetime.
    fn result_can_borrow(f: &ast::Function) -> bool {
        if Self::has_borrowed_result(f) {
            return true;
        }
        let result = crate::grades::split(&f.result).0;
        // An anonymous structural result keeps one summary leaf per borrowed
        // field path, exactly like a nominal borrowed record. Without this the
        // call would look like a scalar boundary and a caller projecting a
        // borrowed field (`wrap(a).view`) would lose the origin.
        if matches!(result.kind, ast::TypeKind::Structural { .. }) {
            return Self::written_type_has_borrow(result);
        }
        // Only a nominal record gets per-field result leaves here. An owned
        // reference container (`Box<&T>`, `Vec<&T>`) and an enum payload keep
        // their existing declared-lifetime inference; treating them as records
        // would turn every container constructor into an unsupported field.
        let ast::TypeKind::Named { path, arguments } = &result.kind else {
            return false;
        };
        if path
            .last()
            .is_some_and(|name| Self::is_reference_container_name(name))
        {
            return false;
        }
        let mut mentioned = BTreeSet::new();
        for argument in arguments {
            type_lifetimes(argument, &mut mentioned);
        }
        !mentioned.is_empty()
    }
    fn is_reference_container_name(name: &str) -> bool {
        matches!(
            name,
            "Box"
                | "Vec"
                | "Bytes"
                | "String"
                | "Task"
                | "TaskExit"
                | "Arena"
                | "ArenaBox"
                | "AllocBox"
                | "AllocVec"
                | "Option"
                | "Result"
        )
    }
    /// Whether a written type can carry borrowed storage, including through an
    /// anonymous structural row. Used to admit structural results into the
    /// per-field summary domain; it never treats an owner reference as a view.
    fn written_type_has_borrow(ty: &ast::Type) -> bool {
        match &ty.kind {
            ast::TypeKind::Borrow { .. } => true,
            ast::TypeKind::Structural { fields, row, .. } => {
                fields
                    .iter()
                    .any(|field| Self::written_type_has_borrow(&field.ty))
                    || row.as_deref().is_some_and(Self::written_type_has_borrow)
            }
            ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
                arguments.iter().any(Self::written_type_has_borrow)
            }
            ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(Self::written_type_has_borrow),
            ast::TypeKind::Slice(inner)
            | ast::TypeKind::Array(inner, _)
            | ast::TypeKind::Graded { inner, .. } => Self::written_type_has_borrow(inner),
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| Self::written_type_has_borrow(&parameter.ty))
                    || Self::written_type_has_borrow(result)
            }
            ast::TypeKind::Binary { left, right, .. } => {
                Self::written_type_has_borrow(left) || Self::written_type_has_borrow(right)
            }
            ast::TypeKind::Lifetime(_)
            | ast::TypeKind::SelfType
            | ast::TypeKind::Infer
            | ast::TypeKind::Capability { .. }
            | ast::TypeKind::Integer(_)
            | ast::TypeKind::Bool(_)
            | ast::TypeKind::Predicate(_) => false,
        }
    }
    /// Whether `path` reaches a borrowed field of the written structural
    /// result. A whole-value key (the empty path) stays because it can flow
    /// into every declared borrowed field; an owned scalar field leaf is not a
    /// provenance channel and must not become a summary path.
    fn result_path_has_borrow(ty: &ast::Type, path: &[String]) -> bool {
        let Some((first, rest)) = path.split_first() else {
            return Self::written_type_has_borrow(ty);
        };
        let ast::TypeKind::Structural { fields, .. } = &ty.kind else {
            // A path through a nominal/container shape is kept conservatively;
            // the result mapping checks its declared lifetime instead of
            // silently discarding an origin.
            return true;
        };
        fields
            .iter()
            .find(|field| field.name == *first)
            .is_some_and(|field| Self::result_path_has_borrow(&field.ty, rest))
    }
    /// Whether the written result is a borrowed slice/text view/reference. Only
    /// these root result slots use the elided-root inference path.
    fn has_borrowed_result(f: &ast::Function) -> bool {
        matches!(
            &crate::grades::split(&f.result).0.kind,
            ast::TypeKind::Borrow { .. }
        )
    }
    /// Number of independent input borrow lifetimes, including named lifetimes
    /// nested in a record or container parameter. Record-field lifetimes are
    /// deduplicated by name; a direct elided borrow counts once. This count is
    /// used only to distinguish a genuinely ambiguous unseeded cycle from the
    /// existing single-input parametric elision.
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
                continue;
            }
            type_lifetimes(ty, &mut names);
        }
        names.len() + elided
    }
    /// Syntactic type name of a written type after stripping references,
    /// grades, and type arguments. `Self` uses the enclosing impl target.
    fn ast_type_name(&self, ty: &ast::Type) -> Option<String> {
        match &ty.kind {
            ast::TypeKind::Borrow { inner, .. } | ast::TypeKind::Graded { inner, .. } => {
                self.ast_type_name(inner)
            }
            // Only a concrete nominal type identifies a receiver. A generic
            // parameter (`fn id<A>(x: A) -> A`), alias, or projection could
            // stand for any type, so it stays an unknown boundary rather than
            // matching an unrelated impl of the same name.
            ast::TypeKind::Named { path, .. } => match self.resolution.reference(ty.span) {
                Some(id) if self.resolution.bindings[id].kind != BindingKind::Data => None,
                _ => path.last().cloned(),
            },
            ast::TypeKind::SelfType => self.self_type_name.clone(),
            _ => None,
        }
    }
    fn self_name_of(&self, declared: &Declared<'a>) -> Option<String> {
        let Type::Enum(id) = declared.self_ty? else {
            return None;
        };
        Some(self.types.enums[id].name.clone())
    }
    /// Rebuild the simple receiver/local type environment for one body. This is
    /// deliberately a syntactic over-approximation: it never invents a method
    /// target, and an unresolved receiver keeps the explicit-contract boundary.
    fn prepare_type_names(&mut self, declared: &Declared<'a>) {
        self.self_type_name = self.self_name_of(declared);
        self.type_names.clear();
        self.parameter_bindings.clear();
        for (index, parameter) in Self::runtime_parameters(declared.ast) {
            if let Some(binder) = self.resolution.binder(parameter.span) {
                self.parameter_bindings.insert(binder, index);
            }
        }
        for parameter in declared.ast.parameters.iter().filter(|p| !p.erased) {
            if let (Some(binder), Some(name)) = (
                self.resolution.binder(parameter.span),
                self.ast_type_name(&parameter.ty),
            ) {
                self.type_names.insert(binder, name);
            }
        }
        if let Some(body) = &declared.ast.body {
            self.collect_type_names(body);
        }
    }
    fn collect_type_names(&mut self, block: &ast::Block) {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { pattern, value, .. } => {
                    let name = self.expr_type_name(value);
                    if let (Some(name), ast::PatternKind::Name(_)) = (name, &pattern.kind)
                        && let Some(binder) = self.resolution.binder(pattern.span)
                    {
                        self.type_names.entry(binder).or_insert(name);
                    }
                    self.collect_expr_type_names(value);
                }
                ast::Statement::Expr(value) => self.collect_expr_type_names(value),
            }
        }
        if let Some(tail) = &block.tail {
            self.collect_expr_type_names(tail);
        }
    }
    fn collect_expr_type_names(&mut self, expr: &ast::Expr) {
        use ast::ExprKind as K;
        match &expr.kind {
            K::Block(block) => self.collect_type_names(block),
            K::If {
                then, otherwise, ..
            } => {
                self.collect_type_names(then);
                if let Some(otherwise) = otherwise {
                    self.collect_expr_type_names(otherwise);
                }
            }
            K::Match { arms, .. } => {
                for arm in arms {
                    self.collect_expr_type_names(&arm.body);
                }
            }
            K::While { body, .. } | K::Loop(body) => self.collect_type_names(body),
            K::Handle { body, .. } => self.collect_type_names(body),
            K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value))
            | K::Specialize { callee: value, .. } => self.collect_expr_type_names(value),
            K::Binary { left, right, .. } => {
                self.collect_expr_type_names(left);
                self.collect_expr_type_names(right);
            }
            K::Call { callee, arguments } => {
                self.collect_expr_type_names(callee);
                for argument in arguments {
                    self.collect_expr_type_names(argument);
                }
            }
            K::Tuple(values) | K::Array(values) => {
                for value in values {
                    self.collect_expr_type_names(value);
                }
            }
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                for (_, value) in fields {
                    self.collect_expr_type_names(value);
                }
            }
            _ => {}
        }
    }
    fn expr_type_name(&self, expr: &ast::Expr) -> Option<String> {
        use ast::ExprKind as K;
        match &expr.kind {
            K::Name(_) => self
                .resolution
                .reference(expr.span)
                .and_then(|binder| self.type_names.get(&binder).cloned()),
            K::Unary { operand, .. } => self.expr_type_name(operand),
            K::Record { ty, .. } => self.expr_type_name(ty),
            K::Call { callee, .. } => {
                let (binding, _) = self.call_target(callee)?;
                self.declared
                    .get(&binding)
                    .and_then(|declared| self.ast_type_name(&declared.ast.result))
            }
            K::Block(block) => block
                .tail
                .as_deref()
                .and_then(|tail| self.expr_type_name(tail)),
            _ => None,
        }
    }
    /// Resolve a statically dispatched method call. The receiver type name is
    /// matched against the concrete impl target; a method name with exactly one
    /// declaration is also a static resolution. Dynamic dispatch and builtin
    /// methods stay `None` (an explicit-contract boundary).
    fn method_target<'e>(&self, callee: &'e ast::Expr) -> Option<(BindingId, &'e ast::Expr)> {
        let ast::ExprKind::Field { value, name } = &callee.kind else {
            return None;
        };
        if Self::is_builtin_method_name(name) {
            return None;
        }
        let receiver = match &value.kind {
            ast::ExprKind::Field {
                value: receiver, ..
            } if self
                .resolution
                .reference(value.span)
                .is_some_and(|id| self.resolution.bindings[id].kind == BindingKind::Trait) =>
            {
                receiver.as_ref()
            }
            _ => value.as_ref(),
        };
        let candidates = self.methods_by_name.get(name)?;
        if let Some(receiver_name) = self.expr_type_name(receiver) {
            let matching = candidates
                .iter()
                .copied()
                .filter(|binding| self.method_receivers.get(binding) == Some(&receiver_name))
                .collect::<Vec<_>>();
            if let [binding] = matching.as_slice() {
                return Some((*binding, receiver));
            }
        }
        if let [binding] = candidates.iter().copied().collect::<Vec<_>>().as_slice() {
            return Some((*binding, receiver));
        }
        None
    }
    fn call_target<'e>(&self, callee: &'e ast::Expr) -> Option<(BindingId, Option<&'e ast::Expr>)> {
        match &callee.kind {
            ast::ExprKind::Name(_) => self.callee_binding(callee).map(|binding| (binding, None)),
            ast::ExprKind::Specialize { callee, .. } => {
                self.callee_binding(callee).map(|binding| (binding, None))
            }
            ast::ExprKind::Field { .. } => self
                .method_target(callee)
                .map(|(binding, receiver)| (binding, Some(receiver))),
            _ => None,
        }
    }
    fn is_builtin_method_name(name: &str) -> bool {
        matches!(
            name,
            "len"
                | "capacity"
                | "get"
                | "at"
                | "try_get"
                | "push"
                | "push_reserved"
                | "clear"
                | "reserve"
                | "try_reserve"
                | "copy"
                | "set"
                | "as_bytes"
                | "as_str"
                | "bytes"
                | "substr"
                | "to_string"
                | "byte_at"
                | "scalar_at"
                | "scalar_len"
                | "from_utf8"
                | "take"
                | "read"
                | "code"
                | "convert"
                | "try_convert"
                | "truncate"
                | "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "saturating_add"
                | "saturating_sub"
                | "saturating_mul"
                | "checked_add"
                | "checked_sub"
                | "checked_mul"
                | "abs"
                | "sqrt"
                | "is_nan"
                | "is_infinite"
                | "is_finite"
                | "to_f64"
                | "try_to_f32"
                | "try_to_int"
        )
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
                ast::TypeKind::Slice(inner) | ast::TypeKind::Array(inner, _) => mentioned(inner),
                ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(mentioned),
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
            let ty = crate::grades::split(&parameter.ty).0;
            let mut mentioned = BTreeSet::new();
            type_lifetimes(ty, &mut mentioned);
            // A scalar parameter or a record with no borrow leaf cannot own a
            // borrow origin. Seeding it would fabricate a field leaf for a
            // scalar field written into a record literal.
            if mentioned.is_empty() && !matches!(ty.kind, ast::TypeKind::Borrow { .. }) {
                continue;
            }
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
            | K::Cast { value, .. }
            | K::Is { value, .. } => self.expr_flow(value, locals),
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
        let Some((binding, receiver)) = self.call_target(callee) else {
            return Ok(Flow::unknown(
                span,
                "an indirect, dynamic, or unresolved call in result position requires an explicit checked contract",
            ));
        };
        let Some(declared) = self.declared.get(&binding).copied() else {
            return Ok(Flow::unknown(
                span,
                "a call to a non-function or erased definition in result position requires an explicit checked contract",
            ));
        };
        let call = match receiver {
            Some(receiver) => CallArguments::Method {
                receiver,
                arguments,
            },
            None => CallArguments::Direct(arguments),
        };
        let Some(summary) = self.summaries.get(&binding).cloned() else {
            // A declaration with a borrow-capable result is summarized (possibly
            // empty before the first iteration). Anything else can only be a
            // scalar/free record result. The written shape matters here: an
            // elided `&[T]` mentions no named lifetime, but it is still a
            // borrowed shape and must never look scalar.
            let mut mentioned = BTreeSet::new();
            type_lifetimes(crate::grades::split(&declared.ast.result).0, &mut mentioned);
            return Ok(
                if !Self::has_borrowed_result(declared.ast) && mentioned.is_empty() {
                    Flow::empty()
                } else {
                    Flow::unknown(
                        span,
                        "a call returning a borrowed result without a summary is not part of the recursive fragment; annotate the result lifetime",
                    )
                },
            );
        };
        let callee_name = declared.ast.name.clone();
        let mut leaves: BTreeMap<Vec<String>, BTreeSet<Origin>> = BTreeMap::new();
        let mut unknown: BTreeMap<Vec<String>, Unsupported> = BTreeMap::new();
        let mut note_unknown = |path: Vec<String>, fact: Unsupported| match unknown.get(&path) {
            Some(current) if current.precedes(&fact) => {}
            _ => {
                unknown.insert(path, fact);
            }
        };
        for (result_path, origins) in &summary.leaves {
            for origin in origins {
                let Some(argument) = Self::source_argument(&declared, call, origin.parameter)
                else {
                    note_unknown(
                        result_path.clone(),
                        Unsupported {
                            relayed: false,
                            span,
                            what: format!(
                                "a summary origin names runtime parameter {} but the call has no corresponding source argument",
                                origin.parameter
                            ),
                        },
                    );
                    continue;
                };
                let flow = self.expr_flow(argument, locals)?;
                if flow.has_unknown() {
                    note_unknown(
                        result_path.clone(),
                        Unsupported {
                            relayed: false,
                            span: argument.span,
                            what: "a borrowed call argument comes from an unsupported boundary; annotate the result lifetime"
                                .to_owned(),
                        },
                    );
                    continue;
                }
                // A callee that returns a whole parameter (`fn id(p: Pair) -> Pair
                // { p }`) keeps the argument's own per-field structure: each
                // actual field leaf maps to the same field of the result rather
                // than every owner being merged into every result field.
                if origin.path.is_empty() && !flow.has_unknown() && !flow.leaves.is_empty() {
                    for (actual_path, actual_origins) in &flow.leaves {
                        let target = result_path
                            .iter()
                            .chain(actual_path.iter())
                            .cloned()
                            .collect::<Vec<_>>();
                        for selected in actual_origins {
                            if leaves
                                .entry(target.clone())
                                .or_default()
                                .insert(selected.clone())
                            {
                                self.charge_fact(span)?;
                            }
                        }
                    }
                    continue;
                }
                let mut selected = BTreeSet::new();
                match flow.select(&origin.path, &mut selected, &mut self.steps) {
                    Ok(()) => {}
                    Err(SelectFailure::Missing) => {
                        note_unknown(
                            result_path.clone(),
                            Unsupported {
                                relayed: false,
                                span: argument.span,
                                what: format!(
                                    "a borrowed call argument does not expose the callee result's field path '{}'; annotate the result lifetime or route the value through a direct checked function",
                                    origin.path.join(".")
                                ),
                            },
                        );
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
                    if leaves
                        .entry(result_path.clone())
                        .or_default()
                        .insert(selected)
                    {
                        self.charge_fact(span)?;
                    }
                }
            }
        }
        for (path, summary_unknown) in &summary.unknown {
            // Only a fact that can affect a summarized result leaf matters. An
            // unsupported owned field of a record does not contaminate the
            // borrowed leaves, and cannot be read as provenance either.
            let relevant = summary.leaves.is_empty()
                || summary.leaves.keys().any(|leaf| {
                    path.is_empty()
                        || leaf.is_empty()
                        || leaf.starts_with(path)
                        || path.starts_with(leaf)
                });
            if !relevant {
                continue;
            }
            let candidate = if summary_unknown.relayed {
                summary_unknown.clone()
            } else {
                Unsupported {
                    span,
                    what: format!(
                        "a call to '{callee_name}' returns through an unsupported result channel: {}",
                        summary_unknown.what
                    ),
                    relayed: true,
                }
            };
            note_unknown(path.clone(), candidate);
        }
        Ok(Flow { leaves, unknown })
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
        declared: &Declared<'a>,
        locals: &mut BTreeMap<BindingId, Flow>,
    ) -> Result<(), Diagnostic> {
        self.prepare_type_names(declared);
        self.seed_locals(declared.ast, locals)?;
        let Some(body) = &declared.ast.body else {
            return Ok(());
        };
        let span = declared.ast.result.span;
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
                    locals
                        .get_mut(&binding)
                        .unwrap()
                        .unknown
                        .extend(flow.unknown.clone());
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
        self.collect_calls_in_block(block, &mut found);
        for (callee, start, end) in found {
            self.edges.entry(binding).or_default().insert(callee);
            self.edge_sites
                .entry((binding, callee))
                .or_default()
                .insert((start, end));
        }
        Ok(())
    }
    fn collect_calls_in_block(
        &self,
        block: &ast::Block,
        out: &mut BTreeSet<(BindingId, usize, usize)>,
    ) {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                    self.collect_calls_in_expr(value, out)
                }
            }
        }
        if let Some(tail) = &block.tail {
            self.collect_calls_in_expr(tail, out);
        }
    }
    fn collect_calls_in_expr(
        &self,
        expr: &ast::Expr,
        out: &mut BTreeSet<(BindingId, usize, usize)>,
    ) {
        use ast::ExprKind as K;
        match &expr.kind {
            K::Call { callee, arguments } => {
                if let Some((binding, _)) = self.call_target(callee)
                    && self
                        .declared
                        .get(&binding)
                        .is_some_and(|d| d.ast.body.is_some())
                {
                    out.insert((binding, callee.span.start, callee.span.end));
                }
                self.collect_calls_in_expr(callee, out);
                for argument in arguments {
                    self.collect_calls_in_expr(argument, out);
                }
            }
            K::Block(block) => self.collect_calls_in_block(block, out),
            K::If {
                then, otherwise, ..
            } => {
                self.collect_calls_in_block(then, out);
                if let Some(otherwise) = otherwise {
                    self.collect_calls_in_expr(otherwise, out);
                }
            }
            K::Match { arms, .. } => {
                for arm in arms {
                    self.collect_calls_in_expr(&arm.body, out);
                }
            }
            K::While {
                condition, body, ..
            } => {
                self.collect_calls_in_expr(condition, out);
                self.collect_calls_in_block(body, out);
            }
            K::Loop(body) => self.collect_calls_in_block(body, out),
            K::Handle { handler, body, .. } => {
                self.collect_calls_in_expr(handler, out);
                self.collect_calls_in_block(body, out);
            }
            K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value))
            | K::Perform { value, .. } => self.collect_calls_in_expr(value, out),
            K::Binary { left, right, .. } => {
                self.collect_calls_in_expr(left, out);
                self.collect_calls_in_expr(right, out);
            }
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                for (_, value) in fields {
                    self.collect_calls_in_expr(value, out);
                }
            }
            K::Tuple(values) | K::Array(values) => {
                for value in values {
                    self.collect_calls_in_expr(value, out);
                }
            }
            _ => {}
        }
    }
    /// Collect the independent required-precondition set `R[f]` from every
    /// call and container write in a body. Explicit callee bounds and an
    /// already inferred callee `R[g]` both substitute through the same actual
    /// argument leaves. A field path that cannot be mapped is a checked error,
    /// never silently dropped.
    fn collect_requirements(
        &mut self,
        block: &ast::Block,
        locals: &BTreeMap<BindingId, Flow>,
        out: &mut BTreeSet<Requirement>,
    ) -> Result<(), Diagnostic> {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                    self.requirements_in_expr(value, locals, out)?
                }
            }
        }
        if let Some(tail) = &block.tail {
            self.requirements_in_expr(tail, locals, out)?;
        }
        Ok(())
    }
    fn requirements_in_expr(
        &mut self,
        expr: &ast::Expr,
        locals: &BTreeMap<BindingId, Flow>,
        out: &mut BTreeSet<Requirement>,
    ) -> Result<(), Diagnostic> {
        self.charge(expr.span)?;
        use ast::ExprKind as K;
        match &expr.kind {
            K::Call { callee, arguments } => {
                self.requirements_in_call(callee, arguments, locals, out)?;
                self.requirements_in_expr(callee, locals, out)?;
                for argument in arguments {
                    self.requirements_in_expr(argument, locals, out)?;
                }
            }
            K::Block(block) => self.collect_requirements(block, locals, out)?,
            K::If {
                then, otherwise, ..
            } => {
                self.collect_requirements(then, locals, out)?;
                if let Some(otherwise) = otherwise {
                    self.requirements_in_expr(otherwise, locals, out)?;
                }
            }
            K::Match { arms, .. } => {
                for arm in arms {
                    self.requirements_in_expr(&arm.body, locals, out)?;
                }
            }
            K::While {
                condition, body, ..
            } => {
                self.requirements_in_expr(condition, locals, out)?;
                self.collect_requirements(body, locals, out)?;
            }
            K::Loop(body) => self.collect_requirements(body, locals, out)?,
            K::Handle { body, .. } => self.collect_requirements(body, locals, out)?,
            K::Field { value, .. }
            | K::Slice { value, .. }
            | K::Index { value, .. }
            | K::Unary { operand: value, .. }
            | K::Try(value)
            | K::Cast { value, .. }
            | K::Return(Some(value))
            | K::Break(Some(value))
            | K::Perform { value, .. }
            | K::Specialize { callee: value, .. } => {
                self.requirements_in_expr(value, locals, out)?
            }
            K::Binary { left, right, .. } => {
                self.requirements_in_expr(left, locals, out)?;
                self.requirements_in_expr(right, locals, out)?;
            }
            K::Record { fields, .. } | K::StructuralLiteral(fields) => {
                for (_, value) in fields {
                    self.requirements_in_expr(value, locals, out)?;
                }
            }
            K::Tuple(values) | K::Array(values) => {
                for value in values {
                    self.requirements_in_expr(value, locals, out)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn requirements_in_call(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        locals: &BTreeMap<BindingId, Flow>,
        out: &mut BTreeSet<Requirement>,
    ) -> Result<(), Diagnostic> {
        if let Some((binding, receiver)) = self.call_target(callee) {
            let Some(declared) = self.declared.get(&binding).copied() else {
                return Ok(());
            };
            let call = match receiver {
                Some(receiver) => CallArguments::Method {
                    receiver,
                    arguments,
                },
                None => CallArguments::Direct(arguments),
            };
            let mut requirements = self
                .summaries
                .get(&binding)
                .map(|summary| summary.requirements.clone())
                .unwrap_or_default();
            // The callee's own explicit bounds are preconditions too. They are
            // never invented by this pass; they are read from the declaration
            // exactly as ownership will validate them.
            for (long, short) in Self::declared_bounds(declared.ast) {
                for long in Self::lifetime_origins(declared.ast, &long) {
                    for short in Self::lifetime_origins(declared.ast, &short) {
                        requirements.insert(Requirement {
                            long: long.clone(),
                            short,
                        });
                    }
                }
            }
            for requirement in requirements {
                let longs = self.requirement_actuals(&declared, call, &requirement.long, locals)?;
                let shorts =
                    self.requirement_actuals(&declared, call, &requirement.short, locals)?;
                for long in longs {
                    for short in &shorts {
                        if &long == short {
                            continue;
                        }
                        if out.insert(Requirement {
                            long: long.clone(),
                            short: short.clone(),
                        }) {
                            self.charge_fact(callee.span)?;
                        }
                    }
                }
            }
            return Ok(());
        }
        self.container_write_requirement(callee, arguments, locals, out)
    }
    /// A direct `Vec.push`/`Box.set` writes the value borrow into the container's
    /// declared element lifetime. That relation is not a returned origin, so it
    /// belongs to `R[f]` and must be satisfied by every caller.
    fn container_write_requirement(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        locals: &BTreeMap<BindingId, Flow>,
        out: &mut BTreeSet<Requirement>,
    ) -> Result<(), Diagnostic> {
        let ast::ExprKind::Field { value, name } = &callee.kind else {
            return Ok(());
        };
        if !matches!(name.as_str(), "push" | "set") {
            return Ok(());
        }
        // `Vec.push(values, value)` names the container in the first argument;
        // `values.push(value)` names it in the receiver. The resolved builtin
        // name distinguishes the two spellings.
        let builtin = self.resolution.reference(callee.span).and_then(|id| {
            let binding = &self.resolution.bindings[id];
            (binding.kind == BindingKind::Builtin).then_some(binding.name.as_str())
        });
        let (container, written) = match builtin {
            Some("Vec.push") | Some("Box.set") => {
                let [container, written] = arguments else {
                    return Ok(());
                };
                (container, written)
            }
            Some(_) => return Ok(()),
            None => {
                let [written] = arguments else {
                    return Ok(());
                };
                (value.as_ref(), written)
            }
        };
        let Some(container) = self.root_parameter_origin(container) else {
            return Ok(());
        };
        let flow = self.expr_flow(written, locals)?;
        if flow.has_unknown() {
            return Ok(());
        }
        for origin in flow.all_origins() {
            if origin != container
                && out.insert(Requirement {
                    long: origin,
                    short: container.clone(),
                })
            {
                self.charge_fact(callee.span)?;
            }
        }
        Ok(())
    }
    fn root_parameter_origin(&self, expr: &ast::Expr) -> Option<Origin> {
        let binding = self.resolution.reference(expr.span)?;
        let parameter = *self.parameter_bindings.get(&binding)?;
        Some(Origin {
            parameter,
            path: Vec::new(),
        })
    }
    fn declared_bounds(f: &ast::Function) -> BTreeSet<(String, String)> {
        let mut bounds = BTreeSet::new();
        for lifetime in &f.lifetimes {
            for bound in &lifetime.bounds {
                if bound.name != lifetime.name {
                    bounds.insert((lifetime.name.clone(), bound.name.clone()));
                }
            }
        }
        bounds
    }
    /// The input leaves whose written type mentions `lifetime`. A direct borrow
    /// names its own runtime parameter; a nested lifetime inside a container or
    /// record uses that parameter's root leaf. Result-only lifetimes produce no
    /// precondition.
    fn lifetime_origins(f: &ast::Function, lifetime: &str) -> BTreeSet<Origin> {
        let mut origins = BTreeSet::new();
        for (index, parameter) in Self::runtime_parameters(f) {
            let ty = crate::grades::split(&parameter.ty).0;
            if let ast::TypeKind::Borrow {
                lifetime: Some(name),
                ..
            } = &ty.kind
                && name == lifetime
            {
                origins.insert(Origin {
                    parameter: index,
                    path: Vec::new(),
                });
                continue;
            }
            let mut names = BTreeSet::new();
            type_lifetimes(ty, &mut names);
            if names.contains(lifetime) {
                origins.insert(Origin {
                    parameter: index,
                    path: Vec::new(),
                });
            }
        }
        origins
    }
    fn requirement_actuals(
        &mut self,
        declared: &Declared<'a>,
        call: CallArguments<'_>,
        origin: &Origin,
        locals: &BTreeMap<BindingId, Flow>,
    ) -> Result<BTreeSet<Origin>, Diagnostic> {
        let Some(argument) = Self::source_argument(declared, call, origin.parameter) else {
            return Err(Diagnostic::new(
                declared.span,
                format!(
                    "a required precondition names runtime parameter {} but the call has no corresponding source argument",
                    origin.parameter
                ),
            ));
        };
        let flow = self.expr_flow(argument, locals)?;
        if flow.has_unknown() {
            return Ok(BTreeSet::new());
        }
        let mut actuals = BTreeSet::new();
        match flow.select(&origin.path, &mut actuals, &mut self.steps) {
            Ok(()) => Ok(actuals),
            Err(SelectFailure::Missing) => Err(Diagnostic::new(
                argument.span,
                format!(
                    "this call argument does not expose the required precondition's field path '{}'; annotate the contract explicitly",
                    origin.path.join(".")
                ),
            )),
            Err(SelectFailure::Budget) => Err(Diagnostic::new(
                argument.span,
                "recursive lifetime inference exceeded its finite work budget while substituting a required precondition",
            )),
        }
    }
    fn solve(&mut self) -> Result<(), Diagnostic> {
        // Seed one summary slot per function body. The least fixed point starts
        // empty: a cycle with no base return stays empty and is rejected below
        // instead of bootstrapping "any input". Requirements are seeded from an
        // empty set as well and grow by union with the same call substitution.
        for (binding, declared) in self.declared {
            if declared.ast.body.is_some() {
                self.summaries.insert(*binding, FunctionSummary::default());
            }
        }
        for (binding, declared) in self.declared {
            if let Some(body) = &declared.ast.body {
                self.prepare_type_names(declared);
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
                self.analyze_locals(&declared, &mut locals)?;
                let mut flow = self.block_flow(body, &locals)?;
                let result = crate::grades::split(&declared.ast.result).0;
                if matches!(result.kind, ast::TypeKind::Structural { .. }) {
                    // Record/structural literals extend a whole-value origin to
                    // every field, including owned scalars. Only borrowed field
                    // paths are real summary leaves.
                    flow.leaves.retain(|path, _| {
                        path.is_empty() || Self::result_path_has_borrow(result, path)
                    });
                }
                let mut requirements = BTreeSet::new();
                self.collect_requirements(body, &locals, &mut requirements)?;
                let borrow_capable = Self::result_can_borrow(declared.ast);
                let mut summary = FunctionSummary {
                    leaves: if borrow_capable {
                        flow.leaves.clone()
                    } else {
                        BTreeMap::new()
                    },
                    requirements,
                    inferred_contract: false,
                    unknown: if borrow_capable {
                        flow.unknown.clone()
                    } else {
                        BTreeMap::new()
                    },
                };
                // Join with the previous iteration so a later callee fact can
                // only add origins/requirements. The finite lattice guarantees
                // termination; this also makes the result independent of which
                // caller happened to be visited first.
                let previous = self.summaries[binding].clone();
                for (path, origins) in previous.leaves {
                    summary.leaves.entry(path).or_default().extend(origins);
                }
                summary.requirements.extend(previous.requirements);
                for (path, fact) in previous.unknown {
                    match summary.unknown.get(&path) {
                        Some(current) if current.precedes(&fact) => {}
                        _ => {
                            summary.unknown.insert(path, fact);
                        }
                    }
                }
                if summary != self.summaries[binding] {
                    self.summaries.insert(*binding, summary);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        self.mark_inferred_contracts();
        self.diagnose()
    }
    /// Mark the declarations whose contracts may be inferred: every member of
    /// a recursive call-graph SCC and every callee reachable from one. An
    /// acyclic declaration that no recursive path uses keeps its existing
    /// declared (rigid) contract.
    fn mark_inferred_contracts(&mut self) {
        let mut roots = BTreeSet::new();
        for group in self.sccs() {
            let cyclic = group.len() > 1
                || self
                    .edges
                    .get(&group[0])
                    .is_some_and(|edges| edges.contains(&group[0]));
            if cyclic {
                roots.extend(group);
            }
        }
        let mut reachable = BTreeSet::new();
        let mut stack = roots.into_iter().collect::<Vec<_>>();
        while let Some(node) = stack.pop() {
            if !reachable.insert(node) {
                continue;
            }
            if let Some(next) = self.edges.get(&node) {
                stack.extend(next.iter().copied());
            }
        }
        for (binding, summary) in &mut self.summaries {
            summary.inferred_contract = reachable.contains(binding);
        }
    }
    /// Whether a direct/method call target has an explicit borrowed result
    /// contract. A record result with declared lifetimes is not an explicit
    /// root-result boundary: its per-field leaves are inferred.
    fn explicit_result_call(&self, callee: &ast::Expr) -> bool {
        self.call_target(callee).is_some_and(|(binding, _)| {
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
                if !Self::result_can_borrow(declared.ast) {
                    continue;
                }
                if Self::has_borrowed_result(declared.ast)
                    && borrow_lifetime(crate::grades::split(&declared.ast.result).0).is_some()
                {
                    // An explicit root result contract is parametric forwarding;
                    // it is validated by the ownership pass, not inferred here.
                    continue;
                }
                let Some(body) = &declared.ast.body else {
                    continue;
                };
                let mut locals = BTreeMap::new();
                self.analyze_locals(&declared, &mut locals)?;
                let flow = self.block_flow(body, &locals)?;
                if let Some((_, unknown)) = flow.unknown.iter().find(|(path, _)| {
                    self.summaries[binding].leaves.is_empty()
                        || self.summaries[binding].leaves.keys().any(|leaf| {
                            path.is_empty()
                                || leaf.is_empty()
                                || leaf.starts_with(path)
                                || path.starts_with(leaf)
                        })
                }) {
                    // A no-input elided result already has a more precise
                    // "cannot be returned" rejection in the ordinary pass. For
                    // an acyclic root result a single input lifetime already
                    // fixes the result provenance, so the existing pass keeps
                    // its more specific mutability/escape diagnostic. Multiple
                    // independent inputs are where an empty summary would
                    // silently choose no owner. A borrowed record result has
                    // per-field leaves, so any unsupported channel must be
                    // reported instead of becoming an empty field set.
                    let report = if cyclic {
                        Self::input_has_borrow_shape(declared.ast)
                    } else if Self::has_borrowed_result(declared.ast) {
                        Self::input_lifetime_count(declared.ast) > 1
                    } else {
                        // An acyclic record result keeps its existing rigid
                        // field validation. A non-returning call such as
                        // `panic()` is not evidence of an empty borrowed field.
                        false
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
                    && self.summaries[binding]
                        .leaves
                        .values()
                        .all(BTreeSet::is_empty)
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
        K::While {
            condition, body, ..
        } => {
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
        | K::Cast { value, .. }
        | K::Is { value, .. } => expr_returns(value, out),
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
/// Compute the frozen recursive summaries for every declaration with a
/// borrowed root result. The returned table is complete before any body is
/// checked, so ownership and callable interning never observe a provisional
/// signature.
pub(super) fn solve<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    types: &Types<'a>,
) -> Result<Summaries, Diagnostic> {
    let mut solver = Solver::new(resolution, declared, types);
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
            unknown: BTreeMap::new(),
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
            unknown: BTreeMap::new(),
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
