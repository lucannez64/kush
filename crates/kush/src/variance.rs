//! Lifetime-only variance.
//!
//! This module computes a finite variance table for declared lifetime
//! parameters and provides the contextual pieces needed to check a conversion:
//! occurrence-specific label environments, a pair/path witness judgment, and
//! signed positions for the constructors that currently admit borrowed
//! payloads. It never changes runtime representations: a variance result is
//! checker-only evidence.
use crate::{
    Diagnostic, Span, ast,
    executable::Type,
    resolve::{BindingId, Resolution},
    runtime_types::{BorrowSig, FunctionType, Types},
};
use std::collections::{BTreeMap, BTreeSet};
/// The four-element variance lattice as a set of permitted directions.
///
/// `UNUSED` is bottom, `INVARIANT` is top, and the two singleton sets are the
/// covariant and contravariant elements. Joining is set union.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SignSet(u8);
impl SignSet {
    const POSITIVE_BIT: u8 = 1;
    const NEGATIVE_BIT: u8 = 2;
    pub(crate) const UNUSED: SignSet = SignSet(0);
    pub(crate) const POSITIVE: SignSet = SignSet(Self::POSITIVE_BIT);
    pub(crate) const NEGATIVE: SignSet = SignSet(Self::NEGATIVE_BIT);
    pub(crate) const INVARIANT: SignSet = SignSet(Self::POSITIVE_BIT | Self::NEGATIVE_BIT);
    pub(crate) fn is_unused(self) -> bool {
        self.0 == 0
    }
    pub(crate) fn is_invariant(self) -> bool {
        self == Self::INVARIANT
    }
    pub(crate) fn is_positive_only(self) -> bool {
        self == Self::POSITIVE
    }
    pub(crate) fn is_negative_only(self) -> bool {
        self == Self::NEGATIVE
    }
    /// Least upper bound. Every element is a subset of `INVARIANT`.
    pub(crate) fn join(self, other: SignSet) -> SignSet {
        SignSet(self.0 | other.0)
    }
    /// Composition of occurrences. An absent side has no occurrence, so the
    /// composition is absent even when the other side is invariant. Otherwise
    /// each pair of directions multiplies, and a set composes to the union of
    /// its pairwise products.
    pub(crate) fn compose(self, other: SignSet) -> SignSet {
        if self.is_unused() || other.is_unused() {
            return Self::UNUSED;
        }
        let mut result = 0u8;
        for (left, bit) in [(1i8, Self::POSITIVE_BIT), (-1i8, Self::NEGATIVE_BIT)] {
            if self.0 & bit == 0 {
                continue;
            }
            for (right, right_bit) in [(1i8, Self::POSITIVE_BIT), (-1i8, Self::NEGATIVE_BIT)] {
                if other.0 & right_bit == 0 {
                    continue;
                }
                result |= if left * right > 0 {
                    Self::POSITIVE_BIT
                } else {
                    Self::NEGATIVE_BIT
                };
            }
        }
        SignSet(result)
    }
}
/// One declaration's lifetime-parameter variance, in declaration order.
#[derive(Clone, Debug, Default)]
pub(crate) struct VarianceTable {
    entries: BTreeMap<BindingId, Vec<SignSet>>,
    labels: BTreeMap<BindingId, Vec<String>>,
}
impl VarianceTable {
    /// Variance of one declared lifetime slot. A declaration without a table
    /// entry is unknown, never silently covariant.
    pub(crate) fn of(&self, declaration: BindingId, index: usize) -> Option<SignSet> {
        self.entries
            .get(&declaration)
            .and_then(|slots| slots.get(index))
            .copied()
    }
    fn insert(&mut self, declaration: BindingId, labels: Vec<String>, slots: Vec<SignSet>) {
        self.entries.insert(declaration, slots);
        self.labels.insert(declaration, labels);
    }
}
/// A bounded, deterministic worklist solution for a finite occurrence graph.
///
/// Nodes are global `(declaration, lifetime slot)` indices. An edge
/// `(position, target, source)` contributes `compose(position, target)` to
/// `source`. Seeds are direct occurrences in the body, never self-edges whose
/// value depends on an initial estimate.
fn solve_graph(
    node_count: usize,
    seeds: &BTreeMap<usize, SignSet>,
    edges: &[(SignSet, usize, usize)],
) -> Result<Vec<SignSet>, Diagnostic> {
    let mut values = vec![SignSet::UNUSED; node_count];
    for (&source, &seed) in seeds {
        if source < node_count {
            values[source] = values[source].join(seed);
        }
    }
    let mut outgoing = vec![Vec::new(); node_count];
    for &(position, target, source) in edges {
        if target < node_count && source < node_count {
            outgoing[target].push((position, source));
        }
    }
    let mut work: BTreeSet<usize> = (0..node_count).collect();
    // The lattice has height two. Each node can strictly ascend at most twice,
    // and each ascent notifies every outgoing edge once. This generous finite
    // budget turns an implementation mistake into a diagnostic rather than an
    // unbounded loop.
    let mut budget = node_count
        .saturating_mul(4)
        .saturating_add(edges.len().saturating_mul(4))
        .saturating_add(16);
    while let Some(node) = work.pop_first() {
        if budget == 0 {
            return Err(Diagnostic::new(
                Span::default(),
                "lifetime variance fixed point exhausted its finite budget; the occurrence graph is malformed",
            ));
        }
        budget -= 1;
        let value = values[node];
        for &(position, source) in &outgoing[node] {
            let contribution = position.compose(value);
            let joined = values[source].join(contribution);
            if joined != values[source] {
                values[source] = joined;
                work.insert(source);
            }
        }
    }
    Ok(values)
}
struct DeclInfo<'a> {
    labels: Vec<String>,
    bodies: Vec<&'a ast::Type>,
}
struct Builder<'a> {
    resolution: &'a Resolution,
    /// Declaration -> (global node offset, lifetime labels).
    nodes: BTreeMap<BindingId, (usize, Vec<String>)>,
    seeds: BTreeMap<usize, SignSet>,
    edges: Vec<(SignSet, usize, usize)>,
}
struct Owner {
    declaration: BindingId,
    label_indices: BTreeMap<String, usize>,
}
impl Builder<'_> {
    fn node(&self, declaration: BindingId, index: usize) -> Option<usize> {
        self.nodes
            .get(&declaration)
            .and_then(|(offset, labels)| (index < labels.len()).then_some(offset + index))
    }
    fn seed(&mut self, declaration: BindingId, index: usize, position: SignSet) {
        if position.is_unused() {
            return;
        }
        let Some(node) = self.node(declaration, index) else {
            return;
        };
        let entry = self.seeds.entry(node).or_default();
        *entry = entry.join(position);
    }
    fn edge_for(
        &mut self,
        position: SignSet,
        target: (BindingId, usize),
        owner: &Owner,
        source_index: usize,
    ) {
        let (Some(target_node), Some(source_node)) = (
            self.node(target.0, target.1),
            self.node(owner.declaration, source_index),
        ) else {
            return;
        };
        self.edges.push((position, target_node, source_node));
    }
    /// Walk one declaration body. `position` is the occurrence polarity from
    /// the declaration's root. Direct uses of an owner lifetime are seeds;
    /// uses behind another declaration are composition edges.
    fn walk(&mut self, ty: &ast::Type, position: SignSet, owner: &Owner, depth: usize) {
        if depth >= 64 || position.is_unused() {
            return;
        }
        match &ty.kind {
            ast::TypeKind::Lifetime(name) => {
                if let Some(index) = owner.label_indices.get(name) {
                    self.seed(owner.declaration, *index, position);
                }
            }
            ast::TypeKind::Borrow {
                lifetime,
                mutable,
                inner,
            } => {
                if let Some(name) = lifetime
                    && let Some(index) = owner.label_indices.get(name)
                {
                    self.seed(owner.declaration, *index, position);
                }
                let inner_position = position.compose(if *mutable {
                    SignSet::INVARIANT
                } else {
                    SignSet::POSITIVE
                });
                self.walk(inner, inner_position, owner, depth + 1);
            }
            ast::TypeKind::Slice(inner) => {
                // A slice element is copyable in the admitted subset, but a
                // nested named generic can still mention a lifetime argument.
                self.walk(inner, position.compose(SignSet::POSITIVE), owner, depth + 1);
            }
            ast::TypeKind::Tuple(items) => {
                for item in items {
                    self.walk(item, position, owner, depth + 1);
                }
            }
            ast::TypeKind::Array(element, _) => {
                self.walk(element, position, owner, depth + 1);
            }
            ast::TypeKind::Structural { fields, .. } => {
                // Structural rows retain borrowed leaves exactly until their
                // own provenance contract lands. An occurrence inside one is
                // conservatively invariant.
                for field in fields {
                    self.walk(
                        &field.ty,
                        position.compose(SignSet::INVARIANT),
                        owner,
                        depth + 1,
                    );
                }
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                // Arrow-bound lifetimes are their own binders. A free owner
                // lifetime inside an arrow is not an accepted conversion
                // surface today, so do not claim any covariance for it.
                for parameter in parameters {
                    self.walk(
                        &parameter.ty,
                        position.compose(SignSet::INVARIANT),
                        owner,
                        depth + 1,
                    );
                }
                self.walk(
                    result,
                    position.compose(SignSet::INVARIANT),
                    owner,
                    depth + 1,
                );
            }
            ast::TypeKind::Named { path, arguments } => {
                self.walk_named(ty, path, arguments, position, owner, depth);
            }
            ast::TypeKind::Binary { left, right, .. } => {
                self.walk(left, position.compose(SignSet::INVARIANT), owner, depth + 1);
                self.walk(
                    right,
                    position.compose(SignSet::INVARIANT),
                    owner,
                    depth + 1,
                );
            }
            ast::TypeKind::Graded { inner, .. } => {
                self.walk(inner, position, owner, depth + 1);
            }
            ast::TypeKind::Predicate(_)
            | ast::TypeKind::Dyn(_)
            | ast::TypeKind::SelfType
            | ast::TypeKind::Infer
            | ast::TypeKind::Integer(_)
            | ast::TypeKind::Bool(_) => {}
        }
    }
    fn walk_named(
        &mut self,
        ty: &ast::Type,
        path: &[String],
        arguments: &[ast::Type],
        position: SignSet,
        owner: &Owner,
        depth: usize,
    ) {
        let builtin = path.last().map(String::as_str);
        let type_argument_position = match builtin {
            // Owning Box/Vec of currently admitted borrowed payloads are the
            // covariant containers. Arena/custom-allocator storage remains
            // exact, so their borrowed payload is invariant.
            Some("Box" | "Vec") => position.compose(SignSet::POSITIVE),
            _ => position.compose(SignSet::INVARIANT),
        };
        let target = self
            .resolution
            .reference(ty.span)
            .filter(|id| self.nodes.contains_key(id));
        let mut associated = BTreeSet::new();
        if let Some(target) = target {
            let target_labels = self
                .nodes
                .get(&target)
                .map(|(_, labels)| labels.clone())
                .unwrap_or_default();
            let lifetime_arguments = arguments
                .iter()
                .filter_map(|argument| match &argument.kind {
                    ast::TypeKind::Lifetime(name) => Some(name.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            for (index, (declared, argument)) in
                target_labels.iter().zip(&lifetime_arguments).enumerate()
            {
                let _ = declared;
                associated.insert(argument.clone());
                if let Some(source_index) = owner.label_indices.get(argument) {
                    self.edge_for(position, (target, index), owner, *source_index);
                }
            }
        }
        // Arguments that are not lifetime arguments of a known declaration
        // have unknown variance. Box/Vec stay covariant; everything else is
        // conservative. A lifetime argument that mentions an owner lifetime
        // but could not be associated with a known declaration slot is an
        // unknown occurrence and contributes invariant evidence.
        for argument in arguments {
            match &argument.kind {
                ast::TypeKind::Lifetime(name) => {
                    if let Some(index) = owner.label_indices.get(name)
                        && !associated.contains(name)
                    {
                        self.seed(
                            owner.declaration,
                            *index,
                            position.compose(SignSet::INVARIANT),
                        );
                    }
                }
                _ => self.walk(argument, type_argument_position, owner, depth + 1),
            }
        }
    }
}
/// Infer seeded finite lifetime variance for every declared lifetime parameter.
pub(crate) fn infer(
    module: &ast::Module,
    resolution: &Resolution,
) -> Result<VarianceTable, Diagnostic> {
    let mut infos: BTreeMap<BindingId, DeclInfo<'_>> = BTreeMap::new();
    for declaration in &module.items {
        let Some(id) = resolution
            .declarations
            .get(&declaration.item.span.start)
            .copied()
        else {
            continue;
        };
        let (labels, bodies): (Vec<String>, Vec<&ast::Type>) = match &declaration.item.kind {
            ast::ItemKind::Struct {
                lifetimes, fields, ..
            } => (
                lifetimes
                    .iter()
                    .map(|lifetime| lifetime.name.clone())
                    .collect(),
                fields.iter().map(|field| &field.ty).collect(),
            ),
            ast::ItemKind::Alias { lifetimes, ty, .. } => (
                lifetimes
                    .iter()
                    .map(|lifetime| lifetime.name.clone())
                    .collect(),
                vec![ty],
            ),
            _ => continue,
        };
        if labels.is_empty() {
            continue;
        }
        infos.insert(id, DeclInfo { labels, bodies });
    }
    let mut nodes = BTreeMap::new();
    let mut offset = 0usize;
    for (id, info) in &infos {
        nodes.insert(*id, (offset, info.labels.clone()));
        offset += info.labels.len();
    }
    let mut builder = Builder {
        resolution,
        nodes,
        seeds: BTreeMap::new(),
        edges: Vec::new(),
    };
    for (id, info) in &infos {
        let owner = Owner {
            declaration: *id,
            label_indices: info
                .labels
                .iter()
                .enumerate()
                .map(|(index, label)| (label.clone(), index))
                .collect(),
        };
        for body in &info.bodies {
            builder.walk(body, SignSet::POSITIVE, &owner, 0);
        }
    }
    let values = solve_graph(offset, &builder.seeds, &builder.edges)?;
    let mut table = VarianceTable::default();
    for (id, (start, labels)) in &builder.nodes {
        let slots = (0..labels.len())
            .map(|index| values[start + index])
            .collect::<Vec<_>>();
        table.insert(*id, labels.clone(), slots);
    }
    Ok(table)
}
/// How a label occurrence is bound at a checked conversion site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LabelClass {
    /// A declaration-scope lifetime. It is rigid for this occurrence.
    Free,
    /// A binder owned by the checked occurrence; alpha-renamable.
    Bound(usize),
    /// A compiler-internal identity. It is rigid and never a fresh name.
    Internal,
}
/// Occurrence-specific classification of lifetime labels. The map is kept on
/// the checked conversion, never on an interned function-type ID, because two
/// occurrences can share one canonical contract.
#[derive(Clone, Debug, Default)]
pub(crate) struct LabelEnv {
    free: BTreeSet<String>,
    bound: BTreeMap<String, usize>,
}
impl LabelEnv {
    pub(crate) fn new() -> Self {
        Self::default()
    }
    pub(crate) fn free(&mut self, name: &str) -> &mut Self {
        self.free.insert(name.to_owned());
        self
    }
    pub(crate) fn bind(&mut self, name: &str, binder: usize) -> &mut Self {
        self.bound.insert(name.to_owned(), binder);
        self
    }
    /// Classify a label. Unknown printed names are deliberately not guessed.
    pub(crate) fn classify(&self, name: &str) -> Option<LabelClass> {
        if let Some(binder) = self.bound.get(name) {
            return Some(LabelClass::Bound(*binder));
        }
        if self.free.contains(name) {
            return Some(LabelClass::Free);
        }
        if name.starts_with('<') {
            return Some(LabelClass::Internal);
        }
        None
    }
}
/// One direction required at a checked lifetime occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LabelPolarity {
    Positive,
    Negative,
    Invariant,
}
impl LabelPolarity {
    pub(crate) fn of(position: SignSet) -> Option<Self> {
        if position.is_unused() {
            None
        } else if position.is_invariant() {
            Some(Self::Invariant)
        } else if position.is_positive_only() {
            Some(Self::Positive)
        } else {
            Some(Self::Negative)
        }
    }
}
/// A path inside a checked type. Parameter/result roots keep callable
/// occurrences distinct even when their canonical `BorrowSig` is interned.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum WitnessPath {
    Parameter(usize),
    Result,
}
/// One accepted lifetime pair. `source`/`target` are printed labels for
/// diagnostics; canonical labels remain in the checked contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Obligation {
    pub path: WitnessPath,
    pub fields: Vec<usize>,
    pub polarity: LabelPolarity,
    pub source: Option<String>,
    pub target: Option<String>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Witness {
    pub obligations: Vec<Obligation>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum WitnessError {
    /// A borrowed occurrence has no classified label. This is an unresolved
    /// obligation, not permission to compare erased shapes.
    UnclassifiedLabel {
        path: WitnessPath,
        fields: Vec<usize>,
        label: String,
    },
    /// One side of a borrowed leaf is unlabelled while the other is named.
    MissingLabel {
        path: WitnessPath,
        fields: Vec<usize>,
    },
    /// A positive occurrence did not prove `source: target`.
    MissingOutlives {
        path: WitnessPath,
        fields: Vec<usize>,
        long: String,
        short: String,
    },
    /// An invariant occurrence did not prove identical binder identity.
    NotIdentical {
        path: WitnessPath,
        fields: Vec<usize>,
        source: String,
        target: String,
    },
    /// The two checked types do not have compatible erased structure. This is
    /// an internal integration error: erased shape must be established first.
    ShapeMismatch {
        path: WitnessPath,
        fields: Vec<usize>,
    },
    /// The witness hit its finite nesting budget. This is a checked rejection,
    /// never a successful partial witness: silently skipping the remaining
    /// obligations would accept an unproved conversion.
    Budget {
        path: WitnessPath,
        fields: Vec<usize>,
    },
    /// An arrow occurrence demanded a contract it cannot express.
    CallableContract,
}
impl WitnessError {
    pub(crate) fn message(&self) -> String {
        match self {
            Self::UnclassifiedLabel { label, .. } => format!(
                "lifetime '{label}' has no occurrence-specific binder classification; refusing to guess free-versus-bound identity"
            ),
            Self::MissingLabel { .. } => {
                "a borrowed leaf on one side has no classified lifetime while the other side names one; an unlabelled leaf is not a wildcard region".to_owned()
            }
            Self::MissingOutlives {
                long,
                short,
                path,
                fields,
            } => format!(
                "this conversion requires {}{} to outlive {}{}, but no established outlives edge proves it",
                describe_label(long),
                describe_fields(fields, path),
                describe_label(short),
                describe_fields(fields, path)
            ),
            Self::NotIdentical {
                source,
                target,
                path,
                fields,
            } => format!(
                "this lifetime position is invariant: {}{} and {}{} must denote the same binder identity",
                describe_label(source),
                describe_fields(fields, path),
                describe_label(target),
                describe_fields(fields, path)
            ),
            Self::ShapeMismatch { .. } => {
                "internal error: lifetime witness received types with different erased shapes".to_owned()
            }
            Self::Budget { .. } => {
                "the lifetime witness exceeded its finite nesting budget; this conversion is too deeply nested to prove and is rejected".to_owned()
            }
            Self::CallableContract => {
                "the callable contracts are not compatible: parameter direction, result direction, or instantiated outlives bounds disagree".to_owned()
            }
        }
    }
}
fn describe_label(label: &str) -> String {
    if label.starts_with('<') || label.starts_with('#') {
        crate::runtime_types::lifetime_label_text(label)
    } else {
        format!("lifetime '{label}'")
    }
}
fn describe_fields(fields: &[usize], path: &WitnessPath) -> String {
    let mut text = match path {
        WitnessPath::Parameter(index) => format!(" at parameter {}", index + 1),
        WitnessPath::Result => " at the result".to_owned(),
    };
    if !fields.is_empty() {
        text.push_str(&format!(
            " field path {}",
            fields
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(".")
        ));
    }
    text
}
/// Existing checked evidence used by the witness. `outlives` must come from
/// declared bounds plus the ownership pass's lexical facts; the witness itself
/// never invents an edge.
pub(crate) trait Evidence {
    fn outlives(&self, long: &str, short: &str) -> bool;
    /// Identity after valid substitution. Internal identities are rigid and
    /// only equal to themselves.
    fn identical(&self, left: &str, right: &str) -> bool {
        left == right
    }
}
/// Evidence backed by a closure. Used by the executable checker, which already
/// owns the signature bounds.
pub(crate) struct ClosureEvidence<F> {
    pub outlives: F,
}
impl<F: Fn(&str, &str) -> bool> Evidence for ClosureEvidence<F> {
    fn outlives(&self, long: &str, short: &str) -> bool {
        (self.outlives)(long, short)
    }
}
/// One checked type occurrence: the runtime type plus the outer borrow label
/// that its `Type` variant does not itself carry.
#[derive(Clone, Debug)]
pub(crate) struct TypeOccurrence {
    pub ty: Type,
    pub own: Option<String>,
}
impl TypeOccurrence {
    pub(crate) fn new(ty: Type) -> Self {
        Self { ty, own: None }
    }
}
/// Check a lifetime-only conversion between two erased-shape-compatible type
/// occurrences. The caller must already have established structural
/// compatibility; this judgment adds the lifetime obligations.
pub(crate) fn witness(
    types: &Types<'_>,
    source: &TypeOccurrence,
    target: &TypeOccurrence,
    env: &LabelEnv,
    evidence: &dyn Evidence,
) -> Result<Witness, WitnessError> {
    let mut check = WitnessCheck {
        types,
        env: env.clone(),
        evidence,
        canonical: None,
        witness: Witness::default(),
    };
    check.types(
        source.ty,
        target.ty,
        source.own.as_deref(),
        target.own.as_deref(),
        SignSet::POSITIVE,
        &WitnessPath::Result,
        &mut Vec::new(),
        0,
    )?;
    Ok(check.witness)
}
struct WitnessCheck<'a, 'b> {
    types: &'a Types<'b>,
    /// Occurrence environment. Owned so a nested callable can install its own
    /// canonical bound environment for its parameter/result records and restore
    /// the enclosing one afterwards.
    env: LabelEnv,
    evidence: &'a dyn Evidence,
    /// The canonical borrow contract of the innermost callable occurrence.
    /// Canonical `#k` labels are alpha-renamable binders of that occurrence, so
    /// their outlives/identity evidence comes from the target contract rather
    /// than from the enclosing function's printed lifetime bounds.
    canonical: Option<BorrowSig>,
    witness: Witness,
}
impl WitnessCheck<'_, '_> {
    fn pair(
        &mut self,
        source: Option<&str>,
        target: Option<&str>,
        position: SignSet,
        path: &WitnessPath,
        fields: &[usize],
    ) -> Result<(), WitnessError> {
        let Some(polarity) = LabelPolarity::of(position) else {
            // An unused occurrence carries no obligation. A borrowed leaf at an
            // unused slot is contradictory metadata, not a proof.
            if source.is_some() || target.is_some() {
                return Err(WitnessError::MissingLabel {
                    path: path.clone(),
                    fields: fields.to_vec(),
                });
            }
            return Ok(());
        };
        match (source, target) {
            (None, None) => Ok(()),
            (Some(source), Some(target)) => {
                let source_class = self.env.classify(source);
                let target_class = self.env.classify(target);
                if polarity == LabelPolarity::Invariant {
                    // An invariant position requires identical binder identity
                    // after valid substitution. An internal/fresh identity is
                    // rigid: it is never a wildcard that can stand for a named
                    // binder, and an unclassified callee label has no proof at
                    // this occurrence. Both are checked rejections here rather
                    // than deferred acceptance.
                    let source_class =
                        source_class.ok_or_else(|| WitnessError::UnclassifiedLabel {
                            path: path.clone(),
                            fields: fields.to_vec(),
                            label: source.to_owned(),
                        })?;
                    let target_class =
                        target_class.ok_or_else(|| WitnessError::UnclassifiedLabel {
                            path: path.clone(),
                            fields: fields.to_vec(),
                            label: target.to_owned(),
                        })?;
                    if source != target
                        && (matches!(source_class, LabelClass::Internal)
                            || matches!(target_class, LabelClass::Internal))
                    {
                        return Err(WitnessError::NotIdentical {
                            path: path.clone(),
                            fields: fields.to_vec(),
                            source: source.to_owned(),
                            target: target.to_owned(),
                        });
                    }
                } else if source_class.is_none() || target_class.is_none() {
                    // Outside an invariant position an unclassified label is a
                    // callee-instantiated or elided identity whose outlives
                    // relation is owned by the call/provenance evidence, not by
                    // this same-scope witness. The surrounding call boundary
                    // checks it; this pair contributes no local obligation.
                    return Ok(());
                }
                // Elided and compiler-generated identities are rigid, but
                // their actual outlives relation is established by ownership
                // provenance, not by the named function bounds. Defer only a
                // non-invariant pair that involves such an identity; an
                // invariant pair was rejected above and a fully classified pair
                // still produces a checked obligation.
                if polarity != LabelPolarity::Invariant
                    && source != target
                    && (is_internal_label(source) || is_internal_label(target))
                {
                    return Ok(());
                }
                match polarity {
                    LabelPolarity::Positive => {
                        if !self.outlives(source, target) {
                            return Err(WitnessError::MissingOutlives {
                                path: path.clone(),
                                fields: fields.to_vec(),
                                long: source.to_owned(),
                                short: target.to_owned(),
                            });
                        }
                    }
                    LabelPolarity::Negative => {
                        if !self.outlives(target, source) {
                            return Err(WitnessError::MissingOutlives {
                                path: path.clone(),
                                fields: fields.to_vec(),
                                long: target.to_owned(),
                                short: source.to_owned(),
                            });
                        }
                    }
                    LabelPolarity::Invariant => {
                        if !self.identical(source, target) {
                            return Err(WitnessError::NotIdentical {
                                path: path.clone(),
                                fields: fields.to_vec(),
                                source: source.to_owned(),
                                target: target.to_owned(),
                            });
                        }
                    }
                }
                self.witness.obligations.push(Obligation {
                    path: path.clone(),
                    fields: fields.to_vec(),
                    polarity,
                    source: Some(source.to_owned()),
                    target: Some(target.to_owned()),
                });
                Ok(())
            }
            _ if polarity == LabelPolarity::Invariant => Err(WitnessError::MissingLabel {
                path: path.clone(),
                fields: fields.to_vec(),
            }),
            // One side of a non-invariant borrowed leaf is unlabelled. The
            // missing relation belongs to the surrounding call/provenance
            // evidence, so this same-scope witness contributes no local
            // obligation rather than inventing a region.
            _ => Ok(()),
        }
    }
    /// Outlives evidence. Canonical arrow labels are resolved against the
    /// innermost callable contract; ordinary declared labels use the enclosing
    /// function's evidence.
    fn outlives(&self, long: &str, short: &str) -> bool {
        if let Some(contract) = &self.canonical
            && (is_canonical_label(long) || is_canonical_label(short))
        {
            return contract.outlives(long, short);
        }
        self.evidence.outlives(long, short)
    }
    fn identical(&self, left: &str, right: &str) -> bool {
        if self.canonical.is_some() && (is_canonical_label(left) || is_canonical_label(right)) {
            // Canonical labels are alpha-renamed positionally by
            // `borrow_witness`; after that instantiation, identity is exact.
            return left == right;
        }
        self.evidence.identical(left, right)
    }
    #[allow(clippy::too_many_arguments)]
    fn types(
        &mut self,
        source: Type,
        target: Type,
        source_own: Option<&str>,
        target_own: Option<&str>,
        position: SignSet,
        path: &WitnessPath,
        fields: &mut Vec<usize>,
        depth: usize,
    ) -> Result<(), WitnessError> {
        if depth >= 64 {
            return Err(WitnessError::Budget {
                path: path.clone(),
                fields: fields.clone(),
            });
        }
        match (source, target) {
            (Type::Str, Type::Str) | (Type::StrMut, Type::StrMut) => {
                self.pair(source_own, target_own, position, path, fields)
            }
            (Type::Ref(a), Type::Ref(b)) => {
                self.pair(source_own, target_own, SignSet::POSITIVE, path, fields)?;
                self.types(
                    self.types.pointees[a],
                    self.types.pointees[b],
                    None,
                    None,
                    position.compose(SignSet::POSITIVE),
                    path,
                    fields,
                    depth + 1,
                )
            }
            (Type::RefMut(a), Type::RefMut(b)) => {
                self.pair(source_own, target_own, SignSet::POSITIVE, path, fields)?;
                self.types(
                    self.types.pointees[a],
                    self.types.pointees[b],
                    None,
                    None,
                    position.compose(SignSet::INVARIANT),
                    path,
                    fields,
                    depth + 1,
                )
            }
            (Type::RefMut(a), Type::Ref(b)) => {
                // The explicit checked exclusive-to-shared downgrade keeps its
                // own rules; the lifetime witness only relates the outer borrow.
                self.pair(source_own, target_own, SignSet::POSITIVE, path, fields)?;
                self.types(
                    self.types.pointees[a],
                    self.types.pointees[b],
                    None,
                    None,
                    position.compose(SignSet::INVARIANT),
                    path,
                    fields,
                    depth + 1,
                )
            }
            (Type::Slice(a), Type::Slice(b)) | (Type::SliceMut(a), Type::SliceMut(b)) => {
                self.pair(source_own, target_own, SignSet::POSITIVE, path, fields)?;
                let inner = if matches!(source, Type::SliceMut(_)) {
                    SignSet::INVARIANT
                } else {
                    SignSet::POSITIVE
                };
                self.types(
                    self.types.pointees[a],
                    self.types.pointees[b],
                    None,
                    None,
                    position.compose(inner),
                    path,
                    fields,
                    depth + 1,
                )
            }
            (Type::Annotated(a, label), Type::Annotated(b, target_label)) => {
                let source_label = self.types.reference_label_name(label);
                let target_label = self.types.reference_label_name(target_label);
                self.pair(
                    source_label.as_deref(),
                    target_label.as_deref(),
                    position,
                    path,
                    fields,
                )?;
                self.types(
                    self.types.pointees[a],
                    self.types.pointees[b],
                    None,
                    None,
                    position.compose(SignSet::POSITIVE),
                    path,
                    fields,
                    depth + 1,
                )
            }
            // A container element annotation is metadata on the same erased
            // reference type. Unwrap it when the other occurrence is a plain
            // reference so the label still becomes a checked obligation rather
            // than an internal shape mismatch.
            (Type::Annotated(a, label), _) => {
                let source_label = self.types.reference_label_name(label);
                self.types(
                    self.types.pointees[a],
                    target,
                    source_label.as_deref(),
                    target_own,
                    position,
                    path,
                    fields,
                    depth + 1,
                )
            }
            (_, Type::Annotated(b, label)) => {
                let target_label = self.types.reference_label_name(label);
                self.types(
                    source,
                    self.types.pointees[b],
                    source_own,
                    target_label.as_deref(),
                    position,
                    path,
                    fields,
                    depth + 1,
                )
            }
            (Type::Box(a), Type::Box(b)) | (Type::Vec(a), Type::Vec(b)) => self.types(
                self.types.pointees[a],
                self.types.pointees[b],
                None,
                None,
                position.compose(SignSet::POSITIVE),
                path,
                fields,
                depth + 1,
            ),
            (Type::ArenaBox(a), Type::ArenaBox(b))
            | (Type::AllocBox(a), Type::AllocBox(b))
            | (Type::AllocVec(a), Type::AllocVec(b)) => self.types(
                self.types.pointees[a],
                self.types.pointees[b],
                None,
                None,
                position.compose(SignSet::INVARIANT),
                path,
                fields,
                depth + 1,
            ),
            (Type::Enum(a), Type::Enum(b))
            | (Type::Enum(a), Type::Variants(b, _))
            | (Type::Variants(a, _), Type::Enum(b))
            | (Type::Variants(a, _), Type::Variants(b, _)) => {
                let left_name = self.types.enums[a].name.clone();
                let right_name = self.types.enums[b].name.clone();
                if left_name == "TaskExit" || right_name == "TaskExit" {
                    // Existing task-exit provenance stays exact; no new payload
                    // variance is introduced here.
                    return self.exact_enum(a, b, path, fields, depth);
                }
                let same_definition =
                    self.types.enums[a].definition == self.types.enums[b].definition;
                if self.types.enums[a].record && self.types.enums[b].record && same_definition {
                    for index in 0..self.types.enums[a]
                        .lifetimes
                        .len()
                        .min(self.types.enums[b].lifetimes.len())
                    {
                        let source_label = self.types.enums[a].lifetimes[index].clone();
                        let target_label = self.types.enums[b].lifetimes[index].clone();
                        let variance = self
                            .types
                            .variance
                            .of(self.types.enums[a].definition, index)
                            .ok_or_else(|| WitnessError::UnclassifiedLabel {
                                path: path.clone(),
                                fields: fields.clone(),
                                label: source_label.clone(),
                            })?;
                        self.pair(
                            Some(&source_label),
                            Some(&target_label),
                            position.compose(variance),
                            path,
                            fields,
                        )?;
                    }
                    // A lifetime may occur only inside a type argument
                    // (`Outer<W<'a>>`). Type parameters have no inferred
                    // lifetime variance, so a borrowing argument is compared
                    // invariantly, like an unknown named argument in the table.
                    let arguments = self.types.enums[a]
                        .arguments
                        .iter()
                        .copied()
                        .zip(self.types.enums[b].arguments.iter().copied())
                        .collect::<Vec<_>>();
                    for (source_argument, target_argument) in arguments {
                        if crate::runtime_types::has_borrow(self.types, source_argument)
                            || crate::runtime_types::has_borrow(self.types, target_argument)
                        {
                            self.types(
                                source_argument,
                                target_argument,
                                None,
                                None,
                                position.compose(SignSet::INVARIANT),
                                path,
                                fields,
                                depth + 1,
                            )?;
                        }
                    }
                    Ok(())
                } else if self.types.enums[a].record && self.types.enums[b].structural {
                    self.structural_into(a, b, path, fields, depth)
                } else {
                    self.exact_enum(a, b, path, fields, depth)
                }
            }
            (Type::Fn(a), Type::Fn(b)) | (Type::Once(a), Type::Once(b)) => {
                let (left, right) = (&self.types.function_types[a], &self.types.function_types[b]);
                self.callable(left, right, path, depth)
            }
            (left, right) if left == right => Ok(()),
            _ => Err(WitnessError::ShapeMismatch {
                path: path.clone(),
                fields: fields.clone(),
            }),
        }
    }
    fn structural_into(
        &mut self,
        source: usize,
        target: usize,
        path: &WitnessPath,
        fields: &mut Vec<usize>,
        depth: usize,
    ) -> Result<(), WitnessError> {
        let source_variant = self.types.enums[source].variants[0].clone();
        let target_variant = self.types.enums[target].variants[0].clone();
        for (target_index, target_ty) in target_variant.fields.iter().enumerate() {
            let Some(source_index) = source_variant
                .names
                .iter()
                .position(|name| name == &target_variant.names[target_index])
            else {
                return Err(WitnessError::ShapeMismatch {
                    path: path.clone(),
                    fields: fields.clone(),
                });
            };
            let source_leaf = self.types.enums[source].field_lifetimes[source_index].clone();
            let target_leaf = self.types.enums[target].field_lifetimes[target_index].clone();
            fields.push(source_index);
            let result = self.types(
                source_variant.fields[source_index],
                *target_ty,
                source_leaf.as_deref(),
                target_leaf.as_deref(),
                SignSet::INVARIANT,
                path,
                fields,
                depth + 1,
            );
            fields.pop();
            result?;
        }
        Ok(())
    }
    fn exact_enum(
        &mut self,
        source: usize,
        target: usize,
        path: &WitnessPath,
        fields: &mut Vec<usize>,
        depth: usize,
    ) -> Result<(), WitnessError> {
        let left_lifetimes = self.types.enums[source].lifetimes.clone();
        let right_lifetimes = self.types.enums[target].lifetimes.clone();
        let left_variants = self.types.enums[source].variants.clone();
        let right_variants = self.types.enums[target].variants.clone();
        for (source_label, target_label) in left_lifetimes.iter().zip(&right_lifetimes) {
            self.pair(
                Some(source_label),
                Some(target_label),
                SignSet::INVARIANT,
                path,
                fields,
            )?;
        }
        for (source_variant, target_variant) in left_variants.iter().zip(&right_variants) {
            for (index, (source_field, target_field)) in source_variant
                .fields
                .iter()
                .zip(&target_variant.fields)
                .enumerate()
            {
                fields.push(index);
                let result = self.types(
                    *source_field,
                    *target_field,
                    None,
                    None,
                    SignSet::INVARIANT,
                    path,
                    fields,
                    depth + 1,
                );
                fields.pop();
                result?;
            }
        }
        Ok(())
    }
    fn callable(
        &mut self,
        source: &FunctionType,
        target: &FunctionType,
        path: &WitnessPath,
        depth: usize,
    ) -> Result<(), WitnessError> {
        let _ = path;
        if depth >= 64 {
            return Err(WitnessError::CallableContract);
        }
        let witness = borrow_witness(&source.borrows, &target.borrows)?;
        self.witness.obligations.extend(witness.obligations);
        // A nested callable is its own closed occurrence: its canonical arrow
        // labels are bound here, not inherited from the enclosing function.
        // Install that environment (and its canonical evidence) only while
        // checking the callable's parameter/result records.
        let mut env = LabelEnv::new();
        for label in bound_labels(&source.borrows)
            .into_iter()
            .chain(bound_labels(&target.borrows))
        {
            env.bind(&label, 0);
        }
        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_canonical = self.canonical.replace(target.borrows.clone());
        let result = (|| {
            // Nested parameter and result records can carry lifetime arguments
            // beyond the flat BorrowSig leaves. Compare them in the callable's
            // canonical bound environment with parameter contravariance applied
            // once.
            for (index, (source_ty, target_ty)) in
                source.parameters.iter().zip(&target.parameters).enumerate()
            {
                self.types(
                    *target_ty,
                    *source_ty,
                    None,
                    None,
                    SignSet::NEGATIVE,
                    &WitnessPath::Parameter(index),
                    &mut Vec::new(),
                    depth + 1,
                )?;
            }
            self.types(
                source.result,
                target.result,
                None,
                None,
                SignSet::POSITIVE,
                &WitnessPath::Result,
                &mut Vec::new(),
                depth + 1,
            )
        })();
        self.env = saved_env;
        self.canonical = saved_canonical;
        result
    }
}
fn is_canonical_label(label: &str) -> bool {
    label
        .strip_prefix('#')
        .is_some_and(|index| index.parse::<u8>().is_ok())
}
fn is_internal_label(label: &str) -> bool {
    label.starts_with('<')
}
fn bound_labels(sig: &BorrowSig) -> BTreeSet<String> {
    let mut labels = BTreeSet::new();
    labels.extend(sig.parameters.iter().flatten().cloned());
    labels.extend(sig.result.iter().cloned());
    for leaf in sig.parameter_leaves.iter().flatten() {
        labels.extend(leaf.lifetime.iter().cloned());
    }
    labels.extend(
        sig.result_leaves
            .iter()
            .flat_map(|leaf| leaf.lifetime.clone()),
    );
    labels
}
/// Build the callable occurrence witness. Arrow lifetimes are bound by the
/// arrow, so canonical `#k` labels are classified per occurrence rather than
/// looked up through an interned function-type ID.
pub(crate) fn borrow_witness(
    source: &BorrowSig,
    target: &BorrowSig,
) -> Result<Witness, WitnessError> {
    if source.capture_result != target.capture_result {
        return Err(WitnessError::CallableContract);
    }
    let arity = source
        .parameters
        .len()
        .max(target.parameters.len())
        .max(source.parameter_leaves.len())
        .max(target.parameter_leaves.len());
    let at = |sig: &BorrowSig, index: usize| sig.parameters.get(index).cloned().flatten();
    let mut env = LabelEnv::new();
    for label in bound_labels(source).into_iter().chain(bound_labels(target)) {
        env.bind(&label, 0);
    }
    let mut witness = Witness::default();
    let mut pairs: Vec<(String, String, WitnessPath, Vec<usize>, LabelPolarity)> = Vec::new();
    for index in 0..arity {
        match (at(source, index), at(target, index)) {
            (Some(source_label), Some(target_label)) => {
                pairs.push((
                    source_label,
                    target_label,
                    WitnessPath::Parameter(index),
                    Vec::new(),
                    LabelPolarity::Negative,
                ));
            }
            (None, None) => {}
            _ => return Err(WitnessError::CallableContract),
        }
        let source_leaves = source
            .parameter_leaves
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let target_leaves = target
            .parameter_leaves
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        if source_leaves.len() != target_leaves.len() {
            return Err(WitnessError::CallableContract);
        }
        for source_leaf in source_leaves {
            let Some(target_leaf) = target_leaves
                .iter()
                .find(|leaf| leaf.path == source_leaf.path)
            else {
                return Err(WitnessError::CallableContract);
            };
            match (&source_leaf.lifetime, &target_leaf.lifetime) {
                (Some(source_label), Some(target_label)) => pairs.push((
                    source_label.clone(),
                    target_label.clone(),
                    WitnessPath::Parameter(index),
                    source_leaf.path.clone(),
                    LabelPolarity::Negative,
                )),
                (None, None) => {}
                _ => return Err(WitnessError::CallableContract),
            }
        }
    }
    match (&source.result, &target.result) {
        (Some(source_label), Some(target_label)) => pairs.push((
            source_label.clone(),
            target_label.clone(),
            WitnessPath::Result,
            Vec::new(),
            LabelPolarity::Positive,
        )),
        (None, None) => {}
        _ => return Err(WitnessError::CallableContract),
    }
    if source.result_leaves.len() != target.result_leaves.len() {
        return Err(WitnessError::CallableContract);
    }
    for source_leaf in &source.result_leaves {
        let Some(target_leaf) = target
            .result_leaves
            .iter()
            .find(|leaf| leaf.path == source_leaf.path)
        else {
            return Err(WitnessError::CallableContract);
        };
        match (&source_leaf.lifetime, &target_leaf.lifetime) {
            (Some(source_label), Some(target_label)) => pairs.push((
                source_label.clone(),
                target_label.clone(),
                WitnessPath::Result,
                source_leaf.path.clone(),
                LabelPolarity::Positive,
            )),
            (None, None) => {}
            _ => return Err(WitnessError::CallableContract),
        }
    }
    let mut map: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (source_label, target_label, _, _, _) in &pairs {
        map.entry(source_label.clone())
            .or_default()
            .insert(target_label.clone());
    }
    for (long, short) in &source.bounds {
        let (Some(longs), Some(shorts)) = (map.get(long), map.get(short)) else {
            continue;
        };
        if !longs
            .iter()
            .all(|long| shorts.iter().all(|short| target.outlives(long, short)))
        {
            return Err(WitnessError::CallableContract);
        }
    }
    if let (Some(source_result), Some(target_result)) = (&source.result, &target.result) {
        for index in 0..arity {
            let (Some(source_parameter), Some(target_parameter)) =
                (at(source, index), at(target, index))
            else {
                continue;
            };
            if source.outlives(&source_parameter, source_result)
                && !target.outlives(&target_parameter, target_result)
            {
                return Err(WitnessError::CallableContract);
            }
        }
    }
    for index in 0..arity {
        let source_leaves = source
            .parameter_leaves
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let target_leaves = target
            .parameter_leaves
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        for source_leaf in source_leaves {
            let Some(target_leaf) = target_leaves
                .iter()
                .find(|leaf| leaf.path == source_leaf.path)
            else {
                return Err(WitnessError::CallableContract);
            };
            let (Some(source_lifetime), Some(mapped)) =
                (&source_leaf.lifetime, &target_leaf.lifetime)
            else {
                continue;
            };
            let Some(source_result) = source
                .result_leaves
                .iter()
                .find(|leaf| leaf.path == source_leaf.path)
            else {
                continue;
            };
            let Some(target_result) = target
                .result_leaves
                .iter()
                .find(|leaf| leaf.path == source_leaf.path)
            else {
                return Err(WitnessError::CallableContract);
            };
            if let (Some(source_result), Some(target_result)) =
                (&source_result.lifetime, &target_result.lifetime)
                && source.outlives(source_lifetime, source_result)
                && !target.outlives(mapped, target_result)
            {
                return Err(WitnessError::CallableContract);
            }
        }
    }
    for (source_label, target_label, path, fields, polarity) in pairs {
        // The callable contract accepts canonical arrow labels. They are
        // classified as bound in this occurrence; no interned-type map exists.
        for label in [&source_label, &target_label] {
            if env.classify(label).is_none() {
                return Err(WitnessError::UnclassifiedLabel {
                    path: path.clone(),
                    fields: fields.clone(),
                    label: label.clone(),
                });
            }
        }
        witness.obligations.push(Obligation {
            path,
            fields,
            polarity,
            source: Some(source_label),
            target: Some(target_label),
        });
    }
    Ok(witness)
}
#[cfg(test)]
mod tests {
    use super::*;
    const ALL: [SignSet; 4] = [
        SignSet::UNUSED,
        SignSet::POSITIVE,
        SignSet::NEGATIVE,
        SignSet::INVARIANT,
    ];
    #[test]
    fn exhaustive_join_and_composition_are_a_distributive_lattice() {
        for left in ALL {
            for right in ALL {
                let joined = left.join(right);
                assert_eq!(joined, right.join(left));
                for third in ALL {
                    assert_eq!(joined.join(third), left.join(right.join(third)));
                    assert_eq!(
                        left.compose(right.join(third)),
                        left.compose(right).join(left.compose(third))
                    );
                    assert_eq!(
                        right.join(third).compose(left),
                        right.compose(left).join(third.compose(left))
                    );
                }
            }
        }
        for value in ALL {
            assert_eq!(SignSet::UNUSED.compose(value), SignSet::UNUSED);
            assert_eq!(value.compose(SignSet::UNUSED), SignSet::UNUSED);
            assert_eq!(SignSet::POSITIVE.compose(value), value);
            assert_eq!(value.compose(SignSet::POSITIVE), value);
            assert_eq!(
                SignSet::NEGATIVE.compose(SignSet::NEGATIVE),
                SignSet::POSITIVE
            );
            assert_eq!(
                SignSet::NEGATIVE.compose(SignSet::POSITIVE),
                SignSet::NEGATIVE
            );
            assert_eq!(
                SignSet::INVARIANT.compose(value),
                if value.is_unused() {
                    SignSet::UNUSED
                } else {
                    SignSet::INVARIANT
                }
            );
            assert_eq!(
                value.compose(SignSet::INVARIANT),
                if value.is_unused() {
                    SignSet::UNUSED
                } else {
                    SignSet::INVARIANT
                }
            );
            assert_eq!(value.join(SignSet::INVARIANT), SignSet::INVARIANT);
            assert_eq!(value.join(SignSet::UNUSED), value);
        }
    }
    fn solve(
        nodes: usize,
        seeds: &[(usize, SignSet)],
        edges: &[(SignSet, usize, usize)],
    ) -> Vec<SignSet> {
        solve_graph(
            nodes,
            &seeds.iter().copied().collect::<BTreeMap<_, _>>(),
            edges,
        )
        .expect("finite graph")
    }
    #[test]
    fn seeded_recursive_graphs_ignore_seedless_self_edges() {
        let values = solve(
            3,
            &[(1, SignSet::POSITIVE)],
            &[
                (SignSet::POSITIVE, 0, 0),
                (SignSet::POSITIVE, 2, 2),
                (SignSet::POSITIVE, 1, 0),
            ],
        );
        assert_eq!(values[0], SignSet::POSITIVE);
        assert_eq!(values[1], SignSet::POSITIVE);
        assert_eq!(values[2], SignSet::UNUSED);
    }
    #[test]
    fn fixed_point_is_order_independent_and_reaches_invariant() {
        let edges = [
            (SignSet::POSITIVE, 0, 0),
            (SignSet::INVARIANT, 0, 1),
            (SignSet::POSITIVE, 1, 2),
            (SignSet::POSITIVE, 2, 0),
        ];
        let forward = solve(3, &[(0, SignSet::POSITIVE)], &edges);
        let mut reversed = edges;
        reversed.reverse();
        let backward = solve(3, &[(0, SignSet::POSITIVE)], &reversed);
        assert_eq!(forward, backward);
        assert_eq!(forward[0], SignSet::INVARIANT);
        assert_eq!(forward[1], SignSet::INVARIANT);
        assert_eq!(forward[2], SignSet::INVARIANT);
    }
    #[test]
    fn unused_stays_bottom_and_invariant_composition_is_not_absorbing() {
        assert_eq!(SignSet::INVARIANT.compose(SignSet::UNUSED), SignSet::UNUSED);
        assert_eq!(SignSet::UNUSED.join(SignSet::NEGATIVE), SignSet::NEGATIVE);
        assert_eq!(
            SignSet::NEGATIVE.compose(SignSet::INVARIANT),
            SignSet::INVARIANT
        );
        let values = solve(2, &[], &[(SignSet::INVARIANT, 0, 1)]);
        assert_eq!(values, vec![SignSet::UNUSED, SignSet::UNUSED]);
    }
    struct Bounds(BTreeSet<(String, String)>);
    impl Evidence for Bounds {
        fn outlives(&self, long: &str, short: &str) -> bool {
            long == short || self.0.contains(&(long.to_owned(), short.to_owned()))
        }
    }
    fn pair(
        env: &LabelEnv,
        evidence: &dyn Evidence,
        source: &str,
        target: &str,
        position: SignSet,
    ) -> Result<(), WitnessError> {
        if let Some(polarity) = LabelPolarity::of(position) {
            for label in [source, target] {
                if env.classify(label).is_none() {
                    return Err(WitnessError::UnclassifiedLabel {
                        path: WitnessPath::Result,
                        fields: Vec::new(),
                        label: label.to_owned(),
                    });
                }
            }
            match polarity {
                LabelPolarity::Positive if !evidence.outlives(source, target) => {
                    return Err(WitnessError::MissingOutlives {
                        path: WitnessPath::Result,
                        fields: Vec::new(),
                        long: source.to_owned(),
                        short: target.to_owned(),
                    });
                }
                LabelPolarity::Negative if !evidence.outlives(target, source) => {
                    return Err(WitnessError::MissingOutlives {
                        path: WitnessPath::Result,
                        fields: Vec::new(),
                        long: target.to_owned(),
                        short: source.to_owned(),
                    });
                }
                LabelPolarity::Invariant if !evidence.identical(source, target) => {
                    return Err(WitnessError::NotIdentical {
                        path: WitnessPath::Result,
                        fields: Vec::new(),
                        source: source.to_owned(),
                        target: target.to_owned(),
                    });
                }
                _ => {}
            }
        }
        Ok(())
    }
    #[test]
    fn witnesses_distinguish_positive_negative_and_invariant_positions() {
        let bounds = Bounds(BTreeSet::from([("long".into(), "short".into())]));
        let mut env = LabelEnv::new();
        env.free("long").free("short");
        assert!(pair(&env, &bounds, "long", "short", SignSet::POSITIVE).is_ok());
        assert!(pair(&env, &bounds, "short", "long", SignSet::POSITIVE).is_err());
        assert!(pair(&env, &bounds, "short", "long", SignSet::NEGATIVE).is_ok());
        assert!(pair(&env, &bounds, "long", "short", SignSet::NEGATIVE).is_err());
        assert!(pair(&env, &bounds, "long", "long", SignSet::INVARIANT).is_ok());
        assert!(pair(&env, &bounds, "long", "short", SignSet::INVARIANT).is_err());
        assert!(pair(&env, &bounds, "long", "missing", SignSet::POSITIVE).is_err());
    }
    #[test]
    fn witness_nesting_budget_is_a_rejection_not_success() {
        // A source-level type cannot normally exceed the witness budget before
        // lowering's own nesting limit. Build the erased graph directly so the
        // budget path stays covered: a conversion must never become `Ok` just
        // because recursion was cut off.
        let resolution = Resolution::default();
        let logical = crate::check::LogicalEnvironment {
            kernel: crate::kernel::Kernel::new(crate::kernel::Limits::default()),
            names: BTreeMap::new(),
            data: BTreeMap::new(),
            constructors: BTreeMap::new(),
            constructor_counts: BTreeMap::new(),
            nullary: BTreeMap::new(),
            definitions: Vec::new(),
        };
        let module = ast::Module { items: Vec::new() };
        let mut types = Types::new(&module, &resolution, &logical, BTreeSet::new()).unwrap();
        let mut ty = Type::I64;
        for _ in 0..70 {
            let pointee = types.pointees.len();
            types.pointees.push(ty);
            ty = Type::Box(pointee);
        }
        let env = LabelEnv::new();
        let evidence = Bounds(BTreeSet::new());
        let error = witness(
            &types,
            &TypeOccurrence::new(ty),
            &TypeOccurrence::new(ty),
            &env,
            &evidence,
        )
        .expect_err("a depleted nesting budget is not a proof");
        assert!(matches!(error, WitnessError::Budget { .. }), "{error:?}");
    }
}
