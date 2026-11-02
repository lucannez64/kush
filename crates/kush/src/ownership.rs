//! Ownership and grade checking.
//!
//! * Owned values (boxes, buffers, vectors, and data containing them) are
//!   affine: each is moved at most once and dropped automatically otherwise.
//! * Linear values (`#[linear]` data, or bindings graded `@[1]`) must be
//!   consumed exactly once on every path; an implicit drop is an error.
//! * Copyable values (scalars and data without owned/linear parts) are
//!   unrestricted.
//! * Borrows are immutable and cannot escape a call/full expression or their
//!   owner's scope. Loops must leave every outer owner as they found it.
use crate::{
    Diagnostic, Span,
    executable::{Block, Executable, Expr, ExprKind, Function, Pattern, Statement, Type},
    grades::Grade,
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, Diagnostic>;
pub(crate) fn check(program: &mut Executable) -> Result<()> {
    let mut owned = vec![false; program.enums.len()];
    let mut linear = program.enums.iter().map(|e| e.linear).collect::<Vec<_>>();
    loop {
        let (old_owned, old_linear) = (owned.clone(), linear.clone());
        for (index, layout) in program.enums.iter().enumerate() {
            let fields = || layout.variants.iter().flat_map(|v| v.fields.iter());
            owned[index] =
                fields().any(|ty| owns(*ty, &old_owned, &program.unions, &program.pointees));
            linear[index] |= fields().any(|ty| {
                is_linear(
                    *ty,
                    &old_linear,
                    &program.unions,
                    &program.pointees,
                    &program.function_types,
                )
            });
        }
        if owned == old_owned && linear == old_linear {
            break;
        }
    }
    for pointee in &program.pointees {
        if let Type::Vec(p) = pointee
            && is_linear(
                program.pointees[*p],
                &linear,
                &program.unions,
                &program.pointees,
                &program.function_types,
            )
        {
            return Err(Diagnostic::new(
                Span::default(),
                "vectors cannot hold linear values; a vector may drop or copy its elements",
            ));
        }
    }
    program.owned_enums = owned;
    program.linear_enums = linear;
    let calls = program
        .functions
        .iter()
        .map(|function| {
            let mut parameters = Vec::with_capacity(function.parameters);
            for (index, local) in function.locals.iter().take(function.parameters).enumerate() {
                if local.ty.is_view() {
                    parameters.push(vec![crate::runtime_types::BorrowLeaf {
                        path: vec![],
                        lifetime: function.parameter_lifetimes.get(index).cloned().flatten(),
                        mutable: local.ty.is_mut_slice(),
                    }]);
                } else if local.ty.is_ref() {
                    parameters.push(vec![crate::runtime_types::BorrowLeaf {
                        path: vec![],
                        lifetime: function.parameter_lifetimes.get(index).cloned().flatten(),
                        mutable: matches!(local.ty, Type::RefMut(_)),
                    }]);
                } else {
                    parameters.push(leaves_of(
                        &program.enums,
                        &program.pointees,
                        &program.reference_labels,
                        local.ty,
                    ));
                }
            }
            let result = if function.result.is_view() {
                CallResult::Slice {
                    lifetime: function.result_lifetime.clone(),
                    mutable: function.result.is_mut_slice(),
                }
            } else if function.result.is_ref() {
                CallResult::Reference {
                    lifetime: function.result_lifetime.clone(),
                    mutable: matches!(function.result, Type::RefMut(_)),
                }
            } else if function
                .result
                .layout()
                .is_some_and(|layout| program.enums[layout].borrowed)
                || container_carries_borrow(&program.pointees, function.result)
            {
                CallResult::Record(leaves_of(
                    &program.enums,
                    &program.pointees,
                    &program.reference_labels,
                    function.result,
                ))
            } else {
                CallResult::None
            };
            CallLifetime {
                parameters,
                result,
                bounds: function.lifetime_bounds.clone(),
            }
        })
        .collect::<Vec<_>>();
    let liveness = program
        .functions
        .iter()
        .map(|function| loan_liveness(function, &program.enums, &program.pointees))
        .collect::<Vec<_>>();
    let result_grades = program
        .functions
        .iter()
        .map(|function| {
            function.result_grade.map(|grade| {
                (
                    grade,
                    owns(
                        function.result,
                        &program.owned_enums,
                        &program.unions,
                        &program.pointees,
                    ) || is_linear(
                        function.result,
                        &program.linear_enums,
                        &program.unions,
                        &program.pointees,
                        &program.function_types,
                    ),
                )
            })
        })
        .collect::<Vec<_>>();
    for (function_index, function) in program.functions.iter_mut().enumerate() {
        let mut checker = Checker {
            enums: &program.enums,
            owned: &program.owned_enums,
            linear: &program.linear_enums,
            unions: &program.unions,
            pointees: &program.pointees,
            reference_labels: &program.reference_labels,
            functions: &program.function_types,
            result_grades: &result_grades,
            calls: &calls,
            result_lifetime: function.result_lifetime.clone(),
            result_type: function.result,
            parameter_lifetimes: function.parameter_lifetimes.clone(),
            lifetime_bounds: function.lifetime_bounds.clone(),
            parameter_count: function.parameters,
            available: vec![false; function.locals.len()],
            moved_at: vec![None; function.locals.len()],
            loans: BTreeSet::new(),
            exclusive_loans: BTreeSet::new(),
            shared_record_loans: BTreeSet::new(),
            temporary_shared: BTreeSet::new(),
            temporary_exclusive: BTreeSet::new(),
            reborrowed_views: BTreeSet::new(),
            bound_receivers: BTreeSet::new(),
            temporary_regions: Vec::new(),
            task_regions: Vec::new(),
            task_results: BTreeMap::new(),
            task_sources: vec![None; function.locals.len()],
            wrapped_results: BTreeMap::new(),
            wrapped_locals: vec![None; function.locals.len()],
            view_sources: vec![None; function.locals.len()],
            view_roots: vec![None; function.locals.len()],
            view_mut: vec![false; function.locals.len()],
            view_lifetimes: vec![None; function.locals.len()],
            reference_lifetimes: vec![None; function.locals.len()],
            view_splits: vec![SplitLabels::default(); function.locals.len()],
            view_fields: vec![None; function.locals.len()],
            in_field_subview: false,
            field_target: None,
            record_sources: vec![None; function.locals.len()],
            call_views: BTreeMap::new(),
            call_records: BTreeMap::new(),
            construct_records: BTreeMap::new(),
            call_lifetime_counter: 0,
            call_origins: BTreeMap::new(),
            call_splits: BTreeMap::new(),
            live: &liveness[function_index],
            capture_site: None,
            callee_site: None,
            borrowed_values: BTreeMap::new(),
            borrowed_closures: BTreeMap::new(),
            guard: false,
            reborrow: false,
            pending_linear: Vec::new(),
            locals: function.locals.clone(),
            resources: Vec::new(),
            local_resources: vec![None; function.locals.len()],
            loops: Vec::new(),
        };
        for (index, local) in function.locals.iter().enumerate() {
            if owns(local.ty, checker.owned, checker.unions, checker.pointees) {
                checker.local_resources[index] = Some(checker.resource(local.ty, function.span)?);
            }
            checker.available[index] = index < function.parameters;
            if index < function.parameters && local.ty.is_view() {
                // A borrowed view parameter is external: it owns no local
                // storage and is a root for capability ancestry. Its declared
                // lifetime controls whether it may be returned, and its type
                // controls whether an exclusive child may be derived from it.
                checker.view_sources[index] = Some(BTreeSet::new());
                checker.view_roots[index] = Some(BTreeSet::from([index]));
                checker.view_mut[index] = local.ty.is_mut_slice();
                checker.view_lifetimes[index] =
                    function.parameter_lifetimes.get(index).cloned().flatten();
            } else if index < function.parameters && local.ty.is_ref() {
                // A reference parameter borrows caller-owned storage for a
                // declared lifetime. It is not a local capability that can be
                // re-anchored, but a returned reference may name it.
                checker.reference_lifetimes[index] =
                    function.parameter_lifetimes.get(index).cloned().flatten();
            } else if index < function.parameters && checker.is_carrier_type(local.ty) {
                // A borrowed-record parameter is an aggregate of external
                // field views. Each leaf is rooted at this parameter and
                // carries the declared field lifetime from its type.
                checker.record_sources[index] =
                    Some(checker.parameter_record_provenance(index, local.ty));
            }
        }
        checker.block(&mut function.body)?;
        if function.body.ty != Type::Never {
            if function.body.ty.is_view() {
                let origins = function
                    .body
                    .tail
                    .as_ref()
                    .map(|tail| checker.view_origins(tail))
                    .unwrap_or_default();
                let lifetime = function
                    .body
                    .tail
                    .as_ref()
                    .and_then(|tail| checker.view_loan(tail).lifetime);
                checker.check_return_origins(
                    &origins,
                    lifetime.as_deref(),
                    function.body.ty.is_mut_slice(),
                    function.span,
                )?;
            } else if function.body.ty.is_ref() {
                let origins = function
                    .body
                    .tail
                    .as_ref()
                    .map(|tail| checker.view_origins(tail))
                    .unwrap_or_default();
                let lifetime = function
                    .body
                    .tail
                    .as_ref()
                    .and_then(|tail| checker.view_loan(tail).lifetime);
                checker.check_return_reference(
                    &origins,
                    lifetime.as_deref(),
                    matches!(function.body.ty, Type::RefMut(_)),
                    function.span,
                )?;
            } else if checker.is_carrier_type(function.body.ty) {
                let provenance = function
                    .body
                    .tail
                    .as_ref()
                    .map(|tail| checker.record_provenance(tail))
                    .unwrap_or_default();
                checker.check_return_record(&provenance, function.span)?;
            }
            checker.exit_check(
                0..function.parameters,
                function.span,
                "the function returns",
            )?;
        }
        function.locals = checker.locals;
        function.resources = checker.resources;
        function.local_resources = checker.local_resources;
    }
    Ok(())
}
/// One borrowed shared-slice leaf with its declared erased lifetime. This is
/// the checker-only bridge between a record type and its field provenance.
#[derive(Clone, Debug, Default)]
struct Loan {
    origins: BTreeSet<usize>,
    mutable: bool,
    splits: SplitLabels,
    lifetime: Option<String>,
    /// The record field this loan was derived from, when it is a direct
    /// projection of a local record. Two views of structurally disjoint fields
    /// of one record are separate capabilities; the record itself stays
    /// suspended for moves and whole-value access.
    field: Option<FieldBorrow>,
}
/// A borrowed record-field place: the local record root and the field index
/// path from its tag. The path is a checker-only identity, not a runtime value.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FieldBorrow {
    root: usize,
    path: Vec<usize>,
}
impl FieldBorrow {
    /// Two field places are disjoint when neither path is a prefix of the
    /// other. Paths under different roots are never considered disjoint here;
    /// ordinary root-intersection rules decide those.
    fn disjoint(&self, other: &Self) -> bool {
        self.root == other.root
            && !path_prefix(&self.path, &other.path)
            && !path_prefix(&other.path, &self.path)
    }
}
fn path_prefix(prefix: &[usize], path: &[usize]) -> bool {
    path.len() >= prefix.len() && path[..prefix.len()] == *prefix
}
/// Whether an owning container directly or transitively stores a reference
/// element. Borrowed records are handled separately by their layout flag.
fn container_carries_borrow(pointees: &[Type], ty: Type) -> bool {
    match ty {
        Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => match pointees[p] {
            Type::Annotated(..) | Type::Ref(_) | Type::RefMut(_) => true,
            inner => container_carries_borrow(pointees, inner),
        },
        _ => false,
    }
}
/// Per-leaf provenance of a record value. Paths are field indices from the
/// record root; a slice field is a leaf, and a nested borrowed record extends
/// the path. Ordinary copyable metadata contributes no leaf.
#[derive(Clone, Debug, Default)]
struct RecordProvenance {
    leaves: BTreeMap<Vec<usize>, Loan>,
}
impl RecordProvenance {
    fn merge(parts: impl IntoIterator<Item = RecordProvenance>) -> Self {
        let parts = parts.into_iter().collect::<Vec<_>>();
        let mut merged = RecordProvenance::default();
        let mut labels: BTreeMap<Vec<usize>, Vec<Option<String>>> = BTreeMap::new();
        for part in &parts {
            for (path, loan) in &part.leaves {
                let entry = merged.leaves.entry(path.clone()).or_default();
                entry.origins.extend(loan.origins.iter().copied());
                entry.mutable |= loan.mutable;
                entry.splits = intersect_splits(&entry.splits, &loan.splits);
                labels
                    .entry(path.clone())
                    .or_default()
                    .push(loan.lifetime.clone());
            }
        }
        for (path, entry) in &mut merged.leaves {
            let missing = parts.iter().any(|part| !part.leaves.contains_key(path));
            let first = labels
                .get(path)
                .and_then(|labels| labels.first().cloned())
                .unwrap_or(None);
            let uniform = labels
                .get(path)
                .is_some_and(|labels| labels.iter().all(|label| *label == first));
            entry.lifetime = if missing || !uniform { None } else { first };
            if missing {
                entry.mutable = true;
            }
        }
        merged
    }
}
fn intersect_splits(left: &SplitLabels, right: &SplitLabels) -> SplitLabels {
    let mut labels = left.clone();
    labels
        .0
        .retain(|group, side| right.0.get(group).is_some_and(|other| other == side));
    labels
}
/// Lifetime information needed at a call site: which parameter fields can
/// flow into the borrowed result, plus the callee's declared outlives relation.
struct CallLifetime {
    /// Borrowed leaves of every runtime parameter, in parameter order. A slice
    /// parameter contributes a root leaf; a borrowed record parameter
    /// contributes its flattened field leaves.
    parameters: Vec<Vec<crate::runtime_types::BorrowLeaf>>,
    result: CallResult,
    /// Reflexive-transitive callee bounds; `(long, short)` means `'long: 'short`.
    bounds: BTreeSet<(String, String)>,
}
#[derive(Clone)]
enum CallResult {
    None,
    Slice {
        lifetime: Option<String>,
        mutable: bool,
    },
    /// A returned `&Record`/`&mut Record`. The caller receives a one-word
    /// pointer into caller-owned storage; the loan is tracked until the
    /// reference's checked last use in the enclosing expression.
    Reference {
        lifetime: Option<String>,
        mutable: bool,
    },
    Record(Vec<crate::runtime_types::BorrowLeaf>),
}
fn leaves_of(
    enums: &[crate::runtime_types::Enum],
    pointees: &[Type],
    labels: &[String],
    ty: Type,
) -> Vec<crate::runtime_types::BorrowLeaf> {
    fn go(
        enums: &[crate::runtime_types::Enum],
        pointees: &[Type],
        labels: &[String],
        ty: Type,
        hint: Option<String>,
        path: &mut Vec<usize>,
        out: &mut Vec<crate::runtime_types::BorrowLeaf>,
    ) {
        match ty {
            Type::Slice(_) => out.push(crate::runtime_types::BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: false,
            }),
            Type::SliceMut(_) => out.push(crate::runtime_types::BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: true,
            }),
            Type::Ref(_) => out.push(crate::runtime_types::BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: false,
            }),
            Type::RefMut(_) => out.push(crate::runtime_types::BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: true,
            }),
            Type::Annotated(p, label) => out.push(crate::runtime_types::BorrowLeaf {
                path: path.clone(),
                lifetime: labels
                    .get(label as usize)
                    .filter(|label| !label.is_empty())
                    .cloned(),
                mutable: matches!(pointees[p], Type::RefMut(_)),
            }),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => {
                go(enums, pointees, labels, pointees[p], None, path, out)
            }
            Type::Enum(id) | Type::Variants(id, _)
                if enums[id].record || enums[id].name == "TaskExit" =>
            {
                if enums[id].record {
                    for (index, field) in enums[id].variants[0].fields.iter().enumerate() {
                        path.push(index);
                        let field_hint = enums[id].field_lifetimes[index].clone();
                        go(enums, pointees, labels, *field, field_hint, path, out);
                        path.pop();
                    }
                } else {
                    for variant in &enums[id].variants {
                        for field in &variant.fields {
                            go(enums, pointees, labels, *field, None, path, out);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(enums, pointees, labels, ty, None, &mut Vec::new(), &mut out);
    out
}
/// A callee lifetime for diagnostics; canonical callable lifetimes `#k`
/// print as the arrow's 'a, 'b, ...
fn describe_lifetime(name: &str) -> String {
    match name.strip_prefix('#').and_then(|n| n.parse::<u8>().ok()) {
        Some(index) if index < 26 => format!("'{}", (b'a' + index) as char),
        _ if name.starts_with('<') => "an elided lifetime".to_owned(),
        _ => format!("'{name}"),
    }
}
/// A caller-side lifetime for diagnostics, hiding internal labels.
fn describe_actual(name: &str) -> String {
    if name.starts_with("<local ") {
        "a borrow of a local owner".to_owned()
    } else if name.starts_with('<') {
        "a borrow with no named lifetime".to_owned()
    } else {
        format!("lifetime '{name}'")
    }
}
fn is_internal_lifetime(name: &str) -> bool {
    name.starts_with('<')
}
fn is_place_read(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Peek(_) => true,
        ExprKind::Project(base, _) => is_place_read(base),
        _ => false,
    }
}
fn owns(
    ty: Type,
    enums: &[bool],
    unions: &[crate::runtime_types::UnionType],
    pointees: &[Type],
) -> bool {
    let _ = pointees;
    match ty {
        Type::Box(_)
        | Type::Arena
        | Type::ArenaBox(_)
        | Type::Bytes
        | Type::String
        | Type::Vec(_)
        | Type::Once(_)
        | Type::Task(_) => true,
        Type::Enum(id) | Type::Variants(id, _) => enums[id],
        Type::Union(id) => unions[id]
            .members
            .iter()
            .any(|member| owns(*member, enums, unions, pointees)),
        _ => false,
    }
}
fn is_linear(
    ty: Type,
    enums: &[bool],
    unions: &[crate::runtime_types::UnionType],
    pointees: &[Type],
    functions: &[crate::runtime_types::FunctionType],
) -> bool {
    match ty {
        Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => {
            is_linear(pointees[p], enums, unions, pointees, functions)
        }
        Type::Enum(id) | Type::Variants(id, _) => enums[id],
        Type::Union(id) => unions[id]
            .members
            .iter()
            .any(|member| is_linear(*member, enums, unions, pointees, functions)),
        Type::Once(id) => functions[id].linear,
        _ => false,
    }
}
/// Provenance of a checked `Slice.split_at_mut` pair. A group id is created
/// only by that builtin, and a side is inherited by every descendant view.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct SplitLabels(BTreeMap<usize, bool>);
impl SplitLabels {
    fn with(&self, group: usize, left: bool) -> Self {
        let mut labels = self.clone();
        labels.0.insert(group, left);
        labels
    }
    /// Two views are provably disjoint only when they descend from opposite
    /// sides of the same checked split. No other sibling relationship is
    /// exempted.
    fn disjoint(&self, other: &Self) -> bool {
        self.0.iter().any(|(group, left)| {
            other
                .0
                .get(group)
                .is_some_and(|other_left| other_left != left)
        })
    }
}
/// One borrowed view retained by the current full expression.
#[derive(Clone)]
struct RetainedView {
    origins: BTreeSet<usize>,
    roots: BTreeSet<usize>,
    mutable: bool,
    splits: SplitLabels,
    field: Option<FieldBorrow>,
}
struct LoopState {
    pending_linear_start: usize,
    /// Availability at the loop head; the body must restore it.
    entry: Vec<bool>,
    /// Obligations at the head, including intrinsic type linearity.
    entry_linear: Vec<bool>,
    /// Availability joined over every `break`.
    breaks: Option<Vec<bool>>,
    /// First expression resource id allocated inside the loop.
    resource_start: usize,
    /// Locals bound inside the loop.
    bound: Vec<usize>,
}
/// Loan set carried by a closure that captures borrowed slice views. The
/// closure is a single aggregate capability over these origins: every captured
/// ancestor, root, and split side is reserved for as long as the closure can be
/// called. The origins are never copied into the environment as ownership.
#[derive(Clone, Default)]
struct BorrowedCapture {
    origins: BTreeSet<usize>,
    mutable: bool,
    splits: SplitLabels,
    /// A slice result borrowed from one capture, resolved to the capture's
    /// outer provenance when the closure value is constructed.
    result_slice: Option<Loan>,
    /// A record result whose borrowed leaves come from captured records.
    result_record: Option<RecordProvenance>,
}
struct Checker<'a> {
    enums: &'a [crate::runtime_types::Enum],
    owned: &'a [bool],
    linear: &'a [bool],
    unions: &'a [crate::runtime_types::UnionType],
    pointees: &'a [Type],
    reference_labels: &'a [String],
    functions: &'a [crate::runtime_types::FunctionType],
    /// Static result contract of each checked function, by instance index:
    /// `(grade, owning)`. `owning` distinguishes an owning `@[1]` transfer
    /// (which is a move) from a copyable must-use `@[1]` contract (which the
    /// grade pass enforces). Metadata only; runtime payloads and the ABI are
    /// unchanged.
    result_grades: &'a [Option<(Grade, bool)>],
    calls: &'a [CallLifetime],
    result_lifetime: Option<String>,
    result_type: Type,
    parameter_lifetimes: Vec<Option<String>>,
    /// Reflexive-transitive outlives bounds declared by this function.
    lifetime_bounds: BTreeSet<(String, String)>,
    parameter_count: usize,
    locals: Vec<crate::executable::Local>,
    available: Vec<bool>,
    moved_at: Vec<Option<Span>>,
    /// Temporary borrows that last only for the current full expression.
    loans: BTreeSet<usize>,
    /// Exclusive call-scoped record loans. Unlike the temporary sets, these
    /// survive every nested expression until the enclosing full expression
    /// completes, so a later argument cannot read or alias the owner.
    exclusive_loans: BTreeSet<usize>,
    /// Shared call-scoped record loans. They alias each other but still block
    /// moves, drops, replacement, and any exclusive alias.
    shared_record_loans: BTreeSet<usize>,
    /// Slice values already evaluated but retained by an enclosing expression.
    temporary_shared: BTreeSet<usize>,
    temporary_exclusive: BTreeSet<usize>,
    /// Builtin receivers reserved while their remaining arguments evaluate.
    reborrowed_views: BTreeSet<usize>,
    /// View metadata may be read while its own subview bounds are evaluated.
    bound_receivers: BTreeSet<usize>,
    /// Retained temporary views with checked split provenance.
    temporary_regions: Vec<RetainedView>,
    /// Views captured by spawned child tasks. A child may run at any later
    /// suspension point until the scope's final join, so these loans hold for
    /// the rest of the scope body and survive every temporary restore.
    task_regions: Vec<RetainedView>,
    /// Per-field provenance of a borrowed-record result produced by a child
    /// task, keyed by the TaskSpawn expression. It moves with the handle and
    /// then with the TaskExit value that Task.join produces.
    task_results: BTreeMap<usize, RecordProvenance>,
    /// Result provenance of each local Task<T> handle, keyed by binding slot.
    task_sources: Vec<Option<RecordProvenance>>,
    /// Borrowed-record provenance carried by a TaskExit<T> value, keyed by the
    /// producing expression. Only Task.join creates one.
    wrapped_results: BTreeMap<usize, RecordProvenance>,
    /// Provenance of a local TaskExit<T> binding that wraps a borrowed record.
    wrapped_locals: Vec<Option<RecordProvenance>>,
    /// For each slice view local, its flattened capability ancestry: every
    /// immediate source view and every owned storage root the view derives
    /// from. A parameter view has an empty ancestry and is itself a root.
    view_sources: Vec<Option<BTreeSet<usize>>>,
    /// For each slice view local, the owned/parameter storage roots behind its
    /// ancestry. Two views conflict exactly when these root sets intersect,
    /// unless one is an ancestor of the other.
    view_roots: Vec<Option<BTreeSet<usize>>>,
    /// Whether each local slice view is an exclusive `&mut [T]` capability.
    view_mut: Vec<bool>,
    /// Erased static lifetime label of each local slice view.
    view_lifetimes: Vec<Option<String>>,
    /// Erased static lifetime label of each reference parameter. Reference
    /// locals are not storable, so only parameters carry this label.
    reference_lifetimes: Vec<Option<String>>,
    /// Checked split-side assumptions for each local slice view.
    view_splits: Vec<SplitLabels>,
    /// For a view derived directly from a record field, the field place that
    /// identifies it. Disjoint field places of one record may be loaned at the
    /// same time; the whole record still cannot be moved or accessed.
    view_fields: Vec<Option<FieldBorrow>>,
    /// The projection currently being used as a subview base. It is a place,
    /// not a copied ready-made view, and does not add a second retained loan.
    in_field_subview: bool,
    /// The record field currently being projected. Reading the record to
    /// reach this place is allowed while every live child view of that record
    /// is a structurally disjoint field.
    field_target: Option<FieldBorrow>,
    /// Per-field provenance of each local borrowed-record value. Ordinary
    /// records have no entry.
    record_sources: Vec<Option<RecordProvenance>>,
    /// Provenance of checked borrowed call results, keyed by expression.
    call_views: BTreeMap<usize, Loan>,
    call_records: BTreeMap<usize, RecordProvenance>,
    /// Provenance of checked record literals, keyed by expression.
    construct_records: BTreeMap<usize, RecordProvenance>,
    /// Fresh compiler-internal lifetime identities for call-site unification.
    call_lifetime_counter: usize,
    /// Origins of a checked borrowed return, keyed by call expression.
    call_origins: BTreeMap<usize, BTreeSet<usize>>,
    /// Checked split assumptions of a borrowed call result, keyed by call
    /// expression. Derived from the arguments that contribute the result
    /// lifetime, not from an arbitrary alias.
    call_splits: BTreeMap<usize, SplitLabels>,
    /// Backward liveness of slice-view locals before each expression node.
    live: &'a BTreeMap<usize, BTreeSet<usize>>,
    /// The one `FnValue` expression allowed to capture borrowed slice views in
    /// its enclosing statement/callee position. Borrowed captures are a scoped,
    /// lexical feature: they cannot be constructed in a value-storing or
    /// escaping position.
    capture_site: Option<usize>,
    /// The one `Local` expression allowed to consume a borrowed-capture closure
    /// as the callee of an indirect call.
    callee_site: Option<usize>,
    /// Borrowed capture provenance keyed by `FnValue` expression.
    borrowed_values: BTreeMap<usize, BorrowedCapture>,
    /// Locals holding a closure with borrowed captures, keyed by local slot.
    borrowed_closures: BTreeMap<usize, BorrowedCapture>,
    guard: bool,
    /// Builtin slice reads/writes reborrow an exclusive view for the call.
    reborrow: bool,
    /// Linear results evaluated but not yet consumed by an enclosing operation.
    pending_linear: Vec<Span>,
    resources: Vec<Type>,
    local_resources: Vec<Option<usize>>,
    loops: Vec<LoopState>,
}
impl Checker<'_> {
    /// Values that move instead of being copied.
    fn moves(&self, ty: Type) -> bool {
        ty.is_mut_slice()
            || matches!(ty, Type::RefMut(_))
            || owns(ty, self.owned, self.unions, self.pointees)
            || is_linear(ty, self.linear, self.unions, self.pointees, self.functions)
            || ty.layout().is_some_and(|id| self.enums[id].mutable_borrow)
    }
    fn slot_linear(&self, slot: usize) -> bool {
        self.locals[slot].linear
            || is_linear(
                self.locals[slot].ty,
                self.linear,
                self.unions,
                self.pointees,
                self.functions,
            )
    }
    fn live_views_at(&self, ptr: usize) -> &BTreeSet<usize> {
        static EMPTY: std::sync::LazyLock<BTreeSet<usize>> =
            std::sync::LazyLock::new(BTreeSet::new);
        self.live.get(&ptr).unwrap_or(&EMPTY)
    }
    /// Whether `slot` is a view binding rather than owned storage. Parameters
    /// are external roots even though their type is a slice view. A closure
    /// local carrying borrowed slice captures is treated as the aggregate view
    /// capability it holds.
    fn is_local_view(&self, slot: usize) -> bool {
        slot >= self.parameter_count
            && (self.locals[slot].ty.is_view()
                || self.locals[slot].ty.is_ref()
                || self.borrowed_closures.contains_key(&slot)
                || self.is_carrier_type(self.locals[slot].ty))
    }
    fn is_carrier_type(&self, ty: Type) -> bool {
        ty.layout().is_some_and(|id| self.enums[id].borrowed)
            || container_carries_borrow(self.pointees, ty)
    }
    fn is_task_exit(&self, ty: Type) -> bool {
        ty.layout()
            .is_some_and(|id| self.enums[id].name == "TaskExit")
    }
    fn parameter_record_provenance(&self, slot: usize, ty: Type) -> RecordProvenance {
        let mut provenance = RecordProvenance::default();
        for leaf in leaves_of(self.enums, self.pointees, self.reference_labels, ty) {
            let field = FieldBorrow {
                root: slot,
                path: leaf.path.clone(),
            };
            provenance.leaves.insert(
                leaf.path,
                Loan {
                    origins: BTreeSet::from([slot]),
                    mutable: leaf.mutable,
                    splits: SplitLabels::default(),
                    lifetime: leaf.lifetime,
                    field: Some(field),
                },
            );
        }
        provenance
    }
    /// The record field index at a word offset (word 0 is the tag).
    fn field_index(&self, ty: Type, offset: usize) -> Option<usize> {
        let id = ty.layout().filter(|id| self.enums[*id].record)?;
        let mut at = 1;
        for (index, field) in self.enums[id].variants[0].fields.iter().enumerate() {
            if at == offset {
                return Some(index);
            }
            at += crate::runtime_types::width(self.enums, self.unions, self.functions, *field);
        }
        None
    }
    /// The checked record-field place of a projection rooted at a direct local
    /// record. Nested projections extend the path; coercion wrappers are
    /// transparent. Anything rooted at a temporary, view, or call has no
    /// stable field identity.
    fn projection_field(&self, expr: &Expr) -> Option<FieldBorrow> {
        let mut path = Vec::new();
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::Project(base, offset) => {
                    path.push(self.field_index(base.ty, *offset)?);
                    current = base;
                }
                ExprKind::Coerce { value, .. } => current = value,
                ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                    if current.ty.layout().is_some_and(|id| self.enums[id].record) =>
                {
                    path.reverse();
                    return Some(FieldBorrow { root: *slot, path });
                }
                _ => return None,
            }
        }
    }
    /// Static lifetime label and capability provenance of a checked slice
    /// expression, including fields projected from borrowed records.
    fn view_loan(&self, expr: &Expr) -> Loan {
        let ptr = expr as *const Expr as usize;
        if let Some(loan) = self.call_views.get(&ptr) {
            return loan.clone();
        }
        match &expr.kind {
            ExprKind::Borrow(slot) if expr.ty.is_ref() => Loan {
                origins: BTreeSet::from([*slot]),
                mutable: matches!(expr.ty, Type::RefMut(_)),
                splits: SplitLabels::default(),
                lifetime: None,
                field: self.projection_field(expr),
            },
            ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot)
                if expr.ty.is_ref() =>
            {
                if self.is_local_view(*slot) {
                    // A stored reference is a lexical capability over the
                    // same storage as the reference it was created from. Its
                    // derived origins and lifetime drive every later use, so a
                    // local reborrow cannot silently re-anchor to the reference
                    // descriptor itself.
                    Loan {
                        origins: self.view_origins(expr),
                        mutable: self.view_mut[*slot],
                        splits: self.view_splits[*slot].clone(),
                        lifetime: self.view_lifetimes[*slot]
                            .clone()
                            .or_else(|| self.reference_lifetimes[*slot].clone()),
                        field: None,
                    }
                } else {
                    Loan {
                        origins: BTreeSet::from([*slot]),
                        mutable: matches!(expr.ty, Type::RefMut(_)),
                        splits: SplitLabels::default(),
                        lifetime: self.reference_lifetimes[*slot].clone(),
                        field: None,
                    }
                }
            }
            ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot) => {
                if self.locals[*slot].ty.is_view() {
                    Loan {
                        origins: self.view_origins(expr),
                        mutable: self.view_mut[*slot],
                        splits: self.view_splits[*slot].clone(),
                        lifetime: self.view_lifetimes[*slot].clone(),
                        field: self.view_fields[*slot].clone(),
                    }
                } else {
                    Loan::default()
                }
            }
            ExprKind::Slice { base, .. } => Loan {
                origins: self.view_origins(base),
                mutable: expr.ty.is_mut_slice(),
                splits: self.split_labels(expr),
                lifetime: if base.ty.is_view() {
                    self.view_loan(base).lifetime
                } else {
                    None
                },
                field: match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                        if base.ty.is_view() =>
                    {
                        self.view_fields[*slot].clone()
                    }
                    _ => self.projection_field(base),
                },
            },
            ExprKind::Project(base, offset) => {
                let Some(index) = self.field_index(base.ty, *offset) else {
                    return Loan::default();
                };
                let mut loan = self
                    .record_provenance(base)
                    .leaves
                    .get(&vec![index])
                    .cloned()
                    .unwrap_or_default();
                loan.field = self.projection_field(expr);
                if let Some(field) = &loan.field {
                    // The record binding is an ancestor capability: a field
                    // subview suspends it for moves and whole-value access,
                    // while structurally disjoint field subviews coexist.
                    loan.origins.insert(field.root);
                }
                loan
            }
            ExprKind::Coerce { value, .. } => self.view_loan(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .map(|tail| self.view_loan(tail))
                .unwrap_or_default(),
            ExprKind::If(_, yes, no) => self.merge_loans(
                [&yes.tail, &no.tail]
                    .into_iter()
                    .filter(|tail| tail.as_ref().is_some_and(|tail| tail.ty != Type::Never))
                    .filter_map(|tail| tail.as_deref())
                    .map(|tail| self.view_loan(tail)),
            ),
            ExprKind::Match(_, arms) => self.merge_loans(
                arms.iter()
                    .filter(|arm| arm.body.ty != Type::Never)
                    .map(|arm| self.view_loan(&arm.body)),
            ),
            _ => Loan::default(),
        }
    }
    fn merge_loans(&self, loans: impl IntoIterator<Item = Loan>) -> Loan {
        let loans = loans.into_iter().collect::<Vec<_>>();
        if loans.is_empty() {
            return Loan::default();
        }
        let mut merged = Loan {
            origins: BTreeSet::new(),
            mutable: false,
            splits: loans[0].splits.clone(),
            lifetime: loans[0].lifetime.clone(),
            field: loans[0].field.clone(),
        };
        for loan in &loans {
            merged.origins.extend(loan.origins.iter().copied());
            merged.mutable |= loan.mutable;
            merged.splits = intersect_splits(&merged.splits, &loan.splits);
            if loan.lifetime != merged.lifetime {
                merged.lifetime = None;
            }
            if loan.field != merged.field {
                merged.field = None;
            }
        }
        merged
    }
    /// Verify that a checked record literal's field provenance matches the
    /// declared field lifetimes of its instantiated type. Explicit lifetimes
    /// must agree exactly; compiler-inferred local/argument identities keep the
    /// actual field labels so an escape cannot relabel them.
    fn construct_record_provenance(
        &self,
        enum_id: usize,
        fields: &[Expr],
    ) -> Result<RecordProvenance> {
        let layout = &self.enums[enum_id];
        let variant = &layout.variants[0];
        let mut provenance = RecordProvenance::default();
        for (index, expr) in fields.iter().enumerate() {
            let field_ty = variant.fields[index];
            if field_ty.is_slice() {
                let declared = layout.field_lifetimes[index].clone();
                let loan = self.view_loan(expr);
                if loan.mutable != field_ty.is_mut_slice() {
                    return Err(Diagnostic::new(
                        expr.span,
                        if field_ty.is_mut_slice() {
                            format!(
                                "field '{}' is an exclusive '&mut [T]' field, but its source is a shared view; shared storage cannot be upgraded",
                                variant.names[index]
                            )
                        } else {
                            format!(
                                "field '{}' is a shared '&[T]' field, but its source is an exclusive '&mut [T]' view",
                                variant.names[index]
                            )
                        },
                    ));
                }
                match &declared {
                    Some(lifetime) if !is_internal_lifetime(lifetime) => {
                        let carried = loan
                            .lifetime
                            .as_deref()
                            .is_some_and(|source| self.actual_outlives(source, lifetime));
                        if !carried {
                            return Err(Diagnostic::new(
                                expr.span,
                                format!(
                                    "field '{}' must be borrowed for lifetime '{lifetime}' or a lifetime that outlives it, but its source has lifetime {}",
                                    variant.names[index],
                                    loan.lifetime
                                        .as_deref()
                                        .unwrap_or("a temporary or local owner")
                                ),
                            ));
                        }
                    }
                    Some(_) => {}
                    None => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: borrowed record field has no declared lifetime",
                        ));
                    }
                }
                provenance.leaves.insert(vec![index], loan);
            } else if field_ty.is_ref() {
                let declared = layout.field_lifetimes[index].clone();
                let loan = self.view_loan(expr);
                let mutable_field = matches!(field_ty, Type::RefMut(_));
                if loan.mutable != mutable_field {
                    return Err(Diagnostic::new(
                        expr.span,
                        if mutable_field {
                            format!(
                                "field '{}' is an exclusive '&mut T' field, but its source is a shared reference; shared storage cannot be upgraded",
                                variant.names[index]
                            )
                        } else {
                            format!(
                                "field '{}' is a shared '&T' field, but its source is an exclusive reference",
                                variant.names[index]
                            )
                        },
                    ));
                }
                match &declared {
                    Some(lifetime) if !is_internal_lifetime(lifetime) => {
                        let carried = loan
                            .lifetime
                            .as_deref()
                            .is_some_and(|source| self.actual_outlives(source, lifetime));
                        if !carried {
                            return Err(Diagnostic::new(
                                expr.span,
                                format!(
                                    "field '{}' must be borrowed for lifetime '{lifetime}' or a lifetime that outlives it, but its source has lifetime {}",
                                    variant.names[index],
                                    loan.lifetime
                                        .as_deref()
                                        .unwrap_or("a temporary or local owner")
                                ),
                            ));
                        }
                    }
                    Some(_) => {}
                    None => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: borrowed reference field has no declared lifetime",
                        ));
                    }
                }
                provenance.leaves.insert(vec![index], loan);
            } else if self.is_carrier_type(field_ty) {
                let nested = self.record_provenance(expr);
                let expected =
                    leaves_of(self.enums, self.pointees, self.reference_labels, field_ty);
                for leaf in expected {
                    let Some(loan) = nested.leaves.get(&leaf.path) else {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "nested borrowed record field '{}' is missing its borrowed provenance",
                                variant.names[index]
                            ),
                        ));
                    };
                    if loan.mutable != leaf.mutable {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "nested field '{}' has different borrow mutability than its declared field type",
                                variant.names[index]
                            ),
                        ));
                    }
                    if let Some(lifetime) = &leaf.lifetime
                        && !is_internal_lifetime(lifetime)
                        && !loan
                            .lifetime
                            .as_deref()
                            .is_some_and(|source| self.actual_outlives(source, lifetime))
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "nested field '{}' must be borrowed for lifetime '{lifetime}' or a lifetime that outlives it, but its source has lifetime {}",
                                variant.names[index],
                                loan.lifetime
                                    .as_deref()
                                    .unwrap_or("a temporary or local owner")
                            ),
                        ));
                    }
                    let mut path = vec![index];
                    path.extend(leaf.path.iter().copied());
                    provenance.leaves.insert(path, loan.clone());
                }
                if nested.leaves.len()
                    != provenance
                        .leaves
                        .keys()
                        .filter(|path| path.first() == Some(&index))
                        .count()
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "nested borrowed record provenance does not match its declared fields",
                    ));
                }
            }
        }
        Ok(provenance)
    }
    /// Provenance of a container value reached through a place or borrow. A
    /// `&Box<&T>`/`&Vec<&T>` receiver names the container binding, whose
    /// element loans were recorded when it was constructed or bound.
    fn container_provenance(&self, expr: &Expr) -> RecordProvenance {
        let base = through_coerce(expr);
        match &base.kind {
            ExprKind::Borrow(slot)
            | ExprKind::Local(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Move(slot)
                if self.is_carrier_type(self.locals[*slot].ty) =>
            {
                self.record_sources[*slot].clone().unwrap_or_default()
            }
            _ => self.record_provenance(expr),
        }
    }
    /// The borrow leaf of one reference value stored in a container. A direct
    /// reference expression carries its own loan; a nested borrowed record is
    /// not admitted as a container element.
    fn reference_element_loan(&self, expr: &Expr) -> Option<Loan> {
        expr.ty.is_ref().then(|| self.view_loan(expr))
    }
    /// Per-field provenance of any checked record expression.
    fn record_provenance(&self, expr: &Expr) -> RecordProvenance {
        let ptr = expr as *const Expr as usize;
        if let Some(provenance) = self.wrapped_results.get(&ptr) {
            return provenance.clone();
        }
        if let Some(provenance) = self.call_records.get(&ptr) {
            return provenance.clone();
        }
        if let Some(provenance) = self.construct_records.get(&ptr) {
            return provenance.clone();
        }
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot) => {
                if let Some(provenance) = &self.wrapped_locals[*slot] {
                    return provenance.clone();
                }
                self.record_sources[*slot].clone().unwrap_or_default()
            }
            ExprKind::Project(base, offset) => {
                let Some(index) = self.field_index(base.ty, *offset) else {
                    return RecordProvenance::default();
                };
                let base_provenance = self.record_provenance(base);
                let mut provenance = RecordProvenance::default();
                for (path, loan) in base_provenance.leaves {
                    if path.first() != Some(&index) {
                        continue;
                    }
                    provenance.leaves.insert(path[1..].to_vec(), loan);
                }
                provenance
            }
            ExprKind::Coerce { value, .. } => self.record_provenance(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .map(|tail| self.record_provenance(tail))
                .unwrap_or_default(),
            ExprKind::If(_, yes, no) => RecordProvenance::merge(
                [&yes.tail, &no.tail]
                    .into_iter()
                    .filter(|tail| tail.as_ref().is_some_and(|tail| tail.ty != Type::Never))
                    .filter_map(|tail| tail.as_deref())
                    .map(|tail| self.record_provenance(tail)),
            ),
            ExprKind::Match(_, arms) => RecordProvenance::merge(
                arms.iter()
                    .filter(|arm| arm.body.ty != Type::Never)
                    .map(|arm| self.record_provenance(&arm.body)),
            ),
            _ => RecordProvenance::default(),
        }
    }
    /// Retain every borrowed field of an evaluated record through the rest of
    /// the enclosing expression, including later call arguments/fields.
    fn hold_record(&mut self, expr: &Expr) -> Result<()> {
        if !self.is_carrier_type(expr.ty) {
            return Ok(());
        }
        // A record place being projected into a field subview is an ancestor,
        // not a second retained aggregate capability; the Slice expression
        // retains exactly the selected field.
        if self.in_field_subview {
            return Ok(());
        }
        let provenance = self.record_provenance(expr);
        for loan in provenance.leaves.values() {
            if loan.origins.is_empty() {
                continue;
            }
            let roots = self.origins_roots(&loan.origins);
            for retained in &self.temporary_regions {
                let overlaps = loan
                    .origins
                    .iter()
                    .any(|slot| retained.origins.contains(slot))
                    || roots.iter().any(|root| retained.roots.contains(root));
                if !overlaps || loan.splits.disjoint(&retained.splits) {
                    continue;
                }
                if retained.mutable || loan.mutable {
                    return Err(Diagnostic::new(
                        expr.span,
                        "conflicting slice arguments: a borrowed record field overlaps another view retained by this expression",
                    ));
                }
            }
            self.temporary_regions.push(RetainedView {
                origins: loan.origins.clone(),
                roots,
                mutable: loan.mutable,
                splits: loan.splits.clone(),
                field: loan.field.clone(),
            });
            self.loans.extend(loan.origins.iter().copied());
            if loan.mutable {
                self.temporary_exclusive
                    .extend(loan.origins.iter().copied());
            } else {
                self.temporary_shared.extend(loan.origins.iter().copied());
            }
        }
        Ok(())
    }
    /// Retain a checked temporary's loans through the rest of the enclosing
    /// record literal. Used only for source-order record temporaries.
    fn retain_local(&mut self, slot: usize) {
        if self.locals[slot].ty.is_slice() {
            // The temporary field local itself is about to be moved into the
            // record. Reserve the owners and parents it borrows through the
            // rest of the literal without adding a second retained view for
            // the same capability. The live temporary view already prevents a
            // rival view, while this loan set prevents moving or dropping the
            // owner from a later field.
            let origins = self.view_sources[slot].clone().unwrap_or_default();
            self.loans.extend(origins);
        } else if let Some(provenance) = self.record_sources[slot].clone() {
            for loan in provenance.leaves.values() {
                self.retain_loan(loan.clone());
            }
        }
    }
    fn retain_loan(&mut self, loan: Loan) {
        if loan.origins.is_empty() {
            return;
        }
        let roots = self.origins_roots(&loan.origins);
        self.temporary_regions.push(RetainedView {
            origins: loan.origins.clone(),
            roots,
            mutable: loan.mutable,
            splits: loan.splits,
            field: loan.field,
        });
        self.loans.extend(loan.origins.iter().copied());
        if loan.mutable {
            self.temporary_exclusive.extend(loan.origins);
        } else {
            self.temporary_shared.extend(loan.origins);
        }
    }
    /// Acquire the aggregate loan and per-field provenance of a local borrowed
    /// record binding.
    fn fresh_call_lifetime(&mut self) -> String {
        let index = self.call_lifetime_counter;
        self.call_lifetime_counter += 1;
        format!("<call lifetime {index}>")
    }
    /// A stable anonymous identity for a borrow whose static lifetime is not a
    /// declared caller lifetime. Two borrows of the same storage set share it,
    /// so reflexivity holds; unrelated local owners stay distinct. This keeps
    /// call-site outlives constraints honest without inventing a caller label.
    ///
    /// When every storage root is owned by this function's frame (a
    /// non-parameter local holding no borrow), the identity is marked `local`:
    /// such storage dies before the call returns, so any caller lifetime
    /// outlives it. The mark is part of the label, so it cannot go stale.
    fn anonymous_lifetime(&self, origins: &BTreeSet<usize>) -> String {
        let owners = origins
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(",");
        if self.frame_owned(origins) {
            format!("<local [{owners}]>")
        } else {
            format!("<anonymous [{owners}]>")
        }
    }
    fn frame_owned(&self, origins: &BTreeSet<usize>) -> bool {
        let roots = self.origins_roots(origins);
        !roots.is_empty()
            && roots.iter().all(|root| {
                *root >= self.parameter_count
                    && !self.is_local_view(*root)
                    && !self.may_hold_borrow(self.locals[*root].ty)
            })
    }
    /// Conservative: true for any type that could carry borrowed storage,
    /// including callables and tasks whose captures are not visible here.
    fn may_hold_borrow(&self, ty: Type) -> bool {
        fn go(c: &Checker<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
            if !seen.insert(ty) {
                return false;
            }
            match ty {
                Type::Ref(_)
                | Type::RefMut(_)
                | Type::Slice(_)
                | Type::SliceMut(_)
                | Type::Fn(_)
                | Type::Once(_)
                | Type::Task(_) => true,
                Type::Box(p) | Type::Vec(p) => go(c, c.pointees[p], seen),
                Type::Enum(id) | Type::Variants(id, _) => {
                    c.enums[id].borrowed
                        || c.enums[id]
                            .variants
                            .iter()
                            .flat_map(|variant| variant.fields.iter())
                            .any(|field| go(c, *field, seen))
                }
                Type::Union(id) => c.unions[id].members.iter().any(|m| go(c, *m, seen)),
                _ => false,
            }
        }
        go(self, ty, &mut BTreeSet::new())
    }
    /// Record one actual caller lifetime for a callee lifetime declaration. A
    /// declaration may be instantiated by several caller views; every actual is
    /// kept so a result cannot claim the first one when another is shorter.
    fn unify_call_lifetime(
        &mut self,
        map: &mut BTreeMap<String, BTreeSet<String>>,
        declared: &str,
        actual: Option<&str>,
    ) {
        let actual = match actual {
            Some(actual) => actual.to_owned(),
            None => self.fresh_call_lifetime(),
        };
        map.entry(declared.to_owned()).or_default().insert(actual);
    }
    /// Whether the caller can prove `long` outlives `short` for the current
    /// function's declared bounds. Anonymous and internal identities only prove
    /// reflexivity.
    fn actual_outlives(&self, long: &str, short: &str) -> bool {
        crate::executable::outlives(&self.lifetime_bounds, long, short)
            // A declared lifetime of this function names caller storage that
            // outlives the whole call, hence every frame-owned local.
            || (!is_internal_lifetime(long) && short.starts_with("<local "))
    }
    /// Validate the callee's declared outlives relation at this call site: for
    /// every pair of callee lifetimes where the longer outlives the shorter, the
    /// caller must prove that every actual lifetime supplied for the longer also
    /// outlives every actual supplied for the shorter. Bounds with an
    /// unconstrained side are instantiated reflexively by the callee and need no
    /// caller proof.
    fn validate_call_bounds(
        &self,
        map: &BTreeMap<String, BTreeSet<String>>,
        bounds: &BTreeSet<(String, String)>,
        span: Span,
    ) -> Result<()> {
        for (long, short) in bounds {
            let (Some(long_actuals), Some(short_actuals)) = (map.get(long), map.get(short)) else {
                continue;
            };
            for long_actual in long_actuals {
                for short_actual in short_actuals {
                    if !self.actual_outlives(long_actual, short_actual) {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "this call cannot establish the callee's outlives constraint {}: {}: the argument for {} has {}, which does not outlive {} from the argument for {}. Bind both borrows to parameters with matching declared outlives bounds",
                                describe_lifetime(long),
                                describe_lifetime(short),
                                describe_lifetime(long),
                                describe_actual(long_actual),
                                describe_actual(short_actual),
                                describe_lifetime(short)
                            ),
                        ));
                    }
                }
            }
        }
        Ok(())
    }
    /// Instantiate every callee parameter lifetime from the actual argument
    /// leaves. The mapping keeps all actual labels per declaration so a result
    /// never silently claims the first one.
    fn call_mapping(
        &mut self,
        parameters: &[Vec<crate::runtime_types::BorrowLeaf>],
        args: &[Expr],
    ) -> Result<BTreeMap<String, BTreeSet<String>>> {
        let mut mapping = BTreeMap::new();
        for (leaves, argument) in parameters.iter().zip(args.iter()) {
            for leaf in leaves {
                let Some(declared) = &leaf.lifetime else {
                    continue;
                };
                let loan = self
                    .argument_leaf_loan(argument, &leaf.path)
                    .ok_or_else(|| {
                        Diagnostic::new(
                            argument.span,
                            "internal error: borrowed call argument has no field provenance",
                        )
                    })?;
                if leaf.mutable && !loan.mutable {
                    return Err(Diagnostic::new(
                        argument.span,
                        "a shared record field cannot be passed where an exclusive '&mut [T]' field is expected; shared storage cannot be upgraded",
                    ));
                }
                let actual = loan.lifetime.clone().or_else(|| {
                    (!loan.origins.is_empty()).then(|| self.anonymous_lifetime(&loan.origins))
                });
                self.unify_call_lifetime(&mut mapping, declared, actual.as_deref());
            }
        }
        Ok(mapping)
    }
    /// Apply a callee's borrow contract at a call site: validate its outlives
    /// bounds against the caller's, and record the provenance and instantiated
    /// lifetime of a borrowed result. Shared by direct and indirect calls.
    #[allow(clippy::too_many_arguments)]
    fn apply_call_lifetime(
        &mut self,
        parameters: Vec<Vec<crate::runtime_types::BorrowLeaf>>,
        result: CallResult,
        bounds: BTreeSet<(String, String)>,
        args: &[Expr],
        expr_ptr: usize,
        ty: Type,
        span: Span,
    ) -> Result<()> {
        let mut mapping = BTreeMap::new();
        if !bounds.is_empty() || !matches!(result, CallResult::None) {
            mapping = self.call_mapping(&parameters, args)?;
            self.validate_call_bounds(&mapping, &bounds, span)?;
        }
        match result {
            CallResult::None => {}
            CallResult::Slice { lifetime, mutable } => {
                let Some(lifetime) = lifetime else {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: borrowed return without a declared lifetime",
                    ));
                };
                if ty.is_mut_slice() != mutable {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: borrowed call result mutability disagrees with its signature",
                    ));
                }
                let mut origins = BTreeSet::new();
                let mut mutable_parameters = 0;
                let mut splits: Option<SplitLabels> = None;
                let mut field_candidates = Vec::new();
                for (leaves, argument) in parameters.iter().zip(args.iter()) {
                    for leaf in leaves {
                        let Some(parameter_lifetime) = &leaf.lifetime else {
                            continue;
                        };
                        if !Self::callee_flows(&bounds, parameter_lifetime, &lifetime) {
                            continue;
                        }
                        if ty.is_mut_slice() && !leaf.mutable {
                            return Err(Diagnostic::new(
                                span,
                                "an exclusive borrowed call result must derive only from exclusive '&mut [T]' parameters whose lifetime outlives the declared result lifetime",
                            )
                            .with_note(
                                argument.span,
                                "shared argument that can flow into the mutable result",
                            ));
                        }
                        if leaf.mutable {
                            mutable_parameters += 1;
                        }
                        let loan = self
                            .argument_leaf_loan(argument, &leaf.path)
                            .ok_or_else(|| {
                                Diagnostic::new(
                                    argument.span,
                                    "internal error: borrowed call argument has no field provenance",
                                )
                            })?;
                        origins.extend(loan.origins.iter().copied());
                        splits = Some(match splits {
                            Some(current) => intersect_splits(&current, &loan.splits),
                            None => loan.splits,
                        });
                        field_candidates.push(self.argument_leaf_field(argument, &leaf.path));
                    }
                }
                if origins.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: borrowed call result has no loan provenance",
                    ));
                }
                if ty.is_mut_slice() && mutable_parameters == 0 {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: exclusive borrowed call result has no exclusive parameter",
                    ));
                }
                let lifetime = self.instantiate_result_lifetime(&mapping, &bounds, &lifetime);
                let field = match field_candidates.first() {
                    Some(Some(first))
                        if field_candidates
                            .iter()
                            .all(|candidate| candidate.as_ref() == Some(first)) =>
                    {
                        Some(first.clone())
                    }
                    _ => None,
                };
                self.call_views.insert(
                    expr_ptr,
                    Loan {
                        origins: origins.clone(),
                        mutable,
                        splits: splits.clone().unwrap_or_default(),
                        lifetime,
                        field,
                    },
                );
                self.call_origins.insert(expr_ptr, origins);
                self.call_splits
                    .insert(expr_ptr, splits.unwrap_or_default());
            }
            CallResult::Reference { lifetime, mutable } => {
                let Some(lifetime) = lifetime else {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: borrowed reference return without a declared lifetime",
                    ));
                };
                let mut origins = BTreeSet::new();
                let mut mutable_parameters = 0;
                for (leaves, argument) in parameters.iter().zip(args.iter()) {
                    for leaf in leaves {
                        let Some(parameter_lifetime) = &leaf.lifetime else {
                            continue;
                        };
                        if !Self::callee_flows(&bounds, parameter_lifetime, &lifetime) {
                            continue;
                        }
                        if mutable && !leaf.mutable {
                            return Err(Diagnostic::new(
                                span,
                                "an exclusive '&mut Record' call result must derive only from exclusive '&mut Record' parameters whose lifetime outlives the declared result lifetime",
                            )
                            .with_note(argument.span, "shared argument that can flow into the mutable result"));
                        }
                        if leaf.mutable {
                            mutable_parameters += 1;
                        }
                        let loan = self.argument_leaf_loan(argument, &leaf.path).ok_or_else(
                            || {
                                Diagnostic::new(
                                    argument.span,
                                    "internal error: borrowed reference argument has no provenance",
                                )
                            },
                        )?;
                        origins.extend(loan.origins.iter().copied());
                    }
                }
                if origins.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: borrowed reference call result has no loan provenance",
                    ));
                }
                if mutable && mutable_parameters == 0 {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: exclusive reference call result has no exclusive parameter",
                    ));
                }
                let lifetime = self.instantiate_result_lifetime(&mapping, &bounds, &lifetime);
                self.call_views.insert(
                    expr_ptr,
                    Loan {
                        origins: origins.clone(),
                        mutable,
                        splits: SplitLabels::default(),
                        lifetime,
                        field: None,
                    },
                );
                self.call_origins.insert(expr_ptr, origins);
            }
            CallResult::Record(leaves) => {
                let mut provenance = RecordProvenance::default();
                for leaf in leaves {
                    let Some(declared) = &leaf.lifetime else {
                        return Err(Diagnostic::new(
                            span,
                            "internal error: borrowed record result leaf has no lifetime",
                        ));
                    };
                    let mut origins = BTreeSet::new();
                    let mut splits: Option<SplitLabels> = None;
                    for (parameter_leaves, argument) in parameters.iter().zip(args.iter()) {
                        for parameter_leaf in parameter_leaves {
                            let Some(parameter_lifetime) = &parameter_leaf.lifetime else {
                                continue;
                            };
                            if !Self::callee_flows(&bounds, parameter_lifetime, declared) {
                                continue;
                            }
                            if leaf.mutable && !parameter_leaf.mutable {
                                return Err(Diagnostic::new(
                                    span,
                                    "an exclusive returned record field must derive only from exclusive '&mut [T]' fields whose lifetime outlives the declared result lifetime",
                                )
                                .with_note(
                                    argument.span,
                                    "shared parameter field that can flow into the mutable result",
                                ));
                            }
                            let loan = self
                                .argument_leaf_loan(argument, &parameter_leaf.path)
                                .ok_or_else(|| {
                                    Diagnostic::new(
                                        argument.span,
                                        "internal error: borrowed record argument has no field provenance",
                                    )
                                })?;
                            if parameter_leaf.mutable && !loan.mutable {
                                return Err(Diagnostic::new(
                                    argument.span,
                                    "a shared record field cannot be passed where an exclusive '&mut [T]' field is expected",
                                ));
                            }
                            origins.extend(loan.origins.iter().copied());
                            splits = Some(match splits {
                                Some(current) => intersect_splits(&current, &loan.splits),
                                None => loan.splits,
                            });
                        }
                    }
                    if origins.is_empty() {
                        return Err(Diagnostic::new(
                            span,
                            "internal error: borrowed record result has no loan provenance",
                        ));
                    }
                    provenance.leaves.insert(
                        leaf.path.clone(),
                        Loan {
                            origins,
                            mutable: leaf.mutable,
                            splits: splits.unwrap_or_default(),
                            lifetime: self.instantiate_result_lifetime(&mapping, &bounds, declared),
                            field: None,
                        },
                    );
                }
                self.call_records.insert(expr_ptr, provenance.clone());
                if self.is_task_exit(ty) {
                    self.wrapped_results.insert(expr_ptr, provenance);
                }
            }
        }
        Ok(())
    }
    /// Instantiate a callee result lifetime at this call site. Every caller
    /// lifetime that can flow into the result contributes a candidate; the
    /// result may claim a candidate only when the caller can prove it is the
    /// shortest (outlived by every other candidate). Otherwise the result keeps
    /// an anonymous internal identity, so it can be used locally but cannot be
    /// returned as a caller lifetime.
    fn instantiate_result_lifetime(
        &self,
        map: &BTreeMap<String, BTreeSet<String>>,
        bounds: &BTreeSet<(String, String)>,
        result: &str,
    ) -> Option<String> {
        let mut candidates = BTreeSet::new();
        if let Some(actuals) = map.get(result) {
            candidates.extend(actuals.iter().cloned());
        }
        for (declared, actuals) in map {
            if crate::executable::outlives(bounds, declared, result) {
                candidates.extend(actuals.iter().cloned());
            }
        }
        candidates
            .iter()
            .find(|candidate| {
                candidates
                    .iter()
                    .all(|other| self.actual_outlives(other, candidate))
            })
            .cloned()
    }
    /// Whether a callee parameter lifetime flows into a callee result lifetime:
    /// the parameter lifetime must outlive the result (reflexively or through
    /// declared bounds).
    fn callee_flows(bounds: &BTreeSet<(String, String)>, parameter: &str, result: &str) -> bool {
        crate::executable::outlives(bounds, parameter, result)
    }
    fn argument_leaf_loan(&self, argument: &Expr, path: &[usize]) -> Option<Loan> {
        if path.is_empty() && (argument.ty.is_view() || argument.ty.is_ref()) {
            return Some(self.view_loan(argument));
        }
        if self.is_carrier_type(argument.ty) {
            return self.record_provenance(argument).leaves.get(path).cloned();
        }
        None
    }
    /// Stable record-field identity of a borrowed call argument leaf. A slice
    /// leaf is either a view with its own identity or a direct field
    /// projection; a record leaf is read from a direct local record argument.
    fn argument_leaf_field(&self, argument: &Expr, path: &[usize]) -> Option<FieldBorrow> {
        if path.is_empty() {
            if argument.ty.is_view() {
                return match &argument.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                        self.view_fields[*slot].clone()
                    }
                    _ => None,
                };
            }
            return self.projection_field(argument);
        }
        if !self.is_carrier_type(argument.ty) {
            return None;
        }
        match &argument.kind {
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                Some(FieldBorrow {
                    root: *slot,
                    path: path.to_vec(),
                })
            }
            _ => None,
        }
    }
    fn acquire_record(
        &mut self,
        slot: usize,
        mut provenance: RecordProvenance,
        splits: SplitLabels,
    ) {
        let mut origins = BTreeSet::new();
        let mut mutable = false;
        for (path, loan) in &mut provenance.leaves {
            origins.extend(loan.origins.iter().copied());
            mutable |= loan.mutable;
            // Re-anchor each leaf's field identity to the binding that now
            // holds the record. Two views of disjoint fields of this binding
            // stay distinct even after a helper returned the record.
            loan.field = Some(FieldBorrow {
                root: slot,
                path: path.clone(),
            });
        }
        self.record_sources[slot] = Some(provenance);
        // The aggregate record is a capability holder. Treat it as exclusive
        // when any leaf is exclusive so every owner behind a live mutable-field
        // record stays suspended until the record and its aliases are dead.
        self.acquire_view(slot, mutable, origins, splits, None, None);
    }
    /// Propagate checked record-field provenance into destructuring bindings.
    fn bind_pattern_provenance(
        &mut self,
        pattern: &Pattern,
        ty: Type,
        provenance: &RecordProvenance,
    ) -> Result<()> {
        match pattern {
            Pattern::Bind(slot) => {
                if ty.is_slice() {
                    let loan = provenance
                        .leaves
                        .get(&Vec::new())
                        .cloned()
                        .unwrap_or_default();
                    let field = loan.field.clone();
                    self.acquire_view(
                        *slot,
                        ty.is_mut_slice(),
                        loan.origins,
                        loan.splits,
                        loan.lifetime,
                        field,
                    );
                } else if ty.is_ref() {
                    let loan = provenance
                        .leaves
                        .get(&Vec::new())
                        .cloned()
                        .unwrap_or_default();
                    let lifetime = loan.lifetime.clone();
                    self.acquire_view(
                        *slot,
                        matches!(ty, Type::RefMut(_)),
                        loan.origins,
                        loan.splits,
                        loan.lifetime,
                        loan.field,
                    );
                    self.reference_lifetimes[*slot] = lifetime;
                } else if self.is_carrier_type(ty) {
                    let splits = provenance
                        .leaves
                        .values()
                        .map(|loan| loan.splits.clone())
                        .reduce(|left, right| intersect_splits(&left, &right))
                        .unwrap_or_default();
                    self.acquire_record(*slot, provenance.clone(), splits);
                }
            }
            Pattern::Variant { fields, .. } => {
                for (offset, inner) in fields {
                    let Some(index) = self.field_index(ty, *offset) else {
                        continue;
                    };
                    let Some(field_ty) = ty
                        .layout()
                        .and_then(|id| self.enums[id].variants[0].fields.get(index).copied())
                    else {
                        continue;
                    };
                    let mut sub = RecordProvenance::default();
                    for (path, loan) in &provenance.leaves {
                        if path.first() != Some(&index) {
                            continue;
                        }
                        sub.leaves.insert(path[1..].to_vec(), loan.clone());
                    }
                    if field_ty.is_slice() {
                        // A sliced field pattern binds the direct leaf value.
                        if let Some(loan) = provenance.leaves.get(&vec![index]) {
                            sub.leaves.insert(Vec::new(), loan.clone());
                        }
                    }
                    self.bind_pattern_provenance(inner, field_ty, &sub)?;
                }
            }
            Pattern::Type { member, inner, .. } => {
                self.bind_pattern_provenance(inner, *member, provenance)?;
            }
            Pattern::Or(alternatives) => {
                for alternative in alternatives {
                    self.bind_pattern_provenance(alternative, ty, provenance)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    /// Propagate the borrowed-record payload of a joined `TaskExit<T>` into the
    /// pattern that matches `Completed`. Only the conventional task-exit shape
    /// carries this wrapper; every other enum payload is borrow-free.
    fn bind_task_exit_provenance(
        &mut self,
        pattern: &Pattern,
        ty: Type,
        provenance: &RecordProvenance,
    ) -> Result<()> {
        match pattern {
            Pattern::Type { member, inner, .. } => {
                self.bind_task_exit_provenance(inner, *member, provenance)
            }
            Pattern::Variant { tag, fields } => {
                let Some(id) = ty.layout() else {
                    return Ok(());
                };
                let field_types = {
                    let layout = &self.enums[id];
                    if layout.name != "TaskExit"
                        || layout
                            .variants
                            .get(*tag)
                            .is_none_or(|variant| variant.name != "Completed")
                    {
                        return Ok(());
                    }
                    let variant = &layout.variants[*tag];
                    let mut word = 1;
                    let mut field_types = Vec::with_capacity(variant.fields.len());
                    for field in &variant.fields {
                        field_types.push((word, *field));
                        word += crate::runtime_types::width(
                            self.enums,
                            self.unions,
                            self.functions,
                            *field,
                        );
                    }
                    field_types
                };
                for (offset, inner) in fields {
                    let Some((_, field_ty)) = field_types.iter().find(|(at, _)| at == offset)
                    else {
                        continue;
                    };
                    if self.is_carrier_type(*field_ty) {
                        self.bind_pattern_provenance(inner, *field_ty, provenance)?;
                    }
                }
                Ok(())
            }
            Pattern::Or(alternatives) => {
                for alternative in alternatives {
                    self.bind_task_exit_provenance(alternative, ty, provenance)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    /// Whether a live view borrows `source` through its capability ancestry.
    fn derives_from(&self, view: usize, source: usize) -> bool {
        view != source
            && self.view_sources[view]
                .as_ref()
                .is_some_and(|origins| origins.contains(&source))
    }
    fn has_live_descendant(&self, source: usize, ptr: usize, mutable_only: bool) -> bool {
        self.live_views_at(ptr).iter().any(|view| {
            // A view that is not available here was moved, or is the binding
            // currently being initialized. Neither is an active capability.
            self.available[*view]
                && self.derives_from(*view, source)
                && (!mutable_only || self.view_mut[*view])
        })
    }
    fn temporary_loan_at(&self, source: usize) -> bool {
        self.temporary_shared.contains(&source) || self.temporary_exclusive.contains(&source)
    }
    /// Any live or retained view derived from `source`, regardless of
    /// mutability. Moving or dropping a value requires this to be false.
    fn any_loan_at(&self, source: usize, ptr: usize) -> bool {
        self.temporary_loan_at(source) || self.has_live_descendant(source, ptr, false)
    }
    /// An exclusive view derived from `source` is live or retained.
    fn exclusive_loaned_at(&self, source: usize, ptr: usize) -> bool {
        self.exclusive_loans.contains(&source)
            || self.temporary_exclusive.contains(&source)
            || self.has_live_descendant(source, ptr, true)
    }
    /// Storage roots behind a slot.
    fn roots_of(&self, slot: usize) -> BTreeSet<usize> {
        if self.is_local_view(slot) {
            self.view_roots[slot].clone().unwrap_or_default()
        } else {
            BTreeSet::from([slot])
        }
    }
    fn origins_roots(&self, origins: &BTreeSet<usize>) -> BTreeSet<usize> {
        origins
            .iter()
            .flat_map(|slot| self.roots_of(*slot))
            .collect()
    }
    /// A view capability is suspended while a live or retained child view
    /// derived from it could access the same storage. An exclusive parent is
    /// suspended by any child; a shared parent only by an exclusive child.
    fn capability_suspended(&self, slot: usize, ptr: usize) -> bool {
        if self.view_mut[slot] {
            self.temporary_loan_at(slot) || self.has_live_descendant(slot, ptr, false)
        } else {
            self.temporary_exclusive.contains(&slot) || self.has_live_descendant(slot, ptr, true)
        }
    }
    /// Reject direct access through a slot while its capability is suspended,
    /// or through an owner while an exclusive view of it is live.
    fn check_owner_access(&self, slot: usize, ptr: usize, span: Span, what: &str) -> Result<()> {
        if self.locals[slot].ty.is_view()
            || (slot >= self.parameter_count && self.locals[slot].ty.is_ref())
        {
            if self.capability_suspended(slot, ptr) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot {what} a slice view while a child view derived from it is live (a view lent to a spawned task stays live until the scope ends); use the child, or wait until its last use"
                    ),
                )
                .with_note(self.locals[slot].span, "view declared here"));
            }
        } else if self.exclusive_loaned_at(slot, ptr) {
            if let Some(target) = &self.field_target
                && target.root == slot
                && self.is_carrier_type(self.locals[slot].ty)
                && self.field_access_isolated(slot, target, ptr)
            {
                // Reading the record only to reach a field whose live child
                // views are all structurally disjoint from that field does not
                // alias any exclusive field capability.
                return Ok(());
            }
            return Err(Diagnostic::new(
                span,
                format!("cannot {what} an owner while an exclusive '&mut [T]' view of it is live"),
            )
            .with_note(self.locals[slot].span, "owner declared here"));
        }
        Ok(())
    }
    /// No retained loan and every live descendant view of `record` is a
    /// structurally disjoint field from `target`.
    fn field_access_isolated(&self, record: usize, target: &FieldBorrow, ptr: usize) -> bool {
        if self.temporary_loan_at(record) || self.exclusive_loans.contains(&record) {
            return false;
        }
        self.live_views_at(ptr).iter().all(|view| {
            !self.available[*view]
                || !self.derives_from(*view, record)
                || self.view_fields[*view]
                    .as_ref()
                    .is_some_and(|field| field.disjoint(target))
        })
    }
    /// Capability ancestry a slice-view expression exposes: the view slot
    /// itself plus every view and storage root it derives from.
    fn view_origins(&self, expr: &Expr) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        self.collect_view_origins(expr, &mut out);
        out
    }
    fn collect_view_origins(&self, expr: &Expr, out: &mut BTreeSet<usize>) {
        if let Some(loan) = self.call_views.get(&(expr as *const Expr as usize)) {
            out.extend(loan.origins.iter().copied());
            return;
        }
        if let Some(origins) = self.call_origins.get(&(expr as *const Expr as usize)) {
            out.extend(origins.iter().copied());
            return;
        }
        match &expr.kind {
            ExprKind::Peek(slot) | ExprKind::Local(slot) | ExprKind::Move(slot)
                if expr.ty.is_ref() =>
            {
                out.insert(*slot);
                if let Some(origins) = &self.view_sources[*slot] {
                    out.extend(origins.iter().copied());
                }
            }
            ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
                if self.locals[*slot].ty.is_view() =>
            {
                out.insert(*slot);
                if let Some(origins) = &self.view_sources[*slot] {
                    out.extend(origins.iter().copied());
                }
            }
            ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Local(slot)
            | ExprKind::Move(slot) => {
                out.insert(*slot);
            }
            ExprKind::Slice { base, .. } => self.collect_view_origins(base, out),
            ExprKind::Project(..) if expr.ty.is_slice() => {
                out.extend(self.view_loan(expr).origins.iter().copied());
            }
            ExprKind::Coerce { value, .. } => self.collect_view_origins(value, out),
            ExprKind::Block(block) => {
                if let Some(tail) = &block.tail {
                    self.collect_view_origins(tail, out);
                }
            }
            ExprKind::If(_, yes, no) => {
                if let Some(tail) = &yes.tail {
                    self.collect_view_origins(tail, out);
                }
                if let Some(tail) = &no.tail {
                    self.collect_view_origins(tail, out);
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    self.collect_view_origins(&arm.body, out);
                }
            }
            _ => {}
        }
    }
    /// Split-side assumptions of a view expression. A direct checked split
    /// adds its group; descendants inherit their parent's assumptions. A
    /// borrowed call result inherits only the assumptions shared by every
    /// lifetime-matching argument, so a union of possible sources cannot
    /// launder a sibling exemption.
    fn split_labels(&self, expr: &Expr) -> SplitLabels {
        match &expr.kind {
            ExprKind::Slice { base, split, .. } => {
                let labels = self.split_labels(base);
                match split {
                    Some((group, left)) => labels.with(*group, *left),
                    None => labels,
                }
            }
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
                if self.locals[*slot].ty.is_view() =>
            {
                self.view_splits[*slot].clone()
            }
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot) => {
                let _ = slot;
                SplitLabels::default()
            }
            ExprKind::Project(..) if expr.ty.is_slice() => self.view_loan(expr).splits,
            ExprKind::Coerce { value, .. } => self.split_labels(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .map(|tail| self.split_labels(tail))
                .unwrap_or_default(),
            ExprKind::If(_, yes, no) => {
                let mut labels = match &yes.tail {
                    Some(tail) if yes.ty != Type::Never => self.split_labels(tail),
                    _ => SplitLabels::default(),
                };
                if no.ty != Type::Never {
                    let other = no
                        .tail
                        .as_ref()
                        .map(|tail| self.split_labels(tail))
                        .unwrap_or_default();
                    labels.0.retain(|group, left| {
                        other
                            .0
                            .get(group)
                            .is_some_and(|other_left| other_left == left)
                    });
                }
                labels
            }
            ExprKind::Match(_, arms) => {
                let mut labels: Option<SplitLabels> = None;
                for arm in arms.iter().filter(|arm| arm.body.ty != Type::Never) {
                    let arm_labels = self.split_labels(&arm.body);
                    labels = Some(match labels {
                        Some(mut labels) => {
                            labels.0.retain(|group, left| {
                                arm_labels
                                    .0
                                    .get(group)
                                    .is_some_and(|other_left| other_left == left)
                            });
                            labels
                        }
                        None => arm_labels,
                    });
                }
                labels.unwrap_or_default()
            }
            ExprKind::Call(_, _) | ExprKind::CallIndirect { .. } | ExprKind::TaskScope { .. } => {
                self.call_splits
                    .get(&(expr as *const Expr as usize))
                    .cloned()
                    .unwrap_or_default()
            }
            _ => SplitLabels::default(),
        }
    }
    fn acquire_view(
        &mut self,
        slot: usize,
        mutable: bool,
        origins: BTreeSet<usize>,
        splits: SplitLabels,
        lifetime: Option<String>,
        field: Option<FieldBorrow>,
    ) {
        let roots = self.origins_roots(&origins);
        self.view_mut[slot] = mutable;
        self.view_sources[slot] = Some(origins);
        self.view_roots[slot] = Some(roots);
        self.view_splits[slot] = splits;
        self.view_lifetimes[slot] = lifetime;
        self.view_fields[slot] = field;
    }
    /// Check that a view may be created from `origins` with `mutable`
    /// mutability, or reject an ancestor/sibling/root conflict.
    fn check_view_creation(
        &self,
        origins: &BTreeSet<usize>,
        mutable: bool,
        splits: &SplitLabels,
        field: Option<&FieldBorrow>,
        ptr: usize,
        span: Span,
    ) -> Result<()> {
        if origins.is_empty() {
            return Err(Diagnostic::new(
                span,
                "internal error: slice view has no capability provenance",
            ));
        }
        if mutable {
            for origin in origins {
                let is_mut = if self.is_local_view(*origin) {
                    self.view_mut[*origin]
                } else {
                    self.locals[*origin].ty.is_mut_slice()
                        || matches!(self.locals[*origin].ty, Type::RefMut(_))
                };
                if (self.locals[*origin].ty.is_slice() || self.locals[*origin].ty.is_ref())
                    && !is_mut
                {
                    return Err(Diagnostic::new(
                        span,
                        "cannot create an exclusive borrow from a shared borrow; shared storage cannot be upgraded",
                    )
                    .with_note(self.locals[*origin].span, "shared borrow declared here"));
                }
            }
        }
        let roots = self.origins_roots(origins);
        for retained in &self.temporary_regions {
            let overlaps = origins.iter().any(|slot| retained.origins.contains(slot))
                || roots.iter().any(|root| retained.roots.contains(root));
            let fields_disjoint = field
                .zip(retained.field.as_ref())
                .is_some_and(|(new, old)| new.disjoint(old));
            if !overlaps || splits.disjoint(&retained.splits) || fields_disjoint {
                continue;
            }
            if retained.mutable {
                return Err(Diagnostic::new(
                    span,
                    "cannot create a view while an exclusive view retained by this expression (or lent to a spawned task) is live",
                ));
            }
            if mutable {
                return Err(Diagnostic::new(
                    span,
                    "cannot create an exclusive view while a shared view retained by this expression (or lent to a spawned task) is live",
                ));
            }
        }
        if roots.iter().any(|root| self.exclusive_loans.contains(root)) {
            return Err(Diagnostic::new(
                span,
                if mutable {
                    "cannot create a mutable slice view while an exclusive '&mut Record' borrow of the same owner is live in this call"
                } else {
                    "cannot create a slice view while an exclusive '&mut Record' borrow of the same owner is live in this call"
                },
            ));
        }
        for view in self.live_views_at(ptr) {
            if !self.available[*view] {
                continue;
            }
            if origins.contains(view) {
                // The immediate parent and its ancestors are the capability
                // path being narrowed; they are suspended, not aliases.
                continue;
            }
            let view_roots = self.roots_of(*view);
            if view_roots.is_disjoint(&roots) {
                continue;
            }
            if splits.disjoint(&self.view_splits[*view]) {
                // The only split exemption: both views descend from opposite
                // sides of the same checked Slice.split_at_mut group.
                continue;
            }
            if field
                .zip(self.view_fields[*view].as_ref())
                .is_some_and(|(new, old)| new.disjoint(old))
            {
                // Structurally disjoint fields of one local record are
                // separate loan capabilities. Neither can reach the other's
                // storage, and the record itself stays suspended for moves.
                continue;
            }
            if mutable || self.view_mut[*view] {
                let what = if mutable {
                    "cannot create an exclusive '&mut [T]' view while another view of the same owner is live; split siblings require one checked Slice.split_at_mut pair, and independent disjoint ranges are not inferred"
                } else {
                    "cannot create a shared '&[T]' view while an exclusive '&mut [T]' view of the same owner is live"
                };
                return Err(Diagnostic::new(span, what)
                    .with_note(self.locals[*view].span, "conflicting view declared here"));
            }
        }
        Ok(())
    }
    /// Check that a returned view borrows only parameters carrying the declared
    /// result lifetime and, for an exclusive result, only mutable capability
    /// parameters or mutable child views derived from them.
    fn check_return_origins(
        &self,
        origins: &BTreeSet<usize>,
        view_lifetime: Option<&str>,
        mutable: bool,
        span: Span,
    ) -> Result<()> {
        let Some(lifetime) = &self.result_lifetime else {
            return Err(Diagnostic::new(
                span,
                "a borrowed slice return requires a declared result lifetime",
            ));
        };
        if !view_lifetime.is_some_and(|view| self.actual_outlives(view, lifetime)) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "borrowed return would dangle: the returned view is not a slice parameter with the declared result lifetime '{lifetime}' or a lifetime that outlives it (it has lifetime {})",
                    view_lifetime.unwrap_or("a temporary or local owner")
                ),
            ));
        }
        if origins.is_empty() {
            return Err(Diagnostic::new(
                span,
                "a borrowed slice return must derive from a parameter, not a temporary",
            ));
        }
        for origin in origins {
            if *origin < self.parameter_count {
                let element = &self.locals[*origin];
                if !self.parameter_carries_lifetime(*origin, lifetime, mutable) {
                    return Err(Diagnostic::new(
                        span,
                        if mutable {
                            "an exclusive '&mut [T]' return must derive from an exclusive '&mut [T]' parameter or an exclusive mutable record-field parameter carrying the declared result lifetime"
                        } else {
                            "borrowed return would dangle: the borrowed storage is not a parameter carrying the declared result lifetime"
                        },
                    )
                    .with_note(element.span, "borrowed storage declared here"));
                }
            } else if self.is_local_view(*origin) {
                // A local child view is not owned storage. It may be returned
                // if every root it derives from satisfies the lifetime above.
                if mutable && !self.view_mut[*origin] {
                    return Err(Diagnostic::new(
                        span,
                        "an exclusive '&mut [T]' return cannot derive from a shared child view",
                    )
                    .with_note(self.locals[*origin].span, "shared view declared here"));
                }
            } else {
                return Err(Diagnostic::new(
                    span,
                    "borrowed return would dangle: the returned view borrows a stack local or temporary",
                )
                .with_note(self.locals[*origin].span, "borrowed storage declared here"));
            }
        }
        Ok(())
    }
    /// Check a returned `&Record`/`&mut Record` against the declared result
    /// lifetime. The reference must derive from a matching reference parameter;
    /// a local owner's address cannot escape the callee frame.
    fn check_return_reference(
        &self,
        origins: &BTreeSet<usize>,
        view_lifetime: Option<&str>,
        mutable: bool,
        span: Span,
    ) -> Result<()> {
        let Some(lifetime) = &self.result_lifetime else {
            return Err(Diagnostic::new(
                span,
                "a returned borrowed reference requires a declared result lifetime",
            ));
        };
        if !view_lifetime.is_some_and(|view| self.actual_outlives(view, lifetime)) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "returned reference would dangle: its borrow is not a reference parameter with the declared result lifetime '{lifetime}' or a lifetime that outlives it (it has lifetime {})",
                    view_lifetime.unwrap_or("a temporary or local owner")
                ),
            ));
        }
        if origins.is_empty() {
            return Err(Diagnostic::new(
                span,
                "a returned reference must derive from a reference parameter, not a temporary",
            ));
        }
        for origin in origins {
            if *origin >= self.parameter_count && self.is_local_view(*origin) {
                // A stored reference local is a lexical child of the reference
                // it was derived from. Nothing here owns storage, so every
                // storage root must still be a reference parameter carrying the
                // declared result lifetime. Returning a reference to a record
                // parameter by value is rejected because that parameter's
                // storage dies with the call.
                if mutable && !self.view_mut[*origin] {
                    return Err(Diagnostic::new(
                        span,
                        "an exclusive reference return cannot derive from a shared stored reference",
                    )
                    .with_note(self.locals[*origin].span, "shared reference declared here"));
                }
                for root in self.roots_of(*origin) {
                    if root >= self.parameter_count
                        || (!self.locals[root].ty.is_ref()
                            && !self.is_carrier_type(self.locals[root].ty))
                    {
                        return Err(Diagnostic::new(
                            span,
                            "returned reference would dangle: it is reborrowed from a stack local, a by-value parameter, or another non-reference place",
                        )
                        .with_note(self.locals[root].span, "borrowed storage declared here"));
                    }
                    if !self.parameter_carries_lifetime(root, lifetime, mutable) {
                        return Err(Diagnostic::new(
                            span,
                            if mutable {
                                "an exclusive reference return must derive from an exclusive reference parameter with the declared result lifetime"
                            } else {
                                "returned reference would dangle: the reference parameter does not carry the declared result lifetime"
                            },
                        )
                        .with_note(self.locals[root].span, "reference parameter declared here"));
                    }
                }
                continue;
            }
            if *origin >= self.parameter_count
                || (!self.locals[*origin].ty.is_ref()
                    && !self.is_carrier_type(self.locals[*origin].ty))
            {
                return Err(Diagnostic::new(
                    span,
                    "returned reference would dangle: it borrows a stack local, a record value, or another non-reference place",
                )
                .with_note(self.locals[*origin].span, "borrowed storage declared here"));
            }
            if !self.parameter_carries_lifetime(*origin, lifetime, mutable) {
                return Err(Diagnostic::new(
                    span,
                    if mutable {
                        "an exclusive reference return must derive from an exclusive reference parameter with the declared result lifetime"
                    } else {
                        "returned reference would dangle: the parameter does not carry the declared result lifetime"
                    },
                )
                .with_note(self.locals[*origin].span, "reference parameter declared here"));
            }
        }
        Ok(())
    }
    /// Check a returned borrowed record field by field against the function's
    /// declared result type. Every declared borrow leaf must be present with
    /// exactly the declared lifetime, and every origin must be a parameter
    /// carrying that lifetime.
    fn check_return_record(&self, provenance: &RecordProvenance, span: Span) -> Result<()> {
        let expected = leaves_of(
            self.enums,
            self.pointees,
            self.reference_labels,
            self.result_type,
        );
        for leaf in &expected {
            let Some(loan) = provenance.leaves.get(&leaf.path) else {
                return Err(Diagnostic::new(
                    span,
                    "returned borrowed record is missing provenance for a declared borrowed field",
                ));
            };
            let Some(lifetime) = &leaf.lifetime else {
                return Err(Diagnostic::new(
                    span,
                    "internal error: borrowed result record leaf has no declared lifetime",
                ));
            };
            if !loan
                .lifetime
                .as_ref()
                .is_some_and(|source| self.actual_outlives(source, lifetime))
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "returned borrowed record field has lifetime {}, which does not outlive the declared result lifetime '{lifetime}'",
                        loan.lifetime
                            .as_deref()
                            .unwrap_or("a temporary or local owner")
                    ),
                ));
            }
            if loan.mutable != leaf.mutable {
                return Err(Diagnostic::new(
                    span,
                    if leaf.mutable {
                        "returned borrowed record field is declared exclusive '&mut [T]' but its provenance is shared; shared storage cannot be returned mutably"
                    } else {
                        "returned borrowed record field is declared shared '&[T]' but its provenance is exclusive"
                    },
                ));
            }
            for origin in &loan.origins {
                self.check_return_origin(*origin, lifetime, leaf.mutable, span)?;
            }
        }
        if provenance.leaves.len() != expected.len() {
            return Err(Diagnostic::new(
                span,
                "returned borrowed record provenance does not match its declared fields",
            ));
        }
        Ok(())
    }
    /// Whether a parameter carries `lifetime` with a compatible capability for
    /// a returned view. An exclusive result requires an exclusive parameter or
    /// an exclusive record-field leaf; a shared result may narrow either.
    fn parameter_carries_lifetime(&self, slot: usize, lifetime: &str, mutable: bool) -> bool {
        let local = &self.locals[slot];
        if local.ty.is_ref() {
            return self
                .reference_lifetimes
                .get(slot)
                .and_then(|name| name.as_ref())
                .is_some_and(|name| self.actual_outlives(name, lifetime))
                && (!mutable || matches!(local.ty, Type::RefMut(_)));
        }
        if local.ty.is_view() {
            return self
                .parameter_lifetimes
                .get(slot)
                .and_then(|l| l.as_ref())
                .is_some_and(|name| self.actual_outlives(name, lifetime))
                && (!mutable || local.ty.is_mut_slice());
        }
        if self.is_carrier_type(local.ty) {
            return leaves_of(self.enums, self.pointees, self.reference_labels, local.ty)
                .iter()
                .any(|leaf| {
                    leaf.lifetime
                        .as_deref()
                        .is_some_and(|name| self.actual_outlives(name, lifetime))
                        && (!mutable || leaf.mutable)
                });
        }
        false
    }
    fn check_return_origin(
        &self,
        origin: usize,
        lifetime: &str,
        mutable: bool,
        span: Span,
    ) -> Result<()> {
        if origin < self.parameter_count {
            let local = &self.locals[origin];
            if !self.parameter_carries_lifetime(origin, lifetime, mutable) {
                return Err(Diagnostic::new(
                    span,
                    if mutable {
                        "returned borrowed record would dangle: its exclusive storage is not a parameter carrying the declared result lifetime"
                    } else {
                        "returned borrowed record would dangle: its storage is not a parameter carrying the declared result lifetime"
                    },
                )
                .with_note(local.span, "borrowed storage declared here"));
            }
            return Ok(());
        }
        if self.is_local_view(origin) {
            if mutable && !self.view_mut[origin] {
                return Err(Diagnostic::new(
                    span,
                    "returned borrowed record would dangle: an exclusive field return cannot derive from a shared child view",
                )
                .with_note(self.locals[origin].span, "shared view declared here"));
            }
            for root in self.roots_of(origin) {
                if !self.parameter_carries_lifetime(root, lifetime, mutable) {
                    return Err(Diagnostic::new(
                        span,
                        "returned borrowed record would dangle: a child view root is not a parameter carrying the declared result lifetime",
                    )
                    .with_note(self.locals[root].span, "borrowed storage declared here"));
                }
            }
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            "returned borrowed record would dangle: it borrows a stack local or temporary",
        )
        .with_note(self.locals[origin].span, "borrowed storage declared here"))
    }
    /// Whether the value of `expr` is a direct move of a linear binding,
    /// including through value-position blocks, `if`, and `match`.
    fn value_moves_linear(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.locals[*slot].linear,
            ExprKind::Call(
                crate::executable::Target::Function(index)
                | crate::executable::Target::ObjectFunction {
                    function: index, ..
                },
                _,
            ) => self
                .result_grades
                .get(*index)
                .copied()
                .flatten()
                .is_some_and(|(grade, owning)| grade.is_one() && owning),
            ExprKind::Call(
                crate::executable::Target::Vec(
                    crate::executable::VecOp::Reserve
                    | crate::executable::VecOp::Clear
                    | crate::executable::VecOp::TryReserve { .. },
                    _,
                ),
                args,
            ) => args
                .first()
                .is_some_and(|owner| self.value_moves_linear(owner)),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => self.functions.get(id).is_some_and(|signature| {
                    signature.result_grade.is_some_and(Grade::is_one)
                        && (owns(signature.result, self.owned, self.unions, self.pointees)
                            || is_linear(
                                signature.result,
                                self.linear,
                                self.unions,
                                self.pointees,
                                self.functions,
                            ))
                }),
                _ => false,
            },
            ExprKind::Block(block) => self.block_value_moves_linear(block),
            ExprKind::If(_, yes, no) => {
                (yes.ty != Type::Never && self.block_value_moves_linear(yes))
                    || (no.ty != Type::Never && self.block_value_moves_linear(no))
            }
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|arm| arm.body.ty != Type::Never && self.value_moves_linear(&arm.body)),
            ExprKind::Construct { fields, .. } => {
                fields.iter().any(|field| self.value_moves_linear(field))
            }
            ExprKind::DynArrayPush { array, value, .. } => {
                self.value_moves_linear(array) || self.value_moves_linear(value)
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                self.value_moves_linear(array)
                    || self.value_moves_linear(index)
                    || self.value_moves_linear(value)
            }
            ExprKind::DynArrayPop { array, .. } => self.value_moves_linear(array),
            ExprKind::HandlerPush { body, .. } => body
                .tail
                .as_deref()
                .is_some_and(|tail| self.value_moves_linear(tail)),
            ExprKind::DynamicPerform { .. } => self.moves(expr.ty),
            ExprKind::FnValue { captures, .. } => captures
                .iter()
                .any(|capture| self.value_moves_linear(capture)),
            ExprKind::Loop(body) => loop_break_values(body)
                .into_iter()
                .any(|v| self.value_moves_linear(v)),
            ExprKind::Try { value, .. } => self.value_moves_linear(value),
            ExprKind::BoxTake(value) if self.moves(expr.ty) => self.value_moves_linear(value),
            ExprKind::BoxNew(value) => self.value_moves_linear(value),
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. } => {
                self.value_moves_linear(owner) || self.value_moves_linear(payload)
            }
            ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            }
            | ExprKind::ArenaBoxTake(value) => self.value_moves_linear(value),
            ExprKind::ArenaAlloc { value, .. } => self.value_moves_linear(value),
            ExprKind::VecMap { vector, .. } => self.value_moves_linear(vector),
            ExprKind::TaskSpawn { obligation, .. }
            | ExprKind::TaskScope { obligation, .. }
            | ExprKind::TaskJoin { obligation, .. } => *obligation,
            ExprKind::Coerce { value, .. } => self.value_moves_linear(value),
            _ => false,
        }
    }
    fn block_value_moves_linear(&self, block: &Block) -> bool {
        block
            .tail
            .as_ref()
            .is_some_and(|tail| self.value_moves_linear(tail))
    }
    fn discards_linear(&self, expr: &Expr) -> bool {
        self.value_moves_linear(expr)
    }
    fn resource(&mut self, ty: Type, span: Span) -> Result<usize> {
        if self.resources.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024 ownership-resource limit",
            ));
        }
        let id = self.resources.len();
        self.resources.push(ty);
        Ok(id)
    }
    fn bound(&mut self, slot: usize) {
        for state in &mut self.loops {
            state.bound.push(slot);
        }
    }
    /// Linear locals among `slots` that are still unconsumed are errors.
    fn exit_check(
        &self,
        slots: impl IntoIterator<Item = usize>,
        span: Span,
        reason: &str,
    ) -> Result<()> {
        for slot in slots {
            if self.available[slot] && self.slot_linear(slot) {
                return Err(Diagnostic::new(
                    span,
                    format!("linear value is not consumed before {reason}; move it into a call, constructor, or return value"),
                )
                .with_note(self.locals[slot].span, "linear value bound here"));
            }
        }
        Ok(())
    }
    fn use_after_move(&self, slot: usize, span: Span, message: &str) -> Diagnostic {
        let error = Diagnostic::new(span, message.to_owned());
        match self.moved_at[slot] {
            Some(at) => error.with_note(at, "value moved here"),
            None => error,
        }
    }
    /// Retain a slice result through the rest of its enclosing expression,
    /// including later call arguments. This is separate from local liveness.
    fn hold_view(&mut self, expr: &Expr) -> Result<()> {
        self.hold_view_with(expr, false)
    }
    /// Reference field reads do not retain an argument loan, but passing the
    /// reference to a call does: later arguments must not alias that capability.
    fn hold_reference_argument(&mut self, expr: &Expr) -> Result<()> {
        if expr.ty.is_ref()
            && matches!(
                expr.kind,
                ExprKind::Local(_) | ExprKind::Peek(_) | ExprKind::Move(_) | ExprKind::Borrow(_)
            )
        {
            self.hold_view_with(expr, true)?;
        }
        Ok(())
    }
    fn hold_view_with(&mut self, expr: &Expr, argument: bool) -> Result<()> {
        if !(expr.ty.is_view() || expr.ty.is_ref()) {
            return Ok(());
        }
        // A field projection used as a subview base is a place, not a
        // ready-made view; the Slice expression retains the child capability.
        if self.in_field_subview && matches!(expr.kind, ExprKind::Project(..)) {
            return Ok(());
        }
        // Reading an existing reference is not creating a new capability; its
        // loan was established by the caller. Retaining it per read would make
        // `p.x = p.x + 1` conflict with itself.
        if !argument
            && expr.ty.is_ref()
            && matches!(
                expr.kind,
                ExprKind::Local(_) | ExprKind::Peek(_) | ExprKind::Move(_) | ExprKind::Borrow(_)
            )
        {
            return Ok(());
        }
        // A nested builtin may reborrow the same retained receiver: argument
        // evaluation finishes before either builtin actually accesses storage.
        // This permission never allows moving it into an ordinary function.
        let receiver = match &expr.kind {
            ExprKind::Local(slot) if self.reborrow && expr.ty.is_mut_slice() => Some(*slot),
            _ => None,
        };
        if receiver.is_some_and(|slot| self.reborrowed_views.contains(&slot)) {
            return Ok(());
        }
        let origins = self.view_origins(expr);
        let roots = self.origins_roots(&origins);
        let splits = self.split_labels(expr);
        let mutable = expr.ty.is_mut_slice() || matches!(expr.ty, Type::RefMut(_));
        let field = self.view_loan(expr).field;
        for retained in &self.temporary_regions {
            let overlaps = origins.iter().any(|slot| retained.origins.contains(slot))
                || roots.iter().any(|root| retained.roots.contains(root));
            let fields_disjoint = field
                .as_ref()
                .zip(retained.field.as_ref())
                .is_some_and(|(new, old)| new.disjoint(old));
            if !overlaps || splits.disjoint(&retained.splits) || fields_disjoint {
                continue;
            }
            if retained.mutable || mutable {
                return Err(Diagnostic::new(
                    expr.span,
                    "conflicting slice arguments: an exclusive view overlaps another view retained by this expression",
                ));
            }
        }
        if let Some(slot) = receiver {
            self.reborrowed_views.insert(slot);
        }
        self.temporary_regions.push(RetainedView {
            origins: origins.clone(),
            roots,
            mutable,
            splits,
            field,
        });
        self.loans.extend(origins.iter().copied());
        if mutable {
            self.temporary_exclusive.extend(origins);
        } else {
            self.temporary_shared.extend(origins);
        }
        Ok(())
    }
    fn check_pending_linear(&self, start: usize, span: Span) -> Result<()> {
        if let Some(origin) = self.pending_linear.get(start) {
            return Err(Diagnostic::new(
                span,
                "this exit would discard a pending linear value evaluated by the enclosing expression",
            )
            .with_note(*origin, "linear value evaluated here; consume it before leaving this expression"));
        }
        Ok(())
    }
    fn full(&mut self, expr: &mut Expr) -> Result<()> {
        let pending_linear = self.pending_linear.len();
        let temporary_shared = self.temporary_shared.clone();
        let temporary_exclusive = self.temporary_exclusive.clone();
        let temporary_regions = self.temporary_regions.clone();
        let reborrowed_views = self.reborrowed_views.clone();
        let bound_receivers = self.bound_receivers.clone();
        let loans = self.loans.clone();
        let exclusive_loans = self.exclusive_loans.clone();
        let shared_record_loans = self.shared_record_loans.clone();
        self.expr(expr)?;
        self.pending_linear.truncate(pending_linear);
        self.loans = loans;
        self.exclusive_loans = exclusive_loans;
        self.shared_record_loans = shared_record_loans;
        self.temporary_shared = temporary_shared;
        self.temporary_exclusive = temporary_exclusive;
        self.temporary_regions = temporary_regions;
        self.reborrowed_views = reborrowed_views;
        self.bound_receivers = bound_receivers;
        self.apply_task_regions();
        Ok(())
    }
    /// Re-establish child-task loans after a temporary restore.
    fn apply_task_regions(&mut self) {
        for retained in self.task_regions.clone() {
            self.loans.extend(retained.origins.iter().copied());
            if retained.mutable {
                self.temporary_exclusive
                    .extend(retained.origins.iter().copied());
            } else {
                self.temporary_shared
                    .extend(retained.origins.iter().copied());
            }
            let present = self.temporary_regions.iter().any(|existing| {
                existing.origins == retained.origins && existing.mutable == retained.mutable
            });
            if !present {
                self.temporary_regions.push(retained);
            }
        }
    }
    fn block(&mut self, block: &mut Block) -> Result<()> {
        let entry_loans = self.loans.clone();
        // A reordered borrowed-record literal is lowered to source-order
        // temporaries followed by a layout-order construct. Retain each temp
        // field's loans while the remaining fields evaluate, so an owner cannot
        // be replaced between two fields of the same literal.
        let borrowed_temporaries = block
            .tail
            .as_ref()
            .filter(|tail| self.is_carrier_type(tail.ty))
            .and_then(|tail| match &tail.kind {
                ExprKind::Construct { fields, .. } => Some(
                    fields
                        .iter()
                        .filter_map(|field| match field.kind {
                            ExprKind::Local(slot) | ExprKind::Move(slot) => Some(slot),
                            _ => None,
                        })
                        .collect::<BTreeSet<_>>(),
                ),
                _ => None,
            })
            .unwrap_or_default();
        let mut slots = Vec::new();
        for statement in &mut block.statements {
            match statement {
                Statement::Let(slot, expr) => {
                    let slot = *slot;
                    // Elaboration tracks later assignments for capture typing.
                    // Start this binding with its declaration's obligation, not
                    // a flag inherited from a future replacement value.
                    self.locals[slot].linear = self.locals[slot]
                        .grade
                        .is_some_and(crate::grades::Grade::is_one)
                        && self.moves(self.locals[slot].ty);
                    // Moving a linear binding into an ungraded local must not
                    // launder away its consumption obligation.
                    let linear = self.value_moves_linear(expr);
                    // A borrowed-capture closure is only constructed directly
                    // as this binding's initializer.
                    let site = through_coerce(expr);
                    let site_pointer = site as *const Expr as usize;
                    let capture_site =
                        matches!(site.kind, ExprKind::FnValue { .. }).then_some(site_pointer);
                    let inherited_wrapped = match &site.kind {
                        ExprKind::Local(source) | ExprKind::Move(source) => {
                            self.wrapped_locals[*source].clone()
                        }
                        _ => None,
                    };
                    let old_capture_site = self.capture_site;
                    let old_callee_site = self.callee_site;
                    self.capture_site = capture_site;
                    self.callee_site = None;
                    let checked = self.full(expr);
                    self.capture_site = old_capture_site;
                    self.callee_site = old_callee_site;
                    checked?;
                    if linear || self.value_moves_linear(expr) {
                        self.locals[slot].linear = true;
                    }
                    if self.locals[slot].ty.is_view() {
                        let origins = self.view_origins(expr);
                        let mutable = self.locals[slot].ty.is_mut_slice();
                        let splits = self.split_labels(expr);
                        let loan = self.view_loan(expr);
                        let lifetime = loan.lifetime;
                        let field = loan.field;
                        self.acquire_view(slot, mutable, origins, splits, lifetime, field);
                    } else if self.is_carrier_type(self.locals[slot].ty) {
                        let provenance = self.record_provenance(expr);
                        let splits = provenance
                            .leaves
                            .values()
                            .map(|loan| loan.splits.clone())
                            .reduce(|left, right| intersect_splits(&left, &right))
                            .unwrap_or_default();
                        self.acquire_record(slot, provenance, splits);
                    } else if self.locals[slot].ty.is_ref() {
                        // A stored reference is a lexical capability over its
                        // source storage. It owns nothing at runtime: the
                        // one-word pointer is the checked runtime value. The
                        // lifetime is the source's declared lifetime when the
                        // reference came from a parameter or a call result, and
                        // a frame-local identity otherwise so an escape remains
                        // a checked dangling-borrow error.
                        let loan = self.view_loan(expr);
                        let origins = if loan.origins.is_empty() {
                            self.view_origins(expr)
                        } else {
                            loan.origins.clone()
                        };
                        if origins.is_empty() {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: stored reference has no capability provenance",
                            ));
                        }
                        let lifetime = loan
                            .lifetime
                            .clone()
                            .or_else(|| Some(self.anonymous_lifetime(&origins)));
                        let mutable = matches!(self.locals[slot].ty, Type::RefMut(_));
                        self.acquire_view(
                            slot,
                            mutable,
                            origins,
                            SplitLabels::default(),
                            lifetime.clone(),
                            None,
                        );
                        self.reference_lifetimes[slot] = lifetime;
                    } else if let Some(provenance) = self.task_results.get(&site_pointer).cloned() {
                        // A child task's borrowed-record result is still loaned
                        // to the scope; the handle carries the provenance until
                        // Task.join transfers it to the TaskExit value.
                        self.task_sources[slot] = Some(provenance);
                    } else if let Some(provenance) = self
                        .wrapped_results
                        .get(&site_pointer)
                        .cloned()
                        .or(inherited_wrapped)
                    {
                        // Copying or moving a TaskExit value that wraps a
                        // borrowed record keeps the same loan provenance.
                        self.wrapped_locals[slot] = Some(provenance);
                    } else if let Some(capture) = self.borrowed_values.get(&site_pointer).cloned() {
                        // The closure value is now a scoped loan holder. Its
                        // captures point at the original owners, and the
                        // backward liveness pass keeps this capability live
                        // until its last call or enclosing-scope end.
                        self.acquire_view(
                            slot,
                            capture.mutable,
                            capture.origins.clone(),
                            capture.splits.clone(),
                            None,
                            None,
                        );
                        self.borrowed_closures.insert(slot, capture);
                    }
                    if borrowed_temporaries.contains(&slot) {
                        self.retain_local(slot);
                    }
                    self.available[slot] = true;
                    self.moved_at[slot] = None;
                    self.bound(slot);
                    slots.push(slot);
                }
                Statement::Expr(expr) => {
                    self.full(expr)?;
                    if expr.ty != Type::Never
                        && (is_linear(
                            expr.ty,
                            self.linear,
                            self.unions,
                            self.pointees,
                            self.functions,
                        ) || self.discards_linear(expr))
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            "this linear value is discarded; bind it and consume it",
                        ));
                    }
                }
            }
        }
        if let Some(tail) = &mut block.tail {
            self.expr(tail)?;
        }
        if let Some(tail) = &block.tail
            && (tail.ty.is_slice() || tail.ty.is_ref() || self.is_carrier_type(tail.ty))
        {
            let origins = if tail.ty.is_slice() || tail.ty.is_ref() {
                self.view_origins(tail)
            } else {
                let provenance = self.record_provenance(tail);
                provenance
                    .leaves
                    .values()
                    .flat_map(|loan| loan.origins.iter().copied())
                    .collect()
            };
            if let Some(owner) = slots
                .iter()
                .find(|slot| origins.contains(slot) && !self.is_local_view(**slot))
            {
                return Err(Diagnostic::new(
                    tail.span,
                    if tail.ty.is_slice() {
                        "slice view would outlive the lexical scope of its owner"
                    } else if tail.ty.is_ref() {
                        "reference escapes the lexical scope of the storage it borrows"
                    } else {
                        "borrowed record would outlive the lexical scope of its owner"
                    },
                )
                .with_note(self.locals[*owner].span, "owner declared here"));
            }
        }
        if block.ty != Type::Never {
            self.exit_check(
                slots.iter().copied(),
                block_span(block),
                "the end of its scope",
            )?;
        }
        // A non-borrowing block value cannot carry a loan into the enclosing
        // expression. Borrowed views, borrowed records, and call-scoped owner
        // references (`&Box`/`&Vec`/`&Bytes`) do escape lexically and retain
        // their loan until their checked last use.
        let borrowing_value = block.ty.is_slice()
            || matches!(block.ty, Type::Ref(_) | Type::RefMut(_))
            || self.is_carrier_type(block.ty);
        if !borrowing_value {
            self.loans = entry_loans;
        } else {
            for slot in &slots {
                if self.loans.contains(slot) && !self.is_local_view(*slot) {
                    return Err(Diagnostic::new(
                        block_span(block),
                        "borrow escapes the lexical scope of its owner",
                    )
                    .with_note(self.locals[*slot].span, "owner declared here"));
                }
            }
        }
        for slot in slots {
            self.available[slot] = false;
        }
        Ok(())
    }
    fn loop_end(&self, span: Span, what: &str) -> Result<()> {
        let state = self.loops.last().unwrap();
        for (slot, was) in state.entry.iter().enumerate() {
            if self.available[slot]
                && self.slot_linear(slot)
                && (!*was || !state.entry_linear[slot])
            {
                return Err(Diagnostic::new(span,
                    "loop back-edge introduces a linear obligation absent at the loop head; declare the outer binding linear before the loop or consume the replacement before repeating")
                    .with_note(self.locals[slot].span, "loop-carried binding declared here"));
            }
            if *was && !self.available[slot] && self.moves(self.locals[slot].ty) {
                return Err(self.use_after_move(
                    slot,
                    span,
                    &format!("a value used by the next loop iteration is moved {what}; reassign it before the iteration ends or move it out after the loop"),
                ));
            }
        }
        Ok(())
    }
    fn cleanup_list(&self) -> Vec<usize> {
        let state = self.loops.last().unwrap();
        let mut ids = (state.resource_start..self.resources.len()).collect::<Vec<_>>();
        ids.extend(state.bound.iter().filter_map(|s| self.local_resources[*s]));
        ids.sort_unstable();
        ids.dedup();
        ids.reverse();
        ids
    }
    fn enter_loop(&mut self) {
        self.loops.push(LoopState {
            pending_linear_start: self.pending_linear.len(),
            entry: self.available.clone(),
            entry_linear: (0..self.locals.len())
                .map(|slot| self.slot_linear(slot))
                .collect(),
            breaks: None,
            resource_start: self.resources.len(),
            bound: Vec::new(),
        });
    }
    fn expr(&mut self, expr: &mut Expr) -> Result<()> {
        let pending_linear = self.pending_linear.len();
        let temporary_shared = self.temporary_shared.clone();
        let temporary_exclusive = self.temporary_exclusive.clone();
        let temporary_regions = self.temporary_regions.clone();
        let reborrowed_views = self.reborrowed_views.clone();
        let bound_receivers = self.bound_receivers.clone();
        let expr_ptr = expr as *const Expr as usize;
        let expr_field = matches!(expr.kind, ExprKind::Project(..))
            .then(|| self.projection_field(expr))
            .flatten();
        match &mut expr.kind {
            // Reading a stored reference is a reborrow, not a move: the
            // binding keeps the underlying capability for its whole lexical
            // lifetime, and each use narrows it for the enclosing expression.
            // Explicit `&*p`/`&mut *p` lowers to this same node.
            ExprKind::Local(slot) if self.locals[*slot].ty.is_ref() => {
                if !self.available[*slot] {
                    return Err(self.use_after_move(
                        *slot,
                        expr.span,
                        "use of an uninitialized or unavailable reference binding",
                    ));
                }
                self.check_owner_access(*slot, expr_ptr, expr.span, "use")?;
            }
            ExprKind::Local(slot) if self.moves(expr.ty) || self.locals[*slot].linear => {
                let slot = *slot;
                if !self.available[slot] {
                    return Err(self.use_after_move(
                        slot,
                        expr.span,
                        "use after move (or a move on another control-flow path)",
                    ));
                }
                if self.borrowed_closures.contains_key(&slot) && self.callee_site != Some(expr_ptr)
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a closure with borrowed slice captures is scoped: call it directly at this binding's scope, or pass no borrowed captures. It cannot be moved, returned, stored, captured, or passed to another function",
                    )
                    .with_note(self.locals[slot].span, "borrowing closure bound here"));
                }
                // A builtin slice read/write reborrows an exclusive view for
                // the call instead of consuming the capability.
                if self.reborrow && expr.ty.is_mut_slice() {
                    if !self.reborrowed_views.contains(&slot) {
                        self.check_owner_access(slot, expr_ptr, expr.span, "use")?;
                    }
                    return self.hold_view(expr);
                }
                if self.guard {
                    return Err(Diagnostic::new(
                        expr.span,
                        "match guards cannot consume owned or linear bindings; borrow them instead",
                    ));
                }
                if self.loans.contains(&slot) || self.any_loan_at(slot, expr_ptr) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot move an owner while it is borrowed by this call or a slice view",
                    ));
                }
                self.available[slot] = false;
                self.moved_at[slot] = Some(expr.span);
                expr.kind = ExprKind::Move(slot);
            }
            ExprKind::Peek(slot) => {
                if !self.available[*slot] {
                    return Err(self.use_after_move(
                        *slot,
                        expr.span,
                        "cannot read a field of a moved value",
                    ));
                }
                self.check_owner_access(*slot, expr_ptr, expr.span, "read")?;
            }
            ExprKind::Local(slot) => {
                // A copyable owner (an inline array) still may not be observed
                // through its own name while an exclusive view is live.
                self.check_owner_access(*slot, expr_ptr, expr.span, "read")?;
            }
            ExprKind::Project(base, _) => {
                let old_target = std::mem::replace(&mut self.field_target, expr_field.clone());
                let checked = self.expr(base);
                self.field_target = old_target;
                checked?;
                if expr.ty.is_slice() {
                    let loan = self.view_loan(expr);
                    if loan.mutable && !self.in_field_subview {
                        return Err(Diagnostic::new(
                            expr.span,
                            "an exclusive '&mut [T]' record field cannot be projected directly; destructure the record first, as in 'let Window { view, .. } = window;', or derive a subview with '&mut record.view[..]'",
                        ));
                    }
                    self.check_view_creation(
                        &loan.origins,
                        loan.mutable,
                        &loan.splits,
                        loan.field.as_ref(),
                        expr_ptr,
                        expr.span,
                    )?;
                } else if expr
                    .ty
                    .layout()
                    .is_some_and(|id| self.enums[id].mutable_borrow)
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a nested record containing an exclusive field cannot be projected directly; destructure the parent record first",
                    ));
                }
            }
            ExprKind::Borrow(slot) => {
                if !self.available[*slot] {
                    return Err(self.use_after_move(
                        *slot,
                        expr.span,
                        "cannot borrow a moved owner",
                    ));
                }
                self.check_owner_access(*slot, expr_ptr, expr.span, "borrow")?;
                let record = self.locals[*slot]
                    .ty
                    .layout()
                    .is_some_and(|id| self.enums[id].record);
                if record {
                    if matches!(expr.ty, Type::RefMut(_)) {
                        if self.loans.contains(slot)
                            || self.temporary_shared.contains(slot)
                            || self.temporary_exclusive.contains(slot)
                            || self.any_loan_at(*slot, expr_ptr)
                        {
                            return Err(Diagnostic::new(
                                expr.span,
                                "cannot create an exclusive '&mut Record' borrow while another borrow or view of the same owner is live",
                            )
                            .with_note(self.locals[*slot].span, "owner declared here"));
                        }
                        self.temporary_exclusive.insert(*slot);
                        self.exclusive_loans.insert(*slot);
                    } else {
                        if self.exclusive_loaned_at(*slot, expr_ptr) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "cannot create a shared '&Record' borrow while an exclusive borrow of the same owner is live",
                            )
                            .with_note(self.locals[*slot].span, "owner declared here"));
                        }
                        self.temporary_shared.insert(*slot);
                        self.shared_record_loans.insert(*slot);
                    }
                }
                self.loans.insert(*slot);
            }
            ExprKind::Block(block) => self.block(block)?,
            ExprKind::Coerce { value, .. } => self.expr(value)?,
            ExprKind::Unary(_, value) => self.expr(value)?,
            ExprKind::BoxTake(value) => {
                self.expr(value)?;
                if expr.ty.is_ref() {
                    let loan = self
                        .container_provenance(value)
                        .leaves
                        .get(&Vec::new())
                        .cloned()
                        .unwrap_or_default();
                    self.call_views.insert(expr_ptr, loan.clone());
                    self.call_origins.insert(expr_ptr, loan.origins);
                    self.call_splits.insert(expr_ptr, loan.splits);
                }
            }
            ExprKind::BoxNew(value) => {
                self.expr(value)?;
                if value.ty.is_ref() {
                    let loan = self.view_loan(value);
                    let mut provenance = RecordProvenance::default();
                    provenance.leaves.insert(Vec::new(), loan);
                    self.call_records.insert(expr_ptr, provenance);
                }
            }
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. } => {
                if let Type::Box(p) = owner.ty
                    && self.value_moves_linear(owner)
                    && self.moves(self.pointees[p])
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "in-place box reuse cannot discard an owned payload with a propagated linear obligation",
                    ));
                }
                let loans = self.loans.clone();
                self.expr(owner)?;
                self.expr(payload)?;
                self.loans = loans;
            }
            ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            } => {
                self.expr(value)?;
            }
            ExprKind::ArenaNew => {}
            ExprKind::ArenaAlloc { arena, value } => {
                // The arena borrow lasts for the call only; the returned box
                // carries its own region reference.
                let loans = self.loans.clone();
                self.expr(arena)?;
                self.hold_reference_argument(arena)?;
                self.expr(value)?;
                self.loans = loans;
            }
            ExprKind::ArenaBoxRead(value) => {
                if self.moves(expr.ty) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "ArenaBox.read cannot copy an owned payload (or a linear one); consume it with ArenaBox.take",
                    ));
                }
                let loans = self.loans.clone();
                self.expr(value)?;
                self.loans = loans;
            }
            ExprKind::ArenaBoxTake(value) => self.expr(value)?,
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                let loans = self.loans.clone();
                self.expr(vector)?;
                for callback in callbacks {
                    self.expr(callback)?;
                }
                self.loans = loans;
            }
            ExprKind::Try { value, .. } => {
                self.check_pending_linear(0, expr.span)?;
                self.expr(value)?;
                // The error path returns early; nothing linear may be left behind.
                self.exit_check(0..self.available.len(), expr.span, "'?' returns early")?;
            }
            ExprKind::Return(value) => {
                self.check_pending_linear(0, expr.span)?;
                self.expr(value)?;
                if value.ty.is_view() {
                    let origins = self.view_origins(value);
                    let lifetime = self.view_loan(value).lifetime;
                    self.check_return_origins(
                        &origins,
                        lifetime.as_deref(),
                        value.ty.is_mut_slice(),
                        expr.span,
                    )?;
                } else if value.ty.is_ref() {
                    let origins = self.view_origins(value);
                    let lifetime = self.view_loan(value).lifetime;
                    self.check_return_reference(
                        &origins,
                        lifetime.as_deref(),
                        matches!(value.ty, Type::RefMut(_)),
                        expr.span,
                    )?;
                } else if self.is_carrier_type(value.ty) {
                    let provenance = self.record_provenance(value);
                    self.check_return_record(&provenance, expr.span)?;
                }
                // The error path returns early; nothing linear may be left behind.
                self.exit_check(0..self.available.len(), expr.span, "this return")?;
            }
            ExprKind::Drop(value) => {
                if is_linear(
                    value.ty,
                    self.linear,
                    self.unions,
                    self.pointees,
                    self.functions,
                ) || matches!(&value.kind, ExprKind::Local(s) if self.locals[*s].linear)
                    || self.value_moves_linear(value)
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "linear values cannot be dropped; consume them by matching or passing them on",
                    ));
                }
                if let ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) =
                    &value.kind
                    && (self.shared_record_loans.contains(slot)
                        || self.exclusive_loans.contains(slot)
                        || self.any_loan_at(*slot, expr_ptr)
                        || (self.is_local_view(*slot)
                            && self.capability_suspended(*slot, expr_ptr)))
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot move or drop an owner or view while a slice view derived from it is live",
                    )
                    .with_note(self.locals[*slot].span, "value declared here"));
                }
                self.expr(value)?
            }
            ExprKind::BoxRead(value) => {
                if self.moves(expr.ty) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "Box.read cannot copy an owned payload (or a linear one); consume it with Box.take",
                    ));
                }
                let loans = self.loans.clone();
                self.expr(value)?;
                self.loans = loans;
                if expr.ty.is_ref() {
                    let loan = self
                        .container_provenance(value)
                        .leaves
                        .get(&Vec::new())
                        .cloned()
                        .unwrap_or_default();
                    self.call_views.insert(expr_ptr, loan.clone());
                    self.call_origins.insert(expr_ptr, loan.origins);
                    self.call_splits.insert(expr_ptr, loan.splits);
                }
            }
            ExprKind::Assign(slot, value) => {
                let slot = *slot;
                if self.any_loan_at(slot, expr_ptr) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot replace an owner while a slice view or reference borrows it",
                    ));
                }
                if self.loans.contains(&slot) || (self.moves(self.locals[slot].ty) && self.guard) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot replace an owner in a guard or while it is borrowed by a call",
                    ));
                }
                self.expr(value)?;
                if self.available[slot] && self.slot_linear(slot) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "assignment would drop an unconsumed linear value",
                    )
                    .with_note(self.locals[slot].span, "linear value bound here"));
                }
                if self.value_moves_linear(value) {
                    self.locals[slot].linear = true;
                }
                if self.locals[slot].ty.is_view() {
                    let origins = self.view_origins(value);
                    let mutable = self.locals[slot].ty.is_mut_slice();
                    let splits = self.split_labels(value);
                    let loan = self.view_loan(value);
                    let lifetime = loan.lifetime;
                    let field = loan.field;
                    self.acquire_view(slot, mutable, origins, splits, lifetime, field);
                } else if self.is_carrier_type(self.locals[slot].ty) {
                    let provenance = self.record_provenance(value);
                    let splits = provenance
                        .leaves
                        .values()
                        .map(|loan| loan.splits.clone())
                        .reduce(|left, right| intersect_splits(&left, &right))
                        .unwrap_or_default();
                    self.acquire_record(slot, provenance, splits);
                }
                self.available[slot] = true;
                self.moved_at[slot] = None;
            }
            ExprKind::RefRead(reference) => {
                if !reference.ty.is_ref() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: whole-value reference read requires a reference",
                    ));
                }
                self.expr(reference)?;
            }
            ExprKind::RefWrite(reference, value) => {
                if !matches!(reference.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: whole-value reference write requires an exclusive '&mut' reference",
                    ));
                }
                if self.moves(value.ty) || self.value_moves_linear(value) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot replace a borrowed object with an owning or linear value that the reference does not own",
                    ));
                }
                self.expr(reference)?;
                self.expr(value)?;
            }
            ExprKind::RefAssign(reference, _, value) => {
                if !matches!(reference.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: field assignment requires an exclusive '&mut Record' reference",
                    ));
                }
                if self.moves(value.ty) || self.value_moves_linear(value) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot store an owning or linear value in a record field through a reference; update an owning record value instead",
                    ));
                }
                self.expr(reference)?;
                self.expr(value)?;
            }
            ExprKind::Binary(op, left, right) => {
                self.expr(left)?;
                let before = self.available.clone();
                self.expr(right)?;
                if matches!(
                    op,
                    crate::lexer::Kind::AmpAmp | crate::lexer::Kind::PipePipe
                ) {
                    if right.ty == Type::Never {
                        self.available = before;
                    } else {
                        self.merge(&before, expr.span)?;
                    }
                }
            }
            ExprKind::BytesAt(a, b) => {
                let loans = self.loans.clone();
                self.expr(a)?;
                self.expr(b)?;
                self.loans = loans;
            }
            ExprKind::Call(target, args) => {
                let func = match target {
                    crate::executable::Target::Function(index)
                    | crate::executable::Target::ObjectFunction {
                        function: index, ..
                    } => Some(*index),
                    _ => None,
                };
                let loans = self.loans.clone();
                let reborrow = matches!(target, crate::executable::Target::Slice(_, _));
                if reborrow && let Some(first) = args.first_mut() {
                    let old = self.reborrow;
                    self.reborrow = true;
                    let own_bound_length = matches!(
                        target,
                        crate::executable::Target::Slice(crate::executable::SliceOp::Len, _)
                    ) && matches!(&first.kind, ExprKind::Local(slot)
                        if self.bound_receivers.contains(slot) && self.available[*slot]);
                    // Length reads metadata only and cannot retain a view or
                    // access elements. The reserved receiver was validated
                    // before evaluating its bounds; all other uses still go
                    // through the normal capability checks.
                    if !own_bound_length {
                        self.expr(first)?;
                    }
                    self.reborrow = old;
                }
                for (position, arg) in args.iter_mut().enumerate().skip(usize::from(reborrow)) {
                    self.expr(arg)?;
                    self.hold_reference_argument(arg)?;
                    if position == 0
                        && let crate::executable::Target::ObjectFunction {
                            receiver: Some(slot),
                            mutable,
                            ..
                        } = target
                    {
                        let slot = *slot;
                        if self.locals[slot].ty.is_ref() {
                            self.hold_reference_argument(&Expr {
                                kind: ExprKind::Peek(slot),
                                ty: if !*mutable {
                                    Type::Ref(self.locals[slot].ty.ref_pointee().unwrap())
                                } else {
                                    self.locals[slot].ty
                                },
                                span: arg.span,
                                resource: None,
                            })?;
                        } else {
                            let conflict = if *mutable {
                                self.any_loan_at(slot, expr_ptr) || self.loans.contains(&slot)
                            } else {
                                self.exclusive_loaned_at(slot, expr_ptr)
                            };
                            if conflict {
                                return Err(Diagnostic::new(
                                    arg.span,
                                    "cannot call a dynamic method while its object has a conflicting borrow",
                                ));
                            }
                            self.loans.insert(slot);
                            if *mutable {
                                self.temporary_exclusive.insert(slot);
                            } else {
                                self.temporary_shared.insert(slot);
                            }
                        }
                    }
                }
                self.loans = loans;
                if let crate::executable::Target::Vec(op, element) = target {
                    let element = *element;
                    let mut provenance = RecordProvenance::default();
                    match op {
                        crate::executable::VecOp::WithCapacity
                        | crate::executable::VecOp::Clear
                        | crate::executable::VecOp::TryReserve { .. } => {}
                        crate::executable::VecOp::Push | crate::executable::VecOp::Set => {
                            provenance = self.record_provenance(&args[0]);
                            if crate::runtime_types::width(
                                self.enums,
                                self.unions,
                                self.functions,
                                element,
                            ) == 1
                                && let Some(loan) = self.reference_element_loan(
                                    &args[if *op == crate::executable::VecOp::Set {
                                        2
                                    } else {
                                        1
                                    }],
                                )
                            {
                                // A shared vector may contain references to
                                // several owners. Retain every possible source;
                                // replacing one position does not prove that an
                                // earlier source is absent from other positions.
                                let existing = provenance.leaves.remove(&Vec::new());
                                let loan = self.merge_loans(existing.into_iter().chain([loan]));
                                provenance.leaves.insert(Vec::new(), loan);
                            }
                        }
                        crate::executable::VecOp::Reserve | crate::executable::VecOp::Len => {
                            provenance = self.record_provenance(&args[0]);
                        }
                        crate::executable::VecOp::Get | crate::executable::VecOp::At => {
                            if expr.ty.is_ref() {
                                let loan = self
                                    .container_provenance(&args[0])
                                    .leaves
                                    .get(&Vec::new())
                                    .cloned()
                                    .unwrap_or_default();
                                self.call_views.insert(expr_ptr, loan.clone());
                                self.call_origins.insert(expr_ptr, loan.origins);
                                self.call_splits.insert(expr_ptr, loan.splits);
                            }
                        }
                    }
                    if self.is_carrier_type(expr.ty) {
                        self.call_records.insert(expr_ptr, provenance);
                    }
                }
                if let Some(index) = func {
                    let parameters = self.calls[index].parameters.clone();
                    let result = self.calls[index].result.clone();
                    let bounds = self.calls[index].bounds.clone();
                    self.apply_call_lifetime(
                        parameters, result, bounds, args, expr_ptr, expr.ty, expr.span,
                    )?;
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                let loans = self.loans.clone();
                let callee_value = through_coerce(callee);
                // Save capture provenance before checking consumes the local
                // callee and rewrites it to a Move node.
                let local_capture = match &callee_value.kind {
                    ExprKind::Local(slot) => self.borrowed_closures.get(slot).cloned(),
                    _ => None,
                };
                let capture_site = matches!(callee_value.kind, ExprKind::FnValue { .. })
                    .then_some(callee_value as *const Expr as usize);
                let callee_local = match &callee_value.kind {
                    ExprKind::Local(slot) if self.borrowed_closures.contains_key(slot) => {
                        Some(callee_value as *const Expr as usize)
                    }
                    _ => None,
                };
                let old_capture_site = self.capture_site;
                let old_callee_site = self.callee_site;
                self.capture_site = capture_site;
                self.callee_site = callee_local;
                let checked = self.expr(callee);
                self.capture_site = old_capture_site;
                self.callee_site = old_callee_site;
                checked?;
                // Both a local callee and an immediately-invoked lambda retain
                // their captured views through all later argument evaluation.
                // Local liveness alone ends at the callee's move, before the
                // runtime actually calls it. Re-establish those loans here.
                let capture_info = capture_site
                    .and_then(|site| self.borrowed_values.get(&site))
                    .cloned()
                    .or(local_capture);
                if let Some(info) = &capture_info {
                    let roots = self.origins_roots(&info.origins);
                    self.temporary_regions.push(RetainedView {
                        origins: info.origins.clone(),
                        roots,
                        mutable: info.mutable,
                        splits: info.splits.clone(),
                        field: None,
                    });
                    self.loans.extend(info.origins.iter().copied());
                    if info.mutable {
                        self.temporary_exclusive
                            .extend(info.origins.iter().copied());
                    } else {
                        self.temporary_shared.extend(info.origins.iter().copied());
                    }
                }
                for argument in arguments.iter_mut() {
                    self.expr(argument)?;
                    self.hold_reference_argument(argument)?;
                }
                self.loans = loans;
                // A scoped closure may return a view or record borrowed from
                // its environment. The capture contract names the capture
                // position; resolve it to the capture's outer provenance now,
                // exactly as an argument-derived result is resolved below.
                if let Some(info) = &capture_info {
                    if let Some(loan) = &info.result_slice {
                        if !expr.ty.is_slice() || loan.mutable != expr.ty.is_mut_slice() {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: scoped closure result provenance disagrees with the callable result type",
                            ));
                        }
                        self.call_views.insert(expr_ptr, loan.clone());
                        self.call_origins.insert(expr_ptr, loan.origins.clone());
                        self.call_splits.insert(expr_ptr, loan.splits.clone());
                    }
                    if let Some(provenance) = &info.result_record {
                        if !self.is_carrier_type(expr.ty) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: scoped closure record result provenance disagrees with the callable result type",
                            ));
                        }
                        self.call_records.insert(expr_ptr, provenance.clone());
                    }
                }
                // A callable type with borrowed parameters or results carries
                // a borrow contract; apply it exactly as for a direct call.
                if let Type::Fn(id) | Type::Once(id) = callee.ty {
                    let signature = &self.functions[id];
                    let borrows = &signature.borrows;
                    if !borrows.parameters.is_empty()
                        || !borrows.parameter_leaves.is_empty()
                        || borrows.result.is_some()
                        || !borrows.result_leaves.is_empty()
                    {
                        let parameters = signature
                            .parameters
                            .iter()
                            .enumerate()
                            .map(|(i, ty)| {
                                let mut leaves = if ty.is_slice() {
                                    vec![crate::runtime_types::BorrowLeaf {
                                        path: vec![],
                                        lifetime: borrows.parameters.get(i).cloned().flatten(),
                                        mutable: ty.is_mut_slice(),
                                    }]
                                } else if ty.is_ref() {
                                    vec![crate::runtime_types::BorrowLeaf {
                                        path: vec![],
                                        lifetime: borrows.parameters.get(i).cloned().flatten(),
                                        mutable: matches!(ty, Type::RefMut(_)),
                                    }]
                                } else {
                                    Vec::new()
                                };
                                if let Some(record_leaves) = borrows.parameter_leaves.get(i) {
                                    leaves.extend(record_leaves.iter().map(|leaf| {
                                        crate::runtime_types::BorrowLeaf {
                                            path: leaf.path.clone(),
                                            lifetime: leaf.lifetime.clone(),
                                            mutable: leaf.mutable,
                                        }
                                    }));
                                }
                                leaves
                            })
                            .collect::<Vec<_>>();
                        let result = if signature.result.is_slice() {
                            CallResult::Slice {
                                lifetime: borrows.result.clone(),
                                mutable: signature.result.is_mut_slice(),
                            }
                        } else if signature.result.is_ref() {
                            CallResult::Reference {
                                lifetime: borrows.result.clone(),
                                mutable: matches!(signature.result, Type::RefMut(_)),
                            }
                        } else if self.is_carrier_type(signature.result) {
                            CallResult::Record(
                                borrows
                                    .result_leaves
                                    .iter()
                                    .map(|leaf| crate::runtime_types::BorrowLeaf {
                                        path: leaf.path.clone(),
                                        lifetime: leaf.lifetime.clone(),
                                        mutable: leaf.mutable,
                                    })
                                    .collect(),
                            )
                        } else {
                            CallResult::None
                        };
                        let bounds = borrows.bounds.clone();
                        self.apply_call_lifetime(
                            parameters, result, bounds, arguments, expr_ptr, expr.ty, expr.span,
                        )?;
                    }
                }
            }
            ExprKind::TaskScope { body, .. } => {
                // The scope body runs once, immediately, in this task, and the
                // scope joins every child before returning. Its borrowed
                // captures are therefore an immediate call's captures: their
                // loans cover exactly this expression.
                let loans = self.loans.clone();
                let site = through_coerce(body);
                let site_ptr = site as *const Expr as usize;
                let old_capture_site = self.capture_site;
                self.capture_site = matches!(site.kind, ExprKind::FnValue { .. })
                    .then_some(site as *const Expr as usize);
                let checked = self.expr(body);
                self.capture_site = old_capture_site;
                checked?;
                self.loans = loans;
                if expr.ty.is_view() {
                    let loan = self
                        .borrowed_values
                        .get(&site_ptr)
                        .and_then(|info| info.result_slice.clone())
                        .ok_or_else(|| Diagnostic::new(
                            expr.span,
                            "a borrowed Task.scope result requires checked capture-result provenance",
                        ))?;
                    self.call_views.insert(expr_ptr, loan.clone());
                    self.call_origins.insert(expr_ptr, loan.origins.clone());
                    self.call_splits.insert(expr_ptr, loan.splits.clone());
                } else if self.is_carrier_type(expr.ty) {
                    let provenance = self
                        .borrowed_values
                        .get(&site_ptr)
                        .and_then(|info| info.result_record.clone())
                        .ok_or_else(|| Diagnostic::new(
                            expr.span,
                            "a borrowed-record Task.scope result requires checked capture-result provenance",
                        ))?;
                    self.call_records.insert(expr_ptr, provenance);
                }
            }
            ExprKind::TaskSpawn { body, .. } => {
                let loans = self.loans.clone();
                let site = through_coerce(body);
                let site_ptr = site as *const Expr as usize;
                let lambda = matches!(site.kind, ExprKind::FnValue { .. });
                // One loan per captured view or borrowed record leaf, keeping
                // each split side, so disjoint halves lent to different
                // children stay disjoint.
                let mut lent = Vec::new();
                if let ExprKind::FnValue { captures, .. } = &site.kind {
                    for capture in captures {
                        if capture.ty.is_slice() {
                            lent.push((
                                self.view_origins(capture),
                                capture.ty.is_mut_slice(),
                                self.split_labels(capture),
                                self.view_loan(capture).field,
                            ));
                        } else if self.is_carrier_type(capture.ty) {
                            for loan in self.record_provenance(capture).leaves.values() {
                                lent.push((
                                    loan.origins.clone(),
                                    loan.mutable,
                                    loan.splits.clone(),
                                    loan.field.clone(),
                                ));
                            }
                        }
                    }
                }
                let old_capture_site = self.capture_site;
                self.capture_site = lambda.then_some(site_ptr);
                let checked = self.expr(body);
                self.capture_site = old_capture_site;
                checked?;
                self.loans = loans;
                if let Some(info) = self.borrowed_values.get(&site_ptr).cloned() {
                    // Spawn is legal only lexically in a scope body, so this
                    // function is that body. Its slice and borrowed-record
                    // parameters are values it captured from outside the
                    // scope; their storage outlives the scope's final join.
                    // Its own locals and owned captures die before that join
                    // and cannot be lent to a child.
                    let roots = self.origins_roots(&info.origins);
                    if let Some(root) = roots.iter().find(|root| {
                        **root >= self.parameter_count
                            || !(self.locals[**root].ty.is_slice()
                                || self.is_carrier_type(self.locals[**root].ty))
                    }) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "a spawned task may borrow only slice views or borrowed records that the scope body captured from outside the scope; this storage belongs to the scope body and is freed before the scope joins its children",
                        )
                        .with_note(self.locals[*root].span, "storage owned by the scope body"));
                    }
                    for (origins, mutable, splits, field) in lent {
                        let roots = self.origins_roots(&origins);
                        self.task_regions.push(RetainedView {
                            origins,
                            roots,
                            mutable,
                            splits,
                            field,
                        });
                    }
                    if let Some(provenance) = info.result_record.clone() {
                        // The child returns a borrowed record. Its leaves point
                        // at storage captured from outside the scope, which the
                        // task regions above already keep loaned until the final
                        // join. Carry the same provenance on the handle so the
                        // joined value remains checked after Task.join.
                        self.task_results.insert(expr_ptr, provenance);
                    }
                    self.apply_task_regions();
                }
            }
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => {}
            ExprKind::TaskCancel(reference) => {
                let loans = self.loans.clone();
                self.expr(reference)?;
                self.loans = loans;
            }
            ExprKind::TaskJoin { task, .. } => {
                let loans = self.loans.clone();
                let task_value = through_coerce(task);
                let task_ptr = task_value as *const Expr as usize;
                let task_slot = match &task_value.kind {
                    ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot) => {
                        Some(*slot)
                    }
                    _ => None,
                };
                self.expr(task)?;
                self.loans = loans;
                if let Some(provenance) = task_slot
                    .and_then(|slot| self.task_sources[slot].clone())
                    .or_else(|| self.task_results.get(&task_ptr).cloned())
                {
                    // The joined TaskExit carries the child's borrowed-record
                    // provenance. Whether the result is bound and matched or
                    // matched directly, the ownership pass keeps every loaned
                    // field alive until that value is consumed or dropped.
                    self.wrapped_results.insert(expr_ptr, provenance);
                }
            }
            ExprKind::FnValue { captures, .. } => {
                // A borrowed-capture closure is a scoped lexical capability.
                // It is legal only as a direct `let` initializer or as the
                // immediate callee of an indirect call; both positions are
                // marked by the enclosing statement. Captured slice views and
                // borrowed records are both inert descriptors: the environment
                // never owns the storage behind them.
                let borrowed = captures
                    .iter()
                    .filter(|capture| capture.ty.is_slice())
                    .collect::<Vec<_>>();
                let records = captures
                    .iter()
                    .filter(|capture| self.is_carrier_type(capture.ty))
                    .collect::<Vec<_>>();
                if !borrowed.is_empty() || !records.is_empty() {
                    if self.capture_site != Some(expr_ptr) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "a lambda with borrowed captures must be called immediately or bound directly to a local; it cannot escape through a return, aggregate, box, union, generic call, adapter, or task",
                        ));
                    }
                    let mut origins = BTreeSet::new();
                    let mut splits: Option<SplitLabels> = None;
                    let mut mutable = false;
                    for capture in &borrowed {
                        let capture_origins = self.view_origins(capture);
                        let labels = self.split_labels(capture);
                        let capture_mut = capture.ty.is_mut_slice();
                        let capture_field = self.view_loan(capture).field;
                        self.check_view_creation(
                            &capture_origins,
                            capture_mut,
                            &labels,
                            capture_field.as_ref(),
                            expr_ptr,
                            capture.span,
                        )?;
                        mutable |= capture_mut;
                        origins.extend(capture_origins);
                        splits = Some(match splits {
                            Some(mut current) => {
                                current.0.retain(|group, left| {
                                    labels
                                        .0
                                        .get(group)
                                        .is_some_and(|other_left| other_left == left)
                                });
                                current
                            }
                            None => labels,
                        });
                    }
                    for capture in &records {
                        let provenance = self.record_provenance(capture);
                        for loan in provenance.leaves.values() {
                            mutable |= loan.mutable;
                            origins.extend(loan.origins.iter().copied());
                            splits = Some(match splits {
                                Some(current) => intersect_splits(&current, &loan.splits),
                                None => loan.splits.clone(),
                            });
                        }
                    }
                    let mut info = BorrowedCapture {
                        origins,
                        mutable,
                        splits: splits.unwrap_or_default(),
                        result_slice: None,
                        result_record: None,
                    };
                    let capture_result = match expr.ty {
                        Type::Fn(id) | Type::Once(id) => {
                            self.functions[id].borrows.capture_result.clone()
                        }
                        _ => None,
                    };
                    if let Some(result) = capture_result {
                        if let Some(slice) = result.slice {
                            let capture = &captures[slice.capture];
                            let loan = match &slice.path {
                                Some(path) => {
                                    self.record_provenance(capture).leaves.get(path).cloned()
                                }
                                None => Some(self.view_loan(capture)),
                            };
                            let Some(loan) = loan else {
                                return Err(Diagnostic::new(
                                    expr.span,
                                    "internal error: scoped closure result capture has no borrowed provenance",
                                ));
                            };
                            if loan.mutable != slice.mutable {
                                return Err(Diagnostic::new(
                                    expr.span,
                                    "internal error: scoped closure result capture mutability disagrees with its contract",
                                ));
                            }
                            info.result_slice = Some(loan);
                        }
                        let mut provenance = RecordProvenance::default();
                        for leaf in &result.leaves {
                            let capture = &captures[leaf.capture];
                            let loan = if capture.ty.is_slice() {
                                Some(self.view_loan(capture))
                            } else {
                                self.record_provenance(capture)
                                    .leaves
                                    .get(&leaf.path)
                                    .cloned()
                            };
                            let Some(loan) = loan else {
                                return Err(Diagnostic::new(
                                    expr.span,
                                    "internal error: scoped closure result field has no captured provenance",
                                ));
                            };
                            if loan.mutable != leaf.mutable {
                                return Err(Diagnostic::new(
                                    expr.span,
                                    "internal error: scoped closure result field mutability disagrees with its captured record",
                                ));
                            }
                            provenance.leaves.insert(leaf.path.clone(), loan);
                        }
                        if !provenance.leaves.is_empty() {
                            info.result_record = Some(provenance);
                        }
                    }
                    self.borrowed_values.insert(expr_ptr, info);
                }
                if captures.iter().any(|c| self.value_moves_linear(c))
                    && !is_linear(
                        expr.ty,
                        self.linear,
                        self.unions,
                        self.pointees,
                        self.functions,
                    )
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "closure must preserve captured linear obligations in a linear-once type",
                    ));
                }
                for capture in captures {
                    self.expr(capture)?;
                }
            }
            ExprKind::DynArrayNew { .. } => {}
            ExprKind::DynArrayPush { array, value, .. } => {
                // The array is consumed and returned in the same inline
                // storage; the element is evaluated only after the array.
                self.expr(array)?;
                self.expr(value)?;
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                self.expr(array)?;
                self.expr(index)?;
                self.expr(value)?;
            }
            ExprKind::DynArrayPop { array, .. } => self.expr(array)?,
            ExprKind::HandlerPush { handler, body, .. } => {
                self.expr(handler)?;
                self.block(body)?;
            }
            ExprKind::DynamicPerform {
                payload, resume, ..
            } => {
                self.expr(payload)?;
                self.expr(resume)?;
            }
            ExprKind::Construct {
                enum_id,
                fields,
                tag: _,
            } => {
                for field in fields.iter_mut() {
                    // Each field's own `expr` end retains its borrowed leaves,
                    // so earlier fields protect their owners while later
                    // fields are evaluated and may return or `?` early.
                    self.expr(field)?;
                }
                if self.enums[*enum_id].record {
                    let provenance = self.construct_record_provenance(*enum_id, fields)?;
                    self.construct_records.insert(expr_ptr, provenance);
                }
            }
            ExprKind::If(condition, yes, no) => {
                self.expr(condition)?;
                let before = self.available.clone();
                let loans = self.loans.clone();
                self.block(yes)?;
                let yes_state = self.available.clone();
                let yes_loans = self.loans.clone();
                self.available = before;
                self.loans = loans.clone();
                self.temporary_shared = temporary_shared.clone();
                self.temporary_exclusive = temporary_exclusive.clone();
                self.temporary_regions = temporary_regions.clone();
                self.pending_linear.truncate(pending_linear);
                self.block(no)?;
                if yes.ty != Type::Never {
                    if no.ty == Type::Never {
                        self.available = yes_state;
                    } else {
                        self.merge(&yes_state, expr.span)?;
                    }
                }
                self.loans.extend(yes_loans);
                self.loans.extend(loans);
            }
            ExprKind::Match(value, arms) => {
                // `@[1]` on an owning value is also a linear obligation, even
                // though the underlying type is merely affine.
                let entry_scrutinee_loans = self.loans.clone();
                let scrutinee_linear = self.value_moves_linear(value);
                let wrapped_site = through_coerce(value) as *const Expr as usize;
                let wrapped_slot = match &through_coerce(value).kind {
                    ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot) => {
                        Some(*slot)
                    }
                    _ => None,
                };
                let wrapped_before = self
                    .wrapped_results
                    .get(&wrapped_site)
                    .cloned()
                    .or_else(|| wrapped_slot.and_then(|slot| self.wrapped_locals[slot].clone()));
                self.expr(value)?;
                let wrapped = self
                    .wrapped_results
                    .get(&wrapped_site)
                    .cloned()
                    .or(wrapped_before)
                    .or_else(|| {
                        self.is_task_exit(value.ty)
                            .then(|| self.record_provenance(value))
                    });
                // Pattern bindings now hold the scrutinee's obligations.
                self.pending_linear.truncate(pending_linear);
                let scrutinee = value.ty;
                let scrutinee_provenance = self
                    .is_carrier_type(scrutinee)
                    .then(|| self.record_provenance(value));
                let before = self.available.clone();
                // A shared record's descriptors have now transferred to
                // pattern bindings. Their NLL liveness keeps the relevant
                // owners loaned; retaining the temporary scrutinee loan for
                // the entire arm would defeat last-use release, especially
                // when a destructuring let lowers the rest of the block here.
                let loans = if scrutinee_provenance.is_some() {
                    entry_scrutinee_loans
                } else {
                    self.loans.clone()
                };
                let mut joined: Option<Vec<bool>> = None;
                let mut result_loans = loans.clone();
                for arm in arms {
                    self.pending_linear.truncate(pending_linear);
                    self.temporary_shared = temporary_shared.clone();
                    self.temporary_exclusive = temporary_exclusive.clone();
                    self.temporary_regions = temporary_regions.clone();
                    self.available = before.clone();
                    self.loans = loans.clone();
                    self.ignored_linear(&arm.pattern, scrutinee, expr.span, scrutinee_linear)?;
                    if let Some(provenance) = &scrutinee_provenance {
                        self.bind_pattern_provenance(&arm.pattern, scrutinee, provenance)?;
                    }
                    if let Some(provenance) = &wrapped {
                        self.bind_task_exit_provenance(&arm.pattern, scrutinee, provenance)?;
                    }
                    let mut bindings = BTreeSet::new();
                    pattern_bindings(&arm.pattern, &mut bindings);
                    for slot in &bindings {
                        if scrutinee_linear && self.moves(self.locals[*slot].ty) {
                            self.locals[*slot].linear = true;
                        }
                        self.available[*slot] = true;
                        self.moved_at[*slot] = None;
                        self.bound(*slot);
                    }
                    if let Some(guard) = &mut arm.guard {
                        let old_guard = self.guard;
                        self.guard = true;
                        let result = self.full(guard);
                        self.guard = old_guard;
                        result?;
                    }
                    self.expr(&mut arm.body)?;
                    if arm.body.ty != Type::Never {
                        if arm.body.ty.is_slice()
                            || arm.body.ty.is_ref()
                            || self.is_carrier_type(arm.body.ty)
                        {
                            let origins = if arm.body.ty.is_slice() || arm.body.ty.is_ref() {
                                self.view_origins(&arm.body)
                            } else {
                                let provenance = self.record_provenance(&arm.body);
                                provenance
                                    .leaves
                                    .values()
                                    .flat_map(|loan| loan.origins.iter().copied())
                                    .collect()
                            };
                            if let Some(owner) = bindings
                                .iter()
                                .find(|slot| origins.contains(slot) && !self.is_local_view(**slot))
                            {
                                return Err(Diagnostic::new(
                                    arm.body.span,
                                    if arm.body.ty.is_slice() {
                                        "slice view would outlive the lexical scope of its owner"
                                    } else if arm.body.ty.is_ref() {
                                        "reference escapes the lexical scope of the storage it borrows"
                                    } else {
                                        "borrowed record would outlive the lexical scope of its owner"
                                    },
                                )
                                .with_note(self.locals[*owner].span, "owner declared here"));
                            }
                        }
                        self.exit_check(
                            bindings.iter().copied(),
                            arm.body.span,
                            "the end of this match arm",
                        )?;
                    }
                    for slot in bindings {
                        if self.loans.contains(&slot) && !self.is_local_view(slot) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "borrow escapes a match binding's scope",
                            ));
                        }
                        self.available[slot] = false;
                    }
                    result_loans.extend(self.loans.iter().copied());
                    if arm.body.ty != Type::Never {
                        if let Some(joined) = &mut joined {
                            let current = self.available.clone();
                            self.available = joined.clone();
                            self.merge(&current, arm.body.span)?;
                            *joined = self.available.clone();
                        } else {
                            joined = Some(self.available.clone());
                        }
                    }
                }
                self.available = joined.unwrap_or(before);
                self.loans = result_loans;
            }
            ExprKind::While(condition, body) => {
                self.enter_loop();
                self.expr(condition)?;
                let after_condition = self.available.clone();
                self.block(body)?;
                if body.ty != Type::Never {
                    self.loop_end(expr.span, "in the loop body")?;
                }
                let state = self.loops.pop().unwrap();
                self.available = after_condition;
                if let Some(breaks) = state.breaks {
                    self.merge(&breaks, expr.span)?;
                }
            }
            ExprKind::Loop(body) => {
                self.enter_loop();
                self.block(body)?;
                if body.ty != Type::Never {
                    self.loop_end(expr.span, "in the loop body")?;
                }
                let state = self.loops.pop().unwrap();
                if let Some(breaks) = state.breaks {
                    self.available = breaks;
                } else {
                    self.available = state.entry;
                }
            }
            ExprKind::Break(value, cleanup) => {
                self.check_pending_linear(
                    self.loops.last().unwrap().pending_linear_start,
                    expr.span,
                )?;
                if let Some(value) = value {
                    self.expr(value)?;
                }
                let bound = self.loops.last().unwrap().bound.clone();
                self.exit_check(bound, expr.span, "leaving the loop")?;
                *cleanup = self.cleanup_list();
                if let Some(previous) = self.loops.last().unwrap().breaks.clone() {
                    self.merge(&previous, expr.span)?;
                }
                self.loops.last_mut().unwrap().breaks = Some(self.available.clone());
            }
            ExprKind::Continue(cleanup) => {
                self.check_pending_linear(
                    self.loops.last().unwrap().pending_linear_start,
                    expr.span,
                )?;
                let bound = self.loops.last().unwrap().bound.clone();
                self.exit_check(bound, expr.span, "continuing the loop")?;
                self.loop_end(expr.span, "before 'continue'")?;
                *cleanup = self.cleanup_list();
            }
            ExprKind::Slice {
                base,
                start,
                end,
                split,
                ..
            } => {
                let origins = self.view_origins(base);
                let mutable = expr.ty.is_mut_slice();
                if mutable && base.ty.is_slice() && !base.ty.is_mut_slice() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot create an exclusive '&mut [T]' view from a shared '&[T]' view; shared views cannot be upgraded",
                    )
                    .with_note(base.span, "shared view created here"));
                }
                let base_splits = self.split_labels(base);
                let reservation_splits = base_splits.clone();
                let splits = match split {
                    Some((group, left)) => base_splits.with(*group, *left),
                    None => base_splits,
                };
                let base_field = match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                        if base.ty.is_view() =>
                    {
                        self.view_fields[*slot].clone()
                    }
                    _ => self.projection_field(base),
                };
                self.check_view_creation(
                    &origins,
                    mutable,
                    &splits,
                    base_field.as_ref(),
                    expr_ptr,
                    expr.span,
                )?;
                let view_base = match &base.kind {
                    ExprKind::Local(slot) if self.locals[*slot].ty.is_view() => Some(*slot),
                    _ => None,
                };
                if let Some(slot) = view_base {
                    if !self.available[slot] {
                        return Err(self.use_after_move(
                            slot,
                            base.span,
                            "cannot sub-slice a moved or consumed view",
                        ));
                    }
                    // Sub-slicing reborrows the parent capability instead of
                    // consuming it. Reserve the ancestry while the bounds
                    // evaluate so they cannot move the parent or its owner.
                    if mutable {
                        self.temporary_exclusive.extend(origins.iter().copied());
                    } else {
                        self.temporary_shared.extend(origins.iter().copied());
                    }
                    self.bound_receivers.insert(slot);
                    let roots = self.origins_roots(&origins);
                    self.temporary_regions.push(RetainedView {
                        origins: origins.clone(),
                        roots,
                        mutable,
                        splits: reservation_splits,
                        field: base_field,
                    });
                } else {
                    // A record-field projection is a place used to derive the
                    // child capability. It must not retain a second, competing
                    // view; the Slice expression below retains the child.
                    let old = self.in_field_subview;
                    self.in_field_subview = matches!(base.kind, ExprKind::Project(..));
                    let checked = self.expr(base);
                    self.in_field_subview = old;
                    checked?;
                    // A view of an inline array needs stable storage while the
                    // bounds are evaluated and the view is used.
                    if let ExprKind::Peek(slot) = &base.kind
                        && base
                            .ty
                            .layout()
                            .is_some_and(|id| self.enums[id].array.is_some())
                    {
                        self.loans.insert(*slot);
                    }
                }
                if let Some(start) = start {
                    self.expr(start)?;
                }
                if let Some(end) = end {
                    self.expr(end)?;
                }
            }
            _ => {}
        }
        self.temporary_shared = temporary_shared;
        self.temporary_exclusive = temporary_exclusive;
        self.temporary_regions = temporary_regions;
        self.reborrowed_views = reborrowed_views;
        self.bound_receivers = bound_receivers;
        self.apply_task_regions();
        self.hold_view(expr)?;
        self.hold_record(expr)?;
        self.pending_linear.truncate(pending_linear);
        if expr.ty != Type::Never
            && (is_linear(
                expr.ty,
                self.linear,
                self.unions,
                self.pointees,
                self.functions,
            ) || self.value_moves_linear(expr))
        {
            self.pending_linear.push(expr.span);
        }
        // A place read observes storage still owned by its original local.
        // Registering it as a temporary owner would free the same payload
        // twice. Nested projections remain place reads until an actual move.
        if owns(expr.ty, self.owned, self.unions, self.pointees) && !is_place_read(expr) {
            expr.resource = Some(self.resource(expr.ty, expr.span)?);
        }
        Ok(())
    }
    /// Join two control-flow states. Linear values must agree on both paths.
    fn merge(&mut self, other: &[bool], span: Span) -> Result<()> {
        for (slot, &available) in other.iter().enumerate().take(self.available.len()) {
            if self.available[slot] != available && self.slot_linear(slot) {
                return Err(Diagnostic::new(
                    span,
                    "a linear value is consumed on one branch but not the other",
                )
                .with_note(self.locals[slot].span, "linear value bound here"));
            }
            self.available[slot] &= available;
        }
        Ok(())
    }
    /// Wildcards and omitted record fields drop their part of the value.
    fn ignored_linear(
        &self,
        pattern: &Pattern,
        ty: Type,
        span: Span,
        whole_linear: bool,
    ) -> Result<()> {
        if self.ignores_linear(pattern, ty, whole_linear) {
            return Err(Diagnostic::new(
                span,
                "this pattern ignores a linear value (wildcard or omitted field); bind and consume it",
            ));
        }
        Ok(())
    }
    fn ignores_linear(&self, pattern: &Pattern, ty: Type, whole_linear: bool) -> bool {
        match pattern {
            Pattern::Any => {
                whole_linear
                    || is_linear(ty, self.linear, self.unions, self.pointees, self.functions)
            }
            Pattern::Or(ps) => ps.iter().any(|p| self.ignores_linear(p, ty, whole_linear)),
            Pattern::Variant { tag, fields } => ty.layout().is_some_and(|id| {
                fields
                    .iter()
                    .zip(&self.enums[id].variants[*tag].fields)
                    .any(|((_, p), t)| self.ignores_linear(p, *t, whole_linear))
            }),
            Pattern::Type { member, inner, .. } => {
                self.ignores_linear(inner, *member, whole_linear)
            }
            _ => false,
        }
    }
}
fn through_coerce(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Coerce { value, .. } => through_coerce(value),
        _ => expr,
    }
}
fn block_span(block: &Block) -> Span {
    block
        .tail
        .as_ref()
        .map(|t| t.span)
        .or_else(|| {
            block.statements.last().map(|s| match s {
                Statement::Let(_, e) | Statement::Expr(e) => e.span,
            })
        })
        .unwrap_or_default()
}
pub(crate) fn pattern_bindings(pattern: &Pattern, slots: &mut BTreeSet<usize>) {
    match pattern {
        Pattern::Bind(slot) => {
            slots.insert(*slot);
        }
        Pattern::Variant { fields, .. } => {
            for (_, p) in fields {
                pattern_bindings(p, slots);
            }
        }
        Pattern::Type { inner, .. } => pattern_bindings(inner, slots),
        Pattern::Or(ps) => {
            for p in ps {
                pattern_bindings(p, slots);
            }
        }
        _ => {}
    }
}

/// Values returned by breaks targeting this loop, excluding nested loops.
/// Traverse all expression positions because a break can occur in an argument.
pub(crate) fn loop_break_values(block: &Block) -> Vec<&Expr> {
    fn walk_block<'a>(block: &'a Block, out: &mut Vec<&'a Expr>) {
        for statement in &block.statements {
            let (Statement::Let(_, e) | Statement::Expr(e)) = statement;
            walk(e, out);
        }
        if let Some(e) = &block.tail {
            walk(e, out);
        }
    }
    fn walk<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
        match &expr.kind {
            ExprKind::Break(Some(value), _) => out.push(value),
            ExprKind::Loop(_) | ExprKind::While(_, _) => {}
            ExprKind::Block(b) => walk_block(b, out),
            ExprKind::If(c, a, b) => {
                walk(c, out);
                walk_block(a, out);
                walk_block(b, out);
            }
            ExprKind::Match(v, arms) => {
                walk(v, out);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        walk(g, out);
                    }
                    walk(&arm.body, out);
                }
            }
            ExprKind::Construct { fields, .. } | ExprKind::Call(_, fields) => {
                for field in fields {
                    walk(field, out);
                }
            }
            ExprKind::DynArrayNew { .. } => {}
            ExprKind::DynArrayPush { array, value, .. } => {
                walk(array, out);
                walk(value, out);
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                walk(array, out);
                walk(index, out);
                walk(value, out);
            }
            ExprKind::DynArrayPop { array, .. } => walk(array, out),
            ExprKind::HandlerPush { handler, body, .. } => {
                walk(handler, out);
                walk_block(body, out);
            }
            ExprKind::DynamicPerform {
                payload, resume, ..
            } => {
                walk(payload, out);
                walk(resume, out);
            }
            ExprKind::FnValue { captures, .. } => {
                for capture in captures {
                    walk(capture, out);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                walk(callee, out);
                for arg in arguments {
                    walk(arg, out);
                }
            }
            ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                walk(body, out);
            }
            ExprKind::TaskCancel(reference) => walk(reference, out),
            ExprKind::TaskJoin { task, .. } => walk(task, out),
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => {}
            ExprKind::Unary(_, v)
            | ExprKind::Assign(_, v)
            | ExprKind::Return(v)
            | ExprKind::BoxNew(v)
            | ExprKind::BoxRead(v)
            | ExprKind::BoxTake(v)
            | ExprKind::BoxTryNew { value: v, .. }
            | ExprKind::BytesTryWithCapacity { capacity: v, .. }
            | ExprKind::ArenaBoxRead(v)
            | ExprKind::ArenaBoxTake(v)
            | ExprKind::Drop(v)
            | ExprKind::Project(v, _)
            | ExprKind::Try { value: v, .. }
            | ExprKind::Coerce { value: v, .. } => walk(v, out),
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            } => {
                walk(owner, out);
                walk(payload, out);
            }
            ExprKind::ArenaNew => {}
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                walk(vector, out);
                for callback in callbacks {
                    walk(callback, out);
                }
            }
            ExprKind::Binary(_, a, b) | ExprKind::BytesAt(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            ExprKind::RefAssign(reference, _, value) => {
                walk(reference, out);
                walk(value, out);
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                walk(base, out);
                if let Some(v) = start {
                    walk(v, out);
                }
                if let Some(v) = end {
                    walk(v, out);
                }
            }
            _ => {}
        }
    }
    let mut values = Vec::new();
    walk_block(block, &mut values);
    values
}

/// Backward liveness of slice-view locals, with fixed points at loops. This
/// is a checked IR analysis: a textual last occurrence inside a loop does not
/// end a loan while a later iteration can still use the view.
fn loan_liveness(
    function: &Function,
    enums: &[crate::runtime_types::Enum],
    pointees: &[Type],
) -> BTreeMap<usize, BTreeSet<usize>> {
    let views = function
        .locals
        .iter()
        .enumerate()
        .filter_map(|(slot, local)| {
            (local.ty.is_view()
                || local.ty.is_ref()
                || matches!(local.ty, Type::Once(_))
                || local.ty.layout().is_some_and(|id| enums[id].borrowed)
                || container_carries_borrow(pointees, local.ty))
            .then_some(slot)
        })
        .collect::<BTreeSet<_>>();
    let mut out = BTreeMap::new();
    let mut heads = Vec::new();
    let mut exits = Vec::new();
    block_live(
        &function.body,
        &BTreeSet::new(),
        &views,
        &mut heads,
        &mut exits,
        &mut out,
    );
    out
}
type Live = BTreeSet<usize>;
fn ptr(expr: &Expr) -> usize {
    expr as *const Expr as usize
}
fn add_use(live: &mut Live, slot: usize, views: &BTreeSet<usize>) {
    if views.contains(&slot) {
        live.insert(slot);
    }
}
fn block_live(
    block: &Block,
    live_after: &Live,
    views: &BTreeSet<usize>,
    heads: &mut Vec<Live>,
    exits: &mut Vec<Live>,
    out: &mut BTreeMap<usize, Live>,
) -> Live {
    let mut live = live_after.clone();
    if let Some(tail) = &block.tail {
        live = expr_live(tail, &live, views, heads, exits, out);
    }
    for statement in block.statements.iter().rev() {
        match statement {
            Statement::Let(slot, expr) => {
                let mut after = live.clone();
                add_use(&mut after, *slot, views);
                live = expr_live(expr, &after, views, heads, exits, out);
                live.remove(slot);
            }
            Statement::Expr(expr) => {
                live = expr_live(expr, &live, views, heads, exits, out);
            }
        }
    }
    live
}
fn expr_live(
    expr: &Expr,
    live_after: &Live,
    views: &BTreeSet<usize>,
    heads: &mut Vec<Live>,
    exits: &mut Vec<Live>,
    out: &mut BTreeMap<usize, Live>,
) -> Live {
    let mut live = live_after.clone();
    match &expr.kind {
        ExprKind::Local(slot)
        | ExprKind::Peek(slot)
        | ExprKind::Borrow(slot)
        | ExprKind::Move(slot) => add_use(&mut live, *slot, views),
        ExprKind::Erased(_) => {}
        ExprKind::Assign(slot, value) => {
            let mut after = live.clone();
            after.remove(slot);
            live = expr_live(value, &after, views, heads, exits, out);
            live.remove(slot);
        }
        ExprKind::RefAssign(reference, _, value) | ExprKind::RefWrite(reference, value) => {
            live = expr_live(reference, &live, views, heads, exits, out);
            live = expr_live(value, &live, views, heads, exits, out);
        }
        ExprKind::RefRead(reference) => {
            live = expr_live(reference, &live, views, heads, exits, out);
        }
        ExprKind::Unary(_, value)
        | ExprKind::BoxNew(value)
        | ExprKind::BoxTake(value)
        | ExprKind::BoxRead(value)
        | ExprKind::BoxTryNew { value, .. }
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::ArenaBoxRead(value)
        | ExprKind::ArenaBoxTake(value)
        | ExprKind::Drop(value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _)
        | ExprKind::Coerce { value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::Try { value, .. } => {
            // The success path continues; the error path returns. Keep the
            // continuation live to be conservative about loan lifetimes.
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::BoxReuse { owner, payload }
        | ExprKind::BoxReuseGrow { owner, payload }
        | ExprKind::BoxTryReuse { owner, payload, .. }
        | ExprKind::ArenaAlloc {
            arena: owner,
            value: payload,
        } => {
            live = expr_live(payload, live_after, views, heads, exits, out);
            live = expr_live(owner, &live, views, heads, exits, out);
        }
        ExprKind::ArenaNew => {}
        ExprKind::DynArrayNew { .. } => {}
        ExprKind::DynArrayPush { array, value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
            live = expr_live(array, &live, views, heads, exits, out);
        }
        ExprKind::DynArraySet {
            array,
            index,
            value,
            ..
        } => {
            live = expr_live(value, live_after, views, heads, exits, out);
            live = expr_live(index, &live, views, heads, exits, out);
            live = expr_live(array, &live, views, heads, exits, out);
        }
        ExprKind::DynArrayPop { array, .. } => {
            live = expr_live(array, live_after, views, heads, exits, out);
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            live = block_live(body, live_after, views, heads, exits, out);
            live = expr_live(handler, &live, views, heads, exits, out);
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            live = expr_live(resume, live_after, views, heads, exits, out);
            live = expr_live(payload, &live, views, heads, exits, out);
        }
        ExprKind::Binary(_, left, right) | ExprKind::BytesAt(left, right) => {
            live = expr_live(right, live_after, views, heads, exits, out);
            live = expr_live(left, &live, views, heads, exits, out);
        }
        ExprKind::Call(_, arguments) => {
            for argument in arguments.iter().rev() {
                live = expr_live(argument, &live, views, heads, exits, out);
            }
        }
        ExprKind::CallIndirect { callee, arguments } => {
            for argument in arguments.iter().rev() {
                live = expr_live(argument, &live, views, heads, exits, out);
            }
            live = expr_live(callee, &live, views, heads, exits, out);
        }
        ExprKind::Construct { fields, .. } => {
            for field in fields.iter().rev() {
                live = expr_live(field, &live, views, heads, exits, out);
            }
        }
        ExprKind::VecMap {
            vector, callbacks, ..
        } => {
            for callback in callbacks.iter().rev() {
                live = expr_live(callback, &live, views, heads, exits, out);
            }
            live = expr_live(vector, &live, views, heads, exits, out);
        }
        ExprKind::FnValue { captures, .. } => {
            for capture in captures.iter().rev() {
                live = expr_live(capture, &live, views, heads, exits, out);
            }
        }
        ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
            live = expr_live(body, live_after, views, heads, exits, out);
        }
        ExprKind::TaskCancel(reference) => {
            live = expr_live(reference, live_after, views, heads, exits, out);
        }
        ExprKind::TaskJoin { task, .. } => {
            live = expr_live(task, live_after, views, heads, exits, out);
        }
        ExprKind::TaskYield
        | ExprKind::TaskCheckCancel
        | ExprKind::Constant(_)
        | ExprKind::BytesLiteral(_) => {}
        ExprKind::Block(block) => {
            live = block_live(block, live_after, views, heads, exits, out);
        }
        ExprKind::If(condition, yes, no) => {
            let yes_live = block_live(yes, live_after, views, heads, exits, out);
            let no_live = block_live(no, live_after, views, heads, exits, out);
            let mut branches = yes_live;
            branches.extend(no_live);
            live = expr_live(condition, &branches, views, heads, exits, out);
        }
        ExprKind::Match(value, arms) => {
            let mut all = Live::new();
            for arm in arms {
                let mut after = live_after.clone();
                let mut bindings = BTreeSet::new();
                pattern_bindings(&arm.pattern, &mut bindings);
                for slot in bindings {
                    after.remove(&slot);
                }
                let mut arm_live = if arm.body.ty == Type::Never {
                    Live::new()
                } else {
                    expr_live(&arm.body, &after, views, heads, exits, out)
                };
                if let Some(guard) = &arm.guard {
                    arm_live = expr_live(guard, &arm_live, views, heads, exits, out);
                }
                all.extend(arm_live);
            }
            live = expr_live(value, &all, views, heads, exits, out);
        }
        ExprKind::While(condition, body) => {
            exits.push(live_after.clone());
            let mut head = live_after.clone();
            loop {
                heads.push(head.clone());
                let before_condition = expr_live(condition, &head, views, heads, exits, out);
                let before_body = block_live(body, &head, views, heads, exits, out);
                heads.pop();
                let mut next = before_condition;
                next.extend(before_body);
                if next == head {
                    break;
                }
                head = next;
            }
            // Record the final fixed point on every node.
            heads.push(head.clone());
            let before_condition = expr_live(condition, &head, views, heads, exits, out);
            let before_body = block_live(body, &head, views, heads, exits, out);
            heads.pop();
            exits.pop();
            live = before_condition;
            live.extend(before_body);
        }
        ExprKind::Loop(body) => {
            exits.push(live_after.clone());
            let mut head = live_after.clone();
            loop {
                heads.push(head.clone());
                let before_body = block_live(body, &head, views, heads, exits, out);
                heads.pop();
                let mut next = before_body.clone();
                next.extend(live_after.iter().copied());
                if next == head {
                    break;
                }
                head = next;
            }
            heads.push(head.clone());
            let before_body = block_live(body, &head, views, heads, exits, out);
            heads.pop();
            exits.pop();
            live = before_body;
        }
        ExprKind::Break(value, _) => {
            if let Some(value) = value {
                live = expr_live(value, &Live::new(), views, heads, exits, out);
            } else {
                live = Live::new();
            }
            if let Some(exit) = exits.last() {
                live.extend(exit.iter().copied());
            }
        }
        ExprKind::Continue(_) => {
            live = heads.last().cloned().unwrap_or_default();
        }
        ExprKind::Slice {
            base, start, end, ..
        } => {
            if let Some(end) = end {
                live = expr_live(end, &live, views, heads, exits, out);
            }
            if let Some(start) = start {
                live = expr_live(start, &live, views, heads, exits, out);
            }
            live = expr_live(base, &live, views, heads, exits, out);
        }
    }
    out.insert(ptr(expr), live.clone());
    live
}
