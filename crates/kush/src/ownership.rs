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
    executable::{Block, Coercion, Executable, Expr, ExprKind, Function, Pattern, Statement, Type},
    grades::Grade,
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, Diagnostic>;
/// Call-leaf path prefix marking an element inside a container reached through
/// a reference parameter. It is checker-only and never names a record field.
use crate::runtime_types::CONTAINER_LEAF;
pub(crate) fn check(program: &mut Executable) -> Result<()> {
    let mut owned = vec![false; program.enums.len()];
    let mut linear = program.enums.iter().map(|e| e.linear).collect::<Vec<_>>();
    // Layout and dynamic-object linearity feed each other: a record may hold
    // a dynamic object whose member is linear, and a member may be a record
    // holding another object. Solve both in one fixed point.
    let mut dyn_linear = vec![false; program.dyn_members.len()];
    loop {
        let (old_owned, old_linear, old_dyn) = (owned.clone(), linear.clone(), dyn_linear.clone());
        for (index, layout) in program.enums.iter().enumerate() {
            let fields = || layout.variants.iter().flat_map(|v| v.fields.iter());
            owned[index] = layout.foreign.is_some()
                || fields().any(|ty| owns(*ty, &old_owned, &program.unions, &program.pointees));
            linear[index] |= fields().any(|ty| {
                is_linear(
                    *ty,
                    &old_linear,
                    &program.unions,
                    &program.pointees,
                    &program.function_types,
                    &old_dyn,
                )
            });
        }
        for (index, members) in program.dyn_members.iter().enumerate() {
            dyn_linear[index] |= members.iter().any(|member| {
                is_linear(
                    member.member,
                    &old_linear,
                    &program.unions,
                    &program.pointees,
                    &program.function_types,
                    &old_dyn,
                )
            });
        }
        if owned == old_owned && linear == old_linear && dyn_linear == old_dyn {
            break;
        }
    }
    for pointee in &program.pointees {
        if let Type::Vec(p) | Type::AllocVec(p) = pointee
            && is_linear(
                program.pointees[*p],
                &linear,
                &program.unions,
                &program.pointees,
                &program.function_types,
                &dyn_linear,
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
        .map(|function| -> Result<CallLifetime> {
            let mut parameters = Vec::with_capacity(function.parameters);
            for (index, local) in function.locals.iter().take(function.parameters).enumerate() {
                if local.ty.is_view() {
                    parameters.push(vec![crate::runtime_types::BorrowLeaf {
                        path: vec![],
                        lifetime: function.parameter_lifetimes.get(index).cloned().flatten(),
                        mutable: local.ty.is_mut_slice(),
                        variance: crate::variance::SignSet::POSITIVE,
                    }]);
                } else if local.ty.is_ref() {
                    let mut leaves = vec![crate::runtime_types::BorrowLeaf {
                        path: vec![],
                        lifetime: function.parameter_lifetimes.get(index).cloned().flatten(),
                        mutable: matches!(local.ty, Type::RefMut(_)),
                        variance: crate::variance::SignSet::POSITIVE,
                    }];
                    // A reference to a container exposes its element leaves as
                    // well, so a call that mutates the caller's container can
                    // relate every written reference to the declared element
                    // lifetime.
                    // A reference to a record with borrowed fields exposes
                    // its leaves the same way: through `&mut` the callee may
                    // replace the whole record, and through `&` it may copy a
                    // leaf into another written destination.
                    if let Some(container) =
                        referent_of(&program.pointees, local.ty).filter(|container| {
                            container_carries_borrow(&program.enums, &program.pointees, *container)
                                || container
                                    .layout()
                                    .is_some_and(|id| program.enums[id].borrowed)
                        })
                    {
                        for leaf in leaves_of(
                            &program.enums,
                            &program.pointees,
                            &program.reference_labels,
                            &program.variance,
                            container,
                        )? {
                            let mut path = vec![CONTAINER_LEAF];
                            path.extend(leaf.path);
                            leaves.push(crate::runtime_types::BorrowLeaf {
                                path,
                                lifetime: leaf.lifetime,
                                mutable: leaf.mutable,
                                variance: leaf.variance.compose(
                                    if matches!(local.ty, Type::RefMut(_)) {
                                        crate::variance::SignSet::INVARIANT
                                    } else {
                                        crate::variance::SignSet::POSITIVE
                                    },
                                ),
                            });
                        }
                    }
                    parameters.push(leaves);
                } else {
                    parameters.push(leaves_of(
                        &program.enums,
                        &program.pointees,
                        &program.reference_labels,
                        &program.variance,
                        local.ty,
                    )?);
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
                || container_carries_borrow(&program.enums, &program.pointees, function.result)
            {
                CallResult::Record(leaves_of(
                    &program.enums,
                    &program.pointees,
                    &program.reference_labels,
                    &program.variance,
                    function.result,
                )?)
            } else {
                CallResult::None
            };
            Ok(CallLifetime {
                parameters,
                result,
                bounds: function.lifetime_bounds.clone(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    // Dynamic dispatch uses the checked member function as its lifetime
    // witness. Object safety and exact impl contracts guarantee that every
    // member of one specialization has the same alpha-equivalent borrow
    // contract, so any registered member supplies the same result provenance.
    let empty_call = CallLifetime {
        parameters: Vec::new(),
        result: CallResult::None,
        bounds: BTreeSet::new(),
    };
    let dyn_call_lifetimes = program
        .dyn_calls
        .iter()
        .map(|spec| {
            program
                .dyn_members
                .get(spec.object)
                .and_then(|members| members.first())
                .and_then(|member| member.methods.get(&spec.key))
                .and_then(|function| calls.get(*function))
                .cloned()
                .unwrap_or_else(|| empty_call.clone())
        })
        .collect::<Vec<_>>();
    let union_call_lifetimes = program
        .union_calls
        .iter()
        .map(|spec| {
            spec.members
                .first()
                .and_then(|(_, _, function)| calls.get(*function))
                .cloned()
                .unwrap_or_else(|| empty_call.clone())
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
                        &dyn_linear,
                    ),
                )
            })
        })
        .collect::<Vec<_>>();
    let capture_refs = program
        .functions
        .iter()
        .map(|function| function.capture_refs.clone())
        .collect::<Vec<_>>();
    let capture_writes = program
        .functions
        .iter()
        .map(|function| function.capture_writes.clone())
        .collect::<Vec<_>>();
    let capability_captures = program
        .functions
        .iter()
        .map(|function| {
            if function.closure.is_some() {
                function.capability_parameters.clone()
            } else {
                Vec::new()
            }
        })
        .collect::<Vec<_>>();
    let foreign_functions = program.foreign_functions.clone();
    for (function_index, function) in program.functions.iter_mut().enumerate() {
        // A foreign declaration has a checked inert body but no source
        // operations. Its parameters are consumed by the trusted C contract;
        // Kush still checks every call site's ownership.
        if foreign_functions
            .get(function_index)
            .is_some_and(Option::is_some)
        {
            continue;
        }
        let mut checker = Checker {
            enums: &program.enums,
            owned: &program.owned_enums,
            linear: &program.linear_enums,
            dyn_linear: &dyn_linear,
            unions: &program.unions,
            pointees: &program.pointees,
            reference_labels: &program.reference_labels,
            variance: &program.variance,
            functions: &program.function_types,
            capture_refs: &capture_refs,
            capture_writes: &capture_writes,
            capability_captures: &capability_captures,
            result_grades: &result_grades,
            calls: &calls,
            dyn_call_lifetimes: &dyn_call_lifetimes,
            union_call_lifetimes: &union_call_lifetimes,
            result_lifetime: function.result_lifetime.clone(),
            result_type: function.result,
            parameter_lifetimes: function.parameter_lifetimes.clone(),
            lifetime_bounds: function.lifetime_bounds.clone(),
            declared_lifetimes: function.declared_lifetimes.clone(),
            parameter_labels: calls[function_index]
                .parameters
                .iter()
                .flatten()
                .filter_map(|leaf| leaf.lifetime.clone())
                .collect(),
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
            place_borrow: false,
            slice_place_root: None,
            field_target: None,
            record_sources: vec![None; function.locals.len()],
            call_views: BTreeMap::new(),
            call_records: BTreeMap::new(),
            construct_records: BTreeMap::new(),
            call_lifetime_counter: 0,
            call_origins: BTreeMap::new(),
            call_splits: BTreeMap::new(),
            live: &liveness[function_index],
            index_relations: function.index_relations.clone(),
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
            aborts: Vec::new(),
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
                // A shared `&Box<&T>`/`&Vec<&T>` parameter reads element
                // references owned by the caller; each element leaf is rooted
                // at this parameter with the element's declared lifetime.
                if let Some(container) = checker
                    .referent(local.ty)
                    .filter(|ty| container_carries_borrow(checker.enums, checker.pointees, *ty))
                {
                    checker.record_sources[index] =
                        Some(checker.parameter_record_provenance(index, container)?);
                }
            } else if index < function.parameters && checker.is_carrier_type(local.ty) {
                // A borrowed-record parameter is an aggregate of external
                // field views. Each leaf is rooted at this parameter and
                // carries the declared field lifetime from its type.
                checker.record_sources[index] =
                    Some(checker.parameter_record_provenance(index, local.ty)?);
            }
        }
        checker.block(&mut function.body)?;
        if function.body.ty != Type::Never {
            if function.body.ty.is_view() {
                let origins = function
                    .body
                    .tail
                    .as_ref()
                    .map(|tail| checker.return_origins(tail))
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
                    .map(|tail| checker.return_origins(tail))
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
    /// A local record root that was added only as an ancestor capability for a
    /// borrowed field. Every use keeps it loaned, but a returned view does not
    /// borrow the record's own storage, so return checks follow the field's
    /// external origins instead.
    ancestor: Option<usize>,
}
/// A borrowed record-field place: the local record root and the field index
/// path from its tag. The path is a checker-only identity, not a runtime value.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FieldBorrow {
    root: usize,
    path: Vec<usize>,
}
impl FieldBorrow {
    /// Two places under one root are disjoint when some position of their
    /// paths is provably different: two record fields, two distinct constant
    /// indices, or two index places whose values the checker's facts proved
    /// distinct (`relations`). Until a field step differs both paths address
    /// the same type, so one provable difference at any position separates
    /// the storage. Everything else (a prefix, an unproved index pair, an
    /// index whose identity was stripped) conflicts. Paths under different
    /// roots are never considered disjoint here; ordinary root-intersection
    /// rules decide those.
    fn disjoint(&self, other: &Self, relations: &BTreeSet<(usize, usize)>) -> bool {
        self.root == other.root
            && self
                .path
                .iter()
                .zip(&other.path)
                .any(|(left, right)| steps_distinct(*left, *right, relations))
    }
    /// Forget the index-place identities so no proved relation applies. A
    /// relation is proved for the values of one evaluation of each place; a
    /// loan stored outside a direct reference binding (in a record, a
    /// container, or a task region) can outlive a loop iteration, where the
    /// same place denotes another value.
    fn strip_index_ids(&mut self) {
        for step in &mut self.path {
            if *step & RUNTIME_INDEX_MARK != 0 {
                *step = RUNTIME_INDEX_MARK;
            } else if *step & INDEX_PATH_MARK != 0 {
                *step = INDEX_PATH_MARK | (*step & INDEX_VALUE_MASK);
            }
        }
    }
}
/// Marker bit that distinguishes a constant element-index step from a
/// record-field index in a structural place path. The low 32 bits hold the
/// index value and bits 32..56 the index place's checker identity.
const INDEX_PATH_MARK: usize = 1 << (usize::BITS - 8);
/// Marker bit of a runtime element-index step; the low bits hold the index
/// place's checker identity (zero when unknown or stripped).
const RUNTIME_INDEX_MARK: usize = 1 << (usize::BITS - 7);
const INDEX_VALUE_MASK: usize = (1 << 32) - 1;
const INDEX_ID_LIMIT: usize = 1 << 24;
/// Path step of an index place with checker identity `id`.
fn index_step(id: usize, constant: Option<i64>) -> usize {
    let id = if id < INDEX_ID_LIMIT { id } else { 0 };
    match constant.and_then(|value| usize::try_from(value).ok()) {
        Some(value) if value <= INDEX_VALUE_MASK => INDEX_PATH_MARK | (id << 32) | value,
        _ => RUNTIME_INDEX_MARK | id,
    }
}
/// The checker identity of an index step, if it has one.
fn index_step_id(step: usize) -> Option<usize> {
    let id = if step & RUNTIME_INDEX_MARK != 0 {
        step & !RUNTIME_INDEX_MARK
    } else if step & INDEX_PATH_MARK != 0 {
        (step & !INDEX_PATH_MARK) >> 32
    } else {
        return None;
    };
    (id != 0).then_some(id)
}
fn steps_distinct(left: usize, right: usize, relations: &BTreeSet<(usize, usize)>) -> bool {
    let index = |step: usize| step & (INDEX_PATH_MARK | RUNTIME_INDEX_MARK) != 0;
    match (index(left), index(right)) {
        (false, false) => left != right,
        (true, true) => {
            let constant = |step: usize| step & RUNTIME_INDEX_MARK == 0;
            if constant(left) && constant(right) {
                return left & INDEX_VALUE_MASK != right & INDEX_VALUE_MASK;
            }
            match (index_step_id(left), index_step_id(right)) {
                (Some(a), Some(b)) if a != b => relations.contains(&(a.min(b), a.max(b))),
                _ => false,
            }
        }
        // A field and an index step never meet at one position of two paths
        // under one root; treat the impossible case as a conflict.
        _ => false,
    }
}
/// A container's or record's stored provenance without index-place
/// identities: see [`FieldBorrow::strip_index_ids`].
/// A write into a container or record reached through a place whose owner
/// cannot be identified.
fn untracked_write(span: Span) -> Diagnostic {
    Diagnostic::new(
        span,
        "cannot track which owner this write through a place reference updates; borrow the container or record through a direct local or a reference parameter",
    )
}
fn stripped_provenance(mut provenance: RecordProvenance) -> RecordProvenance {
    for loan in provenance.leaves.values_mut() {
        if let Some(field) = &mut loan.field {
            field.strip_index_ids();
        }
    }
    provenance
}
/// The referent of a shared or exclusive reference type, through annotations.
fn referent_of(pointees: &[Type], ty: Type) -> Option<Type> {
    match ty {
        Type::Ref(p) | Type::RefMut(p) => Some(pointees[p]),
        Type::Annotated(p, _) => referent_of(pointees, pointees[p]),
        _ => None,
    }
}
/// Whether an owning container directly or transitively stores a reference
/// element. Borrowed records are handled separately by their layout flag.
fn container_carries_borrow(
    enums: &[crate::runtime_types::Enum],
    pointees: &[Type],
    ty: Type,
) -> bool {
    match ty {
        Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) | Type::AllocBox(p) | Type::AllocVec(p) => {
            match pointees[p] {
                Type::Annotated(..) | Type::Ref(_) | Type::RefMut(_) | Type::Str => true,
                Type::Enum(id) | Type::Variants(id, _) if enums[id].borrowed => true,
                inner => container_carries_borrow(enums, pointees, inner),
            }
        }
        _ => false,
    }
}
/// Per-leaf provenance of a record value. Paths are field indices from the
/// record root; a slice field is a leaf, and a nested borrowed record extends
/// the path. Ordinary copyable metadata contributes no leaf.
#[derive(Clone, Debug, Default)]
struct RecordProvenance {
    leaves: BTreeMap<Vec<usize>, Loan>,
    /// Every actual lifetime contributed to a leaf before a branch join hid an
    /// incomparable label. Diagnostics use this to name the failing source
    /// instead of falling back to "a temporary or local owner".
    alternatives: BTreeMap<Vec<usize>, BTreeSet<String>>,
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
                if let Some(lifetime) = &loan.lifetime {
                    merged
                        .alternatives
                        .entry(path.clone())
                        .or_default()
                        .insert(lifetime.clone());
                }
                if let Some(alternatives) = part.alternatives.get(path) {
                    merged
                        .alternatives
                        .entry(path.clone())
                        .or_default()
                        .extend(alternatives.iter().cloned());
                }
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
#[derive(Clone)]
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
#[allow(clippy::too_many_arguments)]
fn leaves_of(
    enums: &[crate::runtime_types::Enum],
    pointees: &[Type],
    labels: &[String],
    variance_table: &crate::variance::VarianceTable,
    ty: Type,
) -> Result<Vec<crate::runtime_types::BorrowLeaf>> {
    fn field_position(
        enums: &[crate::runtime_types::Enum],
        pointees: &[Type],
        labels: &[String],
        variance_table: &crate::variance::VarianceTable,
        layout: usize,
        field: usize,
        field_ty: Type,
        position: crate::variance::SignSet,
    ) -> crate::variance::SignSet {
        let record = &enums[layout];
        let definition = record.definition;
        // Apply the enclosing declaration's variance for every record lifetime
        // parameter that occurs in this field, including occurrences reached
        // through a nested record or an owned container. A leaf that is
        // invariant through another field must not be recorded as covariant.
        let mut wanted = BTreeSet::new();
        collect_borrow_lifetimes_in(enums, pointees, labels, field_ty, &mut wanted);
        if let Some(label) = record.field_lifetimes.get(field).cloned().flatten() {
            wanted.insert(label);
        }
        let mut composed = position;
        let mut seen_label = BTreeSet::new();
        for argument in &record.lifetimes {
            if !wanted.contains(argument) || !seen_label.insert(argument.clone()) {
                continue;
            }
            let mut variance = crate::variance::SignSet::UNUSED;
            let mut found = false;
            for (index, slot) in record.lifetimes.iter().enumerate() {
                if slot == argument
                    && let Some(value) = variance_table.of(definition, index)
                {
                    variance = variance.join(value);
                    found = true;
                }
            }
            if !found || variance.is_unused() {
                variance = crate::variance::SignSet::INVARIANT;
            }
            composed = composed.compose(variance);
        }
        // A structural row declares no lifetime parameters: each field label
        // belongs to the erased outer borrow of its own field type, whose
        // constructor is covariant. Only a nominal declaration whose label is
        // not one of its own lifetime parameters is inconsistent metadata.
        if !record.structural
            && record
                .field_lifetimes
                .get(field)
                .and_then(Option::as_ref)
                .is_some_and(|label| !record.lifetimes.iter().any(|slot| slot == label))
        {
            composed = composed.compose(crate::variance::SignSet::INVARIANT);
        }
        composed
    }
    #[allow(clippy::too_many_arguments)]
    fn go(
        enums: &[crate::runtime_types::Enum],
        pointees: &[Type],
        labels: &[String],
        variance_table: &crate::variance::VarianceTable,
        ty: Type,
        hint: Option<String>,
        position: crate::variance::SignSet,
        path: &mut Vec<usize>,
        out: &mut Vec<crate::runtime_types::BorrowLeaf>,
        seen: &mut BTreeSet<Type>,
        depth: usize,
    ) -> Result<()> {
        if depth >= 128 {
            return Err(crate::Diagnostic::new(
                crate::Span::default(),
                "borrowed-leaf enumeration exceeded its finite nesting budget; this type is too deeply nested to summarize",
            ));
        }
        if !seen.insert(ty) {
            let name = ty
                .layout()
                .map(|id| enums[id].name.clone())
                .unwrap_or_else(|| "type".to_owned());
            return Err(crate::Diagnostic::new(
                crate::Span::default(),
                format!(
                    "recursive borrowed type '{name}' stores a borrowed leaf through its own type; this recursive borrow shape is not supported by lifetime summaries. Store the owner outside the recursive type or return the borrow directly"
                ),
            ));
        }
        let result = (|| {
            if let Some(id) = ty.layout()
                && let Some(reference) = enums[id].optional_reference()
            {
                go(
                    enums,
                    pointees,
                    labels,
                    variance_table,
                    reference,
                    None,
                    position.compose(crate::variance::SignSet::INVARIANT),
                    path,
                    out,
                    seen,
                    depth + 1,
                )?;
                return Ok(());
            }
            match ty {
                Type::Slice(_) => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: false,
                    variance: position,
                }),
                Type::SliceMut(_) => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: true,
                    variance: position,
                }),
                Type::Str => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: false,
                    variance: position,
                }),
                Type::StrMut => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: true,
                    variance: position,
                }),
                Type::Ref(_) => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: false,
                    variance: position,
                }),
                Type::RefMut(_) => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: hint,
                    mutable: true,
                    variance: position,
                }),
                Type::Annotated(p, label) => out.push(crate::runtime_types::BorrowLeaf {
                    path: path.clone(),
                    lifetime: labels
                        .get(label as usize)
                        .filter(|label| !label.is_empty())
                        .cloned(),
                    mutable: matches!(pointees[p], Type::RefMut(_)),
                    variance: position,
                }),
                Type::Box(p) | Type::Vec(p) => go(
                    enums,
                    pointees,
                    labels,
                    variance_table,
                    pointees[p],
                    None,
                    position.compose(crate::variance::SignSet::POSITIVE),
                    path,
                    out,
                    seen,
                    depth + 1,
                )?,
                Type::ArenaBox(p) | Type::AllocBox(p) | Type::AllocVec(p) => go(
                    enums,
                    pointees,
                    labels,
                    variance_table,
                    pointees[p],
                    None,
                    position.compose(crate::variance::SignSet::INVARIANT),
                    path,
                    out,
                    seen,
                    depth + 1,
                )?,
                Type::Enum(id) | Type::Variants(id, _)
                    if enums[id].record || enums[id].name == "TaskExit" =>
                {
                    if enums[id].record {
                        for (index, field) in enums[id].variants[0].fields.iter().enumerate() {
                            path.push(index);
                            let field_hint = enums[id].field_lifetimes[index].clone();
                            let position = field_position(
                                enums,
                                pointees,
                                labels,
                                variance_table,
                                id,
                                index,
                                *field,
                                position,
                            );
                            go(
                                enums,
                                pointees,
                                labels,
                                variance_table,
                                *field,
                                field_hint,
                                position,
                                path,
                                out,
                                seen,
                                depth + 1,
                            )?;
                            path.pop();
                        }
                    } else {
                        // A borrowed `TaskExit<T>` payload keeps its existing
                        // scoped provenance; no new payload variance is admitted.
                        for variant in &enums[id].variants {
                            for field in &variant.fields {
                                go(
                                    enums,
                                    pointees,
                                    labels,
                                    variance_table,
                                    *field,
                                    None,
                                    position.compose(crate::variance::SignSet::INVARIANT),
                                    path,
                                    out,
                                    seen,
                                    depth + 1,
                                )?;
                            }
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        })();
        seen.remove(&ty);
        result
    }
    let mut out = Vec::new();
    go(
        enums,
        pointees,
        labels,
        variance_table,
        ty,
        None,
        crate::variance::SignSet::POSITIVE,
        &mut Vec::new(),
        &mut out,
        &mut BTreeSet::new(),
        0,
    )?;
    Ok(out)
}
/// Collect every erased lifetime label reachable from `ty` through borrowing
/// constructors. Used only to compose enclosing declaration variance for leaf
/// collection; it is cycle-safe.
fn collect_borrow_lifetimes_in(
    enums: &[crate::runtime_types::Enum],
    pointees: &[Type],
    labels: &[String],
    ty: Type,
    out: &mut BTreeSet<String>,
) {
    fn go(
        enums: &[crate::runtime_types::Enum],
        pointees: &[Type],
        labels: &[String],
        ty: Type,
        out: &mut BTreeSet<String>,
        seen: &mut BTreeSet<Type>,
    ) {
        if !seen.insert(ty) {
            return;
        }
        match ty {
            Type::Slice(p) | Type::SliceMut(p) | Type::Ref(p) | Type::RefMut(p) | Type::Task(p) => {
                go(enums, pointees, labels, pointees[p], out, seen)
            }
            Type::Str | Type::StrMut => {}
            Type::Annotated(_, label) => {
                if let Some(name) = labels.get(label as usize).filter(|label| !label.is_empty()) {
                    out.insert(name.clone());
                }
            }
            Type::Box(p)
            | Type::ArenaBox(p)
            | Type::Vec(p)
            | Type::AllocBox(p)
            | Type::AllocVec(p) => go(enums, pointees, labels, pointees[p], out, seen),
            Type::Enum(id) | Type::Variants(id, _) => {
                out.extend(enums[id].lifetimes.iter().cloned());
                for argument in &enums[id].arguments {
                    go(enums, pointees, labels, *argument, out, seen);
                }
                for variant in &enums[id].variants {
                    for field in &variant.fields {
                        go(enums, pointees, labels, *field, out, seen);
                    }
                }
            }
            _ => {}
        }
    }
    go(enums, pointees, labels, ty, out, &mut BTreeSet::new());
}
/// A callee lifetime for diagnostics. Every name, including a canonical `#k`
/// or an internal inference identity, uses the shared diagnostic spelling.
fn describe_lifetime(name: &str) -> String {
    crate::runtime_types::lifetime_label_text(name)
}
/// A caller-side lifetime for diagnostics, hiding internal labels.
fn describe_actual(name: &str) -> String {
    if name.starts_with("<local ") {
        "a borrow of a local owner".to_owned()
    } else if name.starts_with('<') || name.starts_with('#') {
        crate::runtime_types::lifetime_label_text(name)
    } else {
        format!("lifetime '{name}'")
    }
}
/// Name one actual lifetime inside a type-level message. A named caller label
/// keeps its surface spelling; a canonical `#k` label is rendered like an arrow
/// lifetime, and an internal inference identity uses the same anonymous `'_N`
/// spelling as the type display instead of leaking its `<...>` storage name.
fn display_actual_lifetime(name: &str) -> String {
    crate::runtime_types::lifetime_label_text(name)
}
fn is_internal_lifetime(name: &str) -> bool {
    name.starts_with('<')
}
fn describe_variance(variance: crate::variance::SignSet) -> &'static str {
    if variance.is_invariant() {
        "invariant"
    } else if variance.is_negative_only() {
        "contravariant"
    } else if variance.is_positive_only() {
        "covariant"
    } else {
        "unused"
    }
}
fn is_place_read(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Peek(_) | ExprKind::InitOwner { .. } => true,
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
        | Type::AllocatorContext
        | Type::AllocBox(_)
        | Type::AllocVec(_)
        | Type::Bytes
        | Type::String
        | Type::Vec(_)
        | Type::Once(_)
        | Type::Task(_)
        | Type::DynObj(_) => true,
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
    dyn_linear: &[bool],
) -> bool {
    match ty {
        Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) | Type::AllocBox(p) | Type::AllocVec(p) => {
            is_linear(pointees[p], enums, unions, pointees, functions, dyn_linear)
        }
        Type::Enum(id) | Type::Variants(id, _) => enums[id],
        Type::Union(id) => unions[id]
            .members
            .iter()
            .any(|member| is_linear(*member, enums, unions, pointees, functions, dyn_linear)),
        Type::DynObj(id) => dyn_linear.get(id).copied().unwrap_or(false),
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
    /// Snapshots taken at each break, before branch-local metadata changes.
    result_provenance: Vec<RecordProvenance>,
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
    /// Only these origins are exclusive; the remaining captures stay shared.
    exclusive_origins: BTreeSet<usize>,
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
    /// `Type::DynObj(id)` is linear when any registered member is linear.
    dyn_linear: &'a [bool],
    unions: &'a [crate::runtime_types::UnionType],
    pointees: &'a [Type],
    reference_labels: &'a [String],
    variance: &'a crate::variance::VarianceTable,
    functions: &'a [crate::runtime_types::FunctionType],
    /// Capture representation of each checked function instance. Scalar
    /// captures marked `true` store a pointer to the caller's location.
    capture_refs: &'a [Vec<bool>],
    /// Capture write metadata: a writing by-reference capture is an exclusive
    /// loan; a read-only one is shared.
    capture_writes: &'a [Vec<bool>],
    /// Capture positions of each closure that hold a capability
    /// (EFF-CAP-LAMBDA): the closure is a shared scoped borrow of it.
    capability_captures: &'a [Vec<usize>],
    /// Static result contract of each checked function, by instance index:
    /// `(grade, owning)`. `owning` distinguishes an owning `@[1]` transfer
    /// (which is a move) from a copyable must-use `@[1]` contract (which the
    /// grade pass enforces). Metadata only; runtime payloads and the ABI are
    /// unchanged.
    result_grades: &'a [Option<(Grade, bool)>],
    calls: &'a [CallLifetime],
    /// Lifetime provenance witness for each dynamic-object and closed-union
    /// borrowed call site.
    dyn_call_lifetimes: &'a [CallLifetime],
    union_call_lifetimes: &'a [CallLifetime],
    result_lifetime: Option<String>,
    result_type: Type,
    parameter_lifetimes: Vec<Option<String>>,
    /// Reflexive-transitive outlives bounds declared by this function.
    lifetime_bounds: BTreeSet<(String, String)>,
    /// Lifetime binders declared by this function. A mutable container/record
    /// write treats these labels as rigid destinations; a label that exists
    /// only in an expected instantiation is a call-site placeholder and defers
    /// to the container's actual provenance.
    declared_lifetimes: BTreeSet<String>,
    /// Every lifetime label on this function's parameter leaves, including
    /// elided ones. An elided parameter label is a distinct, rigid identity:
    /// writing a reference into a parameter's container or record must prove
    /// it outlives that label, exactly like a declared one.
    parameter_labels: BTreeSet<String>,
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
    /// One checked place borrow is being formed. Ancestor reads of the root
    /// are permitted here; `check_view_creation` rejects an overlapping field
    /// or whole-owner capability with a place-specific diagnostic.
    place_borrow: bool,
    /// The view binding under the slice element place being borrowed.
    slice_place_root: Option<usize>,
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
    /// Pairs of index-place identities `(low, high)` whose index values the
    /// type checker's facts proved distinct at the later place.
    index_relations: BTreeSet<(usize, usize)>,
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
    /// Abortive scopes (E-ABORT-LEXICAL) by label: an `AbortExit` is checked
    /// like a `break` to its scope.
    aborts: Vec<(usize, LoopState)>,
}
impl Checker<'_> {
    /// Values that move instead of being copied.
    fn moves(&self, ty: Type) -> bool {
        ty.is_mut_slice()
            || matches!(ty, Type::RefMut(_))
            || owns(ty, self.owned, self.unions, self.pointees)
            || is_linear(
                ty,
                self.linear,
                self.unions,
                self.pointees,
                self.functions,
                self.dyn_linear,
            )
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
                self.dyn_linear,
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
            || container_carries_borrow(self.enums, self.pointees, ty)
    }
    /// The referent of a shared or exclusive reference type, through lifetime
    /// labels.
    fn referent(&self, ty: Type) -> Option<Type> {
        match ty {
            Type::Ref(p) | Type::RefMut(p) => Some(self.pointees[p]),
            Type::Annotated(p, _) => self.referent(self.pointees[p]),
            _ => None,
        }
    }
    fn is_task_exit(&self, ty: Type) -> bool {
        ty.layout()
            .is_some_and(|id| self.enums[id].name == "TaskExit")
    }
    fn parameter_record_provenance(&self, slot: usize, ty: Type) -> Result<RecordProvenance> {
        let mut provenance = RecordProvenance::default();
        for leaf in leaves_of(
            self.enums,
            self.pointees,
            self.reference_labels,
            self.variance,
            ty,
        )? {
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
                    ancestor: None,
                },
            );
        }
        Ok(provenance)
    }
    /// The record field index at a word offset (word 0 is the tag).
    fn field_index(&self, ty: Type, offset: usize) -> Option<usize> {
        let id = ty.layout().filter(|id| self.enums[*id].record)?;
        let mut at = self.enums[id].tag_words();
        for (index, field) in self.enums[id].variants[0].fields.iter().enumerate() {
            if at == offset {
                return Some(index);
            }
            at += crate::runtime_types::width(
                self.pointees,
                self.enums,
                self.unions,
                self.functions,
                *field,
            );
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
                ExprKind::Coerce {
                    value, coercion, ..
                } => {
                    // `path` is outermost-first reversed; renumber the part
                    // below this coercion into the source layout.
                    path.reverse();
                    path = coerce_field_path(coercion, &path)?;
                    path.reverse();
                    current = value;
                }
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
    /// Root binding and record-field path of a checked place. Index places
    /// keep the base field path: two different element indices of one vector
    /// conservatively conflict. A place through a stored reference roots the
    /// reference binding itself; its underlying owners come from `view_loan`.
    fn place_ident(&self, expr: &Expr) -> Option<(usize, Vec<usize>)> {
        match &expr.kind {
            ExprKind::Project(base, offset) => {
                if base.ty.is_ref() {
                    let root = match &base.kind {
                        ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                            *slot
                        }
                        _ => return None,
                    };
                    return Some((root, Vec::new()));
                }
                let (root, mut path) = self.place_ident(base)?;
                path.push(self.field_index(base.ty, *offset)?);
                Some((root, path))
            }
            ExprKind::PlaceIndex { base, index, id } => {
                let (root, mut path) = self.place_ident(base)?;
                let constant = match &index.kind {
                    ExprKind::Constant(position) => Some(*position),
                    _ => None,
                };
                path.push(index_step(*id, constant));
                Some((root, path))
            }
            ExprKind::Coerce { value, .. } | ExprKind::AbortCall { call: value, .. } => {
                self.place_ident(value)
            }
            ExprKind::Local(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Move(slot)
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::BorrowInit { slot, .. } => Some((*slot, Vec::new())),
            _ => None,
        }
    }
    /// Provenance of a checked place borrow. Borrowed leaves (reference and
    /// slice fields) keep their owner ancestry; scalar/array/owning places add
    /// the root binding as an ancestor capability and retain a structural
    /// field identity for disjoint-field exemption.
    fn place_loan(&self, place: &Expr) -> Loan {
        if let Some(view) = slice_place_view(place) {
            // An element of a slice view narrows the view's capability, like a
            // subview: it roots at the view's owners, keeps its split side, and
            // inherits its lifetime, so the owners stay loaned after the view
            // binding's own last use and split_at_mut sides stay disjoint.
            //
            // A view binding is the root of its element places, so two
            // element references into one view coexist exactly when their
            // paths are provably disjoint (distinct constants, or indices the
            // checker's facts proved distinct).
            let parent = self.view_loan(view);
            let field = match &view.kind {
                ExprKind::Local(_) | ExprKind::Peek(_) | ExprKind::Move(_) => self
                    .place_ident(place)
                    .map(|(root, path)| FieldBorrow { root, path }),
                _ => None,
            };
            return Loan {
                origins: self.view_origins(view),
                mutable: false,
                splits: parent.splits,
                lifetime: parent.lifetime,
                field,
                ancestor: None,
            };
        }
        let leaf = self.view_loan(place);
        if !leaf.origins.is_empty() && !matches!(place.kind, ExprKind::PlaceIndex { .. }) {
            let mut loan = leaf;
            if let Some((root, path)) = self.place_ident(place) {
                loan.field.get_or_insert(FieldBorrow { root, path });
            }
            return loan;
        }
        let Some((root, path)) = self.place_ident(place) else {
            return Loan::default();
        };
        Loan {
            origins: BTreeSet::from([root]),
            mutable: false,
            splits: SplitLabels::default(),
            lifetime: None,
            field: Some(FieldBorrow { root, path }),
            ancestor: None,
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
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. } if expr.ty.is_ref() => {
                // A reference to a borrowed record or reference container
                // keeps every leaf that record already borrows loaned as well.
                // Passing `&holder` to a helper therefore cannot outlive the
                // storage behind `holder`'s reference fields.
                let mut origins = BTreeSet::from([*slot]);
                if matches!(expr.ty, Type::Ref(_))
                    && self.is_carrier_type(self.locals[*slot].ty)
                    && let Some(provenance) = &self.record_sources[*slot]
                {
                    for leaf in provenance.leaves.values() {
                        origins.extend(leaf.origins.iter().copied());
                    }
                }
                Loan {
                    origins,
                    mutable: matches!(expr.ty, Type::RefMut(_)),
                    splits: SplitLabels::default(),
                    lifetime: None,
                    field: self.projection_field(expr),
                    ancestor: None,
                }
            }
            ExprKind::InitOwner { slot, .. } if self.is_carrier_type(self.locals[*slot].ty) => {
                // A temporary record owner keeps every borrowed field it
                // contains loaned, exactly like a shared borrow of a local
                // record.
                let mut origins = BTreeSet::from([*slot]);
                if let Some(provenance) = &self.record_sources[*slot] {
                    for leaf in provenance.leaves.values() {
                        origins.extend(leaf.origins.iter().copied());
                    }
                }
                Loan {
                    origins,
                    mutable: false,
                    splits: SplitLabels::default(),
                    lifetime: None,
                    field: self.projection_field(expr),
                    ancestor: None,
                }
            }
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
                        ancestor: None,
                    }
                } else {
                    Loan {
                        origins: BTreeSet::from([*slot]),
                        mutable: matches!(expr.ty, Type::RefMut(_)),
                        splits: SplitLabels::default(),
                        lifetime: self.reference_lifetimes[*slot].clone(),
                        field: None,
                        ancestor: None,
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
                        ancestor: None,
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
                    // A DynArray field view through a record reference lives
                    // as long as that reference's referent.
                    let mut root = base.as_ref();
                    while let ExprKind::Project(inner, _) = &root.kind {
                        root = inner;
                    }
                    if root.ty.is_ref() && !std::ptr::eq(root, base.as_ref()) {
                        self.view_loan(root).lifetime
                    } else {
                        None
                    }
                },
                field: match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                        if base.ty.is_view() =>
                    {
                        self.view_fields[*slot].clone()
                    }
                    _ => self.projection_field(base),
                },
                ancestor: None,
            },
            ExprKind::Project(base, offset) => {
                if base.ty.is_ref() {
                    // A shared reference field projected through `&Record`
                    // reads the stored pointer; it aliases the same storage as
                    // the record's construction did. The field's declared
                    // lifetime is already instantiated in the record type.
                    let Some(pointer) = base.ty.ref_pointee() else {
                        return Loan::default();
                    };
                    let referent = self.pointees[pointer];
                    let Some(index) = self.field_index(referent, *offset) else {
                        return Loan::default();
                    };
                    let declared = referent
                        .layout()
                        .and_then(|id| self.enums[id].field_lifetimes.get(index).cloned())
                        .flatten();
                    return Loan {
                        origins: self.view_origins(base),
                        mutable: false,
                        splits: SplitLabels::default(),
                        lifetime: declared.or_else(|| self.view_loan(base).lifetime),
                        field: None,
                        ancestor: None,
                    };
                }
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
                    //
                    // A borrowed leaf already names the external storage it
                    // points at, so the binding is only an ancestor for local
                    // lifetime purposes. Mark that separately: a returned
                    // view does not borrow the record's own storage, but every
                    // other use still keeps the record loaned. An owned field
                    // has no leaf origin and the binding is its storage root;
                    // a record *parameter* roots its own leaves, so it is a
                    // real owner rather than an ancestor.
                    let external_leaf = loan.origins.iter().any(|origin| *origin != field.root);
                    loan.origins.insert(field.root);
                    if external_leaf {
                        loan.ancestor = Some(field.root);
                    }
                }
                loan
            }
            ExprKind::BorrowPlace(place) => {
                let mut loan = self.place_loan(place);
                loan.mutable = matches!(expr.ty, Type::RefMut(_));
                loan
            }
            ExprKind::Coerce { value, .. } | ExprKind::AbortCall { call: value, .. } => {
                self.view_loan(value)
            }
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
            ancestor: loans[0].ancestor,
        };
        for loan in &loans {
            merged.origins.extend(loan.origins.iter().copied());
            merged.mutable |= loan.mutable;
            merged.splits = intersect_splits(&merged.splits, &loan.splits);
            if loan.lifetime != merged.lifetime {
                // Join branch view lifetimes to their shortest provable common
                // label. Unioning origins keeps every owner loaned; choosing a
                // shorter label only narrows how long the joined view can be
                // used. Incomparable labels keep an anonymous intersection.
                merged.lifetime = match (&merged.lifetime, &loan.lifetime) {
                    (Some(long), Some(short)) if self.actual_outlives(long, short) => {
                        Some(short.clone())
                    }
                    (Some(long), Some(short)) if self.actual_outlives(short, long) => {
                        Some(long.clone())
                    }
                    _ => None,
                };
            }
            if loan.field != merged.field {
                merged.field = None;
            }
            if loan.ancestor != merged.ancestor {
                // One alternative may project an owned field from the same
                // record; the binding is then real storage for that path and
                // no return check may skip it.
                merged.ancestor = None;
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
            if field_ty.is_view() {
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
                    None if layout.structural => {
                        // Structural rows erase field lifetime labels. The
                        // actual loan lifetime stays in provenance, so a later
                        // escape is still checked; there is no declared label
                        // to compare against here.
                    }
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
                let expected = leaves_of(
                    self.enums,
                    self.pointees,
                    self.reference_labels,
                    self.variance,
                    field_ty,
                )?;
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
                        && !self.lifetime_carried_at(
                            loan.lifetime.as_deref(),
                            lifetime,
                            leaf.variance,
                        )
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "nested field '{}' must satisfy the declared lifetime '{lifetime}' at its {} occurrence, but its source has lifetime {}",
                                variant.names[index],
                                describe_variance(leaf.variance),
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
            | ExprKind::BorrowInit { slot, .. }
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::Local(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Move(slot)
                if self.is_carrier_type(self.locals[*slot].ty)
                    || self.locals[*slot].ty.is_ref() =>
            {
                self.record_sources[*slot].clone().unwrap_or_default()
            }
            _ => self.record_provenance(expr),
        }
    }
    /// Record a reference written into an owned container or through a
    /// `&mut` container parameter. `replace` updates the sole element leaf;
    /// `push` keeps the union of every possible element source.
    #[must_use]
    fn merge_container_element(&mut self, receiver: &Expr, loan: Loan, replace: bool) -> bool {
        let mut provenance = RecordProvenance::default();
        provenance.leaves.insert(Vec::new(), loan);
        self.merge_written(receiver, provenance, replace)
    }
    /// The borrow leaf of one reference value stored in a container. A direct
    /// reference expression carries its own loan; a nested borrowed record is
    /// not admitted as a container element.
    fn reference_element_loan(&self, expr: &Expr) -> Option<Loan> {
        (expr.ty.is_ref() || expr.ty.is_view()).then(|| self.view_loan(expr))
    }
    /// Whether a container element itself carries borrowed storage. Container
    /// provenance applies to reference elements, text views, and borrowed
    /// record elements.
    fn element_carries_borrow(&self, ty: Type) -> bool {
        match ty {
            Type::Annotated(..) | Type::Ref(_) | Type::RefMut(_) | Type::Str => true,
            Type::Enum(id) | Type::Variants(id, _) if self.enums[id].borrowed => true,
            Type::Box(p)
            | Type::ArenaBox(p)
            | Type::Vec(p)
            | Type::AllocBox(p)
            | Type::AllocVec(p) => self.element_carries_borrow(self.pointees[p]),
            _ => false,
        }
    }
    /// Provenance of one borrowed-record container element. A direct reference
    /// element has a single leaf at the element root; a borrowed record carries
    /// one leaf per declared borrowed field, addressed relative to the element.
    fn borrowed_element_provenance(&self, expr: &Expr) -> RecordProvenance {
        self.record_provenance(expr)
    }
    /// Merge a whole element provenance into a container binding. Paths are
    /// relative to one element. `replace` is used only where the container
    /// provably holds one element (`Box.set`); vector writes always keep the
    /// union of every possible element source.
    #[must_use]
    fn merge_container_provenance(
        &mut self,
        receiver: &Expr,
        provenance: RecordProvenance,
        replace: bool,
    ) -> bool {
        self.merge_written(receiver, provenance, replace)
    }
    /// Record leaves written through `receiver` (a container or borrowed
    /// record reached by `&mut`) on every local owner it can denote. A place
    /// or a stored reference to a field merges under that field's path; a
    /// stored reference to a whole local merges into owners of the same type,
    /// replacing only when there is exactly one. Returns false when the owner
    /// cannot be identified (a block, branch, or call result receiver, or a
    /// reference whose owners have another type); the caller rejects the
    /// write.
    #[must_use]
    fn merge_written(
        &mut self,
        receiver: &Expr,
        provenance: RecordProvenance,
        replace: bool,
    ) -> bool {
        let base = through_coerce(receiver);
        let slot = match &base.kind {
            ExprKind::BorrowPlace(place) => {
                return match self.place_ident(place) {
                    Some((root, path)) => self.merge_into_place_owner(root, path, provenance),
                    None => false,
                };
            }
            ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. }
            | ExprKind::InitOwner { slot, .. } => {
                self.merge_container_provenance_slot(*slot, provenance, replace);
                return true;
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => *slot,
            _ => return false,
        };
        if !self.locals[slot].ty.is_ref() || slot < self.parameter_count {
            self.merge_container_provenance_slot(slot, provenance, replace);
            return true;
        }
        let tracked = if let Some(field) = self.view_fields[slot].clone() {
            self.merge_into_place_owner(field.root, field.path, provenance.clone())
        } else {
            let referent = self.referent(self.locals[slot].ty);
            let origins = self
                .view_loan(base)
                .origins
                .into_iter()
                .filter(|owner| *owner != slot)
                .collect::<Vec<_>>();
            let owners = origins
                .iter()
                .copied()
                .filter(|owner| {
                    self.is_carrier_type(self.locals[*owner].ty)
                        && referent.is_some_and(|referent| {
                            self.same_shape(self.locals[*owner].ty, referent)
                        })
                })
                .collect::<Vec<_>>();
            let reborrow = origins
                .iter()
                .any(|owner| *owner < self.parameter_count && self.locals[*owner].ty.is_ref());
            let whole = owners.len() == 1;
            for owner in &owners {
                self.merge_container_provenance_slot(*owner, provenance.clone(), replace && whole);
            }
            !owners.is_empty() || reborrow
        };
        self.merge_container_provenance_slot(slot, provenance, false);
        tracked
    }
    /// Whether two types are the same container kind, or the same nominal
    /// record with the same type arguments (lifetimes aside).
    fn same_shape(&self, left: Type, right: Type) -> bool {
        match (left.layout(), right.layout()) {
            (Some(a), Some(b)) => {
                self.enums[a].definition == self.enums[b].definition
                    && self.enums[a].arguments == self.enums[b].arguments
            }
            (None, None) => std::mem::discriminant(&left) == std::mem::discriminant(&right),
            _ => false,
        }
    }
    /// Merge leaves written through a place reference (`&mut o.b`,
    /// `&mut v[i]`, `&mut o.v[i].h`) into the place's root owner. A container
    /// adds no path step, so the leaves go under the place's field path with
    /// index steps dropped; they are merged, never replaced, because other
    /// elements or fields share that path. A place rooted at a reference
    /// parameter writes caller storage, which the caller tracks. Returns
    /// false when the owner cannot be identified (a place rooted at a stored
    /// reference local); the caller must reject the write.
    fn merge_into_place_owner(
        &mut self,
        root: usize,
        path: Vec<usize>,
        provenance: RecordProvenance,
    ) -> bool {
        if self.locals[root].ty.is_ref() {
            return root < self.parameter_count;
        }
        let prefix = path
            .into_iter()
            .filter(|step| step & (INDEX_PATH_MARK | RUNTIME_INDEX_MARK) == 0)
            .collect::<Vec<_>>();
        let mut placed = RecordProvenance::default();
        for (path, loan) in provenance.leaves {
            let mut full = prefix.clone();
            full.extend(path);
            placed.leaves.insert(full, loan);
        }
        self.merge_container_provenance_slot(root, placed, false);
        true
    }
    fn merge_container_provenance_slot(
        &mut self,
        slot: usize,
        provenance: RecordProvenance,
        replace: bool,
    ) {
        let existing = if replace {
            RecordProvenance::default()
        } else {
            self.record_sources[slot].clone().unwrap_or_default()
        };
        let mut merged = RecordProvenance::default();
        let paths = existing
            .leaves
            .keys()
            .chain(provenance.leaves.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        for path in paths {
            let loan = match (existing.leaves.get(&path), provenance.leaves.get(&path)) {
                (Some(old), Some(new)) => self.merge_loans([old.clone(), new.clone()]),
                (Some(old), None) => old.clone(),
                (None, Some(new)) => new.clone(),
                (None, None) => continue,
            };
            merged.leaves.insert(path, loan);
        }
        let alternative_paths = existing
            .alternatives
            .keys()
            .chain(provenance.alternatives.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        for path in alternative_paths {
            let mut alternatives = existing
                .alternatives
                .get(&path)
                .cloned()
                .unwrap_or_default();
            if let Some(more) = provenance.alternatives.get(&path) {
                alternatives.extend(more.iter().cloned());
            }
            merged.alternatives.insert(path, alternatives);
        }
        self.record_sources[slot] = Some(stripped_provenance(merged));
        let mut origins = if replace {
            BTreeSet::new()
        } else {
            self.view_sources[slot].clone().unwrap_or_default()
        };
        for loan in provenance.leaves.values() {
            origins.extend(loan.origins.iter().copied());
        }
        self.view_sources[slot] = Some(origins);
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
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::InitOwner { slot, .. } => {
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
            ExprKind::Coerce {
                value, coercion, ..
            } => coerce_provenance(coercion, self.record_provenance(value)),
            ExprKind::AbortCall { call, .. } => self.record_provenance(call),
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
    /// Whether `actual` satisfies the lifetime occurrence `declared` at the
    /// given variance. A positive occurrence requires the source to outlive the
    /// declared label, a negative occurrence requires the reverse, and an
    /// invariant occurrence requires identity (proved as mutual outlives in the
    /// finite relation). An unused occurrence has no proof.
    fn lifetime_carried_at(
        &self,
        actual: Option<&str>,
        declared: &str,
        variance: crate::variance::SignSet,
    ) -> bool {
        let Some(actual) = actual else {
            return false;
        };
        if variance.is_positive_only() {
            self.actual_outlives(actual, declared)
        } else if variance.is_negative_only() {
            self.actual_outlives(declared, actual)
        } else if variance.is_invariant() {
            self.actual_outlives(actual, declared) && self.actual_outlives(declared, actual)
        } else {
            false
        }
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
                        ).with_note(span, crate::lifetimes::LifetimeGraph::new(&self.lifetime_bounds).explain_missing(long_actual, short_actual)));
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
                        origins.extend(self.loan_return_origins(&loan));
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
                        ancestor: None,
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
                // A reference into one side of a checked split keeps that side,
                // like a sliced result does.
                let mut splits: Option<SplitLabels> = None;
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
                        origins.extend(self.loan_return_origins(&loan));
                        splits = Some(match splits {
                            Some(current) => intersect_splits(&current, &loan.splits),
                            None => loan.splits,
                        });
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
                let splits = splits.unwrap_or_default();
                self.call_views.insert(
                    expr_ptr,
                    Loan {
                        origins: origins.clone(),
                        mutable,
                        splits: splits.clone(),
                        lifetime,
                        field: None,
                        ancestor: None,
                    },
                );
                self.call_origins.insert(expr_ptr, origins);
                self.call_splits.insert(expr_ptr, splits);
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
                            origins.extend(self.loan_return_origins(&loan));
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
                            ancestor: None,
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
    /// The declared destination label for a mutable write, or `None` when the
    /// write is governed only by inferred provenance. A rigid label declared by
    /// this function is authoritative even if the stored provenance was
    /// shortened; a label that exists only in an expected instantiation is a
    /// call-site placeholder, so the container's actual stored label is used
    /// instead. An internal/elided leaf contributes no named destination.
    fn write_destination_label(
        &self,
        expected: Option<&String>,
        path: &[usize],
        provenance: &RecordProvenance,
    ) -> Option<String> {
        if let Some(label) = expected
            && ((!is_internal_lifetime(label) && self.declared_lifetimes.contains(label))
                || self.parameter_labels.contains(label))
        {
            return Some(label.clone());
        }
        provenance
            .leaves
            .get(path)
            .and_then(|loan| loan.lifetime.clone())
            .filter(|label| !is_internal_lifetime(label))
    }
    /// Apply the caller-visible effect of passing an exclusive container
    /// parameter: the callee may store any reference argument whose lifetime
    /// can flow into the container's element lifetime. The caller's container
    /// provenance becomes the union of its existing elements and those
    /// arguments, so a written owner stays loaned after the call. When the
    /// caller's element lifetime is a declared label, every written reference
    /// must outlive it.
    fn apply_mutable_container_effects(
        &mut self,
        parameters: &[Vec<crate::runtime_types::BorrowLeaf>],
        bounds: &BTreeSet<(String, String)>,
        args: &[Expr],
        span: Span,
    ) -> Result<()> {
        for (destination, (leaves, argument)) in parameters.iter().zip(args.iter()).enumerate() {
            if !leaves
                .iter()
                .any(|leaf| leaf.path.is_empty() && leaf.mutable)
            {
                continue;
            }
            let element_leaves = leaves
                .iter()
                .filter(|leaf| leaf.path.first() == Some(&CONTAINER_LEAF))
                .collect::<Vec<_>>();
            if element_leaves.is_empty() {
                continue;
            }
            // A borrowed record behind the argument may be a field or element
            // of a local owner, or caller storage behind a parameter: resolve
            // the exact owner and field path, exactly as for `*r = value`.
            let record_referent = self.referent(argument.ty).is_some_and(|referent| {
                referent.layout().is_some_and(|id| self.enums[id].borrowed)
            });
            let (targets, existings) = if record_referent {
                let targets = self.record_write_targets(argument, span)?;
                let existings = if targets.is_empty() {
                    vec![self.declared_referent_provenance(argument.ty)?]
                } else {
                    targets
                        .iter()
                        .map(|(owner, prefix, _)| self.owner_leaves_under(*owner, prefix))
                        .collect()
                };
                (Some(targets), existings)
            } else {
                (None, vec![self.container_provenance(argument)])
            };
            let mut written = Vec::new();
            for existing in &existings {
                let mut merged = existing.clone();
                for element_leaf in &element_leaves {
                    let Some(declared) = element_leaf.lifetime.clone() else {
                        continue;
                    };
                    let relative = element_leaf.path[1..].to_vec();
                    let element_actual = existing
                        .leaves
                        .get(&relative)
                        .and_then(|loan| loan.lifetime.clone());
                    let mut element = existing.leaves.get(&relative).cloned().unwrap_or_default();
                    for (index, (other_leaves, other)) in
                        parameters.iter().zip(args.iter()).enumerate()
                    {
                        for leaf in other_leaves {
                            // Another argument's element or record leaves are
                            // sources too: the callee may copy a leaf out of
                            // a borrowed record or container it was given.
                            // The destination's own leaves are in `existing`.
                            if index == destination && leaf.path.first() == Some(&CONTAINER_LEAF) {
                                continue;
                            }
                            let Some(other_declared) = &leaf.lifetime else {
                                continue;
                            };
                            if !Self::callee_flows(bounds, other_declared, &declared) {
                                continue;
                            }
                            let Some(loan) = self.argument_leaf_loan(other, &leaf.path) else {
                                continue;
                            };
                            if let Some(actual) = &element_actual
                                && !is_internal_lifetime(actual)
                            {
                                let written = loan.lifetime.clone().or_else(|| {
                                    (!loan.origins.is_empty())
                                        .then(|| self.anonymous_lifetime(&loan.origins))
                                });
                                if !written
                                    .as_deref()
                                    .is_some_and(|written| self.actual_outlives(written, actual))
                                {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!(
                                            "this call would write {} into a container whose declared element lifetime is {}; the written reference must outlive the container's element lifetime",
                                            written.as_deref().map(describe_actual).unwrap_or_else(
                                                || "a temporary or local owner".to_owned()
                                            ),
                                            describe_actual(actual)
                                        ),
                                    ));
                                }
                            }
                            element = self.merge_loans([element, loan]);
                        }
                    }
                    merged.leaves.insert(relative, element);
                }
                written.push(merged);
            }
            match targets {
                None => {
                    let merged = written.pop().unwrap_or_default();
                    if !self.merge_container_provenance(argument, merged, false) {
                        return Err(untracked_write(span));
                    }
                }
                Some(targets) => {
                    for ((owner, prefix, _), merged) in targets.iter().zip(&written) {
                        let mut placed = RecordProvenance::default();
                        for (path, loan) in &merged.leaves {
                            let mut full = prefix.clone();
                            full.extend(path.iter().copied());
                            placed.leaves.insert(full, loan.clone());
                        }
                        self.merge_container_provenance_slot(*owner, placed, false);
                    }
                    // A stored reference argument also carries the new leaves.
                    let base = through_coerce(argument);
                    if let ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) =
                        &base.kind
                        && !targets.is_empty()
                        && let Some(merged) = written.first().cloned()
                    {
                        self.merge_container_provenance_slot(*slot, merged, false);
                    }
                }
            }
        }
        Ok(())
    }
    /// The leaves of a local owner under `prefix`, relative to that prefix.
    fn owner_leaves_under(&self, owner: usize, prefix: &[usize]) -> RecordProvenance {
        let mut existing = RecordProvenance::default();
        if let Some(provenance) = &self.record_sources[owner] {
            for (path, loan) in &provenance.leaves {
                if let Some(rest) = path.strip_prefix(prefix) {
                    existing.leaves.insert(rest.to_vec(), loan.clone());
                }
            }
        }
        existing
    }
    /// The declared leaf lifetimes of the record a reference type points at.
    /// For caller storage behind a parameter they are the only destination.
    fn declared_referent_provenance(&self, reference: Type) -> Result<RecordProvenance> {
        let mut provenance = RecordProvenance::default();
        if let Some(referent) = self.referent(reference) {
            for leaf in leaves_of(
                self.enums,
                self.pointees,
                self.reference_labels,
                self.variance,
                referent,
            )? {
                provenance.leaves.insert(
                    leaf.path,
                    Loan {
                        lifetime: leaf.lifetime,
                        mutable: leaf.mutable,
                        ..Loan::default()
                    },
                );
            }
        }
        Ok(provenance)
    }
    /// `*reference = value` for a record with borrowed fields. Every written
    /// leaf must outlive the destination's lifetime: a lifetime declared by
    /// this function is a rigid destination (lifetimes are invariant under
    /// `&mut`), otherwise the destination keeps the lifetime its current
    /// leaves already carry. The owner behind the reference then holds the
    /// new leaves under the written place's field path. Only a write to a
    /// whole owner through its one possible reference replaces leaves; a
    /// write to a field, a container element, or one of several possible
    /// owners merges them. The old leaves stay checked until the write, which
    /// happens after the value is evaluated.
    fn write_borrowed_record(
        &mut self,
        reference: &Expr,
        value: &Expr,
        referent: Type,
        span: Span,
    ) -> Result<()> {
        let expected = leaves_of(
            self.enums,
            self.pointees,
            self.reference_labels,
            self.variance,
            referent,
        )?;
        let incoming = self.borrowed_element_provenance(value);
        let targets = self.record_write_targets(reference, span)?;
        // A parameter reference has no local owner: its declared labels are
        // the destination and the caller merges the written leaves.
        let mut destinations = targets
            .iter()
            .map(|(owner, prefix, _)| self.owner_leaves_under(*owner, prefix))
            .collect::<Vec<_>>();
        if targets.is_empty() {
            destinations.push(self.declared_referent_provenance(reference.ty)?);
        }
        for existing in &destinations {
            for leaf in &expected {
                let Some(loan) = incoming.leaves.get(&leaf.path) else {
                    return Err(Diagnostic::new(
                        span,
                        "the borrowed record written through this reference is missing provenance for a declared borrowed field",
                    ));
                };
                if leaf.mutable && !loan.mutable {
                    return Err(Diagnostic::new(
                        span,
                        "an exclusive borrowed field cannot be replaced by a shared borrow; shared storage cannot be upgraded",
                    ));
                }
                let Some(declared) =
                    self.write_destination_label(leaf.lifetime.as_ref(), &leaf.path, existing)
                else {
                    continue;
                };
                let written = loan.lifetime.clone().or_else(|| {
                    (!loan.origins.is_empty()).then(|| self.anonymous_lifetime(&loan.origins))
                });
                if !written
                    .as_deref()
                    .is_some_and(|written| self.actual_outlives(written, &declared))
                {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "the record written through this '&mut' reference has a field with {}, which does not outlive the record's lifetime {}; lifetimes are invariant under '&mut', so the written source must live at least as long",
                            written
                                .as_deref()
                                .map(describe_actual)
                                .unwrap_or_else(|| "a temporary or local owner".to_owned()),
                            describe_lifetime(&declared)
                        ),
                    ));
                }
            }
        }
        let replace = targets.len() == 1 && targets[0].2;
        for (owner, prefix, _) in &targets {
            let mut placed = RecordProvenance::default();
            for (path, loan) in &incoming.leaves {
                let mut full = prefix.clone();
                full.extend(path.iter().copied());
                placed.leaves.insert(full, loan.clone());
            }
            self.merge_container_provenance_slot(*owner, placed, replace);
        }
        // A stored reference also carries the leaves it now points at, so a
        // field read through it keeps the written sources loaned.
        let base = through_coerce(reference);
        if let ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) = &base.kind
            && !targets.is_empty()
        {
            self.merge_container_provenance_slot(*slot, incoming, replace);
        }
        Ok(())
    }
    /// The local owners a borrowed-record write through `reference` reaches:
    /// `(owner, field path of the written record inside it, whole owner)`.
    /// An empty list means the reference is a parameter. A place whose field
    /// path cannot be identified is rejected rather than guessed.
    fn record_write_targets(
        &self,
        reference: &Expr,
        span: Span,
    ) -> Result<Vec<(usize, Vec<usize>, bool)>> {
        let unknown = || {
            Diagnostic::new(
                span,
                "cannot track which part of its owner this '&mut' reference replaces; write through '&mut' of the whole record, or of a record field of a local",
            )
        };
        // A place rooted at a reference parameter writes caller storage: the
        // declared labels check it and the caller merges the leaves. A place
        // rooted at a stored reference local is not tracked field by field.
        let parameter_reference =
            |slot: usize| slot < self.parameter_count && self.locals[slot].ty.is_ref();
        let place_target =
            |root: usize, path: Vec<usize>| -> Result<Vec<(usize, Vec<usize>, bool)>> {
                if parameter_reference(root) {
                    return Ok(Vec::new());
                }
                if self.locals[root].ty.is_ref() {
                    return Err(unknown());
                }
                let index = |step: &usize| step & (INDEX_PATH_MARK | RUNTIME_INDEX_MARK) != 0;
                if !path.iter().any(index) {
                    let whole = path.is_empty();
                    return Ok(vec![(root, path, whole)]);
                }
                // An element of a container of borrowed records: a container
                // adds no path step and its leaves are shared by every
                // element, so drop the index steps and merge.
                let prefix = path.into_iter().filter(|step| !index(step)).collect();
                Ok(vec![(root, prefix, false)])
            };
        let base = through_coerce(reference);
        match &base.kind {
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. } => {
                Ok(vec![(*slot, Vec::new(), true)])
            }
            ExprKind::BorrowPlace(place) => {
                let (root, path) = self.place_ident(place).ok_or_else(unknown)?;
                place_target(root, path)
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                if let Some(field) = &self.view_fields[*slot] {
                    return place_target(field.root, field.path.clone());
                }
                let owners = self
                    .view_loan(base)
                    .origins
                    .into_iter()
                    .filter(|owner| *owner != *slot)
                    .collect::<Vec<_>>();
                if owners.iter().all(|owner| parameter_reference(*owner)) {
                    return Ok(Vec::new());
                }
                let carriers = owners
                    .iter()
                    .copied()
                    .filter(|owner| self.is_carrier_type(self.locals[*owner].ty))
                    .collect::<Vec<_>>();
                let referent = self.referent(base.ty);
                // The same nominal record with the same type arguments: a
                // generic record nested in itself shares the definition, so
                // the definition alone does not identify the whole owner.
                let same = |owner: usize| {
                    let shape = |ty: Type| {
                        ty.layout()
                            .map(|id| (self.enums[id].definition, self.enums[id].arguments.clone()))
                    };
                    referent.is_some_and(|referent| {
                        shape(self.locals[owner].ty).is_some()
                            && shape(self.locals[owner].ty) == shape(referent)
                    })
                };
                if carriers.is_empty() || !carriers.iter().all(|owner| same(*owner)) {
                    return Err(unknown());
                }
                let whole = carriers.len() == 1;
                Ok(carriers
                    .into_iter()
                    .map(|owner| (owner, Vec::new(), whole))
                    .collect())
            }
            _ => Err(unknown()),
        }
    }
    /// Writing a reference into a container reached through a parameter whose
    /// element lifetime is elided has no destination label to check against:
    /// the element and the written source have independent caller lifetimes.
    /// Reject it and ask for a named lifetime rather than guess.
    fn check_elided_parameter_destination(
        &self,
        receiver: &Expr,
        expected: &[crate::runtime_types::BorrowLeaf],
        span: Span,
    ) -> Result<()> {
        let elided = expected
            .iter()
            .find(|leaf| leaf.path.is_empty())
            .is_some_and(|leaf| leaf.lifetime.is_none());
        if elided
            && self
                .view_origins(receiver)
                .iter()
                .any(|origin| *origin < self.parameter_count)
        {
            return Err(Diagnostic::new(
                span,
                "cannot write a reference into a parameter's container whose element lifetime is elided; name it and relate the written source to it, as in 'fn f<'a>(v: &mut Vec<&'a T>, x: &'a T)'",
            ));
        }
        Ok(())
    }
    fn argument_leaf_loan(&self, argument: &Expr, path: &[usize]) -> Option<Loan> {
        if let Some(rest) = path.strip_prefix(&[CONTAINER_LEAF]) {
            if let Some(loan) = self.container_provenance(argument).leaves.get(rest) {
                return Some(loan.clone());
            }
            // Caller storage behind a reference parameter has no per-leaf
            // provenance here: its leaf is the parameter's declared lifetime,
            // rooted at the reference itself.
            let declared = self.declared_referent_provenance(argument.ty).ok()?;
            let leaf = declared.leaves.get(rest)?;
            return Some(Loan {
                origins: self.view_origins(argument),
                mutable: leaf.mutable,
                lifetime: leaf.lifetime.clone(),
                ..Loan::default()
            });
        }
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
        // The binding itself, not the storage behind its element references, is
        // the storage root for borrowing the whole container. Leaf owners stay
        // loaned through `view_sources`, while `&mut container` does not alias
        // an element's referent.
        self.view_roots[slot] = Some(BTreeSet::from([slot]));
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
                if ty.is_view() {
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
            Pattern::Variant { tag, fields, .. } => {
                if let Some(id) = ty.layout()
                    && let Some(reference) = self.enums[id].optional_reference()
                {
                    let niche = self.enums[id].niche().expect("optional reference niche");
                    if *tag == niche.payload_tag {
                        for (_, inner) in fields {
                            self.bind_pattern_provenance(inner, reference, provenance)?;
                        }
                    }
                    return Ok(());
                }
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
            Pattern::Variant { tag, fields, .. } => {
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
                            self.pointees,
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
    /// A live scoped closure captures this scalar storage. Used to give the
    /// loan conflict a closure-specific diagnostic.
    fn live_scalar_capture(&self, source: usize, ptr: usize) -> bool {
        self.live_views_at(ptr).iter().any(|view| {
            self.available[*view]
                && self.borrowed_closures.contains_key(view)
                && self.derives_from(*view, source)
        })
    }
    fn has_live_descendant(&self, source: usize, ptr: usize, mutable_only: bool) -> bool {
        self.live_views_at(ptr).iter().any(|view| {
            // A view that is not available here was moved, or is the binding
            // currently being initialized. Neither is an active capability.
            self.available[*view]
                && self.derives_from(*view, source)
                && (!mutable_only
                    || self
                        .borrowed_closures
                        .get(view)
                        .map_or(self.view_mut[*view], |capture| {
                            capture.exclusive_origins.contains(&source)
                        }))
        })
    }
    /// A write through `*r = ...` or `r.field = ...` replaces storage that
    /// views, element references, and borrowed-pattern bindings derived from
    /// `r` may still observe. This also covers reference parameters, whose
    /// ordinary capability suspension is not tracked as a local view.
    fn check_write_through_reference(
        &self,
        reference: &Expr,
        ptr: usize,
        span: Span,
    ) -> Result<()> {
        let (ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)) =
            &through_coerce(reference).kind
        else {
            return Ok(());
        };
        if self.has_live_descendant(*slot, ptr, false) {
            return Err(Diagnostic::new(
                span,
                "cannot write through a reference while a view, element reference, or pattern binding derived from it is live; wait until that borrow's last use",
            )
            .with_note(self.locals[*slot].span, "reference declared here"));
        }
        Ok(())
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
            if self.place_borrow && self.slice_place_root == Some(slot) {
                // Reaching one element of this view: `check_view_creation`
                // compares the element place with every live child of the
                // view, so references to provably distinct elements coexist.
                return Ok(());
            }
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
            if self.place_borrow {
                // The enclosing place borrow checks the exact field against
                // every retained/live child capability afterwards.
                return Ok(());
            }
            if let Some(target) = &self.field_target
                && target.root == slot
                && (self.is_carrier_type(self.locals[slot].ty)
                    || self.locals[slot]
                        .ty
                        .layout()
                        .is_some_and(|id| self.enums[id].record))
                && self.field_access_isolated(slot, target, ptr)
            {
                // Reading the record only to reach a field whose live child
                // views are all structurally disjoint from that field does not
                // alias any exclusive field capability.
                return Ok(());
            }
            if crate::executable::is_live_scalar(self.locals[slot].ty)
                && self.live_scalar_capture(slot, ptr)
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot {what} a scalar location while a closure that exclusively captures it is live; call the closure first or move this access before its last use"
                    ),
                )
                .with_note(self.locals[slot].span, "captured location declared here"));
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
        if self.exclusive_loans.contains(&record) {
            return false;
        }
        // A sibling field borrow retained by the same expression is isolated
        // only when its structural place is disjoint from this one.
        for retained in &self.temporary_regions {
            if (retained.origins.contains(&record) || retained.roots.contains(&record))
                && !retained
                    .field
                    .as_ref()
                    .is_some_and(|field| field.disjoint(target, &self.index_relations))
            {
                return false;
            }
        }
        self.live_views_at(ptr).iter().all(|view| {
            !self.available[*view]
                || !self.derives_from(*view, record)
                || self.view_fields[*view]
                    .as_ref()
                    .is_some_and(|field| field.disjoint(target, &self.index_relations))
        })
    }
    /// Owners behind one loan for a return check. An ancestor record root that
    /// was added only because a field is a borrowed leaf stays loaned for every
    /// ordinary use, but it does not own the returned storage: the leaf's own
    /// origins are the owners. Owned field projections have no ancestor mark,
    /// so their record binding is still checked as storage.
    fn loan_return_origins(&self, loan: &Loan) -> BTreeSet<usize> {
        let mut origins = loan.origins.clone();
        if let Some(ancestor) = loan.ancestor {
            origins.remove(&ancestor);
        }
        origins
    }
    /// Owners of a returned view/reference expression, using the same
    /// ancestor rule as [`Self::loan_return_origins`].
    fn return_origins(&self, expr: &Expr) -> BTreeSet<usize> {
        let loan = self.view_loan(expr);
        self.loan_return_origins(&loan)
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
            ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. }
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
                if expr.ty.is_ref() =>
            {
                out.insert(*slot);
                if let Some(origins) = &self.view_sources[*slot] {
                    out.extend(origins.iter().copied());
                }
            }
            ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. }
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
                if self.locals[*slot].ty.is_view() =>
            {
                out.insert(*slot);
                if let Some(origins) = &self.view_sources[*slot] {
                    out.extend(origins.iter().copied());
                }
            }
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. }
                if matches!(expr.ty, Type::Ref(_))
                    && self.is_carrier_type(self.locals[*slot].ty) =>
            {
                // A shared `&record` also exposes the record's borrowed leaves.
                out.insert(*slot);
                if let Some(provenance) = &self.record_sources[*slot] {
                    for leaf in provenance.leaves.values() {
                        out.extend(leaf.origins.iter().copied());
                    }
                }
            }
            ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. }
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::Local(slot)
            | ExprKind::Move(slot) => {
                out.insert(*slot);
            }
            ExprKind::Slice { base, .. } => self.collect_view_origins(base, out),
            ExprKind::Project(..)
                if expr.ty.is_view()
                    || expr.ty.is_ref()
                    || expr
                        .ty
                        .layout()
                        .is_some_and(|id| self.enums[id].dynamic_array.is_some()) =>
            {
                let origins = self.view_loan(expr).origins;
                if origins.is_empty() {
                    // A DynArray field view of a hoisted temporary record has
                    // no recorded field provenance; its storage is the hidden
                    // owner at the projection root.
                    let mut root = expr;
                    while let ExprKind::Project(base, _) = &root.kind {
                        root = base;
                    }
                    if let ExprKind::InitOwner { slot, .. } = &root.kind {
                        out.insert(*slot);
                    }
                } else {
                    out.extend(origins.iter().copied());
                }
            }
            ExprKind::BorrowPlace(place) => {
                out.extend(self.place_loan(place).origins.iter().copied());
            }
            ExprKind::Coerce { value, .. } | ExprKind::AbortCall { call: value, .. } => {
                self.collect_view_origins(value, out)
            }
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
            // An element reference derived from a view (`&mut side[i]`, or a
            // `&mut DynArray` pattern binding) keeps that view's split sides.
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. }
                if self.locals[*slot].ty.is_view()
                    || (self.locals[*slot].ty.is_ref() && self.view_sources[*slot].is_some()) =>
            {
                self.view_splits[*slot].clone()
            }
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::BorrowInit { slot, .. } => {
                let _ = slot;
                SplitLabels::default()
            }
            ExprKind::Project(..) if expr.ty.is_slice() => self.view_loan(expr).splits,
            ExprKind::BorrowPlace(place) => self.place_loan(place).splits,
            ExprKind::Coerce { value, .. } | ExprKind::AbortCall { call: value, .. } => {
                self.split_labels(value)
            }
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
                .is_some_and(|(new, old)| new.disjoint(old, &self.index_relations));
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
            // A live record or container holds its leaves' loans: a stored
            // `&mut` element (or a mutable slice field) keeps its owner
            // exclusively borrowed, and a stored shared leaf excludes a new
            // exclusive borrow. The holder's own root is only its binding.
            if let Some(provenance) = &self.record_sources[*view] {
                for leaf in provenance.leaves.values() {
                    if leaf.origins.is_empty()
                        || self.origins_roots(&leaf.origins).is_disjoint(&roots)
                        || splits.disjoint(&leaf.splits)
                    {
                        continue;
                    }
                    if mutable || leaf.mutable {
                        return Err(Diagnostic::new(
                            span,
                            "cannot borrow storage that a live record or container still holds a conflicting reference to; use or drop that value first",
                        )
                        .with_note(self.locals[*view].span, "holder declared here"));
                    }
                }
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
                .is_some_and(|(new, old)| new.disjoint(old, &self.index_relations))
            {
                // Structurally disjoint fields of one local record are
                // separate loan capabilities. Neither can reach the other's
                // storage, and the record itself stays suspended for moves.
                continue;
            }
            let exclusive_overlap =
                self.borrowed_closures
                    .get(view)
                    .map_or(self.view_mut[*view], |capture| {
                        !self
                            .origins_roots(&capture.exclusive_origins)
                            .is_disjoint(&roots)
                    });
            if mutable || exclusive_overlap {
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
        let internal = is_internal_lifetime(lifetime);
        if !internal && !view_lifetime.is_some_and(|view| self.actual_outlives(view, lifetime)) {
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
            if internal {
                // An inferred multi-source result has no caller-nameable
                // lifetime. It may return any parameter-derived view; the call
                // site unions every source loan, so no owner can be moved while
                // the result is live, and the view cannot be named as a caller
                // lifetime.
                if *origin < self.parameter_count {
                    if !self.parameter_has_borrow_capability(*origin) {
                        return Err(Diagnostic::new(
                            span,
                            "borrowed return would dangle: the returned view does not name a borrowed parameter",
                        )
                        .with_note(self.locals[*origin].span, "borrowed storage declared here"));
                    }
                    if mutable && !self.parameter_is_mutable_capability(*origin)? {
                        return Err(Diagnostic::new(
                            span,
                            "an exclusive '&mut [T]' return cannot derive from a shared parameter",
                        )
                        .with_note(self.locals[*origin].span, "shared storage declared here"));
                    }
                } else if self.is_local_view(*origin) {
                    if mutable && !self.view_mut[*origin] {
                        return Err(Diagnostic::new(
                            span,
                            "an exclusive '&mut [T]' return cannot derive from a shared child view",
                        )
                        .with_note(self.locals[*origin].span, "shared view declared here"));
                    }
                    for root in self.roots_of(*origin) {
                        if root >= self.parameter_count
                            || !self.parameter_has_borrow_capability(root)
                        {
                            return Err(Diagnostic::new(
                                span,
                                "borrowed return would dangle: the returned view borrows a stack local or temporary",
                            )
                            .with_note(self.locals[root].span, "borrowed storage declared here"));
                        }
                        if mutable && !self.parameter_is_mutable_capability(root)? {
                            return Err(Diagnostic::new(
                                span,
                                "an exclusive '&mut [T]' return cannot derive from shared parameter storage",
                            )
                            .with_note(self.locals[root].span, "shared storage declared here"));
                        }
                    }
                } else {
                    return Err(Diagnostic::new(
                        span,
                        "borrowed return would dangle: the returned view borrows a stack local or temporary",
                    )
                    .with_note(self.locals[*origin].span, "borrowed storage declared here"));
                }
                continue;
            }
            if *origin < self.parameter_count {
                let element = &self.locals[*origin];
                if !self.parameter_carries_lifetime(*origin, lifetime, mutable)? {
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
        let internal = is_internal_lifetime(lifetime);
        if !internal && !view_lifetime.is_some_and(|view| self.actual_outlives(view, lifetime)) {
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
            if internal {
                // Inferred multi-source reference result: any parameter-derived
                // reference is allowed, and the caller keeps every source
                // loaned. The anonymous result cannot name a caller lifetime.
                if *origin < self.parameter_count {
                    if !self.parameter_has_borrow_capability(*origin) {
                        return Err(Diagnostic::new(
                            span,
                            "returned reference would dangle: it does not name a borrowed parameter",
                        )
                        .with_note(self.locals[*origin].span, "borrowed storage declared here"));
                    }
                    if mutable && !self.parameter_is_mutable_capability(*origin)? {
                        return Err(Diagnostic::new(
                            span,
                            "an exclusive reference return cannot derive from a shared parameter",
                        )
                        .with_note(self.locals[*origin].span, "shared storage declared here"));
                    }
                } else if self.is_local_view(*origin) {
                    if mutable && !self.view_mut[*origin] {
                        return Err(Diagnostic::new(
                            span,
                            "an exclusive reference return cannot derive from a shared stored reference",
                        )
                        .with_note(self.locals[*origin].span, "shared reference declared here"));
                    }
                    for root in self.roots_of(*origin) {
                        if root >= self.parameter_count
                            || !self.parameter_has_borrow_capability(root)
                        {
                            return Err(Diagnostic::new(
                                span,
                                "returned reference would dangle: it is reborrowed from a stack local or by-value parameter",
                            )
                            .with_note(self.locals[root].span, "borrowed storage declared here"));
                        }
                        if mutable && !self.parameter_is_mutable_capability(root)? {
                            return Err(Diagnostic::new(
                                span,
                                "an exclusive reference return cannot derive from shared parameter storage",
                            )
                            .with_note(self.locals[root].span, "shared storage declared here"));
                        }
                    }
                } else {
                    return Err(Diagnostic::new(
                        span,
                        "returned reference would dangle: it borrows a stack local, a record value, or another non-reference place",
                    )
                    .with_note(self.locals[*origin].span, "borrowed storage declared here"));
                }
                continue;
            }
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
                    // A slice view parameter is caller storage: an element
                    // reference `&s[i]` may be returned with its lifetime.
                    if root >= self.parameter_count
                        || (!self.locals[root].ty.is_ref()
                            && !self.locals[root].ty.is_slice()
                            && !self.is_carrier_type(self.locals[root].ty))
                    {
                        return Err(Diagnostic::new(
                            span,
                            "returned reference would dangle: it is reborrowed from a stack local, a by-value parameter, or another non-reference place",
                        )
                        .with_note(self.locals[root].span, "borrowed storage declared here"));
                    }
                    if !self.parameter_carries_lifetime(root, lifetime, mutable)? {
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
                    && !self.locals[*origin].ty.is_slice()
                    && !self.is_carrier_type(self.locals[*origin].ty))
            {
                return Err(Diagnostic::new(
                    span,
                    "returned reference would dangle: it borrows a stack local, a record value, or another non-reference place",
                )
                .with_note(self.locals[*origin].span, "borrowed storage declared here"));
            }
            if !self.parameter_carries_lifetime(*origin, lifetime, mutable)? {
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
            self.variance,
            self.result_type,
        )?;
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
                    "a returned record field carries a borrowed value but no resolved lifetime label; annotate the field with a lifetime from a parameter, as in 'struct { view: &'a [T] }', or preserve it through a '..r' row variable",
                ));
            };
            if !self.lifetime_carried_at(loan.lifetime.as_deref(), lifetime, leaf.variance) {
                let failing = provenance
                    .alternatives
                    .get(&leaf.path)
                    .map(|alternatives| {
                        alternatives
                            .iter()
                            .filter(|alternative| {
                                !self.lifetime_carried_at(
                                    Some(alternative),
                                    lifetime,
                                    leaf.variance,
                                )
                            })
                            .map(|alternative| display_actual_lifetime(alternative))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                let actual = if failing.is_empty() {
                    loan.lifetime
                        .as_deref()
                        .map(display_actual_lifetime)
                        .unwrap_or_else(|| "a temporary or local owner".to_owned())
                } else {
                    failing.join(" or ")
                };
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "returned borrowed record field has lifetime {actual}, which does not satisfy the declared result lifetime '{lifetime}' at its {} occurrence",
                        describe_variance(leaf.variance)
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
            for origin in self.loan_return_origins(loan) {
                self.check_return_origin(origin, lifetime, leaf.mutable, leaf.variance, span)?;
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
    /// Whether a parameter can supply a borrow at all. Used for inferred
    /// anonymous results, which are not tied to a named lifetime.
    fn parameter_has_borrow_capability(&self, slot: usize) -> bool {
        let ty = self.locals[slot].ty;
        ty.is_view() || ty.is_ref() || self.is_carrier_type(ty)
    }
    /// Whether a parameter supplies exclusive storage.
    fn parameter_is_mutable_capability(&self, slot: usize) -> Result<bool> {
        let ty = self.locals[slot].ty;
        Ok(ty.is_mut_slice()
            || matches!(ty, Type::RefMut(_))
            || (self.is_carrier_type(ty)
                && leaves_of(
                    self.enums,
                    self.pointees,
                    self.reference_labels,
                    self.variance,
                    ty,
                )?
                .iter()
                .any(|leaf| leaf.mutable)))
    }
    /// Whether a parameter carries `lifetime` with a compatible capability for
    /// a returned view. An exclusive result requires an exclusive parameter or
    /// an exclusive record-field leaf; a shared result may narrow either.
    fn parameter_carries_lifetime(
        &self,
        slot: usize,
        lifetime: &str,
        mutable: bool,
    ) -> Result<bool> {
        self.parameter_carries_lifetime_at(
            slot,
            lifetime,
            mutable,
            crate::variance::SignSet::POSITIVE,
        )
    }
    fn parameter_carries_lifetime_at(
        &self,
        slot: usize,
        lifetime: &str,
        mutable: bool,
        variance: crate::variance::SignSet,
    ) -> Result<bool> {
        let local = &self.locals[slot];
        if local.ty.is_ref() {
            return Ok(self
                .reference_lifetimes
                .get(slot)
                .and_then(|name| name.as_ref())
                .is_some_and(|name| self.lifetime_carried_at(Some(name), lifetime, variance))
                && (!mutable || matches!(local.ty, Type::RefMut(_))));
        }
        if local.ty.is_view() {
            return Ok(self
                .parameter_lifetimes
                .get(slot)
                .and_then(|l| l.as_ref())
                .is_some_and(|name| self.lifetime_carried_at(Some(name), lifetime, variance))
                && (!mutable || local.ty.is_mut_slice()));
        }
        if self.is_carrier_type(local.ty) {
            return Ok(leaves_of(
                self.enums,
                self.pointees,
                self.reference_labels,
                self.variance,
                local.ty,
            )?
            .iter()
            .any(|leaf| {
                leaf.lifetime
                    .as_deref()
                    .is_some_and(|name| self.lifetime_carried_at(Some(name), lifetime, variance))
                    && (!mutable || leaf.mutable)
            }));
        }
        Ok(false)
    }
    fn check_return_origin(
        &self,
        origin: usize,
        lifetime: &str,
        mutable: bool,
        variance: crate::variance::SignSet,
        span: Span,
    ) -> Result<()> {
        if origin < self.parameter_count {
            let local = &self.locals[origin];
            if !self.parameter_carries_lifetime_at(origin, lifetime, mutable, variance)? {
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
                if !self.parameter_carries_lifetime(root, lifetime, mutable)? {
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
            ExprKind::Call(crate::executable::Target::Function(index), _) => self
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
                                self.dyn_linear,
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
            ExprKind::DynArrayFill { length, value, .. } => {
                self.value_moves_linear(length) || self.value_moves_linear(value)
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
            ExprKind::DynArrayEqual { left, right, .. } => {
                self.value_moves_linear(left) || self.value_moves_linear(right)
            }
            ExprKind::HandlerPush { body, .. } => self.block_value_moves_linear(body),
            ExprKind::AbortScope { body, .. } => self.block_value_moves_linear(body),
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
            ExprKind::Coerce { value, .. } | ExprKind::AbortCall { call: value, .. } => {
                self.value_moves_linear(value)
            }
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
        for (_, state) in &mut self.aborts {
            state.bound.push(slot);
        }
    }
    /// Establish a freshly initialized binding: check its initializer, carry
    /// linear obligations, acquire view/record/reference provenance, and make
    /// the slot available. Shared by ordinary `let` statements and hidden
    /// temporary-owner initialization, which must behave the same way even
    /// though its initializer runs inside an expression.
    fn establish_local(&mut self, slot: usize, expr: &mut Expr) -> Result<()> {
        // Elaboration tracks later assignments for capture typing. Start this
        // binding with its declaration's obligation, not a flag inherited from
        // a future replacement value.
        self.locals[slot].linear = self.locals[slot]
            .grade
            .is_some_and(crate::grades::Grade::is_one)
            && self.moves(self.locals[slot].ty);
        // Moving a linear binding into an ungraded local must not launder away
        // its consumption obligation.
        let linear = self.value_moves_linear(expr);
        // A borrowed-capture closure is only constructed directly as this
        // binding's initializer.
        let site = through_coerce(expr);
        let site_pointer = site as *const Expr as usize;
        let capture_site = matches!(site.kind, ExprKind::FnValue { .. }).then_some(site_pointer);
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
            // A stored reference is a lexical capability over its source
            // storage. It owns nothing at runtime: the one-word pointer is the
            // checked runtime value. The lifetime is the source's declared
            // lifetime when the reference came from a parameter or a call
            // result, and a frame-local identity otherwise so an escape remains
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
                    "cannot bind this reference: the storage it borrows cannot be tracked through this expression (for example a 'break' value); create the reference where it is used",
                ));
            }
            let lifetime = loan
                .lifetime
                .clone()
                .or_else(|| Some(self.anonymous_lifetime(&origins)));
            let mutable = matches!(self.locals[slot].ty, Type::RefMut(_));
            let field = loan.field.clone();
            // An element reference into one side of a checked split keeps
            // that side's label, so references into opposite sides coexist.
            let splits = self.split_labels(expr);
            self.acquire_view(slot, mutable, origins, splits, lifetime.clone(), field);
            self.reference_lifetimes[slot] = lifetime;
            if self.referent(self.locals[slot].ty).is_some_and(|referent| {
                self.is_carrier_type(referent)
                    || container_carries_borrow(self.enums, self.pointees, referent)
            }) {
                self.record_sources[slot] =
                    Some(stripped_provenance(self.container_provenance(expr)));
            }
        } else if let Some(provenance) = self.task_results.get(&site_pointer).cloned() {
            // A child task's borrowed-record result is still loaned to the
            // scope; the handle carries the provenance until Task.join
            // transfers it to the TaskExit value.
            self.task_sources[slot] = Some(provenance);
        } else if let Some(provenance) = self
            .wrapped_results
            .get(&site_pointer)
            .cloned()
            .or(inherited_wrapped)
        {
            // Copying or moving a TaskExit value that wraps a borrowed record
            // keeps the same loan provenance.
            self.wrapped_locals[slot] = Some(provenance);
        } else if let Some(capture) = self.borrowed_values.get(&site_pointer).cloned() {
            // The closure value is now a scoped loan holder. Its captures point
            // at the original owners, and the backward liveness pass keeps this
            // capability live until its last call or enclosing-scope end.
            self.acquire_view(
                slot,
                !capture.exclusive_origins.is_empty(),
                capture.origins.clone(),
                capture.splits.clone(),
                None,
                None,
            );
            self.borrowed_closures.insert(slot, capture);
        }
        self.available[slot] = true;
        self.moved_at[slot] = None;
        self.bound(slot);
        Ok(())
    }
    /// Check one direct local borrow after its storage is available.
    fn check_local_borrow(
        &mut self,
        slot: usize,
        reference: Type,
        expr_ptr: usize,
        span: Span,
    ) -> Result<()> {
        if !self.available[slot] {
            return Err(self.use_after_move(slot, span, "cannot borrow a moved owner"));
        }
        self.check_owner_access(slot, expr_ptr, span, "borrow")?;
        let owner_ty = self.locals[slot].ty;
        let record = owner_ty.layout().is_some_and(|id| self.enums[id].record)
            || matches!(owner_ty, Type::DynObj(_) | Type::Union(_));
        // Records, trait objects (open or closed-union), and owning handles all
        // have stable caller-visible storage borrowed in place, so a `&mut`
        // borrow suspends the owner and a shared borrow blocks exclusive
        // aliases.
        let owner = record
            || matches!(
                owner_ty,
                Type::Box(_)
                    | Type::Arena
                    | Type::ArenaBox(_)
                    | Type::Bytes
                    | Type::String
                    | Type::Vec(_)
            );
        if owner {
            if matches!(reference, Type::RefMut(_)) {
                if self.loans.contains(&slot)
                    || self.temporary_shared.contains(&slot)
                    || self.temporary_exclusive.contains(&slot)
                    || self.any_loan_at(slot, expr_ptr)
                {
                    return Err(Diagnostic::new(
                        span,
                        "cannot create an exclusive '&mut Record' (or '&mut dyn') borrow while another borrow or view of the same owner is live",
                    )
                    .with_note(self.locals[slot].span, "owner declared here"));
                }
                self.temporary_exclusive.insert(slot);
                if record {
                    self.exclusive_loans.insert(slot);
                }
            } else {
                if self.exclusive_loaned_at(slot, expr_ptr) {
                    return Err(Diagnostic::new(
                        span,
                        "cannot create a shared '&Record' (or '&dyn') borrow while an exclusive borrow of the same owner is live",
                    )
                    .with_note(self.locals[slot].span, "owner declared here"));
                }
                self.temporary_shared.insert(slot);
                if record {
                    self.shared_record_loans.insert(slot);
                }
            }
        }
        self.loans.insert(slot);
        Ok(())
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
        let splits = self.split_labels(expr);
        let mutable = expr.ty.is_mut_slice() || matches!(expr.ty, Type::RefMut(_));
        let field = self.view_loan(expr).field;
        // `&mut record` is exclusive over the record and its exclusive leaves,
        // but only shared over the storage behind its shared leaves: through
        // the reference a shared leaf can be read or replaced, never written.
        // Every leaf of the referent is lent for the call too, including the
        // leaves of a record reached through a stored `&mut` reference.
        if matches!(expr.ty, Type::RefMut(_))
            && self
                .referent(expr.ty)
                .is_some_and(|referent| self.is_carrier_type(referent))
        {
            let provenance = self.container_provenance(expr);
            let exclusive = provenance
                .leaves
                .values()
                .filter(|loan| loan.mutable)
                .flat_map(|loan| loan.origins.iter().copied())
                .collect::<BTreeSet<_>>();
            let shared_sources = provenance
                .leaves
                .values()
                .filter(|loan| !loan.mutable)
                .flat_map(|loan| loan.origins.iter().copied())
                .filter(|origin| !exclusive.contains(origin))
                .collect::<BTreeSet<_>>();
            let exclusive_origins = origins
                .iter()
                .chain(&exclusive)
                .copied()
                .filter(|origin| !shared_sources.contains(origin))
                .collect::<BTreeSet<_>>();
            self.retain_region(expr, exclusive_origins, splits.clone(), true, field.clone())?;
            if shared_sources.is_empty() {
                return Ok(());
            }
            return self.retain_region(expr, shared_sources, splits, false, None);
        }
        if let Some(slot) = receiver {
            self.reborrowed_views.insert(slot);
        }
        self.retain_region(expr, origins, splits, mutable, field)
    }
    /// Retain one view region for the rest of the enclosing expression, or
    /// reject an overlap with a region already retained by it.
    fn retain_region(
        &mut self,
        expr: &Expr,
        origins: BTreeSet<usize>,
        splits: SplitLabels,
        mutable: bool,
        field: Option<FieldBorrow>,
    ) -> Result<()> {
        let roots = self.origins_roots(&origins);
        for retained in &self.temporary_regions {
            let overlaps = origins.iter().any(|slot| retained.origins.contains(slot))
                || roots.iter().any(|root| retained.roots.contains(root));
            let fields_disjoint = field
                .as_ref()
                .zip(retained.field.as_ref())
                .is_some_and(|(new, old)| new.disjoint(old, &self.index_relations));
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
                    self.establish_local(slot, expr)?;
                    if borrowed_temporaries.contains(&slot) {
                        self.retain_local(slot);
                    }
                    slots.push(slot);
                }
                Statement::Declare(slot) => {
                    // Hidden temporary-owner storage. The initializer runs
                    // later, at its source position; declaration contributes
                    // lexical cleanup and loop-break cleanup only.
                    let slot = *slot;
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
                            self.dyn_linear,
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
            && (tail.ty.is_view() || tail.ty.is_ref() || self.is_carrier_type(tail.ty))
        {
            let origins = if tail.ty.is_view() || tail.ty.is_ref() {
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
                    if tail.ty.is_view() {
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
        // A call may have written a borrow of a block-local owner into an
        // outer container through `&mut`. The outer container now keeps that
        // owner loaned, so the block cannot end while the container is live.
        // Views declared inside this same block die with it and are not
        // escapes.
        let block_start = block
            .statements
            .first()
            .map(|statement| match statement {
                Statement::Let(_, expr) | Statement::Expr(expr) => expr.span.start,
                Statement::Declare(slot) => self.locals[*slot].span.start,
            })
            .or_else(|| block.tail.as_ref().map(|tail| tail.span.start))
            .unwrap_or(0);
        for slot in &slots {
            if !self.available[*slot] {
                continue;
            }
            let escapes = self.view_sources.iter().enumerate().any(|(view, sources)| {
                !slots.contains(&view)
                    && self.locals[view].span.start < block_start
                    && self.available[view]
                    && sources
                        .as_ref()
                        .is_some_and(|sources| sources.contains(slot))
            });
            if escapes {
                return Err(Diagnostic::new(
                    block_span(block),
                    "borrow escapes the lexical scope of its owner: an outer container was updated with a reference to this block-local value",
                )
                .with_note(self.locals[*slot].span, "owner declared here"));
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
        self.cleanup_list_for(self.loops.last().unwrap())
    }
    fn cleanup_list_for(&self, state: &LoopState) -> Vec<usize> {
        let mut ids = (state.resource_start..self.resources.len()).collect::<Vec<_>>();
        ids.extend(state.bound.iter().filter_map(|s| self.local_resources[*s]));
        ids.sort_unstable();
        ids.dedup();
        ids.reverse();
        ids
    }
    fn loop_state(&self) -> LoopState {
        LoopState {
            pending_linear_start: self.pending_linear.len(),
            entry: self.available.clone(),
            entry_linear: (0..self.locals.len())
                .map(|slot| self.slot_linear(slot))
                .collect(),
            breaks: None,
            result_provenance: Vec::new(),
            resource_start: self.resources.len(),
            bound: Vec::new(),
        }
    }
    fn enter_loop(&mut self) {
        self.loops.push(LoopState {
            pending_linear_start: self.pending_linear.len(),
            entry: self.available.clone(),
            entry_linear: (0..self.locals.len())
                .map(|slot| self.slot_linear(slot))
                .collect(),
            breaks: None,
            result_provenance: Vec::new(),
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
                        "a closure with borrowed captures (slices, by-reference scalars or capabilities) is scoped: call it directly at this binding's scope, or pass no borrowed captures. It cannot be moved, returned, stored, captured, or passed to another function",
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
                self.check_local_borrow(*slot, expr.ty, expr_ptr, expr.span)?;
            }
            ExprKind::InitOwner { slot, value } => {
                // Hidden backing storage is initialized exactly once at this
                // source position; the slot then behaves like a local place.
                self.establish_local(*slot, value)?;
            }
            ExprKind::BorrowInit { slot, value } => {
                // A temporary owner is initialized at the operand position and
                // then borrowed with the same rules as a direct local.
                self.establish_local(*slot, value)?;
                self.check_local_borrow(*slot, expr.ty, expr_ptr, expr.span)?;
            }
            ExprKind::BorrowPlace(place) => {
                let old_place_borrow = self.place_borrow;
                self.place_borrow = true;
                let old_root = std::mem::replace(
                    &mut self.slice_place_root,
                    slice_place_view(place).and_then(|view| match &view.kind {
                        ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                            Some(*slot)
                        }
                        _ => None,
                    }),
                );
                let checked = self.expr(place);
                self.place_borrow = old_place_borrow;
                self.slice_place_root = old_root;
                checked?;
                let mutable = matches!(expr.ty, Type::RefMut(_));
                let loan = self.place_loan(place);
                if loan.origins.is_empty() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: place borrow has no capability provenance",
                    ));
                }
                for origin in &loan.origins {
                    if *origin >= self.available.len() {
                        continue;
                    }
                    if !self.available[*origin] {
                        return Err(self.use_after_move(
                            *origin,
                            expr.span,
                            "cannot borrow a field of a moved owner",
                        ));
                    }
                }
                if self
                    .check_view_creation(
                        &loan.origins,
                        mutable,
                        &loan.splits,
                        loan.field.as_ref(),
                        expr_ptr,
                        expr.span,
                    )
                    .is_err()
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        if mutable {
                            "cannot create an exclusive place borrow while an overlapping borrow or view of the same owner is live; use structurally disjoint fields or wait until the previous loan's last use"
                        } else {
                            "cannot create a shared place borrow while an exclusive borrow of the same owner is live; use a structurally disjoint field or wait until the exclusive loan's last use"
                        },
                    ));
                }
                if mutable {
                    for origin in &loan.origins {
                        self.temporary_exclusive.insert(*origin);
                    }
                } else {
                    for origin in &loan.origins {
                        self.temporary_shared.insert(*origin);
                        if self.locals[*origin]
                            .ty
                            .layout()
                            .is_some_and(|id| self.enums[id].record)
                        {
                            self.shared_record_loans.insert(*origin);
                        }
                    }
                }
                self.loans.extend(loan.origins.iter().copied());
            }
            ExprKind::PlaceIndex { base, index, .. } => {
                self.expr(base)?;
                // The index is an ordinary read: it may not touch storage that
                // a live exclusive borrow of the place's owner still covers.
                let old_place_borrow = std::mem::replace(&mut self.place_borrow, false);
                let old_root = self.slice_place_root.take();
                let checked = self.expr(index);
                self.place_borrow = old_place_borrow;
                self.slice_place_root = old_root;
                checked?;
            }
            ExprKind::DerefWrite(reference, value) => {
                if !matches!(reference.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: dereference write requires an exclusive reference",
                    ));
                }
                if self.value_moves_linear(value) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot replace a borrowed place with a linear value whose obligation would be laundered",
                    ));
                }
                self.check_write_through_reference(reference, expr_ptr, expr.span)?;
                self.expr(reference)?;
                self.expr(value)?;
                if let Some(referent) = self.referent(reference.ty)
                    && referent.layout().is_some_and(|id| self.enums[id].borrowed)
                {
                    self.write_borrowed_record(reference, value, referent, expr.span)?;
                }
            }
            ExprKind::Block(block) => self.block(block)?,
            ExprKind::Coerce { value, .. } => self.expr(value)?,
            ExprKind::Unary(_, value) => self.expr(value)?,
            ExprKind::BoxTake(value) => {
                self.expr(value)?;
                if self.is_carrier_type(expr.ty) {
                    // A boxed borrowed record transfers its per-field element
                    // provenance to the consumed value.
                    self.call_records
                        .insert(expr_ptr, self.container_provenance(value));
                } else if expr.ty.is_ref() || expr.ty.is_view() {
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
                if value.ty.is_ref() || value.ty.is_view() {
                    let loan = self.view_loan(value);
                    let mut provenance = RecordProvenance::default();
                    provenance.leaves.insert(Vec::new(), loan);
                    self.call_records.insert(expr_ptr, provenance);
                } else if self.is_carrier_type(value.ty) {
                    self.call_records
                        .insert(expr_ptr, self.borrowed_element_provenance(value));
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
            ExprKind::ArenaNewWith { strategy } => self.expr(strategy)?,
            ExprKind::ArenaAlloc { arena, value } => {
                // The arena borrow lasts for the call only; the returned box
                // carries its own region reference.
                let loans = self.loans.clone();
                self.expr(arena)?;
                self.hold_reference_argument(arena)?;
                self.expr(value)?;
                self.loans = loans;
            }
            ExprKind::ArenaTryAlloc { arena, value, .. } => {
                // A refused allocation returns the payload in `Err`; the
                // region borrow still ends with the call.
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
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                self.expr(alloc)?;
                self.expr(free)?;
                if let Some(realloc) = realloc {
                    self.expr(realloc)?;
                }
            }
            ExprKind::AllocatorContextNew { value, .. }
            | ExprKind::AllocatorContextShare(value) => self.expr(value)?,
            ExprKind::AllocBoxNew { allocator, value }
            | ExprKind::AllocBoxTryNew {
                allocator, value, ..
            } => {
                self.expr(allocator)?;
                self.expr(value)?;
            }
            ExprKind::AllocBoxRead(value) => {
                if self.moves(expr.ty) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "AllocBox.read cannot copy an owned payload (or a linear one); consume it with AllocBox.take",
                    ));
                }
                let loans = self.loans.clone();
                self.expr(value)?;
                self.loans = loans;
            }
            ExprKind::AllocBoxTake(value) => self.expr(value)?,
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                ..
            } => {
                self.expr(allocator)?;
                if let Some(capacity) = capacity {
                    self.expr(capacity)?;
                }
            }
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
                    let origins = self.return_origins(value);
                    let lifetime = self.view_loan(value).lifetime;
                    self.check_return_origins(
                        &origins,
                        lifetime.as_deref(),
                        value.ty.is_mut_slice(),
                        expr.span,
                    )?;
                } else if value.ty.is_ref() {
                    let origins = self.return_origins(value);
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
                    self.dyn_linear,
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
                if self.is_carrier_type(expr.ty) {
                    self.call_records
                        .insert(expr_ptr, self.container_provenance(value));
                } else if expr.ty.is_ref() || expr.ty.is_view() {
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
            ExprKind::BoxWrite(reference, value) => {
                if !matches!(reference.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: box write requires an exclusive '&mut Box<T>' reference",
                    ));
                }
                self.expr(reference)?;
                self.expr(value)?;
                if self.is_carrier_type(value.ty) {
                    // Replacing the single boxed element replaces every
                    // per-field loan with the new value's provenance. The
                    // declared destination comes from the box's static element
                    // type, not from the reference's current provenance: a
                    // shortened read label must never weaken the storage
                    // contract, and a missing provenance leaf must not skip the
                    // check.
                    let Type::RefMut(pointer) = reference.ty else {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: box write requires an exclusive '&mut Box<T>' reference",
                        ));
                    };
                    let Type::Box(inner) = self.pointees[pointer] else {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: box write reference does not point at a Box",
                        ));
                    };
                    let element = self.pointees[inner];
                    let expected = leaves_of(
                        self.enums,
                        self.pointees,
                        self.reference_labels,
                        self.variance,
                        element,
                    )?;
                    let existing = self.container_provenance(reference);
                    let incoming = self.borrowed_element_provenance(value);
                    for leaf in &expected {
                        let Some(loan) = incoming.leaves.get(&leaf.path) else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "the borrowed record written into this box is missing provenance for a declared borrowed field",
                            ));
                        };
                        let Some(declared) = self.write_destination_label(
                            leaf.lifetime.as_ref(),
                            &leaf.path,
                            &existing,
                        ) else {
                            continue;
                        };
                        let written = loan.lifetime.clone().or_else(|| {
                            (!loan.origins.is_empty())
                                .then(|| self.anonymous_lifetime(&loan.origins))
                        });
                        if !written
                            .as_deref()
                            .is_some_and(|written| self.actual_outlives(written, &declared))
                        {
                            return Err(Diagnostic::new(
                                expr.span,
                                format!(
                                    "the borrowed record written into this box has a field with {}, which does not outlive its declared element lifetime {}; declare the written source with that lifetime or an outlives bound",
                                    written
                                        .as_deref()
                                        .map(describe_actual)
                                        .unwrap_or_else(|| "a temporary or local owner".to_owned()),
                                    describe_lifetime(&declared)
                                ),
                            ));
                        }
                    }
                    if !self.merge_container_provenance(reference, incoming, true) {
                        return Err(untracked_write(expr.span));
                    }
                } else if self.element_carries_borrow(value.ty)
                    && let Some(loan) = self.reference_element_loan(value)
                {
                    let Type::RefMut(pointer) = reference.ty else {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: box write requires an exclusive '&mut Box<T>' reference",
                        ));
                    };
                    let Type::Box(inner) = self.pointees[pointer] else {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal error: box write reference does not point at a Box",
                        ));
                    };
                    let element = self.pointees[inner];
                    let expected = leaves_of(
                        self.enums,
                        self.pointees,
                        self.reference_labels,
                        self.variance,
                        element,
                    )?;
                    let existing = self.container_provenance(reference);
                    self.check_elided_parameter_destination(reference, &expected, expr.span)?;
                    if let Some(expected_leaf) = expected.iter().find(|leaf| leaf.path.is_empty())
                        && let Some(declared) = self.write_destination_label(
                            expected_leaf.lifetime.as_ref(),
                            &[],
                            &existing,
                        )
                    {
                        let written = loan.lifetime.clone().or_else(|| {
                            (!loan.origins.is_empty())
                                .then(|| self.anonymous_lifetime(&loan.origins))
                        });
                        if !written
                            .as_deref()
                            .is_some_and(|written| self.actual_outlives(written, &declared))
                        {
                            return Err(Diagnostic::new(
                                expr.span,
                                format!(
                                    "the reference written into this box has {}, which does not outlive its declared element lifetime {}; declare the written source with that lifetime or an outlives bound",
                                    written
                                        .as_deref()
                                        .map(describe_actual)
                                        .unwrap_or_else(|| "a temporary or local owner".to_owned()),
                                    describe_lifetime(&declared)
                                ),
                            ));
                        }
                    }
                    if !self.merge_container_element(reference, loan, true) {
                        return Err(untracked_write(expr.span));
                    }
                }
            }
            ExprKind::Assign(slot, value) => {
                let slot = *slot;
                if self.any_loan_at(slot, expr_ptr) {
                    if crate::executable::is_live_scalar(self.locals[slot].ty)
                        && self.live_scalar_capture(slot, expr_ptr)
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            "cannot assign to a scalar location while a closure capturing it is live; call the closure first or move this write after its last use",
                        )
                        .with_note(self.locals[slot].span, "captured location declared here"));
                    }
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
                self.check_write_through_reference(reference, expr_ptr, expr.span)?;
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
            // Equality operands are arbitrary expressions: they can move,
            // drop, or borrow owners, so they take the full ownership walk.
            ExprKind::StructEq { left, right, .. }
            | ExprKind::DynArrayEqual { left, right, .. } => {
                let loans = self.loans.clone();
                self.expr(left)?;
                self.expr(right)?;
                self.loans = loans;
            }
            ExprKind::Call(target, args) => {
                let func = match target {
                    crate::executable::Target::Function(index) => Some(*index),
                    _ => None,
                };
                let loans = self.loans.clone();
                let reborrow = matches!(
                    target,
                    crate::executable::Target::Slice(_, _) | crate::executable::Target::Str(_)
                );
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
                for arg in args.iter_mut().skip(usize::from(reborrow)) {
                    self.expr(arg)?;
                    self.hold_reference_argument(arg)?;
                }
                self.loans = loans;
                if let crate::executable::Target::Vec(op, element) = target {
                    let element = *element;
                    let mut provenance = RecordProvenance::default();
                    match op {
                        crate::executable::VecOp::WithCapacity
                        | crate::executable::VecOp::Clear
                        | crate::executable::VecOp::ClearBorrowed
                        | crate::executable::VecOp::TryReserve { .. } => {}
                        crate::executable::VecOp::Push
                        | crate::executable::VecOp::Set
                        | crate::executable::VecOp::PushBorrowed
                        | crate::executable::VecOp::SetBorrowed => {
                            provenance = self.container_provenance(&args[0]);
                            let setting = matches!(
                                op,
                                crate::executable::VecOp::Set
                                    | crate::executable::VecOp::SetBorrowed
                            );
                            let value_index = if setting { 2 } else { 1 };
                            if self.is_carrier_type(element) {
                                // A borrowed-record element carries one leaf per
                                // borrowed field. Validate every written field
                                // against the container's static element type,
                                // then keep the union of all possible element
                                // sources. The static type is authoritative: a
                                // truncated stored provenance must not weaken a
                                // declared destination label or skip a leaf.
                                let incoming = self.borrowed_element_provenance(&args[value_index]);
                                let expected = leaves_of(
                                    self.enums,
                                    self.pointees,
                                    self.reference_labels,
                                    self.variance,
                                    element,
                                )?;
                                for leaf in &expected {
                                    let Some(loan) = incoming.leaves.get(&leaf.path) else {
                                        return Err(Diagnostic::new(
                                            expr.span,
                                            "the borrowed record written into this container is missing provenance for a declared borrowed field",
                                        ));
                                    };
                                    let Some(declared) = self.write_destination_label(
                                        leaf.lifetime.as_ref(),
                                        &leaf.path,
                                        &provenance,
                                    ) else {
                                        continue;
                                    };
                                    let written = loan.lifetime.clone().or_else(|| {
                                        (!loan.origins.is_empty())
                                            .then(|| self.anonymous_lifetime(&loan.origins))
                                    });
                                    if !written.as_deref().is_some_and(|written| {
                                        self.actual_outlives(written, &declared)
                                    }) {
                                        return Err(Diagnostic::new(
                                            expr.span,
                                            format!(
                                                "the borrowed record written into this container has field {} with {}, which does not outlive its declared element lifetime {}; declare the pushed source with that lifetime or an outlives bound",
                                                leaf.path
                                                    .iter()
                                                    .map(usize::to_string)
                                                    .collect::<Vec<_>>()
                                                    .join("."),
                                                written
                                                    .as_deref()
                                                    .map(describe_actual)
                                                    .unwrap_or_else(|| {
                                                        "a temporary or local owner".to_owned()
                                                    }),
                                                describe_lifetime(&declared)
                                            ),
                                        ));
                                    }
                                }
                                for (path, loan) in incoming.leaves {
                                    match provenance.leaves.get(&path) {
                                        Some(existing) => {
                                            let merged = self.merge_loans([existing.clone(), loan]);
                                            provenance.leaves.insert(path, merged);
                                        }
                                        None => {
                                            provenance.leaves.insert(path, loan);
                                        }
                                    }
                                }
                                if matches!(
                                    op,
                                    crate::executable::VecOp::PushBorrowed
                                        | crate::executable::VecOp::SetBorrowed
                                ) {
                                    let updated = provenance.clone();
                                    if !self.merge_container_provenance(&args[0], updated, false) {
                                        return Err(untracked_write(expr.span));
                                    }
                                }
                            } else if self.element_carries_borrow(element)
                                && let Some(loan) = self.reference_element_loan(&args[value_index])
                            {
                                // A reference written into a container whose
                                // element type declares a lifetime must outlive
                                // that lifetime. The static element type is the
                                // authority, so a missing or shortened stored
                                // provenance leaf cannot skip the check. Local
                                // containers with an inferred element label keep
                                // the union and do not impose this relation.
                                let expected = leaves_of(
                                    self.enums,
                                    self.pointees,
                                    self.reference_labels,
                                    self.variance,
                                    element,
                                )?;
                                self.check_elided_parameter_destination(
                                    &args[0], &expected, expr.span,
                                )?;
                                if let Some(expected_leaf) =
                                    expected.iter().find(|leaf| leaf.path.is_empty())
                                    && let Some(declared) = self.write_destination_label(
                                        expected_leaf.lifetime.as_ref(),
                                        &[],
                                        &provenance,
                                    )
                                {
                                    let pushed = loan.lifetime.clone().or_else(|| {
                                        (!loan.origins.is_empty())
                                            .then(|| self.anonymous_lifetime(&loan.origins))
                                    });
                                    if !pushed.as_deref().is_some_and(|pushed| {
                                        self.actual_outlives(pushed, &declared)
                                    }) {
                                        return Err(Diagnostic::new(
                                            expr.span,
                                            format!(
                                                "the reference written into this container has {}, which does not outlive its declared element lifetime {}; declare the pushed source with that lifetime or an outlives bound",
                                                pushed
                                                    .as_deref()
                                                    .map(describe_actual)
                                                    .unwrap_or_else(|| {
                                                        "a temporary or local owner".to_owned()
                                                    }),
                                                describe_lifetime(&declared)
                                            ),
                                        ));
                                    }
                                }
                                // A vector may contain references to several
                                // owners. Retain every possible source;
                                // replacing one position does not prove that an
                                // earlier source is absent from other positions.
                                let existing = provenance.leaves.remove(&Vec::new());
                                let loan = self.merge_loans(existing.into_iter().chain([loan]));
                                provenance.leaves.insert(Vec::new(), loan);
                                if matches!(
                                    op,
                                    crate::executable::VecOp::PushBorrowed
                                        | crate::executable::VecOp::SetBorrowed
                                ) {
                                    let updated = provenance
                                        .leaves
                                        .get(&Vec::new())
                                        .cloned()
                                        .unwrap_or_default();
                                    if !self.merge_container_element(&args[0], updated, false) {
                                        return Err(untracked_write(expr.span));
                                    }
                                }
                            }
                        }
                        crate::executable::VecOp::Reserve
                        | crate::executable::VecOp::ReserveBorrowed
                        | crate::executable::VecOp::Len => {
                            provenance = self.container_provenance(&args[0]);
                        }
                        crate::executable::VecOp::Get | crate::executable::VecOp::At => {
                            if self.is_carrier_type(expr.ty) {
                                provenance = self.container_provenance(&args[0]);
                            } else if expr.ty.is_ref() || expr.ty.is_view() {
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
                let call_lifetime = if let Some(index) = func {
                    Some(&self.calls[index])
                } else {
                    match target {
                        crate::executable::Target::DynCall { spec } => {
                            self.dyn_call_lifetimes.get(*spec)
                        }
                        crate::executable::Target::UnionBorrowCall { spec } => {
                            self.union_call_lifetimes.get(*spec)
                        }
                        _ => None,
                    }
                };
                if let Some(call) = call_lifetime {
                    let parameters = call.parameters.clone();
                    let result = call.result.clone();
                    let bounds = call.bounds.clone();
                    let effect_parameters = parameters.clone();
                    self.apply_call_lifetime(
                        parameters,
                        result,
                        bounds.clone(),
                        args,
                        expr_ptr,
                        expr.ty,
                        expr.span,
                    )?;
                    self.apply_mutable_container_effects(
                        &effect_parameters,
                        &bounds,
                        args,
                        expr.span,
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
                    for mutable in [false, true] {
                        let origins = if mutable {
                            info.exclusive_origins.clone()
                        } else {
                            info.origins
                                .difference(&info.exclusive_origins)
                                .copied()
                                .collect()
                        };
                        if origins.is_empty() {
                            continue;
                        }
                        let roots = self.origins_roots(&origins);
                        self.temporary_regions.push(RetainedView {
                            origins: origins.clone(),
                            roots,
                            mutable,
                            splits: info.splits.clone(),
                            field: None,
                        });
                        self.loans.extend(origins.iter().copied());
                        if mutable {
                            self.temporary_exclusive.extend(origins);
                        } else {
                            self.temporary_shared.extend(origins);
                        }
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
                                        variance: crate::variance::SignSet::POSITIVE,
                                    }]
                                } else if ty.is_ref() {
                                    vec![crate::runtime_types::BorrowLeaf {
                                        path: vec![],
                                        lifetime: borrows.parameters.get(i).cloned().flatten(),
                                        mutable: matches!(ty, Type::RefMut(_)),
                                        variance: crate::variance::SignSet::POSITIVE,
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
                                            variance: crate::variance::SignSet::POSITIVE,
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
                                        variance: crate::variance::SignSet::POSITIVE,
                                    })
                                    .collect(),
                            )
                        } else {
                            CallResult::None
                        };
                        let bounds = borrows.bounds.clone();
                        let effect_parameters = parameters.clone();
                        self.apply_call_lifetime(
                            parameters,
                            result,
                            bounds.clone(),
                            arguments,
                            expr_ptr,
                            expr.ty,
                            expr.span,
                        )?;
                        self.apply_mutable_container_effects(
                            &effect_parameters,
                            &bounds,
                            arguments,
                            expr.span,
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
                    for (origins, mutable, splits, mut field) in lent {
                        let roots = self.origins_roots(&origins);
                        if let Some(field) = &mut field {
                            field.strip_index_ids();
                        }
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
            ExprKind::FnValue { function, captures } => {
                // A borrowed-capture closure is a scoped lexical capability.
                // It is legal only as a direct `let` initializer or as the
                // immediate callee of an indirect call; both positions are
                // marked by the enclosing statement. Captured slice views,
                // borrowed records, and by-reference scalar locations are all
                // inert descriptors: the environment never owns the storage
                // behind them.
                let capture_ref = self
                    .capture_refs
                    .get(*function)
                    .cloned()
                    .unwrap_or_default();
                let capture_write = self
                    .capture_writes
                    .get(*function)
                    .cloned()
                    .unwrap_or_default();
                let capabilities = self
                    .capability_captures
                    .get(*function)
                    .cloned()
                    .unwrap_or_default();
                let scalars = captures
                    .iter()
                    .enumerate()
                    .filter(|(index, capture)| {
                        (capture_ref.get(*index).copied().unwrap_or(false)
                            && crate::executable::is_live_scalar(capture.ty))
                            || capabilities.contains(index)
                    })
                    .collect::<Vec<_>>();
                let borrowed = captures
                    .iter()
                    .filter(|capture| capture.ty.is_slice())
                    .collect::<Vec<_>>();
                let records = captures
                    .iter()
                    .filter(|capture| self.is_carrier_type(capture.ty))
                    .collect::<Vec<_>>();
                if !scalars.is_empty() || !borrowed.is_empty() || !records.is_empty() {
                    if self.capture_site != Some(expr_ptr) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "a lambda with borrowed captures must be called immediately or bound directly to a local; it cannot escape through a return, aggregate, box, union, generic call, adapter, or task",
                        ));
                    }
                    let mut origins = BTreeSet::new();
                    let mut splits: Option<SplitLabels> = None;
                    let mut exclusive_origins = BTreeSet::new();
                    for (index, capture) in &scalars {
                        let slot = match &capture.kind {
                            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                                *slot
                            }
                            _ => {
                                return Err(Diagnostic::new(
                                    capture.span,
                                    "internal error: by-reference scalar capture is not a local place",
                                ));
                            }
                        };
                        let capture_origins = BTreeSet::from([slot]);
                        let capture_mut = capture_write.get(*index).copied().unwrap_or(false);
                        self.check_view_creation(
                            &capture_origins,
                            capture_mut,
                            &SplitLabels::default(),
                            None,
                            expr_ptr,
                            capture.span,
                        )?;
                        if capture_mut {
                            exclusive_origins.extend(capture_origins.iter().copied());
                        }
                        origins.extend(capture_origins);
                        splits.get_or_insert_with(SplitLabels::default);
                    }
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
                        if capture_mut {
                            exclusive_origins.extend(capture_origins.iter().copied());
                        }
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
                            if loan.mutable {
                                exclusive_origins.extend(loan.origins.iter().copied());
                            }
                            origins.extend(loan.origins.iter().copied());
                            splits = Some(match splits {
                                Some(current) => intersect_splits(&current, &loan.splits),
                                None => loan.splits.clone(),
                            });
                        }
                    }
                    let mut info = BorrowedCapture {
                        origins,
                        exclusive_origins,
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
                        self.dyn_linear,
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
            ExprKind::DynArrayFill { length, value, .. } => {
                // The length is read first, then the copyable element.
                self.expr(length)?;
                self.expr(value)?;
            }
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
            ExprKind::DynArrayPop { array, .. } => {
                // `pop` returns a shorter array value; while a slice view of
                // the owner is live the owner must stay unchanged, as for
                // push, set, and assignment.
                if let ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot) =
                    &through_coerce(array).kind
                    && self.any_loan_at(*slot, expr_ptr)
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "cannot pop from a DynArray while a slice view of it is live",
                    )
                    .with_note(self.locals[*slot].span, "owner declared here"));
                }
                self.expr(array)?;
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                self.expr(handler)?;
                self.block(body)?;
            }
            ExprKind::Suspendable(suspendable) => self.block(&mut suspendable.body)?,
            ExprKind::Suspend { call, .. } => self.expr(call)?,
            ExprKind::Region { .. }
            | ExprKind::RegionExit { .. }
            | ExprKind::HandlerDepth
            | ExprKind::HandlerRedirect { .. }
            | ExprKind::TryExit { .. } => {
                unreachable!("ownership runs before suspendable bodies are lowered")
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
                } else if self.enums[*enum_id].optional_reference().is_some() {
                    let mut provenance = RecordProvenance::default();
                    if let Some(field) = fields.first() {
                        let loan = self.view_loan(field);
                        if loan.origins.is_empty() {
                            return Err(Diagnostic::new(
                                field.span,
                                "optional reference payload has no checked capability provenance",
                            ));
                        }
                        provenance.leaves.insert(Vec::new(), loan);
                    }
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
                let entry_exclusive_loans = self.exclusive_loans.clone();
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
                // A borrowed DynArray scrutinee likewise transfers its loan to
                // the element-reference bindings, which are views of their own.
                let borrowed_array = matches!(scrutinee, Type::Ref(pointer) | Type::RefMut(pointer)
                    if self.pointees[pointer]
                        .layout()
                        .is_some_and(|id| self.enums[id].dynamic_array.is_some()));
                let loans = if scrutinee_provenance.is_some() || borrowed_array {
                    entry_scrutinee_loans
                } else {
                    self.loans.clone()
                };
                // A `&mut DynArray` scrutinee's call-scoped exclusive loan
                // likewise moves to the exclusive bindings, whose own views
                // keep the array suspended until their last use. Keeping it
                // would reject disjoint borrows of those bindings.
                if borrowed_array && matches!(scrutinee, Type::RefMut(_)) {
                    self.exclusive_loans = entry_exclusive_loans;
                }
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
                    if let Pattern::DynArray {
                        prefix,
                        suffix,
                        rest_binding,
                        borrowed: true,
                        exclusive,
                        ..
                    } = &arm.pattern
                    {
                        // Element references and the rest view borrow the
                        // scrutinee's storage: they are views rooted at its
                        // owners, live until their own last use. Over `&mut`,
                        // they are exclusive, and binding `i` takes side
                        // `true` of its own split group and side `false` of
                        // every other binding's group, so any two bindings
                        // are disjoint while every other view still conflicts.
                        let origins = self.view_origins(value);
                        let lifetime = self.view_loan(value).lifetime.or_else(|| {
                            (!origins.is_empty()).then(|| self.anonymous_lifetime(&origins))
                        });
                        let splits = self.split_labels(value);
                        let slots = prefix
                            .iter()
                            .chain(suffix)
                            .filter_map(|pattern| match pattern {
                                Pattern::Bind(slot) => Some(*slot),
                                _ => None,
                            })
                            .chain(*rest_binding)
                            .collect::<Vec<_>>();
                        let count = slots.len();
                        for (index, slot) in slots.into_iter().enumerate() {
                            let mut labels = splits.clone();
                            if let Some(base) = exclusive {
                                for other in 0..count {
                                    labels = labels.with(base + other, other == index);
                                }
                            }
                            self.acquire_view(
                                slot,
                                exclusive.is_some(),
                                origins.clone(),
                                labels,
                                lifetime.clone(),
                                None,
                            );
                            if self.locals[slot].ty.is_ref() {
                                self.reference_lifetimes[slot] = lifetime.clone();
                            }
                        }
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
                            let origins = if arm.body.ty.is_view() || arm.body.ty.is_ref() {
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
                                    if arm.body.ty.is_view() {
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
                self.wrapped_results
                    .insert(expr_ptr, RecordProvenance::merge(state.result_provenance));
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
                    if self.is_carrier_type(value.ty) {
                        let provenance = self.record_provenance(value);
                        let bound = &self.loops.last().unwrap().bound;
                        for loan in provenance.leaves.values() {
                            if let Some(owner) = loan
                                .origins
                                .iter()
                                .find(|owner| bound.contains(owner) && !self.is_local_view(**owner))
                            {
                                return Err(Diagnostic::new(
                                    value.span,
                                    "borrowed loop result would outlive the lexical scope of its owner",
                                ).with_note(self.locals[*owner].span, "owner declared here"));
                            }
                        }
                        self.loops
                            .last_mut()
                            .unwrap()
                            .result_provenance
                            .push(provenance);
                    }
                }
                let bound = self.loops.last().unwrap().bound.clone();
                self.exit_check(bound, expr.span, "leaving the loop")?;
                *cleanup = self.cleanup_list();
                if let Some(previous) = self.loops.last().unwrap().breaks.clone() {
                    self.merge(&previous, expr.span)?;
                }
                self.loops.last_mut().unwrap().breaks = Some(self.available.clone());
            }
            ExprKind::AbortScope {
                label,
                body,
                handler,
                ..
            } => {
                let state = self.loop_state();
                self.aborts.push((*label, state));
                self.block(body)?;
                let (_, state) = self.aborts.pop().unwrap();
                let completed = (body.ty != Type::Never).then(|| self.available.clone());
                match state.breaks {
                    Some(aborted) => {
                        // The handler runs only on the abort path.
                        self.available = aborted;
                        let loans = self.loans.clone();
                        self.expr(handler)?;
                        self.loans = loans;
                        if let Some(completed) = completed {
                            self.merge(&completed, expr.span)?;
                        }
                    }
                    None => self.available = completed.unwrap_or(state.entry),
                }
            }
            ExprKind::AbortPerform { value, .. } => {
                self.check_pending_linear(0, expr.span)?;
                self.expr(value)?;
                self.exit_check(
                    0..self.available.len(),
                    expr.span,
                    "this abortive perform leaves the function",
                )?;
            }
            ExprKind::AbortCall {
                call,
                exits,
                propagates,
            } => {
                let mut start = if *propagates { 0 } else { usize::MAX };
                let mut indices = Vec::new();
                for (label, _) in exits.iter() {
                    let index = self
                        .aborts
                        .iter()
                        .rposition(|(target, _)| target == label)
                        .expect("an abort call is inside its scopes");
                    start = start.min(self.aborts[index].1.pending_linear_start);
                    indices.push(index);
                }
                self.check_pending_linear(start, expr.span)?;
                self.expr(call)?;
                // The wrapper owns the result (registered below), so it is
                // tracked only once the call did not abort.
                call.resource = None;
                for ((_, cleanup), index) in exits.iter_mut().zip(indices) {
                    let bound = self.aborts[index].1.bound.clone();
                    self.exit_check(bound, expr.span, "a call that may abort to its 'handle'")?;
                    *cleanup = self.cleanup_list_for(&self.aborts[index].1);
                    if let Some(previous) = self.aborts[index].1.breaks.clone() {
                        let current = self.available.clone();
                        self.merge(&previous, expr.span)?;
                        self.aborts[index].1.breaks = Some(self.available.clone());
                        self.available = current;
                    } else {
                        self.aborts[index].1.breaks = Some(self.available.clone());
                    }
                }
                if *propagates {
                    self.exit_check(
                        0..self.available.len(),
                        expr.span,
                        "a call that may abort out of the function",
                    )?;
                }
            }
            ExprKind::AbortExit {
                label,
                value,
                cleanup,
                ..
            } => {
                let index = self
                    .aborts
                    .iter()
                    .rposition(|(target, _)| target == label)
                    .expect("an abort exit is inside its scope");
                self.check_pending_linear(self.aborts[index].1.pending_linear_start, expr.span)?;
                self.expr(value)?;
                let bound = self.aborts[index].1.bound.clone();
                self.exit_check(bound, expr.span, "this abortive perform")?;
                *cleanup = self.cleanup_list_for(&self.aborts[index].1);
                if let Some(previous) = self.aborts[index].1.breaks.clone() {
                    self.merge(&previous, expr.span)?;
                }
                self.aborts[index].1.breaks = Some(self.available.clone());
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
            // Leaves. `Move` is only created by this pass from a `Local`, so
            // it has already been accounted for. There is deliberately no
            // wildcard: a new expression kind must decide here how ownership
            // treats it, or the build fails.
            ExprKind::Constant(_)
            | ExprKind::BytesLiteral(_)
            | ExprKind::Erased(_)
            | ExprKind::Move(_) => {}
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
                self.dyn_linear,
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
                    || is_linear(
                        ty,
                        self.linear,
                        self.unions,
                        self.pointees,
                        self.functions,
                        self.dyn_linear,
                    )
            }
            Pattern::Or(ps) => ps.iter().any(|p| self.ignores_linear(p, ty, whole_linear)),
            Pattern::Variant { tag, fields, .. } => ty.layout().is_some_and(|id| {
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
/// Strip representation-only coercions. A structural record conversion
/// renumbers fields, so it is not transparent for per-field provenance.
fn through_coerce(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Coerce {
            value, coercion, ..
        } if !matches!(coercion, Coercion::Struct { .. }) => through_coerce(value),
        _ => expr,
    }
}
/// Move per-field provenance from a coercion's source layout to its target
/// layout. Leaves of dropped source fields disappear with the field.
fn coerce_provenance(coercion: &Coercion, provenance: RecordProvenance) -> RecordProvenance {
    let Coercion::Struct { kept, .. } = coercion else {
        return provenance;
    };
    let mut out = RecordProvenance::default();
    if let Some(root) = provenance.leaves.get(&Vec::new()) {
        out.leaves.insert(Vec::new(), root.clone());
        if let Some(alternatives) = provenance.alternatives.get(&Vec::new()) {
            out.alternatives.insert(Vec::new(), alternatives.clone());
        }
    }
    for (target, source, nested) in kept {
        let mut field = RecordProvenance::default();
        for (path, loan) in &provenance.leaves {
            if path.first() == Some(source) {
                let relative = path[1..].to_vec();
                field.leaves.insert(relative.clone(), loan.clone());
                if let Some(alternatives) = provenance.alternatives.get(path) {
                    field.alternatives.insert(relative, alternatives.clone());
                }
            }
        }
        if let Some(nested) = nested {
            field = coerce_provenance(nested, field);
        }
        for (path, loan) in field.leaves {
            let mut full = vec![*target];
            full.extend(path);
            out.leaves.insert(full, loan);
        }
        for (path, alternatives) in field.alternatives {
            let mut full = vec![*target];
            full.extend(path);
            out.alternatives.insert(full, alternatives);
        }
    }
    out
}
/// Map a target-layout field path back through a coercion to its source
/// layout. `None` when the coercion does not keep that field.
fn coerce_field_path(coercion: &Coercion, path: &[usize]) -> Option<Vec<usize>> {
    let Coercion::Struct { kept, .. } = coercion else {
        return Some(path.to_vec());
    };
    let Some((first, rest)) = path.split_first() else {
        return Some(Vec::new());
    };
    let (_, source, nested) = kept.iter().find(|(target, ..)| target == first)?;
    let rest = match nested {
        Some(nested) => coerce_field_path(nested, rest)?,
        None => rest.to_vec(),
    };
    let mut full = vec![*source];
    full.extend(rest);
    Some(full)
}
fn block_span(block: &Block) -> Span {
    block
        .tail
        .as_ref()
        .map(|t| t.span)
        .or_else(|| {
            block.statements.last().map(|s| match s {
                Statement::Let(_, e) | Statement::Expr(e) => e.span,
                Statement::Declare(_) => Span::default(),
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
        Pattern::DynArray {
            prefix,
            suffix,
            rest_binding,
            ..
        } => {
            if let Some(slot) = rest_binding {
                slots.insert(*slot);
            }
            for p in prefix.iter().chain(suffix) {
                pattern_bindings(p, slots);
            }
        }
        Pattern::Or(ps) => {
            for p in ps {
                pattern_bindings(p, slots);
            }
        }
        _ => {}
    }
}

/// The slice view under a checked element place `view[i]`, through any field
/// projections of that element (`view[i].x`).
fn slice_place_view(place: &Expr) -> Option<&Expr> {
    match &place.kind {
        ExprKind::PlaceIndex { base, .. } if base.ty.is_slice() => Some(base),
        ExprKind::Project(base, _) if !base.ty.is_ref() => slice_place_view(base),
        ExprKind::Coerce { value, .. } => slice_place_view(value),
        _ => None,
    }
}
/// Values returned by breaks targeting this loop, excluding nested loops.
/// Traverse all expression positions because a break can occur in an argument.
pub(crate) fn loop_break_values(block: &Block) -> Vec<&Expr> {
    fn walk_block<'a>(block: &'a Block, out: &mut Vec<&'a Expr>) {
        for statement in &block.statements {
            match statement {
                Statement::Let(_, e) | Statement::Expr(e) => walk(e, out),
                Statement::Declare(_) => {}
            }
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
            ExprKind::DynArrayFill { length, value, .. } => {
                walk(length, out);
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
            ExprKind::AbortScope { handler, body, .. } => {
                walk(handler, out);
                walk_block(body, out);
            }
            ExprKind::AbortExit { value, .. } => walk(value, out),
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
            }
            | ExprKind::ArenaTryAlloc {
                arena: owner,
                value: payload,
                ..
            } => {
                walk(owner, out);
                walk(payload, out);
            }
            ExprKind::ArenaNew => {}
            ExprKind::ArenaNewWith { strategy } => walk(strategy, out),
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                walk(vector, out);
                for callback in callbacks {
                    walk(callback, out);
                }
            }
            ExprKind::Binary(_, a, b)
            | ExprKind::BytesAt(a, b)
            | ExprKind::StructEq {
                left: a, right: b, ..
            }
            | ExprKind::DynArrayEqual {
                left: a, right: b, ..
            } => {
                walk(a, out);
                walk(b, out);
            }
            ExprKind::RefAssign(reference, _, value) | ExprKind::BoxWrite(reference, value) => {
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
                || container_carries_borrow(enums, pointees, local.ty))
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
    exits: &mut Vec<(Option<usize>, Live)>,
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
            Statement::Declare(_) => {
                // The matching InitOwner/BorrowInit expression records the
                // hidden storage's use at its source position.
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
    exits: &mut Vec<(Option<usize>, Live)>,
    out: &mut BTreeMap<usize, Live>,
) -> Live {
    let mut live = live_after.clone();
    match &expr.kind {
        ExprKind::Local(slot)
        | ExprKind::Peek(slot)
        | ExprKind::Borrow(slot)
        | ExprKind::Move(slot) => add_use(&mut live, *slot, views),
        ExprKind::InitOwner { slot, value: init } | ExprKind::BorrowInit { slot, value: init } => {
            let mut after = live.clone();
            after.remove(slot);
            live = expr_live(init, &after, views, heads, exits, out);
            add_use(&mut live, *slot, views);
        }
        ExprKind::Erased(_) => {}
        ExprKind::Assign(slot, value) => {
            let mut after = live.clone();
            after.remove(slot);
            live = expr_live(value, &after, views, heads, exits, out);
            live.remove(slot);
        }
        ExprKind::RefAssign(reference, _, value)
        | ExprKind::DerefWrite(reference, value)
        | ExprKind::BoxWrite(reference, value) => {
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
        | ExprKind::BorrowPlace(value)
        | ExprKind::Coerce { value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::PlaceIndex { base, index, .. } => {
            live = expr_live(base, &live, views, heads, exits, out);
            live = expr_live(index, &live, views, heads, exits, out);
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
        }
        | ExprKind::ArenaTryAlloc {
            arena: owner,
            value: payload,
            ..
        } => {
            live = expr_live(payload, live_after, views, heads, exits, out);
            live = expr_live(owner, &live, views, heads, exits, out);
        }
        ExprKind::ArenaNew => {}
        ExprKind::ArenaNewWith { strategy } => {
            live = expr_live(strategy, live_after, views, heads, exits, out);
        }
        ExprKind::AllocatorNew {
            alloc,
            free,
            realloc,
        } => {
            if let Some(realloc) = realloc {
                live = expr_live(realloc, live_after, views, heads, exits, out);
            }
            live = expr_live(free, &live, views, heads, exits, out);
            live = expr_live(alloc, &live, views, heads, exits, out);
        }
        ExprKind::AllocatorContextNew { value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::AllocatorContextShare(value) => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::AllocBoxNew { allocator, value }
        | ExprKind::AllocBoxTryNew {
            allocator, value, ..
        } => {
            live = expr_live(value, live_after, views, heads, exits, out);
            live = expr_live(allocator, &live, views, heads, exits, out);
        }
        ExprKind::AllocBoxRead(value) | ExprKind::AllocBoxTake(value) => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::AllocVecNew {
            allocator,
            capacity,
            ..
        } => {
            if let Some(capacity) = capacity {
                live = expr_live(capacity, live_after, views, heads, exits, out);
            }
            live = expr_live(allocator, &live, views, heads, exits, out);
        }
        ExprKind::DynArrayNew { .. } => {}
        ExprKind::DynArrayPush { array, value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
            live = expr_live(array, &live, views, heads, exits, out);
        }
        ExprKind::DynArrayFill { length, value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
            live = expr_live(length, &live, views, heads, exits, out);
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
        ExprKind::Suspendable(suspendable) => {
            live = block_live(&suspendable.body, live_after, views, heads, exits, out);
        }
        ExprKind::Suspend { call, .. } => {
            live = expr_live(call, live_after, views, heads, exits, out);
        }
        ExprKind::Region { body, finish, .. } => {
            let after = match finish {
                Some(finish) => expr_live(finish, live_after, views, heads, exits, out),
                None => live_after.clone(),
            };
            live = block_live(body, &after, views, heads, exits, out);
        }
        ExprKind::RegionExit { value, .. } | ExprKind::TryExit { value, .. } => {
            live = expr_live(value, live_after, views, heads, exits, out);
        }
        ExprKind::AbortScope {
            label,
            body,
            handler,
            ..
        } => {
            // An abort continues with the handler call, then after the scope.
            let aborted = expr_live(handler, live_after, views, heads, exits, out);
            exits.push((Some(*label), aborted));
            live = block_live(body, live_after, views, heads, exits, out);
            exits.pop();
        }
        ExprKind::AbortPerform { value, .. } => {
            live = expr_live(value, &Live::new(), views, heads, exits, out);
        }
        ExprKind::AbortCall {
            call,
            exits: targets,
            ..
        } => {
            let mut after = live_after.clone();
            for (label, _) in targets {
                if let Some((_, live)) = exits
                    .iter()
                    .rev()
                    .find(|(target, _)| *target == Some(*label))
                {
                    after.extend(live.iter().copied());
                }
            }
            live = expr_live(call, &after, views, heads, exits, out);
        }
        ExprKind::AbortExit { label, value, .. } => {
            let exit = exits
                .iter()
                .rev()
                .find(|(target, _)| *target == Some(*label))
                .map(|(_, live)| live.clone())
                .unwrap_or_default();
            live = expr_live(value, &exit, views, heads, exits, out);
        }
        ExprKind::HandlerDepth => {}
        ExprKind::HandlerRedirect { depth, body } => {
            live = block_live(body, live_after, views, heads, exits, out);
            live = expr_live(depth, &live, views, heads, exits, out);
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            live = expr_live(resume, live_after, views, heads, exits, out);
            live = expr_live(payload, &live, views, heads, exits, out);
        }
        ExprKind::Binary(_, left, right)
        | ExprKind::BytesAt(left, right)
        | ExprKind::StructEq { left, right, .. }
        | ExprKind::DynArrayEqual { left, right, .. } => {
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
            exits.push((None, live_after.clone()));
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
            exits.push((None, live_after.clone()));
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
            if let Some((_, exit)) = exits.iter().rev().find(|(label, _)| label.is_none()) {
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
