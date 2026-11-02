//! Finite, inline enum, record, and heterogeneous union layouts for the
//! executable subset. Instantiations are nominal, memoized, and admitted only
//! after every payload layout is complete. A record is a single-variant layout
//! with named fields; a union is a discriminator plus its widest alternative.
use crate::{
    Diagnostic, Span, ast,
    check::LogicalEnvironment,
    executable::{TraitArguments, Type},
    grades::Grade,
    resolve::{BindingId, BindingKind, Resolution},
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, Diagnostic>;
pub(crate) const MAX_WORDS: usize = 32;
/// A normalized union has at most this many alternatives. Larger unions are
/// rejected rather than causing unbounded dispatchers and layout searches.
pub(crate) const MAX_UNION_MEMBERS: usize = 16;
/// Work budget for distributive intersection normalization.
const MAX_INTERSECTION_WORK: usize = 4096;
/// Executable type-alias expansion is transparent but bounded.
const MAX_ALIAS_DEPTH: usize = 64;
/// Substitution for one specialization: type arguments and compile-time
/// natural (const) arguments. Grades are never part of a runtime type.
#[derive(Debug, Clone, Default)]
pub(crate) struct Subst {
    pub types: BTreeMap<BindingId, Type>,
    pub consts: BTreeMap<BindingId, usize>,
    pub grades: BTreeMap<BindingId, Grade>,
    /// Concrete effect-row arguments for `e: Effects` parameters. Effects are
    /// compile-time bitsets; a row may combine a fixed part with variables.
    pub effects: BTreeMap<BindingId, u8>,
    /// Erased lifetime substitution for a data declaration or alias. Names are
    /// lexical lifetime identities, not bindings in the value namespace.
    pub lifetimes: BTreeMap<String, String>,
    /// Concrete impl target for `Self` inside a method signature. Ordinary
    /// functions leave this empty, so a stray `Self` is rejected.
    pub self_type: Option<Type>,
    /// Associated type values of the impl that supplies a method signature.
    /// `Self::Item` in a trait/impl signature normalizes to this AST value
    /// (which may itself mention impl generic parameters and is lowered with
    /// the same substitution).
    pub associated_types: BTreeMap<String, ast::Type>,
    /// Associated type projections resolved for concrete generic specializations.
    /// The key is the base generic binder and the declared associated name, so
    /// `T::Item` lowers to the value supplied by the impl selected for `T`.
    pub projections: BTreeMap<(BindingId, String), Type>,
    /// Concrete closed-world values for `Self::Item` on a trait object. They are
    /// populated only after every impl of the object specialization agrees.
    pub self_projections: BTreeMap<String, Type>,
}
#[derive(Clone, Copy)]
struct Alias<'a> {
    lifetimes: &'a [ast::Lifetime],
    generics: &'a [ast::Generic],
    ty: &'a ast::Type,
}
#[derive(Debug, Clone)]
pub(crate) struct Variant {
    pub name: String,
    pub fields: Vec<Type>,
    pub tuple: bool,
    /// Field names for records; empty for enum variants.
    pub names: Vec<String>,
}
#[derive(Debug)]
pub(crate) struct Enum {
    pub definition: BindingId,
    pub name: String,
    pub arguments: Vec<Type>,
    /// Compile-time natural arguments, in declaration order among const
    /// generics. They have no runtime representation.
    pub consts: Vec<usize>,
    /// Erased lifetime arguments of this record instance. Checker-only: they
    /// add no tag, word, or allocation to the inline layout.
    pub lifetimes: Vec<String>,
    pub variants: Vec<Variant>,
    pub words: usize,
    pub result: Option<ResultShape>,
    pub record: bool,
    /// For each record field, the declared shared-borrow lifetime of a direct
    /// `&'a [T]` field. `None` for ordinary fields. Empty for enums/arrays.
    pub field_lifetimes: Vec<Option<String>>,
    /// Whether this record transitively contains a borrowed slice leaf.
    pub borrowed: bool,
    /// Whether this record transitively contains an exclusive borrowed slice
    /// leaf. Such records are affine even when they own no heap storage.
    pub mutable_borrow: bool,
    pub array: Option<(Type, usize)>,
    /// A runtime-sized inline array: fixed compile-time capacity and a runtime
    /// length in word zero. Fields beyond the length are uninitialized and must
    /// never be dropped or read.
    pub dynamic_array: Option<(Type, usize)>,
    /// An anonymous tuple layout; `arguments` are its element types.
    pub tuple: bool,
    /// Declared `#[linear]`: values must be consumed, never implicitly dropped.
    pub linear: bool,
    /// An anonymous structural record type (`struct { a: A, b: B }`). Its
    /// fields are stored in canonical name order, so equal rows intern to one
    /// layout. Structural width subtyping is checked field by field.
    pub structural: bool,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnionType {
    /// Normalized alternatives, sorted by `Type`. No alternative is `Never`,
    /// another union, or a duplicate, and each alternative is a concrete
    /// non-borrowed runtime value type.
    pub members: Vec<Type>,
}
/// One dynamically dispatched trait-object specialization. Unlike the
/// closed-world union representation, this does not enumerate members at the
/// type level: the runtime value carries a member identifier and an owned
/// payload, so adding an impl (including a generic or blanket instantiation)
/// changes only the dispatch tables, never the value layout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DynObjectType {
    pub trait_id: BindingId,
    pub arguments: TraitArguments,
    /// Checker spelling such as `dyn Show` or `dyn Convert<i64>`.
    pub name: String,
}

type FunctionKey = (
    Vec<Type>,
    Type,
    u8,
    Vec<Option<Grade>>,
    Option<Grade>,
    bool,
    bool,
    BorrowSig,
);
/// The borrow contract of a callable type: which runtime parameters are slice
/// views and under which lifetime, the result view's lifetime, and the
/// reflexive-transitive outlives relation between them. Lifetimes are
/// canonical (`#0`, `#1`, ... in order of first use), so alpha-equivalent
/// arrow types intern to one function type. Empty for borrow-free callables.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BorrowSig {
    pub parameters: Vec<Option<String>>,
    pub result: Option<String>,
    /// Borrowed record leaves of each runtime parameter, aligned with
    /// `parameters`. Slice parameters stay in `parameters` and contribute an
    /// empty entry here, so one runtime parameter index always has one slot.
    pub parameter_leaves: Vec<Vec<BorrowLeafSig>>,
    /// Borrowed record leaves of a record result, at the same field paths as
    /// `runtime_types::borrow_leaves`.
    pub result_leaves: Vec<BorrowLeafSig>,
    /// A scoped closure result borrowed from a captured view or captured
    /// record field. The environment is not part of the arrow's visible
    /// parameter contract, so the source capture index travels here; a closure
    /// carrying this contract may only be called through its exact local
    /// binding, never coerced to another callable value.
    pub capture_result: Option<CaptureResultSig>,
    pub bounds: BTreeSet<(String, String)>,
}
/// Which capture supplies a closure's borrowed result. Capture indices are
/// positions in the synthesized closure function's leading parameter list.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CaptureResultSig {
    pub slice: Option<CaptureSliceSig>,
    pub leaves: Vec<CaptureLeafSig>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CaptureSliceSig {
    pub capture: usize,
    /// The record-field path inside the capture when the result borrows a field
    /// of a captured borrowed record rather than the captured slice itself.
    pub path: Option<Vec<usize>>,
    pub mutable: bool,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CaptureLeafSig {
    pub path: Vec<usize>,
    pub capture: usize,
    pub mutable: bool,
}
/// One borrowed record leaf in a callable contract. Lifetimes are canonical
/// (`#0`, `#1`, ...) just like `BorrowSig::parameters`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BorrowLeafSig {
    pub path: Vec<usize>,
    pub lifetime: Option<String>,
    pub mutable: bool,
}
impl BorrowSig {
    /// Canonicalize slice parameters, a slice result, and borrowed record
    /// leaves together. Names are numbered in one order so a lifetime shared by
    /// a slice parameter and a record field keeps a single identity.
    pub fn canonical_with_leaves(
        parameters: &[Option<String>],
        result: Option<&String>,
        parameter_leaves: &[Vec<BorrowLeaf>],
        result_leaves: &[BorrowLeaf],
        bounds: &BTreeSet<(String, String)>,
    ) -> Self {
        let mut order: Vec<String> = Vec::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut push = |name: &String| {
            if seen.insert(name.clone()) {
                order.push(name.clone());
            }
        };
        for name in parameters.iter().flatten() {
            push(name);
        }
        if let Some(name) = result {
            push(name);
        }
        for leaves in parameter_leaves {
            for leaf in leaves {
                if let Some(name) = &leaf.lifetime {
                    push(name);
                }
            }
        }
        for leaf in result_leaves {
            if let Some(name) = &leaf.lifetime {
                push(name);
            }
        }
        if order.is_empty() {
            return Self::default();
        }
        let names = order
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), format!("#{index}")))
            .collect::<BTreeMap<_, _>>();
        let canonical = |name: &String| names[name].clone();
        let parameters = parameters
            .iter()
            .map(|name| name.as_ref().map(canonical))
            .collect::<Vec<_>>();
        let result = result.map(canonical);
        let parameter_leaves = parameter_leaves
            .iter()
            .map(|leaves| {
                leaves
                    .iter()
                    .map(|leaf| BorrowLeafSig {
                        path: leaf.path.clone(),
                        lifetime: leaf.lifetime.as_ref().map(canonical),
                        mutable: leaf.mutable,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let result_leaves = result_leaves
            .iter()
            .map(|leaf| BorrowLeafSig {
                path: leaf.path.clone(),
                lifetime: leaf.lifetime.as_ref().map(canonical),
                mutable: leaf.mutable,
            })
            .collect::<Vec<_>>();
        Self {
            parameters,
            result,
            parameter_leaves,
            result_leaves,
            capture_result: None,
            bounds: bounds
                .iter()
                .filter_map(|(long, short)| {
                    Some((names.get(long)?.clone(), names.get(short)?.clone()))
                })
                .collect(),
        }
    }
    fn outlives(&self, long: &str, short: &str) -> bool {
        crate::executable::outlives(&self.bounds, long, short)
    }
    /// Whether a callable with contract `self` may be used where `target` is
    /// expected. Target lifetimes are rigid; each source lifetime is
    /// instantiated by the target lifetimes at the same parameter positions
    /// (plus the target result for the source result). The source's bounds must
    /// then follow from the target's, and every source parameter that can flow
    /// into the source result must map to target lifetimes outliving the
    /// target result, so the target's call-site provenance covers it.
    pub fn usable_as(&self, target: &BorrowSig) -> bool {
        // A closure result borrowed from its environment is not expressible by
        // an ordinary arrow. Only an identical contract may be used in the
        // same position; a representation-changing coercion would lose it.
        if self.capture_result != target.capture_result {
            return false;
        }
        let arity = self
            .parameters
            .len()
            .max(target.parameters.len())
            .max(self.parameter_leaves.len())
            .max(target.parameter_leaves.len());
        let at = |sig: &BorrowSig, i: usize| sig.parameters.get(i).cloned().flatten();
        // One source lifetime maps to every target lifetime that occupies the
        // same position. Record leaves add positions beyond the slice
        // parameters; a leaf may only map to a leaf at the same path.
        let mut pairs: Vec<(String, String)> = Vec::new();
        for i in 0..arity {
            match (at(self, i), at(target, i)) {
                (Some(source), Some(target)) => pairs.push((source, target)),
                (None, None) => {}
                _ => return false,
            }
            let source_leaves = self
                .parameter_leaves
                .get(i)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let target_leaves = target
                .parameter_leaves
                .get(i)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            if source_leaves.len() != target_leaves.len() {
                return false;
            }
            for source in source_leaves {
                let Some(target_leaf) = target_leaves.iter().find(|leaf| leaf.path == source.path)
                else {
                    return false;
                };
                match (&source.lifetime, &target_leaf.lifetime) {
                    (Some(source), Some(target)) => pairs.push((source.clone(), target.clone())),
                    (None, None) => {}
                    _ => return false,
                }
            }
        }
        match (&self.result, &target.result) {
            (Some(source), Some(target)) => pairs.push((source.clone(), target.clone())),
            (None, None) => {}
            _ => return false,
        }
        if self.result_leaves.len() != target.result_leaves.len() {
            return false;
        }
        for source in &self.result_leaves {
            let Some(target_leaf) = target
                .result_leaves
                .iter()
                .find(|leaf| leaf.path == source.path)
            else {
                return false;
            };
            match (&source.lifetime, &target_leaf.lifetime) {
                (Some(source), Some(target)) => pairs.push((source.clone(), target.clone())),
                (None, None) => {}
                _ => return false,
            }
        }
        let mut map: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (source, target) in pairs {
            map.entry(source).or_default().insert(target);
        }
        for (long, short) in &self.bounds {
            let (Some(longs), Some(shorts)) = (map.get(long), map.get(short)) else {
                continue;
            };
            if !longs
                .iter()
                .all(|l| shorts.iter().all(|s| target.outlives(l, s)))
            {
                return false;
            }
        }
        if let (Some(source_result), Some(target_result)) = (&self.result, &target.result) {
            for i in 0..arity {
                let (Some(source), Some(mapped)) = (at(self, i), at(target, i)) else {
                    continue;
                };
                if self.outlives(&source, source_result) && !target.outlives(&mapped, target_result)
                {
                    return false;
                }
            }
        }
        for i in 0..arity {
            let source_leaves = self
                .parameter_leaves
                .get(i)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let target_leaves = target
                .parameter_leaves
                .get(i)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            for source in source_leaves {
                let Some(target_leaf) = target_leaves.iter().find(|leaf| leaf.path == source.path)
                else {
                    return false;
                };
                let (Some(source_lifetime), Some(mapped)) =
                    (&source.lifetime, &target_leaf.lifetime)
                else {
                    continue;
                };
                let Some(source_result) = self
                    .result_leaves
                    .iter()
                    .find(|leaf| leaf.path == source.path)
                else {
                    continue;
                };
                let Some(target_result) = target
                    .result_leaves
                    .iter()
                    .find(|leaf| leaf.path == source.path)
                else {
                    return false;
                };
                if let (Some(source_result), Some(target_result)) =
                    (&source_result.lifetime, &target_result.lifetime)
                    && self.outlives(source_lifetime, source_result)
                    && !target.outlives(mapped, target_result)
                {
                    return false;
                }
            }
        }
        true
    }
}
/// Memoization key for one nominal layout: declaration, type arguments,
/// compile-time natural arguments, and erased lifetime labels.
type LayoutKey = (BindingId, Vec<Type>, Vec<usize>, Vec<String>);
/// The checked signature of a first-class callable. `once` distinguishes a
/// copyable, noncapturing function pointer from an owning, at-most-once
/// closure value. `linear` marks the linear-once mode: the callable carries
/// captured linear obligations and must be consumed by exactly one call.
/// Parameter grades are part of the callable contract and are checked
/// covariantly when a function value is used at a wider arrow type.
/// `result_grade` is a static transfer contract: only `@[1]` on an owning or
/// intrinsically linear result is representable, and it requires an exact
/// match across subtyping, coercion, and adapters. It has no runtime
/// representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FunctionType {
    pub parameters: Vec<Type>,
    pub result: Type,
    pub effects: u8,
    pub parameter_grades: Vec<Option<Grade>>,
    pub result_grade: Option<Grade>,
    pub once: bool,
    pub linear: bool,
    pub borrows: BorrowSig,
}
/// Whether a usage grade physically erases the value it annotates. `@[0]` and
/// any custom algebra's additive identity are erasure annotations.
pub(crate) fn grade_erases(grade: Option<Grade>) -> bool {
    grade.is_some_and(Grade::is_zero)
}
impl FunctionType {
    /// Whether logical parameter `index` has no physical ABI slot. A grade-zero
    /// parameter is still evaluated at the source call site and remains in the
    /// logical parameter list, but it is absent from the calling convention.
    pub(crate) fn parameter_erased(&self, index: usize) -> bool {
        grade_erases(self.parameter_grades.get(index).copied().flatten())
    }
    /// Whether the callable result is physically erased. A `@[0]` result has no
    /// returned payload; callers observe `Unit`.
    pub(crate) fn result_erased(&self) -> bool {
        grade_erases(self.result_grade)
    }
}
#[derive(Debug, Clone, Copy)]
pub(crate) struct ResultShape {
    pub ok_tag: usize,
    pub err_tag: usize,
    pub ok: Type,
    pub error: Type,
}
/// The conventional `Option<T> { None, Some(T) }` returned by
/// `Slice.try_get`. Only the exact shape is accepted; either declaration order
/// and therefore either tag numbering is allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct OptionShape {
    pub some_tag: usize,
    pub none_tag: usize,
    pub result: Type,
}
#[derive(Clone, Copy)]
struct Definition<'a> {
    name: &'a str,
    lifetimes: &'a [ast::Lifetime],
    generics: &'a [ast::Generic],
    variants: &'a [ast::Variant],
    /// Present for records.
    fields: Option<&'a [ast::Field]>,
    linear: bool,
}
/// Whether a type is the reserved unsized text type `str`, which is only
/// admitted behind a shared borrow as `&str`.
fn is_str_type(ty: &ast::Type) -> bool {
    matches!(
        &ty.kind,
        ast::TypeKind::Named { path, arguments }
            if arguments.is_empty() && path.len() == 1 && path[0] == "str"
    )
}
pub(crate) struct Types<'a> {
    resolution: &'a Resolution,
    logical: &'a LogicalEnvironment,
    definitions: BTreeMap<BindingId, Definition<'a>>,
    aliases: BTreeMap<BindingId, Alias<'a>>,
    alias_active: BTreeSet<BindingId>,
    pub enums: Vec<Enum>,
    pub pointees: Vec<Type>,
    pub unions: Vec<UnionType>,
    pub function_types: Vec<FunctionType>,
    cache: BTreeMap<LayoutKey, usize>,
    union_cache: BTreeMap<Vec<Type>, usize>,
    /// Canonical structural record rows. Fields are sorted by name, so the key
    /// is both the interning identity and the runtime storage order.
    structural_cache: BTreeMap<Vec<(String, Type)>, usize>,
    function_cache: BTreeMap<FunctionKey, usize>,
    active: BTreeSet<BindingId>,
    /// Trait objects by `(trait, trait arguments)`. A trait with a finite
    /// non-generic member set keeps the legacy inline closed-world union; an
    /// open/generic member set, or any trait used inside a nominal field, uses
    /// the dynamically dispatched fat object below.
    pub dyn_objects: BTreeMap<(BindingId, TraitArguments), Type>,
    /// Dynamically dispatched trait-object specializations, indexed by
    /// `Type::DynObj`. Interning is by `(trait, trait arguments)`.
    pub objects: Vec<DynObjectType>,
    object_cache: BTreeMap<(BindingId, TraitArguments), usize>,
    /// Traits whose objects cannot use the inline closed-world union because
    /// they have generic/blanket impls or appear in a nominal field. This is
    /// decided before layouts are built so a field can hold a fixed-size fat
    /// object without knowing the member set.
    pub dynamic_traits: BTreeSet<BindingId>,
    /// Traits that cannot be used as `dyn` objects, with the checked reason.
    pub dyn_errors: BTreeMap<BindingId, String>,
    /// Monotonic source of compiler-internal lifetime identities for inferred
    /// local record construction and call-argument freshening. These names are
    /// not surface syntax and cannot collide with declared lifetimes.
    inferred_lifetimes: usize,
    /// Erased lifetime names attached to reference elements stored in
    /// containers. Index 0 is the empty/elided label, so an unannotated
    /// container element contributes no declared lifetime.
    pub reference_labels: Vec<String>,
}
impl<'a> Types<'a> {
    pub fn new(
        module: &'a ast::Module,
        resolution: &'a Resolution,
        logical: &'a LogicalEnvironment,
        dynamic_traits: BTreeSet<BindingId>,
    ) -> Result<Self> {
        let mut definitions = BTreeMap::new();
        let mut aliases = BTreeMap::new();
        for declaration in &module.items {
            if matches!(
                declaration.item.kind,
                ast::ItemKind::Enum { total: true, .. } | ast::ItemKind::Prop { .. }
            ) {
                // Logical data and propositions are erased and live only in
                // the kernel.
                continue;
            }
            if !matches!(
                declaration.item.kind,
                ast::ItemKind::Enum { .. }
                    | ast::ItemKind::Struct { .. }
                    | ast::ItemKind::Alias { .. }
            ) {
                continue;
            }
            let id = resolution.declarations[&declaration.item.span.start];
            let (name, lifetimes, generics, variants, fields) = match &declaration.item.kind {
                ast::ItemKind::Enum {
                    name,
                    generics,
                    variants,
                    ..
                } => (name, &[][..], generics, variants.as_slice(), None),
                ast::ItemKind::Struct {
                    name,
                    lifetimes,
                    generics,
                    fields,
                } => (
                    name,
                    lifetimes.as_slice(),
                    generics,
                    &[][..],
                    Some(fields.as_slice()),
                ),
                ast::ItemKind::Alias {
                    lifetimes,
                    generics,
                    ty,
                    ..
                } => {
                    let mut seen = BTreeSet::new();
                    for lifetime in lifetimes {
                        if let Some(bound) = lifetime.bounds.first() {
                            return Err(Diagnostic::new(
                                bound.span,
                                "outlives bounds are only supported on executable function signatures; a type alias lifetime cannot declare a bound",
                            ));
                        }
                        if !seen.insert(lifetime.name.clone()) {
                            return Err(Diagnostic::new(
                                lifetime.span,
                                format!("duplicate lifetime parameter '{}'", lifetime.name),
                            ));
                        }
                        if generics.iter().any(|generic| generic.name == lifetime.name) {
                            return Err(Diagnostic::new(
                                lifetime.span,
                                "alias lifetime parameters must be distinct from type, natural, grade, and effect generics",
                            ));
                        }
                    }
                    aliases.insert(
                        id,
                        Alias {
                            lifetimes,
                            generics,
                            ty,
                        },
                    );
                    continue;
                }
                _ => continue,
            };
            if fields.is_none() && (variants.is_empty() || variants.len() > 64) {
                return Err(Diagnostic::new(
                    declaration.item.span,
                    "runtime enums require 1..64 variants",
                ));
            }
            if fields.is_some_and(|f| f.len() > 64) {
                return Err(Diagnostic::new(
                    declaration.item.span,
                    "records support at most 64 fields",
                ));
            }
            for generic in generics {
                if let Some(bound) = &generic.bound {
                    let valid = matches!(&bound.kind, ast::TypeKind::Named { arguments, .. } if arguments.is_empty())
                        && resolution.reference(bound.span).is_some_and(|id| {
                            resolution.bindings[id].kind == BindingKind::Builtin
                                && matches!(resolution.bindings[id].name.as_str(), "Type" | "Nat")
                        });
                    if !valid {
                        return Err(Diagnostic::new(
                            generic.span,
                            "runtime data parameters must be ordinary types or natural const parameters ('N: Nat'); grade parameters belong to functions and bindings",
                        ));
                    }
                }
            }
            // A natural const parameter must actually index a length in this
            // declaration. This keeps phantom const parameters from being
            // confused with type parameters and preserves the existing
            // "ordinary types" rejection for unused indices.
            for generic in generics {
                if !is_const_generic(resolution, generic) {
                    continue;
                }
                let id = resolution.binder(generic.span).unwrap();
                if !data_uses_const(fields.unwrap_or(&[]), variants, resolution, id) {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "runtime data parameters must be ordinary types: natural parameter '{}' is not used as an array length",
                            generic.name
                        ),
                    ));
                }
            }
            // Validate compile-time lengths in the declaration itself, so an
            // unused generic data type cannot hide an unbound or runtime index.
            let mut template_types = Vec::new();
            if let Some(fields) = fields {
                template_types.extend(fields.iter().map(|field| &field.ty));
            }
            for variant in variants {
                if !variant.locals.is_empty() {
                    return Err(Diagnostic::new(
                        variant.span,
                        "constructor-local binders are only supported by 'total enum' and 'prop' declarations",
                    ));
                }
                match &variant.payload {
                    ast::Payload::Unit => {}
                    ast::Payload::Tuple(types) => template_types.extend(types.iter()),
                    ast::Payload::Fields(_) => {
                        return Err(Diagnostic::new(
                            variant.span,
                            "named logical constructor fields are only supported by 'total enum' and 'prop' declarations, not runtime enums",
                        ));
                    }
                    ast::Payload::Record(fields) => {
                        template_types.extend(fields.iter().map(|field| &field.ty))
                    }
                }
                if let Some(result) = &variant.result {
                    template_types.push(result);
                }
            }
            crate::executable::validate_type_templates_for(resolution, generics, &template_types)?;
            for variant in variants {
                if variant.result.is_some() || matches!(variant.payload, ast::Payload::Record(_)) {
                    return Err(Diagnostic::new(
                        variant.span,
                        "runtime enum variants currently support unit or tuple payloads, without indexed result types",
                    ));
                }
            }
            let linear = declaration.attributes.iter().any(|a| a.kind == "linear");
            if let Some(fields) = fields {
                validate_record_declaration(
                    declaration.item.span,
                    lifetimes,
                    generics,
                    fields,
                    linear,
                )?;
            }
            definitions.insert(
                resolution.declarations[&declaration.item.span.start],
                Definition {
                    name,
                    lifetimes,
                    generics,
                    variants,
                    fields,
                    linear,
                },
            );
        }
        let mut result = Self {
            resolution,
            logical,
            definitions,
            aliases,
            alias_active: BTreeSet::new(),
            enums: Vec::new(),
            pointees: Vec::new(),
            unions: Vec::new(),
            function_types: Vec::new(),
            cache: BTreeMap::new(),
            union_cache: BTreeMap::new(),
            structural_cache: BTreeMap::new(),
            function_cache: BTreeMap::new(),
            active: BTreeSet::new(),
            dyn_objects: BTreeMap::new(),
            objects: Vec::new(),
            object_cache: BTreeMap::new(),
            dynamic_traits,
            dyn_errors: BTreeMap::new(),
            inferred_lifetimes: 0,
            reference_labels: vec![String::new()],
        };
        let monomorphic = result
            .definitions
            .iter()
            // A declaration with erased lifetime parameters still needs a use
            // site to supply its lifetime arguments.
            .filter(|(_, d)| d.generics.is_empty() && d.lifetimes.is_empty())
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        for id in monomorphic {
            result.instantiate(id, vec![], vec![], vec![], resolution.bindings[id].span)?;
        }
        Ok(result)
    }
    pub fn array(&mut self, element: Type, length: usize, span: Span) -> Result<Type> {
        if length > 31
            || 1 + self.width(element) * length > MAX_WORDS
            || matches!(
                element,
                Type::Ref(_) | Type::RefMut(_) | Type::Slice(_) | Type::SliceMut(_) | Type::Str
            )
            || has_borrow(self, element)
        {
            return Err(Diagnostic::new(
                span,
                "inline array exceeds the 32-word layout budget or stores references/slice views/borrowed text views/borrowed records",
            ));
        }
        if contains_task(self, element) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in arrays; join them in the scope that owns them",
            ));
        }
        if let Some(id) = self
            .enums
            .iter()
            .position(|e| e.array == Some((element, length)))
        {
            return Ok(Type::Enum(id));
        }
        if self.enums.len() >= 256 {
            return Err(Diagnostic::new(span, "array layout budget exhausted"));
        }
        let id = self.enums.len();
        self.enums.push(Enum {
            definition: usize::MAX,
            name: format!("[{}; {}]", self.name(element), length),
            arguments: vec![element],
            consts: vec![],
            lifetimes: vec![],
            variants: vec![Variant {
                name: "Array".into(),
                fields: vec![element; length],
                tuple: true,
                names: vec![],
            }],
            words: 1 + self.width(element) * length,
            result: None,
            record: false,
            field_lifetimes: vec![],
            borrowed: false,
            mutable_borrow: false,
            linear: false,
            array: Some((element, length)),
            dynamic_array: None,
            tuple: false,
            structural: false,
        });
        Ok(Type::Enum(id))
    }
    /// Intern a runtime-sized inline array `DynArray<T, capacity>`. Word zero is
    /// the runtime length; the remaining `capacity * width(T)` words are inline
    /// storage. The capacity is a compile-time bound, so the layout is finite
    /// and a value may be moved or returned without a hidden stack pointer.
    pub fn dynamic_array(&mut self, element: Type, capacity: usize, span: Span) -> Result<Type> {
        if capacity == 0 || capacity > 31 {
            return Err(Diagnostic::new(
                span,
                "DynArray capacity must be 1..31 (word zero stores the runtime length and the 32-word layout limit applies)",
            ));
        }
        if matches!(
            element,
            Type::Ref(_)
                | Type::RefMut(_)
                | Type::Slice(_)
                | Type::SliceMut(_)
                | Type::Str
                | Type::Never
        ) || has_borrow(self, element)
        {
            return Err(Diagnostic::new(
                span,
                "DynArray elements must be concrete non-borrowed values; a view cannot escape the inline storage",
            ));
        }
        if contains_task(self, element) || contains_linear(self, element) {
            return Err(Diagnostic::new(
                span,
                "DynArray elements cannot be task handles or carry linear obligations; use an explicit record/vector for owned linear payloads",
            ));
        }
        let width = self.width(element);
        if 1 + width * capacity > MAX_WORDS {
            return Err(Diagnostic::new(
                span,
                "DynArray exceeds the 32-word inline layout budget; reduce its capacity or element width",
            ));
        }
        if let Some(id) = self
            .enums
            .iter()
            .position(|e| e.dynamic_array == Some((element, capacity)))
        {
            return Ok(Type::Enum(id));
        }
        if self.enums.len() >= 256 {
            return Err(Diagnostic::new(span, "DynArray layout budget exhausted"));
        }
        let id = self.enums.len();
        self.enums.push(Enum {
            definition: usize::MAX,
            name: format!("DynArray<{}; {}>", self.name(element), capacity),
            arguments: vec![element],
            consts: vec![capacity],
            lifetimes: vec![],
            variants: vec![Variant {
                name: "DynArray".into(),
                fields: vec![element; capacity],
                tuple: false,
                names: vec![],
            }],
            words: 1 + width * capacity,
            result: None,
            record: true,
            field_lifetimes: vec![None; capacity],
            borrowed: false,
            mutable_borrow: false,
            linear: false,
            array: None,
            dynamic_array: Some((element, capacity)),
            tuple: false,
            structural: false,
        });
        Ok(Type::Enum(id))
    }
    /// Intern an anonymous structural record row. Fields are sorted by name:
    /// this is the canonical row representation used for layout, equality, and
    /// field coercion. Duplicate names are rejected, so the ordering is total.
    pub fn structural(&mut self, mut fields: Vec<(String, Type)>, span: Span) -> Result<Type> {
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        if fields.is_empty() {
            return Err(Diagnostic::new(
                span,
                "a structural record type must have at least one field",
            ));
        }
        if fields.len() > 64 {
            return Err(Diagnostic::new(
                span,
                "structural records support at most 64 fields",
            ));
        }
        for pair in fields.windows(2) {
            if pair[0].0 == pair[1].0 {
                return Err(Diagnostic::new(
                    span,
                    format!("duplicate structural record field '{}'", pair[0].0),
                ));
            }
        }
        for (name, ty) in &fields {
            if *ty == Type::Never {
                return Err(Diagnostic::new(
                    span,
                    format!("structural record field '{name}' cannot have type Never"),
                ));
            }
            if matches!(ty, Type::Ref(_) | Type::RefMut(_)) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "structural record field '{name}' cannot store an owner reference; use a by-value owner, a slice view, or a borrowed record"
                    ),
                ));
            }
            if contains_task(self, *ty) {
                return Err(Diagnostic::new(
                    span,
                    format!("structural record field '{name}' cannot store a task handle"),
                ));
            }
        }
        let words = 1 + fields.iter().map(|(_, ty)| self.width(*ty)).sum::<usize>();
        if words > MAX_WORDS {
            return Err(Diagnostic::new(
                span,
                "structural record exceeds the 32-word layout limit",
            ));
        }
        if let Some(id) = self.structural_cache.get(&fields) {
            return Ok(Type::Enum(*id));
        }
        if self.enums.len() >= 256 {
            return Err(Diagnostic::new(
                span,
                "structural record layout budget exhausted (256)",
            ));
        }
        let borrowed = fields.iter().any(|(_, ty)| has_borrow(self, *ty));
        let mutable_borrow = fields.iter().any(|(_, ty)| has_mutable_borrow(self, *ty));
        let linear = fields.iter().any(|(_, ty)| contains_linear(self, *ty));
        let id = self.enums.len();
        let name = format!(
            "struct {{ {} }}",
            fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", self.name(*ty)))
                .collect::<Vec<_>>()
                .join(", ")
        );
        self.enums.push(Enum {
            definition: usize::MAX,
            name,
            arguments: fields.iter().map(|(_, ty)| *ty).collect(),
            consts: vec![],
            lifetimes: vec![],
            variants: vec![Variant {
                name: "Struct".into(),
                fields: fields.iter().map(|(_, ty)| *ty).collect(),
                tuple: false,
                names: fields.iter().map(|(name, _)| name.clone()).collect(),
            }],
            words,
            result: None,
            record: true,
            field_lifetimes: vec![None; fields.len()],
            borrowed,
            mutable_borrow,
            linear,
            array: None,
            dynamic_array: None,
            tuple: false,
            structural: true,
        });
        self.structural_cache.insert(fields, id);
        Ok(Type::Enum(id))
    }
    /// Whether a layout is an anonymous structural record.
    pub fn is_structural(&self, ty: Type) -> bool {
        ty.layout().is_some_and(|id| self.enums[id].structural)
    }
    /// An anonymous tuple layout `(A, B, ...)`: a record whose fields are
    /// named `0`, `1`, ... Equal element types give the same layout.
    pub fn tuple(&mut self, elements: Vec<Type>, span: Span) -> Result<Type> {
        if elements.len() == 1 {
            return Err(Diagnostic::new(
                span,
                "one-element tuples are not supported; write '()' for unit or omit the trailing comma",
            ));
        }
        if elements.len() < 2 || elements.len() > 16 {
            return Err(Diagnostic::new(span, "tuples have 2 to 16 elements"));
        }
        for element in &elements {
            if matches!(element, Type::Ref(_) | Type::RefMut(_) | Type::Never)
                || element.is_view()
                || has_borrow(self, *element)
            {
                return Err(Diagnostic::new(
                    span,
                    "tuples cannot store references, slice views, or borrowed records (including &str text views); use a borrowed record instead",
                ));
            }
            if contains_task(self, *element) {
                return Err(Diagnostic::new(
                    span,
                    "task handles cannot be stored in tuples",
                ));
            }
        }
        if let Some(id) = self
            .enums
            .iter()
            .position(|e| e.tuple && e.arguments == elements)
        {
            return Ok(Type::Enum(id));
        }
        let words = 1 + elements.iter().map(|t| self.width(*t)).sum::<usize>();
        if words > MAX_WORDS {
            return Err(Diagnostic::new(
                span,
                "tuple exceeds the 32-word layout limit",
            ));
        }
        if self.enums.len() >= 256 {
            return Err(Diagnostic::new(span, "tuple layout budget exhausted"));
        }
        let linear = elements.iter().any(|t| contains_linear(self, *t));
        let id = self.enums.len();
        self.enums.push(Enum {
            definition: usize::MAX,
            name: format!(
                "({})",
                elements
                    .iter()
                    .map(|t| self.name(*t))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            arguments: elements.clone(),
            consts: vec![],
            lifetimes: vec![],
            variants: vec![Variant {
                name: "Tuple".into(),
                fields: elements.clone(),
                tuple: true,
                names: (0..elements.len()).map(|i| i.to_string()).collect(),
            }],
            words,
            result: None,
            record: true,
            field_lifetimes: vec![None; elements.len()],
            borrowed: false,
            mutable_borrow: false,
            linear,
            array: None,
            dynamic_array: None,
            tuple: true,
            structural: false,
        });
        Ok(Type::Enum(id))
    }
    pub fn width(&self, ty: Type) -> usize {
        width(
            &self.pointees,
            &self.enums,
            &self.unions,
            &self.function_types,
            ty,
        )
    }
    /// Whether dropping this value can release storage or a linear obligation.
    /// Mirrors the executable checker's ownership predicate for the checked
    /// runtime type graph. Depth is bounded so binary recursive data cannot
    /// cause unbounded work.
    pub(crate) fn owns(&self, ty: Type) -> bool {
        fn go(types: &Types<'_>, ty: Type, depth: usize) -> bool {
            match ty {
                Type::Box(p) | Type::Vec(p) if depth < 64 => {
                    go(types, types.pointees[p], depth + 1)
                }
                Type::Bytes
                | Type::String
                | Type::Box(_)
                | Type::Vec(_)
                | Type::Once(_)
                | Type::Task(_)
                | Type::DynObj(_) => true,
                Type::Enum(id) | Type::Variants(id, _) if depth < 64 => {
                    types.enums[id].linear
                        || types.enums[id].variants.iter().any(|variant| {
                            variant
                                .fields
                                .iter()
                                .any(|field| go(types, *field, depth + 1))
                        })
                }
                Type::Union(id) if depth < 64 => types.unions[id]
                    .members
                    .iter()
                    .any(|member| go(types, *member, depth + 1)),
                _ => false,
            }
        }
        go(self, ty, 0)
    }
    /// Intern a checked callable signature. The `once` flag is part of the
    /// identity because it changes representation (one word vs two) and the
    /// callable usage contract.
    /// Intern a callable type that may carry a slice borrow contract and a
    /// static result-transfer contract.
    #[allow(clippy::too_many_arguments)]
    pub fn function_type_with(
        &mut self,
        parameters: Vec<Type>,
        result: Type,
        effects: u8,
        parameter_grades: Vec<Option<Grade>>,
        result_grade: Option<Grade>,
        once: bool,
        linear: bool,
        borrows: BorrowSig,
    ) -> usize {
        let linear = once && linear;
        let key = (
            parameters,
            result,
            effects,
            parameter_grades,
            result_grade,
            once,
            linear,
            borrows,
        );
        if let Some(id) = self.function_cache.get(&key) {
            return *id;
        }
        let id = self.function_types.len();
        self.function_types.push(FunctionType {
            parameters: key.0.clone(),
            result: key.1,
            effects: key.2,
            parameter_grades: key.3.clone(),
            result_grade: key.4,
            once: key.5,
            linear: key.6,
            borrows: key.7.clone(),
        });
        self.function_cache.insert(key, id);
        id
    }
    /// Forget variant refinements, including inside a heterogeneous union.
    /// Stored and reassignable values keep the declared enum alternatives.
    pub fn full(&mut self, ty: Type, span: Span) -> Result<Type> {
        match ty {
            Type::Variants(id, _) => Ok(Type::Enum(id)),
            Type::Union(id) => {
                let members = self.unions[id].members.clone();
                let widened = members
                    .into_iter()
                    .map(|member| match member {
                        Type::Variants(id, _) => Type::Enum(id),
                        other => other,
                    })
                    .collect::<Vec<_>>();
                self.union(widened, span)
            }
            _ => Ok(ty),
        }
    }
    /// Lower a type inside a specialized generic function or alias.
    pub fn ty_in(&mut self, ty: &ast::Type, substitution: &Subst) -> Result<Type> {
        let ty = self.lower(ty, substitution, 0)?;
        self.finish_layouts(ty_span(ty, Span::default()))?;
        Ok(ty)
    }
    pub fn record_fields(&self, id: BindingId) -> (&'a [ast::Generic], &'a [ast::Field]) {
        let d = self.definitions[&id];
        (d.generics, d.fields.unwrap())
    }
    pub fn record_lifetimes(&self, id: BindingId) -> &'a [ast::Lifetime] {
        self.definitions[&id].lifetimes
    }
    pub fn is_record(&self, id: BindingId) -> bool {
        self.definitions
            .get(&id)
            .is_some_and(|d| d.fields.is_some())
    }
    /// A fresh compiler-internal lifetime identity for local record inference
    /// and call-argument freshening. It is not surface syntax.
    pub fn fresh_lifetime(&mut self, prefix: &str) -> String {
        let index = self.inferred_lifetimes;
        self.inferred_lifetimes += 1;
        format!("<{prefix} {index}>")
    }
    /// Whether two record instances differ only in erased lifetime labels. The
    /// runtime layout and every non-lifetime type argument are identical, so
    /// one can be used where the other is expected; the caller is responsible
    /// for relating the actual value's field provenance at a call boundary.
    pub fn same_erased_shape(&self, left: Type, right: Type) -> bool {
        fn go(
            types: &Types<'_>,
            left: Type,
            right: Type,
            depth: usize,
            seen: &mut BTreeSet<(Type, Type)>,
        ) -> bool {
            if left == right {
                return true;
            }
            if depth >= 32 || !seen.insert((left, right)) {
                return false;
            }
            match (left, right) {
                (Type::Enum(a), Type::Enum(b)) | (Type::Variants(a, _), Type::Enum(b))
                    if types.enums[a].record && types.enums[b].record =>
                {
                    if types.enums[a].structural || types.enums[b].structural {
                        // Structural rows are interned by canonical field row,
                        // so only exact identity is representation-equivalent.
                        return false;
                    }
                    let (a, b) = (&types.enums[a], &types.enums[b]);
                    a.definition == b.definition
                        && a.consts == b.consts
                        && a.arguments.len() == b.arguments.len()
                        && a.arguments
                            .iter()
                            .zip(&b.arguments)
                            .all(|(left, right)| go(types, *left, *right, depth + 1, seen))
                }
                (Type::Slice(a), Type::Slice(b))
                | (Type::SliceMut(a), Type::SliceMut(b))
                | (Type::Ref(a), Type::Ref(b))
                | (Type::RefMut(a), Type::RefMut(b)) => {
                    go(types, types.pointees[a], types.pointees[b], depth + 1, seen)
                }
                (Type::Box(a), Type::Box(b)) | (Type::Vec(a), Type::Vec(b)) => {
                    go(types, types.pointees[a], types.pointees[b], depth + 1, seen)
                }
                (Type::Annotated(a, _), b) => go(types, types.pointees[a], b, depth + 1, seen),
                (a, Type::Annotated(b, _)) => go(types, a, types.pointees[b], depth + 1, seen),
                (Type::Enum(a), Type::Enum(b))
                    if types.enums[a].name == "TaskExit" && types.enums[b].name == "TaskExit" =>
                {
                    let (a, b) = (&types.enums[a], &types.enums[b]);
                    a.definition == b.definition
                        && a.consts == b.consts
                        && a.arguments.len() == b.arguments.len()
                        && a.arguments
                            .iter()
                            .zip(&b.arguments)
                            .all(|(left, right)| go(types, *left, *right, depth + 1, seen))
                }
                (Type::Union(a), Type::Union(b)) => {
                    types.unions[a].members.len() == types.unions[b].members.len()
                        && types.unions[a]
                            .members
                            .iter()
                            .zip(&types.unions[b].members)
                            .all(|(left, right)| go(types, *left, *right, depth + 1, seen))
                }
                _ => false,
            }
        }
        go(self, left, right, 0, &mut BTreeSet::new())
    }
    /// Erase a callable parameter's record lifetimes to fresh local identities.
    /// Passing `Window<'x, i64>` to a parameter written `Window<'a, i64>` is a
    /// checked instantiation, not a silent relabeling: the argument's own field
    /// provenance is related to `'a` by the caller.
    pub fn freshen_borrows(&mut self, ty: Type, span: Span) -> Result<Type> {
        let mut map = BTreeMap::new();
        self.freshen_borrows_with(ty, &mut map, span)
    }
    fn freshen_borrows_with(
        &mut self,
        ty: Type,
        map: &mut BTreeMap<String, String>,
        span: Span,
    ) -> Result<Type> {
        match ty {
            Type::Enum(id) if self.enums[id].structural => Ok(ty),
            Type::Enum(id) if self.enums[id].record && self.enums[id].borrowed => {
                let definition = self.enums[id].definition;
                let consts = self.enums[id].consts.clone();
                let arguments = self.enums[id].arguments.clone();
                let lifetimes = self.enums[id].lifetimes.clone();
                let mut fresh_arguments = Vec::new();
                for argument in arguments {
                    fresh_arguments.push(self.freshen_borrows_with(argument, map, span)?);
                }
                let mut fresh_lifetimes = Vec::new();
                for (index, lifetime) in lifetimes.into_iter().enumerate() {
                    let fresh = if let Some(fresh) = map.get(&lifetime) {
                        fresh.clone()
                    } else {
                        // Deterministic per record instance and lifetime
                        // position: argument labels are checker-only and must
                        // not burn a fresh layout instantiation per call.
                        let fresh = format!("<argument lifetime {id}:{index}>");
                        map.insert(lifetime, fresh.clone());
                        fresh
                    };
                    fresh_lifetimes.push(fresh);
                }
                self.instantiate(definition, fresh_arguments, consts, fresh_lifetimes, span)
                    .map(Type::Enum)
            }
            Type::Variants(..)
            | Type::Slice(_)
            | Type::SliceMut(_)
            | Type::Str
            | Type::Ref(_)
            | Type::RefMut(_) => Ok(ty),
            _ => Ok(ty),
        }
    }
    /// The declared generic parameters and right-hand side of a type alias.
    pub fn alias_definition(&self, id: BindingId) -> Option<(&'a [ast::Generic], &'a ast::Type)> {
        self.aliases
            .get(&id)
            .map(|alias| (alias.generics, alias.ty))
    }
    /// Number of erased lifetime parameters of a type alias.
    pub fn alias_lifetime_count(&self, id: BindingId) -> Option<usize> {
        self.aliases.get(&id).map(|alias| alias.lifetimes.len())
    }
    /// The trusted logical environment used for constant-length evaluation.
    pub(crate) fn logical(&self) -> &'a LogicalEnvironment {
        self.logical
    }
    /// The nominal layout index of a declared record/enum binding, when it is
    /// instantiated without generic arguments. Used to resolve `Type.CONST`
    /// projections before type lowering.
    pub fn nominal_by_binding(&self, id: BindingId) -> Option<usize> {
        self.enums
            .iter()
            .position(|layout| layout.definition == id && layout.arguments.is_empty())
    }
    /// Human-readable type name for diagnostics.
    pub fn name(&self, ty: Type) -> String {
        match ty {
            Type::I64 => "i64".into(),
            Type::Int(kind) => kind.name().into(),
            Type::Float(kind) => kind.name().into(),
            Type::Char => "Char".into(),
            Type::Bool => "Bool".into(),
            Type::Unit => "Unit".into(),
            Type::Never => "Never".into(),
            Type::Bytes => "Bytes".into(),
            Type::String => "String".into(),
            Type::Str => "&str".into(),
            Type::Stdin => "Stdin".into(),
            Type::Stdout => "Stdout".into(),
            Type::Box(p) => format!("Box<{}>", self.name(self.pointees[p])),
            Type::Arena => "Arena".into(),
            Type::ArenaBox(p) => format!("ArenaBox<{}>", self.name(self.pointees[p])),
            Type::Vec(p) => format!("Vec<{}>", self.name(self.pointees[p])),
            Type::Ref(p) => format!("&{}", self.name(self.pointees[p])),
            Type::RefMut(p) => format!("&mut {}", self.name(self.pointees[p])),
            Type::Annotated(p, _) => self.name(self.pointees[p]),
            Type::Slice(p) => format!("&[{}]", self.name(self.pointees[p])),
            Type::SliceMut(p) => format!("&mut [{}]", self.name(self.pointees[p])),
            Type::Enum(id) => self.layout_name(id),
            Type::Variants(id, mask) => {
                let names = self.enums[id]
                    .variants
                    .iter()
                    .enumerate()
                    .filter(|(tag, _)| mask & (1 << tag) != 0)
                    .map(|(_, v)| format!("{}.{}", self.enums[id].name, v.name))
                    .collect::<Vec<_>>();
                names.join(" | ")
            }
            Type::Union(id) => self.unions[id]
                .members
                .iter()
                .map(|t| self.name(*t))
                .collect::<Vec<_>>()
                .join(" | "),
            Type::Fn(id) => self.callable_name(id),
            Type::Once(id) => self.callable_name(id),
            Type::Task(p) => format!("Task<{}>", self.name(self.pointees[p])),
            Type::DynObj(id) => self
                .objects
                .get(id)
                .map(|object| object.name.clone())
                .unwrap_or_else(|| "dyn <unknown>".into()),
        }
    }
    fn function_name(&self, id: usize) -> String {
        let signature = &self.function_types[id];
        let borrows = &signature.borrows;
        // Show canonical lifetimes `#k` as 'a, 'b, ... so contracts differ visibly.
        let named = |canonical: &str| -> String {
            let index = canonical
                .trim_start_matches('#')
                .parse::<usize>()
                .unwrap_or(0);
            let letter = (b'a' + (index % 26) as u8) as char;
            if index < 26 {
                format!("'{letter}")
            } else {
                format!("'{letter}{}", index / 26)
            }
        };
        let with_lifetime = |ty: Type, lifetime: Option<&String>| -> String {
            let text = self.name(ty);
            match lifetime {
                Some(lifetime) if text.starts_with('&') => {
                    format!("&{} {}", named(lifetime), &text[1..])
                }
                _ => text,
            }
        };
        let parameters = signature
            .parameters
            .iter()
            .zip(&signature.parameter_grades)
            .enumerate()
            .map(|(i, (ty, grade))| {
                let text = with_lifetime(*ty, borrows.parameters.get(i).and_then(Option::as_ref));
                match grade {
                    Some(grade) => format!("{text} @[{grade}]"),
                    None => text,
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let mut binders = borrows
            .parameters
            .iter()
            .flatten()
            .chain(&borrows.result)
            .cloned()
            .collect::<Vec<_>>();
        binders.sort_by_key(|name| name.trim_start_matches('#').parse::<usize>().unwrap_or(0));
        binders.dedup();
        let binder = if binders.is_empty() {
            String::new()
        } else {
            let list = binders
                .iter()
                .map(|lifetime| {
                    let outlived = borrows
                        .bounds
                        .iter()
                        .filter(|(long, short)| long == lifetime && short != lifetime)
                        .map(|(_, short)| named(short))
                        .collect::<Vec<_>>();
                    if outlived.is_empty() {
                        named(lifetime)
                    } else {
                        format!("{}: {}", named(lifetime), outlived.join(" + "))
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("<{list}>")
        };
        let mut effects = Vec::new();
        for (bit, name) in [(1u8, "panic"), (2, "io"), (4, "alloc"), (8, "suspend")] {
            if signature.effects & bit != 0 {
                effects.push(name);
            }
        }
        format!(
            "fn{binder}({parameters}) -> {}{} ! {{{}}}",
            with_lifetime(signature.result, borrows.result.as_ref()),
            match signature.result_grade {
                Some(grade) => format!(" @[{grade}]"),
                None => String::new(),
            },
            effects.join(", ")
        )
    }
    fn callable_name(&self, id: usize) -> String {
        let name = self.function_name(id);
        if self.function_types[id].linear {
            format!("linear once {name}")
        } else if self.function_types[id].once {
            format!("once {name}")
        } else {
            name
        }
    }
    fn layout_name(&self, id: usize) -> String {
        let layout = &self.enums[id];
        if layout.tuple
            || layout.array.is_some()
            || layout.dynamic_array.is_some()
            || layout.structural
        {
            return layout.name.clone();
        }
        if layout.arguments.is_empty() && layout.consts.is_empty() && layout.lifetimes.is_empty() {
            return layout.name.clone();
        }
        let arguments = if let Some(definition) = self.definitions.get(&layout.definition) {
            let mut types = layout.arguments.iter();
            let mut consts = layout.consts.iter();
            layout
                .lifetimes
                .iter()
                .cloned()
                .chain(definition.generics.iter().filter_map(|generic| {
                    if is_const_generic(self.resolution, generic) {
                        consts.next().map(|value| value.to_string())
                    } else {
                        types.next().map(|ty| self.name(*ty))
                    }
                }))
                .collect::<Vec<_>>()
        } else {
            layout
                .arguments
                .iter()
                .map(|ty| self.name(*ty))
                .chain(layout.consts.iter().map(|value| value.to_string()))
                .collect::<Vec<_>>()
        };
        format!("{}<{}>", layout.name, arguments.join(", "))
    }
    fn lower(&mut self, ty: &ast::Type, substitution: &Subst, depth: usize) -> Result<Type> {
        if depth >= 64 {
            return Err(Diagnostic::new(
                ty.span,
                "runtime type nesting budget exhausted",
            ));
        }
        if let ast::TypeKind::Lifetime(name) = &ty.kind {
            return Err(Diagnostic::new(
                ty.span,
                format!(
                    "lifetime '{name}' is not a runtime type; lifetimes may appear only as arguments of a record or alias type"
                ),
            ));
        }
        if matches!(ty.kind, ast::TypeKind::SelfType) {
            return substitution.self_type.ok_or_else(|| {
                Diagnostic::new(
                    ty.span,
                    "'Self' is only valid inside a trait or impl method signature, where it is replaced by the concrete impl target",
                )
            });
        }
        if let ast::TypeKind::Borrow { mutable, inner, .. } = &ty.kind {
            if is_str_type(inner) {
                if *mutable {
                    return Err(Diagnostic::new(
                        ty.span,
                        "mutable borrowed text '&mut str' is not supported; text views are immutable",
                    ));
                }
                return Ok(Type::Str);
            }
            if let ast::TypeKind::Slice(element) = &inner.kind {
                let element = self.lower(element, substitution, depth + 1)?;
                if matches!(
                    element,
                    Type::Ref(_)
                        | Type::RefMut(_)
                        | Type::Slice(_)
                        | Type::SliceMut(_)
                        | Type::Never
                ) || contains_task(self, element)
                    || has_borrow(self, element)
                {
                    return Err(Diagnostic::new(
                        ty.span,
                        "slice elements must be concrete copyable values, not references, slices, task handles, or Never",
                    ));
                }
                return Ok(if *mutable {
                    Type::SliceMut(self.pointer(element))
                } else {
                    Type::Slice(self.pointer(element))
                });
            }
            let inner = self.lower(inner, substitution, depth + 1)?;
            let record = inner.layout().is_some_and(|id| self.enums[id].record);
            if record {
                if *mutable {
                    if self.enums[inner.layout().expect("record layout")].borrowed {
                        return Err(Diagnostic::new(
                            ty.span,
                            "exclusive '&mut Record' receivers and parameters are not supported for records with borrowed fields; borrow the record shared, or update its owned metadata through an owning value",
                        ));
                    }
                    return Ok(Type::RefMut(self.pointer(inner)));
                }
                return Ok(Type::Ref(self.pointer(inner)));
            }
            // A borrowed trait object is a reference to the closed-world union
            // or to a fixed dynamic fat object. Dispatch through it is checked
            // separately: local/reference calls borrow the payload in place,
            // while a temporary shared receiver still needs copyable members.
            if matches!(inner, Type::Union(_) | Type::DynObj(_)) {
                return Ok(if *mutable {
                    Type::RefMut(self.pointer(inner))
                } else {
                    Type::Ref(self.pointer(inner))
                });
            }
            if *mutable {
                if !matches!(
                    inner,
                    Type::Box(_)
                        | Type::Arena
                        | Type::ArenaBox(_)
                        | Type::Bytes
                        | Type::String
                        | Type::Vec(_)
                ) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "mutable owner borrows support Box<T>, Arena, ArenaBox<T>, Bytes, String, Vec<T>, records, and mutable slice views",
                    ));
                }
                return Ok(Type::RefMut(self.pointer(inner)));
            }
            if !matches!(
                inner,
                Type::Box(_)
                    | Type::Arena
                    | Type::ArenaBox(_)
                    | Type::Bytes
                    | Type::String
                    | Type::Vec(_)
            ) {
                return Err(Diagnostic::new(
                    ty.span,
                    "borrowing supports immutable &Box<T>, &ArenaBox<T>, &Bytes, &String, &Vec<T>, &Record, and &[T] slice views",
                ));
            }
            return Ok(Type::Ref(self.pointer(inner)));
        }
        if let ast::TypeKind::Array(element, length) = &ty.kind {
            let element = self.lower(element, substitution, depth + 1)?;
            let length = crate::length::eval_type(
                self.resolution,
                self.logical,
                &substitution.consts,
                length,
            )?;
            return self.array(element, length, ty.span);
        }
        if let ast::TypeKind::Structural(fields) = &ty.kind {
            let mut lowered = Vec::with_capacity(fields.len());
            for field in fields {
                let (inner, grade) = crate::grades::split(&field.ty);
                if grade.is_some() {
                    return Err(Diagnostic::new(
                        field.ty.span,
                        "a structural record field cannot carry a usage grade; grade the record value or binding instead",
                    ));
                }
                lowered.push((
                    field.name.clone(),
                    self.lower(inner, substitution, depth + 1)?,
                ));
            }
            return self.structural(lowered, ty.span);
        }
        if let ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
        } = &ty.kind
        {
            let mut declared = BTreeSet::new();
            for lifetime in lifetimes {
                if !declared.insert(lifetime.name.clone()) {
                    return Err(Diagnostic::new(
                        lifetime.span,
                        format!("duplicate lifetime parameter '{}'", lifetime.name),
                    ));
                }
            }
            let bounds = crate::executable::build_lifetime_bounds(lifetimes)?;
            let mut parameter_lifetimes: Vec<Option<String>> = Vec::new();
            let mut parameter_mutable: Vec<bool> = Vec::new();
            let mut parameter_leaves: Vec<Vec<BorrowLeaf>> = Vec::new();
            if *call_linear && !*call_once {
                return Err(Diagnostic::new(
                    ty.span,
                    "a linear callable must be a once callable: write 'linear once fn(...)'",
                ));
            }
            let mut lowered = Vec::with_capacity(parameters.len());
            let mut grades = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let (inner, grade) = crate::grades::split(&parameter.ty);
                if matches!(inner.kind, ast::TypeKind::Predicate(_)) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "function values cannot have erased proposition parameters; erase the proof at the direct call site instead",
                    ));
                }
                let ty = self.lower(inner, substitution, depth + 1)?;
                if matches!(ty, Type::Never) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "a function value parameter cannot have type Never",
                    ));
                }
                let mut leaves = Vec::new();
                let lifetime = if ty.is_slice() || ty.is_ref() {
                    Some(arrow_lifetime(
                        inner,
                        &declared,
                        parameter_lifetimes.len(),
                        parameter.ty.span,
                    )?)
                } else if ty
                    .layout()
                    .is_some_and(|id| self.enums[id].record && self.enums[id].borrowed)
                    || is_reference_container(self, ty)
                    || is_borrowed_task_exit(self, ty)
                {
                    // A by-value borrowed record parameter carries one erased
                    // lifetime per borrowed field. Every field lifetime must be
                    // bound by the arrow itself, and the leaves travel in the
                    // callable contract so indirect calls keep the argument's
                    // owner loaned exactly like a direct call.
                    leaves = borrow_leaves(self, ty);
                    for leaf in &leaves {
                        let Some(name) = &leaf.lifetime else {
                            return Err(Diagnostic::new(
                                parameter.ty.span,
                                "internal error: borrowed record arrow parameter leaf has no lifetime",
                            ));
                        };
                        if !declared.contains(name) {
                            return Err(Diagnostic::new(
                                parameter.ty.span,
                                format!(
                                    "lifetime '{name}' in a function arrow type must be bound by the arrow itself, as in fn<'{0}>(Window<'{0}>) -> ...; an arrow cannot borrow for an outer lifetime",
                                    name.trim_start_matches('\'')
                                ),
                            ));
                        }
                    }
                    None
                } else if has_borrow(self, ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "function arrow types may borrow slice views ('&'a [T]', '&'a mut [T]') and records with borrowed slice fields, but not owner references or &str text views; pass a text view to a named function instead",
                    ));
                } else {
                    None
                };
                parameter_mutable.push(ty.is_mut_slice() || matches!(ty, Type::RefMut(_)));
                parameter_lifetimes.push(lifetime);
                parameter_leaves.push(leaves);
                grades.push(
                    grade
                        .map(|grade| {
                            crate::grades::evaluate(self.resolution, &substitution.grades, grade)
                        })
                        .transpose()?,
                );
                if grades.last().copied().flatten().is_some_and(Grade::is_zero) && self.owns(ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "a grade-zero arrow parameter would silently discard an owning/linear argument; erase only copyable parameters",
                    ));
                }
                lowered.push(ty);
            }
            let result_ast = self.expand_result_alias(result)?;
            let (result_inner, result_grade) = crate::grades::split(&result_ast);
            let result_grade = result_grade
                .map(|grade| crate::grades::evaluate(self.resolution, &substitution.grades, grade))
                .transpose()?;
            let result = self.lower(result_inner, substitution, depth + 1)?;
            if result_grade.is_some() && !result_grade.is_some_and(Grade::is_one) {
                if result_grade.is_some_and(Grade::is_zero) && !self.owns(result) {
                    // A copyable erased result carries no payload and no
                    // observable value. It is representable as `Unit` at the
                    // ABI boundary.
                } else if result_grade.is_some_and(Grade::is_zero) {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        "a grade-zero arrow result would silently discard an owning/linear value; return an owning @[1] contract or Unit",
                    ));
                } else {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        "callable result grades currently support exactly @[1] or @[0] on a copyable result; a larger or unbounded grade could duplicate the value",
                    ));
                }
            }
            let mut result_lifetime = None;
            let mut result_leaves: Vec<BorrowLeaf> = Vec::new();
            // Every input lifetime that can supply a borrowed slice result:
            // explicit slice parameters and borrowed record field leaves.
            let mut input_candidates = parameter_lifetimes
                .iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
            for leaves in &parameter_leaves {
                input_candidates.extend(leaves.iter().filter_map(|leaf| leaf.lifetime.clone()));
            }
            input_candidates.sort();
            input_candidates.dedup();
            if result.is_slice() {
                let (inner, _) = crate::grades::split(&result_ast);
                let lifetime = match arrow_explicit_lifetime(inner, &declared)? {
                    Some(name) => name,
                    None => match input_candidates.as_slice() {
                        [only] => only.clone(),
                        [] => {
                            return Err(Diagnostic::new(
                                result_ast.span,
                                "this arrow type returns a borrowed slice but takes no borrowed parameter or record field it could borrow from",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                result_ast.span,
                                "cannot infer this arrow result's lifetime from several borrowed inputs; name them, as in fn<'a, 'b>(&'a [T], &'b [T]) -> &'a [T]",
                            ));
                        }
                    },
                };
                let sources = parameter_lifetimes
                    .iter()
                    .zip(&parameter_mutable)
                    .filter(|(p, _)| {
                        p.as_ref()
                            .is_some_and(|p| crate::executable::outlives(&bounds, p, &lifetime))
                    })
                    .collect::<Vec<_>>();
                let record_sources = parameter_leaves
                    .iter()
                    .flat_map(|leaves| leaves.iter())
                    .filter(|leaf| {
                        leaf.lifetime.as_ref().is_some_and(|name| {
                            crate::executable::outlives(&bounds, name, &lifetime)
                        })
                    })
                    .collect::<Vec<_>>();
                if sources.is_empty() && record_sources.is_empty() {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        format!(
                            "the arrow result lifetime '{lifetime}' is not outlived by any slice parameter or borrowed record field, so no call could produce it"
                        ),
                    ));
                }
                if result.is_mut_slice()
                    && !sources.iter().any(|(_, mutable)| **mutable)
                    && !record_sources.iter().any(|leaf| leaf.mutable)
                {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        "an exclusive '&mut [T]' arrow result needs an exclusive slice parameter or exclusive record field whose lifetime outlives it",
                    ));
                }
                result_lifetime = Some(lifetime);
            } else if result.is_ref() {
                let (inner, _) = crate::grades::split(&result_ast);
                let lifetime = match arrow_explicit_lifetime(inner, &declared)? {
                    Some(name) => name,
                    None => match input_candidates.as_slice() {
                        [only] => only.clone(),
                        [] => {
                            return Err(Diagnostic::new(
                                result_ast.span,
                                "this arrow type returns a borrowed reference but takes no borrowed parameter or record field it could borrow from",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                result_ast.span,
                                "cannot infer this arrow result's lifetime from several borrowed inputs; name them, as in fn<'a, 'b>(&'a T, &'b U) -> &'a T",
                            ));
                        }
                    },
                };
                let sources = parameter_lifetimes
                    .iter()
                    .zip(&parameter_mutable)
                    .filter(|(p, _)| {
                        p.as_ref()
                            .is_some_and(|p| crate::executable::outlives(&bounds, p, &lifetime))
                    })
                    .collect::<Vec<_>>();
                let record_sources = parameter_leaves
                    .iter()
                    .flat_map(|leaves| leaves.iter())
                    .filter(|leaf| {
                        leaf.lifetime.as_ref().is_some_and(|name| {
                            crate::executable::outlives(&bounds, name, &lifetime)
                        })
                    })
                    .collect::<Vec<_>>();
                if sources.is_empty() && record_sources.is_empty() {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        format!(
                            "the arrow result lifetime '{lifetime}' is not outlived by any reference parameter or borrowed record field, so no call could produce it"
                        ),
                    ));
                }
                if matches!(result, Type::RefMut(_))
                    && !sources.iter().any(|(_, mutable)| **mutable)
                    && !record_sources.iter().any(|leaf| leaf.mutable)
                {
                    return Err(Diagnostic::new(
                        result_ast.span,
                        "an exclusive '&mut T' arrow result needs an exclusive reference parameter or exclusive record field whose lifetime outlives it",
                    ));
                }
                result_lifetime = Some(lifetime);
            } else if result
                .layout()
                .is_some_and(|id| self.enums[id].record && self.enums[id].borrowed)
                || is_reference_container(self, result)
                || is_borrowed_task_exit(self, result)
            {
                result_leaves = borrow_leaves(self, result);
                for leaf in &result_leaves {
                    let Some(name) = &leaf.lifetime else {
                        return Err(Diagnostic::new(
                            result_ast.span,
                            "internal error: borrowed record arrow result leaf has no lifetime",
                        ));
                    };
                    if !declared.contains(name) {
                        return Err(Diagnostic::new(
                            result_ast.span,
                            format!(
                                "lifetime '{name}' in a function arrow result must be bound by the arrow itself; an arrow cannot return a borrow for an outer lifetime"
                            ),
                        ));
                    }
                    let mut source = parameter_leaves
                        .iter()
                        .flat_map(|leaves| leaves.iter())
                        .filter(|input| {
                            input.lifetime.as_ref().is_some_and(|input| {
                                crate::executable::outlives(&bounds, input, name)
                            })
                        });
                    let Some(first) = source.next() else {
                        return Err(Diagnostic::new(
                            result_ast.span,
                            format!(
                                "the arrow result field lifetime '{name}' is not outlived by any borrowed parameter field, so no call could produce it"
                            ),
                        ));
                    };
                    if leaf.mutable
                        && !std::iter::once(first)
                            .chain(source)
                            .any(|input| input.mutable)
                    {
                        return Err(Diagnostic::new(
                            result_ast.span,
                            "an exclusive '&mut [T]' arrow result field needs an exclusive borrowed parameter field whose lifetime outlives it",
                        ));
                    }
                }
            } else if matches!(result, Type::Ref(_)) || has_borrow(self, result) {
                return Err(Diagnostic::new(
                    ty.span,
                    "function arrow types may return slice views and records with borrowed slice fields, but not borrowed owner references or &str text views",
                ));
            }
            let borrows = BorrowSig::canonical_with_leaves(
                &parameter_lifetimes,
                result_lifetime.as_ref(),
                &parameter_leaves,
                &result_leaves,
                &bounds,
            );
            if contains_task(self, result) {
                return Err(Diagnostic::new(
                    ty.span,
                    "function values cannot return task handles; a child handle must not escape its scope",
                ));
            }
            let effects = effect_bits_with(self.resolution, effects, &substitution.effects)?;
            let id = self.function_type_with(
                lowered,
                result,
                effects,
                grades,
                result_grade,
                *call_once,
                *call_linear,
                borrows,
            );
            return Ok(if *call_once {
                Type::Once(id)
            } else {
                Type::Fn(id)
            });
        }
        if let ast::TypeKind::Binary { op, left, right } = &ty.kind
            && matches!(op, crate::lexer::Kind::Pipe | crate::lexer::Kind::Amp)
        {
            let left = self.algebraic_operand(left, substitution, depth + 1)?;
            let right = self.algebraic_operand(right, substitution, depth + 1)?;
            return if *op == crate::lexer::Kind::Pipe {
                self.union(vec![left, right], ty.span)
            } else {
                self.intersect(left, right, ty.span)
            };
        }
        if matches!(&ty.kind, ast::TypeKind::Tuple(items) if items.is_empty()) {
            return Ok(Type::Unit);
        }
        if let ast::TypeKind::Tuple(items) = &ty.kind {
            let mut elements = Vec::with_capacity(items.len());
            for item in items {
                let element = self.lower(item, substitution, depth + 1)?;
                elements.push(self.full(element, item.span)?);
            }
            return self.tuple(elements, ty.span);
        }
        if let ast::TypeKind::Dyn(trait_path) = &ty.kind {
            let ast::TypeKind::Named { arguments, .. } = &trait_path.kind else {
                return Err(Diagnostic::new(
                    trait_path.span,
                    "a trait object must name one declared trait",
                ));
            };
            let trait_id = self.resolution.reference(trait_path.span).ok_or_else(|| {
                Diagnostic::new(trait_path.span, "trait object path did not resolve")
            })?;
            if self.resolution.bindings[trait_id].kind != BindingKind::Trait {
                return Err(Diagnostic::new(
                    trait_path.span,
                    format!(
                        "'{}' is not a declared trait; 'dyn' names a trait object",
                        self.resolution.bindings[trait_id].name
                    ),
                ));
            }
            let mut type_arguments = Vec::new();
            for argument in arguments {
                if matches!(argument.kind, ast::TypeKind::Lifetime(_)) {
                    return Err(Diagnostic::new(
                        argument.span,
                        "trait objects do not take lifetime arguments in this subset; object values own their payload and cannot store borrows",
                    ));
                }
                type_arguments.push(self.lower(argument, substitution, depth + 1)?);
            }
            let key = (
                trait_id,
                TraitArguments {
                    types: type_arguments,
                    ..Default::default()
                },
            );
            if let Some(reason) = self.dyn_errors.get(&trait_id) {
                return Err(Diagnostic::new(
                    ty.span,
                    format!(
                        "trait '{}' is not object-safe: {reason}",
                        self.resolution.bindings[trait_id].name
                    ),
                ));
            }
            if self.dynamic_traits.contains(&trait_id) {
                if let Some(id) = self.object_cache.get(&key) {
                    return Ok(Type::DynObj(*id));
                }
                if self.objects.len() >= 256 {
                    return Err(Diagnostic::new(
                        ty.span,
                        "trait-object budget exhausted (256)",
                    ));
                }
                let mut name = self.resolution.bindings[trait_id].name.clone();
                if !key.1.types.is_empty() {
                    name.push('<');
                    name.push_str(
                        &key.1
                            .types
                            .iter()
                            .map(|argument| self.name(*argument))
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                    name.push('>');
                }
                let id = self.objects.len();
                self.objects.push(DynObjectType {
                    trait_id,
                    arguments: key.1.clone(),
                    name: format!("dyn {name}"),
                });
                self.object_cache.insert(key, id);
                return Ok(Type::DynObj(id));
            }
            return self.dyn_objects.get(&key).copied().ok_or_else(|| {
                Diagnostic::new(
                    ty.span,
                    format!(
                        "no finite closed-world object type exists for trait '{}'; it needs at least one concrete impl and no generic or blanket impls",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            });
        }
        if let ast::TypeKind::Named { path, arguments } = &ty.kind {
            if path.len() == 2 {
                if path[0] == "Self" {
                    if !arguments.is_empty() {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "associated type projection 'Self::{}' does not take type arguments",
                                path[1]
                            ),
                        ));
                    }
                    if let Some(value) = substitution.self_projections.get(&path[1]) {
                        return Ok(*value);
                    }
                    let value = substitution
                        .associated_types
                        .get(&path[1])
                        .cloned()
                        .ok_or_else(|| {
                            Diagnostic::new(
                                ty.span,
                                format!(
                                    "associated type '{}' is not defined by this impl",
                                    path[1]
                                ),
                            )
                        })?;
                    return self.lower(&value, substitution, depth + 1);
                }
                if let Some(base) = self.resolution.reference(ty.span)
                    && matches!(
                        self.resolution.bindings[base].kind,
                        BindingKind::Generic | BindingKind::Parameter
                    )
                {
                    let key = (base, path[1].clone());
                    if let Some(value) = substitution.projections.get(&key) {
                        if !arguments.is_empty() {
                            return Err(Diagnostic::new(
                                ty.span,
                                format!(
                                    "associated type projection '{}::{}' does not take type arguments",
                                    self.resolution.bindings[base].name, path[1]
                                ),
                            ));
                        }
                        return Ok(*value);
                    }
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "cannot project associated type '{}' from '{}' without a concrete impl; add a trait bound '<{}: Trait>' that declares it",
                            path[1],
                            self.resolution.bindings[base].name,
                            self.resolution.bindings[base].name
                        ),
                    ));
                }
            }
            let id = self.resolution.reference(ty.span).unwrap();
            let b = &self.resolution.bindings[id];
            let (lifetime_arguments, arguments) =
                split_lifetime_arguments(arguments, substitution, ty.span)?;
            if b.kind == BindingKind::Alias {
                return self.expand_alias(
                    id,
                    &arguments,
                    &lifetime_arguments,
                    substitution,
                    depth,
                    ty.span,
                );
            }
            if b.kind == BindingKind::Builtin && b.name == "DynArray" {
                if !lifetime_arguments.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        "builtin 'DynArray' does not take lifetime arguments",
                    ));
                }
                if arguments.len() != 2 {
                    return Err(Diagnostic::new(
                        ty.span,
                        "DynArray expects an element type and a compile-time capacity, as in DynArray<i64, 8>",
                    ));
                }
                let element = self.lower(arguments[0], substitution, depth + 1)?;
                let capacity = crate::length::eval_type(
                    self.resolution,
                    self.logical,
                    &substitution.consts,
                    arguments[1],
                )?;
                return self.dynamic_array(element, capacity, ty.span);
            }
            if b.kind == BindingKind::Builtin
                && matches!(b.name.as_str(), "Box" | "Vec" | "Task" | "ArenaBox")
            {
                if !lifetime_arguments.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!("builtin '{}' does not take lifetime arguments", b.name),
                    ));
                }
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!("{} expects one element type", b.name),
                    ));
                }
                let inner = self.lower(arguments[0], substitution, depth + 1)?;
                let inner = self.full(inner, ty.span)?;
                let direct_reference = matches!(
                    inner,
                    Type::Ref(_) | Type::RefMut(_) | Type::Str
                ) && matches!(arguments[0].kind, ast::TypeKind::Borrow { .. });
                let task_borrowed_record = b.name == "Task" && is_borrowed_record(self, inner);
                if (matches!(
                    inner,
                    Type::Ref(_) | Type::RefMut(_) | Type::Slice(_) | Type::SliceMut(_) | Type::Str
                ) || has_borrow(self, inner))
                    && !task_borrowed_record
                    && !direct_reference
                {
                    return Err(Diagnostic::new(
                        ty.span,
                        "containers cannot store borrowed references or slice views (including &str text views, or borrowed records); keep the borrow in a lexical record",
                    ));
                }
                if b.name == "Task" {
                    if matches!(inner, Type::Never) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "Task<T> cannot use Never as its result type",
                        ));
                    }
                    if contains_task(self, inner) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "Task<T> cannot contain another task handle; a child handle must not escape its scope",
                        ));
                    }
                    let pointer = self.pointer(inner);
                    return Ok(Type::Task(pointer));
                }
                if contains_task(self, inner) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "task handles cannot be stored inside Box, ArenaBox, or Vec; join them in the scope that owns them",
                    ));
                }
                let inner = self.annotate_container_element(inner, arguments[0], substitution);
                let pointer = self.pointer(inner);
                return Ok(match b.name.as_str() {
                    "Box" => Type::Box(pointer),
                    "ArenaBox" => Type::ArenaBox(pointer),
                    _ => Type::Vec(pointer),
                });
            }
            if b.kind == BindingKind::Constructor && arguments.is_empty() {
                if !lifetime_arguments.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        "variant types do not take lifetime arguments",
                    ));
                }
                let (owner, tag) = self.owner(id);
                if !self.definitions[&owner].generics.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        "variant types are limited to monomorphic enums",
                    ));
                }
                let layout = self.instantiate(owner, vec![], vec![], vec![], ty.span)?;
                return Ok(refine(&self.enums, layout, 1 << tag));
            }
            if arguments.is_empty() && !self.definitions.contains_key(&id) {
                if !lifetime_arguments.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!("'{}' does not take lifetime arguments", b.name),
                    ));
                }
                if let Some(ty) = substitution.types.get(&id) {
                    return Ok(*ty);
                }
                if b.kind == BindingKind::Generic {
                    if substitution.consts.contains_key(&id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "natural const parameter '{}' is not a runtime type; use it only as an array length or compile-time index",
                                b.name
                            ),
                        ));
                    }
                    if is_effect_generic_binding(self.resolution, id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "effect row parameter '{}' is not a runtime type; use it only in an effect row or an effect specialization",
                                b.name
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        ty.span,
                        format!("type parameter '{}' is not bound here", b.name),
                    ));
                }
                if b.kind == BindingKind::Trait {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "trait '{}' is not a runtime type; use it only as a generic bound such as '<T: {}>' or implement it for a concrete type",
                            b.name, b.name
                        ),
                    ));
                }
                if b.kind == BindingKind::Builtin {
                    match b.name.as_str() {
                        "i64" => return Ok(Type::I64),
                        "f32" => return Ok(Type::Float(crate::float::FloatKind::F32)),
                        "f64" => return Ok(Type::Float(crate::float::FloatKind::F64)),
                        "Char" => return Ok(Type::Char),
                        name if crate::int::IntKind::named(name).is_some() => {
                            return Ok(Type::int(crate::int::IntKind::named(name).unwrap()));
                        }
                        "Bool" => return Ok(Type::Bool),
                        "Unit" => return Ok(Type::Unit),
                        "Bytes" => return Ok(Type::Bytes),
                        "String" => return Ok(Type::String),
                        "Arena" => return Ok(Type::Arena),
                        "str" => {
                            return Err(Diagnostic::new(
                                ty.span,
                                "'str' is unsized; write a borrowed text view as '&str' with a declared or elided lifetime",
                            ));
                        }
                        "Stdin" => return Ok(Type::Stdin),
                        "Stdout" => return Ok(Type::Stdout),
                        _ => {}
                    }
                }
            }
            if self.definitions.contains_key(&id) {
                let definition = self.definitions[&id];
                if lifetime_arguments.len() != definition.lifetimes.len() {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "{} '{}' expects {} lifetime argument(s), found {}",
                            if definition.fields.is_some() {
                                "record"
                            } else {
                                "enum"
                            },
                            definition.name,
                            definition.lifetimes.len(),
                            lifetime_arguments.len()
                        ),
                    ));
                }
                if arguments.len() != definition.generics.len() {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "{} '{}' expects {} type arguments, found {}",
                            if definition.fields.is_some() {
                                "record"
                            } else {
                                "enum"
                            },
                            definition.name,
                            definition.generics.len(),
                            arguments.len()
                        ),
                    ));
                }
                let mut args = Vec::new();
                let mut consts = Vec::new();
                for (generic, argument) in definition.generics.iter().zip(arguments) {
                    if is_const_generic(self.resolution, generic) {
                        consts.push(crate::length::eval_type(
                            self.resolution,
                            self.logical,
                            &substitution.consts,
                            argument,
                        )?);
                    } else {
                        args.push(
                            self.lower(argument, substitution, depth + 1)
                                .map(Type::full)?,
                        );
                    }
                }
                return self
                    .instantiate_raw(id, args, consts, lifetime_arguments, ty.span)
                    .map(Type::Enum);
            }
            if self.logical.data.contains_key(&id) {
                return Err(Diagnostic::new(
                    ty.span,
                    format!(
                        "total logical data type '{}' is erased before runtime lowering; it may appear only in erased proof parameters, never in executable values",
                        b.name
                    ),
                ));
            }
            if self.logical.constructors.contains_key(&id) {
                return Err(Diagnostic::new(
                    ty.span,
                    format!(
                        "constructor '{}' of a total logical data type is erased proof evidence, not a runtime constructor",
                        b.name
                    ),
                ));
            }
        }
        if let ast::TypeKind::Graded { .. } = &ty.kind {
            return Err(Diagnostic::new(
                ty.span,
                "usage grades apply to function parameters, let bindings, and an outer owning result (as in '-> Box<T> @[1]'); they are not allowed on stored fields, nested type arguments, arrays, or grades nested inside a composite result type",
            ));
        }
        Err(Diagnostic::new(
            ty.span,
            "executable values support i64, fixed-width integers, f32, f64, Char, Bool, Unit, records, inline enums, Box, Vec, and Bytes; logical Nat is not a machine integer",
        ))
    }
    /// Lower one operand of `|`/`&`. A bare constructor such as `Op.Mul`
    /// denotes its single-variant set, which keeps the zero-cost enum-mask
    /// representation instead of materializing a heterogeneous union.
    fn algebraic_operand(
        &mut self,
        ty: &ast::Type,
        substitution: &Subst,
        depth: usize,
    ) -> Result<Type> {
        if let ast::TypeKind::Named { arguments, .. } = &ty.kind
            && arguments.is_empty()
            && let Some(id) = self.resolution.reference(ty.span)
            && self.resolution.bindings[id].kind == BindingKind::Constructor
        {
            let (owner, tag) = self.owner(id);
            if !self.definitions[&owner].generics.is_empty() {
                return Err(Diagnostic::new(
                    ty.span,
                    "variant types are limited to monomorphic enums",
                ));
            }
            let layout = self.instantiate(owner, vec![], vec![], vec![], ty.span)?;
            return Ok(refine(&self.enums, layout, 1 << tag));
        }
        self.lower(ty, substitution, depth)
    }
    /// Expand an outer chain of transparent aliases for a *result* position so
    /// a callable arrow can carry a graded result contract written through an
    /// alias, as in `type Handle<T> = Box<T> @[1]; fn(...) -> Handle<i64>`.
    /// Grade arguments are substituted structurally here (only result-contract
    /// positions permit them) and the resulting grade is evaluated below.
    /// This mirrors the executable checker's result-contract expansion.
    fn expand_result_alias(&self, ty: &ast::Type) -> Result<ast::Type> {
        let mut current = ty.clone();
        let mut active = BTreeSet::new();
        for _ in 0..MAX_ALIAS_DEPTH {
            let ast::TypeKind::Named { arguments, .. } = &current.kind else {
                return Ok(current);
            };
            let Some(id) = self.resolution.reference(current.span) else {
                return Ok(current);
            };
            if self.resolution.bindings[id].kind != BindingKind::Alias {
                return Ok(current);
            }
            let Some((generics, rhs)) = self.alias_definition(id) else {
                return Ok(current);
            };
            let lifetime_arguments = arguments
                .iter()
                .filter(|argument| matches!(argument.kind, ast::TypeKind::Lifetime(_)))
                .count();
            if let Some(expected) = self.alias_lifetime_count(id)
                && lifetime_arguments != expected
            {
                return Err(Diagnostic::new(
                    current.span,
                    format!(
                        "type alias '{}' expects {expected} lifetime argument(s), found {lifetime_arguments}",
                        self.resolution.bindings[id].name
                    ),
                ));
            }
            let runtime_arguments = arguments
                .iter()
                .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
                .collect::<Vec<_>>();
            if runtime_arguments.len() != generics.len() {
                return Err(Diagnostic::new(
                    current.span,
                    format!(
                        "type alias '{}' expects {} runtime argument(s), found {}",
                        self.resolution.bindings[id].name,
                        generics.len(),
                        runtime_arguments.len()
                    ),
                ));
            }
            if !active.insert(id) {
                return Err(Diagnostic::new(
                    current.span,
                    format!(
                        "cyclic executable type alias '{}' is not allowed",
                        self.resolution.bindings[id].name
                    ),
                ));
            }
            let mut map = BTreeMap::new();
            for (generic, argument) in generics.iter().zip(runtime_arguments) {
                // This expansion is only reachable from a result-contract
                // position (a callable arrow result), so grade arguments are
                // substituted structurally and evaluated just below. Ordinary
                // alias lowering in `expand_alias` still rejects grade
                // parameters in parameters and stored types.
                map.insert(self.resolution.binder(generic.span).unwrap(), argument);
            }
            current = crate::executable::substitute_alias_type(self.resolution, rhs, &map);
        }
        Err(Diagnostic::new(
            ty.span,
            "executable type alias expansion exceeds the 64-level budget",
        ))
    }
    /// Expand a transparent executable type alias. Aliases never add a runtime
    /// tag, box, or allocation: the right-hand side is lowered directly in the
    /// alias parameters' substitution. Recursive aliases and excessive
    /// expansion are explicit errors.
    fn expand_alias(
        &mut self,
        id: BindingId,
        arguments: &[&ast::Type],
        lifetime_arguments: &[String],
        substitution: &Subst,
        depth: usize,
        span: Span,
    ) -> Result<Type> {
        let alias = *self
            .aliases
            .get(&id)
            .ok_or_else(|| Diagnostic::new(span, "unknown type alias"))?;
        if lifetime_arguments.len() != alias.lifetimes.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type alias '{}' expects {} lifetime argument(s), found {}",
                    self.resolution.bindings[id].name,
                    alias.lifetimes.len(),
                    lifetime_arguments.len()
                ),
            ));
        }
        if arguments.len() != alias.generics.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type alias '{}' expects {} type/const/effect arguments, found {}",
                    self.resolution.bindings[id].name,
                    alias.generics.len(),
                    arguments.len()
                ),
            ));
        }
        if self.alias_active.len() >= MAX_ALIAS_DEPTH {
            return Err(Diagnostic::new(
                span,
                "type alias expansion exceeds the 64-level budget",
            ));
        }
        if !self.alias_active.insert(id) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cyclic executable type alias '{}' is not allowed",
                    self.resolution.bindings[id].name
                ),
            ));
        }
        let mut inner = Subst::default();
        for (declared, actual) in alias.lifetimes.iter().zip(lifetime_arguments) {
            inner
                .lifetimes
                .insert(declared.name.clone(), actual.clone());
        }
        for (generic, argument) in alias.generics.iter().zip(arguments) {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_const_generic(self.resolution, generic) {
                let value = crate::length::eval_type(
                    self.resolution,
                    self.logical,
                    &substitution.consts,
                    argument,
                )?;
                inner.consts.insert(binder, value);
            } else if is_grade_generic(self.resolution, generic) {
                let result = Err(Diagnostic::new(
                    generic.span,
                    "grade parameters are not part of runtime type aliases",
                ));
                self.alias_active.remove(&id);
                return result;
            } else if is_effect_generic(self.resolution, generic) {
                let value = effect_bits_with(
                    self.resolution,
                    std::slice::from_ref(argument),
                    &substitution.effects,
                )?;
                inner.effects.insert(binder, value);
            } else {
                let value = self.lower(argument, substitution, depth + 1)?;
                inner.types.insert(binder, self.full(value, span)?);
            }
        }
        let result = self.lower(alias.ty, &inner, depth + 1);
        self.alias_active.remove(&id);
        result
    }
    /// Normalize a union: flatten nested unions, drop `Never`, merge variant
    /// masks of one enum, sort/deduplicate, and reject alternatives whose
    /// representation cannot safely cross a union boundary.
    pub fn union(&mut self, members: Vec<Type>, span: Span) -> Result<Type> {
        let mut atoms = Vec::new();
        let mut work = 0usize;
        for member in members {
            match member {
                Type::Never => {}
                Type::Union(id) => {
                    work += self.unions[id].members.len();
                    atoms.extend(self.unions[id].members.iter().copied());
                }
                atom => atoms.push(atom),
            }
        }
        if work > MAX_INTERSECTION_WORK {
            return Err(Diagnostic::new(
                span,
                "union normalization budget exhausted; reduce nested unions",
            ));
        }
        if atoms.len() > MAX_INTERSECTION_WORK {
            return Err(Diagnostic::new(
                span,
                "union normalization budget exhausted; reduce the number of alternatives",
            ));
        }
        // Merge all variant-set alternatives of the same enum. This preserves
        // the cheap tag-only representation for `E.A | E.B` and widens a full
        // mask back to `E`.
        let mut masks: BTreeMap<usize, u64> = BTreeMap::new();
        let mut rest = Vec::new();
        for atom in atoms {
            if let Some(id) = atom.layout() {
                *masks.entry(id).or_default() |= mask_of(atom, &self.enums);
            } else {
                rest.push(atom);
            }
        }
        rest.extend(
            masks
                .into_iter()
                .filter(|(_, mask)| *mask != 0)
                .map(|(id, mask)| refine(&self.enums, id, mask)),
        );
        rest.sort();
        rest.dedup();
        if rest.len() > MAX_UNION_MEMBERS * 4 {
            return Err(Diagnostic::new(
                span,
                format!("union exceeds the {MAX_UNION_MEMBERS}-alternative normalization limit"),
            ));
        }
        // A narrower alternative is already covered by a wider one. The mask
        // merge above handles the common nominal-enum case; this keeps the
        // normalization law `A | B = B` when `A <: B` for any supported atom.
        // Two distinct but mutually subtype arrows (for example an unannotated
        // and a `@[many]` parameter grade) are representation-equivalent, so
        // keep one deterministic representative instead of dropping both and
        // falsely normalizing the union to `Never`.
        let mut normalized: Vec<Type> = Vec::new();
        for atom in &rest {
            if rest.iter().any(|other| {
                other != atom
                    && self.subtype(*atom, *other)
                    && (!self.subtype(*other, *atom)
                        || self.canonical_equivalent(*atom, *other) != *atom)
            }) {
                continue;
            }
            normalized.push(*atom);
        }
        if normalized.len() > MAX_UNION_MEMBERS {
            return Err(Diagnostic::new(
                span,
                format!("union exceeds the {MAX_UNION_MEMBERS}-alternative normalization limit"),
            ));
        }
        if normalized.len() > 1 {
            for atom in &normalized {
                self.check_union_member(*atom, span)?;
            }
        }
        match normalized.len() {
            0 => Ok(Type::Never),
            1 => Ok(normalized[0]),
            _ => {
                if let Some(id) = self.union_cache.get(&normalized) {
                    return Ok(Type::Union(*id));
                }
                if self.unions.len() >= 256 {
                    return Err(Diagnostic::new(span, "union layout budget exhausted (256)"));
                }
                let id = self.unions.len();
                self.unions.push(UnionType {
                    members: normalized.clone(),
                });
                self.union_cache.insert(normalized, id);
                Ok(Type::Union(id))
            }
        }
    }
    /// Normalize an intersection by distribution over unions. Because the
    /// supported atoms have no structural refinement other than enum variant
    /// masks, every nonempty atom intersection is either the same atom or a
    /// variant subset; every empty one becomes `Never`. The result is again a
    /// normalized union (or a single atom, or `Never`).
    pub fn intersect(&mut self, left: Type, right: Type, span: Span) -> Result<Type> {
        if left == Type::Never || right == Type::Never {
            return Ok(Type::Never);
        }
        let left = self.union_members(left);
        let right = self.union_members(right);
        let mut clauses = Vec::new();
        let mut work = 0usize;
        for a in left {
            for b in &right {
                work += 1;
                if work > MAX_INTERSECTION_WORK {
                    return Err(Diagnostic::new(
                        span,
                        "intersection normalization budget exhausted; simplify the type",
                    ));
                }
                let clause = if self.subtype(a, *b) && self.subtype(*b, a) {
                    // Distinct but mutually subtype arrows (for example
                    // unannotated and `@[many]` parameter grades) are
                    // representation-equivalent. Keep a deterministic
                    // canonical representative rather than absorbing both
                    // into `Never`.
                    self.canonical_equivalent(a, *b)
                } else if self.subtype(a, *b) {
                    a
                } else if self.subtype(*b, a) {
                    *b
                } else if matches!(a, Type::Fn(_) | Type::Once(_))
                    && matches!(b, Type::Fn(_) | Type::Once(_))
                {
                    return Err(Diagnostic::new(
                        span,
                        "incomparable callable intersections require an overloaded function representation; this intersection is not known to be empty",
                    ));
                } else {
                    self.atom_intersection(a, *b)
                };
                if clause != Type::Never {
                    clauses.push(clause);
                }
            }
        }
        self.union(clauses, span)
    }
    pub(crate) fn union_members(&self, ty: Type) -> Vec<Type> {
        match ty {
            Type::Never => Vec::new(),
            Type::Union(id) => self.unions[id].members.clone(),
            atom => vec![atom],
        }
    }
    fn atom_intersection(&self, left: Type, right: Type) -> Type {
        if left == right {
            return left;
        }
        if left == Type::Never || right == Type::Never {
            return Type::Never;
        }
        match (left.layout(), right.layout()) {
            (Some(a), Some(b)) if a == b => refine(
                &self.enums,
                a,
                mask_of(left, &self.enums) & mask_of(right, &self.enums),
            ),
            _ => Type::Never,
        }
    }
    fn check_union_member(&self, ty: Type, span: Span) -> Result<()> {
        match ty {
            Type::Ref(_) | Type::RefMut(_) | Type::Slice(_) | Type::SliceMut(_) | Type::Str => {
                Err(Diagnostic::new(
                    span,
                    "unions cannot contain borrowed references or slice views (including &str text views); a borrow must not escape its lexical owner through a union",
                ))
            }
            ty if has_borrow(self, ty) => Err(Diagnostic::new(
                span,
                "unions cannot contain borrowed records; a borrow must not escape its lexical owner through a union",
            )),
            Type::Stdin | Type::Stdout => Err(Diagnostic::new(
                span,
                "opaque standard-stream handles cannot be union members; pass the capability directly",
            )),
            Type::Task(_) => Err(Diagnostic::new(
                span,
                "task handles cannot be union members; a child handle must not escape its scope",
            )),
            Type::Union(_) | Type::Never => Err(Diagnostic::new(
                span,
                "internal error: union normalization did not flatten its members",
            )),
            Type::Fn(id) | Type::Once(id) => {
                let signature = &self.function_types[id];
                if self.width(if signature.once {
                    Type::Once(id)
                } else {
                    Type::Fn(id)
                }) > MAX_WORDS
                {
                    return Err(Diagnostic::new(
                        span,
                        "callable union alternative exceeds the 32-word layout budget",
                    ));
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    /// Normalized subtyping over the supported value fragment.
    pub fn subtype(&self, actual: Type, expected: Type) -> bool {
        if actual == expected {
            return true;
        }
        if actual == Type::Never {
            return true;
        }
        if expected == Type::Never {
            return false;
        }
        match (actual, expected) {
            (Type::Union(a), Type::Union(b)) => self.unions[a].members.iter().all(|left| {
                self.unions[b]
                    .members
                    .iter()
                    .any(|right| self.atom_subtype(*left, *right))
            }),
            (Type::Union(a), _) => self.unions[a]
                .members
                .iter()
                .all(|left| self.atom_subtype(*left, expected)),
            (_, Type::Union(b)) => self.unions[b]
                .members
                .iter()
                .any(|right| self.atom_subtype(actual, *right)),
            _ => self.atom_subtype(actual, expected),
        }
    }
    fn atom_subtype(&self, actual: Type, expected: Type) -> bool {
        if actual == expected {
            return true;
        }
        if actual == Type::Never {
            return true;
        }
        if expected == Type::Never {
            return false;
        }
        match (actual, expected) {
            (Type::Annotated(a, _), Type::Annotated(b, _)) => {
                return self.subtype(self.pointees[a], self.pointees[b])
                    && self.subtype(self.pointees[b], self.pointees[a]);
            }
            (Type::Annotated(a, _), _) => return self.subtype(self.pointees[a], expected),
            (_, Type::Annotated(b, _)) => return self.subtype(actual, self.pointees[b]),
            // Lifetimes are erased, including the checker-only element
            // annotations inside a pointee. Two references to the same pointee
            // shape must therefore compare equal regardless of the labels their
            // nested containers happen to carry. An exclusive reference may
            // always be used as a shared one, never the reverse.
            (Type::Ref(a), Type::Ref(b)) | (Type::RefMut(a), Type::RefMut(b)) => {
                return self.subtype(self.pointees[a], self.pointees[b])
                    && self.subtype(self.pointees[b], self.pointees[a]);
            }
            (Type::RefMut(a), Type::Ref(b)) => {
                return self.subtype(self.pointees[a], self.pointees[b]);
            }
            (Type::Box(a), Type::Box(b))
            | (Type::ArenaBox(a), Type::ArenaBox(b))
            | (Type::Vec(a), Type::Vec(b)) => {
                return self.subtype(self.pointees[a], self.pointees[b])
                    && self.subtype(self.pointees[b], self.pointees[a]);
            }
            _ => {}
        }
        match (actual, expected) {
            (Type::Fn(a), Type::Fn(b))
            | (Type::Fn(a), Type::Once(b))
            | (Type::Once(a), Type::Once(b)) => {
                return self.function_subtype(&self.function_types[a], &self.function_types[b]);
            }
            (Type::Once(_), Type::Fn(_)) => return false,
            (Type::Enum(a), Type::Enum(b))
                if self.enums[a].name == "TaskExit" && self.enums[b].name == "TaskExit" =>
            {
                return self.same_erased_shape(actual, expected);
            }
            (Type::Enum(a), Type::Enum(b)) if self.enums[a].record && self.enums[b].structural => {
                return self.structural_subtype(a, b);
            }
            (Type::Enum(a), Type::Enum(b)) if self.enums[a].record && self.enums[b].record => {
                // Erased record lifetimes are not part of the runtime layout or
                // of nominal identity. A call boundary still relates the
                // argument's actual field provenance to the parameter labels.
                return self.same_erased_shape(actual, expected);
            }
            _ => {}
        }
        match (actual.layout(), expected.layout()) {
            (Some(a), Some(b)) if a == b => {
                mask_of(actual, &self.enums) & !mask_of(expected, &self.enums) == 0
            }
            _ => false,
        }
    }
    /// Structural width/depth subtyping into a canonical structural row.
    /// Every target field must exist in the source with a subtype-compatible
    /// value. Borrowed leaves are invariant: a structural conversion may not
    /// relabel, reborrow, or change the mutability of a view. Source fields
    /// absent from the target are erased, so they must not carry a linear
    /// obligation; owning affine fields are dropped exactly once by the
    /// checked coercion.
    fn structural_subtype(&self, source: usize, target: usize) -> bool {
        let source_enum = &self.enums[source];
        let target_enum = &self.enums[target];
        let source_variant = &source_enum.variants[0];
        let target_variant = &target_enum.variants[0];
        for (target_name, target_ty) in target_variant.names.iter().zip(&target_variant.fields) {
            let Some(index) = source_variant
                .names
                .iter()
                .position(|name| name == target_name)
            else {
                return false;
            };
            let source_ty = source_variant.fields[index];
            if !self.subtype(source_ty, *target_ty) {
                return false;
            }
            if has_borrow(self, *target_ty) || has_mutable_borrow(self, *target_ty) {
                // Borrowed leaves are invariant under structural subtyping.
                if source_ty != *target_ty {
                    return false;
                }
            }
        }
        for (index, source_ty) in source_variant.names.iter().zip(&source_variant.fields) {
            if target_variant.names.contains(index) {
                continue;
            }
            if contains_linear(self, *source_ty) {
                return false;
            }
        }
        true
    }
    /// The canonical `(name, type)` row of a structural record layout.
    pub fn structural_row(&self, ty: Type) -> Option<Vec<(String, Type)>> {
        let id = ty.layout().filter(|id| self.enums[*id].structural)?;
        let variant = &self.enums[id].variants[0];
        Some(
            variant
                .names
                .iter()
                .cloned()
                .zip(variant.fields.iter().copied())
                .collect(),
        )
    }
    /// Whether two types have the same runtime word layout despite differing
    /// only in erased record lifetime labels.
    pub fn same_representation(&self, actual: Type, expected: Type) -> bool {
        actual == expected
            || match (actual, expected) {
                (Type::Annotated(a, _), Type::Annotated(b, _)) => {
                    self.same_representation(self.pointees[a], self.pointees[b])
                }
                (Type::Annotated(a, _), _) => self.same_representation(self.pointees[a], expected),
                (_, Type::Annotated(b, _)) => self.same_representation(actual, self.pointees[b]),
                (Type::Ref(a), Type::Ref(b)) | (Type::RefMut(a), Type::RefMut(b)) => {
                    self.same_representation(self.pointees[a], self.pointees[b])
                }
                (Type::RefMut(a), Type::Ref(b)) => {
                    self.same_representation(self.pointees[a], self.pointees[b])
                }
                (Type::Box(a), Type::Box(b))
                | (Type::ArenaBox(a), Type::ArenaBox(b))
                | (Type::Vec(a), Type::Vec(b)) => {
                    self.same_representation(self.pointees[a], self.pointees[b])
                }
                _ => {
                    actual.layout().is_some()
                        && expected.layout().is_some()
                        && self.same_erased_shape(actual, expected)
                }
            }
    }
    /// Deterministic representative for two atoms that are mutual subtypes.
    /// Mutually subtype arrows differ only in representation-free parts such
    /// as a `None`/`@[many]` parameter grade; prefer the more permissive,
    /// unannotated contract so canonicalization does not impose an exact-use
    /// demand that neither written order required.
    fn canonical_equivalent(&self, left: Type, right: Type) -> Type {
        match (left, right) {
            (Type::Fn(a), Type::Fn(b)) | (Type::Once(a), Type::Once(b)) => {
                let source = &self.function_types[a];
                let target = &self.function_types[b];
                let rank = |grades: &[Option<Grade>]| {
                    grades
                        .iter()
                        .map(|grade| match grade {
                            None => 0u8,
                            Some(Grade::Many) => 1,
                            Some(Grade::Finite(_) | Grade::Element(..)) => 2,
                        })
                        .collect::<Vec<_>>()
                };
                match rank(&source.parameter_grades).cmp(&rank(&target.parameter_grades)) {
                    std::cmp::Ordering::Less => left,
                    std::cmp::Ordering::Greater => right,
                    std::cmp::Ordering::Equal => left.min(right),
                }
            }
            _ => left.min(right),
        }
    }
    /// Arrow subtyping: contravariant parameters, covariant result, effect-row
    /// inclusion, and compatible usage contracts.
    fn function_subtype(&self, source: &FunctionType, target: &FunctionType) -> bool {
        if source.parameters.len() != target.parameters.len()
            || source.effects & !target.effects != 0
        {
            return false;
        }
        // A linear-once callable carries captured linear obligations. Widening
        // it to an affine once type would let an uncalled closure be dropped,
        // laundering those obligations. The reverse direction is safe: a
        // caller that promises exactly one call may consume an affine callable.
        if source.linear && !target.linear {
            return false;
        }
        if source
            .parameters
            .iter()
            .zip(&target.parameters)
            .any(|(source, target)| !self.subtype(*target, *source))
        {
            return false;
        }
        if !self.subtype(source.result, target.result) {
            return false;
        }
        // A result-transfer contract is not a representation detail. Dropping
        // it would let a linear resource escape through an arrow conversion, so
        // only an exact match is accepted (conservative but sound).
        if source.result_grade != target.result_grade {
            return false;
        }
        if !source.borrows.usable_as(&target.borrows) {
            return false;
        }
        source
            .parameter_grades
            .iter()
            .zip(&target.parameter_grades)
            .all(|(source, target)| grade_contract_compatible(*source, *target))
    }
    pub fn pointer(&mut self, ty: Type) -> usize {
        if let Some(index) = self.pointees.iter().position(|t| *t == ty) {
            return index;
        }
        let index = self.pointees.len();
        self.pointees.push(ty);
        index
    }
    /// Intern an erased lifetime name for a reference element stored inside a
    /// container. The empty name is the elided/unknown label at index zero.
    pub fn reference_label_id(&mut self, name: Option<&str>) -> u32 {
        let Some(name) = name.filter(|name| !name.is_empty()) else {
            return 0;
        };
        if let Some(index) = self.reference_labels.iter().position(|label| label == name) {
            return index as u32;
        }
        let index = self.reference_labels.len();
        self.reference_labels.push(name.to_owned());
        index as u32
    }
    pub fn reference_label_name(&self, id: u32) -> Option<String> {
        self.reference_labels
            .get(id as usize)
            .filter(|label| !label.is_empty())
            .cloned()
    }
    /// Attach the declared element lifetime to a direct reference element.
    /// Other pointees are unchanged; a nested container has already annotated
    /// its own direct reference leaf.
    fn annotate_container_element(
        &mut self,
        inner: Type,
        inner_ast: &ast::Type,
        substitution: &Subst,
    ) -> Type {
        if !matches!(inner, Type::Ref(_) | Type::RefMut(_) | Type::Str) {
            return inner;
        }
        let label = match &inner_ast.kind {
            ast::TypeKind::Borrow { lifetime, .. } => lifetime.as_ref().map(|name| {
                substitution
                    .lifetimes
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone())
            }),
            _ => None,
        };
        let inner_index = self.pointer(inner);
        let label = self.reference_label_id(label.as_deref());
        Type::Annotated(inner_index, label)
    }
    pub fn instantiate(
        &mut self,
        id: BindingId,
        arguments: Vec<Type>,
        consts: Vec<usize>,
        lifetimes: Vec<String>,
        span: Span,
    ) -> Result<usize> {
        let index = self.instantiate_raw(id, arguments, consts, lifetimes, span)?;
        self.finish_layouts(span)?;
        Ok(index)
    }
    fn instantiate_raw(
        &mut self,
        id: BindingId,
        arguments: Vec<Type>,
        consts: Vec<usize>,
        lifetimes: Vec<String>,
        span: Span,
    ) -> Result<usize> {
        let def = *self
            .definitions
            .get(&id)
            .ok_or_else(|| Diagnostic::new(span, "not a runtime enum"))?;
        let expected_types = def
            .generics
            .iter()
            .filter(|generic| !is_const_generic(self.resolution, generic))
            .count();
        let expected_consts = def.generics.len() - expected_types;
        if arguments.len() != expected_types || consts.len() != expected_consts {
            let natural = if expected_consts == 0 {
                String::new()
            } else {
                format!(" and {expected_consts} natural const argument(s)")
            };
            return Err(Diagnostic::new(
                span,
                format!(
                    "{} '{}' expects {} type arguments{}, found {} type and {} natural argument(s)",
                    if def.fields.is_some() {
                        "record"
                    } else {
                        "enum"
                    },
                    def.name,
                    expected_types,
                    natural,
                    arguments.len(),
                    consts.len()
                ),
            ));
        }
        if lifetimes.len() != def.lifetimes.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{} '{}' expects {} lifetime argument(s), found {}",
                    if def.fields.is_some() {
                        "record"
                    } else {
                        "enum"
                    },
                    def.name,
                    def.lifetimes.len(),
                    lifetimes.len()
                ),
            ));
        }
        let key = (id, arguments.clone(), consts.clone(), lifetimes.clone());
        if let Some(index) = self.cache.get(&key) {
            return Ok(*index);
        }
        if self.active.contains(&id) {
            return Err(Diagnostic::new(
                span,
                "non-regular recursive inline enum instantiation changes its type arguments",
            ));
        }
        if self.active.len() >= 32 || self.enums.len() >= 256 {
            return Err(Diagnostic::new(
                span,
                "runtime enum layout budget exhausted (32 levels, 256 instantiations)",
            ));
        }
        self.active.insert(id);
        let index = self.enums.len();
        self.enums.push(Enum {
            definition: id,
            name: def.name.to_owned(),
            arguments: arguments.clone(),
            consts: consts.clone(),
            lifetimes: lifetimes.clone(),
            variants: vec![],
            words: 0,
            result: None,
            array: None,
            dynamic_array: None,
            tuple: false,
            record: def.fields.is_some(),
            field_lifetimes: Vec::new(),
            borrowed: false,
            mutable_borrow: false,
            linear: def.linear,
            structural: false,
        });
        self.cache.insert(key.clone(), index);
        let mut substitution = Subst::default();
        let mut type_arguments = arguments.iter();
        let mut const_arguments = consts.iter();
        for generic in def.generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_const_generic(self.resolution, generic) {
                substitution.consts.insert(
                    binder,
                    *const_arguments
                        .next()
                        .expect("validated const argument count"),
                );
            } else {
                substitution.types.insert(
                    binder,
                    *type_arguments
                        .next()
                        .expect("validated type argument count"),
                );
            }
        }
        for (declared, actual) in def.lifetimes.iter().zip(&lifetimes) {
            substitution
                .lifetimes
                .insert(declared.name.clone(), actual.clone());
        }
        let built = (|| {
            let mut variants = Vec::new();
            let words = 0;
            let mut field_lifetimes = Vec::new();
            let mut borrowed = false;
            let mut mutable_borrow = false;
            if let Some(fields) = def.fields {
                let mut types = Vec::new();
                for field in fields {
                    let ty = self.lower(&field.ty, &substitution, 0).map(Type::full)?;
                    let direct = match &field.ty.kind {
                        ast::TypeKind::Borrow { lifetime, .. } => {
                            let Some(name) = lifetime else {
                                return Err(Diagnostic::new(
                                    field.span,
                                    "a borrowed record field must name a declared lifetime, as in 'view: &'a [T]' or 'point: &'a Point'",
                                ));
                            };
                            let Some(actual) = substitution.lifetimes.get(name) else {
                                return Err(Diagnostic::new(
                                    field.span,
                                    format!(
                                        "borrowed field lifetime '{name}' is not declared by record '{}'; declare it in the record's lifetime parameter list",
                                        def.name
                                    ),
                                ));
                            };
                            Some(actual.clone())
                        }
                        _ => None,
                    };
                    if matches!(ty, Type::Ref(_) | Type::RefMut(_)) && direct.is_none() {
                        return Err(Diagnostic::new(
                            field.span,
                            "a borrowed reference field must be written directly as '&'a T' or '&'a mut T' with a declared lifetime; aliases and generic substitution do not supply field provenance",
                        ));
                    }
                    if ty.is_slice() && direct.is_none() {
                        return Err(Diagnostic::new(
                            field.span,
                            "a borrowed slice field must be written directly as '&'a [T]' or '&'a mut [T]' with a declared lifetime; aliases and generic substitution do not supply field provenance",
                        ));
                    }
                    if let Some(label) = &direct {
                        if ty.is_slice() {
                            borrowed = true;
                            mutable_borrow |= ty.is_mut_slice();
                        } else if matches!(ty, Type::Ref(_) | Type::RefMut(_)) {
                            borrowed = true;
                            mutable_borrow |= matches!(ty, Type::RefMut(_));
                        } else if ty == Type::Str {
                            borrowed = true;
                        } else {
                            return Err(Diagnostic::new(
                                field.span,
                                "internal error: a declared borrow field did not lower to a slice view or reference",
                            ));
                        }
                        field_lifetimes.push(Some(label.clone()));
                    } else {
                        field_lifetimes.push(None);
                    }
                    types.push(ty);
                }
                if types.iter().any(|t| contains_task(self, *t)) {
                    return Err(Diagnostic::new(
                        span,
                        "task handles cannot be stored in records; join them in the scope that owns them",
                    ));
                }
                if types.iter().any(|t| has_borrow(self, *t)) {
                    borrowed = true;
                }
                if types.iter().any(|t| has_mutable_borrow(self, *t)) {
                    mutable_borrow = true;
                }
                if borrowed {
                    if def.linear {
                        return Err(Diagnostic::new(
                            span,
                            "a record with borrowed fields cannot be #[linear]; mixed borrowed and linear ownership is not implemented",
                        ));
                    }
                    for (field, ty) in fields.iter().zip(&types) {
                        // Owning metadata is allowed when it cannot hide a
                        // borrow: Box/Vec/Bytes and ordinary owned records or
                        // enums are dropped exactly once. Streams, unions,
                        // callables and linear obligations remain outside the
                        // mixed-record subset so none can be silently dropped
                        // or laundered.
                        if has_forbidden_record_metadata(self, *ty) {
                            return Err(Diagnostic::new(
                                field.span,
                                "a mixed borrowed record may contain Box, Vec, Bytes and ordinary owned records or enums, but not streams, unions, callables or task handles",
                            ));
                        }
                        if contains_linear(self, *ty) {
                            return Err(Diagnostic::new(
                                field.span,
                                "a mixed borrowed record cannot contain a linear field or an owned payload with a linear obligation; consume linear values outside the record",
                            ));
                        }
                        if matches!(
                            ty,
                            Type::Box(_)
                                | Type::ArenaBox(_)
                                | Type::Vec(_)
                                | Type::Bytes
                                | Type::String
                        ) && has_borrow(self, *ty)
                            && !is_reference_container(self, *ty)
                        {
                            return Err(Diagnostic::new(
                                field.span,
                                "an owning mixed record field must not hide a borrowed value; only direct reference elements are admitted in Box/Vec",
                            ));
                        }
                    }
                    // Every declared lifetime must describe at least one borrow
                    // leaf, so phantom lifetime parameters cannot be confused
                    // with the record's field provenance.
                    let mut used = BTreeSet::new();
                    for label in field_lifetimes.iter().flatten() {
                        used.insert(label.clone());
                    }
                    for ty in &types {
                        collect_borrow_lifetimes(self, *ty, &mut used);
                    }
                    for (declared, actual) in def.lifetimes.iter().zip(&lifetimes) {
                        if !used.contains(actual) {
                            return Err(Diagnostic::new(
                                declared.span,
                                format!(
                                    "record lifetime parameter '{}' is not used by a borrowed field or nested borrowed record",
                                    declared.name
                                ),
                            ));
                        }
                    }
                } else if !def.lifetimes.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "record '{}' declares lifetime parameters but has no borrowed field",
                            def.name
                        ),
                    ));
                }
                variants.push(Variant {
                    name: def.name.to_owned(),
                    fields: types,
                    tuple: true,
                    names: fields.iter().map(|f| f.name.clone()).collect(),
                });
            }
            let mut borrowed_payload: Option<Span> = None;
            for variant in def.variants {
                let (types, tuple) = match &variant.payload {
                    ast::Payload::Unit => (&[][..], false),
                    ast::Payload::Tuple(ts) => (ts.as_slice(), true),
                    _ => {
                        return Err(Diagnostic::new(
                            variant.span,
                            "runtime enum variants support only unit or tuple payloads",
                        ));
                    }
                };
                let fields = types
                    .iter()
                    .map(|t| self.lower(t, &substitution, 0).map(Type::full))
                    .collect::<Result<Vec<_>>>()?;
                if fields.iter().any(|t| has_borrow(self, *t)) {
                    borrowed_payload.get_or_insert(variant.span);
                    mutable_borrow |= fields.iter().any(|t| has_mutable_borrow(self, *t));
                }
                if fields.iter().any(|t| contains_task(self, *t)) {
                    return Err(Diagnostic::new(
                        variant.span,
                        "task handles cannot be stored in enum payloads; join them in the scope that owns them",
                    ));
                }
                variants.push(Variant {
                    name: variant.name.clone(),
                    fields,
                    tuple,
                    names: vec![],
                });
            }
            if let Some(span) = borrowed_payload {
                // The only enum value allowed to carry a borrowed payload is
                // the conventional structured-task exit. `Task.join` produces
                // it, and its borrow provenance is tracked by the ownership
                // pass until the matched record is consumed. User construction
                // of TaskExit<T> with a borrowed payload stays rejected, so the
                // only way to obtain one is Task.join.
                let completed = variants.iter().position(|v| v.name == "Completed");
                let cancelled = variants.iter().position(|v| v.name == "Cancelled");
                let conventional = def.name == "TaskExit"
                    && def.generics.len() == 1
                    && arguments.len() == 1
                    && variants.len() == 2
                    && is_borrowed_record(self, arguments[0])
                    && completed.is_some_and(|index| {
                        variants[index].tuple && variants[index].fields == [arguments[0]]
                    })
                    && cancelled.is_some_and(|index| {
                        !variants[index].tuple && variants[index].fields.is_empty()
                    });
                if !conventional {
                    return Err(Diagnostic::new(
                        span,
                        "enums cannot store borrowed references or slice views (or borrowed records); only TaskExit<T> may carry a borrowed task result, and only Task.join produces it",
                    ));
                }
            }
            // '?' recognizes the exact conventional Result<T,E> declaration,
            // never an arbitrary enum merely named Result with unrelated fields.
            let result = if def.name == "Result"
                && def.generics.len() == 2
                && expected_consts == 0
                && def.variants.len() == 2
            {
                let ok_tag = variants.iter().position(|v| v.name == "Ok");
                let err_tag = variants.iter().position(|v| v.name == "Err");
                match (ok_tag, err_tag) {
                    (Some(ok), Some(err))
                        if variants[ok].tuple
                            && variants[err].tuple
                            && variants[ok].fields == [arguments[0]]
                            && variants[err].fields == [arguments[1]]
                            && self.is_parameter_payload(&def.variants[ok], &def.generics[0])
                            && self.is_parameter_payload(&def.variants[err], &def.generics[1]) =>
                    {
                        Some(ResultShape {
                            ok_tag: ok,
                            err_tag: err,
                            ok: arguments[0],
                            error: arguments[1],
                        })
                    }
                    _ => None,
                }
            } else {
                None
            };
            if borrowed_payload.is_some() {
                borrowed = true;
            }
            Ok(Enum {
                definition: id,
                name: def.name.to_owned(),
                arguments: arguments.clone(),
                consts: consts.clone(),
                lifetimes,
                variants,
                words,
                result,
                array: None,
                dynamic_array: None,
                tuple: false,
                record: def.fields.is_some(),
                field_lifetimes,
                borrowed,
                mutable_borrow,
                linear: def.linear,
                structural: false,
            })
        })();
        self.active.remove(&id);
        let layout = built?;
        self.enums[index] = layout;
        Ok(index)
    }
    fn finish_layouts(&mut self, span: Span) -> Result<()> {
        fn size_of_type(
            ty: Type,
            enums: &[Enum],
            unions: &[UnionType],
            sizes: &mut [Option<usize>],
            active: &mut [bool],
            span: Span,
        ) -> Result<usize> {
            if let Some(child) = ty.layout() {
                return size(child, enums, unions, sizes, active, span);
            }
            match ty {
                Type::Union(id) => {
                    let mut largest = 0;
                    for member in &unions[id].members {
                        largest =
                            largest.max(size_of_type(*member, enums, unions, sizes, active, span)?);
                    }
                    Ok(1 + largest)
                }
                Type::Slice(_) | Type::SliceMut(_) | Type::Str => Ok(4),
                Type::Fn(_) => Ok(1),
                Type::Once(_) | Type::DynObj(_) => Ok(2),
                _ => Ok(1),
            }
        }
        fn size(
            id: usize,
            enums: &[Enum],
            unions: &[UnionType],
            sizes: &mut [Option<usize>],
            active: &mut [bool],
            span: Span,
        ) -> Result<usize> {
            if let Some(size) = sizes[id] {
                return Ok(size);
            }
            if active[id] {
                return Err(Diagnostic::new(
                    span,
                    "recursive inline enum layout; put recursive fields behind Box<T>",
                ));
            }
            active[id] = true;
            let mut largest = 1;
            for variant in &enums[id].variants {
                let mut words = 1;
                for ty in &variant.fields {
                    words += size_of_type(*ty, enums, unions, sizes, active, span)?;
                }
                largest = largest.max(words);
            }
            if largest > MAX_WORDS {
                return Err(Diagnostic::new(
                    span,
                    "inline enum exceeds the 32-word layout limit",
                ));
            }
            active[id] = false;
            sizes[id] = Some(largest);
            Ok(largest)
        }
        let mut sizes = vec![None; self.enums.len()];
        let mut active = vec![false; self.enums.len()];
        for id in 0..self.enums.len() {
            size(id, &self.enums, &self.unions, &mut sizes, &mut active, span)?;
        }
        for (layout, size) in self.enums.iter_mut().zip(&sizes) {
            layout.words = size.unwrap();
        }
        for union in &self.unions {
            let mut largest = 0;
            for member in &union.members {
                largest = largest.max(size_of_type(
                    *member,
                    &self.enums,
                    &self.unions,
                    &mut sizes,
                    &mut active,
                    span,
                )?);
            }
            if 1 + largest > MAX_WORDS {
                return Err(Diagnostic::new(
                    span,
                    "union exceeds the 32-word layout limit",
                ));
            }
        }
        Ok(())
    }
    fn is_parameter_payload(&self, variant: &ast::Variant, generic: &ast::Generic) -> bool {
        let ast::Payload::Tuple(fields) = &variant.payload else {
            return false;
        };
        fields.len() == 1
            && matches!(&fields[0].kind, ast::TypeKind::Named { arguments, .. } if arguments.is_empty())
            && self.resolution.reference(fields[0].span) == self.resolution.binder(generic.span)
    }
    pub fn owner(&self, constructor: BindingId) -> (BindingId, usize) {
        let b = &self.resolution.bindings[constructor];
        let owner = b.owner.unwrap();
        let name = b.name.rsplit('.').next().unwrap();
        let variant = self.definitions[&owner]
            .variants
            .iter()
            .position(|v| v.name == name)
            .unwrap();
        (owner, variant)
    }
    pub fn generic_count(&self, id: BindingId) -> usize {
        self.definitions[&id].generics.len()
    }
    /// For each declared generic of a nominal data type, `true` when it is a
    /// compile-time natural parameter. The order matches the declaration.
    pub fn generic_kinds(&self, id: BindingId) -> Vec<bool> {
        self.definitions[&id]
            .generics
            .iter()
            .map(|generic| is_const_generic(self.resolution, generic))
            .collect()
    }
    /// The conventional `TaskExit<T> { Completed(T), Cancelled }` required by
    /// `Task.join`. As with `Result`, only the exact shape is accepted.
    pub fn task_exit(
        &mut self,
        payload: Type,
        span: Span,
    ) -> Result<crate::executable::TaskExitShape> {
        let id = self
            .definitions
            .iter()
            .find(|(_, def)| def.name == "TaskExit")
            .map(|(id, _)| *id)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "Task.join requires enum TaskExit<T> { Completed(T), Cancelled } in this file",
                )
            })?;
        let ty = Type::Enum(self.instantiate(id, vec![payload], vec![], vec![], span)?);
        let Some(layout) = ty.layout() else {
            unreachable!("TaskExit is an enum")
        };
        let enum_ = &self.enums[layout];
        let completed = enum_
            .variants
            .iter()
            .position(|variant| variant.name == "Completed");
        let cancelled = enum_
            .variants
            .iter()
            .position(|variant| variant.name == "Cancelled");
        let (Some(completed), Some(cancelled)) = (completed, cancelled) else {
            return Err(Diagnostic::new(
                span,
                "Task.join requires the exact enum TaskExit<T> { Completed(T), Cancelled }",
            ));
        };
        let variant = &enum_.variants[completed];
        if enum_.variants.len() != 2
            || !variant.tuple
            || variant.fields != [payload]
            || enum_.variants[cancelled].tuple
            || !enum_.variants[cancelled].fields.is_empty()
        {
            return Err(Diagnostic::new(
                span,
                "Task.join requires the exact enum TaskExit<T> { Completed(T), Cancelled }",
            ));
        }
        Ok(crate::executable::TaskExitShape {
            completed_tag: completed,
            cancelled_tag: cancelled,
            payload,
            result: ty,
        })
    }
    pub fn io_result(&mut self, ok: Type, span: Span) -> Result<Type> {
        let Ok((ty, _)) = self.result_type(ok, Type::I64, span) else {
            return Err(Diagnostic::new(
                span,
                "I/O requires enum Result<T,E> { Ok(T), Err(E) } in this file",
            ));
        };
        Ok(ty)
    }
    /// The conventional `Result<T,E>` with exactly the requested payload types.
    /// Used by I/O and by checked UTF-8 conversion. A user declaration may
    /// order the variants either way.
    pub fn result_type(
        &mut self,
        ok: Type,
        error: Type,
        span: Span,
    ) -> Result<(Type, ResultShape)> {
        let id = self
            .definitions
            .iter()
            .find(|(_, def)| def.name == "Result")
            .map(|(id, _)| *id)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "this operation requires enum Result<T,E> { Ok(T), Err(E) } in this file",
                )
            })?;
        let ty = Type::Enum(self.instantiate(id, vec![ok, error], vec![], vec![], span)?);
        let shape = self.result(ty, span).map_err(|_| {
            Diagnostic::new(
                span,
                "this operation requires the exact conventional enum Result<T,E> { Ok(T), Err(E) }",
            )
        })?;
        if shape.ok != ok || shape.error != error {
            return Err(Diagnostic::new(
                span,
                "this operation requires the exact conventional enum Result<T,E> { Ok(T), Err(E) }",
            ));
        }
        Ok((ty, shape))
    }
    /// The conventional `Option<T> { None, Some(T) }` required by
    /// `Slice.try_get`. As with `Result` and `TaskExit`, only the exact shape
    /// is accepted, so a user declaration may order the variants either way.
    pub fn option(&mut self, id: BindingId, payload: Type, span: Span) -> Result<OptionShape> {
        if !self
            .definitions
            .get(&id)
            .is_some_and(|def| def.name == "Option")
        {
            return Err(Diagnostic::new(
                span,
                "Slice.try_get requires the exact enum Option<T> { None, Some(T) } in scope",
            ));
        }
        let ty = Type::Enum(self.instantiate(id, vec![payload], vec![], vec![], span)?);
        let Some(layout) = ty.layout() else {
            unreachable!("Option is an enum")
        };
        let enum_ = &self.enums[layout];
        let some = enum_
            .variants
            .iter()
            .position(|variant| variant.name == "Some");
        let none = enum_
            .variants
            .iter()
            .position(|variant| variant.name == "None");
        let (Some(some), Some(none)) = (some, none) else {
            return Err(Diagnostic::new(
                span,
                "Slice.try_get requires the exact enum Option<T> { None, Some(T) }",
            ));
        };
        let variant = &enum_.variants[some];
        let def = self.definitions[&id];
        if enum_.variants.len() != 2
            || !variant.tuple
            || variant.fields != [payload]
            || enum_.variants[none].tuple
            || !enum_.variants[none].fields.is_empty()
            || def.generics.len() != 1
            || !self.is_parameter_payload(&def.variants[some], &def.generics[0])
        {
            return Err(Diagnostic::new(
                span,
                "Slice.try_get requires the exact enum Option<T> { None, Some(T) }",
            ));
        }
        Ok(OptionShape {
            some_tag: some,
            none_tag: none,
            result: ty,
        })
    }
    pub fn result(&self, ty: Type, span: Span) -> Result<ResultShape> {
        if let Some(id) = ty.layout()
            && let Some(shape) = self.enums[id].result
        {
            return Ok(shape);
        }
        Err(Diagnostic::new(
            span,
            "'?' requires the conventional enum Result<T,E> { Ok(T), Err(E) } for both operand and enclosing return type",
        ))
    }
}
/// Convert a declared effect row to the executable effect bitset. Function
/// value types and direct declarations share this single rule. `subst` maps
/// `<e: Effects>` binders to concrete rows; a row is the union of its fixed
/// effect names and its substituted variables.
pub(crate) fn effect_bits_with(
    resolution: &Resolution,
    effects: &[ast::Type],
    subst: &BTreeMap<BindingId, u8>,
) -> Result<u8> {
    let (fixed, variables) = effect_bits_partial(resolution, effects)?;
    let mut bits = fixed;
    for variable in variables {
        let Some(value) = subst.get(&variable) else {
            return Err(Diagnostic::new(
                resolution.bindings[variable].span,
                format!(
                    "effect parameter '{}' is not specialized here; effect-polymorphic signatures require explicit specialization or an inferable callable argument",
                    resolution.bindings[variable].name
                ),
            ));
        };
        if *value & !crate::executable::EFFECT_BITS != 0 {
            return Err(Diagnostic::new(
                resolution.bindings[variable].span,
                "internal error: effect argument contains unknown effect bits",
            ));
        }
        bits |= *value;
    }
    Ok(bits)
}
/// Split an effect row into its fixed effect bits and its effect variables,
/// without requiring the variables to be specialized. Used to validate a
/// polymorphic declaration and to infer a row from callable arguments.
pub(crate) fn effect_bits_partial(
    resolution: &Resolution,
    effects: &[ast::Type],
) -> Result<(u8, Vec<BindingId>)> {
    let mut bits = 0u8;
    let mut variables = Vec::new();
    for effect in effects {
        effect_row_part(resolution, effect, &mut bits, &mut variables)?;
    }
    variables.sort();
    variables.dedup();
    Ok((bits, variables))
}
fn effect_row_part(
    resolution: &Resolution,
    effect: &ast::Type,
    bits: &mut u8,
    variables: &mut Vec<BindingId>,
) -> Result<()> {
    match &effect.kind {
        ast::TypeKind::Binary {
            op: crate::lexer::Kind::Pipe,
            left,
            right,
        } => {
            effect_row_part(resolution, left, bits, variables)?;
            effect_row_part(resolution, right, bits, variables)
        }
        ast::TypeKind::Named { arguments, .. } => {
            let Some(id) = resolution.reference(effect.span) else {
                return Err(Diagnostic::new(
                    effect.span,
                    "expected an executable effect name",
                ));
            };
            let binding = &resolution.bindings[id];
            if binding.kind == BindingKind::Generic && is_effect_generic_binding(resolution, id) {
                if !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        effect.span,
                        format!(
                            "effect parameter '{}' does not take arguments",
                            binding.name
                        ),
                    ));
                }
                variables.push(id);
                return Ok(());
            }
            let bit = match (binding.kind, binding.name.as_str(), arguments.is_empty()) {
                (BindingKind::Builtin, "panic", true) => crate::executable::PANIC,
                (BindingKind::Builtin, "io", true) => crate::executable::IO,
                (BindingKind::Builtin, "alloc", true) => crate::executable::ALLOC,
                (BindingKind::Builtin, "suspend", true) => crate::executable::SUSPEND,
                _ => {
                    return Err(Diagnostic::new(
                        effect.span,
                        "only io, alloc, suspend, and panic effects are supported by the executable subset; use an '<e: Effects>' row variable for a polymorphic row",
                    ));
                }
            };
            if *bits & bit != 0 {
                return Err(Diagnostic::new(effect.span, "duplicate effect"));
            }
            *bits |= bit;
            Ok(())
        }
        _ => Err(Diagnostic::new(
            effect.span,
            "expected an executable effect name or an effect-row variable",
        )),
    }
}
/// Whether a generic binder is an effect row parameter `<e: Effects>`.
pub(crate) fn is_effect_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    generic.bound.as_ref().is_some_and(|bound| {
        resolution.reference(bound.span).is_some_and(|id| {
            resolution.bindings[id].kind == BindingKind::Builtin
                && resolution.bindings[id].name == "Effects"
        })
    })
}
/// The concrete effects a binder's `<e: Effects - ...>` exclusion forbids, or
/// `None` when the binder is unconstrained.
///
/// Exclusions are a bound on specialization, not row subtraction: the returned
/// bits are never removed from a signature's effect row. Every leaf must name a
/// directly declared concrete effect. Effect variables, aliases, data, and
/// unknown names are rejected instead of being treated as row operations.
pub(crate) fn effect_excludes(
    resolution: &Resolution,
    generic: &ast::Generic,
) -> Result<Option<u8>> {
    let Some(excludes) = &generic.excludes else {
        return Ok(None);
    };
    let mut bits = 0u8;
    effect_exclusion_part(resolution, excludes, &mut bits)?;
    Ok(Some(bits))
}
/// Concrete effects required by a `<e: Effects + io>` lower bound.
pub(crate) fn effect_includes(
    resolution: &Resolution,
    generic: &ast::Generic,
) -> Result<Option<u8>> {
    let Some(includes) = &generic.includes else {
        return Ok(None);
    };
    let mut bits = 0u8;
    effect_exclusion_part(resolution, includes, &mut bits)?;
    Ok(Some(bits))
}
fn effect_exclusion_part(resolution: &Resolution, ty: &ast::Type, bits: &mut u8) -> Result<()> {
    match &ty.kind {
        ast::TypeKind::Binary {
            op: crate::lexer::Kind::Pipe,
            left,
            right,
        } => {
            effect_exclusion_part(resolution, left, bits)?;
            effect_exclusion_part(resolution, right, bits)
        }
        ast::TypeKind::Named { arguments, .. } => {
            if !arguments.is_empty() {
                return Err(Diagnostic::new(
                    ty.span,
                    "an effect exclusion names a concrete effect and takes no arguments",
                ));
            }
            let Some(id) = resolution.reference(ty.span) else {
                return Err(Diagnostic::new(
                    ty.span,
                    "an effect exclusion must name one of the concrete effects 'io', 'alloc', 'suspend', or 'panic'",
                ));
            };
            let binding = &resolution.bindings[id];
            let bit = match (binding.kind, binding.name.as_str()) {
                (BindingKind::Builtin, "panic") => crate::executable::PANIC,
                (BindingKind::Builtin, "io") => crate::executable::IO,
                (BindingKind::Builtin, "alloc") => crate::executable::ALLOC,
                (BindingKind::Builtin, "suspend") => crate::executable::SUSPEND,
                (BindingKind::Builtin, _) => {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "'{}' is not an effect; supported effects are 'io', 'alloc', 'suspend', and 'panic'",
                            binding.name
                        ),
                    ));
                }
                _ => {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "'{}' is not a concrete effect; an effect exclusion cannot mention an effect variable or another declaration",
                            binding.name
                        ),
                    ));
                }
            };
            *bits |= bit;
            Ok(())
        }
        _ => Err(Diagnostic::new(
            ty.span,
            "effect exclusions must be concrete effect names or a '|' union of them, as in '<e: Effects - (alloc | suspend)>'",
        )),
    }
}
fn is_effect_generic_binding(resolution: &Resolution, id: BindingId) -> bool {
    resolution.effect_binders.contains(&id)
}
/// Whether a generic binder is a compile-time natural const parameter.
pub(crate) fn is_const_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    generic.bound.as_ref().is_some_and(|bound| {
        resolution.reference(bound.span).is_some_and(|id| {
            resolution.bindings[id].kind == BindingKind::Builtin
                && resolution.bindings[id].name == "Nat"
        })
    })
}
/// Whether a generic binder is an abstract usage grade.
fn is_grade_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    generic.bound.as_ref().is_some_and(|bound| {
        resolution.reference(bound.span).is_some_and(|id| {
            resolution.bindings[id].kind == BindingKind::Builtin
                && resolution.bindings[id].name == "Grade"
        })
    })
}
/// Whether a data declaration uses a natural const parameter as an array
/// length somewhere in its fields or variant payloads.
fn data_uses_const(
    fields: &[ast::Field],
    variants: &[ast::Variant],
    resolution: &Resolution,
    binder: BindingId,
) -> bool {
    fn length_uses(ty: &ast::Type, resolution: &Resolution, binder: BindingId) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } => {
                resolution.reference(ty.span) == Some(binder)
                    || arguments
                        .iter()
                        .any(|argument| length_uses(argument, resolution, binder))
            }
            ast::TypeKind::Binary { left, right, .. } => {
                length_uses(left, resolution, binder) || length_uses(right, resolution, binder)
            }
            _ => false,
        }
    }
    fn ty_uses(ty: &ast::Type, resolution: &Resolution, binder: BindingId) -> bool {
        match &ty.kind {
            ast::TypeKind::Array(_, length) => length_uses(length, resolution, binder),
            ast::TypeKind::Named { arguments, .. } => {
                resolution.reference(ty.span) == Some(binder)
                    || arguments
                        .iter()
                        .any(|argument| ty_uses(argument, resolution, binder))
            }
            ast::TypeKind::Slice(inner) | ast::TypeKind::Borrow { inner, .. } => {
                ty_uses(inner, resolution, binder)
            }
            ast::TypeKind::Tuple(items) => {
                items.iter().any(|item| ty_uses(item, resolution, binder))
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| ty_uses(&parameter.ty, resolution, binder))
                    || ty_uses(result, resolution, binder)
            }
            ast::TypeKind::Binary { left, right, .. } => {
                ty_uses(left, resolution, binder) || ty_uses(right, resolution, binder)
            }
            ast::TypeKind::Graded { inner, .. } => ty_uses(inner, resolution, binder),
            _ => false,
        }
    }
    fields
        .iter()
        .any(|field| ty_uses(&field.ty, resolution, binder))
        || variants.iter().any(|variant| match &variant.payload {
            ast::Payload::Unit => variant
                .result
                .as_ref()
                .is_some_and(|result| ty_uses(result, resolution, binder)),
            ast::Payload::Tuple(types) => types.iter().any(|ty| ty_uses(ty, resolution, binder)),
            ast::Payload::Fields(fields) | ast::Payload::Record(fields) => fields
                .iter()
                .any(|field| ty_uses(&field.ty, resolution, binder)),
        })
}
/// Whether a source callable's exact parameter demand fits within the demand
/// promised by a target arrow type. A target may allow more uses than the
/// source performs, but never fewer. Unannotated source parameters may perform
/// an unbounded number of uses, so they are only compatible with an unbounded
/// target.
fn grade_contract_compatible(source: Option<Grade>, target: Option<Grade>) -> bool {
    // A source parameter graded `@[0]` is physically absent and never observed
    // by the callee. It is safe to use that function where a stricter usage
    // contract is expected: the extra argument supplied by callers is
    // evaluated for effects and then discarded. The reverse direction is not
    // safe, because the target caller would supply no value for a parameter
    // the source function observes.
    if source.is_some_and(Grade::is_zero) {
        return true;
    }
    match (source, target) {
        (_, None) => true,
        (_, Some(target)) if target.is_many() => true,
        (Some(source), Some(_)) if source.is_many() => false,
        (Some(source), Some(target)) => source == target,
        (None, Some(_)) => false,
    }
}
/// Whether a runtime type contains a task handle. Handles are scope-bound and
/// must not be stored in data that could outlive their scope.
/// Split a named type application's arguments into erased lifetime identities
/// and ordinary runtime type arguments. Lifetimes must come first, which keeps
/// `Window<'a, i64>` distinct from a type argument that merely mentions a
/// lifetime.
fn split_lifetime_arguments<'a>(
    arguments: &'a [ast::Type],
    substitution: &Subst,
    span: Span,
) -> Result<(Vec<String>, Vec<&'a ast::Type>)> {
    let mut lifetimes = Vec::new();
    let mut types = Vec::new();
    let mut seen_type = false;
    for argument in arguments {
        if let ast::TypeKind::Lifetime(name) = &argument.kind {
            if seen_type {
                return Err(Diagnostic::new(
                    span,
                    "lifetime arguments must precede type, natural, grade, and effect arguments",
                ));
            }
            lifetimes.push(
                substitution
                    .lifetimes
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
            );
        } else {
            seen_type = true;
            types.push(argument);
        }
    }
    Ok((lifetimes, types))
}
/// Declaration-level validation of lifetime binders and direct borrowed-field
/// syntax, including unused declarations. Restrictions requiring alias expansion
/// or concrete metadata ownership are checked when a record is instantiated.
fn validate_record_declaration(
    span: Span,
    lifetimes: &[ast::Lifetime],
    generics: &[ast::Generic],
    fields: &[ast::Field],
    linear: bool,
) -> Result<()> {
    fn collect_lifetimes(ty: &ast::Type, out: &mut BTreeSet<String>) {
        match &ty.kind {
            ast::TypeKind::Borrow {
                lifetime, inner, ..
            } => {
                if let Some(lifetime) = lifetime {
                    out.insert(lifetime.clone());
                }
                collect_lifetimes(inner, out);
            }
            ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
                for argument in arguments {
                    collect_lifetimes(argument, out);
                }
            }
            ast::TypeKind::Lifetime(name) => {
                out.insert(name.clone());
            }
            ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
                collect_lifetimes(inner, out)
            }
            ast::TypeKind::Array(inner, length) => {
                collect_lifetimes(inner, out);
                collect_lifetimes(length, out);
            }
            ast::TypeKind::Binary { left, right, .. } => {
                collect_lifetimes(left, out);
                collect_lifetimes(right, out);
            }
            ast::TypeKind::Function {
                lifetimes,
                parameters,
                result,
                effects,
                ..
            } => {
                // Lifetimes bound by the arrow itself are not free in the type.
                let mut inner = Default::default();
                for parameter in parameters {
                    collect_lifetimes(&parameter.ty, &mut inner);
                }
                collect_lifetimes(result, &mut inner);
                for effect in effects {
                    collect_lifetimes(effect, &mut inner);
                }
                for lifetime in lifetimes {
                    inner.retain(|name| *name != lifetime.name);
                }
                out.extend(inner);
            }
            _ => {}
        }
    }
    fn syntactic_unsupported_owned(ty: &ast::Type) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { path, .. } => path
                .last()
                .is_some_and(|name| matches!(name.as_str(), "Stdin" | "Stdout" | "Task")),
            ast::TypeKind::Function { .. } => true,
            ast::TypeKind::Binary { op, .. } => matches!(op, crate::lexer::Kind::Pipe),
            _ => false,
        }
    }
    let mut declared = BTreeSet::new();
    for lifetime in lifetimes {
        if let Some(bound) = lifetime.bounds.first() {
            return Err(Diagnostic::new(
                bound.span,
                "outlives bounds are only supported on executable function signatures; a record lifetime cannot declare a bound",
            ));
        }
        if !declared.insert(lifetime.name.clone()) {
            return Err(Diagnostic::new(
                lifetime.span,
                format!("duplicate lifetime parameter '{}'", lifetime.name),
            ));
        }
        if generics.iter().any(|generic| generic.name == lifetime.name) {
            return Err(Diagnostic::new(
                lifetime.span,
                "record lifetime parameters must be distinct from type, natural, grade, and effect generics",
            ));
        }
    }
    let mut used = BTreeSet::new();
    let mut borrowed = false;
    let mut direct_borrows = 0;
    for field in fields {
        match &field.ty.kind {
            ast::TypeKind::Borrow {
                lifetime,
                mutable: _,
                inner,
            } if !is_str_type(inner) => {
                let Some(name) = lifetime else {
                    return Err(Diagnostic::new(
                        field.span,
                        "records cannot store borrowed references or slice views without a declared lifetime; write 'struct R<'a> { view: &'a [T] }', 'struct R<'a> { point: &'a Point }', or 'struct R<'a> { point: &'a mut Point }'",
                    ));
                };
                if !declared.contains(name) {
                    return Err(Diagnostic::new(
                        field.span,
                        format!(
                            "borrowed field lifetime '{name}' is not declared by this record; declare it in the record's lifetime parameter list"
                        ),
                    ));
                }
                used.insert(name.clone());
                direct_borrows += 1;
                borrowed = true;
            }
            ast::TypeKind::Borrow { lifetime, inner, .. } if is_str_type(inner) => {
                let Some(name) = lifetime else {
                    return Err(Diagnostic::new(
                        field.span,
                        "records cannot store borrowed text views without a declared lifetime; write 'struct R<'a> { text: &'a str }'",
                    ));
                };
                if !declared.contains(name) {
                    return Err(Diagnostic::new(
                        field.span,
                        format!(
                            "borrowed field lifetime '{name}' is not declared by this record; declare it in the record's lifetime parameter list"
                        ),
                    ));
                }
                used.insert(name.clone());
                direct_borrows += 1;
                borrowed = true;
            }
            _ => {}
        }
        let mut mentioned = BTreeSet::new();
        collect_lifetimes(&field.ty, &mut mentioned);
        for name in &mentioned {
            if !declared.contains(name) {
                return Err(Diagnostic::new(
                    field.span,
                    format!(
                        "field lifetime '{name}' is not declared by this record's lifetime parameter list"
                    ),
                ));
            }
        }
        if !mentioned.is_empty() {
            borrowed = true;
        }
        used.extend(mentioned);
    }
    if borrowed {
        if linear {
            return Err(Diagnostic::new(
                span,
                "a record with borrowed fields cannot be #[linear]; mixed borrowed and linear ownership is not implemented",
            ));
        }
        if direct_borrows == 0 && !lifetimes.is_empty() && used.is_empty() {
            return Err(Diagnostic::new(
                span,
                "record declares lifetime parameters but has no borrowed field",
            ));
        }
        for field in fields {
            if syntactic_unsupported_owned(&field.ty) {
                return Err(Diagnostic::new(
                    field.span,
                    "a mixed borrowed record may contain Box, Vec, Bytes and ordinary owned records or enums, but not streams, unions, callables or task handles",
                ));
            }
        }
        for lifetime in lifetimes {
            if !used.contains(&lifetime.name) {
                return Err(Diagnostic::new(
                    lifetime.span,
                    format!(
                        "record lifetime parameter '{}' is not used by a borrowed field or nested borrowed record",
                        lifetime.name
                    ),
                ));
            }
        }
    } else if !lifetimes.is_empty() {
        return Err(Diagnostic::new(
            span,
            "record declares lifetime parameters but has no borrowed field",
        ));
    }
    Ok(())
}
/// Whether a type contains a shared/exclusive slice view, a borrowed owner
/// reference, or a record with such a leaf.
pub(crate) fn has_borrow(types: &Types<'_>, ty: Type) -> bool {
    fn go(types: &Types<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        match ty {
            Type::Ref(_) | Type::RefMut(_) | Type::Slice(_) | Type::SliceMut(_) | Type::Str => true,
            Type::Annotated(p, _) => go(types, types.pointees[p], seen),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => go(types, types.pointees[p], seen),
            Type::Enum(id) | Type::Variants(id, _) => {
                types.enums[id].borrowed
                    || types.enums[id]
                        .variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .any(|field| go(types, *field, seen))
            }
            Type::Union(id) => types.unions[id]
                .members
                .iter()
                .any(|member| go(types, *member, seen)),
            _ => false,
        }
    }
    go(types, ty, &mut BTreeSet::new())
}
/// Metadata exclusions apply through owned wrappers and nominal aggregates,
/// not only to the immediate field. Slice pointees describe borrowed storage,
/// rather than metadata stored by value, and are checked by slice validation.
fn has_forbidden_record_metadata(types: &Types<'_>, ty: Type) -> bool {
    let mut pending = vec![ty];
    let mut seen = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) {
            continue;
        }
        match ty {
            Type::Stdin
            | Type::Stdout
            | Type::Union(_)
            | Type::Fn(_)
            | Type::Once(_)
            | Type::Task(_) => return true,
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => pending.push(types.pointees[p]),
            Type::Enum(id) | Type::Variants(id, _) => pending.extend(
                types.enums[id]
                    .variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter())
                    .copied(),
            ),
            _ => {}
        }
    }
    false
}
/// Whether a type transitively contains an exclusive slice-view leaf. A
/// record with such a leaf is affine/move-only even when it owns no heap
/// storage, because copying its descriptor would duplicate an exclusive
/// capability.
pub(crate) fn has_mutable_borrow(types: &Types<'_>, ty: Type) -> bool {
    fn go(types: &Types<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        match ty {
            Type::SliceMut(_) | Type::RefMut(_) => true,
            Type::Annotated(p, _) => go(types, types.pointees[p], seen),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => go(types, types.pointees[p], seen),
            Type::Enum(id) | Type::Variants(id, _) => {
                types.enums[id].mutable_borrow
                    || types.enums[id]
                        .variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .any(|field| go(types, *field, seen))
            }
            Type::Union(id) => types.unions[id]
                .members
                .iter()
                .any(|member| go(types, *member, seen)),
            _ => false,
        }
    }
    go(types, ty, &mut BTreeSet::new())
}
/// Whether a type transitively carries an intrinsic linear obligation. Such a
/// value cannot be hidden in a mixed borrowed record, where it could be
/// dropped or copied without the explicit linear protocol.
pub(crate) fn contains_linear(types: &Types<'_>, ty: Type) -> bool {
    fn go(types: &Types<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        match ty {
            Type::Once(id) => types.function_types[id].linear,
            Type::Annotated(p, _) => go(types, types.pointees[p], seen),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => go(types, types.pointees[p], seen),
            Type::Enum(id) | Type::Variants(id, _) => {
                types.enums[id].linear
                    || types.enums[id]
                        .variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .any(|field| go(types, *field, seen))
            }
            Type::Union(id) => types.unions[id]
                .members
                .iter()
                .any(|member| go(types, *member, seen)),
            _ => false,
        }
    }
    go(types, ty, &mut BTreeSet::new())
}
/// Collect every erased lifetime label reachable through borrow leaves. A
/// direct slice leaf carries its label in the enclosing record's
/// `field_lifetimes`; nested records carry their own instantiated labels.
fn collect_borrow_lifetimes(types: &Types<'_>, ty: Type, out: &mut BTreeSet<String>) {
    fn go(types: &Types<'_>, ty: Type, out: &mut BTreeSet<String>, seen: &mut BTreeSet<Type>) {
        if !seen.insert(ty) {
            return;
        }
        match ty {
            Type::Slice(_) | Type::SliceMut(_) | Type::Str | Type::Ref(_) | Type::RefMut(_) => {}
            Type::Annotated(_, label) => {
                if let Some(name) = types.reference_label_name(label) {
                    out.insert(name);
                }
            }
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => {
                go(types, types.pointees[p], out, seen)
            }
            Type::Enum(id) | Type::Variants(id, _) => {
                let layout = &types.enums[id];
                out.extend(layout.lifetimes.iter().cloned());
                for argument in &layout.arguments {
                    go(types, *argument, out, seen);
                }
                for variant in &layout.variants {
                    for field in &variant.fields {
                        go(types, *field, out, seen);
                    }
                }
            }
            Type::Union(id) => {
                for member in &types.unions[id].members {
                    go(types, *member, out, seen);
                }
            }
            _ => {}
        }
    }
    go(types, ty, out, &mut BTreeSet::new());
}
/// One shared borrowed-slice leaf of a record value, addressed by field index
/// path from the record root. Checker-only: erased at runtime.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BorrowLeaf {
    pub path: Vec<usize>,
    pub lifetime: Option<String>,
    pub mutable: bool,
}
/// Whether `ty` is a nominal record with at least one borrowed slice field.
pub(crate) fn is_borrowed_record(types: &Types<'_>, ty: Type) -> bool {
    ty.layout()
        .is_some_and(|id| types.enums[id].record && types.enums[id].borrowed)
}
/// Whether `ty` is the conventional `TaskExit<T>` whose payload carries
/// borrowed storage. Only `Task.join` constructs such a value, but it may be
/// passed through a function or callable boundary when its leaves are declared.
pub(crate) fn is_borrowed_task_exit(types: &Types<'_>, ty: Type) -> bool {
    ty.layout().is_some_and(|id| {
        types.enums[id].name == "TaskExit"
            && types.enums[id]
                .variants
                .iter()
                .flat_map(|variant| variant.fields.iter())
                .any(|field| has_borrow(types, *field))
    })
}
/// Whether `ty` is an owning container whose element is (or contains) a
/// directly declared reference leaf. Such a value carries borrow provenance
/// even though its immediate type is not a reference or borrowed record.
pub(crate) fn is_reference_container(types: &Types<'_>, ty: Type) -> bool {
    match ty {
        Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => match types.pointees[p] {
            Type::Annotated(..) | Type::Ref(_) | Type::RefMut(_) => true,
            inner => is_reference_container(types, inner),
        },
        _ => false,
    }
}
/// Whether a type transitively contains a conventional `TaskExit<T>` whose
/// payload carries borrowed storage. Such a value is produced only by
/// `Task.join` and is checked lexically; it must not cross a function boundary,
/// a callable type, or an aggregate that could hide it.
pub(crate) fn contains_task_exit_borrow(types: &Types<'_>, ty: Type) -> bool {
    fn go(types: &Types<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        match ty {
            Type::Enum(id) | Type::Variants(id, _) => {
                let layout = &types.enums[id];
                if layout.name == "TaskExit"
                    && layout
                        .variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .any(|field| has_borrow(types, *field))
                {
                    return true;
                }
                layout
                    .variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter())
                    .any(|field| go(types, *field, seen))
            }
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) | Type::Task(p) => {
                go(types, types.pointees[p], seen)
            }
            Type::Union(id) => types.unions[id]
                .members
                .iter()
                .any(|member| go(types, *member, seen)),
            Type::Fn(id) | Type::Once(id) => types.function_types[id]
                .parameters
                .iter()
                .copied()
                .chain(std::iter::once(types.function_types[id].result))
                .any(|part| go(types, part, seen)),
            _ => false,
        }
    }
    go(types, ty, &mut BTreeSet::new())
}

pub(crate) fn borrow_leaves(types: &Types<'_>, ty: Type) -> Vec<BorrowLeaf> {
    fn go(
        types: &Types<'_>,
        ty: Type,
        hint: Option<String>,
        path: &mut Vec<usize>,
        out: &mut Vec<BorrowLeaf>,
    ) {
        match ty {
            Type::Slice(_) => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: false,
            }),
            Type::SliceMut(_) => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: true,
            }),
            Type::Str => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: false,
            }),
            Type::Ref(_) => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: false,
            }),
            Type::RefMut(_) => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: hint,
                mutable: true,
            }),
            Type::Annotated(p, label) => out.push(BorrowLeaf {
                path: path.clone(),
                lifetime: types.reference_label_name(label),
                mutable: matches!(types.pointees[p], Type::RefMut(_)),
            }),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => {
                go(types, types.pointees[p], None, path, out)
            }
            Type::Enum(id) | Type::Variants(id, _)
                if types.enums[id].record || types.enums[id].name == "TaskExit" =>
            {
                if types.enums[id].record {
                    for (index, field) in types.enums[id].variants[0].fields.iter().enumerate() {
                        path.push(index);
                        let field_hint = types.enums[id].field_lifetimes[index].clone();
                        go(types, *field, field_hint, path, out);
                        path.pop();
                    }
                } else {
                    // A borrowed `TaskExit<T>` payload travels at the same paths
                    // as `T`: matching `Completed(value)` rebinds those leaves
                    // directly to the inner value.
                    for variant in &types.enums[id].variants {
                        for field in &variant.fields {
                            go(types, *field, None, path, out);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(types, ty, None, &mut Vec::new(), &mut out);
    out
}

/// Structural ownership for a lowered type, used while checking a result
/// contract before the ownership pass has computed the enum ownership table.
/// It follows the same rules as the later ownership analysis: boxes, buffers,
/// strings, vectors, callables, task handles, linear layouts, and any layout
/// with an owning field are owning.
pub(crate) fn type_owns(enums: &[Enum], unions: &[UnionType], ty: Type, depth: usize) -> bool {
    if depth >= 64 {
        return false;
    }
    match ty {
        Type::Box(_)
        | Type::Arena
        | Type::ArenaBox(_)
        | Type::Bytes
        | Type::String
        | Type::Vec(_)
        | Type::Once(_)
        | Type::Task(_)
        | Type::DynObj(_) => true,
        Type::Enum(id) | Type::Variants(id, _) => {
            enums[id].linear
                || enums[id]
                    .variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter())
                    .any(|field| type_owns(enums, unions, *field, depth + 1))
        }
        Type::Union(id) => unions[id]
            .members
            .iter()
            .any(|member| type_owns(enums, unions, *member, depth + 1)),
        _ => false,
    }
}

pub(crate) fn contains_task(types: &Types<'_>, ty: Type) -> bool {
    fn go(types: &Types<'_>, ty: Type, seen: &mut BTreeSet<Type>) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        match ty {
            Type::Task(_) => true,
            Type::Annotated(p, _) => go(types, types.pointees[p], seen),
            Type::Box(p) | Type::ArenaBox(p) | Type::Vec(p) => go(types, types.pointees[p], seen),
            Type::Enum(id) | Type::Variants(id, _) => types.enums[id]
                .variants
                .iter()
                .flat_map(|variant| variant.fields.iter())
                .any(|field| go(types, *field, seen)),
            Type::Union(id) => types.unions[id]
                .members
                .iter()
                .any(|member| go(types, *member, seen)),
            _ => false,
        }
    }
    go(types, ty, &mut BTreeSet::new())
}

pub(crate) fn width(
    pointees: &[Type],
    enums: &[Enum],
    unions: &[UnionType],
    functions: &[FunctionType],
    ty: Type,
) -> usize {
    if let Some(index) = ty.layout() {
        enums[index].words
    } else if let Type::Union(id) = ty {
        // One discriminator word plus the widest active alternative.
        1 + unions[id]
            .members
            .iter()
            .map(|member| width(pointees, enums, unions, functions, *member))
            .max()
            .unwrap_or(0)
    } else if let Type::Annotated(p, _) = ty {
        // A container element annotation is representation-free: it has the
        // same width as the annotated element (a one-word reference or a
        // four-word text view).
        width(pointees, enums, unions, functions, pointees[p])
    } else if matches!(ty, Type::Slice(_) | Type::SliceMut(_) | Type::Str) {
        // (data pointer, length, stride, byte-elements flag)
        4
    } else if matches!(ty, Type::Once(_)) {
        // (code pointer, owned environment pointer)
        2
    } else if matches!(ty, Type::DynObj(_)) {
        // (member identifier, owned payload pointer)
        2
    } else {
        let _ = functions;
        1
    }
}
pub(crate) fn full_mask(variants: usize) -> u64 {
    if variants >= 64 {
        u64::MAX
    } else {
        (1u64 << variants) - 1
    }
}
/// The variants selected by an enum or variant-set type. A non-layout type
/// selects nothing.
pub(crate) fn mask_of(ty: Type, enums: &[Enum]) -> u64 {
    match ty {
        Type::Enum(id) => full_mask(enums[id].variants.len()),
        Type::Variants(_, mask) => mask,
        _ => 0,
    }
}
/// Normalize a variant set: the full set is the enum itself.
pub(crate) fn refine(enums: &[Enum], id: usize, mask: u64) -> Type {
    if mask == 0 {
        Type::Never
    } else if mask == full_mask(enums[id].variants.len()) {
        Type::Enum(id)
    } else {
        Type::Variants(id, mask)
    }
}
fn ty_span(_: Type, span: Span) -> Span {
    span
}

/// The lifetime of a slice parameter in an arrow type: its explicit name
/// (which the arrow must bind) or a fresh elided identity.
fn arrow_lifetime(
    ty: &ast::Type,
    declared: &BTreeSet<String>,
    index: usize,
    span: Span,
) -> Result<String> {
    let _ = span;
    Ok(arrow_explicit_lifetime(ty, declared)?.unwrap_or_else(|| format!("<elided {index}>")))
}
fn arrow_explicit_lifetime(ty: &ast::Type, declared: &BTreeSet<String>) -> Result<Option<String>> {
    let ast::TypeKind::Borrow { lifetime, .. } = &ty.kind else {
        return Ok(None);
    };
    match lifetime {
        Some(name) if declared.contains(name) => Ok(Some(name.clone())),
        Some(name) => Err(Diagnostic::new(
            ty.span,
            format!(
                "lifetime '{name}' in a function arrow type must be bound by the arrow itself, as in fn<'{0}>(&'{0} [T]) -> ...; an arrow cannot borrow for an outer lifetime",
                name.trim_start_matches('\'')
            ),
        )),
        None => Ok(None),
    }
}
