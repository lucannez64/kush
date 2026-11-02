//! Usage grades: natural multiplicities, unbounded usage, and exact-use checking.
//!
//! ## Algebra
//!
//! A grade is an element of the ordered semiring of natural usage bounds
//! extended with infinity:
//!
//! ```text
//! Grade = 0 | 1 | 2 | ... | many
//! 0 + g = g           g + many = many        (checked finite addition)
//! 0 * g = 0           n * many = many (n > 0) (checked finite multiplication)
//! 1 * g = g           many * many = many
//! ```
//!
//! `0 * many = 0` is the annihilation law: an expression whose result is used
//! zero times cannot duplicate anything, even when the enclosing operation
//! permits arbitrary duplication. Finite arithmetic is overflow-checked; a
//! grade annotation that overflows 64 bits is rejected rather than silently
//! becoming `many`.
//!
//! ## Surface forms
//!
//! * `T @[0]` — ghost/non-observable binding. The value must not be read,
//!   moved, borrowed, or passed at runtime. Owning/linear values are rejected:
//!   a grade must never silently discard storage.
//! * `T @[1]` — exactly one use. For owning/linear storage this remains the
//!   original linear obligation (the ownership pass also enforces it). For a
//!   copyable value the grade checker enforces exactly one observation.
//! * `T @[n]`, `n >= 2` — exactly `n` uses. Only copyable, non-linear values.
//! * `T @[many]` — unrestricted use. Only copyable, non-linear values.
//! * `T @[G]`, `T @[G + 1]`, `T @[G * 2]` — an abstract grade parameter,
//!   declared as `<G: Grade>`. Instances are created only by explicit
//!   compile-time specialization (`f::<..., 4>(...)`). No runtime grade value
//!   exists.
//!
//! Grade expressions support `+`, `*`, parentheses, natural literals, `many`,
//! and grade variables. They are evaluated entirely at compile time.
//!
//! ## Checking rules
//!
//! * Each use of a copyable binding contributes its surrounding duplication
//!   demand to the binding's use count. A call argument is evaluated under the
//!   callee parameter's demand: passing a variable to a `@[2]` parameter counts
//!   as two uses, to a `@[many]` parameter as unbounded use, and to a `@[0]`
//!   parameter as one evaluation (strict evaluation still reads the argument;
//!   the callee simply cannot observe the parameter).
//! * Consuming an owning/linear value (`Move`, `Box.take`, a move into a call)
//!   counts once regardless of demand. Owning/linear parameters cannot be
//!   graded above one, so a callee can only duplicate a *copyable result*, not
//!   the owner that produced it.
//! * Sequential uses add. Branches (`if`, `match`, short-circuit right
//!   operands) must produce the same count on every normally surviving path.
//! * A `return` and the error path of `?` check every in-scope exact grade
//!   before transferring control.
//! * Loop back-edges, `break`, and `continue` require outer exact-grade counts
//!   to be restored to their loop-entry values. A loop may therefore use and
//!   reassign a graded binding each iteration, but may not consume a fixed
//!   outer budget an unknown number of times. Locals bound inside the loop must
//!   satisfy their exact grade on every iteration.
//! * A match guard cannot observe a finite exact-grade binding: a guard is
//!   evaluated a path-dependent number of times. `@[many]` bindings remain
//!   usable in guards; owning borrows are not consumptions and stay legal.
//! * Assignment to a graded mutable binding requires the old value to have met
//!   its exact grade, then starts a new obligation for the replacement value.
//!
//! These rules are deliberately conservative at a few boundaries (notably
//! side-effecting blocks passed to a high-demand parameter, and loops). They
//! reject programs they cannot decide; they do not infer an exact grade from
//! runtime values.
use crate::{
    Diagnostic, Span, ast,
    executable::{
        Block, BytesOp, Executable, Expr, ExprKind, Function, Statement, Target, Type, VecOp,
    },
    resolve::{BindingId, Resolution},
};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, Diagnostic>;

/// Compiler-owned, law-checked finite grade algebra. Executables retain their
/// tables; copyable grade handles use a weak registry and never own/leak data.
#[derive(Debug)]
pub(crate) struct Algebra {
    id: u64,
    pub name: String,
    pub elements: Vec<String>,
    pub add: Vec<Vec<usize>>,
    pub mul: Vec<Vec<usize>>,
    pub zero: usize,
    pub one: usize,
}
impl Algebra {
    pub(crate) fn element(&self, name: &str) -> Option<usize> {
        self.elements.iter().position(|element| element == name)
    }
}
type AlgebraRegistry = std::sync::Mutex<BTreeMap<u64, std::sync::Weak<Algebra>>>;
fn algebra_registry() -> &'static AlgebraRegistry {
    static REGISTRY: std::sync::OnceLock<AlgebraRegistry> = std::sync::OnceLock::new();
    REGISTRY.get_or_init(Default::default)
}
impl Drop for Algebra {
    fn drop(&mut self) {
        algebra_registry()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&self.id);
    }
}
/// Stable identity only; the resolving compilation/executable owns the tables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct AlgebraRef(u64);
impl AlgebraRef {
    fn get(self) -> std::sync::Arc<Algebra> {
        let table = {
            let registry = algebra_registry()
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            registry.get(&self.0).and_then(std::sync::Weak::upgrade)
        };
        // An invariant failure must not poison the global registry or turn
        // subsequent table cleanup into a second panic during unwinding.
        table.expect("grade algebra must remain owned by its compilation or executable")
    }
}
/// The usage semiring: finite natural bounds plus infinity, extended with
/// finite user-defined algebra elements.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Grade {
    Finite(u64),
    Many,
    /// An element of a validated finite algebra, identified by a weak table
    /// handle and element index. The executable retains the table owner.
    Element(AlgebraRef, usize),
}
impl PartialEq for Grade {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => a == b,
            (Self::Many, Self::Many) => true,
            (Self::Element(a, x), Self::Element(b, y)) => a == b && x == y,
            _ => false,
        }
    }
}
impl Eq for Grade {}
impl std::hash::Hash for Grade {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Finite(value) => {
                0u8.hash(state);
                value.hash(state);
            }
            Self::Many => 1u8.hash(state),
            Self::Element(algebra, element) => {
                2u8.hash(state);
                algebra.hash(state);
                element.hash(state);
            }
        }
    }
}
impl PartialOrd for Grade {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Grade {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        fn rank(grade: &Grade) -> u8 {
            match grade {
                Grade::Finite(_) => 0,
                Grade::Many => 1,
                Grade::Element(..) => 2,
            }
        }
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => a.cmp(b),
            (Self::Many, Self::Many) => Ordering::Equal,
            (Self::Element(a, x), Self::Element(b, y)) => a.cmp(b).then(x.cmp(y)),
            _ => rank(self).cmp(&rank(other)),
        }
    }
}
impl Grade {
    pub(crate) const ZERO: Self = Self::Finite(0);
    pub(crate) const ONE: Self = Self::Finite(1);

    pub(crate) fn is_zero(self) -> bool {
        match self {
            Self::Finite(0) => true,
            Self::Element(algebra, element) => element == algebra.get().zero,
            _ => false,
        }
    }
    pub(crate) fn is_one(self) -> bool {
        match self {
            Self::Finite(1) => true,
            Self::Element(algebra, element) => element == algebra.get().one,
            _ => false,
        }
    }
    pub(crate) fn is_many(self) -> bool {
        matches!(self, Self::Many)
    }
    pub(crate) fn algebra_zero(algebra: AlgebraRef) -> Self {
        Self::Element(algebra, algebra.get().zero)
    }
    /// Repeated addition of one algebra element. Bounded so a hostile finite
    /// demand cannot make the compiler loop for an unbounded time.
    fn repeated_add(handle: AlgebraRef, element: usize, times: u64) -> Option<Self> {
        if times > 1_000_000 {
            return None;
        }
        let algebra = handle.get();
        let mut result = algebra.zero;
        for _ in 0..times {
            result = algebra.add[result][element];
        }
        Some(Self::Element(handle, result))
    }
    /// Addition with checked finite overflow. `None` means the mathematical
    /// finite result does not fit in `u64` or mixes incompatible algebras;
    /// callers checking a source annotation report an error instead of
    /// approximating it.
    pub(crate) fn checked_add(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Many, _) | (_, Self::Many) => Some(Self::Many),
            (Self::Finite(a), Self::Finite(b)) => a.checked_add(b).map(Self::Finite),
            (Self::Element(a, x), Self::Element(b, y)) if a == b => {
                Some(Self::Element(a, a.get().add[x][y]))
            }
            (Self::Element(a, x), Self::Finite(n)) => {
                Self::repeated_add(a, a.get().one, n).map(|amount| match amount {
                    Self::Element(_, count) => Self::Element(a, a.get().add[x][count]),
                    _ => unreachable!("repeated_add stays in its algebra"),
                })
            }
            (Self::Finite(n), Self::Element(b, y)) => {
                Self::repeated_add(b, b.get().one, n).map(|amount| match amount {
                    Self::Element(_, count) => Self::Element(b, b.get().add[count][y]),
                    _ => unreachable!("repeated_add stays in its algebra"),
                })
            }
            _ => None,
        }
    }
    /// Multiplication with the extended-natural annihilation law `0 * many = 0`
    /// and the declared finite algebra table.
    pub(crate) fn checked_mul(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Finite(0), Self::Element(algebra, _))
            | (Self::Element(algebra, _), Self::Finite(0)) => {
                Some(Self::Element(algebra, algebra.get().zero))
            }
            (Self::Finite(0), _) | (_, Self::Finite(0)) => Some(Self::ZERO),
            (Self::Many, Self::Many) => Some(Self::Many),
            (Self::Many, Self::Finite(_)) | (Self::Finite(_), Self::Many) => Some(Self::Many),
            (Self::Finite(a), Self::Finite(b)) => a.checked_mul(b).map(Self::Finite),
            (Self::Element(a, x), Self::Element(b, y)) if a == b => {
                Some(Self::Element(a, a.get().mul[x][y]))
            }
            (Self::Element(a, x), Self::Finite(n)) => Self::repeated_add(a, x, n),
            (Self::Finite(n), Self::Element(b, y)) => Self::repeated_add(b, y, n),
            _ => None,
        }
    }
    /// Saturating addition for observed usage counts. A count that overflows
    /// or leaves its algebra becomes unbounded; a finite exact grade can then
    /// never match it.
    fn saturating_add(self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::Many)
    }
    fn saturating_mul(self, other: Self) -> Self {
        self.checked_mul(other).unwrap_or(Self::Many)
    }
}
impl std::fmt::Display for Grade {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Finite(0) => f.write_str("0"),
            Self::Finite(n) => write!(f, "{n}"),
            Self::Many => f.write_str("many"),
            Self::Element(algebra, element) => {
                let algebra = algebra.get();
                write!(f, "{}.{}", algebra.name, algebra.elements[*element])
            }
        }
    }
}

/// Split `T @[grade]` into the underlying type and the grade expression.
pub(crate) fn split(ty: &ast::Type) -> (&ast::Type, Option<&ast::Type>) {
    match &ty.kind {
        ast::TypeKind::Graded { inner, grade } => (inner, Some(grade)),
        _ => (ty, None),
    }
}

/// Count occurrences of `binder` in a grade/type expression.
fn grade_occurrences(resolution: &Resolution, ty: &ast::Type, binder: BindingId) -> usize {
    use ast::TypeKind as K;
    match &ty.kind {
        K::Named { arguments, .. } => {
            usize::from(resolution.reference(ty.span) == Some(binder))
                + arguments
                    .iter()
                    .map(|argument| grade_occurrences(resolution, argument, binder))
                    .sum::<usize>()
        }
        K::Tuple(items) => items
            .iter()
            .map(|item| grade_occurrences(resolution, item, binder))
            .sum(),
        K::Structural { fields, .. } => fields
            .iter()
            .map(|field| grade_occurrences(resolution, &field.ty, binder))
            .sum(),
        K::Slice(inner) | K::Borrow { inner, .. } | K::Dyn(inner) => {
            grade_occurrences(resolution, inner, binder)
        }
        K::Array(element, length) => {
            grade_occurrences(resolution, element, binder)
                + grade_occurrences(resolution, length, binder)
        }
        K::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .map(|parameter| grade_occurrences(resolution, &parameter.ty, binder))
                .sum::<usize>()
                + grade_occurrences(resolution, result, binder)
                + effects
                    .iter()
                    .map(|effect| grade_occurrences(resolution, effect, binder))
                    .sum::<usize>()
        }
        K::Binary { left, right, .. } => {
            grade_occurrences(resolution, left, binder)
                + grade_occurrences(resolution, right, binder)
        }
        K::Graded { inner, grade } => {
            grade_occurrences(resolution, inner, binder)
                + grade_occurrences(resolution, grade, binder)
        }
        K::Integer(_) | K::Bool(_) | K::Lifetime(_) | K::SelfType | K::Predicate(_) => 0,
    }
}

/// Maximum number of candidate naturals examined for one polynomial equation.
/// Targets above this bound stay outside the inference fragment rather than
/// turning compilation into an unbounded search.
const SOLVER_BUDGET: u64 = 100_000;

/// Solve a set of grade constraints simultaneously.
///
/// Each constraint pairs a declared grade expression with the concrete grade
/// required at that position. A binder is solved only when it is the single
/// remaining unknown in that expression; solutions are substituted back into
/// every other constraint, so later equations can mention earlier binders.
/// Conflicting equations are reported, and a binder that no constraint can
/// determine stays unsolved instead of being guessed.
pub(crate) fn solve_all(
    resolution: &Resolution,
    base: &BTreeMap<BindingId, Grade>,
    binders: &[BindingId],
    constraints: &[(&ast::Type, Grade)],
) -> Result<Option<BTreeMap<BindingId, Grade>>> {
    let mut solved: BTreeMap<BindingId, Grade> = BTreeMap::new();
    loop {
        let mut progress = false;
        for binder in binders {
            if solved.contains_key(binder) {
                continue;
            }
            let mut variables = base.clone();
            variables.extend(solved.iter().map(|(key, value)| (*key, *value)));
            for (expr, target) in constraints {
                if grade_occurrences(resolution, expr, *binder) == 0 {
                    continue;
                }
                let unresolved = binders
                    .iter()
                    .filter(|other| {
                        !variables.contains_key(*other)
                            && grade_occurrences(resolution, expr, **other) > 0
                    })
                    .copied()
                    .collect::<Vec<_>>();
                if unresolved.as_slice() != [*binder] {
                    continue;
                }
                let Some(solution) = solve_binder(resolution, &variables, expr, *binder, *target)?
                else {
                    continue;
                };
                // A candidate must satisfy every constraint that is already
                // evaluable; otherwise the system is inconsistent.
                let mut trial = variables.clone();
                trial.insert(*binder, solution);
                for (other_expr, other_target) in constraints {
                    if let Ok(value) = evaluate(resolution, &trial, other_expr)
                        && value != *other_target
                    {
                        return Err(Diagnostic::new(
                            resolution.bindings[*binder].span,
                            format!(
                                "conflicting inferred grades for '{}': one position requires @[{other_target}] but the simultaneous solution @[{solution}] gives @[{value}]",
                                resolution.bindings[*binder].name
                            ),
                        ));
                    }
                }
                solved.insert(*binder, solution);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    let mut variables = base.clone();
    variables.extend(solved.iter().map(|(key, value)| (*key, *value)));
    for (expr, target) in constraints {
        if let Ok(value) = evaluate(resolution, &variables, expr)
            && value != *target
        {
            return Err(Diagnostic::new(
                expr.span,
                format!(
                    "conflicting grade constraints: this position requires @[{target}] but the simultaneous solution gives @[{value}]"
                ),
            ));
        }
    }
    Ok((solved.len() == binders.len()).then_some(solved))
}

/// The unique finite algebra named by element leaves/target, if any.
fn grade_algebra(resolution: &Resolution, expr: &ast::Type, target: Grade) -> Option<AlgebraRef> {
    let algebra = match target {
        Grade::Element(algebra, _) => Some(algebra),
        _ => None,
    };
    let found = algebra_leaf(resolution, expr);
    match (algebra, found) {
        (Some(existing), Some(found)) if existing != found => None,
        (Some(existing), _) => Some(existing),
        (None, found) => found,
    }
}

fn algebra_leaf(resolution: &Resolution, expr: &ast::Type) -> Option<AlgebraRef> {
    use ast::TypeKind as K;
    match &expr.kind {
        K::Named { path, arguments } => {
            if arguments.is_empty()
                && path.len() == 2
                && let Some(table) = resolution.lowered_algebras.get(&path[0])
                && table.element(&path[1]).is_some()
            {
                return Some(AlgebraRef(table.id));
            }
            arguments
                .iter()
                .find_map(|argument| algebra_leaf(resolution, argument))
        }
        K::Binary { left, right, .. } => {
            algebra_leaf(resolution, left).or_else(|| algebra_leaf(resolution, right))
        }
        K::Slice(inner) | K::Borrow { inner, .. } | K::Dyn(inner) => {
            algebra_leaf(resolution, inner)
        }
        _ => None,
    }
}

/// Solve one binder from a single expression. Returns `None` when the equation
/// has no unique solution or lies outside the documented decidable fragment.
fn solve_binder(
    resolution: &Resolution,
    variables: &BTreeMap<BindingId, Grade>,
    expr: &ast::Type,
    binder: BindingId,
    target: Grade,
) -> Result<Option<Grade>> {
    if crate::executable::bare_grade_binder(resolution, expr) == Some(binder) {
        return Ok(Some(target));
    }
    // Finite algebra: enumerate the carrier. A carrier has at most 64
    // elements, so this is a bounded, exhaustive search with an explicit
    // uniqueness requirement.
    if let Some(algebra) = grade_algebra(resolution, expr, target) {
        let table = algebra.get();
        let mut found = None;
        let mut count = 0;
        for element in 0..table.elements.len() {
            let mut trial = variables.clone();
            trial.insert(binder, Grade::Element(algebra, element));
            if let Ok(value) = evaluate(resolution, &trial, expr)
                && value == target
            {
                count += 1;
                found = Some(Grade::Element(algebra, element));
            }
        }
        return Ok((count == 1).then_some(found).flatten());
    }
    let Grade::Finite(wanted) = target else {
        // A `many` target has no unique finite solution; only a bare binder
        // (handled above) can be assigned `many` directly.
        return Ok(None);
    };
    let mut at_zero = variables.clone();
    at_zero.insert(binder, Grade::ZERO);
    let zero = match evaluate(resolution, &at_zero, expr) {
        Ok(Grade::Finite(value)) => value,
        _ => return Ok(None),
    };
    let mut at_one = variables.clone();
    at_one.insert(binder, Grade::ONE);
    let one = match evaluate(resolution, &at_one, expr) {
        Ok(Grade::Finite(value)) => value,
        _ => return Ok(None),
    };
    // Every expression in this fragment has nonnegative integer coefficients
    // and no subtraction. If it grows between 0 and 1, it contains a term
    // `c * g^k` with `c >= 1`, so `e(g) >= g` for every `g >= 1`. A target
    // larger than `g` therefore proves that no solution exists above the
    // target, which makes enumeration up to the target complete.
    if one <= zero {
        return Ok(None);
    }
    if wanted > SOLVER_BUDGET {
        return Ok(None);
    }
    let mut found = None;
    let mut count = 0;
    for candidate in 0..=wanted {
        let mut trial = variables.clone();
        trial.insert(binder, Grade::Finite(candidate));
        match evaluate(resolution, &trial, expr) {
            Ok(value) if value == target => {
                count += 1;
                found = Some(Grade::Finite(candidate));
            }
            Ok(_) => {}
            // An overflow above the target cannot be the solution. Because
            // the expression is monotone in the binder, no later candidate
            // can return to the target value either.
            Err(_) => break,
        }
    }
    Ok((count == 1).then_some(found).flatten())
}

/// Validate and lower every declared finite grade algebra. The operation
/// tables must be total and are checked by exhaustive enumeration: zero/one
/// identities, commutativity, associativity, distributivity, and zero
/// annihilation. A law is never assumed; a failure names the algebra and law.
pub(crate) fn validate_algebras(resolution: &mut Resolution) -> Result<()> {
    let names = resolution.algebras.keys().cloned().collect::<Vec<_>>();
    for name in names {
        let declaration = resolution.algebras[&name].clone();
        let algebra = lower_algebra(&declaration)?;
        resolution.lowered_algebras.insert(name, algebra);
    }
    Ok(())
}

fn lower_algebra(
    declaration: &crate::resolve::GradeAlgebraDecl,
) -> Result<std::sync::Arc<Algebra>> {
    let count = declaration.elements.len();
    // Exhaustive law checking is cubic and table storage is quadratic. Bound
    // both before allocating tables, rather than trusting source declarations.
    if count > 64 {
        return Err(Diagnostic::new(
            declaration.span,
            "a grade algebra supports at most 64 elements (exhaustive law-checking budget)",
        ));
    }
    if count == 0 {
        return Err(Diagnostic::new(
            declaration.span,
            format!("grade algebra '{}' has no elements", declaration.name),
        ));
    }
    let mut index = BTreeMap::new();
    for (position, element) in declaration.elements.iter().enumerate() {
        index.insert(element.clone(), position);
    }
    let lookup = |name: &str| {
        index.get(name).copied().ok_or_else(|| {
            Diagnostic::new(
                declaration.span,
                format!(
                    "grade algebra '{}' names unknown element '{name}'",
                    declaration.name
                ),
            )
        })
    };
    let zero = lookup(&declaration.zero)?;
    let one = lookup(&declaration.one)?;
    if zero == one {
        return Err(Diagnostic::new(
            declaration.span,
            format!(
                "grade algebra '{}' has the same element for zero and one; erasure (@[0]) and an exact-observation contract (@[1]) would be indistinguishable",
                declaration.name
            ),
        ));
    }
    let add = algebra_table(declaration, &declaration.add, "add", &index, count)?;
    let mul = algebra_table(declaration, &declaration.mul, "mul", &index, count)?;
    let law = |detail: String| {
        Diagnostic::new(
            declaration.span,
            format!(
                "grade algebra '{}' violates its semiring laws: {detail}",
                declaration.name
            ),
        )
    };
    let element = |index: usize| declaration.elements[index].as_str();
    for element_index in 0..count {
        if add[zero][element_index] != element_index || add[element_index][zero] != element_index {
            return Err(law(format!(
                "'{}' is not an additive identity for '{}'",
                element(zero),
                element(element_index)
            )));
        }
        if mul[one][element_index] != element_index || mul[element_index][one] != element_index {
            return Err(law(format!(
                "'{}' is not a multiplicative identity for '{}'",
                element(one),
                element(element_index)
            )));
        }
        if mul[zero][element_index] != zero || mul[element_index][zero] != zero {
            return Err(law(format!(
                "zero does not annihilate '{}'",
                element(element_index)
            )));
        }
    }
    for left in 0..count {
        for right in 0..count {
            if add[left][right] != add[right][left] {
                return Err(law(format!(
                    "addition is not commutative for '{}' and '{}'",
                    element(left),
                    element(right)
                )));
            }
            if mul[left][right] != mul[right][left] {
                return Err(law(format!(
                    "multiplication is not commutative for '{}' and '{}'",
                    element(left),
                    element(right)
                )));
            }
        }
    }
    for a in 0..count {
        for b in 0..count {
            for c in 0..count {
                if add[add[a][b]][c] != add[a][add[b][c]] {
                    return Err(law("addition is not associative".to_owned()));
                }
                if mul[mul[a][b]][c] != mul[a][mul[b][c]] {
                    return Err(law("multiplication is not associative".to_owned()));
                }
                if mul[a][add[b][c]] != add[mul[a][b]][mul[a][c]] {
                    return Err(law(format!(
                        "multiplication does not distribute over addition for '{}', '{}', '{}'",
                        element(a),
                        element(b),
                        element(c)
                    )));
                }
            }
        }
    }
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };
    static NEXT_ID: AtomicU64 = AtomicU64::new(1);
    let mut candidate = NEXT_ID.load(Ordering::Relaxed);
    let id = loop {
        let next = candidate
            .checked_add(1)
            .expect("algebra identity space exhausted");
        match NEXT_ID.compare_exchange_weak(candidate, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => break candidate,
            Err(actual) => candidate = actual,
        }
    };
    let algebra = Arc::new(Algebra {
        id,
        name: declaration.name.clone(),
        elements: declaration.elements.clone(),
        add,
        mul,
        zero,
        one,
    });
    algebra_registry()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(id, Arc::downgrade(&algebra));
    Ok(algebra)
}

fn algebra_table(
    declaration: &crate::resolve::GradeAlgebraDecl,
    equations: &[crate::ast::GradeEquation],
    operation: &str,
    index: &BTreeMap<String, usize>,
    count: usize,
) -> Result<Vec<Vec<usize>>> {
    let mut table = vec![vec![usize::MAX; count]; count];
    for equation in equations {
        let Some(&left) = index.get(&equation.left) else {
            return Err(Diagnostic::new(
                equation.span,
                format!(
                    "grade algebra '{}' {operation} table names unknown element '{}'",
                    declaration.name, equation.left
                ),
            ));
        };
        let Some(&right) = index.get(&equation.right) else {
            return Err(Diagnostic::new(
                equation.span,
                format!(
                    "grade algebra '{}' {operation} table names unknown element '{}'",
                    declaration.name, equation.right
                ),
            ));
        };
        let Some(&result) = index.get(&equation.result) else {
            return Err(Diagnostic::new(
                equation.span,
                format!(
                    "grade algebra '{}' {operation} table names unknown element '{}'",
                    declaration.name, equation.result
                ),
            ));
        };
        if table[left][right] != usize::MAX {
            return Err(Diagnostic::new(
                equation.span,
                format!(
                    "grade algebra '{}' {operation} table repeats the pair '{}' and '{}'",
                    declaration.name, equation.left, equation.right
                ),
            ));
        }
        table[left][right] = result;
    }
    for (left, row) in table.iter().enumerate() {
        for (right, result) in row.iter().enumerate() {
            if *result == usize::MAX {
                return Err(Diagnostic::new(
                    declaration.span,
                    format!(
                        "grade algebra '{}' {operation} table is missing the pair '{}' and '{}'",
                        declaration.name, declaration.elements[left], declaration.elements[right]
                    ),
                ));
            }
        }
    }
    Ok(table)
}

/// Evaluate a grade annotation at compile time. No runtime grade values exist.
pub(crate) fn evaluate(
    resolution: &Resolution,
    variables: &BTreeMap<BindingId, Grade>,
    expr: &ast::Type,
) -> Result<Grade> {
    fn go(
        resolution: &Resolution,
        variables: &BTreeMap<BindingId, Grade>,
        expr: &ast::Type,
        budget: &mut usize,
    ) -> Result<Grade> {
        if *budget == 0 {
            return Err(Diagnostic::new(
                expr.span,
                "usage grade expression exceeds the 128-node evaluation budget",
            ));
        }
        *budget -= 1;
        match &expr.kind {
            ast::TypeKind::Integer(text) => text.parse::<u64>().map(Grade::Finite).map_err(|_| {
                Diagnostic::new(
                    expr.span,
                    "usage grades are nonnegative naturals that fit in 64 bits",
                )
            }),
            ast::TypeKind::Named { path, arguments } if arguments.is_empty() && path.len() == 2 => {
                let algebra = resolution.lowered_algebras.get(&path[0]).ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        format!(
                            "unknown grade algebra '{}'; declare it with 'algebra {} {{ ... }}'",
                            path[0], path[0]
                        ),
                    )
                })?;
                let element = algebra.element(&path[1]).ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        format!(
                            "grade algebra '{}' has no element '{}'; declare it in the algebra's elements list",
                            path[0], path[1]
                        ),
                    )
                })?;
                Ok(Grade::Element(AlgebraRef(algebra.id), element))
            }
            ast::TypeKind::Named { path, arguments } if arguments.is_empty() && path.len() == 1 => {
                let Some(id) = resolution.reference(expr.span) else {
                    if resolution.lowered_algebras.contains_key(&path[0]) {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "grade algebra '{}' requires an element, as in '{}::Element'",
                                path[0], path[0]
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        expr.span,
                        format!("unknown name '{}' in a usage grade", path[0]),
                    ));
                };
                let binding = &resolution.bindings[id];
                if binding.kind == crate::resolve::BindingKind::Builtin && binding.name == "many" {
                    return Ok(Grade::Many);
                }
                if binding.kind == crate::resolve::BindingKind::GradeAlgebra {
                    return Err(Diagnostic::new(
                        expr.span,
                        format!(
                            "grade algebra '{}' requires an element, as in '{}.Element'",
                            binding.name, binding.name
                        ),
                    ));
                }
                variables.get(&id).copied().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        format!(
                            "'{}' is not an abstract grade parameter in this specialization; declare it as <{}: Grade> or use 0, 1, many",
                            binding.name, binding.name
                        ),
                    )
                })
            }
            ast::TypeKind::Binary { op, left, right } => {
                use crate::lexer::Kind;
                let left = go(resolution, variables, left, budget)?;
                let right = go(resolution, variables, right, budget)?;
                let result = match op {
                    Kind::Plus => left.checked_add(right),
                    Kind::Star => left.checked_mul(right),
                    _ => None,
                };
                result.ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "usage grade arithmetic overflows the 64-bit finite bound (or uses an unsupported operator); use 'many' explicitly if an unbounded grade is intended",
                    )
                })
            }
            _ => Err(Diagnostic::new(
                expr.span,
                "usage grades are natural literals, 'many', grade variables, and '+'/'*' expressions",
            )),
        }
    }
    let mut budget = 128;
    go(resolution, variables, expr, &mut budget)
}

/// Check exact-use obligations for every function after ownership elaboration.
pub(crate) fn check(program: &Executable) -> Result<()> {
    for function in &program.functions {
        Checker::new(program, function).run()?;
    }
    Ok(())
}

#[derive(Clone)]
struct Frame {
    /// Counts at the loop head for every tracked outer binding.
    entry: BTreeMap<usize, Grade>,
    /// Number of active bindings at the loop head; later bindings are local
    /// to this loop body.
    active_start: usize,
    /// Counts observed at each `break`, for outer bindings. `while` must also
    /// join these with the zero-iteration head; `loop` continues with them.
    breaks: Option<BTreeMap<usize, Grade>>,
}

#[derive(Clone)]
struct Checker<'a> {
    program: &'a Executable,
    function: &'a Function,
    /// Bindings currently in scope, in declaration order.
    active: Vec<usize>,
    /// Use counts for finite exact grades. Unbounded/default bindings are not
    /// tracked because they have no exact obligation.
    counts: BTreeMap<usize, Grade>,
    loops: Vec<Frame>,
    /// A match guard is evaluated a path-dependent number of times.
    guard: bool,
    steps: usize,
}
/// A conservative per-function traversal budget. It bounds compiler work on
/// adversarial expression graphs; it is not a program-runtime budget.
const MAX_STEPS: usize = 1_000_000;

impl<'a> Checker<'a> {
    fn new(program: &'a Executable, function: &'a Function) -> Self {
        Self {
            program,
            function,
            active: Vec::new(),
            counts: BTreeMap::new(),
            loops: Vec::new(),
            guard: false,
            steps: 0,
        }
    }
    fn run(mut self) -> Result<()> {
        for slot in 0..self.function.parameters {
            self.activate(slot);
        }
        let function = self.function;
        let survives = self.block(&function.body, false, Grade::ONE)?;
        if survives {
            self.check_exact(&self.active.clone(), function.span, "the function returns")?;
        }
        Ok(())
    }
    fn tick(&mut self, span: Span) -> Result<()> {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            return Err(Diagnostic::new(
                span,
                "usage-grade checking exceeds the per-function 1,000,000-step budget",
            ));
        }
        Ok(())
    }
    fn moves(&self, ty: Type) -> bool {
        match ty {
            Type::Box(_)
            | Type::Bytes
            | Type::String
            | Type::Vec(_)
            | Type::Once(_)
            | Type::Task(_)
            | Type::DynObj(_) => true,
            Type::Enum(id) | Type::Variants(id, _) => {
                self.program.owned_enums.get(id).copied().unwrap_or(false)
                    || self.program.linear_enums.get(id).copied().unwrap_or(false)
            }
            Type::Union(id) => self.program.unions[id]
                .members
                .iter()
                .any(|member| self.moves(*member)),
            _ => false,
        }
    }
    /// A type-level `#[linear]` obligation (distinct from a `@[1]` binding grade).
    fn is_linear_type(&self, ty: Type) -> bool {
        match ty {
            Type::Box(pointee) | Type::Vec(pointee) => {
                self.is_linear_type(self.program.pointees[pointee])
            }
            Type::Enum(id) | Type::Variants(id, _) => {
                self.program.linear_enums.get(id).copied().unwrap_or(false)
            }
            Type::Union(id) => self.program.unions[id]
                .members
                .iter()
                .any(|member| self.is_linear_type(*member)),
            Type::Once(id) => self
                .program
                .function_types
                .get(id)
                .is_some_and(|signature| signature.linear),
            _ => false,
        }
    }
    /// Whether the value of `expr` is a move of a binding carrying a linear
    /// obligation, including through value-position blocks, `if`, `match`,
    /// constructors, and `Box.new`. A copyable `@[1]` result is a must-use
    /// obligation, not an owning move, so its result type must own storage.
    fn value_moves_linear(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.function.locals[*slot].linear,
            ExprKind::Call(
                Target::Function(index)
                | Target::ObjectFunction {
                    function: index, ..
                },
                _,
            ) => self.program.functions.get(*index).is_some_and(|function| {
                function.result_grade.is_some_and(Grade::is_one) && self.moves(function.result)
            }),
            ExprKind::Call(Target::DynCall { spec, .. }, _) => {
                self.program.dyn_calls.get(*spec).is_some_and(|spec| {
                    spec.result_grade.is_some_and(Grade::is_one) && self.moves(spec.result)
                })
            }
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => {
                    self.program
                        .function_types
                        .get(id)
                        .is_some_and(|signature| {
                            signature.result_grade.is_some_and(Grade::is_one)
                                && self.moves(signature.result)
                        })
                }
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
            ExprKind::FnValue { captures, .. } => captures
                .iter()
                .any(|capture| self.value_moves_linear(capture)),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .any(|v| self.value_moves_linear(v)),
            ExprKind::Try { value, .. } => self.value_moves_linear(value),
            ExprKind::BoxTake(value) if self.program.owns(expr.ty) => {
                self.value_moves_linear(value)
            }
            ExprKind::BoxNew(value) => self.value_moves_linear(value),
            ExprKind::BoxReuse { owner, payload } => {
                self.value_moves_linear(owner) || self.value_moves_linear(payload)
            }
            ExprKind::VecMap { vector, .. } => self.value_moves_linear(vector),
            ExprKind::Coerce { value, .. } => self.value_moves_linear(value),
            ExprKind::TaskSpawn { obligation, .. }
            | ExprKind::TaskScope { obligation, .. }
            | ExprKind::TaskJoin { obligation, .. } => *obligation,
            _ => false,
        }
    }
    fn block_value_moves_linear(&self, block: &Block) -> bool {
        block
            .tail
            .as_ref()
            .is_some_and(|tail| self.value_moves_linear(tail))
    }
    /// Whether the value is bound by `@[1]` (or a propagated linear binding),
    /// used to preserve the original "linear values cannot be dropped" rule.
    fn value_has_grade_one(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => {
                self.function.locals[*slot].linear || self.grade(*slot).is_some_and(Grade::is_one)
            }
            ExprKind::Call(
                Target::Function(index)
                | Target::ObjectFunction {
                    function: index, ..
                },
                _,
            ) => self
                .program
                .functions
                .get(*index)
                .is_some_and(|function| function.result_grade.is_some_and(Grade::is_one)),
            ExprKind::Call(Target::DynCall { spec, .. }, _) => self
                .program
                .dyn_calls
                .get(*spec)
                .is_some_and(|spec| spec.result_grade.is_some_and(Grade::is_one)),
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
                .is_some_and(|owner| self.value_has_grade_one(owner)),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => self
                    .program
                    .function_types
                    .get(id)
                    .is_some_and(|signature| signature.result_grade.is_some_and(Grade::is_one)),
                _ => false,
            },
            ExprKind::Block(block) => self.block_value_has_grade_one(block),
            ExprKind::If(_, yes, no) => {
                (yes.ty != Type::Never && self.block_value_has_grade_one(yes))
                    || (no.ty != Type::Never && self.block_value_has_grade_one(no))
            }
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|arm| arm.body.ty != Type::Never && self.value_has_grade_one(&arm.body)),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .any(|v| self.value_has_grade_one(v)),
            ExprKind::Try { value, .. } => self.value_has_grade_one(value),
            ExprKind::BoxReuse { owner, payload } => {
                self.value_has_grade_one(owner) || self.value_has_grade_one(payload)
            }
            ExprKind::VecMap { vector, .. } => self.value_has_grade_one(vector),
            ExprKind::Coerce { value, .. } => self.value_has_grade_one(value),
            ExprKind::TaskSpawn { obligation, .. }
            | ExprKind::TaskScope { obligation, .. }
            | ExprKind::TaskJoin { obligation, .. } => *obligation,
            // A constructor or Box.new consumes its inputs and produces a new
            // value; dropping that new value is a separate affine action.
            _ => false,
        }
    }
    fn block_value_has_grade_one(&self, block: &Block) -> bool {
        block
            .tail
            .as_ref()
            .is_some_and(|tail| self.value_has_grade_one(tail))
    }
    /// A linear value may only be handed to a parameter that will consume it
    /// (an explicit `@[1]` parameter or a `#[linear]` type), or to a terminal
    /// builtin such as `Box.take`. Value-carrying builtins are rejected because
    /// their ungraded result could be dropped.
    fn check_linear_parameter(
        &self,
        grade: Option<Grade>,
        ty: Option<Type>,
        span: Span,
    ) -> Result<()> {
        if grade.is_some_and(Grade::is_one) || ty.is_some_and(|ty| self.is_linear_type(ty)) {
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            "a value with a linear @[1] obligation is passed to an ungraded parameter that may drop it; mark the parameter @[1] or consume the value at the call site",
        ))
    }
    fn check_linear_argument(&self, target: Target, index: usize, span: Span) -> Result<()> {
        match target {
            Target::String(
                crate::executable::StringOp::IntoBytes
                | crate::executable::StringOp::FromUtf8 { .. },
            ) => Err(Diagnostic::new(
                span,
                "this string conversion would return a linear @[1] owner through an ungraded result; consume it through an explicitly graded parameter instead",
            )),
            Target::Function(function) | Target::ObjectFunction { function, .. } => {
                let Some(function) = self.program.functions.get(function) else {
                    return Ok(());
                };
                self.check_linear_parameter(
                    function.parameter_grades.get(index).copied().flatten(),
                    function.locals.get(index).map(|local| local.ty),
                    span,
                )
            }
            Target::Vec(VecOp::Push | VecOp::Set, _) => Err(Diagnostic::new(
                span,
                "this vector operation would store a linear @[1] value in an ungraded vector that could be dropped; consume it first",
            )),
            Target::Bytes(BytesOp::Push | BytesOp::PushReserved | BytesOp::Clear) => {
                Err(Diagnostic::new(
                    span,
                    "this byte-buffer operation would store or return a linear @[1] value in an ungraded buffer; consume it first",
                ))
            }
            _ => Ok(()),
        }
    }
    fn grade(&self, slot: usize) -> Option<Grade> {
        self.function.locals[slot].grade
    }
    fn is_tracked(&self, slot: usize) -> bool {
        matches!(
            self.grade(slot),
            Some(Grade::Finite(_) | Grade::Element(..))
        )
    }
    fn activate(&mut self, slot: usize) {
        self.active.push(slot);
        if self.is_tracked(slot) {
            let zero = match self.grade(slot) {
                Some(Grade::Element(algebra, _)) => Grade::algebra_zero(algebra),
                _ => Grade::ZERO,
            };
            self.counts.insert(slot, zero);
        }
    }
    fn deactivate(&mut self, slot: usize) {
        if let Some(index) = self.active.iter().position(|s| *s == slot) {
            self.active.remove(index);
        }
        self.counts.remove(&slot);
    }
    /// Record `amount` uses of `slot`. `amount` is already the full multiplicity
    /// for this occurrence. Consuming uses pass `Grade::ONE`.
    fn record(&mut self, slot: usize, amount: Grade, span: Span) -> Result<()> {
        if amount.is_zero() || !self.is_tracked(slot) {
            return Ok(());
        }
        if self.guard {
            return Err(self.grade_error(
                slot,
                span,
                "cannot be observed in a match guard",
                "a guard may be evaluated a path-dependent number of times, so exact usage cannot be established",
            ));
        }
        let current = self.counts.get(&slot).copied().unwrap_or(Grade::ZERO);
        self.counts.insert(slot, current.saturating_add(amount));
        Ok(())
    }
    fn grade_error(&self, slot: usize, span: Span, action: &str, detail: &str) -> Diagnostic {
        let grade = self.grade(slot).unwrap_or(Grade::ZERO);
        Diagnostic::new(
            span,
            format!("a value graded @[{grade}] {action}; {detail}"),
        )
        .with_note(
            self.function.locals[slot].span,
            format!("value graded @[{grade}] bound here"),
        )
    }
    fn check_exact(&self, slots: &[usize], span: Span, reason: &str) -> Result<()> {
        for slot in slots {
            let Some(wanted) = self.grade(*slot) else {
                continue;
            };
            if !matches!(wanted, Grade::Finite(_) | Grade::Element(..)) {
                continue;
            }
            let seen = self.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if seen != wanted {
                let seen_text = seen.to_string();
                let detail = if wanted.is_zero() {
                    format!(
                        "the value is used {seen_text} time(s) on this path; grade @[{wanted}] forbids runtime observation"
                    )
                } else {
                    format!(
                        "the value is used {seen_text} time(s) on this path; the annotation requires exactly {wanted}"
                    )
                };
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is not used consistently before {reason}"),
                    &detail,
                ));
            }
        }
        Ok(())
    }
    /// A back-edge or `continue`: the next iteration starts from the loop head.
    /// Outer exact grades must be restored; loop-local bindings must finish
    /// their per-iteration obligation.
    fn check_iteration(&self, span: Span, what: &str) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        for (slot, entry) in &frame.entry {
            let seen = self.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if seen != *entry {
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used an unknown number of times by the loop before {what}"),
                    "the loop may run zero, one, or many iterations; use @[many], use the value outside the loop, or reassign it to restore the loop-head use count on every path",
                ));
            }
        }
        self.check_loop_locals(span, what)
    }
    /// Bindings declared inside the loop body must satisfy their exact grade on
    /// every exit path, including `break` and `continue`.
    fn check_loop_locals(&self, span: Span, what: &str) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        for slot in &self.active[frame.active_start..] {
            self.check_exact(
                &[*slot],
                span,
                &format!("the end of this loop iteration ({what})"),
            )?;
        }
        Ok(())
    }
    /// Record the outer counts of a `break`. Different break paths must agree.
    fn note_break(&mut self, span: Span) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        let slots: Vec<usize> = frame.entry.keys().copied().collect();
        let current: BTreeMap<usize, Grade> = slots
            .iter()
            .map(|slot| (*slot, self.counts.get(slot).copied().unwrap_or(Grade::ZERO)))
            .collect();
        let frame = self.loops.last_mut().unwrap();
        let mut mismatch = None;
        match &mut frame.breaks {
            Some(previous) => {
                for (slot, count) in current {
                    if previous.get(&slot).copied().unwrap_or(Grade::ZERO) != count {
                        mismatch = Some(slot);
                        break;
                    }
                }
            }
            None => frame.breaks = Some(current),
        }
        if let Some(slot) = mismatch {
            let grade = self.grade(slot).unwrap_or(Grade::ZERO);
            return Err(self.grade_error(
                slot,
                span,
                "is used a different number of times on different break paths",
                &format!("exact grade @[{grade}] must match on every path that leaves the loop"),
            ));
        }
        Ok(())
    }
    /// Merge break records from a branch clone. Break paths diverge, but their
    /// counts still determine the surrounding loop's post-state.
    fn merge_breaks(&mut self, other: &Self, span: Span) -> Result<()> {
        let depth = self.loops.len().min(other.loops.len());
        let mut mismatch = None;
        for index in 0..depth {
            let Some(other_breaks) = other.loops[index].breaks.as_ref() else {
                continue;
            };
            let frame = &mut self.loops[index];
            match &mut frame.breaks {
                Some(previous) => {
                    for (slot, count) in other_breaks {
                        if previous.get(slot).copied().unwrap_or(Grade::ZERO) != *count {
                            mismatch = Some(*slot);
                            break;
                        }
                    }
                }
                None => frame.breaks = Some(other_breaks.clone()),
            }
            if mismatch.is_some() {
                break;
            }
        }
        if let Some(slot) = mismatch {
            let grade = self.grade(slot).unwrap_or(Grade::ZERO);
            return Err(self.grade_error(
                slot,
                span,
                "is used a different number of times on different break paths",
                &format!("exact grade @[{grade}] must match on every path that leaves the loop"),
            ));
        }
        Ok(())
    }
    fn join(&mut self, other: &Self, span: Span, what: &str) -> Result<()> {
        for (slot, left) in &self.counts {
            let right = other.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if *left != right {
                let grade = self.grade(*slot).unwrap_or(Grade::ZERO);
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used a different number of times on different paths in {what}"),
                    &format!(
                        "one path uses it {} time(s) and the other {} time(s); exact grade @[{grade}] must match on every normally surviving path",
                        left, right
                    ),
                ));
            }
        }
        for slot in other.counts.keys() {
            if !self.counts.contains_key(slot) {
                let grade = self.grade(*slot).unwrap_or(Grade::ZERO);
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used on only one path in {what}"),
                    &format!(
                        "exact grade @[{grade}] must be satisfied on every normally surviving path"
                    ),
                ));
            }
        }
        Ok(())
    }
    fn block(&mut self, block: &Block, loop_body: bool, multiplier: Grade) -> Result<bool> {
        self.tick(block_span(block))?;
        let active_start = self.active.len();
        let mut survives = true;
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    survives = self.expr(value, multiplier)?;
                    if !survives {
                        break;
                    }
                    self.activate(*slot);
                }
                Statement::Expr(expr) => {
                    survives = self.expr(expr, multiplier)?;
                    if !survives {
                        break;
                    }
                }
            }
        }
        if survives && let Some(tail) = &block.tail {
            survives = self.expr(tail, multiplier)?;
        }
        if survives && loop_body {
            self.check_iteration(block_span(block), "the loop falls through")?;
        }
        let bound = self.active[active_start..].to_vec();
        if survives {
            self.check_exact(&bound, block_span(block), "the end of its lexical scope")?;
        }
        for slot in bound {
            self.deactivate(slot);
        }
        Ok(survives)
    }
    fn expr(&mut self, expr: &Expr, multiplier: Grade) -> Result<bool> {
        self.tick(expr.span)?;
        match &expr.kind {
            ExprKind::Constant(_)
            | ExprKind::BytesLiteral(_)
            | ExprKind::Erased(_)
            | ExprKind::DynArrayNew { .. } => {}
            ExprKind::DynArrayPush { array, value, .. } => {
                if !self.expr(array, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                if !self.expr(array, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(index, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::DynArrayPop { array, .. } => {
                if !self.expr(array, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::DynArrayEqual { left, right, .. } => {
                if !self.expr(left, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(right, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                if !self.expr(handler, Grade::ONE)? {
                    return Ok(false);
                }
                self.block(body, false, multiplier)?;
            }
            ExprKind::DynamicPerform {
                payload, resume, ..
            } => {
                if !self.expr(payload, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(resume, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::BorrowPlace(value) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::PlaceIndex { base, index } => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(index, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::Local(slot) => {
                let amount = if self.moves(self.function.locals[*slot].ty) {
                    Grade::ONE
                } else {
                    multiplier
                };
                self.record(*slot, amount, expr.span)?;
            }
            ExprKind::Move(slot) => self.record(*slot, Grade::ONE, expr.span)?,
            ExprKind::Peek(slot) | ExprKind::Borrow(slot) => {
                let amount = if self.moves(self.function.locals[*slot].ty) {
                    Grade::ZERO
                } else {
                    multiplier
                };
                self.record(*slot, amount, expr.span)?;
            }
            ExprKind::Block(block) => {
                return self.block(block, false, multiplier);
            }
            ExprKind::Project(base, _)
            | ExprKind::BorrowField(base)
            | ExprKind::Unary(_, base)
            | ExprKind::BoxRead(base)
            | ExprKind::Coerce { value: base, .. } => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::BoxNew(base) | ExprKind::BoxTake(base) => {
                // The argument is consumed/evaluated once; duplicating the
                // resulting copyable value does not duplicate the consumption.
                if !self.expr(base, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. } => {
                // Both arguments are evaluated exactly once. The returned
                // owner inherits any binding-based obligation from either.
                if !self.expr(owner, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(payload, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            } => {
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::ArenaNew => {}
            ExprKind::ArenaNewWith { strategy } => {
                if !self.expr(strategy, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::ArenaAlloc { arena, value } => {
                if !self.expr(arena, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::ArenaTryAlloc { arena, value, .. } => {
                if !self.expr(arena, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::ArenaBoxRead(value) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::ArenaBoxTake(value) => {
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                if !self.expr(alloc, Grade::ONE)? || !self.expr(free, Grade::ONE)? {
                    return Ok(false);
                }
                if let Some(realloc) = realloc
                    && !self.expr(realloc, Grade::ONE)?
                {
                    return Ok(false);
                }
            }
            ExprKind::AllocBoxNew { allocator, value }
            | ExprKind::AllocBoxTryNew {
                allocator, value, ..
            } => {
                if !self.expr(allocator, Grade::ONE)? || !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::AllocBoxRead(value) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::AllocBoxTake(value) => {
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                ..
            } => {
                if !self.expr(allocator, Grade::ONE)? {
                    return Ok(false);
                }
                if let Some(capacity) = capacity
                    && !self.expr(capacity, Grade::ONE)?
                {
                    return Ok(false);
                }
            }
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                // The vector owner is consumed once and the copyable callable
                // values are observed once. The number of element calls is not
                // a usage count of the callback binding.
                if !self.expr(vector, Grade::ONE)? {
                    return Ok(false);
                }
                for callback in callbacks {
                    if !self.expr(callback, Grade::ONE)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Drop(base) => {
                if self.value_has_grade_one(base) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "linear values cannot be dropped; consume them by matching or passing them on",
                    ));
                }
                if !self.expr(base, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::Try { value, .. } => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                // The error path returns before the rest of the expression.
                self.check_exact(
                    &self.active.clone(),
                    expr.span,
                    "'?' takes its early error return",
                )?;
            }
            ExprKind::Return(value) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                self.check_exact(&self.active.clone(), expr.span, "this return")?;
                return Ok(false);
            }
            ExprKind::Assign(slot, value) => {
                if self.guard && self.is_tracked(*slot) {
                    return Err(self.grade_error(
                        *slot,
                        expr.span,
                        "cannot be replaced inside a match guard",
                        "a guard may fail after the replacement, so a later arm would observe a path-dependent value",
                    ));
                }
                // The replacement expression is evaluated once; only its
                // resulting value is subject to the surrounding demand.
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
                if self.is_tracked(*slot) {
                    self.check_exact(&[*slot], expr.span, "it is replaced by an assignment")?;
                    let zero = match self.grade(*slot) {
                        Some(Grade::Element(algebra, _)) => Grade::algebra_zero(algebra),
                        _ => Grade::ZERO,
                    };
                    self.counts.insert(*slot, zero);
                }
            }
            ExprKind::Binary(
                crate::lexer::Kind::AmpAmp | crate::lexer::Kind::PipePipe,
                left,
                right,
            ) => {
                if !self.expr(left, multiplier)? {
                    return Ok(false);
                }
                let mut skipped = self.clone();
                let right_survives = self.expr(right, multiplier)?;
                if right_survives {
                    self.join(&skipped, expr.span, "a short-circuit expression")?;
                    self.merge_breaks(&skipped, expr.span)?;
                } else {
                    // Only the left-value path that skips the right operand
                    // continues; the right path diverges. Its break records
                    // still matter to an enclosing loop.
                    skipped.merge_breaks(self, expr.span)?;
                    skipped.guard = self.guard;
                    *self = skipped;
                }
            }
            ExprKind::Binary(_, left, right) | ExprKind::StructEq { left, right, .. } => {
                if !self.expr(left, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(right, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::Call(target, arguments) => {
                for (index, argument) in arguments.iter().enumerate() {
                    if self.value_moves_linear(argument) {
                        self.check_linear_argument(*target, index, argument.span)?;
                    }
                    let demand = self.demand(*target, index);
                    let nested = multiplier.saturating_mul(demand);
                    if !self.expr(argument, nested)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                if !self.expr(callee, multiplier)? {
                    return Ok(false);
                }
                let id = match callee.ty {
                    Type::Fn(id) | Type::Once(id) => Some(id),
                    _ => None,
                };
                for (index, argument) in arguments.iter().enumerate() {
                    let grade = id
                        .and_then(|id| self.program.function_types.get(id))
                        .and_then(|signature| {
                            signature.parameter_grades.get(index).copied().flatten()
                        });
                    if self.value_moves_linear(argument) {
                        let ty = id
                            .and_then(|id| self.program.function_types.get(id))
                            .and_then(|signature| signature.parameters.get(index).copied());
                        self.check_linear_parameter(grade, ty, argument.span)?;
                    }
                    let demand = match grade {
                        None => Grade::ONE,
                        Some(grade) if grade.is_zero() => Grade::ONE,
                        Some(grade) => grade,
                    };
                    let nested = multiplier.saturating_mul(demand);
                    if !self.expr(argument, nested)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                if !self.expr(body, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => {}
            ExprKind::TaskCancel(task) => {
                if !self.expr(task, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::TaskJoin { task, .. } => {
                if !self.expr(task, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::FnValue { captures, .. } => {
                for capture in captures {
                    if !self.expr(capture, Grade::ONE)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Construct { fields, .. } => {
                for field in fields {
                    if !self.expr(field, multiplier)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::If(condition, yes, no) => {
                if !self.expr(condition, multiplier)? {
                    return Ok(false);
                }
                let mut baseline = self.clone();
                let yes_survives = baseline.block(yes, false, multiplier)?;
                let mut other = self.clone();
                let no_survives = other.block(no, false, multiplier)?;
                return match (yes_survives, no_survives) {
                    (true, true) => {
                        baseline.join(&other, expr.span, "an if/else")?;
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(true)
                    }
                    (true, false) => {
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(true)
                    }
                    (false, true) => {
                        other.merge_breaks(&baseline, expr.span)?;
                        *self = other;
                        Ok(true)
                    }
                    (false, false) => {
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(false)
                    }
                };
            }
            ExprKind::Match(value, arms) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                let baseline = self.clone();
                let mut joined: Option<Self> = None;
                let mut break_records = baseline.clone();
                for arm in arms {
                    let mut arm_state = baseline.clone();
                    let mut binding_set = std::collections::BTreeSet::new();
                    crate::ownership::pattern_bindings(&arm.pattern, &mut binding_set);
                    let bindings: Vec<usize> = binding_set.into_iter().collect();
                    for slot in &bindings {
                        arm_state.activate(*slot);
                    }
                    if let Some(guard) = &arm.guard {
                        let old = arm_state.guard;
                        arm_state.guard = true;
                        let survives = arm_state.expr(guard, multiplier)?;
                        arm_state.guard = old;
                        if !survives {
                            break_records.merge_breaks(&arm_state, arm.body.span)?;
                            continue;
                        }
                    }
                    let survives = arm_state.expr(&arm.body, multiplier)?;
                    let local: Vec<usize> = arm_state.active[baseline.active.len()..].to_vec();
                    if survives {
                        arm_state.check_exact(
                            &local,
                            arm.body.span,
                            "the end of this match arm",
                        )?;
                    }
                    for slot in local {
                        arm_state.deactivate(slot);
                    }
                    break_records.merge_breaks(&arm_state, arm.body.span)?;
                    if survives {
                        match &mut joined {
                            Some(state) => state.join(&arm_state, arm.body.span, "a match")?,
                            None => joined = Some(arm_state),
                        }
                    }
                }
                return match joined {
                    Some(mut state) => {
                        state.merge_breaks(&break_records, expr.span)?;
                        *self = state;
                        Ok(true)
                    }
                    None => {
                        let mut state = baseline;
                        state.merge_breaks(&break_records, expr.span)?;
                        *self = state;
                        Ok(false)
                    }
                };
            }
            ExprKind::While(condition, body) => {
                self.enter_loop();
                let entry = self.clone();
                let alive = self.expr(condition, multiplier)?;
                if !alive {
                    self.loops.pop();
                    return Ok(false);
                }
                // The condition runs before every iteration and once on the
                // zero-iteration path; exact outer grades must be restored.
                self.check_iteration(condition.span, "the while condition")?;
                self.block(body, true, multiplier)?;
                let frame = self.loops.pop().unwrap();
                // A `while` may execute zero times: the head counts and every
                // break path must agree.
                if let Some(breaks) = frame.breaks {
                    self.counts = entry.counts.clone();
                    self.active = entry.active.clone();
                    for (slot, count) in &entry.counts {
                        if breaks.get(slot).copied().unwrap_or(Grade::ZERO) != *count {
                            return Err(self.grade_error(
                                *slot,
                                expr.span,
                                "is used differently on the zero-iteration and break paths of a while loop",
                                "the loop may not run at all, so an exact grade cannot rely on a break-path use",
                            ));
                        }
                    }
                } else {
                    self.counts = entry.counts;
                    self.active = entry.active;
                }
            }
            ExprKind::Loop(body) => {
                self.enter_loop();
                let entry = self.clone();
                let body_alive = self.block(body, true, multiplier)?;
                let frame = self.loops.pop().unwrap();
                self.active = entry.active;
                if let Some(breaks) = frame.breaks {
                    self.counts = breaks;
                } else {
                    self.counts = entry.counts;
                    if !body_alive || expr.ty == Type::Never {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Break(value, _) => {
                if let Some(value) = value
                    && !self.expr(value, multiplier)?
                {
                    return Ok(false);
                }
                self.check_loop_locals(expr.span, "'break'")?;
                self.note_break(expr.span)?;
                return Ok(false);
            }
            ExprKind::Continue(_) => {
                self.check_iteration(expr.span, "'continue'")?;
                return Ok(false);
            }
            ExprKind::BytesAt(bytes, index) => {
                if !self.expr(bytes, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(index, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
                if let Some(start) = start
                    && !self.expr(start, multiplier)?
                {
                    return Ok(false);
                }
                if let Some(end) = end
                    && !self.expr(end, multiplier)?
                {
                    return Ok(false);
                }
            }
            ExprKind::RefRead(base) => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::RefAssign(reference, _, value)
            | ExprKind::RefWrite(reference, value)
            | ExprKind::DerefWrite(reference, value)
            | ExprKind::BoxWrite(reference, value) => {
                if !self.expr(reference, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
        }
        Ok(expr.ty != Type::Never)
    }
    fn enter_loop(&mut self) {
        self.loops.push(Frame {
            entry: self.counts.clone(),
            active_start: self.active.len(),
            breaks: None,
        });
    }
    /// The multiplicity a callee places on runtime argument `index`.
    ///
    /// An unannotated parameter uses its argument once. A `@[0]` parameter
    /// still evaluates its argument (the language is strict), so it counts as
    /// one evaluation; only `@[n]` and `@[many]` duplicate the resulting value.
    fn demand(&self, target: Target, index: usize) -> Grade {
        match target {
            Target::Function(function) | Target::ObjectFunction { function, .. } => self
                .program
                .functions
                .get(function)
                .and_then(|f| f.parameter_grades.get(index))
                .map_or(Grade::ONE, |grade| match grade {
                    None => Grade::ONE,
                    Some(grade) if grade.is_zero() => Grade::ONE,
                    Some(grade) => *grade,
                }),
            Target::DynCall { spec, .. } => self
                .program
                .dyn_calls
                .get(spec)
                .and_then(|spec| spec.parameter_grades.get(index.saturating_sub(1)))
                .copied()
                .flatten()
                .map_or(
                    Grade::ONE,
                    |grade| {
                        if grade.is_zero() { Grade::ONE } else { grade }
                    },
                ),
            Target::UnionBorrowCall { spec, .. } => self
                .program
                .union_calls
                .get(spec)
                .and_then(|spec| spec.parameter_grades.get(index.saturating_sub(1)))
                .copied()
                .flatten()
                .map_or(
                    Grade::ONE,
                    |grade| {
                        if grade.is_zero() { Grade::ONE } else { grade }
                    },
                ),
            _ => Grade::ONE,
        }
    }
}
fn block_span(block: &Block) -> Span {
    block
        .tail
        .as_ref()
        .map(|tail| tail.span)
        .or_else(|| {
            block.statements.last().map(|statement| match statement {
                Statement::Let(_, expr) | Statement::Expr(expr) => expr.span,
            })
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::Grade;

    fn n(value: u64) -> Grade {
        Grade::Finite(value)
    }

    #[test]
    fn grade_semiring_has_expected_laws() {
        assert_eq!(n(0).checked_add(n(3)), Some(n(3)));
        assert_eq!(n(2).checked_add(n(3)), Some(n(5)));
        assert_eq!(Grade::Many.checked_add(n(2)), Some(Grade::Many));
        assert_eq!(n(0).checked_mul(Grade::Many), Some(n(0)));
        assert_eq!(n(1).checked_mul(n(7)), Some(n(7)));
        assert_eq!(n(2).checked_mul(n(3)), Some(n(6)));
        assert_eq!(n(2).checked_mul(Grade::Many), Some(Grade::Many));
        assert_eq!(Grade::Many.checked_mul(Grade::Many), Some(Grade::Many));
        assert_eq!(n(u64::MAX).checked_add(n(1)), None);
        assert_eq!(n(u64::MAX).checked_mul(n(2)), None);
        assert_eq!(Grade::Many.saturating_add(n(u64::MAX)), Grade::Many);
        assert_eq!(n(0).saturating_mul(Grade::Many), n(0));
    }

    #[test]
    fn grade_display_is_stable() {
        assert_eq!(n(0).to_string(), "0");
        assert_eq!(n(42).to_string(), "42");
        assert_eq!(Grade::Many.to_string(), "many");
    }
}

#[cfg(test)]
mod algebra_ownership_tests {
    use super::*;

    #[test]
    fn invalid_internal_identity_does_not_poison_registry_cleanup() {
        // Identity zero is reserved and can never be allocated from source.
        assert!(std::panic::catch_unwind(|| AlgebraRef(0).get()).is_err());
        assert!(!algebra_registry().is_poisoned());
    }

    #[test]
    fn oversized_algebras_are_rejected_before_allocating_operation_tables() {
        let elements = (0..65)
            .map(|i| format!("E{i}"))
            .collect::<Vec<_>>()
            .join(",");
        let source = format!(
            "algebra Huge {{ elements {{ {elements} }} zero = E0; one = E1; add {{}} mul {{}} }}\nfn main() -> i64 ! {{}} {{ 0 }}"
        );
        let error = crate::executable::check(&source).unwrap_err();
        assert!(error.message.contains("at most 64 elements"), "{error:?}");
    }

    #[test]
    fn executable_owns_algebra_tables_and_releases_registry_entries() {
        // This tests the public source -> executable boundary: the temporary
        // resolution has already gone away when check returns. Weak probes do
        // not keep the tables alive and remain independent of parallel tests.
        for _ in 0..8 {
            let program =
                crate::executable::check(include_str!("../../../examples/grade-algebras.kush"))
                    .unwrap();
            assert!(!program._grade_algebras.is_empty());
            let table = &program._grade_algebras[0];
            let weak = std::sync::Arc::downgrade(table);
            let id = table.id;
            let one = Grade::Element(AlgebraRef(id), table.one);
            assert!(one.is_one());
            assert_eq!(one.checked_mul(Grade::ONE), Some(one));
            assert!(weak.upgrade().is_some());
            drop(program);
            assert!(
                weak.upgrade().is_none(),
                "program drop must release its tables"
            );
            assert!(!algebra_registry().lock().unwrap().contains_key(&id));
        }
    }
}
