//! Erased proof obligations for executable code.
//!
//! Propositions are conjunctions of integer comparisons between **linear
//! expressions** over runtime scalar terms (`x`, `x + c`, `c * x`,
//! `len(xs) + c`). Every comparison becomes a linear inequality
//! `sum coefficient * term <= bound`. Facts come from branch conditions,
//! guards, loop conditions, early exits, and erased parameters.
//!
//! Discharging an obligation first runs Fourier–Motzkin elimination over exact
//! rational coefficients. The rational certificate records the non-negative
//! multipliers of the hypotheses and of the integer negation of the goal.
//! [`verify`] checks the combination independently of the search that produced
//! it. If the hypotheses and the negation derive `0 <= negative`, the goal holds
//! for every *integer* assignment (all admitted terms are integer-valued).
//!
//! Soundness relies on: checked i64 arithmetic (a computed value is its
//! mathematical value), immutable or versioned locals (assignment bumps a
//! version so stale facts no longer match), and immutable borrows (a borrowed
//! buffer's length cannot change during a call).
//!
//! When the rational relaxation is feasible but the integer system is not,
//! a bounded integer fallback applies Chvátal–Gomory rounding cuts and an
//! integer branch-and-bound split. Both rules are recorded in the certificate
//! and re-checked by [`verify`]: a cut is a non-negative integer combination
//! of available constraints divided by the gcd of its coefficients, with the
//! bound rounded down; a branch proves both integer halves
//! `x <= t` and `x >= t + 1` of one variable.
//!
//! The fragment is deliberately bounded. The integer fallback is not a full
//! integer Presburger decision procedure: it explores a small number of cut
//! rounds and a shallow case split, and it never accepts an unverified
//! certificate. The rational search also has explicit row, pair, and
//! coefficient budgets; exceeding any budget means "not established", never a
//! guessed proof.
use crate::{
    Diagnostic, Span,
    executable::{BytesOp, Expr, ExprKind, SliceOp, Target, VecOp},
    lexer::Kind,
};
use std::collections::{BTreeMap, BTreeSet};

/// A symbolic integer-valued term. `Zero` is never stored as a map key; it is
/// kept as a variant so callers can refer to the constant term explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Term {
    Zero,
    /// An i64 local at a version.
    Var(usize, u32),
    /// The length of the Bytes/Vec owned by (or borrowed through) a local.
    Len(usize, u32),
    /// A scalar reached from a root value through field, tag and payload
    /// steps (ENSURES); the path is interned, see [`path_of`].
    Path(u32),
}

/// The root of a [`Term::Path`]: a local at a version, or the result of one
/// call occurrence (a fresh identity per checked call).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Root {
    Var(usize, u32),
    Value(u32),
}

/// One step of a [`Term::Path`]. Offsets are word offsets in the record or
/// in the variant's payload, as in the IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Step {
    Field(u32),
    /// The variant index of an enum value.
    Tag,
    /// Payload word offset of the given variant.
    Payload(u32, u32),
}

type PathKey = (Root, Vec<Step>);
type PathTable = std::sync::Mutex<(Vec<PathKey>, std::collections::HashMap<PathKey, u32>)>;

fn path_table() -> &'static PathTable {
    static TABLE: std::sync::OnceLock<PathTable> = std::sync::OnceLock::new();
    TABLE.get_or_init(Default::default)
}

/// The term for a scalar at `root` followed by `steps`. A bare local is its
/// ordinary variable term.
pub(crate) fn path_term(root: Root, steps: &[Step]) -> Term {
    if steps.is_empty()
        && let Root::Var(slot, version) = root
    {
        return Term::Var(slot, version);
    }
    let mut table = path_table()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let key = (root, steps.to_vec());
    if let Some(id) = table.1.get(&key) {
        return Term::Path(*id);
    }
    let id = u32::try_from(table.0.len()).expect("path table overflow");
    table.0.push(key.clone());
    table.1.insert(key, id);
    Term::Path(id)
}

/// The root and steps of an interned path.
pub(crate) fn path_of(id: u32) -> PathKey {
    path_table()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .0[id as usize]
        .clone()
}

/// A fresh identity for one call's result.
pub(crate) fn fresh_value() -> u32 {
    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// One integer linear expression: `sum coefficients[term] * term + constant`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Linear {
    pub coefficients: BTreeMap<Term, i128>,
    pub constant: i128,
}

impl Linear {
    pub(crate) fn constant(value: i128) -> Self {
        Linear {
            coefficients: BTreeMap::new(),
            constant: value,
        }
    }
    pub(crate) fn variable(term: Term) -> Self {
        let mut coefficients = BTreeMap::new();
        if term != Term::Zero {
            coefficients.insert(term, 1);
        }
        Linear {
            coefficients,
            constant: 0,
        }
    }
    pub(crate) fn is_constant(&self) -> bool {
        self.coefficients.is_empty()
    }
    pub(crate) fn scale(mut self, factor: i128) -> Option<Self> {
        if factor == 0 {
            return Some(Linear::default());
        }
        self.constant = self.constant.checked_mul(factor)?;
        for coefficient in self.coefficients.values_mut() {
            *coefficient = coefficient.checked_mul(factor)?;
        }
        Some(self)
    }
    pub(crate) fn add_scaled(mut self, other: &Linear, factor: i128) -> Option<Self> {
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(factor)?)?;
        for (term, coefficient) in &other.coefficients {
            let value = coefficient.checked_mul(factor)?;
            let entry = self.coefficients.entry(*term).or_insert(0);
            *entry = entry.checked_add(value)?;
            if *entry == 0 {
                self.coefficients.remove(term);
            }
        }
        Some(self)
    }
    pub(crate) fn add(self, other: &Linear) -> Option<Self> {
        self.add_scaled(other, 1)
    }
    pub(crate) fn sub(self, other: &Linear) -> Option<Self> {
        self.add_scaled(other, -1)
    }
    pub(crate) fn negate(self) -> Option<Self> {
        self.scale(-1)
    }
}

/// `sum coefficients[term] * term <= bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Constraint {
    pub coefficients: BTreeMap<Term, i128>,
    pub bound: i128,
}

/// A reference to one runtime parameter or length term inside a proposition
/// before it is specialized with actual argument expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ParamTerm {
    Zero,
    Param(usize),
    Len(usize),
}

/// A linear expression over [`ParamTerm`]s.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ParamLinear {
    pub coefficients: BTreeMap<ParamTerm, i128>,
    pub constant: i128,
}

impl ParamLinear {
    pub(crate) fn constant(value: i128) -> Self {
        ParamLinear {
            coefficients: BTreeMap::new(),
            constant: value,
        }
    }
    pub(crate) fn variable(term: ParamTerm, coefficient: i128) -> Self {
        let mut coefficients = BTreeMap::new();
        if term != ParamTerm::Zero && coefficient != 0 {
            coefficients.insert(term, coefficient);
        }
        ParamLinear {
            coefficients,
            constant: 0,
        }
    }
    pub(crate) fn scale(mut self, factor: i128) -> Option<Self> {
        if factor == 0 {
            return Some(ParamLinear::default());
        }
        self.constant = self.constant.checked_mul(factor)?;
        for coefficient in self.coefficients.values_mut() {
            *coefficient = coefficient.checked_mul(factor)?;
        }
        Some(self)
    }
    fn add_scaled(mut self, other: &ParamLinear, factor: i128) -> Option<Self> {
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(factor)?)?;
        for (term, coefficient) in &other.coefficients {
            let value = coefficient.checked_mul(factor)?;
            let entry = self.coefficients.entry(*term).or_insert(0);
            *entry = entry.checked_add(value)?;
            if *entry == 0 {
                self.coefficients.remove(term);
            }
        }
        Some(self)
    }
    pub(crate) fn add(self, other: &ParamLinear) -> Option<Self> {
        self.add_scaled(other, 1)
    }
    pub(crate) fn sub(self, other: &ParamLinear) -> Option<Self> {
        self.add_scaled(other, -1)
    }
    pub(crate) fn negate(self) -> Option<Self> {
        self.scale(-1)
    }
}

/// A comparison between symbolic linear expressions over a callee's parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proposition {
    /// Disjunctive normal form (PROVE-DISJ): each disjunct is a conjunction
    /// of atoms `left op right` (`op` may be `!=`).
    pub disjuncts: Vec<Vec<(ParamLinear, Kind, ParamLinear)>>,
    /// Parameters used as bare `Bool` atoms (`b`, `!b`); they must have type
    /// `Bool` where the proposition is used.
    pub booleans: Vec<usize>,
    pub text: String,
}

/// A checked Farkas refutation. The non-negative numerators are interpreted
/// over the positive `denominator`; the weighted constraints cancel exactly
/// and leave a negative constant bound.
#[derive(Debug, Clone)]
pub(crate) struct Farkas {
    pub steps: Vec<Constraint>,
    pub multipliers: Vec<i128>,
    pub denominator: i128,
}

/// A refutation of an integer linear system. Every step is checked in the
/// context established by the enclosing cuts and branches.
#[derive(Debug, Clone)]
pub(crate) enum Refutation {
    /// The goal is a non-negative constant and needs no hypotheses.
    Trivial,
    /// A non-negative rational combination of available constraints.
    Farkas(Farkas),
    /// A Chvátal–Gomory cut of the non-negative integer combination
    /// `sum multipliers[i] * steps[i]`. The combination's coefficients are
    /// divided by `divisor`, which must be their gcd, and its bound is rounded
    /// down (`div_euclid`).
    Cut {
        steps: Vec<Constraint>,
        multipliers: Vec<i128>,
        divisor: i128,
        result: Constraint,
        then: Box<Refutation>,
    },
    /// An integer case split on `variable`: the left context adds
    /// `variable <= threshold`, the right adds `variable >= threshold + 1`.
    Branch {
        variable: Term,
        threshold: i128,
        left: Box<Refutation>,
        right: Box<Refutation>,
    },
    /// A case split on an available disjunctive clause (PROVE-DISJ): one
    /// refutation per disjunct, each in the context extended by that
    /// disjunct's constraints. An empty clause is itself false.
    Cases {
        clause: Dnf,
        branches: Vec<Refutation>,
    },
}

/// A disjunction of conjunctions of constraints. `vec![vec![]]` is true and
/// `vec![]` is false.
pub(crate) type Dnf = Vec<Vec<Constraint>>;

/// Most disjuncts a hypothesis or goal may expand to; a larger formula is
/// not used as a hypothesis (sound: weaker) and not accepted as a goal.
const MAX_DNF: usize = 32;
/// Most case-split nodes per obligation.
const MAX_CASE_NODES: usize = 512;

/// `a && b` in disjunctive normal form.
pub(crate) fn dnf_and(a: &Dnf, b: &Dnf) -> Option<Dnf> {
    if a.len().checked_mul(b.len())? > MAX_DNF {
        return None;
    }
    let mut out = Vec::new();
    for left in a {
        for right in b {
            let mut both = left.clone();
            both.extend(right.iter().cloned());
            out.push(both);
        }
    }
    Some(out)
}

/// `a || b` in disjunctive normal form.
pub(crate) fn dnf_or(mut a: Dnf, b: Dnf) -> Option<Dnf> {
    a.extend(b);
    (a.len() <= MAX_DNF).then_some(a)
}

/// `l op r` exactly, as a formula: `!=` is two disjuncts. `None` when a
/// translation overflows, so a goal is never silently weakened.
pub(crate) fn compare_dnf(l: Linear, op: &Kind, r: Linear) -> Option<Dnf> {
    let exact = |l: Linear, op: Kind, r: Linear| {
        let mut out = Vec::new();
        compare(l, &op, r, &mut out);
        let wanted = if op == Kind::EqEq { 2 } else { 1 };
        (out.len() == wanted).then_some(out)
    };
    match op {
        Kind::Ne => Some(vec![
            exact(l.clone(), Kind::Lt, r.clone())?,
            exact(l, Kind::Gt, r)?,
        ]),
        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq => {
            Some(vec![exact(l, op.clone(), r)?])
        }
        _ => None,
    }
}

/// The negation of a goal formula, as clauses that must all hold: for each
/// disjunct `c1 && c2 && ..`, the clause `!c1 || !c2 || ..` (integer
/// negations). The verifier recomputes this itself.
fn negated_goal(goal: &Dnf) -> Option<Vec<Dnf>> {
    goal.iter()
        .map(|disjunct| {
            disjunct
                .iter()
                .map(|constraint| Some(vec![negation(constraint)?]))
                .collect::<Option<Dnf>>()
        })
        .collect()
}

/// A discharged obligation and the facts that justify it.
#[derive(Debug, Clone)]
pub struct Certificate {
    pub span: Span,
    pub obligation: String,
    pub(crate) goal: Constraint,
    pub(crate) proof: Refutation,
    pub(crate) hypotheses: Vec<Constraint>,
    /// Disjunctive hypotheses available to `Cases` steps.
    pub(crate) clauses: Vec<Dnf>,
    /// A formula goal (PROVE-DISJ). When set, `goal` is unused and the
    /// verifier adds the negation of this formula as clauses itself.
    pub(crate) goal_formula: Option<Dnf>,
}

impl Certificate {
    /// Independently check this certificate without the search that produced
    /// it. Every Farkas combination, cut rounding, and branch split is
    /// re-verified against the recorded hypotheses and the integer negation of
    /// the goal.
    pub fn verify(&self) -> bool {
        verify(self)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Facts {
    known: Vec<Constraint>,
    versions: BTreeMap<usize, u32>,
    /// Locals whose address was taken by `&mut`. A write through the
    /// reference is not an assignment the checker can see, so such a local
    /// is never a linear term from that point on.
    opaque: BTreeSet<usize>,
    /// Established disequalities `expr != 0` (from `a != b` conditions). They
    /// are not convex, so they never enter the Fourier–Motzkin system; they
    /// only answer [`Facts::prove_distinct`].
    distinct: Vec<Linear>,
    /// Index places of the current body: `(identity, root binding, index)`.
    /// They are records, not facts, so `reset` keeps them.
    index_places: Vec<(usize, usize, Linear)>,
    /// Value range of each local used as a `Bool` (0..=1) or fixed-width
    /// integer term (PROVE-SCALARS). Recorded when the term is first built,
    /// added as implicit hypotheses. `i64` locals need none.
    ranges: std::cell::RefCell<BTreeMap<usize, (i128, i128)>>,
    /// Disjunctive facts (PROVE-DISJ), e.g. from `if a || b` or `a != b`.
    clauses: Vec<Dnf>,
    /// Locals recorded as `i64` (their range is not added to every proof,
    /// only to range proofs; a local not recorded here gets no bound).
    wide: std::cell::RefCell<BTreeSet<usize>>,
    /// Ranges of path terms (ENSURES): a `Bool` result, a tag, a field.
    term_ranges: std::cell::RefCell<BTreeMap<Term, (i128, i128)>>,
    /// A local that denotes a symbolic value: a call result or an enum
    /// payload bound by a match (ENSURES). Cleared by assignment.
    aliases: BTreeMap<usize, (Root, Vec<Step>)>,
    /// Call occurrences with postconditions, by call span, and the identity
    /// of their results.
    call_values: BTreeMap<(usize, usize), u32>,
}

/// The mathematical range of a scalar type admitted as a linear term, or
/// `None` for types that are not integer-valued.
pub(crate) fn scalar_range(ty: crate::executable::Type) -> Option<(i128, i128)> {
    use crate::executable::Type;
    match ty {
        Type::I64 => Some((i128::from(i64::MIN), i128::from(i64::MAX))),
        Type::Bool => Some((0, 1)),
        Type::Int(kind) => Some((kind.min(), kind.max())),
        _ => None,
    }
}

/// The value of a constant of scalar type `ty`: unsigned kinds are stored
/// zero-extended, and `u64` keeps its raw bit pattern in the word.
fn constant_value(n: i64, ty: crate::executable::Type) -> i128 {
    match ty {
        crate::executable::Type::Int(kind) if !kind.signed() => i128::from(n as u64),
        _ => i128::from(n),
    }
}

/// A restore point for [`Facts::reset`]: the lengths of the inequality and
/// disequality lists when it was taken.
#[derive(Debug, Clone, Copy)]
pub(crate) struct FactsMark(usize, usize, usize);

/// Bounds for the Fourier–Motzkin search. These are work limits, not a claim of
/// completeness: a system beyond them is reported as not established.
const MAX_FM_ROWS: usize = 4096;
const MAX_FM_PAIRS: usize = 200_000;
const MAX_FM_TERMS: usize = 64;

/// Bounds for the integer fallback. They bound the worst-case work after the
/// rational search already failed; exhausting one means "not established".
const MAX_INTEGER_DEPTH: usize = 4;
const MAX_INTEGER_NODES: usize = 48;
const MAX_INTEGER_CUTS: usize = 8;
const MAX_INTEGER_CUT_ROUNDS: usize = 2;
const MAX_INTEGER_CUT_PAIRS: usize = 64;
const MAX_INTEGER_TERMS: usize = 16;
const MAX_INTEGER_CONSTRAINTS: usize = 128;
const MAX_INTEGER_BRANCH_ATTEMPTS: usize = 8;
const MAX_INTEGER_THRESHOLDS: usize = 6;

#[derive(Debug, Clone, Copy)]
struct IntegerBudget {
    nodes: usize,
    cuts: usize,
    cut_rounds: usize,
}

impl IntegerBudget {
    fn standard() -> Self {
        IntegerBudget {
            nodes: MAX_INTEGER_NODES,
            cuts: MAX_INTEGER_CUTS,
            cut_rounds: MAX_INTEGER_CUT_ROUNDS,
        }
    }
}

impl Facts {
    pub fn same_versions(&self, other: &Self) -> bool {
        self.versions == other.versions
    }
    /// Sibling branches start from identical versions. A join forgets facts
    /// about every value changed on either path.
    pub fn branch_join(base: &Self, left: &Self, right: &Self) -> Self {
        let mut result = base.clone();
        result.opaque.extend(left.opaque.iter().copied());
        result.opaque.extend(right.opaque.iter().copied());
        for slot in left.versions.keys().chain(right.versions.keys()) {
            let version = left.version(*slot).max(right.version(*slot));
            if version != base.version(*slot) {
                result.versions.insert(*slot, version + 1);
                // A value replaced on either path no longer has its alias.
                result.aliases.remove(slot);
            }
        }
        result
    }

    pub(crate) fn mark(&self) -> FactsMark {
        FactsMark(self.known.len(), self.distinct.len(), self.clauses.len())
    }
    pub(crate) fn reset(&mut self, mark: FactsMark) {
        self.known.truncate(mark.0);
        self.distinct.truncate(mark.1);
        self.clauses.truncate(mark.2);
    }
    /// Leave a region that ran only under a condition (the right operand of
    /// `&&` / `||`). Facts learnt since `inner` (such as a call's
    /// postconditions) hold only when it ran, so they are kept as
    /// `not_condition || facts`; the rest since `outer` is dropped. Facts
    /// that do not fit the case limit are dropped, which only weakens.
    pub(crate) fn reset_guarded(
        &mut self,
        outer: FactsMark,
        inner: FactsMark,
        not_condition: Option<Dnf>,
    ) {
        let learnt = (inner.0 <= self.known.len() && inner.2 <= self.clauses.len()).then(|| {
            let mut formula: Dnf = vec![self.known[inner.0..].to_vec()];
            for clause in &self.clauses[inner.2..] {
                formula = dnf_and(&formula, clause)?;
            }
            Some(formula)
        });
        self.reset(outer);
        if let (Some(Some(learnt)), Some(not_condition)) = (learnt, not_condition)
            && !(learnt.len() == 1 && learnt[0].is_empty())
            && !not_condition.iter().any(Vec::is_empty)
            && let Some(formula) = dnf_or(not_condition, learnt)
        {
            self.clauses.push(formula);
        }
    }
    pub fn version(&self, slot: usize) -> u32 {
        self.versions.get(&slot).copied().unwrap_or(0)
    }
    /// `&mut slot` was taken: forget every fact about the slot and never
    /// derive a new one, because later writes go through the reference.
    pub fn make_opaque(&mut self, slot: usize) {
        self.bump(slot);
        self.opaque.insert(slot);
    }
    /// Assignment invalidates every fact about the old value.
    pub fn bump(&mut self, slot: usize) {
        *self.versions.entry(slot).or_default() += 1;
        self.aliases.remove(&slot);
    }
    /// The symbolic root of a local: its alias or the local at its version.
    pub(crate) fn local_root(&self, slot: usize) -> (Root, Vec<Step>) {
        self.aliases
            .get(&slot)
            .cloned()
            .unwrap_or((Root::Var(slot, self.version(slot)), Vec::new()))
    }
    pub(crate) fn alias(&mut self, slot: usize, root: Root, steps: Vec<Step>) {
        if !self.opaque.contains(&slot) {
            self.aliases.insert(slot, (root, steps));
        }
    }
    /// Give the call at `span` a fresh result identity.
    pub(crate) fn register_call(&mut self, span: Span) -> u32 {
        let id = fresh_value();
        self.call_values.insert((span.start, span.end), id);
        id
    }
    pub(crate) fn call_value(&self, span: Span) -> Option<u32> {
        self.call_values.get(&(span.start, span.end)).copied()
    }
    /// Record the value range of a path term.
    pub(crate) fn note_term(&self, term: Term, range: (i128, i128)) {
        self.term_ranges.borrow_mut().insert(term, range);
    }
    /// The symbolic root of an expression, when it denotes a whole value:
    /// a local (or its alias), a field of one, or a registered call.
    pub(crate) fn root_of(&self, expr: &Expr) -> Option<(Root, Vec<Step>)> {
        match &expr.kind {
            // A reference is not a value root: writes through it are not
            // assignments the facts see.
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot)
                if !self.opaque.contains(slot) && !expr.ty.is_ref() =>
            {
                Some(self.local_root(*slot))
            }
            ExprKind::Project(base, offset) => {
                let (root, mut steps) = self.root_of(base)?;
                steps.push(Step::Field(u32::try_from(*offset).ok()?));
                Some((root, steps))
            }
            ExprKind::Call(..) => self
                .call_value(expr.span)
                .map(|id| (Root::Value(id), Vec::new())),
            _ => None,
        }
    }
    pub fn add(&mut self, constraints: impl IntoIterator<Item = Constraint>) {
        self.known.extend(constraints);
    }
    /// Assume `condition` evaluates to `truth`: add its inequalities and its
    /// disequalities.
    pub fn assume(&mut self, condition: &Expr, truth: bool) {
        let facts = self.condition(condition, truth);
        self.known.extend(facts);
        // A disjunctive condition is kept as one clause for case splits.
        if fact_safe(condition)
            && let Some(formula) = self.formula(condition, truth)
            && formula.len() != 1
        {
            self.clauses.push(formula);
        }
        if fact_safe(condition) {
            let mut distinct = Vec::new();
            self.collect_distinct(condition, truth, &mut distinct);
            self.distinct.extend(distinct);
        }
    }
    fn collect_distinct(&self, expr: &Expr, truth: bool, out: &mut Vec<Linear>) {
        match &expr.kind {
            ExprKind::Unary(Kind::Bang, inner) => self.collect_distinct(inner, !truth, out),
            ExprKind::Binary(Kind::AmpAmp, l, r) if truth => {
                self.collect_distinct(l, true, out);
                self.collect_distinct(r, true, out);
            }
            ExprKind::Binary(Kind::PipePipe, l, r) if !truth => {
                self.collect_distinct(l, false, out);
                self.collect_distinct(r, false, out);
            }
            ExprKind::Binary(op @ (Kind::Ne | Kind::EqEq), l, r) if (*op == Kind::Ne) == truth => {
                if let (Some(l), Some(r)) = (self.linear(l), self.linear(r))
                    && let Some(difference) = l.sub(&r)
                {
                    out.push(difference);
                }
            }
            ExprKind::Block(block) if block.statements.is_empty() => {
                if let Some(tail) = &block.tail {
                    self.collect_distinct(tail, truth, out);
                }
            }
            _ => {}
        }
    }
    /// Remember an index place so later places of the same root can be
    /// related to it.
    pub(crate) fn record_index_place(&mut self, id: usize, root: usize, index: Linear) {
        self.index_places.push((id, root, index));
    }
    /// Identities of earlier index places of `root` whose index provably
    /// differs from `index` under the current facts. Only the most recent
    /// places are tried, which bounds the proof work per place.
    pub(crate) fn distinct_index_places(&self, root: usize, index: &Linear) -> Vec<usize> {
        const MAX_RELATED_PLACES: usize = 32;
        self.index_places
            .iter()
            .rev()
            .filter(|(_, other, _)| *other == root)
            .take(MAX_RELATED_PLACES)
            .filter(|(_, _, earlier)| self.prove_distinct(earlier, index))
            .map(|(id, _, _)| *id)
            .collect()
    }
    /// Whether `left != right` holds for every integer assignment satisfying
    /// the known facts: either one strict order is proved, or the difference
    /// is provably equal (up to sign) to an established nonzero difference.
    /// Never assumes; a budget overflow means "not established".
    pub(crate) fn prove_distinct(&self, left: &Linear, right: &Linear) -> bool {
        let Some(difference) = left.clone().sub(right) else {
            return false;
        };
        if difference.is_constant() {
            return difference.constant != 0;
        }
        // `difference <= bound` as a goal constraint.
        let at_most = |linear: &Linear, bound: i128| -> Option<Constraint> {
            Some(Constraint {
                coefficients: linear.coefficients.clone(),
                bound: bound.checked_sub(linear.constant)?,
            })
        };
        let proves =
            |goal: Option<Constraint>| goal.is_some_and(|goal| self.prove(&goal).is_some());
        if proves(at_most(&difference, -1))
            || difference
                .clone()
                .negate()
                .is_some_and(|negated| proves(at_most(&negated, -1)))
        {
            return true;
        }
        let zero = |linear: Option<Linear>| {
            linear.is_some_and(|linear| {
                if linear.is_constant() {
                    return linear.constant == 0;
                }
                proves(at_most(&linear, 0))
                    && linear
                        .clone()
                        .negate()
                        .is_some_and(|negated| proves(at_most(&negated, 0)))
            })
        };
        self.distinct
            .iter()
            .any(|known| zero(difference.clone().sub(known)) || zero(difference.clone().add(known)))
    }
    /// Facts implied by `condition` evaluating to `truth`.
    pub fn condition(&self, condition: &Expr, truth: bool) -> Vec<Constraint> {
        let mut out = Vec::new();
        if !fact_safe(condition) {
            return out;
        }
        self.collect(condition, truth, &mut out);
        out
    }
    fn collect(&self, expr: &Expr, truth: bool, out: &mut Vec<Constraint>) {
        match &expr.kind {
            ExprKind::Unary(Kind::Bang, inner) => self.collect(inner, !truth, out),
            ExprKind::Binary(Kind::AmpAmp, l, r) if truth => {
                self.collect(l, true, out);
                self.collect(r, true, out);
            }
            ExprKind::Binary(Kind::PipePipe, l, r) if !truth => {
                self.collect(l, false, out);
                self.collect(r, false, out);
            }
            ExprKind::Binary(op, l, r) => {
                if let (Some(l), Some(r)) = (self.linear(l), self.linear(r)) {
                    let op = if truth { Some(op.clone()) } else { negate(op) };
                    if let Some(op) = op {
                        compare(l, &op, r, out);
                    }
                }
            }
            ExprKind::Block(block) if block.statements.is_empty() => {
                if let Some(tail) = &block.tail {
                    self.collect(tail, truth, out);
                }
            }
            // A `Bool` term used as a condition: `b` is `b == 1`, `!b` is
            // `b == 0` (PROVE-SCALARS).
            _ if expr.ty == crate::executable::Type::Bool => {
                if let Some(term) = self.linear(expr) {
                    let one = Linear::constant(i128::from(truth));
                    compare(term, &Kind::EqEq, one, out);
                }
            }
            _ => {}
        }
    }
    /// Add a disjunctive hypothesis (a single disjunct is added as facts).
    pub(crate) fn add_formula(&mut self, formula: Dnf) {
        match formula.len() {
            1 => self.known.extend(formula.into_iter().next().unwrap()),
            _ => self.clauses.push(formula),
        }
    }
    /// The condition `expr == truth` as a formula, or `None` when its shape is
    /// unknown (then it says nothing). Unknown parts of a conjunction are
    /// dropped, which only weakens the hypothesis.
    pub(crate) fn formula(&self, expr: &Expr, truth: bool) -> Option<Dnf> {
        self.formula_with(expr, truth, true)
    }
    /// The condition exactly, or `None` if any part is unknown: for goals,
    /// where weakening would be unsound.
    pub(crate) fn formula_exact(&self, expr: &Expr, truth: bool) -> Option<Dnf> {
        self.formula_with(expr, truth, false)
    }
    fn formula_with(&self, expr: &Expr, truth: bool, lenient: bool) -> Option<Dnf> {
        let known = |formula: Option<Dnf>| {
            if lenient {
                Some(formula.unwrap_or_else(|| vec![Vec::new()]))
            } else {
                formula
            }
        };
        match &expr.kind {
            ExprKind::Unary(Kind::Bang, inner) => self.formula_with(inner, !truth, lenient),
            ExprKind::Binary(op @ (Kind::AmpAmp | Kind::PipePipe), l, r) => {
                // `a && b` true or `a || b` false is a conjunction.
                if (*op == Kind::AmpAmp) == truth {
                    dnf_and(
                        &known(self.formula_with(l, truth, lenient))?,
                        &known(self.formula_with(r, truth, lenient))?,
                    )
                } else {
                    dnf_or(
                        self.formula_with(l, truth, lenient)?,
                        self.formula_with(r, truth, lenient)?,
                    )
                }
            }
            ExprKind::Binary(op, l, r) => {
                let (l, r) = (self.linear(l)?, self.linear(r)?);
                let op = if truth { op.clone() } else { negate(op)? };
                compare_dnf(l, &op, r)
            }
            ExprKind::Block(block) if block.statements.is_empty() => {
                self.formula_with(block.tail.as_ref()?, truth, lenient)
            }
            _ if expr.ty == crate::executable::Type::Bool => {
                let term = self.linear(expr)?;
                compare_dnf(term, &Kind::EqEq, Linear::constant(i128::from(truth)))
            }
            _ => None,
        }
    }
    /// Prove a goal formula from the facts, including disjunctive ones, and
    /// return its certificate. A conjunctive goal without disjunctive facts
    /// uses the direct search per constraint.
    pub(crate) fn certify(
        &self,
        goal: &Dnf,
        span: Span,
        obligation: &str,
    ) -> Option<Vec<Certificate>> {
        if goal.len() == 1 && self.clauses.is_empty() {
            let mut out = Vec::new();
            for constraint in &goal[0] {
                let proof = self.prove(constraint)?;
                out.push(Certificate {
                    span,
                    obligation: obligation.to_owned(),
                    goal: constraint.clone(),
                    proof,
                    hypotheses: self.snapshot(constraint),
                    clauses: Vec::new(),
                    goal_formula: None,
                });
            }
            return Some(out);
        }
        let hypotheses = self.snapshot_formula(goal);
        let mut available = self.clauses.clone();
        available.extend(negated_goal(goal)?);
        let mut budget = MAX_CASE_NODES;
        let proof = search_cases(&hypotheses, &available, &mut budget)?;
        Some(vec![Certificate {
            span,
            obligation: obligation.to_owned(),
            goal: Constraint {
                coefficients: BTreeMap::new(),
                bound: -1,
            },
            proof,
            hypotheses,
            clauses: self.clauses.clone(),
            goal_formula: Some(goal.clone()),
        }])
    }
    /// Facts plus implicit ranges for every term of `goal` and of the
    /// disjunctive facts.
    pub(crate) fn snapshot_formula(&self, goal: &Dnf) -> Vec<Constraint> {
        let mut probe = Constraint {
            coefficients: BTreeMap::new(),
            bound: 0,
        };
        for constraint in goal
            .iter()
            .flatten()
            .chain(self.clauses.iter().flatten().flatten())
        {
            for term in constraint.coefficients.keys() {
                probe.coefficients.insert(*term, 1);
            }
        }
        self.snapshot(&probe)
    }
    /// A checked i64 expression as a linear term, when it has that shape.
    /// Integer constants, locals, lengths, unary negation, `+`/`-`, and
    /// multiplication by an integer constant are admitted. Anything else (for
    /// example `x * y` or a float) is not reinterpreted.
    pub fn linear(&self, expr: &Expr) -> Option<Linear> {
        scalar_range(expr.ty)?;
        match &expr.kind {
            ExprKind::Constant(n) => Some(Linear::constant(constant_value(*n, expr.ty))),
            ExprKind::Local(slot) | ExprKind::Peek(slot) if !self.opaque.contains(slot) => {
                if let Some((root, steps)) = self.aliases.get(slot) {
                    let term = path_term(*root, steps);
                    if let Some(range) = scalar_range(expr.ty) {
                        self.note_term(term, range);
                    }
                    return Some(Linear::variable(term));
                }
                self.note_type(*slot, expr.ty);
                Some(Linear::variable(Term::Var(*slot, self.version(*slot))))
            }
            // A scalar field of a symbolic value, or a registered call's
            // scalar result (ENSURES).
            ExprKind::Project(..) | ExprKind::Call(..) if self.root_of(expr).is_some() => {
                let (root, steps) = self.root_of(expr)?;
                let term = path_term(root, &steps);
                if let Some(range) = scalar_range(expr.ty) {
                    self.note_term(term, range);
                }
                Some(Linear::variable(term))
            }
            ExprKind::Unary(Kind::Minus, inner) => self.linear(inner)?.negate(),
            ExprKind::Binary(op @ (Kind::Plus | Kind::Minus), l, r) => {
                let (l, r) = (self.linear(l)?, self.linear(r)?);
                if *op == Kind::Plus {
                    l.add(&r)
                } else {
                    l.sub(&r)
                }
            }
            ExprKind::Binary(Kind::Star, l, r) => {
                let (l, r) = (self.linear(l)?, self.linear(r)?);
                if l.is_constant() {
                    r.scale(l.constant)
                } else if r.is_constant() {
                    l.scale(r.constant)
                } else {
                    None
                }
            }
            ExprKind::Call(
                Target::Bytes(BytesOp::Len)
                | Target::Vec(VecOp::Len, _)
                | Target::Slice(SliceOp::Len, _),
                arguments,
            ) => {
                let slot = owner_slot(&arguments[0]).filter(|slot| !self.opaque.contains(slot))?;
                Some(Linear::variable(Term::Len(slot, self.version(slot))))
            }
            ExprKind::Block(block) if block.statements.is_empty() => {
                self.linear(block.tail.as_ref()?)
            }
            // `x & mask` with a constant mask `0 <= mask`: an unknown value in
            // `0 ..= mask` (two's complement, any width). Each occurrence is a
            // fresh term; `let i = x & 255` ties `i` to it.
            ExprKind::Binary(Kind::Amp, l, r) => {
                let mask = [l, r].into_iter().find_map(|side| match side.kind {
                    ExprKind::Constant(n) => Some(constant_value(n, side.ty)),
                    _ => None,
                })?;
                if mask < 0 {
                    return None;
                }
                let term = path_term(Root::Value(fresh_value()), &[]);
                self.note_term(term, (0, mask));
                Some(Linear::variable(term))
            }
            // A lossless widening keeps the value.
            ExprKind::Call(Target::Int(crate::int::IntOp::Convert, _, _), arguments) => {
                self.linear(&arguments[0])
            }
            // Proved in range, so its value is the exact result.
            ExprKind::Call(Target::Int(crate::int::IntOp::Unchecked(arith), _, _), arguments) => {
                let (l, r) = (self.linear(&arguments[0])?, self.linear(&arguments[1])?);
                match arith {
                    crate::int::ArithOp::Add => l.add(&r),
                    crate::int::ArithOp::Sub => l.sub(&r),
                    crate::int::ArithOp::Mul if l.is_constant() => r.scale(l.constant),
                    crate::int::ArithOp::Mul if r.is_constant() => l.scale(r.constant),
                    crate::int::ArithOp::Mul => None,
                }
            }
            _ => None,
        }
    }
    /// OVERFLOW-ELIDE: certificates that `left op right` stays within the
    /// range of `ty` under the current facts, or `None`.
    pub(crate) fn in_range(
        &self,
        op: &Kind,
        left: &Expr,
        right: &Expr,
        ty: crate::executable::Type,
        span: Span,
    ) -> Option<Vec<Certificate>> {
        let (low, high) = scalar_range(ty)?;
        let (l, r) = (self.linear(left)?, self.linear(right)?);
        let value = match op {
            Kind::Plus => l.add(&r)?,
            Kind::Minus => l.sub(&r)?,
            Kind::Star if l.is_constant() => r.scale(l.constant)?,
            Kind::Star if r.is_constant() => l.scale(r.constant)?,
            _ => return None,
        };
        // The operands' terms and those of the facts that may bound them
        // (`x <= limit` needs `limit <= i64::MAX`). Only locals recorded as
        // `i64` get that bound; an unrecorded one gets none (a u64 local
        // above i64::MAX must never be assumed below it).
        let mut terms = value.coefficients.keys().copied().collect::<Vec<_>>();
        for constraint in self
            .known
            .iter()
            .chain(self.clauses.iter().flatten().flatten())
        {
            terms.extend(constraint.coefficients.keys().copied());
        }
        let goal = compare_dnf(Linear::constant(low), &Kind::Le, value.clone())?;
        let upper = compare_dnf(value, &Kind::Le, Linear::constant(high))?;
        let goal = dnf_and(&goal, &upper)?;
        // `i64` operands carry no implicit range elsewhere (their huge bounds
        // only slow other proofs down); a range proof needs them.
        let with_ranges = self.clone();
        for term in &terms {
            if let Term::Var(slot, _) = term
                && !with_ranges.ranges.borrow().contains_key(slot)
                && self.wide.borrow().contains(slot)
            {
                with_ranges
                    .ranges
                    .borrow_mut()
                    .insert(*slot, (i128::from(i64::MIN), i128::from(i64::MAX)));
            }
        }
        with_ranges.certify(&goal, span, "the result stays in range")
    }
    /// `slot = value`: the right side is read at the old version, then the
    /// slot moves to a new version equal to it.
    pub fn assign(&mut self, slot: usize, value: &Expr) {
        // The slot has the value's type; record its range before any fact
        // mentions it (`in_range` treats an unrecorded slot as `i64`).
        self.note_type(slot, value.ty);
        let value = self.linear(value);
        self.bump(slot);
        if let Some(value) = value.filter(|_| !self.opaque.contains(&slot)) {
            let var = Linear::variable(Term::Var(slot, self.version(slot)));
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
        }
    }
    /// Facts for a new binding `slot = value` at the slot's current version.
    pub fn define(&mut self, slot: usize, value: &Expr) {
        if self.opaque.contains(&slot) {
            return;
        }
        self.note_type(slot, value.ty);
        if let Some(value) = self.linear(value) {
            let var = Linear::variable(Term::Var(slot, self.version(slot)));
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
        } else if value.ty == crate::executable::Type::Bool && fact_safe(value) {
            // `let b = condition`: b is true exactly when the condition is.
            // Each side may be weakened (unknown atoms dropped), which keeps
            // the clause true.
            let var = Linear::variable(Term::Var(slot, self.version(slot)));
            let truth = |t: i128| compare_dnf(var.clone(), &Kind::EqEq, Linear::constant(t));
            let clause = (|| {
                let holds = dnf_and(&truth(1)?, &self.formula(value, true)?)?;
                let fails = dnf_and(&truth(0)?, &self.formula(value, false)?)?;
                dnf_or(holds, fails)
            })();
            if let Some(clause) = clause {
                self.ranges.borrow_mut().insert(slot, (0, 1));
                self.clauses.push(clause);
            }
        }
    }
    /// Tightest proven `to - from <= d`, if any. Used only to preserve a
    /// monotone loop bound; it extracts the difference-shaped constraints from
    /// the general system and runs the previous shortest-path relaxation.
    pub fn distance(&self, from: Term, to: Term) -> Option<i128> {
        let mut differences = Vec::new();
        for constraint in self.snapshot_universal() {
            let mut positive = None;
            let mut negative = None;
            let mut scale = 0i128;
            for (term, coefficient) in &constraint.coefficients {
                if *coefficient > 0 {
                    if positive.is_some() || *term == Term::Zero {
                        positive = None;
                        negative = None;
                        break;
                    }
                    positive = Some(*term);
                    scale = *coefficient;
                } else {
                    if negative.is_some() || *term == Term::Zero {
                        positive = None;
                        negative = None;
                        break;
                    }
                    negative = Some(*term);
                }
            }
            // A one-variable bound `c*x <= d` (or `-c*x <= d`) is a difference
            // constraint against zero: `x - 0 <= d/c` (or `0 - x <= d/c`).
            if constraint.coefficients.len() == 1 {
                let (term, coefficient) = constraint
                    .coefficients
                    .iter()
                    .next()
                    .map(|(term, coefficient)| (*term, *coefficient))
                    .expect("one coefficient");
                if term != Term::Zero && coefficient != 0 {
                    let bound = constraint.bound.div_euclid(coefficient.abs());
                    if coefficient > 0 {
                        differences.push((Term::Zero, term, bound));
                    } else {
                        differences.push((term, Term::Zero, bound));
                    }
                }
                continue;
            }
            let (Some(left), Some(right)) = (positive, negative) else {
                continue;
            };
            if constraint
                .coefficients
                .get(&right)
                .copied()
                .unwrap_or(0)
                .checked_neg()
                != Some(scale)
                || scale <= 0
            {
                continue;
            }
            differences.push((right, left, constraint.bound.div_euclid(scale)));
        }
        if from == to {
            return Some(0);
        }
        let mut dist: BTreeMap<Term, i128> = BTreeMap::new();
        dist.insert(from, 0);
        for _ in 0..=differences.len() {
            let mut changed = false;
            for (b, a, bound) in &differences {
                if let Some(&d) = dist.get(b) {
                    let candidate = d + bound;
                    if dist.get(a).is_none_or(|old| candidate < *old) {
                        dist.insert(*a, candidate);
                        changed = true;
                    }
                }
            }
            if !changed {
                return dist.get(&to).copied();
            }
        }
        None
    }
    /// A loop-carried local that only increases (decreases) keeps its lower
    /// (upper) bound from loop entry at every later version.
    pub fn bump_monotone(&mut self, slot: usize, increasing: bool) {
        let old = Term::Var(slot, self.version(slot));
        let bound = if increasing {
            self.distance(old, Term::Zero)
        } else {
            self.distance(Term::Zero, old)
        };
        self.bump(slot);
        let new = Term::Var(slot, self.version(slot));
        if let Some(bound) = bound {
            let mut coefficients = BTreeMap::new();
            if increasing {
                coefficients.insert(new, -1);
            } else {
                coefficients.insert(new, 1);
            }
            self.known.push(Constraint {
                coefficients,
                bound,
            });
        }
    }
    /// Try to prove `goal`; returns a refutation certificate. The rational
    /// search runs first; only if it fails does the bounded integer fallback
    /// try rounding cuts and case splits.
    pub fn prove(&self, goal: &Constraint) -> Option<Refutation> {
        // A true constant goal needs no hypotheses. A false one still holds
        // where the facts are contradictory (dead code, ex falso lemmas), so
        // it falls through to a refutation of the hypotheses.
        if goal.coefficients.is_empty() && goal.bound >= 0 {
            return Some(Refutation::Trivial);
        }
        // Implicit facts (lengths, scalar ranges) for the goal's terms too.
        let hypotheses = self.snapshot(goal);
        if let Some(proof) = prove_with(&hypotheses, goal) {
            return Some(Refutation::Farkas(proof));
        }
        prove_integer(&hypotheses, goal)
    }
    /// Remember the value range of `slot`'s type, so proofs may use it
    /// (`0 <= b <= 1` for a `Bool`, `0 <= x <= 255` for a `u8`, ...).
    pub(crate) fn note_type(&self, slot: usize, ty: crate::executable::Type) {
        if ty == crate::executable::Type::I64 {
            self.wide.borrow_mut().insert(slot);
        } else if let Some(range) = scalar_range(ty) {
            self.ranges.borrow_mut().insert(slot, range);
        }
    }
    fn implicit(&self, goal: &Constraint) -> Vec<Constraint> {
        let mut terms = goal.coefficients.keys().copied().collect::<Vec<_>>();
        for c in &self.known {
            terms.extend(c.coefficients.keys().copied());
        }
        terms.sort();
        terms.dedup();
        let ranges = self.ranges.borrow();
        let mut out = Vec::new();
        for term in terms {
            let (low, high) = match term {
                Term::Len(..) => (0, i128::MAX),
                Term::Var(slot, _) => match ranges.get(&slot) {
                    Some(range) => *range,
                    None => continue,
                },
                Term::Path(_) => match self.term_ranges.borrow().get(&term) {
                    Some(range) => *range,
                    None => continue,
                },
                Term::Zero => continue,
            };
            // -term <= -low, and term <= high when bounded.
            out.push(Constraint {
                coefficients: BTreeMap::from([(term, -1)]),
                bound: -low,
            });
            if high != i128::MAX {
                out.push(Constraint {
                    coefficients: BTreeMap::from([(term, 1)]),
                    bound: high,
                });
            }
        }
        out
    }
    pub fn snapshot_universal(&self) -> Vec<Constraint> {
        let mut known = self.known.clone();
        known.extend(self.implicit(&Constraint {
            coefficients: BTreeMap::new(),
            bound: 0,
        }));
        known
    }
    pub fn snapshot(&self, goal: &Constraint) -> Vec<Constraint> {
        let mut known = self.known.clone();
        known.extend(self.implicit(goal));
        known
    }
}

// Conditions that mutate locals cannot be reinterpreted at their final versions.
fn fact_safe(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Constant(_) | ExprKind::Local(_) | ExprKind::Peek(_) | ExprKind::Borrow(_) => {
            true
        }
        ExprKind::Unary(_, e) | ExprKind::BoxRead(e) | ExprKind::Project(e, _) => fact_safe(e),
        ExprKind::Binary(_, a, b) | ExprKind::BytesAt(a, b) => fact_safe(a) && fact_safe(b),
        ExprKind::Call(_, args) => args.iter().all(fact_safe),
        ExprKind::Block(b) => {
            b.statements.is_empty() && b.tail.as_ref().is_some_and(|e| fact_safe(e))
        }
        _ => false,
    }
}

/// The local that owns (or is borrowed as) a length-carrying value.
pub(crate) fn owner_slot(expr: &Expr) -> Option<usize> {
    match &expr.kind {
        ExprKind::Borrow(slot) | ExprKind::Local(slot) | ExprKind::Peek(slot) => Some(*slot),
        _ => None,
    }
}

fn negate(op: &Kind) -> Option<Kind> {
    Some(match op {
        Kind::Lt => Kind::Ge,
        Kind::Le => Kind::Gt,
        Kind::Gt => Kind::Le,
        Kind::Ge => Kind::Lt,
        Kind::EqEq => Kind::Ne,
        Kind::Ne => Kind::EqEq,
        _ => return None,
    })
}

/// Translate `l op r` into integer linear inequalities.
pub(crate) fn compare(l: Linear, op: &Kind, r: Linear, out: &mut Vec<Constraint>) {
    // l op r  ==>  l - r <= 0 (or < 0 for strict comparisons). Strictness is
    // converted to `<= -1` because every admitted term is integer-valued.
    let one_sided = |l: Linear, r: Linear, strict: bool| {
        let difference = l.sub(&r)?;
        let constant = if strict {
            difference.constant.checked_add(1)?
        } else {
            difference.constant
        };
        Some(Constraint {
            coefficients: difference.coefficients,
            bound: constant.checked_neg()?,
        })
    };
    match op {
        Kind::Lt => out.extend(one_sided(l, r, true)),
        Kind::Le => out.extend(one_sided(l, r, false)),
        Kind::Gt => out.extend(one_sided(r, l, true)),
        Kind::Ge => out.extend(one_sided(r, l, false)),
        Kind::EqEq => {
            out.extend(one_sided(l.clone(), r.clone(), false));
            out.extend(one_sided(r, l, false));
        }
        _ => {}
    }
}

/// Integer negation of `goal`: `goal` is `c*x <= d`, so the negation is
/// `-c*x <= -d - 1` (every term is integer-valued).
fn negation(goal: &Constraint) -> Option<Constraint> {
    let mut coefficients = BTreeMap::new();
    for (term, coefficient) in &goal.coefficients {
        coefficients.insert(*term, coefficient.checked_neg()?);
    }
    Some(Constraint {
        coefficients,
        bound: goal.bound.checked_neg()?.checked_sub(1)?,
    })
}

/// Eliminate every variable with Fourier–Motzkin. The returned rows are the
/// final `0 <= bound` consequences; `None` means a work budget was exceeded or
/// exact rational arithmetic overflowed.
fn eliminate(mut rows: Vec<Row>) -> Option<Vec<Row>> {
    let mut terms = BTreeMap::<Term, usize>::new();
    for row in &rows {
        for term in row.coefficients.keys() {
            terms.insert(*term, 0);
        }
    }
    if terms.len() > MAX_FM_TERMS || rows.len() > MAX_FM_ROWS {
        return None;
    }
    let variables = terms.keys().copied().collect::<Vec<_>>();
    let mut pairs = 0usize;
    for variable in variables {
        let mut upper = Vec::new();
        let mut lower = Vec::new();
        let mut zero = Vec::new();
        for row in rows {
            match row.coefficients.get(&variable).copied() {
                Some(coefficient) if coefficient.is_positive() => upper.push((row, coefficient)),
                Some(coefficient) => lower.push((row, coefficient)),
                None => zero.push(row),
            }
        }
        let mut next = zero;
        for (up, up_coefficient) in &upper {
            for (low, low_coefficient) in &lower {
                pairs += 1;
                if pairs > MAX_FM_PAIRS || next.len() >= MAX_FM_ROWS {
                    return None;
                }
                // up: au*x + ru <= bu, au > 0
                // low: al*x + rl <= bl, al < 0
                // (-al)*up + au*low eliminates x with both weights positive.
                let weight_low = up_coefficient.checked_abs()?;
                let weight_up = low_coefficient.checked_abs()?;
                let combined = up.combine(low, weight_up, weight_low, &variable)?;
                next.push(combined);
            }
        }
        rows = next;
    }
    Some(rows)
}

/// The weights of a contradictory row: a positive denominator and, per
/// source row (the row origins), a non-negative numerator.
fn conflict_weights(conflict: &Row) -> Option<(i128, Vec<(u32, i128)>)> {
    let mut denominator = 1i128;
    for multiplier in conflict.origins.values() {
        denominator = lcm(denominator, multiplier.den);
    }
    let mut weights = Vec::new();
    for (origin, multiplier) in &conflict.origins {
        let numerator = multiplier.num.checked_mul(denominator / multiplier.den)?;
        weights.push((u32::try_from(*origin).ok()?, numerator));
    }
    // Reduce a common factor so certificates stay small.
    let mut divisor = denominator;
    for (_, numerator) in &weights {
        divisor = gcd(divisor, *numerator);
    }
    if divisor > 1 {
        denominator /= divisor;
        for (_, numerator) in &mut weights {
            *numerator /= divisor;
        }
    }
    Some((denominator, weights))
}

/// The Farkas certificate those weights describe over `sources`.
fn farkas_from_weights(
    denominator: i128,
    weights: &[(u32, i128)],
    sources: &[Constraint],
) -> Option<Farkas> {
    let mut steps = Vec::with_capacity(weights.len());
    let mut multipliers = Vec::with_capacity(weights.len());
    for (origin, numerator) in weights {
        steps.push(sources.get(*origin as usize)?.clone());
        multipliers.push(*numerator);
    }
    Some(Farkas {
        steps,
        multipliers,
        denominator,
    })
}

/// Serialize a system for the proof cache with its terms renamed to their
/// rank in term order. Elimination depends only on the order of terms and of
/// rows, so systems with equal serializations search identically.
fn system_key(sources: &[Constraint], required: Option<usize>) -> u128 {
    system_key_with(sources, &[required.map_or(u64::MAX, |index| index as u64)])
}

/// `domain` separates the kinds of question asked about one system.
fn system_key_with(sources: &[Constraint], domain: &[u64]) -> u128 {
    let mut terms = BTreeSet::new();
    for source in sources {
        terms.extend(source.coefficients.keys().copied());
    }
    let ranks: BTreeMap<Term, u32> = terms.into_iter().zip(0u32..).collect();
    let mut bytes = Vec::with_capacity(sources.len() * 48 + 16);
    for word in domain {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    for source in sources {
        bytes.extend_from_slice(&(source.coefficients.len() as u32).to_le_bytes());
        for (term, coefficient) in &source.coefficients {
            bytes.extend_from_slice(&ranks[term].to_le_bytes());
            bytes.extend_from_slice(&coefficient.to_le_bytes());
        }
        bytes.extend_from_slice(&source.bound.to_le_bytes());
    }
    crate::proof_cache::key(&bytes)
}

/// Search for a rational refutation of `sources`. With `required`, the
/// refutation must use that row with a positive weight. Outcomes are
/// remembered across builds; a remembered refutation is rebuilt over the
/// current rows and verified again, so the cache is never trusted.
fn refute_system(sources: &[Constraint], required: Option<usize>) -> Option<Farkas> {
    let key = system_key(sources, required);
    match crate::proof_cache::get(key) {
        Some(None) => return None,
        Some(Some((denominator, weights))) => {
            let uses_required = required.is_none_or(|index| {
                weights
                    .iter()
                    .any(|(origin, numerator)| *origin as usize == index && *numerator > 0)
            });
            if uses_required
                && let Some(proof) = farkas_from_weights(denominator, &weights, sources)
                && verify_farkas(sources, &proof)
            {
                return Some(proof);
            }
        }
        None => {}
    }
    let found = search_refutation(sources, required);
    crate::proof_cache::put(key, found.clone());
    let (denominator, weights) = found?;
    farkas_from_weights(denominator, &weights, sources)
}

fn search_refutation(
    sources: &[Constraint],
    required: Option<usize>,
) -> Option<(i128, Vec<(u32, i128)>)> {
    let mut rows = Vec::with_capacity(sources.len());
    for (index, source) in sources.iter().enumerate() {
        rows.push(Row::from_constraint(source, index)?);
    }
    let rows = eliminate(rows)?;
    // After eliminating every variable, every row is `0 <= bound`. A negative
    // bound is a contradiction. With a goal, prefer a contradiction that
    // actually uses the goal's negation, so the certificate is a proof of the
    // goal rather than merely an observation that the hypotheses are
    // inconsistent.
    let conflict = rows.iter().find(|row| {
        row.coefficients.is_empty()
            && row.bound.is_negative()
            && required.is_none_or(|index| {
                row.origins
                    .get(&index)
                    .is_some_and(|multiplier| multiplier.is_positive())
            })
    })?;
    conflict_weights(conflict)
}

fn prove_with(hypotheses: &[Constraint], goal: &Constraint) -> Option<Farkas> {
    if goal.coefficients.is_empty() {
        return (goal.bound >= 0).then(|| Farkas {
            steps: Vec::new(),
            multipliers: Vec::new(),
            denominator: 1,
        });
    }
    let negated = negation(goal)?;
    let mut sources = Vec::with_capacity(hypotheses.len() + 1);
    sources.extend(hypotheses.iter().cloned());
    let negation_index = sources.len();
    sources.push(negated);
    refute_system(&sources, Some(negation_index))
}

/// Refute a complete integer system without a distinguished goal. This is the
/// leaf rule used by the integer fallback: any negative constant consequence
/// of the available constraints is a contradiction.
fn refute_rational(system: &[Constraint]) -> Option<Farkas> {
    refute_system(system, None)
}

/// Exact non-negative rational used by the Fourier–Motzkin search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Ratio {
    num: i128,
    den: i128,
}

impl Ratio {
    fn integer(value: i128) -> Self {
        Ratio { num: value, den: 1 }
    }
    fn is_positive(&self) -> bool {
        self.num > 0
    }
    fn is_negative(&self) -> bool {
        self.num < 0
    }
    fn checked_abs(self) -> Option<Self> {
        Some(Ratio {
            num: self.num.checked_abs()?,
            den: self.den,
        })
    }
    fn checked_add(self, other: Self) -> Option<Self> {
        let num = self
            .num
            .checked_mul(other.den)?
            .checked_add(other.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(other.den)?;
        Self::normalized(num, den)
    }
    fn checked_mul(self, other: Self) -> Option<Self> {
        Self::normalized(
            self.num.checked_mul(other.num)?,
            self.den.checked_mul(other.den)?,
        )
    }
    fn normalized(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        // Already in lowest terms; the common case, since weights are integers.
        if den == 1 {
            return Some(Ratio { num, den });
        }
        let (num, den) = if den < 0 {
            (num.checked_neg()?, den.checked_neg()?)
        } else {
            (num, den)
        };
        let divisor = gcd(num, den);
        let divisor = if divisor == 0 { 1 } else { divisor };
        Some(Ratio {
            num: num / divisor,
            den: den / divisor,
        })
    }
}

struct Row {
    coefficients: BTreeMap<Term, Ratio>,
    bound: Ratio,
    origins: BTreeMap<usize, Ratio>,
}

impl Row {
    fn from_constraint(constraint: &Constraint, origin: usize) -> Option<Self> {
        let mut coefficients = BTreeMap::new();
        for (term, coefficient) in &constraint.coefficients {
            if *coefficient != 0 {
                coefficients.insert(*term, Ratio::integer(*coefficient));
            }
        }
        let mut origins = BTreeMap::new();
        origins.insert(origin, Ratio::integer(1));
        Some(Row {
            coefficients,
            bound: Ratio::integer(constraint.bound),
            origins,
        })
    }
    /// `weight_self * self + weight_other * other`; the caller guarantees that
    /// the weights are positive and exactly cancel `eliminated`.
    fn combine(
        &self,
        other: &Row,
        weight_self: Ratio,
        weight_other: Ratio,
        eliminated: &Term,
    ) -> Option<Self> {
        let mut coefficients = BTreeMap::new();
        for (term, coefficient) in &self.coefficients {
            if term == eliminated {
                continue;
            }
            coefficients.insert(*term, coefficient.checked_mul(weight_self)?);
        }
        for (term, coefficient) in &other.coefficients {
            if term == eliminated {
                continue;
            }
            let value = coefficient.checked_mul(weight_other)?;
            match coefficients.entry(*term) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(value);
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    let sum = entry.get().checked_add(value)?;
                    if sum.num == 0 {
                        entry.remove();
                    } else {
                        *entry.get_mut() = sum;
                    }
                }
            }
        }
        let bound = self
            .bound
            .checked_mul(weight_self)?
            .checked_add(other.bound.checked_mul(weight_other)?)?;
        let mut origins = BTreeMap::new();
        for (origin, multiplier) in &self.origins {
            let value = multiplier.checked_mul(weight_self)?;
            origins.insert(*origin, value);
        }
        for (origin, multiplier) in &other.origins {
            let value = multiplier.checked_mul(weight_other)?;
            match origins.entry(*origin) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(value);
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    let sum = entry.get().checked_add(value)?;
                    if sum.num == 0 {
                        entry.remove();
                    } else {
                        *entry.get_mut() = sum;
                    }
                }
            }
        }
        Some(Row {
            coefficients,
            bound,
            origins,
        })
    }
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a
}

fn gcd(a: i128, b: i128) -> i128 {
    i128::try_from(gcd_u128(a.unsigned_abs(), b.unsigned_abs()))
        .unwrap_or(i128::MAX)
        .max(1)
}

fn lcm(a: i128, b: i128) -> i128 {
    let divisor = gcd(a, b);
    a / divisor * b
}

/// One rounding cut produced by the search. `steps`/`multipliers` describe the
/// non-negative integer combination that is rounded by `divisor`.
#[derive(Debug, Clone)]
struct CutRule {
    steps: Vec<Constraint>,
    multipliers: Vec<i128>,
    divisor: i128,
    result: Constraint,
}

fn prove_integer(hypotheses: &[Constraint], goal: &Constraint) -> Option<Refutation> {
    prove_integer_with(hypotheses, goal, IntegerBudget::standard())
}

fn prove_integer_with(
    hypotheses: &[Constraint],
    goal: &Constraint,
    mut budget: IntegerBudget,
) -> Option<Refutation> {
    let negated = negation(goal)?;
    let mut system = Vec::with_capacity(hypotheses.len() + 1);
    system.extend(hypotheses.iter().cloned());
    system.push(negated);
    if system.len() > MAX_INTEGER_CONSTRAINTS {
        return None;
    }
    // Most goals that reach the integer fallback are simply not provable,
    // and establishing that is the expensive part. Remember failures only:
    // a proof is searched again, so nothing remembered is ever trusted.
    let key = system_key_with(
        &system,
        &[
            u64::MAX - 1,
            budget.nodes as u64,
            budget.cuts as u64,
            budget.cut_rounds as u64,
        ],
    );
    if crate::proof_cache::get(key) == Some(None) {
        return None;
    }
    let proof = solve_integer(&system, MAX_INTEGER_DEPTH, &mut budget);
    if proof.is_none() {
        crate::proof_cache::put(key, None);
    }
    proof
}

fn solve_integer(
    system: &[Constraint],
    depth: usize,
    budget: &mut IntegerBudget,
) -> Option<Refutation> {
    if budget.nodes == 0
        || system.len() > MAX_INTEGER_CONSTRAINTS
        || integer_term_count(system) > MAX_INTEGER_TERMS
    {
        return None;
    }
    budget.nodes -= 1;
    if let Some(farkas) = refute_rational(system) {
        return Some(Refutation::Farkas(farkas));
    }

    // Add a small batch of rounding cuts, then retry the rational refutation.
    // The cuts are nested in `Refutation::Cut` in the order they were added so
    // every cut's source is available when the verifier reaches it.
    let mut local = system.to_vec();
    let mut cuts = Vec::new();
    for _ in 0..budget.cut_rounds.min(MAX_INTEGER_CUT_ROUNDS) {
        if budget.cuts == 0 {
            break;
        }
        let candidates = cut_candidates(&local, budget.cuts);
        let mut added = false;
        for cut in candidates {
            if budget.cuts == 0 {
                break;
            }
            if local.contains(&cut.result) {
                continue;
            }
            budget.cuts -= 1;
            local.push(cut.result.clone());
            cuts.push(cut);
            added = true;
        }
        if !added {
            break;
        }
        if let Some(farkas) = refute_rational(&local) {
            return Some(wrap_cuts(cuts, Refutation::Farkas(farkas)));
        }
    }

    if depth == 0 || budget.nodes == 0 {
        return None;
    }

    let candidates = branch_candidates(&local);
    for (attempted, (variable, threshold)) in candidates.into_iter().enumerate() {
        if attempted >= MAX_INTEGER_BRANCH_ATTEMPTS || budget.nodes == 0 {
            break;
        }
        let Some(above) = threshold.checked_add(1) else {
            continue;
        };
        let Some(negated_above) = above.checked_neg() else {
            continue;
        };
        let mut left_system = local.clone();
        left_system.push(bound_constraint(variable, 1, threshold));
        let Some(left) = solve_integer(&left_system, depth - 1, budget) else {
            continue;
        };
        let mut right_system = local.clone();
        right_system.push(bound_constraint(variable, -1, negated_above));
        let Some(right) = solve_integer(&right_system, depth - 1, budget) else {
            continue;
        };
        return Some(wrap_cuts(
            cuts,
            Refutation::Branch {
                variable,
                threshold,
                left: Box::new(left),
                right: Box::new(right),
            },
        ));
    }
    None
}

fn wrap_cuts(cuts: Vec<CutRule>, mut inner: Refutation) -> Refutation {
    for cut in cuts.into_iter().rev() {
        inner = Refutation::Cut {
            steps: cut.steps,
            multipliers: cut.multipliers,
            divisor: cut.divisor,
            result: cut.result,
            then: Box::new(inner),
        };
    }
    inner
}

fn integer_term_count(system: &[Constraint]) -> usize {
    let mut terms = BTreeSet::new();
    for constraint in system {
        for term in constraint.coefficients.keys() {
            if *term != Term::Zero {
                terms.insert(*term);
            }
        }
    }
    terms.len()
}

fn bound_constraint(variable: Term, coefficient: i128, bound: i128) -> Constraint {
    let mut coefficients = BTreeMap::new();
    if variable != Term::Zero && coefficient != 0 {
        coefficients.insert(variable, coefficient);
    }
    Constraint {
        coefficients,
        bound,
    }
}

fn combine_steps(
    steps: &[&Constraint],
    multipliers: &[i128],
) -> Option<(BTreeMap<Term, i128>, i128)> {
    if steps.len() != multipliers.len() || steps.is_empty() {
        return None;
    }
    let mut coefficients: BTreeMap<Term, i128> = BTreeMap::new();
    let mut bound = 0i128;
    for (step, multiplier) in steps.iter().zip(multipliers) {
        if *multiplier < 0 {
            return None;
        }
        bound = bound.checked_add(step.bound.checked_mul(*multiplier)?)?;
        for (term, coefficient) in &step.coefficients {
            let value = coefficient.checked_mul(*multiplier)?;
            let entry = coefficients.entry(*term).or_insert(0);
            *entry = entry.checked_add(value)?;
            if *entry == 0 {
                coefficients.remove(term);
            }
        }
    }
    Some((coefficients, bound))
}

fn coefficient_gcd(coefficients: &BTreeMap<Term, i128>) -> Option<i128> {
    let mut divisor = 0u128;
    for coefficient in coefficients.values() {
        divisor = gcd_u128(divisor, coefficient.unsigned_abs());
    }
    i128::try_from(divisor).ok().filter(|divisor| *divisor > 1)
}

fn rounded_cut(steps: &[&Constraint], multipliers: &[i128]) -> Option<(i128, Constraint)> {
    let (coefficients, bound) = combine_steps(steps, multipliers)?;
    if coefficients.is_empty() {
        return None;
    }
    let divisor = coefficient_gcd(&coefficients)?;
    // A cut with a divisible bound is just the combination divided by its gcd,
    // so it adds no strength over the rational system. Keep only real rounds.
    if bound.rem_euclid(divisor) == 0 {
        return None;
    }
    let mut cut_coefficients = BTreeMap::new();
    for (term, coefficient) in coefficients {
        cut_coefficients.insert(term, coefficient.div_euclid(divisor));
    }
    Some((
        divisor,
        Constraint {
            coefficients: cut_coefficients,
            bound: bound.div_euclid(divisor),
        },
    ))
}

fn push_cut(
    system: &[Constraint],
    out: &mut Vec<CutRule>,
    steps: Vec<Constraint>,
    multipliers: Vec<i128>,
    divisor: i128,
    result: Constraint,
    limit: usize,
) {
    if out.len() >= limit || system.contains(&result) || out.iter().any(|cut| cut.result == result)
    {
        return;
    }
    out.push(CutRule {
        steps,
        multipliers,
        divisor,
        result,
    });
}

/// Single-constraint rounding cuts plus pairwise sums. The pairwise sums let a
/// cut use a non-negative combination that cancels a term, for example
/// `(x + y <= 1) + (x - y <= 0)` giving `2*x <= 1` and then `x <= 0`.
fn cut_candidates(system: &[Constraint], limit: usize) -> Vec<CutRule> {
    let mut out = Vec::new();
    for constraint in system {
        if out.len() >= limit {
            return out;
        }
        let steps = [constraint];
        if let Some((divisor, result)) = rounded_cut(&steps, &[1]) {
            push_cut(
                system,
                &mut out,
                vec![constraint.clone()],
                vec![1],
                divisor,
                result,
                limit,
            );
        }
    }
    let mut pairs = 0usize;
    'pairs: for i in 0..system.len() {
        for j in (i + 1)..system.len() {
            if out.len() >= limit {
                break 'pairs;
            }
            pairs += 1;
            if pairs > MAX_INTEGER_CUT_PAIRS {
                break 'pairs;
            }
            let steps = [&system[i], &system[j]];
            if let Some((divisor, result)) = rounded_cut(&steps, &[1, 1]) {
                push_cut(
                    system,
                    &mut out,
                    vec![system[i].clone(), system[j].clone()],
                    vec![1, 1],
                    divisor,
                    result,
                    limit,
                );
            }
        }
    }
    out
}

fn branch_candidates(system: &[Constraint]) -> Vec<(Term, i128)> {
    let mut variables = BTreeSet::new();
    for constraint in system {
        for term in constraint.coefficients.keys() {
            if *term != Term::Zero {
                variables.insert(*term);
            }
        }
    }
    let mut out = Vec::new();
    for variable in variables {
        let mut thresholds = BTreeSet::new();
        thresholds.insert(0i128);
        for constraint in system {
            let Some(&coefficient) = constraint.coefficients.get(&variable) else {
                continue;
            };
            if coefficient == 0 {
                continue;
            }
            if let Some(split) = constraint.bound.checked_div_euclid(coefficient) {
                thresholds.insert(split);
                if constraint.coefficients.len() == 1 {
                    if let Some(previous) = split.checked_sub(1) {
                        thresholds.insert(previous);
                    }
                    if let Some(next) = split.checked_add(1) {
                        thresholds.insert(next);
                    }
                }
            }
        }
        let mut ordered = vec![0i128];
        ordered.extend(thresholds.into_iter().filter(|threshold| *threshold != 0));
        for threshold in ordered.into_iter().take(MAX_INTEGER_THRESHOLDS) {
            out.push((variable, threshold));
        }
        if out.len() >= MAX_INTEGER_BRANCH_ATTEMPTS {
            break;
        }
    }
    out
}

fn verify_farkas(context: &[Constraint], proof: &Farkas) -> bool {
    if proof.denominator <= 0
        || proof.steps.len() != proof.multipliers.len()
        || proof.multipliers.iter().any(|multiplier| *multiplier < 0)
        || !proof.steps.iter().all(|step| context.contains(step))
    {
        return false;
    }
    let steps = proof.steps.iter().collect::<Vec<_>>();
    let Some((coefficients, bound)) = combine_steps(&steps, &proof.multipliers) else {
        return false;
    };
    coefficients.is_empty() && bound < 0
}

fn verify_cut(
    context: &[Constraint],
    steps: &[Constraint],
    multipliers: &[i128],
    divisor: i128,
    result: &Constraint,
    then: &Refutation,
) -> bool {
    if divisor <= 1
        || steps.is_empty()
        || steps.len() != multipliers.len()
        || multipliers.iter().any(|multiplier| *multiplier < 0)
        || !steps.iter().all(|step| context.contains(step))
    {
        return false;
    }
    let borrowed = steps.iter().collect::<Vec<_>>();
    let Some((coefficients, bound)) = combine_steps(&borrowed, multipliers) else {
        return false;
    };
    let Some(expected_divisor) = coefficient_gcd(&coefficients) else {
        return false;
    };
    if expected_divisor != divisor {
        return false;
    }
    let mut cut_coefficients = BTreeMap::new();
    for (term, coefficient) in coefficients {
        cut_coefficients.insert(term, coefficient.div_euclid(divisor));
    }
    let expected = Constraint {
        coefficients: cut_coefficients,
        bound: bound.div_euclid(divisor),
    };
    if expected != *result {
        return false;
    }
    let mut next = context.to_vec();
    next.push(result.clone());
    verify_refutation(&next, then)
}

fn verify_branch(
    context: &[Constraint],
    variable: Term,
    threshold: i128,
    left: &Refutation,
    right: &Refutation,
) -> bool {
    if variable == Term::Zero {
        return false;
    }
    let Some(above) = threshold.checked_add(1) else {
        return false;
    };
    let Some(negated_above) = above.checked_neg() else {
        return false;
    };
    let mut left_context = context.to_vec();
    left_context.push(bound_constraint(variable, 1, threshold));
    let mut right_context = context.to_vec();
    right_context.push(bound_constraint(variable, -1, negated_above));
    verify_refutation(&left_context, left) && verify_refutation(&right_context, right)
}

/// Refute `units` together with every clause, splitting on clauses
/// (smallest first). Each leaf is a rational refutation or the bounded
/// integer fallback.
fn search_cases(units: &[Constraint], clauses: &[Dnf], budget: &mut usize) -> Option<Refutation> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    if let Some(farkas) = refute_rational(units) {
        return Some(Refutation::Farkas(farkas));
    }
    // Simplify before splitting, as a SAT solver does: a clause with a
    // disjunct that the units already entail cannot help (that branch is the
    // units again), so it is set aside; a disjunct that contradicts the units
    // is closed by its own refutation, so only the live disjuncts branch.
    let entails = |disjunct: &Vec<Constraint>| {
        disjunct.iter().all(|constraint| {
            negation(constraint).is_some_and(|negated| {
                let mut system = units.to_vec();
                system.push(negated);
                refute_rational(&system).is_some()
            })
        })
    };
    let mut candidates: Vec<(usize, Vec<Option<Refutation>>)> = Vec::new();
    for (index, clause) in clauses.iter().enumerate() {
        if clause.iter().any(entails) {
            continue;
        }
        let dead = clause
            .iter()
            .map(|disjunct| {
                let mut system = units.to_vec();
                system.extend(disjunct.iter().cloned());
                refute_rational(&system).map(Refutation::Farkas)
            })
            .collect::<Vec<_>>();
        candidates.push((index, dead));
    }
    let live = |dead: &Vec<Option<Refutation>>| dead.iter().filter(|d| d.is_none()).count();
    let Some(position) = (0..candidates.len()).min_by_key(|&i| live(&candidates[i].1)) else {
        if units.len() > MAX_INTEGER_CONSTRAINTS {
            return None;
        }
        return solve_integer(units, MAX_INTEGER_DEPTH, &mut IntegerBudget::standard());
    };
    let (index, dead) = candidates.swap_remove(position);
    let clause = &clauses[index];
    let rest = candidates
        .iter()
        .map(|(other, _)| clauses[*other].clone())
        .collect::<Vec<_>>();
    let mut branches = Vec::with_capacity(clause.len());
    for (disjunct, closed) in clause.iter().zip(dead) {
        branches.push(match closed {
            Some(proof) => proof,
            None => {
                let mut extended = units.to_vec();
                extended.extend(disjunct.iter().cloned());
                search_cases(&extended, &rest, budget)?
            }
        });
    }
    Some(Refutation::Cases {
        clause: clause.clone(),
        branches,
    })
}

fn verify_refutation(context: &[Constraint], proof: &Refutation) -> bool {
    verify_with_clauses(context, &[], proof)
}

/// Like [`verify_refutation`], with disjunctive clauses available to `Cases`.
fn verify_with_clauses(context: &[Constraint], clauses: &[Dnf], proof: &Refutation) -> bool {
    match proof {
        Refutation::Cases { clause, branches } => {
            clauses.contains(clause)
                && clause.len() == branches.len()
                && clause.iter().zip(branches).all(|(disjunct, branch)| {
                    let mut extended = context.to_vec();
                    extended.extend(disjunct.iter().cloned());
                    verify_with_clauses(&extended, clauses, branch)
                })
        }
        _ => verify_refutation_leaf(context, proof),
    }
}

fn verify_refutation_leaf(context: &[Constraint], proof: &Refutation) -> bool {
    match proof {
        Refutation::Cases { .. } => false,
        Refutation::Trivial => false,
        Refutation::Farkas(farkas) => verify_farkas(context, farkas),
        Refutation::Cut {
            steps,
            multipliers,
            divisor,
            result,
            then,
        } => verify_cut(context, steps, multipliers, *divisor, result, then),
        Refutation::Branch {
            variable,
            threshold,
            left,
            right,
        } => verify_branch(context, *variable, *threshold, left, right),
    }
}

/// Independent certificate check. A `Trivial` goal is a non-negative constant.
/// Otherwise the certificate must refute the hypotheses together with the
/// integer negation of the goal. Each Farkas leaf is a non-negative rational
/// combination with a negative bound; each cut must be a non-negative integer
/// combination whose coefficients have exactly the recorded gcd and whose bound
/// is the recorded floor; each branch must refute both integer halves.
pub fn verify(certificate: &Certificate) -> bool {
    if let Some(goal) = &certificate.goal_formula {
        // The verifier negates the formula goal itself.
        let Some(negated) = negated_goal(goal) else {
            return false;
        };
        let mut clauses = certificate.clauses.clone();
        clauses.extend(negated);
        return verify_with_clauses(&certificate.hypotheses, &clauses, &certificate.proof);
    }
    if !certificate.clauses.is_empty() {
        return false;
    }
    match &certificate.proof {
        Refutation::Trivial => {
            certificate.goal.coefficients.is_empty() && certificate.goal.bound >= 0
        }
        proof => {
            let Some(negated) = negation(&certificate.goal) else {
                return false;
            };
            let mut context = certificate.hypotheses.clone();
            context.push(negated);
            verify_refutation(&context, proof)
        }
    }
}

pub(crate) fn describe(term: Term, names: &dyn Fn(usize) -> String) -> String {
    match term {
        Term::Zero => "0".into(),
        Term::Var(slot, _) => names(slot),
        Term::Len(slot, _) => format!("len({})", names(slot)),
        Term::Path(id) => {
            let (root, steps) = path_of(id);
            let mut text = match root {
                Root::Var(slot, _) => names(slot),
                Root::Value(value) => format!("call#{value}"),
            };
            for step in steps {
                text.push_str(&match step {
                    Step::Field(offset) => format!(".field@{offset}"),
                    Step::Tag => ".tag".to_owned(),
                    Step::Payload(variant, offset) => format!(".payload{variant}@{offset}"),
                });
            }
            text
        }
    }
}

fn describe_constraint(constraint: &Constraint, names: &dyn Fn(usize) -> String) -> String {
    if constraint.coefficients.is_empty() {
        return format!("0 <= {}", constraint.bound);
    }
    let terms = constraint
        .coefficients
        .iter()
        .map(|(term, coefficient)| {
            let term = describe(*term, names);
            if *coefficient == 1 {
                term
            } else {
                format!("{coefficient}*{term}")
            }
        })
        .collect::<Vec<_>>()
        .join(" + ");
    format!("{terms} <= {}", constraint.bound)
}

pub(crate) fn failure(
    span: Span,
    obligation: &str,
    known: &[Constraint],
    names: &dyn Fn(usize) -> String,
) -> Diagnostic {
    let facts = known
        .iter()
        .filter(|c| {
            !c.coefficients
                .iter()
                .all(|(term, coefficient)| matches!(term, Term::Len(..)) && *coefficient == -1)
        })
        .map(|constraint| describe_constraint(constraint, names))
        .collect::<Vec<_>>();
    Diagnostic::new(
        span,
        format!(
            "cannot prove '{obligation}' here; known facts: {}. Add a check such as 'if ... {{ }}' or an early return that establishes it",
            if facts.is_empty() {
                "none".to_owned()
            } else {
                facts.join(", ")
            }
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inequality(coefficients: &[(Term, i128)], bound: i128) -> Constraint {
        Constraint {
            coefficients: coefficients.iter().copied().collect(),
            bound,
        }
    }

    fn certificate(hypotheses: Vec<Constraint>, goal: Constraint) -> Certificate {
        let proof = prove_with(&hypotheses, &goal).expect("linear implication");
        Certificate {
            span: Span::default(),
            obligation: "test".to_owned(),
            goal,
            proof: Refutation::Farkas(proof),
            hypotheses,
            clauses: Vec::new(),
            goal_formula: None,
        }
    }

    fn integer_certificate(
        hypotheses: Vec<Constraint>,
        goal: Constraint,
        budget: IntegerBudget,
    ) -> Option<Certificate> {
        let proof = prove_integer_with(&hypotheses, &goal, budget)?;
        Some(Certificate {
            span: Span::default(),
            obligation: "test".to_owned(),
            goal,
            proof,
            hypotheses,
            clauses: Vec::new(),
            goal_formula: None,
        })
    }

    #[test]
    fn case_split_certificates_are_checked_against_their_clauses() {
        // x <= 0 || x >= 10, together with 1 <= x <= 9, is contradictory.
        let x = Term::Var(0, 0);
        let mut facts = Facts::default();
        facts.add(vec![inequality(&[(x, -1)], -1), inequality(&[(x, 1)], 9)]);
        facts.add_formula(vec![
            vec![inequality(&[(x, 1)], 0)],
            vec![inequality(&[(x, -1)], -10)],
        ]);
        let goal = vec![vec![Constraint {
            coefficients: BTreeMap::new(),
            bound: -1,
        }]];
        let mut certificates = facts.certify(&goal, Span::default(), "false").unwrap();
        let mut certificate = certificates.remove(0);
        assert!(verify(&certificate));
        // A clause that is not available is rejected.
        let Refutation::Cases { clause, .. } = &mut certificate.proof else {
            panic!("expected a case split");
        };
        clause.pop();
        assert!(!verify(&certificate));
        // A missing branch is rejected.
        let mut certificates = facts.certify(&goal, Span::default(), "false").unwrap();
        let mut certificate = certificates.remove(0);
        let Refutation::Cases { branches, .. } = &mut certificate.proof else {
            panic!("expected a case split");
        };
        branches.pop();
        assert!(!verify(&certificate));
        // Dropping the clause from the hypotheses is rejected.
        let mut certificates = facts.certify(&goal, Span::default(), "false").unwrap();
        let mut certificate = certificates.remove(0);
        certificate.clauses.clear();
        assert!(!verify(&certificate));
    }

    #[test]
    fn independent_verifier_accepts_a_valid_linear_certificate() {
        let x = Term::Var(0, 0);
        let hypotheses = vec![inequality(&[(x, 2)], 4)];
        let goal = inequality(&[(x, 1)], 2);
        let certificate = certificate(hypotheses, goal);
        assert!(verify(&certificate));
        assert!(certificate.verify());
    }

    #[test]
    fn independent_verifier_rejects_tampered_multipliers_and_bounds() {
        let x = Term::Var(0, 0);
        let hypotheses = vec![inequality(&[(x, 2)], 4)];
        let goal = inequality(&[(x, 1)], 2);
        let good = certificate(hypotheses, goal);
        assert!(verify(&good));

        let mut tampered = good.clone();
        match &mut tampered.proof {
            Refutation::Farkas(proof) => proof.multipliers[0] += 1,
            _ => panic!("expected a Farkas certificate"),
        }
        assert!(!verify(&tampered));

        let mut wrong_goal = good;
        wrong_goal.goal = inequality(&[(x, 1)], 1);
        assert!(!verify(&wrong_goal));
    }

    #[test]
    fn integer_gap_is_closed_by_a_verified_cut() {
        // 2*x == 1 is rationally feasible at x = 1/2 but has no integer
        // solution. The goal 2*x <= 0 follows only after rounding 2*x <= 1.
        let x = Term::Var(0, 0);
        let hypotheses = vec![inequality(&[(x, 2)], 1), inequality(&[(x, -2)], -1)];
        let goal = inequality(&[(x, 2)], 0);
        let good = integer_certificate(hypotheses.clone(), goal.clone(), IntegerBudget::standard())
            .expect("integer refutation");
        assert!(verify(&good));
        assert!(
            matches!(&good.proof, Refutation::Cut { .. }),
            "expected a rounding cut, got {:?}",
            good.proof
        );

        let mut bad_divisor = good.clone();
        match &mut bad_divisor.proof {
            Refutation::Cut { divisor, .. } => *divisor += 1,
            _ => unreachable!(),
        }
        assert!(!verify(&bad_divisor));

        let mut bad_result = good;
        match &mut bad_result.proof {
            Refutation::Cut { result, .. } => result.bound += 1,
            _ => unreachable!(),
        }
        assert!(!verify(&bad_result));
    }

    #[test]
    fn integer_gap_is_closed_by_a_verified_branch_when_cuts_are_disabled() {
        let x = Term::Var(0, 0);
        let hypotheses = vec![inequality(&[(x, 2)], 1), inequality(&[(x, -2)], -1)];
        let goal = inequality(&[(x, 2)], 0);
        let mut budget = IntegerBudget::standard();
        budget.cuts = 0;
        let good = integer_certificate(hypotheses, goal, budget).expect("integer refutation");
        assert!(verify(&good));
        assert!(
            matches!(&good.proof, Refutation::Branch { .. }),
            "expected a branch, got {:?}",
            good.proof
        );

        let mut bad_threshold = good;
        match &mut bad_threshold.proof {
            Refutation::Branch { threshold, .. } => *threshold += 1,
            _ => unreachable!(),
        }
        assert!(!verify(&bad_threshold));
    }

    #[test]
    fn integer_budget_exhaustion_returns_no_proof() {
        let x = Term::Var(0, 0);
        let hypotheses = vec![inequality(&[(x, 2)], 1), inequality(&[(x, -2)], -1)];
        let goal = inequality(&[(x, 2)], 0);
        let budget = IntegerBudget {
            nodes: 0,
            cuts: 0,
            cut_rounds: 0,
        };
        assert!(integer_certificate(hypotheses, goal, budget).is_none());
    }

    #[test]
    fn difference_shaped_facts_still_prove_and_refute() {
        let x = Term::Var(0, 0);
        let y = Term::Var(1, 0);
        let hypotheses = vec![
            inequality(&[(x, 1), (y, -1)], 2),
            inequality(&[(y, 1), (x, -1)], 1),
        ];
        // y - x <= 1 does not imply x - y <= 0.
        assert!(prove_with(&hypotheses, &inequality(&[(x, 1), (y, -1)], 0)).is_none());
        // Together they imply 2 <= 3, a trivially constant goal.
        assert!(prove_with(&hypotheses, &inequality(&[], 3)).is_some());
    }
}
