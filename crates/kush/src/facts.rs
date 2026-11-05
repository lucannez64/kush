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
    /// Each atom: left linear expression, comparison, right linear expression.
    pub atoms: Vec<(ParamLinear, Kind, ParamLinear)>,
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
}

/// A discharged obligation and the facts that justify it.
#[derive(Debug, Clone)]
pub struct Certificate {
    pub span: Span,
    pub obligation: String,
    pub(crate) goal: Constraint,
    pub(crate) proof: Refutation,
    pub(crate) hypotheses: Vec<Constraint>,
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
}

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
            }
        }
        result
    }

    pub fn mark(&self) -> usize {
        self.known.len()
    }
    pub fn reset(&mut self, mark: usize) {
        self.known.truncate(mark);
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
    }
    pub fn add(&mut self, constraints: impl IntoIterator<Item = Constraint>) {
        self.known.extend(constraints);
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
            _ => {}
        }
    }
    /// A checked i64 expression as a linear term, when it has that shape.
    /// Integer constants, locals, lengths, unary negation, `+`/`-`, and
    /// multiplication by an integer constant are admitted. Anything else (for
    /// example `x * y` or a float) is not reinterpreted.
    pub fn linear(&self, expr: &Expr) -> Option<Linear> {
        if expr.ty != crate::executable::Type::I64 {
            return None;
        }
        match &expr.kind {
            ExprKind::Constant(n) => Some(Linear::constant(i128::from(*n))),
            ExprKind::Local(slot) | ExprKind::Peek(slot) if !self.opaque.contains(slot) => {
                Some(Linear::variable(Term::Var(*slot, self.version(*slot))))
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
            _ => None,
        }
    }
    /// `slot = value`: the right side is read at the old version, then the
    /// slot moves to a new version equal to it.
    pub fn assign(&mut self, slot: usize, value: &Expr) {
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
        if let Some(value) = self.linear(value).filter(|_| !self.opaque.contains(&slot)) {
            let var = Linear::variable(Term::Var(slot, self.version(slot)));
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
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
        if goal.coefficients.is_empty() {
            return (goal.bound >= 0).then_some(Refutation::Trivial);
        }
        let hypotheses = self.snapshot_universal();
        if let Some(proof) = prove_with(&hypotheses, goal) {
            return Some(Refutation::Farkas(proof));
        }
        prove_integer(&hypotheses, goal)
    }
    fn implicit(&self, goal: &Constraint) -> Vec<Constraint> {
        let mut terms = goal.coefficients.keys().copied().collect::<Vec<_>>();
        for c in &self.known {
            terms.extend(c.coefficients.keys().copied());
        }
        terms.sort();
        terms.dedup();
        terms
            .into_iter()
            .filter(|t| matches!(t, Term::Len(..)))
            .map(|term| {
                let mut coefficients = BTreeMap::new();
                coefficients.insert(term, -1);
                Constraint {
                    coefficients,
                    bound: 0,
                }
            })
            .collect()
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

/// Turn a contradictory row into a Farkas certificate over `sources`, whose
/// indices are the row origins.
fn farkas_from_conflict(conflict: &Row, sources: &[Constraint]) -> Option<Farkas> {
    let mut denominator = 1i128;
    for multiplier in conflict.origins.values() {
        denominator = lcm(denominator, multiplier.den);
    }
    let mut steps = Vec::new();
    let mut multipliers = Vec::new();
    for (origin, multiplier) in &conflict.origins {
        let source = sources.get(*origin)?.clone();
        let numerator = multiplier.num.checked_mul(denominator / multiplier.den)?;
        steps.push(source);
        multipliers.push(numerator);
    }
    // Reduce a common factor so certificates stay small.
    let mut divisor = denominator;
    for numerator in &multipliers {
        divisor = gcd(divisor, *numerator);
    }
    if divisor > 1 {
        denominator /= divisor;
        for numerator in &mut multipliers {
            *numerator /= divisor;
        }
    }
    Some(Farkas {
        steps,
        multipliers,
        denominator,
    })
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
    let mut rows = Vec::with_capacity(sources.len());
    for (index, source) in sources.iter().enumerate() {
        rows.push(Row::from_constraint(source, index)?);
    }
    let rows = eliminate(rows)?;
    // After eliminating every variable, every row is `0 <= bound`. A negative
    // bound is a contradiction. Prefer a contradiction that actually uses the
    // goal's negation, so the certificate is a proof of the goal rather than
    // merely an observation that the hypotheses are inconsistent.
    let conflict = rows.iter().find(|row| {
        row.coefficients.is_empty()
            && row.bound.is_negative()
            && row
                .origins
                .get(&negation_index)
                .is_some_and(|multiplier| multiplier.is_positive())
    })?;
    farkas_from_conflict(conflict, &sources)
}

/// Refute a complete integer system without a distinguished goal. This is the
/// leaf rule used by the integer fallback: any negative constant consequence
/// of the available constraints is a contradiction.
fn refute_rational(system: &[Constraint]) -> Option<Farkas> {
    let mut rows = Vec::with_capacity(system.len());
    for (index, constraint) in system.iter().enumerate() {
        rows.push(Row::from_constraint(constraint, index)?);
    }
    let rows = eliminate(rows)?;
    let conflict = rows
        .iter()
        .find(|row| row.coefficients.is_empty() && row.bound.is_negative())?;
    farkas_from_conflict(conflict, system)
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
    solve_integer(&system, MAX_INTEGER_DEPTH, &mut budget)
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

fn verify_refutation(context: &[Constraint], proof: &Refutation) -> bool {
    match proof {
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
        })
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
