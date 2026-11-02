//! Erased proof obligations for executable code.
//!
//! Propositions are conjunctions of integer comparisons between **linear
//! expressions** over runtime scalar terms (`x`, `x + c`, `c * x`,
//! `len(xs) + c`). Every comparison becomes a linear inequality
//! `sum coefficient * term <= bound`. Facts come from branch conditions,
//! guards, loop conditions, early exits, and erased parameters.
//!
//! Discharging an obligation uses Fourier–Motzkin elimination over exact
//! rational coefficients. The solver returns a refutation of the hypotheses
//! together with the integer negation of the goal; the certificate records the
//! non-negative multipliers of every hypothesis and of that negation.
//! [`verify`] checks the combination independently of the search that produced
//! it. If the hypotheses and the negation derive `0 <= negative`, the goal holds
//! for every *integer* assignment (all admitted terms are integer-valued).
//!
//! Soundness relies on: checked i64 arithmetic (a computed value is its
//! mathematical value), immutable or versioned locals (assignment bumps a
//! version so stale facts no longer match), and immutable borrows (a borrowed
//! buffer's length cannot change during a call).
//!
//! The fragment is deliberately bounded. Elimination drops the eliminated
//! variable existentially, which is complete for rational feasibility but not
//! a full integer Presburger decision procedure: facts that need cutting
//! planes (for example `2*x <= 1` implying `x <= 0`) are not proved by the
//! rational relaxation alone. The search also has explicit row, pair, and
//! coefficient budgets; exceeding one means "not established", never a guessed
//! proof.
use crate::{
    Diagnostic, Span,
    executable::{BytesOp, Expr, ExprKind, SliceOp, Target, VecOp},
    lexer::Kind,
};
use std::collections::BTreeMap;

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

/// The search result behind one discharged obligation. The certificate keeps
/// the non-negative rational multipliers of the hypotheses and of the integer
/// negation of the goal.
#[derive(Debug, Clone)]
pub(crate) struct Proof {
    pub steps: Vec<Constraint>,
    pub multipliers: Vec<i128>,
    pub denominator: i128,
    /// Index in `steps` of the negation of the goal.
    pub negation: usize,
}

/// A discharged obligation and the facts that justify it.
#[derive(Debug, Clone)]
pub struct Certificate {
    pub span: Span,
    pub obligation: String,
    pub(crate) goal: Constraint,
    pub(crate) steps: Vec<Constraint>,
    pub(crate) multipliers: Vec<i128>,
    pub(crate) denominator: i128,
    pub(crate) negation: usize,
    pub(crate) hypotheses: Vec<Constraint>,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Facts {
    known: Vec<Constraint>,
    versions: BTreeMap<usize, u32>,
}

/// Bounds for the Fourier–Motzkin search. These are work limits, not a claim of
/// completeness: a system beyond them is reported as not established.
const MAX_FM_ROWS: usize = 4096;
const MAX_FM_PAIRS: usize = 200_000;
const MAX_FM_TERMS: usize = 64;

impl Facts {
    pub fn same_versions(&self, other: &Self) -> bool {
        self.versions == other.versions
    }
    /// Sibling branches start from identical versions. A join forgets facts
    /// about every value changed on either path.
    pub fn branch_join(base: &Self, left: &Self, right: &Self) -> Self {
        let mut result = base.clone();
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
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
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
                let slot = owner_slot(&arguments[0])?;
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
        if let Some(value) = value {
            let var = Linear::variable(Term::Var(slot, self.version(slot)));
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
        }
    }
    /// Facts for a new binding `slot = value` at the slot's current version.
    pub fn define(&mut self, slot: usize, value: &Expr) {
        if let Some(value) = self.linear(value) {
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
    /// Try to prove `goal`; returns a Farkas-style refutation certificate.
    pub fn prove(&self, goal: &Constraint) -> Option<Proof> {
        let hypotheses = self.snapshot_universal();
        prove_with(&hypotheses, goal)
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

fn prove_with(hypotheses: &[Constraint], goal: &Constraint) -> Option<Proof> {
    if goal.coefficients.is_empty() {
        return (goal.bound >= 0).then(|| Proof {
            steps: Vec::new(),
            multipliers: Vec::new(),
            denominator: 1,
            negation: 0,
        });
    }
    let negated = negation(goal)?;
    let mut rows = Vec::with_capacity(hypotheses.len() + 1);
    for hypothesis in hypotheses {
        rows.push(Row::from_constraint(hypothesis, rows.len())?);
    }
    let negation_index = rows.len();
    rows.push(Row::from_constraint(&negated, negation_index)?);
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
                let weight_low = up_coefficient.abs();
                let weight_up = low_coefficient.abs();
                let combined = up.combine(low, weight_up, weight_low, &variable)?;
                next.push(combined);
            }
        }
        rows = next;
    }
    // After eliminating every variable, every row is `0 <= bound`. A negative
    // bound is a contradiction. Prefer a contradiction that actually uses the
    // goal's negation, so the certificate is a proof of the goal rather than
    // merely an observation that the hypotheses are inconsistent.
    let mut conflict = None;
    for row in &rows {
        if !row.coefficients.is_empty() {
            continue;
        }
        if row.bound.is_negative()
            && row
                .origins
                .get(&negation_index)
                .is_some_and(|multiplier| multiplier.is_positive())
        {
            conflict = Some(row);
            break;
        }
    }
    let conflict = conflict?;
    let mut denominator = 1i128;
    for multiplier in conflict.origins.values() {
        denominator = lcm(denominator, multiplier.den);
    }
    let mut steps = Vec::new();
    let mut multipliers = Vec::new();
    let mut used_negation = None;
    for (origin, multiplier) in &conflict.origins {
        let source = if *origin == negation_index {
            used_negation = Some(steps.len());
            negated.clone()
        } else {
            hypotheses.get(*origin)?.clone()
        };
        let numerator = multiplier.num.checked_mul(denominator / multiplier.den)?;
        steps.push(source);
        multipliers.push(numerator);
    }
    let negation = used_negation?;
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
    Some(Proof {
        steps,
        multipliers,
        denominator,
        negation,
    })
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
    fn abs(self) -> Self {
        Ratio {
            num: self.num.abs(),
            den: self.den,
        }
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
        let divisor = gcd(num.abs(), den);
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

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a.abs().max(1)
}

fn lcm(a: i128, b: i128) -> i128 {
    let divisor = gcd(a, b);
    a / divisor * b
}

/// Independent certificate check: every step is a hypothesis or the integer
/// negation of the goal, all multipliers are non-negative, the scaled
/// coefficients cancel exactly, and the scaled bounds sum to a negative value.
pub fn verify(certificate: &Certificate) -> bool {
    if certificate.steps.is_empty() {
        return certificate.goal.coefficients.is_empty() && certificate.goal.bound >= 0;
    }
    if certificate.denominator <= 0
        || certificate.steps.len() != certificate.multipliers.len()
        || certificate.negation >= certificate.steps.len()
        || certificate
            .multipliers
            .iter()
            .any(|multiplier| *multiplier < 0)
    {
        return false;
    }
    let Some(negated) = negation(&certificate.goal) else {
        return false;
    };
    if certificate.steps[certificate.negation] != negated
        || certificate.multipliers[certificate.negation] <= 0
    {
        return false;
    }
    for (index, step) in certificate.steps.iter().enumerate() {
        if index != certificate.negation && !certificate.hypotheses.contains(step) {
            return false;
        }
    }
    let mut coefficients: BTreeMap<Term, i128> = BTreeMap::new();
    let mut bound = 0i128;
    for (step, multiplier) in certificate.steps.iter().zip(&certificate.multipliers) {
        let Some(scaled_bound) = step.bound.checked_mul(*multiplier) else {
            return false;
        };
        let Some(next) = bound.checked_add(scaled_bound) else {
            return false;
        };
        bound = next;
        for (term, coefficient) in &step.coefficients {
            let Some(scaled) = coefficient.checked_mul(*multiplier) else {
                return false;
            };
            let entry = coefficients.entry(*term).or_insert(0);
            let Some(next) = entry.checked_add(scaled) else {
                return false;
            };
            *entry = next;
        }
    }
    coefficients.values().all(|coefficient| *coefficient == 0) && bound < 0
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
