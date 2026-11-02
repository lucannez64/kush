//! Erased proof obligations for executable code.
//!
//! Propositions are conjunctions of integer comparisons between linear terms
//! (`x + c`, `len(xs) + c`, constants). Every comparison becomes difference
//! constraints `a - b <= k`. Facts come from branch conditions, guards, loop
//! conditions, early exits, and erased parameters. An obligation is discharged
//! when a chain of facts sums to the required bound; that chain is recorded as
//! a certificate and checked again by [`verify`], which does not use the search.
//!
//! Soundness relies on: checked i64 arithmetic (a computed value is its
//! mathematical value), immutable or versioned locals (assignment bumps a
//! version so stale facts no longer match), and immutable borrows (a borrowed
//! buffer's length cannot change during a call).
use crate::{
    Diagnostic, Span,
    executable::{BytesOp, Expr, ExprKind, SliceOp, Target, VecOp},
    lexer::Kind,
};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Term {
    Zero,
    /// An i64 local at a version.
    Var(usize, u32),
    /// The length of the Bytes/Vec owned by (or borrowed through) a local.
    Len(usize, u32),
}
/// `a - b <= bound`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Constraint {
    pub a: Term,
    pub b: Term,
    pub bound: i128,
}
/// A comparison between symbolic linear terms over a callee's parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParamTerm {
    Zero,
    Param(usize),
    Len(usize),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proposition {
    /// Each atom: (left term, left offset, op, right term, right offset).
    pub atoms: Vec<(ParamTerm, i128, Kind, ParamTerm, i128)>,
    pub text: String,
}
/// A discharged obligation and the facts that justify it.
#[derive(Debug, Clone)]
pub struct Certificate {
    pub span: Span,
    pub obligation: String,
    pub(crate) goal: Constraint,
    pub(crate) steps: Vec<Constraint>,
    pub(crate) hypotheses: Vec<Constraint>,
}
#[derive(Debug, Default, Clone)]
pub(crate) struct Facts {
    known: Vec<Constraint>,
    versions: BTreeMap<usize, u32>,
}
/// A linear term `term + offset`, or a constant when `term` is Zero.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Linear(pub Term, pub i128);

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
    pub fn linear(&self, expr: &Expr) -> Option<Linear> {
        match &expr.kind {
            ExprKind::Constant(n) if expr.ty == crate::executable::Type::I64 => {
                Some(Linear(Term::Zero, i128::from(*n)))
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot)
                if expr.ty == crate::executable::Type::I64 =>
            {
                Some(Linear(Term::Var(*slot, self.version(*slot)), 0))
            }
            ExprKind::Unary(Kind::Minus, inner) => match self.linear(inner)? {
                Linear(Term::Zero, n) => Some(Linear(Term::Zero, -n)),
                _ => None,
            },
            ExprKind::Binary(op @ (Kind::Plus | Kind::Minus), l, r) => {
                let (l, r) = (self.linear(l)?, self.linear(r)?);
                let sign = if *op == Kind::Plus { 1 } else { -1 };
                match (l, r) {
                    (Linear(t, a), Linear(Term::Zero, b)) => Some(Linear(t, a + sign * b)),
                    (Linear(Term::Zero, a), Linear(t, b)) if sign == 1 => Some(Linear(t, a + b)),
                    _ => None,
                }
            }
            ExprKind::Call(
                Target::Bytes(BytesOp::Len)
                | Target::Vec(VecOp::Len, _)
                | Target::Slice(SliceOp::Len, _),
                arguments,
            ) => {
                let slot = owner_slot(&arguments[0])?;
                Some(Linear(Term::Len(slot, self.version(slot)), 0))
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
            let var = Linear(Term::Var(slot, self.version(slot)), 0);
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
        }
    }
    /// Facts for a new binding `slot = value` at the slot's current version.
    pub fn define(&mut self, slot: usize, value: &Expr) {
        if let Some(value) = self.linear(value) {
            let var = Linear(Term::Var(slot, self.version(slot)), 0);
            let mut out = Vec::new();
            compare(var, &Kind::EqEq, value, &mut out);
            self.known.extend(out);
        }
    }
    /// Tightest proven `to - from <= d`, if any.
    pub fn distance(&self, from: Term, to: Term) -> Option<i128> {
        let known = self.snapshot(Constraint {
            a: to,
            b: from,
            bound: 0,
        });
        let mut dist: BTreeMap<Term, i128> = BTreeMap::new();
        dist.insert(from, 0);
        for _ in 0..=known.len() {
            let mut changed = false;
            for c in &known {
                if let Some(&d) = dist.get(&c.b) {
                    let candidate = d + c.bound;
                    if dist.get(&c.a).is_none_or(|old| candidate < *old) {
                        dist.insert(c.a, candidate);
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
            self.known.push(if increasing {
                Constraint {
                    a: Term::Zero,
                    b: new,
                    bound,
                }
            } else {
                Constraint {
                    a: new,
                    b: Term::Zero,
                    bound,
                }
            });
        }
    }
    /// Try to prove `goal`; returns the chain of facts on success.
    pub fn prove(&self, goal: Constraint) -> Option<Vec<Constraint>> {
        let mut known = self.known.clone();
        known.extend(self.implicit(goal));
        search(&known, goal)
    }
    /// Lengths are never negative.
    fn implicit(&self, goal: Constraint) -> Vec<Constraint> {
        let mut terms = vec![goal.a, goal.b];
        for c in &self.known {
            terms.push(c.a);
            terms.push(c.b);
        }
        terms.sort();
        terms.dedup();
        terms
            .into_iter()
            .filter(|t| matches!(t, Term::Len(..)))
            .map(|t| Constraint {
                a: Term::Zero,
                b: t,
                bound: 0,
            })
            .collect()
    }
    pub fn snapshot(&self, goal: Constraint) -> Vec<Constraint> {
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
/// Translate `l op r` into difference constraints.
pub(crate) fn compare(l: Linear, op: &Kind, r: Linear, out: &mut Vec<Constraint>) {
    // l.t + l.c  op  r.t + r.c   ==>   l.t - r.t  op  r.c - l.c
    let le = |a: Linear, b: Linear, strict: bool| Constraint {
        a: a.0,
        b: b.0,
        bound: b.1 - a.1 - i128::from(strict),
    };
    match op {
        Kind::Lt => out.push(le(l, r, true)),
        Kind::Le => out.push(le(l, r, false)),
        Kind::Gt => out.push(le(r, l, true)),
        Kind::Ge => out.push(le(r, l, false)),
        Kind::EqEq => {
            out.push(le(l, r, false));
            out.push(le(r, l, false));
        }
        _ => {}
    }
}
/// Bellman-Ford shortest path from `goal.b` to `goal.a` over edges
/// `b -> a` of weight `bound`. A path of total weight <= goal.bound proves it.
/// A reachable negative cycle means the facts are contradictory (dead code).
fn search(known: &[Constraint], goal: Constraint) -> Option<Vec<Constraint>> {
    if goal.a == goal.b {
        return (goal.bound >= 0).then(Vec::new);
    }
    let mut dist: BTreeMap<Term, (i128, Option<usize>)> = BTreeMap::new();
    dist.insert(goal.b, (0, None));
    let rounds = known.len() + 1;
    for _ in 0..rounds {
        let mut changed = false;
        for (index, c) in known.iter().enumerate() {
            if let Some(&(d, _)) = dist.get(&c.b) {
                let candidate = d + c.bound;
                if dist.get(&c.a).is_none_or(|(old, _)| candidate < *old) {
                    dist.insert(c.a, (candidate, Some(index)));
                    changed = true;
                }
            }
        }
        if !changed {
            let (d, _) = *dist.get(&goal.a)?;
            if d > goal.bound {
                return None;
            }
            let mut steps = Vec::new();
            let mut at = goal.a;
            while at != goal.b {
                let index = dist[&at].1?;
                steps.push(known[index]);
                at = known[index].b;
                if steps.len() > known.len() {
                    return None;
                }
            }
            steps.reverse();
            return Some(steps);
        }
    }
    None // negative cycle: contradictory facts; refuse rather than exploit
}
/// Independent certificate check: every step is a hypothesis, the steps form
/// a chain from `goal.b` to `goal.a`, and their bounds sum to at most the goal.
pub fn verify(certificate: &Certificate) -> bool {
    let goal = certificate.goal;
    let mut at = goal.b;
    let mut total = 0i128;
    for step in &certificate.steps {
        if !certificate.hypotheses.contains(step) || step.b != at {
            return false;
        }
        total += step.bound;
        at = step.a;
    }
    at == goal.a && total <= goal.bound
}
pub(crate) fn describe(term: Term, names: &dyn Fn(usize) -> String) -> String {
    match term {
        Term::Zero => "0".into(),
        Term::Var(slot, _) => names(slot),
        Term::Len(slot, _) => format!("len({})", names(slot)),
    }
}
pub(crate) fn failure(
    span: Span,
    obligation: &str,
    known: &[Constraint],
    names: &dyn Fn(usize) -> String,
) -> Diagnostic {
    let facts = known
        .iter()
        .filter(|c| !matches!((c.a, c.b), (Term::Zero, Term::Len(..))))
        .map(|c| {
            format!(
                "{} - {} <= {}",
                describe(c.a, names),
                describe(c.b, names),
                c.bound
            )
        })
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
