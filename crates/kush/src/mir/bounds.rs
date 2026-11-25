//! Upper-bound facts (FND-MIR-BOUNDS, docs/mir-design.md section 8).
//!
//! A slice element call checks `0 <= index < len`. Where a dominating test
//! already established `index < len(view)` for the same index and view,
//! the upper half is redundant: the call is marked `below`, and native code
//! keeps only the sign check (a negative index passes a signed `<`).
//!
//! A forward must-analysis carries, per program point:
//! - temporaries known to hold a local's value, a slice local's length, or
//!   the result of `local < len(view)`;
//! - facts `index < len(view)`, made on the nonzero edge of a switch on such
//!   a comparison.
//!
//! An assignment to a local forgets everything that mentions it. Locals
//! whose address the body takes are never tracked, since a store through a
//! reference could change them unseen.

use super::loops::{address_taken, reverse_postorder, successors};
use super::*;
use crate::executable::{SliceOp, Target};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq)]
enum Known {
    /// A copy of the local's value.
    Copy(LocalId),
    /// The length of the slice in the local.
    Length(LocalId),
    /// Whether `index < len(view)`.
    Below(LocalId, LocalId),
}

impl Known {
    fn mentions(self, local: LocalId) -> bool {
        match self {
            Known::Copy(other) | Known::Length(other) => other == local,
            Known::Below(index, view) => index == local || view == local,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
struct State {
    known: BTreeMap<LocalId, Known>,
    /// `(index, view)`: `index < len(view)` holds.
    facts: BTreeSet<(LocalId, LocalId)>,
}

impl State {
    fn meet(&mut self, other: &State) {
        self.known
            .retain(|local, known| other.known.get(local) == Some(known));
        self.facts.retain(|fact| other.facts.contains(fact));
    }
    fn kill(&mut self, local: LocalId) {
        self.known
            .retain(|temp, known| *temp != local && !known.mentions(local));
        self.facts
            .retain(|(index, view)| *index != local && *view != local);
    }
}

struct Analysis<'b> {
    body: &'b Body,
    /// Locals that can be tracked: not address-taken.
    tracked: Vec<bool>,
}

impl Analysis<'_> {
    /// The tracked local an operand reads the value of, directly or
    /// through a temporary copy.
    fn local(&self, state: &State, operand: Operand) -> Option<LocalId> {
        let place = operand.place()?;
        if place.deref || place.field.is_some() || !self.tracked[place.local] {
            return None;
        }
        if !self.body.locals[place.local].temporary {
            return Some(place.local);
        }
        match state.known.get(&place.local)? {
            Known::Copy(local) => Some(*local),
            _ => None,
        }
    }
    fn known(&self, state: &State, operand: Operand) -> Option<Known> {
        let place = operand.place()?;
        if place.deref || place.field.is_some() {
            return None;
        }
        state.known.get(&place.local).copied()
    }
    fn statement(&self, state: &mut State, statement: &Statement) {
        let StatementKind::Assign(place, rvalue) = &statement.kind;
        if place.deref {
            return;
        }
        state.kill(place.local);
        if place.field.is_some() || !self.body.locals[place.local].temporary {
            return;
        }
        let known = match rvalue {
            Rvalue::Use(operand) => self
                .known(state, *operand)
                .filter(|known| !matches!(known, Known::Below(..)))
                .or_else(|| self.local(state, *operand).map(Known::Copy)),
            Rvalue::Binary(BinOp::Lt, left, right) => {
                match (self.local(state, *left), self.known(state, *right)) {
                    (Some(index), Some(Known::Length(view))) => Some(Known::Below(index, view)),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(known) = known
            && !known.mentions(place.local)
        {
            state.known.insert(place.local, known);
        }
    }
    /// The state at the end of a block, before its terminator's edges.
    fn transfer(&self, block: BlockId, mut state: State) -> State {
        let data = &self.body.blocks[block];
        for statement in &data.statements {
            self.statement(&mut state, statement);
        }
        state
    }
    /// The state along the edge from `block` (with `state` at its end) to
    /// `target`.
    fn edge(&self, block: BlockId, state: &State, target: BlockId) -> State {
        let mut out = state.clone();
        match &self.body.blocks[block].terminator.kind {
            TerminatorKind::Call {
                callee,
                args,
                destination,
                ..
            } => {
                let length = match callee {
                    Callee::Builtin { index, .. } => {
                        matches!(self.body.builtins.0[*index], Target::Slice(SliceOp::Len, _))
                    }
                    _ => false,
                };
                let view = match args.as_slice() {
                    [view] if length => self.local(state, *view),
                    _ => None,
                };
                out.kill(*destination);
                if let Some(view) = view
                    && self.body.locals[*destination].temporary
                {
                    out.known.insert(*destination, Known::Length(view));
                }
            }
            TerminatorKind::Switch {
                value,
                targets,
                otherwise,
            } => {
                let zero = targets.iter().all(|(case, _)| *case == 0);
                if zero
                    && target == *otherwise
                    && targets.iter().all(|(_, other)| *other != target)
                    && let Some(Known::Below(index, view)) = self.known(state, *value)
                {
                    out.facts.insert((index, view));
                }
            }
            _ => {}
        }
        out
    }
}

/// Mark the slice element calls whose index is known to be below the
/// slice's length. Returns how many it marked.
pub(crate) fn mark(body: &mut Body) -> usize {
    let taken = address_taken(body);
    let analysis = Analysis {
        body,
        tracked: (0..body.locals.len())
            .map(|local| !taken.contains(&local))
            .collect(),
    };
    let order = reverse_postorder(body);
    let mut entry: Vec<Option<State>> = vec![None; body.blocks.len()];
    entry[0] = Some(State::default());
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &order {
            let Some(state) = entry[block].clone() else {
                continue;
            };
            let end = analysis.transfer(block, state);
            for target in successors(&body.blocks[block].terminator.kind) {
                let incoming = analysis.edge(block, &end, target);
                let merged = match &entry[target] {
                    None => incoming,
                    Some(current) => {
                        let mut merged = current.clone();
                        merged.meet(&incoming);
                        merged
                    }
                };
                if entry[target].as_ref() != Some(&merged) {
                    entry[target] = Some(merged);
                    changed = true;
                }
            }
        }
    }
    let mut marks = Vec::new();
    for (block, state) in entry.into_iter().enumerate() {
        let Some(state) = state else {
            continue;
        };
        let TerminatorKind::Call {
            callee:
                Callee::Builtin {
                    index,
                    hint: CallHint::None,
                },
            args,
            ..
        } = &body.blocks[block].terminator.kind
        else {
            continue;
        };
        if !matches!(
            body.builtins.0[*index],
            Target::Slice(SliceOp::Get | SliceOp::Set | SliceOp::TryGet { .. }, _)
        ) {
            continue;
        }
        let end = analysis.transfer(block, state);
        let (Some(view), Some(position)) = (
            args.first().and_then(|view| analysis.local(&end, *view)),
            args.get(1).and_then(|index| analysis.local(&end, *index)),
        ) else {
            continue;
        };
        if end.facts.contains(&(position, view)) {
            marks.push(block);
        }
    }
    for block in &marks {
        if let TerminatorKind::Call {
            callee: Callee::Builtin { hint, .. },
            ..
        } = &mut body.blocks[*block].terminator.kind
        {
            *hint = CallHint::Below;
        }
    }
    marks.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn marked(source: &str, name: &str) -> (Body, usize) {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some(name))
            .expect("the function");
        let mut body = build(&program, index).expect("the function builds");
        let count = mark(&mut body);
        verify(&program, &body).expect("the marked body verifies");
        let printed = text::print(&body);
        assert_eq!(text::parse(&printed).unwrap(), body, "{printed}");
        (body, count)
    }

    fn function(body: &str) -> String {
        format!(
            "fn f(xs: &[i64], n: i64) -> i64 {{
                let mut i = 0;
                let mut total = 0;
                {body}
                total
            }}
            fn main() -> Unit ! {{io}} {{ print_i64(0); }}"
        )
    }

    #[test]
    fn a_loop_test_proves_the_reads_it_guards() {
        let (body, count) = marked(
            &function("while i < xs.len() { total = total + xs[i]; i = i + 1; }"),
            "f",
        );
        assert_eq!(count, 1);
        assert!(text::print(&body).contains(" below("));
    }

    #[test]
    fn a_changed_index_or_another_bound_proves_nothing() {
        for shape in [
            // The index moves before the read.
            "while i < xs.len() { i = i + 1; total = total + xs[i]; }",
            // The test is against another bound.
            "while i < n { total = total + xs[i]; i = i + 1; }",
            // The read is on the exit path.
            "while i < xs.len() { i = i + 1; } total = xs[i];",
            // `<=` admits the length itself.
            "while i <= xs.len() { total = total + xs[i]; i = i + 1; }",
        ] {
            let (_, count) = marked(&function(shape), "f");
            assert_eq!(count, 0, "{shape}");
        }
    }

    #[test]
    fn a_branch_test_proves_the_reads_under_it() {
        let (_, count) = marked(
            &function("if i < xs.len() { total = xs[i] + xs[i]; } else { total = 1; }"),
            "f",
        );
        assert_eq!(count, 2);
    }
}
