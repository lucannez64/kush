//! Static drop-flag elimination (FND-MIR-DROP-FLAGS, docs/mir-design.md).
//!
//! The builder gives each owned resource a dynamic drop flag, as the tree
//! path does: a boolean temporary set when the resource becomes live,
//! cleared when it moves, and tested by a `switch` before each drop. Most
//! of those tests have an answer known statically. This pass computes the
//! flags' values along the CFG, turns every `switch` on a flag of known
//! value into a `goto`, and deletes the assignments of flags no `switch`
//! reads any more. A test reached with different values on different paths
//! (typically in the shared unwind cleanup) stays dynamic.

use super::*;

/// The value of one flag at a program point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Value {
    /// No path reaches the point.
    Unreached,
    Known(bool),
    Unknown,
}

impl Value {
    fn join(self, other: Value) -> Value {
        match (self, other) {
            (Value::Unreached, value) | (value, Value::Unreached) => value,
            (Value::Known(a), Value::Known(b)) if a == b => Value::Known(a),
            _ => Value::Unknown,
        }
    }
}

/// Fold the drop-flag tests of `body` whose outcome is known statically.
pub(crate) fn eliminate(body: &mut Body) {
    let flags = flag_locals(body);
    if flags.is_empty() {
        return;
    }
    let index = |local: LocalId| flags.iter().position(|flag| *flag == local);
    let states = entry_states(body, &flags, &index);
    // Fold the switches whose flag is known where they run.
    for (block, entry) in body.blocks.iter_mut().zip(&states) {
        if entry.iter().all(|value| *value == Value::Unreached) {
            continue;
        }
        let mut state = entry.clone();
        for statement in &block.statements {
            apply(statement, &mut state, &index);
        }
        if let TerminatorKind::Switch {
            value: Operand::Copy(place) | Operand::Move(place),
            targets,
            otherwise,
        } = &block.terminator.kind
            && place.field.is_none()
            && !place.deref
            && let Some(flag) = index(place.local)
            && let Value::Known(live) = state[flag]
        {
            let value = i64::from(live);
            let target = targets
                .iter()
                .find(|(case, _)| *case == value)
                .map_or(*otherwise, |(_, target)| *target);
            block.terminator.kind = TerminatorKind::Goto(target);
        }
    }
    // Drop the assignments of flags nothing tests any more.
    let tested = flags
        .iter()
        .filter(|flag| {
            body.blocks.iter().any(|block| {
                matches!(
                    &block.terminator.kind,
                    TerminatorKind::Switch {
                        value: Operand::Copy(place) | Operand::Move(place),
                        ..
                    } if place.local == **flag
                )
            })
        })
        .copied()
        .collect::<Vec<_>>();
    for block in &mut body.blocks {
        block.statements.retain(|statement| {
            let StatementKind::Assign(place, _) = &statement.kind;
            !(flags.contains(&place.local) && !tested.contains(&place.local))
        });
    }
}

/// Boolean temporaries assigned only constants and read only by `switch`.
fn flag_locals(body: &Body) -> Vec<LocalId> {
    let mut candidate = body
        .locals
        .iter()
        .map(|local| local.temporary && local.ty == Type::Bool)
        .collect::<Vec<_>>();
    let mut reject = |operand: &Operand| {
        if let Some(place) = operand.place() {
            candidate[place.local] = false;
        }
    };
    for block in &body.blocks {
        for statement in &block.statements {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            let constant = matches!(rvalue, Rvalue::Use(Operand::Constant(_, Type::Bool)));
            if !constant || place.field.is_some() || place.deref {
                reject(&Operand::Copy(Place::local(place.local)));
            }
            for operand in rvalue_operands(rvalue) {
                reject(&operand);
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Switch { value, .. } => {
                if let Some(place) = value.place()
                    && (place.field.is_some() || place.deref)
                {
                    reject(value);
                }
            }
            TerminatorKind::Call { callee, args, .. } => {
                if let Callee::Indirect(code) = callee {
                    reject(code);
                }
                for arg in args {
                    reject(arg);
                }
            }
            TerminatorKind::Return(value) => reject(value),
            TerminatorKind::Drop { place, .. } => reject(&Operand::Copy(*place)),
            TerminatorKind::Goto(_)
            | TerminatorKind::Panic { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable => {}
        }
    }
    (0..body.locals.len())
        .filter(|local| candidate[*local])
        .collect()
}

/// Every operand an rvalue reads, including places used by address.
pub(super) fn rvalue_operands(rvalue: &Rvalue) -> Vec<Operand> {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Unary(_, operand) => vec![*operand],
        Rvalue::BoxNew(operand)
        | Rvalue::BoxTake(operand)
        | Rvalue::Coerce(operand, _)
        | Rvalue::Buffer(operand, _) => {
            vec![*operand]
        }
        Rvalue::Binary(_, left, right)
        | Rvalue::ByteAt(left, right)
        | Rvalue::StructEq(left, right, _) => vec![*left, *right],
        Rvalue::Int(_, _, _, operands)
        | Rvalue::Aggregate(_, _, operands)
        | Rvalue::Task(_, operands)
        | Rvalue::Runtime(_, operands)
        | Rvalue::Alloc(_, operands)
        | Rvalue::Array(_, operands)
        | Rvalue::Map(_, operands) => operands.clone(),
        Rvalue::Bytes(_) => Vec::new(),
        Rvalue::Ref(place) => vec![Operand::Copy(*place)],
        Rvalue::ElementAddress(base, index) => {
            let base = match base {
                ElementBase::Slice(view) => *view,
                ElementBase::Stored(place) => Operand::Copy(*place),
            };
            vec![base, *index]
        }
        Rvalue::FnValue { captures, .. } => captures
            .iter()
            .map(|capture| match capture {
                Capture::Value(operand) => *operand,
                Capture::Address(local) => Operand::Copy(Place::local(*local)),
            })
            .collect(),
        Rvalue::View {
            source, start, end, ..
        } => {
            let mut operands = vec![match source {
                ViewSource::Array(local) => Operand::Copy(Place::local(*local)),
                ViewSource::Value(operand) => *operand,
                ViewSource::DynArray(place) => Operand::Copy(*place),
            }];
            operands.extend(start.iter().chain(end));
            operands
        }
    }
}

fn apply(statement: &Statement, state: &mut [Value], index: &impl Fn(LocalId) -> Option<usize>) {
    let StatementKind::Assign(place, rvalue) = &statement.kind;
    if let Some(flag) = index(place.local)
        && let Rvalue::Use(Operand::Constant(value, _)) = rvalue
    {
        state[flag] = Value::Known(*value != 0);
    }
}

/// The flags' values on entry to each block: a forward dataflow over the
/// normal and unwind edges. A `switch` on a known flag only reaches the
/// branch taken, and a block's statement-level unwind target sees the
/// values at every point of the block, since any statement may panic.
fn entry_states(
    body: &Body,
    flags: &[LocalId],
    index: &impl Fn(LocalId) -> Option<usize>,
) -> Vec<Vec<Value>> {
    let mut states = vec![vec![Value::Unreached; flags.len()]; body.blocks.len()];
    states[0] = vec![Value::Unknown; flags.len()];
    let mut pending = vec![0];
    let mut queued = vec![false; body.blocks.len()];
    queued[0] = true;
    let flow = |states: &mut Vec<Vec<Value>>,
                pending: &mut Vec<BlockId>,
                queued: &mut Vec<bool>,
                target: BlockId,
                state: &[Value]| {
        let mut changed = false;
        for (slot, value) in states[target].iter_mut().zip(state) {
            let joined = slot.join(*value);
            if joined != *slot {
                *slot = joined;
                changed = true;
            }
        }
        if changed && !queued[target] {
            queued[target] = true;
            pending.push(target);
        }
    };
    while let Some(block) = pending.pop() {
        queued[block] = false;
        let data = &body.blocks[block];
        let mut state = states[block].clone();
        if let Some(unwind) = data.unwind {
            flow(&mut states, &mut pending, &mut queued, unwind, &state);
        }
        for statement in &data.statements {
            apply(statement, &mut state, index);
            if let Some(unwind) = data.unwind {
                flow(&mut states, &mut pending, &mut queued, unwind, &state);
            }
        }
        let mut successors = Vec::new();
        match &data.terminator.kind {
            TerminatorKind::Goto(target) => successors.push(*target),
            TerminatorKind::Switch {
                value,
                targets,
                otherwise,
            } => {
                let known = value
                    .place()
                    .filter(|place| place.field.is_none() && !place.deref)
                    .and_then(|place| index(place.local))
                    .and_then(|flag| match state[flag] {
                        Value::Known(live) => Some(i64::from(live)),
                        _ => None,
                    });
                match known {
                    Some(value) => successors.push(
                        targets
                            .iter()
                            .find(|(case, _)| *case == value)
                            .map_or(*otherwise, |(_, target)| *target),
                    ),
                    None => {
                        successors.extend(targets.iter().map(|(_, target)| *target));
                        successors.push(*otherwise);
                    }
                }
            }
            TerminatorKind::Call { next, unwind, .. }
            | TerminatorKind::Drop { next, unwind, .. } => {
                successors.push(*next);
                successors.extend(*unwind);
            }
            TerminatorKind::Panic { unwind } => successors.extend(*unwind),
            TerminatorKind::Return(_)
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable => {}
        }
        for target in successors {
            flow(&mut states, &mut pending, &mut queued, target, &state);
        }
    }
    states
}
