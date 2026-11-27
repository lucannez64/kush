//! Copy and destination propagation (FND-MIR-COPY-PROP).
//!
//! The builder evaluates every expression into a fresh temporary, so a body
//! is full of `t = <rvalue>; x = move t` and `t = copy x; f(move t)`. This
//! pass folds both, as Rust's `DestinationPropagation` and `CopyProp` do,
//! and then removes the blocks no edge reaches any more and the empty
//! blocks that only jump on:
//!
//! - **Destinations:** `x = move t`, where the temporary `t` has no other
//!   use and is defined earlier in the same block (or by the call that
//!   enters it), becomes the definition writing `x`.
//! - **Copies:** `t = copy x` (or `move x`) whose one use comes later in the
//!   same block becomes that use reading `x` itself, when nothing assigns
//!   `x` in between.
//!
//! A local whose address the body takes is never involved: a store through
//! a reference could reach it unseen. Temporaries the cleanup reads (a
//! resource's copy for its drop) have two uses and are left alone, so drop
//! elaboration and unwinding keep their meaning.

use super::drop_flags::rvalue_operands;
use super::loops::address_taken;
use super::*;
use std::collections::BTreeSet;

pub(crate) fn propagate(body: &mut Body) {
    let taken = address_taken(body);
    destinations(body, &taken);
    copies(body, &taken);
    thread(body);
    prune(body);
}

/// Every operand a terminator reads, with places used by address.
fn terminator_operands(kind: &TerminatorKind) -> Vec<Operand> {
    match kind {
        TerminatorKind::Switch { value, .. } | TerminatorKind::Return(value) => vec![*value],
        TerminatorKind::Call { callee, args, .. } => {
            let mut operands = args.clone();
            if let Callee::Indirect(code) = callee {
                operands.push(*code);
            }
            operands
        }
        TerminatorKind::Drop { place, .. } => vec![Operand::Copy(*place)],
        TerminatorKind::Goto(_)
        | TerminatorKind::Panic { .. }
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => Vec::new(),
    }
}

/// Locals a terminator writes: a call's destination and its shadow words.
fn terminator_writes(kind: &TerminatorKind) -> Vec<LocalId> {
    match kind {
        TerminatorKind::Call {
            destination,
            callee,
            ..
        } => {
            let mut writes = vec![*destination];
            match callee {
                Callee::Builtin {
                    hint: CallHint::Shadow(length, capacity),
                    ..
                } => writes.extend([*length, *capacity]),
                Callee::Builtin {
                    hint: CallHint::Fill(length),
                    ..
                } => writes.push(*length),
                _ => {}
            }
            writes
        }
        _ => Vec::new(),
    }
}

/// The locals a statement reads (including a pointer it stores through).
fn statement_reads(statement: &Statement) -> Vec<LocalId> {
    let StatementKind::Assign(place, rvalue) = &statement.kind;
    let mut reads = rvalue_operands(rvalue)
        .into_iter()
        .filter_map(|operand| operand.place().map(|place| place.local))
        .collect::<Vec<_>>();
    if place.deref || place.field.is_some() {
        // A store through a pointer reads it; a field store keeps the rest.
        reads.push(place.local);
    }
    reads
}

/// The locals a statement writes.
fn statement_writes(statement: &Statement) -> Vec<LocalId> {
    let StatementKind::Assign(place, rvalue) = &statement.kind;
    let mut writes = Vec::new();
    if !place.deref {
        writes.push(place.local);
    }
    if let Rvalue::Deferred(deferral, _) = rvalue {
        writes.push(deferral.sticky);
    }
    writes
}

/// How many times each local is read, over the whole body.
fn reads(body: &Body) -> Vec<usize> {
    let mut count = vec![0; body.locals.len()];
    for block in &body.blocks {
        for statement in &block.statements {
            for local in statement_reads(statement) {
                count[local] += 1;
            }
        }
        for operand in terminator_operands(&block.terminator.kind) {
            if let Some(place) = operand.place() {
                count[place.local] += 1;
            }
        }
    }
    count
}

/// How many times each local is written, over the whole body.
fn writes(body: &Body) -> Vec<usize> {
    let mut count = vec![0; body.locals.len()];
    for block in &body.blocks {
        for statement in &block.statements {
            for local in statement_writes(statement) {
                count[local] += 1;
            }
        }
        for local in terminator_writes(&block.terminator.kind) {
            count[local] += 1;
        }
    }
    count
}

/// The whole local an operand names, if it is one.
fn whole(operand: Operand) -> Option<LocalId> {
    let place = operand.place()?;
    (!place.deref && place.field.is_none()).then_some(place.local)
}

/// A temporary read and written exactly once, whose address is not taken.
fn single(
    body: &Body,
    local: LocalId,
    reads: &[usize],
    writes: &[usize],
    taken: &BTreeSet<LocalId>,
) -> bool {
    body.locals[local].temporary
        && reads[local] == 1
        && writes[local] == 1
        && !taken.contains(&local)
}

fn destinations(body: &mut Body, taken: &BTreeSet<LocalId>) {
    let reads = reads(body);
    let writes = writes(body);
    for block in 0..body.blocks.len() {
        let mut at = 0;
        while at < body.blocks[block].statements.len() {
            if let Some((x, t)) = moved_into(&body.blocks[block].statements[at])
                && single(body, t, &reads, &writes, taken)
                && !taken.contains(&x)
                && body.locals[x].ty == body.locals[t].ty
                && retarget(body, block, at, x, t)
            {
                body.blocks[block].statements.remove(at);
                continue;
            }
            at += 1;
        }
    }
}

/// `x = move t` (or `copy t`) of whole locals.
fn moved_into(statement: &Statement) -> Option<(LocalId, LocalId)> {
    let StatementKind::Assign(place, Rvalue::Use(operand)) = &statement.kind else {
        return None;
    };
    if place.deref || place.field.is_some() {
        return None;
    }
    Some((place.local, whole(*operand)?))
}

/// Make the definition of `t` that the statement at `at` of `block` moves
/// into `x` write `x` directly. Returns whether it could.
fn retarget(body: &mut Body, block: BlockId, at: usize, x: LocalId, t: LocalId) -> bool {
    let statements = &body.blocks[block].statements;
    // A definition earlier in the block, with nothing touching `x` between.
    for before in (0..at).rev() {
        let statement = &statements[before];
        if statement_writes(statement).contains(&t) {
            // The definition may read `x`: an assignment evaluates its
            // rvalue before it stores.
            let StatementKind::Assign(place, _) = &statement.kind;
            if *place != Place::local(t) {
                return false;
            }
            let StatementKind::Assign(place, _) = &mut body.blocks[block].statements[before].kind;
            *place = Place::local(x);
            return true;
        }
        if statement_reads(statement).contains(&x) || statement_writes(statement).contains(&x) {
            return false;
        }
    }
    // The call that enters this block, when the move comes first.
    if at != 0 {
        return false;
    }
    let calls = body
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, data)| super::loops::successors(&data.terminator.kind).contains(&block))
        .collect::<Vec<_>>();
    let [(caller, _)] = calls.as_slice() else {
        return false;
    };
    let caller = *caller;
    let TerminatorKind::Call { destination, .. } = &mut body.blocks[caller].terminator.kind else {
        return false;
    };
    if *destination != t {
        return false;
    }
    *destination = x;
    true
}

fn copies(body: &mut Body, taken: &BTreeSet<LocalId>) {
    let reads = reads(body);
    let writes = writes(body);
    for block in 0..body.blocks.len() {
        let mut at = 0;
        while at < body.blocks[block].statements.len() {
            if let Some((t, source)) = copy_of(&body.blocks[block].statements[at])
                && single(body, t, &reads, &writes, taken)
                && !taken.contains(&source.local)
                && replace_use(body, block, at, t, source)
            {
                body.blocks[block].statements.remove(at);
                continue;
            }
            at += 1;
        }
    }
}

/// `t = copy x` or `t = move x`: the temporary and the operand read.
fn copy_of(statement: &Statement) -> Option<(LocalId, Place)> {
    let StatementKind::Assign(place, Rvalue::Use(operand)) = &statement.kind else {
        return None;
    };
    if place.deref || place.field.is_some() {
        return None;
    }
    let source = operand.place()?;
    if source.deref || source.field.is_some() {
        return None;
    }
    Some((place.local, source))
}

/// Replace the one use of `t` after the statement at `at` of `block` by the
/// operand reading `source`, if it comes later in the block with nothing
/// writing `source` in between. Returns whether it did.
fn replace_use(body: &mut Body, block: BlockId, at: usize, t: LocalId, source: Place) -> bool {
    let StatementKind::Assign(_, Rvalue::Use(operand)) = &body.blocks[block].statements[at].kind
    else {
        return false;
    };
    let original = *operand;
    let substitute = |operand: &mut Operand| -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place)
                if place.local == t && !place.deref && place.field.is_none() =>
            {
                *operand = match original {
                    Operand::Move(_) => Operand::Move(source),
                    _ => Operand::Copy(source),
                };
                true
            }
            _ => false,
        }
    };
    for statement in &mut body.blocks[block].statements[at + 1..] {
        if statement_reads(statement).contains(&t) {
            // Only a plain operand use is substituted.
            let StatementKind::Assign(_, rvalue) = &mut statement.kind;
            return substitute_rvalue(rvalue, &substitute);
        }
        if statement_writes(statement).contains(&source.local) {
            return false;
        }
    }
    match &mut body.blocks[block].terminator.kind {
        TerminatorKind::Switch { value, .. } | TerminatorKind::Return(value) => substitute(value),
        TerminatorKind::Call { args, .. } => args.iter_mut().any(substitute),
        _ => false,
    }
}

/// Substitute in the operands an rvalue reads by value (not a place used
/// by address).
fn substitute_rvalue(rvalue: &mut Rvalue, substitute: &dyn Fn(&mut Operand) -> bool) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Unary(_, operand)
        | Rvalue::BoxNew(operand)
        | Rvalue::BoxTake(operand)
        | Rvalue::Coerce(operand, _)
        | Rvalue::Buffer(operand, _) => substitute(operand),
        Rvalue::Binary(_, left, right)
        | Rvalue::SetLength(left, right)
        | Rvalue::ByteAt(left, right)
        | Rvalue::StructEq(left, right, _) => substitute(left) || substitute(right),
        Rvalue::Int(_, _, _, operands)
        | Rvalue::Aggregate(_, _, operands)
        | Rvalue::Task(_, operands)
        | Rvalue::Runtime(_, operands)
        | Rvalue::Alloc(_, operands)
        | Rvalue::Array(_, operands)
        | Rvalue::Map(_, operands)
        | Rvalue::Deferred(_, operands)
        | Rvalue::Loop(_, operands) => operands.iter_mut().any(substitute),
        _ => false,
    }
}

/// Send edges into an empty block that only jumps on straight to its
/// target.
fn thread(body: &mut Body) {
    let forward = |body: &Body, mut block: BlockId| {
        let mut seen = BTreeSet::new();
        while body.blocks[block].statements.is_empty()
            && let TerminatorKind::Goto(next) = body.blocks[block].terminator.kind
            && seen.insert(block)
        {
            block = next;
        }
        block
    };
    for block in 0..body.blocks.len() {
        let mut kind = body.blocks[block].terminator.kind.clone();
        let edit = |target: &mut BlockId| *target = forward(body, *target);
        match &mut kind {
            TerminatorKind::Goto(target) => edit(target),
            TerminatorKind::Switch {
                targets, otherwise, ..
            } => {
                for (_, target) in targets {
                    edit(target);
                }
                edit(otherwise);
            }
            TerminatorKind::Call { next, unwind, .. }
            | TerminatorKind::Drop { next, unwind, .. } => {
                edit(next);
                if let Some(unwind) = unwind {
                    edit(unwind);
                }
            }
            TerminatorKind::Panic {
                unwind: Some(unwind),
            } => edit(unwind),
            _ => {}
        }
        body.blocks[block].terminator.kind = kind;
        if let Some(unwind) = body.blocks[block].unwind {
            body.blocks[block].unwind = Some(forward(body, unwind));
        }
    }
}

/// Remove the blocks the entry does not reach, along normal or unwind
/// edges, and renumber the rest.
fn prune(body: &mut Body) {
    let mut reached = vec![false; body.blocks.len()];
    let mut work = vec![0];
    while let Some(block) = work.pop() {
        if std::mem::replace(&mut reached[block], true) {
            continue;
        }
        let data = &body.blocks[block];
        work.extend(super::loops::successors(&data.terminator.kind));
        work.extend(data.unwind);
        match &data.terminator.kind {
            TerminatorKind::Call { unwind, .. }
            | TerminatorKind::Drop { unwind, .. }
            | TerminatorKind::Panic { unwind } => work.extend(*unwind),
            _ => {}
        }
    }
    if reached.iter().all(|reached| *reached) {
        return;
    }
    let mut number = vec![usize::MAX; body.blocks.len()];
    let mut next = 0;
    for (block, reached) in reached.iter().enumerate() {
        if *reached {
            number[block] = next;
            next += 1;
        }
    }
    let blocks = std::mem::take(&mut body.blocks);
    for (block, mut data) in blocks.into_iter().enumerate() {
        if !reached[block] {
            continue;
        }
        let edit = |target: &mut BlockId| *target = number[*target];
        match &mut data.terminator.kind {
            TerminatorKind::Goto(target) => edit(target),
            TerminatorKind::Switch {
                targets, otherwise, ..
            } => {
                for (_, target) in targets {
                    edit(target);
                }
                edit(otherwise);
            }
            TerminatorKind::Call { next, unwind, .. }
            | TerminatorKind::Drop { next, unwind, .. } => {
                edit(next);
                if let Some(unwind) = unwind {
                    edit(unwind);
                }
            }
            TerminatorKind::Panic {
                unwind: Some(unwind),
            } => edit(unwind),
            _ => {}
        }
        if let Some(unwind) = &mut data.unwind {
            edit(unwind);
        }
        body.blocks.push(data);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn built(source: &str, name: &str) -> (Body, String) {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some(name))
            .expect("the function");
        let body = build(&program, index).expect("the function builds");
        verify(&program, &body).expect("the propagated body verifies");
        let printed = text::print(&body);
        assert_eq!(text::parse(&printed).unwrap(), body, "{printed}");
        (body, printed)
    }

    #[test]
    fn results_land_in_their_variables() {
        let (body, printed) = built(
            "fn f(a: i64, b: i64) -> i64 {
                let sum = a + b;
                let product = sum * a;
                product - b
            }
            fn main() -> Unit ! {io} { print_i64(f(2, 3)); }",
            "f",
        );
        // `let sum = a + b` is one statement, reading the parameters.
        assert!(printed.contains("_2 = Add(copy _0, copy _1)"), "{printed}");
        assert_eq!(body.blocks.len(), 1, "{printed}");
    }

    #[test]
    fn a_copy_stays_when_its_source_changes_before_the_use() {
        let (_, printed) = built(
            "fn f(n: i64) -> i64 {
                let mut x = n;
                let y = x + { x = 7; x };
                y
            }
            fn main() -> Unit ! {io} { print_i64(f(2)); }",
            "f",
        );
        // The left operand is read before the block assigns `x`.
        assert!(printed.contains("= copy _1"), "{printed}");
    }
}
