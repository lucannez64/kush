//! Vector push shadows (FND-MIR-PUSH-SHADOWS, docs/mir-design.md section 8).
//!
//! `Vec.push` reads the length and the capacity from the vector's buffer
//! header, because a growth may have changed both. In a loop that touches
//! a vector only through `v = Vec.push(v, e)` and reads of its length and
//! elements, nothing else can change them. There the two words live in
//! locals instead: the loop's preheader loads them once, and each push,
//! marked `shadow`, reads and updates them (the length is still stored, so
//! memory is never stale). As on the tree path, only for LLVM release
//! builds: Cranelift's code measured slower with the two extra loop-carried
//! values.

use super::drop_flags::rvalue_operands;
use super::loops::{self, Loop};
use super::*;
use crate::executable::{Target, VecOp};
use crate::int::{ArithOp, IntKind, IntOp};
use std::collections::BTreeSet;

/// A shadowed vector of a loop: the vector, its length and capacity
/// locals, and the blocks of its pushes.
type Shadowed = (LocalId, LocalId, LocalId, Vec<BlockId>);

fn whole(operand: Operand) -> Option<LocalId> {
    let place = operand.place()?;
    (!place.deref && place.field.is_none()).then_some(place.local)
}

fn mentions(operand: &Operand, locals: &BTreeSet<LocalId>) -> bool {
    operand
        .place()
        .is_some_and(|place| locals.contains(&place.local))
}

/// The vector op a block's terminator calls, with the call's arguments and
/// destination.
fn vector_call(body: &Body, block: BlockId) -> Option<(VecOp, &[Operand], LocalId)> {
    match &body.blocks[block].terminator.kind {
        TerminatorKind::Call {
            callee:
                Callee::Builtin {
                    index,
                    hint: CallHint::None,
                },
            args,
            destination,
            ..
        } => match body.builtins.0[*index] {
            Target::Vec(op, _) => Some((op, args, *destination)),
            _ => None,
        },
        _ => None,
    }
}

/// The blocks of the pushes of `vector` when the loop touches it only
/// through `vector = Vec.push(vector, e)` and reads of its length and
/// elements.
fn push_only(body: &Body, lp: &Loop, vector: LocalId) -> Option<Vec<BlockId>> {
    // Temporaries holding the vector's handle (one moves it into a push,
    // others are cleanup copies), and temporaries borrowing it.
    let mut copies = BTreeSet::from([vector]);
    let mut borrows = BTreeSet::new();
    // Values the loop assigns back to the vector.
    let mut stored = BTreeSet::new();
    for block in &lp.blocks {
        for statement in &body.blocks[*block].statements {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            let temporary = body.locals[place.local].temporary && place.field.is_none();
            match rvalue {
                Rvalue::Use(operand) if whole(*operand) == Some(vector) && temporary => {
                    copies.insert(place.local);
                }
                Rvalue::Ref(source)
                    if source.local == vector
                        && !source.deref
                        && source.field.is_none()
                        && temporary =>
                {
                    borrows.insert(place.local);
                }
                Rvalue::Use(operand)
                    if place.local == vector && place.field.is_none() && !place.deref =>
                {
                    stored.insert(whole(*operand)?);
                }
                _ if place.local == vector => return None,
                _ => {}
            }
        }
    }
    // Every other use of those temporaries is a push or a read.
    let mut pushes = Vec::new();
    let mut results = BTreeSet::new();
    let watched = copies.union(&borrows).copied().collect::<BTreeSet<_>>();
    for block in &lp.blocks {
        let data = &body.blocks[*block];
        for statement in &data.statements {
            let StatementKind::Assign(_, rvalue) = &statement.kind;
            let defines = matches!(rvalue, Rvalue::Use(operand) if whole(*operand) == Some(vector))
                || matches!(rvalue, Rvalue::Ref(source) if source.local == vector);
            if !defines
                && rvalue_operands(rvalue)
                    .iter()
                    .any(|o| mentions(o, &watched))
            {
                return None;
            }
        }
        match vector_call(body, *block) {
            Some((VecOp::Push, [handle, rest @ ..], destination))
                if whole(*handle).is_some_and(|local| copies.contains(&local)) =>
            {
                if rest.iter().any(|o| mentions(o, &watched)) {
                    return None;
                }
                pushes.push(*block);
                results.insert(destination);
            }
            Some((VecOp::Len | VecOp::Get, [receiver, rest @ ..], _))
                if whole(*receiver).is_some_and(|local| borrows.contains(&local)) =>
            {
                if rest.iter().any(|o| mentions(o, &watched)) {
                    return None;
                }
            }
            _ => {
                let touches = match &data.terminator.kind {
                    TerminatorKind::Call { callee, args, .. } => {
                        args.iter().any(|o| mentions(o, &watched))
                            || matches!(callee, Callee::Indirect(code) if mentions(code, &watched))
                    }
                    TerminatorKind::Switch { value, .. } | TerminatorKind::Return(value) => {
                        mentions(value, &watched)
                    }
                    TerminatorKind::Drop { place, .. } => watched.contains(&place.local),
                    _ => false,
                };
                if touches {
                    return None;
                }
            }
        }
    }
    (!pushes.is_empty() && stored.is_subset(&results)).then_some(pushes)
}

/// Shadow the push-only vectors of every loop of `body`. Returns how many
/// loops keep a vector in locals; with `trace`, reports each one as the
/// tree path does.
pub(crate) fn shadow(body: &mut Body, trace: bool) -> usize {
    let all = loops::loops(body);
    let vectors = (0..body.locals.len())
        .filter(|local| {
            !body.locals[*local].temporary && matches!(body.locals[*local].ty, Type::Vec(_))
        })
        .collect::<Vec<_>>();
    // A vector an enclosing loop shadows keeps that shadow inside: its
    // pushes there are already marked.
    let mut done: Vec<(BTreeSet<BlockId>, LocalId)> = Vec::new();
    let mut shadows: Vec<Shadowed> = Vec::new();
    let mut count = 0;
    for lp in &all {
        let found = vectors
            .iter()
            .filter(|vector| {
                !done
                    .iter()
                    .any(|(blocks, other)| other == *vector && blocks.contains(&lp.header))
            })
            .filter_map(|vector| push_only(body, lp, *vector).map(|pushes| (*vector, pushes)))
            .collect::<Vec<_>>();
        if found.is_empty() {
            continue;
        }
        let entry = loops::preheader(body, lp);
        let span = body.blocks[entry].terminator.span;
        for (vector, pushes) in &found {
            let mut word = |word: BufferWord| {
                let local = body.locals.len();
                body.locals.push(LocalDecl {
                    ty: Type::I64,
                    mutable: true,
                    temporary: true,
                });
                body.blocks[entry].statements.push(Statement {
                    kind: StatementKind::Assign(
                        Place::local(local),
                        Rvalue::Buffer(Operand::Copy(Place::local(*vector)), word),
                    ),
                    span,
                });
                local
            };
            let (length, capacity) = (word(BufferWord::Length), word(BufferWord::Capacity));
            for push in pushes {
                if let TerminatorKind::Call {
                    callee: Callee::Builtin { hint, .. },
                    ..
                } = &mut body.blocks[*push].terminator.kind
                {
                    *hint = CallHint::Shadow(length, capacity);
                }
            }
            done.push((lp.blocks.clone(), *vector));
            shadows.push((*vector, length, capacity, pushes.clone()));
        }
        if trace {
            eprintln!(
                "vector shadows: a loop in {} keeps {} vector(s) in variables",
                body.name,
                found.len()
            );
        }
        if let [(vector, length, capacity, pushes)] = shadows.as_slice()
            && loops::innermost(lp, &all)
            && fill_with_room(body, lp, entry, *vector, *length, *capacity, pushes)
            && trace
        {
            eprintln!(
                "vector fill: a loop in {} fills a vector it checked has room",
                body.name
            );
        }
        shadows.clear();
        count += 1;
    }
    count
}

/// Whether a type has no drop glue and fits one word: a stale length left
/// by an unwind out of a filling loop can then only hide elements, never
/// skip or repeat a drop.
fn plain(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Bool
    )
}

/// FND-PUSH-FILL: version a counted loop `while i < bound { ...; i = i + 1 }`
/// whose only shadowed vector holds plain values and is only pushed to.
/// The preheader tests that the vector has room for every push the loop can
/// make, `saturating(bound - i) * pushes <= capacity - length`; the copy
/// taken then marks its pushes `fill` (no room test, no grow call, no
/// header store), and each of its exits stores the length once. With
/// neither a call nor a header store left in the loop, LLVM can vectorize
/// it. Returns whether it versioned the loop.
fn fill_with_room(
    body: &mut Body,
    lp: &Loop,
    entry: BlockId,
    vector: LocalId,
    length: LocalId,
    capacity: LocalId,
    pushes: &[BlockId],
) -> bool {
    let Some(counted) = loops::counted(body, lp) else {
        return false;
    };
    let bound = match counted.bound {
        loops::Term::Local(local) if body.locals[local].ty == Type::I64 => {
            Operand::Copy(Place::local(local))
        }
        loops::Term::Constant(value) => Operand::Constant(value, Type::I64),
        _ => return false,
    };
    if counted.comparison != BinOp::Lt
        || counted.step != 1
        || body.locals[counted.counter].ty != Type::I64
    {
        return false;
    }
    // Every push stores a plain value, and nothing borrows the vector (its
    // length or elements would be read from the stale header).
    let plain_pushes = pushes.iter().all(|push| {
        matches!(
            &body.blocks[*push].terminator.kind,
            TerminatorKind::Call {
                callee: Callee::Builtin { index, .. },
                ..
            } if matches!(body.builtins.0[*index], Target::Vec(VecOp::Push, element) if plain(element))
        )
    });
    let borrowed = lp.blocks.iter().any(|block| {
        body.blocks[*block].statements.iter().any(|statement| {
            let StatementKind::Assign(_, rvalue) = &statement.kind;
            matches!(rvalue, Rvalue::Ref(source) if source.local == vector)
        })
    });
    if !plain_pushes || borrowed {
        return false;
    }
    let span = body.blocks[entry].terminator.span;
    let mut temp = |ty: Type| {
        body.locals.push(LocalDecl {
            ty,
            mutable: false,
            temporary: true,
        });
        body.locals.len() - 1
    };
    let (trips, needed, room, fits) = (
        temp(Type::I64),
        temp(Type::I64),
        temp(Type::I64),
        temp(Type::Bool),
    );
    let assign = |local: LocalId, rvalue: Rvalue| Statement {
        kind: StatementKind::Assign(Place::local(local), rvalue),
        span,
    };
    let copy = |local: LocalId| Operand::Copy(Place::local(local));
    let saturating = |op: ArithOp, left: Operand, right: Operand| {
        Rvalue::Int(
            IntOp::Saturating(op),
            IntKind::I64,
            IntKind::I64,
            vec![left, right],
        )
    };
    // Each block runs at most once per iteration of an innermost loop, so
    // the loop pushes at most `trips` times per push site.
    let statements = vec![
        assign(
            trips,
            saturating(ArithOp::Sub, bound, copy(counted.counter)),
        ),
        assign(
            needed,
            saturating(
                ArithOp::Mul,
                copy(trips),
                Operand::Constant(pushes.len() as i64, Type::I64),
            ),
        ),
        assign(
            room,
            Rvalue::Int(
                IntOp::Wrapping(ArithOp::Sub),
                IntKind::I64,
                IntKind::I64,
                vec![copy(capacity), copy(length)],
            ),
        ),
        assign(fits, Rvalue::Binary(BinOp::Le, copy(needed), copy(room))),
    ];
    let copies = loops::version(
        body,
        lp,
        entry,
        statements,
        Operand::Move(Place::local(fits)),
    );
    for push in pushes {
        if let TerminatorKind::Call {
            callee: Callee::Builtin { hint, .. },
            ..
        } = &mut body.blocks[copies[push]].terminator.kind
        {
            *hint = CallHint::Fill(length);
        }
    }
    // Every normal edge out of the copy goes through a block that stores
    // the length.
    let inside = copies.values().copied().collect::<BTreeSet<_>>();
    for copy_block in copies.values() {
        let targets = loops::successors(&body.blocks[*copy_block].terminator.kind);
        for target in targets.into_iter().collect::<BTreeSet<_>>() {
            if inside.contains(&target) {
                continue;
            }
            let unit = body.locals.len();
            body.locals.push(LocalDecl {
                ty: Type::Unit,
                mutable: false,
                temporary: true,
            });
            let store = body.blocks.len();
            body.blocks.push(BasicBlock {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::local(unit),
                        Rvalue::SetLength(
                            Operand::Copy(Place::local(vector)),
                            Operand::Copy(Place::local(length)),
                        ),
                    ),
                    span,
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Goto(target),
                    span,
                },
                unwind: None,
            });
            loops::retarget(&mut body.blocks[*copy_block].terminator.kind, target, store);
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shadowed(source: &str) -> (Body, usize) {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some("fill"))
            .expect("the function");
        let mut body = build(&program, index).expect("the function builds");
        let count = shadow(&mut body, false);
        verify(&program, &body).expect("the shadowed body verifies");
        let printed = text::print(&body);
        assert_eq!(text::parse(&printed).unwrap(), body, "{printed}");
        (body, count)
    }

    fn fill(loop_body: &str) -> String {
        format!(
            "fn peek(v: &Vec<i64>) -> i64 {{ Vec.len(v) }}
            fn fill(n: i64) -> i64 ! {{alloc}} {{
                let mut v: Vec<i64> = Vec.with_capacity(0);
                let mut i = 0;
                while i < n {{
                    {loop_body}
                    i = i + 1;
                }}
                Vec.len(&v)
            }}
            fn main() -> Unit ! {{io, alloc}} {{ print_i64(fill(5)); }}"
        )
    }

    #[test]
    fn a_push_loop_keeps_the_header_in_locals() {
        for shape in [
            "v = Vec.push(v, i * 2);",
            "v = Vec.push(v, i);
            if Vec.len(&v) > 3 { let first = Vec.get(&v, 0); v = Vec.push(v, first); }",
        ] {
            let (body, count) = shadowed(&fill(shape));
            assert_eq!(count, 1, "{shape}");
            let printed = text::print(&body);
            assert!(printed.contains("buffer capacity(copy _1)"), "{printed}");
            assert!(printed.contains(" shadow _"), "{printed}");
        }
    }

    #[test]
    fn a_counted_push_loop_gets_a_copy_that_fills() {
        let (body, count) = shadowed(&fill("v = Vec.push(v, i * 2);"));
        assert_eq!(count, 1);
        let printed = text::print(&body);
        assert!(printed.contains(" fill _"), "{printed}");
        assert!(printed.contains("set_length(copy _1"), "{printed}");
        // A loop that reads the vector keeps only the shadow.
        let (body, _) = shadowed(&fill(
            "v = Vec.push(v, i);
            if Vec.len(&v) > 3 { v = Vec.push(v, 1); }",
        ));
        let printed = text::print(&body);
        assert!(!printed.contains(" fill _"), "{printed}");
    }

    #[test]
    fn other_uses_of_the_vector_keep_the_reloads() {
        for shape in [
            // A call that could change it.
            "let seen = peek(&v); v = Vec.push(v, seen);",
            // A push whose result goes elsewhere.
            "let w = Vec.push(v, i); v = w;",
        ] {
            let (_, count) = shadowed(&fill(shape));
            assert_eq!(count, 0, "{shape}");
        }
    }
}
