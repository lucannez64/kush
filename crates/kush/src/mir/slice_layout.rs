//! Slice-layout loop versioning (FND-MIR-SLICE-VERSION, docs/mir-design.md
//! section 8).
//!
//! A view is the words `(pointer, length, stride, bytes)`. A loop over
//! `i < v.len()` vectorizes only when `v` holds whole consecutive elements
//! (the stride is the element width and the view is not over a byte
//! buffer), and the code generator cannot know that from words in
//! variables. As the tree path does, the loop is versioned on that test,
//! and the copy for the common layout starts by storing the two words'
//! values again as constants, so in that copy they are constants.
//!
//! Only in `Speed` builds, and only for small innermost loops: versioning
//! doubles the loop's code.

use super::loops::{self, Term};
use super::*;
use crate::executable::{SliceOp, Target};

/// The tree path's budget for a versioned loop, here in statements and
/// terminators.
const BUDGET: usize = 96;

/// The view and its element type, when `lp` is a small innermost loop
/// testing `i < v.len()` with `v` unchanged in the loop.
fn candidate(
    body: &Body,
    lp: &loops::Loop,
    all: &[loops::Loop],
) -> Option<(LocalId, Type, Vec<(LocalId, Type)>)> {
    if !loops::innermost(lp, all) {
        return None;
    }
    let size = lp
        .blocks
        .iter()
        .map(|block| body.blocks[*block].statements.len() + 1)
        .sum::<usize>();
    if size > BUDGET {
        return None;
    }
    let test = loops::test(body, lp)?;
    let (BinOp::Lt, Term::Local(index), Term::Length(Target::Slice(SliceOp::Len, element), view)) =
        (test.comparison, test.left, test.right)
    else {
        return None;
    };
    if body.locals[index].ty != Type::I64
        || !matches!(body.locals[view].ty, Type::Slice(_) | Type::SliceMut(_))
        || loops::assigned(body, &lp.blocks).contains(&view)
    {
        return None;
    }
    Some((view, element, companions(body, lp, index, view)))
}

/// At most this many other views get a length test.
const COMPANIONS: usize = 4;

/// The other views the loop reads or writes at the counter (`w[i]`), unchanged
/// in the loop, with their element types. The copy also requires
/// `len(view) <= len(w)` for each, so the bounds pass drops their upper
/// checks there as it does the view's own (FND-MIR-BOUNDS-VERSION).
fn companions(
    body: &Body,
    lp: &loops::Loop,
    index: LocalId,
    view: LocalId,
) -> Vec<(LocalId, Type)> {
    let assigned = loops::assigned(body, &lp.blocks);
    // The plain local an operand reads, through a temporary copied from
    // it in the loop.
    let source = |operand: Operand| -> Option<LocalId> {
        let place = operand.place()?;
        if place.deref || place.field.is_some() {
            return None;
        }
        if !body.locals[place.local].temporary {
            return Some(place.local);
        }
        lp.blocks.iter().find_map(|block| {
            body.blocks[*block]
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(
                        target,
                        Rvalue::Use(Operand::Copy(copied) | Operand::Move(copied)),
                    ) if *target == Place::local(place.local)
                        && !copied.deref
                        && copied.field.is_none()
                        && !body.locals[copied.local].temporary =>
                    {
                        Some(copied.local)
                    }
                    _ => None,
                })
        })
    };
    let mut found: Vec<(LocalId, Type)> = Vec::new();
    for block in &lp.blocks {
        let TerminatorKind::Call {
            callee: Callee::Builtin { index: builtin, .. },
            args,
            ..
        } = &body.blocks[*block].terminator.kind
        else {
            continue;
        };
        let Target::Slice(SliceOp::Get | SliceOp::Set | SliceOp::TryGet { .. }, element) =
            body.builtins.0[*builtin]
        else {
            continue;
        };
        let (Some(other), Some(position)) = (
            args.first().and_then(|operand| source(*operand)),
            args.get(1).and_then(|operand| source(*operand)),
        ) else {
            continue;
        };
        if other != view
            && position == index
            && matches!(body.locals[other].ty, Type::Slice(_) | Type::SliceMut(_))
            && !assigned.contains(&other)
            && !found.iter().any(|(known, _)| *known == other)
            && found.len() < COMPANIONS
        {
            found.push((other, element));
        }
    }
    found
}

/// Version every candidate loop of `body` except those with a header in
/// `skip` (deferred loops, whose chunk has its own specialization). Returns
/// how many it versioned.
pub(crate) fn version(
    program: &Executable,
    body: &mut Body,
    skip: &std::collections::BTreeSet<BlockId>,
) -> usize {
    let all = loops::loops(body);
    let candidates = all
        .iter()
        .filter(|lp| !skip.contains(&lp.header))
        .filter_map(|lp| candidate(body, lp, &all).map(|found| (lp.clone(), found)))
        .collect::<Vec<_>>();
    for (lp, (view, element, companions)) in &candidates {
        let views = std::iter::once((*view, *element))
            .chain(companions.iter().copied())
            .map(|(local, element)| (local, (program.width(element) * 8) as i64))
            .collect::<Vec<_>>();
        let entry = loops::preheader(body, lp);
        let span = body.blocks[entry].terminator.span;
        let word =
            |local: LocalId, offset: usize| Operand::Copy(Place::field(local, offset, Type::I64));
        let assign = |local: LocalId, rvalue: Rvalue| Statement {
            kind: StatementKind::Assign(Place::local(local), rvalue),
            span,
        };
        let store = |local: LocalId, offset: usize, value: i64| Statement {
            kind: StatementKind::Assign(
                Place::field(local, offset, Type::I64),
                Rvalue::Use(Operand::Constant(value, Type::I64)),
            ),
            span,
        };
        // Each test is statements and the flag they set. Every view holds
        // whole consecutive elements; then, after the copy's constants are
        // stored (the bounds pass forgets what it knew about a view whose
        // words are assigned), every companion is at least as long as the
        // view the loop runs over.
        let mut layout = Vec::new();
        let mut stores = Vec::new();
        for (local, stride) in &views {
            let strided = temp(body, Type::Bool);
            layout.push((
                vec![assign(
                    strided,
                    Rvalue::Binary(
                        BinOp::Eq,
                        word(*local, 2),
                        Operand::Constant(*stride, Type::I64),
                    ),
                )],
                strided,
            ));
            let flat = temp(body, Type::Bool);
            layout.push((
                vec![assign(
                    flat,
                    Rvalue::Binary(BinOp::Eq, word(*local, 3), Operand::Constant(0, Type::I64)),
                )],
                flat,
            ));
            stores.push(store(*local, 2, *stride));
            stores.push(store(*local, 3, 0));
        }
        let mut lengths = Vec::new();
        for (other, _) in companions {
            let (short, long, covers) = (
                temp(body, Type::I64),
                temp(body, Type::I64),
                temp(body, Type::Bool),
            );
            lengths.push((
                vec![
                    assign(short, Rvalue::Use(word(*view, 1))),
                    assign(long, Rvalue::Use(word(*other, 1))),
                    assign(
                        covers,
                        Rvalue::Binary(
                            BinOp::Le,
                            Operand::Copy(Place::local(short)),
                            Operand::Copy(Place::local(long)),
                        ),
                    ),
                ],
                covers,
            ));
        }
        let mut layout = layout.into_iter();
        let (first, flag) = layout.next().expect("a layout test");
        let copies = loops::version(body, lp, entry, first, Operand::Move(Place::local(flag)));
        // The entry goes on through the other tests, in a chain of blocks
        // with the stores between the two kinds, to the copy.
        let tests = layout.collect::<Vec<_>>();
        let base = body.blocks.len();
        let count = tests.len() + 1 + lengths.len();
        let next = |at: usize| {
            if at + 1 < count {
                base + at + 1
            } else {
                copies[&lp.header]
            }
        };
        let test = |at: usize, (statements, flag): (Vec<Statement>, LocalId)| BasicBlock {
            statements,
            terminator: Terminator {
                kind: TerminatorKind::Switch {
                    value: Operand::Move(Place::local(flag)),
                    targets: vec![(0, lp.header)],
                    otherwise: next(at),
                },
                span,
            },
            unwind: None,
        };
        let mut chain = Vec::with_capacity(count);
        for test_data in tests {
            chain.push(test(chain.len(), test_data));
        }
        chain.push(BasicBlock {
            statements: stores,
            terminator: Terminator {
                kind: TerminatorKind::Goto(next(chain.len())),
                span,
            },
            unwind: None,
        });
        for test_data in lengths {
            chain.push(test(chain.len(), test_data));
        }
        body.blocks.extend(chain);
        if let TerminatorKind::Switch { otherwise, .. } = &mut body.blocks[entry].terminator.kind {
            *otherwise = base;
        }
    }
    candidates.len()
}

/// A new temporary of `ty`.
fn temp(body: &mut Body, ty: Type) -> LocalId {
    body.locals.push(LocalDecl {
        ty,
        mutable: false,
        temporary: true,
    });
    body.locals.len() - 1
}

#[cfg(test)]
mod tests {
    use super::*;

    fn versioned(source: &str) -> (Body, usize) {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some("f"))
            .expect("the function");
        let mut body = build(&program, index).expect("the function builds");
        let count = version(&program, &mut body, &Default::default());
        verify(&program, &body).expect("the versioned body verifies");
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
    fn a_loop_over_a_view_gets_a_copy_for_whole_elements() {
        let (body, count) = versioned(&function(
            "while i < xs.len() { total = total + xs[i]; i = i + 1; }",
        ));
        assert_eq!(count, 1);
        assert_eq!(loops::loops(&body).len(), 2);
        // The copy's entry stores the constant layout.
        let printed = text::print(&body);
        assert!(printed.contains("_0.2:i64 = const 8: i64"), "{printed}");
    }

    #[test]
    fn a_second_view_at_the_counter_gets_a_length_test() {
        let source = "fn f(xs: &[i64], ys: &[i64]) -> i64 {
                let mut i = 0;
                let mut total = 0;
                while i < xs.len() { total = total + xs[i] * ys[i]; i = i + 1; }
                total
            }
            fn main() -> Unit ! {io} { print_i64(0); }";
        let (mut body, count) = versioned(source);
        assert_eq!(count, 1);
        let printed = text::print(&body);
        assert!(printed.contains("_1.2:i64 = const 8: i64"), "{printed}");
        assert!(printed.contains("Le("), "{printed}");
        // In the copy both reads lose their upper check; in the original
        // loop only the read of the view it runs over does.
        assert_eq!(super::super::bounds::mark(&mut body), 3);
    }

    #[test]
    fn other_loops_are_left_alone() {
        for shape in [
            // Not a length test.
            "while i < n { total = total + xs[i]; i = i + 1; }",
            // Not innermost.
            "while i < xs.len() { let mut j = 0; while j < n { j = j + 1; } i = i + 1; }",
            // Too large to copy.
            &format!(
                "while i < xs.len() {{ {} i = i + 1; }}",
                "total = total + xs[i] * 3 - 1;".repeat(40)
            ),
        ] {
            let (_, count) = versioned(&function(shape));
            assert_eq!(count, 0, "{shape}");
        }
    }
}
