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
fn candidate(body: &Body, lp: &loops::Loop, all: &[loops::Loop]) -> Option<(LocalId, Type)> {
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
    Some((view, element))
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
    for (lp, (view, element)) in &candidates {
        let stride = (program.width(*element) * 8) as i64;
        let entry = loops::preheader(body, lp);
        let span = body.blocks[entry].terminator.span;
        let mut temp = |ty: Type| {
            body.locals.push(LocalDecl {
                ty,
                mutable: false,
                temporary: true,
            });
            body.locals.len() - 1
        };
        let (strided, flat) = (temp(Type::Bool), temp(Type::Bool));
        let word = |offset: usize| Operand::Copy(Place::field(*view, offset, Type::I64));
        let assign = |local: LocalId, rvalue: Rvalue| Statement {
            kind: StatementKind::Assign(Place::local(local), rvalue),
            span,
        };
        let store = |offset: usize, value: i64| Statement {
            kind: StatementKind::Assign(
                Place::field(*view, offset, Type::I64),
                Rvalue::Use(Operand::Constant(value, Type::I64)),
            ),
            span,
        };
        let first = assign(
            strided,
            Rvalue::Binary(BinOp::Eq, word(2), Operand::Constant(stride, Type::I64)),
        );
        let copies = loops::version(
            body,
            lp,
            entry,
            vec![first],
            Operand::Move(Place::local(strided)),
        );
        // The entry goes on to test the second word, then to the copy
        // through a block that stores the constants.
        let fast = body.blocks.len();
        body.blocks.push(BasicBlock {
            statements: vec![store(2, stride), store(3, 0)],
            terminator: Terminator {
                kind: TerminatorKind::Goto(copies[&lp.header]),
                span,
            },
            unwind: None,
        });
        let second = body.blocks.len();
        body.blocks.push(BasicBlock {
            statements: vec![assign(
                flat,
                Rvalue::Binary(BinOp::Eq, word(3), Operand::Constant(0, Type::I64)),
            )],
            terminator: Terminator {
                kind: TerminatorKind::Switch {
                    value: Operand::Move(Place::local(flat)),
                    targets: vec![(0, lp.header)],
                    otherwise: fast,
                },
                span,
            },
            unwind: None,
        });
        if let TerminatorKind::Switch { otherwise, .. } = &mut body.blocks[entry].terminator.kind {
            *otherwise = second;
        }
    }
    candidates.len()
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
