//! EFF-ROW-LAWS: the row-algebra obligations of docs/effect-capabilities.md
//! section 4, checked against the checker's own row operations
//! ([`EffectRowTerm`] evaluation and [`solve_row_bits`]).
//!
//! Rows are 16-bit sets. A law with one free row is checked for every one of
//! the 2^16 rows; a second or third row ranges over a stratified sample (empty,
//! full, every singleton and co-singleton, builtin/declared halves, and fixed
//! pseudo-random rows). The solver is compared with an independent brute-force
//! search over whole rows, not bit by bit.

use std::collections::{BTreeMap, BTreeSet};

use crate::runtime_types::{EffectRowTerm, RowSolve, solve_row_bits};

type Term = EffectRowTerm;

fn var(id: usize) -> Term {
    Term::Variable(id)
}
fn constant(bits: u16) -> Term {
    Term::Constant(bits)
}
fn union(left: Term, right: Term) -> Term {
    Term::Union(Box::new(left), Box::new(right))
}
fn minus(left: Term, right: Term) -> Term {
    Term::Difference(Box::new(left), Box::new(right))
}

fn eval(term: &Term, rows: &[u16]) -> u16 {
    term.evaluate_with(&mut |id| rows.get(id).copied())
        .expect("every variable is bound")
}

/// Reference set semantics, independent of the bitset encoding.
fn set_of(bits: u16) -> BTreeSet<u8> {
    (0..16).filter(|bit| bits & (1 << bit) != 0).collect()
}
fn reference(term: &Term, rows: &[u16]) -> BTreeSet<u8> {
    match term {
        Term::Constant(bits) => set_of(*bits),
        Term::Variable(id) => set_of(rows[*id]),
        Term::Union(left, right) => &reference(left, rows) | &reference(right, rows),
        Term::Difference(left, right) => &reference(left, rows) - &reference(right, rows),
    }
}

/// Deterministic pseudo-random rows (no external crate).
fn lcg(seed: &mut u64) -> u16 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    (*seed >> 33) as u16
}

fn sample() -> Vec<u16> {
    let mut rows = vec![0, 0xFFFF, 0x000F, 0xFFF0, 0x5555, 0xAAAA, 0x00FF, 0xFF00];
    for bit in 0..16 {
        rows.push(1 << bit);
        rows.push(!(1u16 << bit));
    }
    let mut seed = 7;
    for _ in 0..8 {
        rows.push(lcg(&mut seed));
    }
    rows.sort();
    rows.dedup();
    rows
}

/// Every term of depth at most `depth` over two variables and two constants.
fn terms(depth: usize) -> Vec<Term> {
    let mut all = vec![var(0), var(1), constant(0x0013), constant(0xA040)];
    for _ in 0..depth {
        let previous = all.clone();
        for left in &previous {
            for right in &previous {
                all.push(union(left.clone(), right.clone()));
                all.push(minus(left.clone(), right.clone()));
            }
        }
    }
    all
}

#[test]
fn term_evaluation_is_set_semantics_and_bitwise() {
    let rows = sample();
    let terms = terms(2);
    assert!(terms.len() > 2000);
    let mut checked = 0usize;
    for term in &terms {
        for (index, x) in rows.iter().enumerate().step_by(3) {
            let y = rows[(index * 7 + 3) % rows.len()];
            let value = eval(term, &[*x, y]);
            assert_eq!(set_of(value), reference(term, &[*x, y]), "{term:?}");
            // Bit `b` of the result depends only on bit `b` of each variable:
            // the lemma the per-bit solver relies on.
            for bit in 0..16 {
                let mask = 1u16 << bit;
                let restricted = eval(term, &[x & mask, y & mask]);
                assert_eq!(value & mask, restricted & mask, "{term:?} bit {bit}");
            }
            checked += 1;
        }
    }
    assert!(checked > 30_000);
}

#[test]
fn composition_is_an_idempotent_commutative_monoid() {
    let others = sample();
    let assoc = union(union(var(0), var(1)), var(2));
    let assoc_right = union(var(0), union(var(1), var(2)));
    for a in 0..=u16::MAX {
        // Unit and idempotence over every row.
        assert_eq!(eval(&union(var(0), constant(0)), &[a]), a);
        assert_eq!(eval(&union(constant(0), var(0)), &[a]), a);
        assert_eq!(eval(&union(var(0), var(0)), &[a]), a);
        for b in &others {
            assert_eq!(
                eval(&union(var(0), var(1)), &[a, *b]),
                eval(&union(var(1), var(0)), &[a, *b])
            );
        }
        let b = others[a as usize % others.len()];
        let c = others[(a as usize / 7) % others.len()];
        assert_eq!(eval(&assoc, &[a, b, c]), eval(&assoc_right, &[a, b, c]));
    }
}

fn subset(a: u16, b: u16) -> bool {
    a & !b == 0
}

#[test]
fn subeffecting_is_a_congruence_and_subtraction_is_antitone_on_the_right() {
    let others = sample();
    for a in 0..=u16::MAX {
        for (index, widen) in others.iter().enumerate() {
            let a_wide = a | widen;
            let b = others[(index * 5 + a as usize) % others.len()];
            let b_wide = b | others[(index + 1) % others.len()];
            // e1 ⊆ e1', e2 ⊆ e2'  ⇒  e1 ∪ e2 ⊆ e1' ∪ e2'
            assert!(subset(
                eval(&union(var(0), var(1)), &[a, b]),
                eval(&union(var(0), var(1)), &[a_wide, b_wide])
            ));
            // a ⊆ a', b' ⊆ b  ⇒  a - b ⊆ a' - b'
            assert!(subset(
                eval(&minus(var(0), var(1)), &[a, b_wide]),
                eval(&minus(var(0), var(1)), &[a_wide, b])
            ));
        }
    }
}

/// `handle Op` with handler row `h`: the body is typed at `e ∪ {Op}` and the
/// whole expression at `(body - {Op}) ∪ h`.
fn discharge(op: u16) -> Term {
    union(minus(var(0), constant(op)), var(1))
}

#[test]
fn discharge_commutes_with_subeffecting_and_keeps_the_handler_row() {
    let handlers = sample();
    for op_bit in 4..16 {
        let op = 1u16 << op_bit;
        let rule = discharge(op);
        for e in 0..=u16::MAX {
            let h = handlers[e as usize % handlers.len()];
            let body = e | op;
            let result = eval(&rule, &[body, h]);
            // The handler row is never dropped and Op is discharged unless the
            // handler itself performs it.
            assert!(subset(h, result));
            assert_eq!(result & op, h & op);
            // Discharging a body that already includes Op equals discharging
            // the body without it.
            assert_eq!(result, eval(&rule, &[e & !op, h]));
            // Monotone in the body row.
            let wider = body | handlers[(e as usize / 3) % handlers.len()];
            assert!(subset(result, eval(&rule, &[wider, h])));
        }
    }
}

/// Independent whole-row solver: enumerate every assignment of the
/// variables over `universe`, keep the valid ones, and return the one that is
/// a subset of every other valid assignment.
fn brute_force(
    variables: usize,
    allowed: &[u16],
    required: &[u16],
    constraints: &[(Term, u16)],
    universe_bits: u32,
) -> RowSolve {
    let size = 1usize << universe_bits;
    let mut valid: Vec<Vec<u16>> = Vec::new();
    let mut assignment = vec![0u16; variables];
    let total = size.pow(variables as u32);
    for mut index in 0..total {
        for slot in assignment.iter_mut() {
            *slot = (index % size) as u16;
            index /= size;
        }
        let in_domain = assignment
            .iter()
            .enumerate()
            .all(|(v, row)| subset(*row, allowed[v]) && subset(required[v], *row));
        if in_domain
            && constraints
                .iter()
                .all(|(row, actual)| subset(*actual, eval(row, &assignment)))
        {
            valid.push(assignment.clone());
        }
    }
    if valid.is_empty() {
        return RowSolve::Unsatisfiable;
    }
    let minimal = valid.iter().find(|candidate| {
        valid.iter().all(|other| {
            candidate
                .iter()
                .zip(other)
                .all(|(small, large)| subset(*small, *large))
        })
    });
    match minimal {
        Some(rows) => RowSolve::Solved(rows.iter().copied().enumerate().collect()),
        None => RowSolve::Ambiguous,
    }
}

/// The checker's solver reports the first failing bit; the brute force sees
/// whole rows. Both agree on solvability and on the solution; when some bit
/// is unsatisfiable the whole system is, and when no bit is unsatisfiable but
/// some bit is ambiguous the whole system is ambiguous. If one bit is
/// ambiguous and a later one unsatisfiable, the checker reports the earlier
/// ambiguity while the brute force sees no solution: both reject.
fn agree(solver: &RowSolve, brute: &RowSolve, context: &dyn std::fmt::Debug) {
    match (solver, brute) {
        (RowSolve::Solved(left), RowSolve::Solved(right)) => assert_eq!(left, right, "{context:?}"),
        (RowSolve::Unsatisfiable, RowSolve::Unsatisfiable)
        | (RowSolve::Ambiguous, RowSolve::Ambiguous)
        | (RowSolve::Ambiguous, RowSolve::Unsatisfiable) => {}
        _ => panic!("solver {solver:?} but brute force {brute:?}: {context:?}"),
    }
}

fn run_solver(
    variables: usize,
    allowed: &[u16],
    required: &[u16],
    constraints: &[(Term, u16)],
    universe: u16,
) -> RowSolve {
    let unbound = (0..variables).collect::<Vec<_>>();
    let allowed_map = allowed
        .iter()
        .copied()
        .enumerate()
        .collect::<BTreeMap<_, _>>();
    let required_map = required
        .iter()
        .copied()
        .enumerate()
        .collect::<BTreeMap<_, _>>();
    let rows = constraints
        .iter()
        .map(|(row, actual)| (row, *actual))
        .collect::<Vec<_>>();
    solve_row_bits(
        &unbound,
        &allowed_map,
        &required_map,
        &BTreeMap::new(),
        &rows,
        universe,
    )
}

#[test]
fn one_variable_solver_matches_whole_row_search_over_all_16_bit_rows() {
    let rows = sample();
    let mut seed = 99;
    let mut outcomes = BTreeMap::new();
    for round in 0..48 {
        let pick = |seed: &mut u64| rows[lcg(seed) as usize % rows.len()];
        let actual = pick(&mut seed);
        let k1 = pick(&mut seed);
        let k2 = pick(&mut seed);
        let shapes = [
            var(0),
            union(var(0), constant(k1)),
            minus(var(0), constant(k1)),
            minus(union(var(0), constant(k1)), constant(k2)),
            // Variable on the right of a subtraction: anti-monotone, so the
            // minimal row is the empty one when the constant covers.
            minus(constant(k1), var(0)),
        ];
        let shape = &shapes[round % shapes.len()];
        let allowed = if round % 3 == 0 { !k2 } else { 0xFFFF };
        let required = if round % 4 == 1 { k2 & allowed } else { 0 };
        let mut constraints = vec![(shape.clone(), actual)];
        if round % 2 == 0 {
            constraints.push((union(var(0), constant(k2)), pick(&mut seed)));
        }
        let solver = run_solver(1, &[allowed], &[required], &constraints, 0xFFFF);
        let brute = brute_force(1, &[allowed], &[required], &constraints, 16);
        agree(&solver, &brute, &(round, &constraints, allowed, required));
        *outcomes
            .entry(format!("{brute:?}").chars().take(6).collect::<String>())
            .or_insert(0) += 1;
    }
    // The sample exercises both solvable and unsolvable systems.
    assert!(outcomes.len() >= 2, "{outcomes:?}");
}

#[test]
fn two_variable_solver_matches_whole_row_search() {
    // Two variables over a five-bit sub-universe: 2^10 whole assignments per
    // system, compared with the per-bit solver on the same constraints.
    const BITS: u32 = 5;
    let universe = (1u16 << BITS) - 1;
    let mut seed = 3;
    let mut seen = BTreeSet::new();
    for round in 0..400 {
        let mut pick = || lcg(&mut seed) & universe;
        let (a1, a2, k1, k2) = (pick(), pick(), pick(), pick());
        let allowed = [universe & !(if round % 5 == 0 { k1 } else { 0 }), universe];
        let required = [0, if round % 7 == 3 { k2 & universe } else { 0 }];
        let shapes = [
            union(var(0), var(1)),
            union(var(0), constant(k1)),
            minus(union(var(0), var(1)), constant(k2)),
            minus(var(0), var(1)),
            union(minus(var(1), constant(k1)), var(0)),
            var(1),
        ];
        let constraints = vec![
            (shapes[round % shapes.len()].clone(), a1),
            (shapes[(round / 6) % shapes.len()].clone(), a2),
        ];
        let solver = run_solver(2, &allowed, &required, &constraints, universe);
        let brute = brute_force(2, &allowed, &required, &constraints, BITS);
        agree(&solver, &brute, &(round, &constraints, allowed, required));
        seen.insert(format!("{brute:?}").split('(').next().unwrap().to_owned());
    }
    // Solved, unsatisfiable and ambiguous systems all occur.
    assert_eq!(seen.len(), 3);
}

#[test]
fn bounded_binders_are_domain_restrictions() {
    // `<e: Effects - x>` and `<e: Effects + y>` restrict the whole-row
    // domain; the minimal solution always contains `y` and never `x`.
    for x in 0..16u16 {
        let excluded = 1u16 << x;
        for y in 0..16u16 {
            let included = 1u16 << y;
            for actual in [0u16, 0x0003, 0x0F00, 0x8001] {
                let constraints = vec![(var(0), actual)];
                let result = run_solver(1, &[!excluded], &[included], &constraints, 0xFFFF);
                if excluded & (actual | included) != 0 {
                    assert_eq!(result, RowSolve::Unsatisfiable, "x={x} y={y} {actual:#x}");
                } else {
                    assert_eq!(
                        result,
                        RowSolve::Solved(BTreeMap::from([(0, actual | included)])),
                        "x={x} y={y} {actual:#x}"
                    );
                }
            }
        }
    }
}
