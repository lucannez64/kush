use kush::{
    check,
    kernel::{Kernel, Limits, Term as T},
    natural::{Error, MAX_DIGITS, Natural},
};

fn number(text: &str) -> Natural {
    text.parse().unwrap()
}
fn term(text: &str) -> T {
    T::natural(number(text))
}
fn unary(n: u32) -> T {
    (0..n).fold(T::Zero, |n, _| T::succ(n))
}

#[test]
fn parsing_and_display_are_canonical_across_limb_boundaries() {
    for text in [
        "0",
        "1",
        "999999999",
        "1000000000",
        "1000000000000000000",
        "18446744073709551616",
        "340282366920938463463374607431768211456",
    ] {
        let value = number(text);
        assert_eq!(value.to_string(), text);
        assert_eq!(value.decimal_digits(), text.len());
        assert_eq!(number(&format!("000{text}")), value);
        assert_eq!(format!("{value:?}"), text);
    }
    assert_eq!(number("000"), Natural::default());
    assert!(number("000").is_zero());
    assert_eq!(Natural::default().decimal_digits(), 1);
    for input in ["", "-1", "+1", " 1", "1 ", "1_0", "1.0", "١", "１", "0x10"] {
        assert_eq!(input.parse::<Natural>(), Err(Error::InvalidDecimal));
    }
}

#[test]
fn successor_and_predecessor_handle_long_carry_and_borrow_chains() {
    for digits in [1, 8, 9, 10, 17, 18, 19, 100, MAX_DIGITS - 1] {
        let nines = number(&"9".repeat(digits));
        let power = number(&format!("1{}", "0".repeat(digits)));
        assert_eq!(nines.successor().unwrap(), power);
        assert_eq!(power.predecessor().unwrap(), nines);
        assert_eq!(nines.predecessor().unwrap().successor().unwrap(), nines);
    }
    assert_eq!(Natural::default().predecessor(), None);
    assert_eq!(Natural::default().successor().unwrap(), Natural::from(1));
    assert_eq!(Natural::from(1).predecessor().unwrap(), Natural::default());
}

#[test]
fn deterministic_numeric_corpus_agrees_with_independent_u128_arithmetic() {
    let mut state = 0x0123456789abcdef_u64;
    for _ in 0..2000 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let value = Natural::from(state);
        assert_eq!(value.to_string(), state.to_string());
        assert_eq!(number(&state.to_string()), value);
        assert_eq!(
            value.successor().unwrap().to_string(),
            (u128::from(state) + 1).to_string()
        );
        assert_eq!(
            value.predecessor().map(|n| n.to_string()),
            state.checked_sub(1).map(|n| n.to_string())
        );
    }
    assert_eq!(
        Natural::from(u64::MAX).successor().unwrap().to_string(),
        "18446744073709551616"
    );
    assert_eq!(
        number(&u128::MAX.to_string())
            .successor()
            .unwrap()
            .to_string(),
        "340282366920938463463374607431768211456"
    );
}

#[test]
fn digit_budget_is_explicit_and_never_wraps_or_truncates() {
    let max = number(&"9".repeat(MAX_DIGITS));
    assert_eq!(max.decimal_digits(), MAX_DIGITS);
    assert_eq!(max.successor(), Err(Error::DigitLimit));
    assert_eq!(
        format!("1{}", "0".repeat(MAX_DIGITS)).parse::<Natural>(),
        Err(Error::DigitLimit)
    );
    // Leading zeroes consume source bytes, not significant-digit budget.
    assert_eq!(number(&"0".repeat(MAX_DIGITS + 1)), Natural::default());
    assert_eq!(
        number(&format!("{}1", "0".repeat(MAX_DIGITS + 1))),
        Natural::from(1)
    );
    assert_eq!(max.predecessor().unwrap().successor().unwrap(), max);
}

#[test]
fn compact_numerals_convert_to_raw_zero_and_successor_terms() {
    let k = Kernel::default();
    for n in 0..40 {
        let compact = T::natural(Natural::from(u64::from(n)));
        assert_eq!(k.normalize_closed(&unary(n)).unwrap(), compact);
        k.check_closed(
            &T::refl(T::Nat, compact.clone()),
            &T::eq(T::Nat, unary(n), compact),
        )
        .unwrap();
    }
    // The public Literal variant can contain zero, but its normal form is Zero.
    assert_eq!(
        k.normalize_closed(&T::Literal(Natural::default())).unwrap(),
        T::Zero
    );
    k.check_closed(
        &T::refl(T::Nat, T::Zero),
        &T::eq(T::Nat, T::Literal(Natural::default()), T::Zero),
    )
    .unwrap();
    // Open successors stay constructors: no arithmetic on an unknown variable.
    let open = T::lam(T::Nat, T::succ(T::Var(0)));
    assert_eq!(k.normalize_closed(&open).unwrap(), open);
}

#[test]
fn large_literal_magnitude_does_not_consume_syntax_nesting() {
    let k = Kernel::new(Limits {
        steps: 10_000,
        depth: 4,
    });
    let value = term(&"9".repeat(MAX_DIGITS));
    assert_eq!(k.infer_closed(&value).unwrap(), T::Nat);
    assert_eq!(k.normalize_closed(&value).unwrap(), value);
    let too_little_fuel = Kernel::new(Limits {
        steps: 4,
        depth: 128,
    });
    assert!(
        too_little_fuel
            .infer_closed(&value)
            .unwrap_err()
            .0
            .contains("computation budget")
    );
    assert_eq!(too_little_fuel.infer_closed(&term("1")).unwrap(), T::Nat);
}

#[test]
fn kernel_successor_checks_carry_and_distinguishes_adjacent_large_numbers() {
    let k = Kernel::default();
    let before = term("999999999999999999999999999999999999999");
    let after = term("1000000000000000000000000000000000000000");
    assert_eq!(k.normalize_closed(&T::succ(before.clone())).unwrap(), after);
    k.check_closed(
        &T::refl(T::Nat, after.clone()),
        &T::eq(T::Nat, T::succ(before.clone()), after.clone()),
    )
    .unwrap();
    assert!(
        k.check_closed(
            &T::refl(T::Nat, before.clone()),
            &T::eq(T::Nat, before, after)
        )
        .is_err()
    );
    assert!(
        k.infer_closed(&T::app(term("1000000000000000000000000"), T::Zero))
            .is_err()
    );
}

fn eliminate(value: T, step: T) -> T {
    T::NatElim {
        motive: Box::new(T::lam(T::Nat, T::Nat)),
        zero: Box::new(T::Zero),
        step: Box::new(step),
        value: Box::new(value),
    }
}
#[test]
fn induction_retains_its_constructor_equations_for_literals() {
    let k = Kernel::default();
    let step = T::lam(T::Nat, T::lam(T::Nat, T::succ(T::Var(0))));
    for n in 0..8 {
        let compact = T::natural(Natural::from(u64::from(n)));
        assert_eq!(
            k.normalize_closed(&eliminate(compact.clone(), step.clone()))
                .unwrap(),
            compact
        );
        assert_eq!(
            k.normalize_closed(&eliminate(unary(n), step.clone()))
                .unwrap(),
            compact
        );
    }
    let big = term("340282366920938463463374607431768211456");
    // A step ignoring its hypothesis reduces once, without constructing a huge
    // unary value or an eager loop through every preceding case.
    let predecessor = T::lam(T::Nat, T::lam(T::Nat, T::Var(1)));
    assert_eq!(
        k.normalize_closed(&eliminate(big.clone(), predecessor))
            .unwrap(),
        term("340282366920938463463374607431768211455")
    );
    assert!(
        k.normalize_closed(&eliminate(big, step))
            .unwrap_err()
            .0
            .contains("budget")
    );
}

#[test]
fn numeric_budget_exhaustion_cannot_produce_a_false_proof_or_admit_a_global() {
    let mut k = Kernel::default();
    let too_large = T::succ(term(&"9".repeat(MAX_DIGITS)));
    assert!(
        k.normalize_closed(&too_large)
            .unwrap_err()
            .0
            .contains("significant-digit budget")
    );
    let false_type = T::eq(T::Nat, too_large, T::Zero);
    assert!(
        k.define("bad".into(), false_type, T::refl(T::Nat, T::Zero))
            .is_err()
    );
    assert!(!k.contains("bad"));
}

#[test]
fn source_large_naturals_and_proofs_check_end_to_end() {
    let checked = check(include_str!("../../../examples/large-naturals.kush")).unwrap();
    assert_eq!(checked.definitions.len(), 7);
    assert_eq!(
        checked
            .kernel
            .normalize_closed(&T::Global("large".into()))
            .unwrap(),
        term("340282366920938463463374607431768211456")
    );
    let false_proof = include_str!("../../../examples/large-naturals.kush").replace(
        "refl::<Nat>(340282366920938463463374607431768211457)",
        "refl::<Nat>(340282366920938463463374607431768211456)",
    );
    assert!(
        check(&false_proof)
            .unwrap_err()
            .message
            .contains("type mismatch")
    );
}

#[test]
fn source_digit_budget_reports_a_span_and_universe_levels_stay_separate() {
    let source = format!(
        "total fn huge() -> Nat ! {{}} {{ 1{} }}",
        "0".repeat(MAX_DIGITS)
    );
    let error = check(&source).unwrap_err();
    assert!(error.message.contains("significant-digit budget"));
    assert_eq!(
        &source[error.span.start..error.span.end],
        format!("1{}", "0".repeat(MAX_DIGITS))
    );
    let max_proof = format!(
        "total fn max() -> Eq<Nat, {0}, {0}> ! {{}} {{ refl::<Nat>({0}) }}",
        "9".repeat(MAX_DIGITS)
    );
    check(&max_proof).unwrap();
    assert!(
        check("type U = Type<18446744073709551616>;")
            .unwrap_err()
            .message
            .contains("universe levels")
    );
}
