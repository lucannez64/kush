//! Representation-disjointness certificates (docs/unboxing-certificates.md).
//!
//! A layout that omits an enum's tag word must come with a [`Certificate`]:
//! for each variant, the set of bit patterns it may hold in word 0. The
//! chooser ([`choose`]) is untrusted; [`check`] recomputes every set from the
//! value-set domain ([`value_set`]) and accepts only disjoint, decodable
//! certificates. Matching, construction and drop glue use the [`Decoder`]
//! generated from a checked certificate, so they cannot drift apart.
//!
//! The domain is per instantiated type and never follows an indirection, so it
//! terminates without a recursion bound beyond [`MAX_DEPTH`] for inline enums.

use crate::executable::Type;
use crate::runtime_types::{Enum, Niche};

/// At most this many closed intervals per value set.
pub(crate) const MAX_INTERVALS: usize = 8;
/// Inline enums examined below this depth keep their explicit tag.
pub(crate) const MAX_DEPTH: usize = 4;

/// A set of 64-bit words: a union of sorted, disjoint, non-adjacent closed
/// intervals, restricted to multiples of `align`. Sets are supersets of the
/// values a type can hold (over-approximation is sound for disjointness).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ValueSet {
    intervals: Vec<(u64, u64)>,
    align: u64,
}

impl ValueSet {
    pub(crate) fn top() -> Self {
        Self {
            intervals: vec![(0, u64::MAX)],
            align: 1,
        }
    }
    pub(crate) fn singleton(value: u64) -> Self {
        Self {
            intervals: vec![(value, value)],
            align: 1,
        }
    }
    /// Normalize: sort, merge overlapping or adjacent intervals. `None` when
    /// the result needs more than [`MAX_INTERVALS`] intervals or is empty.
    pub(crate) fn new(mut intervals: Vec<(u64, u64)>, align: u64) -> Option<Self> {
        if align == 0 || !align.is_power_of_two() || intervals.iter().any(|(a, b)| a > b) {
            return None;
        }
        intervals.sort();
        let mut merged: Vec<(u64, u64)> = Vec::new();
        for (low, high) in intervals {
            match merged.last_mut() {
                Some((_, last)) if low <= last.saturating_add(1) => *last = (*last).max(high),
                _ => merged.push((low, high)),
            }
        }
        (!merged.is_empty() && merged.len() <= MAX_INTERVALS).then_some(Self {
            intervals: merged,
            align,
        })
    }
    pub(crate) fn is_top(&self) -> bool {
        self.align == 1 && self.intervals == [(0, u64::MAX)]
    }
    pub(crate) fn contains(&self, value: u64) -> bool {
        value.is_multiple_of(self.align)
            && self
                .intervals
                .iter()
                .any(|(low, high)| *low <= value && value <= *high)
    }
    /// The smallest multiple of `align` that is at least `low`, if any.
    fn first_multiple(low: u64, align: u64) -> Option<u64> {
        let remainder = low % align;
        if remainder == 0 {
            Some(low)
        } else {
            low.checked_add(align - remainder)
        }
    }
    /// Exact emptiness of the intersection (alignments are powers of two, so
    /// their least common multiple is the larger one).
    pub(crate) fn intersects(&self, other: &Self) -> bool {
        let align = self.align.max(other.align);
        self.intervals.iter().any(|(a_low, a_high)| {
            other.intervals.iter().any(|(b_low, b_high)| {
                let low = (*a_low).max(*b_low);
                let high = (*a_high).min(*b_high);
                low <= high && Self::first_multiple(low, align).is_some_and(|x| x <= high)
            })
        })
    }
    /// A superset of the union (the smaller alignment is kept).
    pub(crate) fn union(&self, other: &Self) -> Self {
        let mut intervals = self.intervals.clone();
        intervals.extend(other.intervals.iter().copied());
        Self::new(intervals, self.align.min(other.align)).unwrap_or_else(Self::top)
    }
    /// The chooser's niche constant: the smallest word above the set's
    /// maximum, otherwise the smallest word outside the set.
    pub(crate) fn first_free(&self) -> Option<u64> {
        let max = self.intervals.last()?.1;
        if let Some(above) = max.checked_add(1) {
            return Some(above);
        }
        // The smallest word outside is 0, one past an interval, or one past
        // the first aligned member of an interval (an unaligned word).
        let mut candidates = vec![0];
        for (low, high) in &self.intervals {
            candidates.extend(high.checked_add(1));
            if self.align > 1 {
                candidates
                    .extend(Self::first_multiple(*low, self.align).and_then(|x| x.checked_add(1)));
            }
        }
        candidates.into_iter().filter(|x| !self.contains(*x)).min()
    }
}

/// The value set of word 0 of a value of type `ty`. Only types with a known
/// discriminating word are refined; everything else is `⊤` (trusted host
/// representations, integers, floats including every NaN payload).
pub(crate) fn value_set(ty: Type, enums: &[Enum], depth: usize) -> ValueSet {
    match ty {
        Type::Bool => ValueSet::new(vec![(0, 1)], 1).unwrap(),
        Type::Char => ValueSet::new(vec![(0, 0xD7FF), (0xE000, 0x10FFFF)], 1).unwrap(),
        // Nonzero and pointer aligned (UNBOX-ALIGN-CONTRACT); expansion
        // never follows the pointee.
        Type::Box(_) | Type::Ref(_) | Type::RefMut(_) => {
            ValueSet::new(vec![(1, u64::MAX)], crate::native::POINTER_ALIGN).unwrap()
        }
        Type::Enum(id) if depth < MAX_DEPTH => {
            let Some(layout) = enums.get(id) else {
                return ValueSet::top();
            };
            if layout.foreign.is_some() || layout.result.is_some() {
                return ValueSet::top();
            }
            if let Some(niche) = layout.niche() {
                let payload = layout.variants[niche.payload_tag].fields[0];
                return value_set(payload, enums, depth + 1)
                    .union(&ValueSet::singleton(niche.sentinel as u64));
            }
            ValueSet::top()
        }
        _ => ValueSet::top(),
    }
}

/// The evidence for one variant's word-0 values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum VariantSet {
    /// A one-field payload variant: the field's value set.
    Payload(ValueSet),
    /// An empty variant stored as this constant.
    Niche(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Certificate {
    pub word: usize,
    pub variants: Vec<VariantSet>,
}

/// Why a certificate was refused. Refusal means an explicit tag, never a
/// compile error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Refusal {
    Ineligible,
    NotWordZero,
    VariantCount,
    PayloadShape,
    PayloadSetMismatch,
    Overlap,
    TooManyPayloads,
}

fn eligible(layout: &Enum) -> bool {
    !layout.record
        && layout.foreign.is_none()
        && layout.result.is_none()
        && layout.array.is_none()
        && layout.dynamic_array.is_none()
}

/// The untrusted chooser for the layouts enabled today: exactly two variants,
/// one empty and one single-field payload whose word-0 set leaves room.
/// Payloads are restricted to the scalar and pointer types of the original
/// niche layouts, so no other layout changes.
pub(crate) fn choose(layout: &Enum) -> Option<Certificate> {
    if !eligible(layout) || layout.variants.len() != 2 {
        return None;
    }
    let empty = layout.variants.iter().position(|v| v.fields.is_empty())?;
    let payload = 1 - empty;
    let [field] = layout.variants[payload].fields.as_slice() else {
        return None;
    };
    if !matches!(
        field,
        Type::Box(_) | Type::Ref(_) | Type::RefMut(_) | Type::Bool | Type::Char
    ) {
        return None;
    }
    let set = value_set(*field, &[], 0);
    let constant = set.first_free()?;
    let mut variants = vec![VariantSet::Niche(constant); 2];
    variants[payload] = VariantSet::Payload(set);
    Some(Certificate { word: 0, variants })
}

/// The independent checker. Every payload set is recomputed from
/// [`value_set`]; the chooser's sets are only compared, never believed.
pub(crate) fn check(
    layout: &Enum,
    enums: &[Enum],
    certificate: &Certificate,
) -> Result<(), Refusal> {
    if !eligible(layout) {
        return Err(Refusal::Ineligible);
    }
    if certificate.word != 0 {
        return Err(Refusal::NotWordZero);
    }
    if certificate.variants.len() != layout.variants.len() || layout.variants.len() < 2 {
        return Err(Refusal::VariantCount);
    }
    let mut payloads = 0;
    let mut sets = Vec::new();
    for (variant, claimed) in layout.variants.iter().zip(&certificate.variants) {
        match (variant.fields.as_slice(), claimed) {
            ([], VariantSet::Niche(constant)) => sets.push(ValueSet::singleton(*constant)),
            ([field], VariantSet::Payload(set)) => {
                let actual = value_set(*field, enums, 0);
                if actual != *set || actual.is_top() {
                    return Err(Refusal::PayloadSetMismatch);
                }
                payloads += 1;
                sets.push(actual);
            }
            _ => return Err(Refusal::PayloadShape),
        }
    }
    // One payload variant keeps the decoder to "not any niche constant".
    if payloads != 1 {
        return Err(Refusal::TooManyPayloads);
    }
    for (index, left) in sets.iter().enumerate() {
        for right in &sets[index + 1..] {
            if left.intersects(right) {
                return Err(Refusal::Overlap);
            }
        }
    }
    Ok(())
}

/// The membership test of one variant, generated from a checked certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Decoder {
    /// Word 0 equals this constant.
    Equal(i64),
    /// Word 0 differs from this constant (the only niche constant, so the
    /// payload variant is exactly the complement).
    NotEqual(i64),
}

impl Niche {
    /// The test that selects `tag`, derived from the checked certificate.
    pub(crate) fn decoder(&self, tag: usize) -> Decoder {
        if tag == self.empty_tag {
            Decoder::Equal(self.sentinel)
        } else {
            debug_assert_eq!(tag, self.payload_tag);
            Decoder::NotEqual(self.sentinel)
        }
    }
}

/// Choose and check a niche layout for `layout`; only a checked certificate
/// becomes a [`Niche`].
pub(crate) fn certified_niche(layout: &Enum) -> Option<Niche> {
    let certificate = choose(layout)?;
    check(layout, &[], &certificate).ok()?;
    let empty_tag = certificate
        .variants
        .iter()
        .position(|v| matches!(v, VariantSet::Niche(_)))?;
    let VariantSet::Niche(constant) = certificate.variants[empty_tag] else {
        return None;
    };
    Some(Niche {
        payload_tag: 1 - empty_tag,
        empty_tag,
        sentinel: constant as i64,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executable::check as check_program;

    /// The instantiated `Option` layouts of a program with one local per
    /// payload type, plus the whole enum table. A payload is identified by a
    /// predicate on the `Some` field's type.
    type Payload = (&'static str, fn(Type) -> bool);

    fn layouts(payloads: &[Payload]) -> (Vec<Enum>, Vec<usize>) {
        let locals = payloads
            .iter()
            .enumerate()
            .map(|(i, (p, _))| format!("let v{i}: Option<{p}> = Option.None; drop(v{i});"))
            .collect::<String>();
        let source = format!(
            "struct P {{ x: i64 }} enum Option<T> {{ None, Some(T) }}
             fn main() -> Unit ! {{}} {{ {locals} }}"
        );
        let program = check_program(&source).unwrap();
        let ids = payloads
            .iter()
            .map(|(payload, matches)| {
                program
                    .enums
                    .iter()
                    .rposition(|layout| {
                        layout.name == "Option"
                            && layout.variants[1]
                                .fields
                                .first()
                                .is_some_and(|ty| matches(*ty))
                    })
                    .unwrap_or_else(|| panic!("no layout for {payload}"))
            })
            .collect();
        (program.enums, ids)
    }

    #[test]
    fn the_three_existing_niches_are_reproduced_bit_for_bit() {
        type Case = (&'static str, fn(Type) -> bool, i64);
        let cases: [Case; 5] = [
            ("Box<i64>", |t| matches!(t, Type::Box(_)), 0),
            ("&P", |t| matches!(t, Type::Ref(_)), 0),
            ("&mut P", |t| matches!(t, Type::RefMut(_)), 0),
            ("Bool", |t| t == Type::Bool, 2),
            ("Char", |t| t == Type::Char, 0x110000),
        ];
        let (enums, ids) = layouts(&cases.map(|(payload, matches, _)| (payload, matches)));
        for ((payload, _, sentinel), id) in cases.iter().zip(ids) {
            let layout = &enums[id];
            let certificate = choose(layout).unwrap();
            assert_eq!(check(layout, &enums, &certificate), Ok(()), "{payload}");
            let niche = layout.niche().unwrap();
            assert_eq!(niche.sentinel, *sentinel, "{payload}");
            assert_eq!((niche.empty_tag, niche.payload_tag), (0, 1), "{payload}");
            assert_eq!(niche.decoder(0), Decoder::Equal(*sentinel));
            assert_eq!(niche.decoder(1), Decoder::NotEqual(*sentinel));
            assert_eq!(layout.words, 1, "{payload}");
        }
    }

    #[test]
    fn full_range_payloads_and_ineligible_layouts_get_no_certificate() {
        let (enums, ids) = layouts(&[
            ("i64", |t| t == Type::I64),
            ("u64", |t| matches!(t, Type::Int(_))),
            ("f64", |t| matches!(t, Type::Float(_))),
            ("Bytes", |t| t == Type::Bytes),
            ("Option<Box<i64>>", |t| matches!(t, Type::Enum(_))),
        ]);
        for id in ids {
            assert_eq!(choose(&enums[id]), None, "{}", enums[id].name);
            assert_eq!(enums[id].niche(), None);
        }
    }

    fn forged(layout: &Enum, enums: &[Enum], certificate: Certificate) -> Refusal {
        check(layout, enums, &certificate).unwrap_err()
    }

    #[test]
    fn forged_certificates_are_refused() {
        let (enums, ids) = layouts(&[
            ("Bool", |t| t == Type::Bool),
            ("Char", |t| t == Type::Char),
            ("Box<i64>", |t| matches!(t, Type::Box(_))),
            ("f64", |t| matches!(t, Type::Float(_))),
        ]);
        let (boolean, character, boxed, float) = (
            &enums[ids[0]],
            &enums[ids[1]],
            &enums[ids[2]],
            &enums[ids[3]],
        );
        let bool_set = value_set(Type::Bool, &enums, 0);
        // A niche constant inside the payload set.
        for constant in [0, 1] {
            assert_eq!(
                forged(
                    boolean,
                    &enums,
                    Certificate {
                        word: 0,
                        variants: vec![
                            VariantSet::Niche(constant),
                            VariantSet::Payload(bool_set.clone())
                        ]
                    }
                ),
                Refusal::Overlap
            );
        }
        // A payload set claimed smaller than the type's: recomputed, refused.
        let small = ValueSet::new(vec![(0, 0x10)], 1).unwrap();
        assert_eq!(
            forged(
                character,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(0x11), VariantSet::Payload(small)]
                }
            ),
            Refusal::PayloadSetMismatch
        );
        // The surrogate gap is not a niche for the null pointer case either:
        // a box set claimed to exclude 8 is refused.
        let holey = ValueSet::new(vec![(16, u64::MAX)], 8).unwrap();
        assert_eq!(
            forged(
                boxed,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(8), VariantSet::Payload(holey)]
                }
            ),
            Refusal::PayloadSetMismatch
        );
        // Floats have no niche: every NaN payload is a value.
        assert_eq!(
            forged(
                float,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(0), VariantSet::Payload(ValueSet::top())]
                }
            ),
            Refusal::PayloadSetMismatch
        );
        // Discrimination uses word 0 only.
        assert_eq!(
            forged(
                boolean,
                &enums,
                Certificate {
                    word: 1,
                    variants: vec![VariantSet::Niche(2), VariantSet::Payload(bool_set.clone())]
                }
            ),
            Refusal::NotWordZero
        );
        // Shapes: a niche for the payload variant, a payload for the empty
        // one, wrong arity, two niches and no payload.
        assert_eq!(
            forged(
                boolean,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(2), VariantSet::Niche(3)]
                }
            ),
            Refusal::PayloadShape
        );
        assert_eq!(
            forged(
                boolean,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![
                        VariantSet::Payload(bool_set.clone()),
                        VariantSet::Payload(bool_set.clone())
                    ]
                }
            ),
            Refusal::PayloadShape
        );
        assert_eq!(
            forged(
                boolean,
                &enums,
                Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(2)]
                }
            ),
            Refusal::VariantCount
        );
    }

    #[test]
    fn records_results_and_foreign_layouts_are_never_certified() {
        let program = check_program(
            "struct One { b: Bool } enum Result<T, E> { Ok(T), Err(E) }
             fn main() -> i64 ! {} { let r: Result<Bool, Unit> = Result.Ok(true); let o = One { b: true }; drop(o); match r { Result.Ok(_) => 1, Result.Err(_) => 0 } }",
        )
        .unwrap();
        let mut seen = (0, 0);
        for layout in &program.enums {
            seen.0 += usize::from(layout.record);
            seen.1 += usize::from(layout.result.is_some());
            if layout.record || layout.result.is_some() {
                let certificate = Certificate {
                    word: 0,
                    variants: vec![VariantSet::Niche(2); layout.variants.len()],
                };
                assert_eq!(
                    check(layout, &program.enums, &certificate),
                    Err(Refusal::Ineligible),
                    "{}",
                    layout.name
                );
                assert_eq!(layout.niche(), None);
            }
        }
        assert!(seen.0 >= 1 && seen.1 >= 1, "{seen:?}");
    }

    #[test]
    fn value_set_domain_laws() {
        // Normalization merges overlapping and adjacent intervals.
        let set = ValueSet::new(vec![(5, 9), (0, 2), (3, 4), (20, 30)], 1).unwrap();
        assert_eq!(set.intervals, vec![(0, 9), (20, 30)]);
        // More than MAX_INTERVALS intervals is refused, not truncated.
        let many = (0..=MAX_INTERVALS as u64)
            .map(|i| (i * 10, i * 10 + 1))
            .collect();
        assert_eq!(ValueSet::new(many, 1), None);
        assert_eq!(ValueSet::new(vec![(3, 1)], 1), None);
        assert_eq!(ValueSet::new(vec![(1, 3)], 3), None);
        // Alignment: {8, 16, ...} misses 1..7 and the surrogate-like gap.
        let pointer = ValueSet::new(vec![(1, u64::MAX)], 8).unwrap();
        assert!(!pointer.contains(0) && !pointer.contains(7) && pointer.contains(8));
        assert!(!pointer.intersects(&ValueSet::new(vec![(1, 7)], 1).unwrap()));
        assert!(pointer.intersects(&ValueSet::new(vec![(1, 8)], 1).unwrap()));
        assert!(!pointer.intersects(&ValueSet::singleton(0)));
        assert_eq!(pointer.first_free(), Some(0));
        // Char boundaries.
        let character = value_set(Type::Char, &[], 0);
        for (code, inside) in [
            (0xD7FF, true),
            (0xD800, false),
            (0xDFFF, false),
            (0xE000, true),
            (0x10FFFF, true),
            (0x110000, false),
        ] {
            assert_eq!(character.contains(code), inside, "{code:#x}");
        }
        assert_eq!(character.first_free(), Some(0x110000));
        assert_eq!(value_set(Type::Bool, &[], 0).first_free(), Some(2));
        // Union is a superset of both sides.
        let union = character.union(&ValueSet::singleton(0x110000));
        for code in [0, 0xD7FF, 0xE000, 0x10FFFF, 0x110000] {
            assert!(union.contains(code));
        }
        assert!(!union.contains(0xD800));
        // Top intersects everything and has no free word.
        assert!(ValueSet::top().intersects(&ValueSet::singleton(u64::MAX)));
        assert_eq!(ValueSet::top().first_free(), None);
    }
}

/// Measurement harness for UNBOX-MULTI-NICHE and UNBOX-TAG-NICHE: how many
/// instantiated layouts in the repository's Kush programs would lose their
/// tag word under each extension. Run with
/// `mbx test -p kush --lib layout_cert::census -- --ignored --nocapture`.
#[cfg(test)]
mod census {
    use super::*;

    #[derive(Debug, Default)]
    struct Counts {
        programs: usize,
        failed: usize,
        layouts: usize,
        tagged: usize,
        niche_today: usize,
        multi_empty: Vec<String>,
        nested: Vec<String>,
        tag_niche: Vec<String>,
    }

    fn classify(enums: &[Enum], file: &str, counts: &mut Counts) {
        for layout in enums {
            counts.layouts += 1;
            if !eligible(layout) || layout.tuple || layout.structural {
                continue;
            }
            if layout.niche().is_some() {
                counts.niche_today += 1;
                continue;
            }
            if layout.tag_words() == 0 {
                continue;
            }
            counts.tagged += 1;
            let empties = layout
                .variants
                .iter()
                .filter(|v| v.fields.is_empty())
                .count();
            let payloads = layout
                .variants
                .iter()
                .filter(|v| !v.fields.is_empty())
                .collect::<Vec<_>>();
            let [payload] = payloads.as_slice() else {
                continue;
            };
            let [field] = payload.fields.as_slice() else {
                continue;
            };
            let name = format!("{file}: {}", layout.name);
            if empties == 0 {
                continue;
            }
            match field {
                Type::Enum(inner) if enums[*inner].niche().is_some() => counts.nested.push(name),
                Type::Enum(inner)
                    if enums[*inner].tag_words() == 1
                        && eligible(&enums[*inner])
                        && !enums[*inner].tuple =>
                {
                    counts.tag_niche.push(name)
                }
                Type::Bool | Type::Char | Type::Box(_) | Type::Ref(_) | Type::RefMut(_)
                    if empties >= 2 =>
                {
                    counts.multi_empty.push(name)
                }
                _ => {}
            }
        }
    }

    #[test]
    #[ignore]
    fn census_of_extension_candidates() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut files = Vec::new();
        for directory in [
            "examples",
            "benchmarks",
            "crates/kush/std",
            "crates/kush/tests/fixtures",
        ] {
            let mut stack = vec![root.join(directory)];
            while let Some(path) = stack.pop() {
                for entry in std::fs::read_dir(&path).into_iter().flatten().flatten() {
                    let path = entry.path();
                    if path.is_dir() {
                        stack.push(path);
                    } else if path.extension().is_some_and(|e| e == "kush") {
                        files.push(path);
                    }
                }
            }
        }
        files.sort();
        let mut counts = Counts::default();
        for file in &files {
            let source = std::fs::read_to_string(file).unwrap();
            let name = file.strip_prefix(&root).unwrap().display().to_string();
            match crate::executable::check(&source) {
                Ok(program) => {
                    counts.programs += 1;
                    classify(&program.enums, &name, &mut counts);
                }
                Err(_) => counts.failed += 1,
            }
        }
        // Projects: load each manifest's entry with its modules.
        for manifest in [
            "benchmarks/json-memory/Kush.toml",
            "benchmarks/feature-pipeline/kush/Kush.toml",
            "examples/otp-tui/Kush.toml",
            "examples/todo-cli/Kush.toml",
            "examples/project-demo/Kush.toml",
        ] {
            let Ok(project) = crate::project::load_manifest(&root.join(manifest)) else {
                counts.failed += 1;
                continue;
            };
            let entry = project.package.entry_path();
            match project
                .load_program(&entry)
                .ok()
                .and_then(|program| crate::executable::check_program(&program).ok())
            {
                Some(checked) => {
                    counts.programs += 1;
                    classify(&checked.enums, manifest, &mut counts);
                }
                None => counts.failed += 1,
            }
        }
        println!("files: {}", files.len());
        println!("{counts:#?}");
    }
}
