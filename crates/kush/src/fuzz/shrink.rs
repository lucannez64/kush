//! PROOF-FUZZ counterexamples: minimize the input, suggest the fact that
//! would let the prover remove the check, and write the input as a
//! `kush test` case. See docs/proof-fuzz.md, section 3.
use super::engine::{element_ranges, element_width, get, put, signed};
use super::harness::{Collection, Layout, Passing, Scalar, Slot, Target};
use crate::executable::{Container, ObligationKind};

/// A decoded argument: a scalar, or a collection's elements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Scalar(i128),
    List(Vec<i128>),
}

/// The values a tape decodes to, in slot order.
pub fn values(layout: &Layout, tape: &[u8]) -> Vec<Value> {
    let ranges = element_ranges(layout, tape);
    layout
        .slots
        .iter()
        .enumerate()
        .map(|(index, slot)| match slot {
            Slot::Scalar { offset, scalar, .. } => {
                Value::Scalar(signed(get(tape, *offset, scalar.width()), *scalar))
            }
            Slot::Collection { collection, .. } => {
                let &(_, start, length) = ranges
                    .iter()
                    .find(|(slot, ..)| *slot == index)
                    .expect("every collection has a range");
                let width = element_width(*collection);
                let element = match collection {
                    Collection::Bytes => Scalar::Int {
                        name: "u8",
                        bytes: 1,
                        signed: false,
                    },
                    Collection::Vec(element) => *element,
                };
                Value::List(
                    (0..length)
                        .map(|k| signed(get(tape, start + k * width, width), element))
                        .collect(),
                )
            }
        })
        .collect()
}

/// The canonical tape of these values (no trailing bytes).
pub fn encode(layout: &Layout, values: &[Value]) -> Vec<u8> {
    let mut tape = vec![0; layout.fixed];
    let mut tail = Vec::new();
    for (slot, value) in layout.slots.iter().zip(values) {
        match (slot, value) {
            (Slot::Scalar { offset, scalar, .. }, Value::Scalar(v)) => {
                put(&mut tape, *offset, scalar.width(), *v);
            }
            (
                Slot::Collection {
                    offset,
                    collection,
                    minimum,
                    maximum,
                    ..
                },
                Value::List(items),
            ) => {
                let extra = items.len().saturating_sub(*minimum).min(*maximum);
                put(&mut tape, *offset, 2, extra as i128);
                let width = element_width(*collection);
                for item in items.iter().take(minimum + extra) {
                    let at = tail.len();
                    put(&mut tail, at, width, *item);
                }
            }
            _ => unreachable!("values follow the layout"),
        }
    }
    tape.extend(tail);
    tape
}

/// Shrink a failing tape while `fails` still holds, spending at most
/// `budget` calls of it. Collections get shorter first, then every number
/// moves as close to zero as it can. Returns the smallest failing tape and
/// the number of calls made.
pub fn shrink(
    layout: &Layout,
    tape: &[u8],
    budget: usize,
    mut fails: impl FnMut(&[u8]) -> bool,
) -> (Vec<u8>, usize) {
    let mut calls = 0;
    let mut best = values(layout, tape);
    let mut try_values = |candidate: &[Value], calls: &mut usize| -> bool {
        if *calls >= budget {
            return false;
        }
        *calls += 1;
        fails(&encode(layout, candidate))
    };
    // The canonical form of the input must fail too; otherwise keep it as is.
    if !try_values(&best, &mut calls) {
        return (tape.to_vec(), calls);
    }
    loop {
        let before = best.clone();
        // Shorter collections: empty, half, then one element less.
        for (index, slot) in layout.slots.iter().enumerate() {
            let Slot::Collection { minimum, .. } = slot else {
                continue;
            };
            loop {
                let Value::List(items) = &best[index] else {
                    unreachable!()
                };
                if items.len() <= *minimum {
                    break;
                }
                let mut shorter = None;
                let lengths = [*minimum, (items.len() + minimum) / 2];
                for length in lengths {
                    if length < items.len() {
                        let mut candidate = best.clone();
                        candidate[index] = Value::List(items[..length].to_vec());
                        if try_values(&candidate, &mut calls) {
                            shorter = Some(candidate);
                            break;
                        }
                    }
                }
                if shorter.is_none() {
                    for remove in 0..items.len() {
                        let mut candidate = best.clone();
                        let mut fewer = items.clone();
                        fewer.remove(remove);
                        candidate[index] = Value::List(fewer);
                        if try_values(&candidate, &mut calls) {
                            shorter = Some(candidate);
                            break;
                        }
                    }
                }
                match shorter {
                    Some(candidate) => best = candidate,
                    None => break,
                }
            }
        }
        // Every number toward zero: zero itself, then a bisection between
        // zero (assumed to pass) and the current value (known to fail).
        let positions: Vec<(usize, Option<usize>)> = best
            .iter()
            .enumerate()
            .flat_map(|(index, value)| match value {
                Value::Scalar(_) => vec![(index, None)],
                Value::List(items) => (0..items.len()).map(|k| (index, Some(k))).collect(),
            })
            .collect();
        for (index, element) in positions {
            let read = |values: &[Value]| match (&values[index], element) {
                (Value::Scalar(v), None) => *v,
                (Value::List(items), Some(k)) => items[k],
                _ => unreachable!(),
            };
            let write = |values: &mut Vec<Value>, v: i128| match (&mut values[index], element) {
                (Value::Scalar(slot), None) => *slot = v,
                (Value::List(items), Some(k)) => items[k] = v,
                _ => unreachable!(),
            };
            let current = read(&best);
            if current == 0 {
                continue;
            }
            let mut candidate = best.clone();
            write(&mut candidate, 0);
            if try_values(&candidate, &mut calls) {
                best = candidate;
                continue;
            }
            let (mut passing, mut failing) = (0i128, current);
            while (failing - passing).abs() > 1 {
                let middle = passing + (failing - passing) / 2;
                let mut candidate = best.clone();
                write(&mut candidate, middle);
                if try_values(&candidate, &mut calls) {
                    failing = middle;
                } else {
                    passing = middle;
                }
            }
            write(&mut best, failing);
        }
        if best == before || calls >= budget {
            break;
        }
    }
    (encode(layout, &best), calls)
}

/// The value range of an integer type by name.
pub fn type_range(name: &str) -> Option<(i128, i128)> {
    let (bits, signed) = match name {
        "i8" => (8, true),
        "i16" => (16, true),
        "i32" => (32, true),
        "i64" => (64, true),
        "u8" => (8, false),
        "u16" => (16, false),
        "u32" => (32, false),
        "u64" => (64, false),
        _ => return None,
    };
    Some(if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    })
}

/// Split `text` at its last top-level binary `op` (outside parentheses and
/// brackets, and not a unary sign): the root operation of a left-associative
/// chain.
fn split_binary(text: &str, op: char) -> Option<(&str, &str)> {
    let bytes = text.as_bytes();
    let mut depth = 0i32;
    let mut found = None;
    for (at, &byte) in bytes.iter().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ if depth == 0 && byte == op as u8 => {
                // A sign after another operator (or at the start) is unary.
                let before = text[..at].trim_end();
                let unary = before.is_empty()
                    || before.ends_with(['+', '-', '*', '/', '%', '(', '[', ',', '=', '<', '>']);
                // `<<` and `>>` are two characters.
                if !unary {
                    found = Some(at);
                }
            }
            _ => {}
        }
    }
    let at = found?;
    let width = if matches!(op, '<' | '>') { 2 } else { 1 };
    let left = text[..at].trim();
    let right = text[at + width..].trim();
    (!left.is_empty() && !right.is_empty()).then_some((left, right))
}

/// `base[index]` into its two parts.
fn split_index(text: &str) -> Option<(&str, &str)> {
    let text = text.trim();
    if !text.ends_with(']') {
        return None;
    }
    let mut depth = 0i32;
    for (at, byte) in text.bytes().enumerate().rev() {
        match byte {
            b']' => depth += 1,
            b'[' => {
                depth -= 1;
                if depth == 0 {
                    return Some((text[..at].trim(), text[at + 1..text.len() - 1].trim()));
                }
            }
            _ => {}
        }
    }
    None
}

fn is_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// What would let the prover discharge this check: an erased precondition
/// when the check only involves `function`'s parameters, otherwise the
/// missing fact about the value that comes from elsewhere.
pub fn suggestion(kind: ObligationKind, text: &str, goal: &str, function: &Target) -> String {
    let runtime: Vec<&str> = function
        .parameters
        .iter()
        .filter(|(_, erased)| !erased)
        .map(|(name, _)| name.as_str())
        .collect();
    let known = |operand: &str| {
        runtime.contains(&operand) || super::harness::integer_literal(operand).is_some()
    };
    let unknown = |operands: &[&str]| -> Option<String> {
        operands
            .iter()
            .find(|operand| !known(operand))
            .map(|operand| operand.to_string())
    };
    let lemma = |operand: &str| {
        format!(
            "the prover has no fact bounding `{operand}` here: state its range with an \
             `ensures` on the function that computes it, a loop `invariant`, or an earlier check"
        )
    };
    let on = &function.function;
    match kind {
        ObligationKind::Bounds { container, .. } => {
            let Some((base, index)) = split_index(text) else {
                return format!("check the index before `{text}`, or state its range as a precondition");
            };
            let length = match container {
                Container::Vec => "Vec",
                Container::Bytes => "Bytes",
                Container::Slice => "Slice",
                Container::Array => {
                    return format!("state the range of `{index}` as a precondition of {on}");
                }
            };
            if !runtime.contains(&base) || !is_identifier(base) {
                return format!(
                    "`{base}` has no stated length here: give the field a length refinement \
                     (`where len >= N`) or pass the container as a parameter"
                );
            }
            match unknown(&[index]) {
                Some(operand) => lemma(&operand),
                None => format!(
                    "`erased in_bounds: {{ 0 <= {index} && {index} < {length}.len({base}) }}` on {on}, \
                     and read with `{length}.at({base}, {index}, _)`; callers then prove it"
                ),
            }
        }
        ObligationKind::Overflow => {
            let Some(type_name) = goal.rsplit(' ').next() else {
                return lemma(text);
            };
            let Some((low, high)) = type_range(type_name) else {
                return lemma(text);
            };
            if let Some(operand) = text.trim().strip_prefix('-') {
                let operand = operand.trim();
                return match unknown(&[operand]) {
                    Some(operand) => lemma(&operand),
                    None => format!("`erased fits: {{ {} < {operand} }}` on {on}; callers then prove it", low),
                };
            }
            let op = ['+', '-', '*']
                .into_iter()
                .find(|op| goal.contains(&format!("of {op} stays")))
                .unwrap_or('+');
            let Some((left, right)) = split_binary(text, op) else {
                return lemma(text);
            };
            if let Some(operand) = unknown(&[left, right]) {
                return lemma(&operand);
            }
            if op == '*' && !(super::harness::integer_literal(left).is_some()
                || super::harness::integer_literal(right).is_some())
            {
                return format!(
                    "`{left} * {right}` is a product of two values, which the prover does not \
                     reason about: bound each factor with a precondition of {on} and keep the \
                     product checked, or check it explicitly"
                );
            }
            let expression = format!("{left} {op} {right}");
            format!(
                "`erased fits: {{ {low} <= {expression} && {expression} <= {high} }}` on {on}; \
                 callers then prove it"
            )
        }
        ObligationKind::Division => match split_binary(text, '/').or_else(|| split_binary(text, '%')) {
            Some((_, divisor)) if known(divisor) => format!(
                "`erased nonzero: {{ {divisor} != 0 }}` on {on} (and rule out MIN / -1 for signed types); \
                 division keeps a run-time check"
            ),
            Some((_, divisor)) => lemma(divisor),
            None => lemma(text),
        },
        ObligationKind::Shift => {
            let split = split_binary(text, '<').or_else(|| split_binary(text, '>'));
            match split {
                Some((_, amount)) => format!(
                    "a shift amount stays checked; `{amount}` must be below the width of the shifted type"
                ),
                None => lemma(text),
            }
        }
    }
}

/// Kush source for one value of `scalar`'s type.
fn literal(value: i128, scalar: Scalar) -> String {
    match scalar {
        Scalar::Bool => (value != 0).to_string(),
        Scalar::Int { name: "i64", .. } => i64_literal(value as i64),
        Scalar::Int { .. } => {
            // Its two's-complement bits as an i64, truncated to the type.
            format!("Int.truncate({})", i64_literal(value as i64))
        }
    }
}

fn i64_literal(value: i64) -> String {
    if value == i64::MIN {
        "0 - 9223372036854775807 - 1".into()
    } else if value < 0 {
        format!("0 - {}", value.unsigned_abs())
    } else {
        value.to_string()
    }
}

/// The function name a generated test gets.
pub fn test_name(target: &Target, line: usize) -> String {
    format!("fuzz_{}_line_{line}", target.function)
}

/// A `#[test]` that calls `target` with `values`, for the test target.
/// Only public functions outside the entry file can be called from there.
pub fn reproduction(
    target: &Target,
    layout: &Layout,
    values: &[Value],
    what: &str,
    line: usize,
) -> Option<String> {
    if !target.public || target.entry {
        return None;
    }
    let mut body = String::new();
    let mut slots = layout.slots.iter().zip(values);
    let mut arguments = Vec::new();
    for (name, erased) in &target.parameters {
        if *erased {
            arguments.push("_".to_owned());
            continue;
        }
        let (slot, value) = slots.next()?;
        match (slot, value) {
            (Slot::Scalar { scalar, passing, .. }, Value::Scalar(v)) => {
                body.push_str(&format!(
                    "    let {name}: {} = {};\n",
                    scalar_type(*scalar),
                    literal(*v, *scalar)
                ));
                arguments.push(pass(name, *passing));
            }
            (
                Slot::Collection {
                    collection,
                    passing,
                    ..
                },
                Value::List(items),
            ) => {
                match collection {
                    Collection::Bytes => {
                        body.push_str(&format!(
                            "    let mut {name} = Bytes.with_capacity({});\n",
                            items.len()
                        ));
                        for item in items {
                            body.push_str(&format!("    {name} = Bytes.push({name}, {item});\n"));
                        }
                    }
                    Collection::Vec(element) => {
                        body.push_str(&format!(
                            "    let mut {name}: Vec<{}> = Vec.new();\n",
                            scalar_type(*element)
                        ));
                        for item in items {
                            body.push_str(&format!(
                                "    {name} = {name}.push({});\n",
                                literal(*item, *element)
                            ));
                        }
                    }
                }
                arguments.push(pass(name, *passing));
            }
            _ => return None,
        }
    }
    // An entry lives in the test target itself.
    let callee = if target.fuzz_entry {
        target.function.clone()
    } else {
        format!("{}.{}", target.module.last()?, target.function)
    };
    Some(format!(
        "#[test]\nfn {}() -> Unit ! {{io, alloc, panic}} {{\n    // kush fuzz: {what}\n{body}    let _ = {callee}({});\n}}\n",
        test_name(target, line),
        arguments.join(", ")
    ))
}

fn scalar_type(scalar: Scalar) -> &'static str {
    match scalar {
        Scalar::Int { name, .. } => name,
        Scalar::Bool => "Bool",
    }
}

fn pass(name: &str, passing: Passing) -> String {
    match passing {
        Passing::Value => name.to_owned(),
        Passing::Shared => format!("&{name}"),
        Passing::Exclusive => format!("&mut {name}"),
        Passing::Slice => format!("&{name}[..]"),
    }
}
