//! Bounded pattern-matrix usefulness checking. Guards never contribute rows.
use crate::{
    Diagnostic, Span,
    executable::{Pattern, Type},
    runtime_types::{Enum, UnionType},
};
#[derive(Clone)]
enum Pat {
    Wild,
    Scalar(i64),
    Variant(usize, Vec<Pat>),
    Or(Vec<Pat>),
}
fn lower(p: &Pattern) -> Pat {
    match p {
        Pattern::Any | Pattern::Bind(_) => Pat::Wild,
        Pattern::Literal(n) => Pat::Scalar(*n),
        Pattern::Variant { tag, fields } => {
            Pat::Variant(*tag, fields.iter().map(|(_, p)| lower(p)).collect())
        }
        Pattern::Type { tag, inner, .. } => Pat::Variant(*tag, vec![lower(inner)]),
        Pattern::Or(ps) => Pat::Or(ps.iter().map(lower).collect()),
    }
}
pub(crate) struct Coverage {
    rows: Vec<Vec<Pat>>,
    budget: usize,
    span: Span,
}
impl Coverage {
    pub fn new(span: Span) -> Self {
        Self {
            rows: Vec::new(),
            budget: 50_000,
            span,
        }
    }
    pub fn useful(
        &mut self,
        pattern: &Pattern,
        ty: Type,
        enums: &[Enum],
        unions: &[UnionType],
    ) -> Result<bool, Diagnostic> {
        useful(
            &self.rows,
            &[lower(pattern)],
            &[ty],
            enums,
            unions,
            &mut self.budget,
            self.span,
        )
    }
    pub fn add(&mut self, pattern: &Pattern) {
        self.rows.push(vec![lower(pattern)]);
    }
}
fn spend(budget: &mut usize, span: Span) -> Result<(), Diagnostic> {
    *budget = budget.checked_sub(1).ok_or_else(|| {
        Diagnostic::new(
            span,
            "pattern coverage budget exhausted; simplify the match or add an earlier catch-all",
        )
    })?;
    Ok(())
}
fn expand(rows: &[Vec<Pat>], budget: &mut usize, span: Span) -> Result<Vec<Vec<Pat>>, Diagnostic> {
    let mut out = Vec::new();
    let mut pending = rows.to_vec();
    while let Some(row) = pending.pop() {
        spend(budget, span)?;
        if let Some(Pat::Or(ps)) = row.first() {
            for p in ps {
                let mut next = vec![p.clone()];
                next.extend_from_slice(&row[1..]);
                pending.push(next);
            }
        } else {
            out.push(row);
        }
    }
    Ok(out)
}
fn specialize(
    rows: &[Vec<Pat>],
    key: Option<usize>,
    scalar: Option<i64>,
    arity: usize,
) -> Vec<Vec<Pat>> {
    rows.iter()
        .filter_map(|row| {
            let mut fields = match row.first()? {
                Pat::Wild => vec![Pat::Wild; arity],
                Pat::Variant(tag, fields) if Some(*tag) == key => fields.clone(),
                Pat::Scalar(n) if Some(*n) == scalar => vec![],
                _ => return None,
            };
            fields.extend_from_slice(&row[1..]);
            Some(fields)
        })
        .collect()
}
fn useful(
    rows: &[Vec<Pat>],
    candidate: &[Pat],
    types: &[Type],
    enums: &[Enum],
    unions: &[UnionType],
    budget: &mut usize,
    span: Span,
) -> Result<bool, Diagnostic> {
    spend(budget, span)?;
    if rows
        .iter()
        .any(|row| row.iter().all(|p| matches!(p, Pat::Wild)))
    {
        return Ok(false);
    }
    if candidate.is_empty() {
        return Ok(true);
    }
    let rows = expand(rows, budget, span)?;
    if let Pat::Or(ps) = &candidate[0] {
        for p in ps {
            let mut next = vec![p.clone()];
            next.extend_from_slice(&candidate[1..]);
            if useful(&rows, &next, types, enums, unions, budget, span)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    match &candidate[0] {
        Pat::Scalar(n) => useful(
            &specialize(&rows, None, Some(*n), 0),
            &candidate[1..],
            &types[1..],
            enums,
            unions,
            budget,
            span,
        ),
        Pat::Variant(tag, fields) => {
            let mut member_types = variant_fields(types[0], *tag, enums, unions);
            let mut next = fields.clone();
            next.extend_from_slice(&candidate[1..]);
            member_types.extend_from_slice(&types[1..]);
            useful(
                &specialize(&rows, Some(*tag), None, fields.len()),
                &next,
                &member_types,
                enums,
                unions,
                budget,
                span,
            )
        }
        Pat::Wild => match types[0] {
            Type::Enum(id) | Type::Variants(id, _) => {
                let mask = crate::runtime_types::mask_of(types[0], enums);
                for (tag, variant) in enums[id].variants.iter().enumerate() {
                    if mask & (1 << tag) == 0 {
                        continue;
                    }
                    let mut next = vec![Pat::Wild; variant.fields.len()];
                    next.extend_from_slice(&candidate[1..]);
                    let mut next_types = variant.fields.clone();
                    next_types.extend_from_slice(&types[1..]);
                    if useful(
                        &specialize(&rows, Some(tag), None, variant.fields.len()),
                        &next,
                        &next_types,
                        enums,
                        unions,
                        budget,
                        span,
                    )? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Union(id) => {
                let members = unions[id].members.clone();
                for (tag, member) in members.iter().enumerate() {
                    let mut next = vec![Pat::Wild];
                    next.extend_from_slice(&candidate[1..]);
                    let mut next_types = vec![*member];
                    next_types.extend_from_slice(&types[1..]);
                    if useful(
                        &specialize(&rows, Some(tag), None, 1),
                        &next,
                        &next_types,
                        enums,
                        unions,
                        budget,
                        span,
                    )? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Bool | Type::Unit => {
                for n in 0..if types[0] == Type::Bool { 2 } else { 1 } {
                    if useful(
                        &specialize(&rows, None, Some(n), 0),
                        &candidate[1..],
                        &types[1..],
                        enums,
                        unions,
                        budget,
                        span,
                    )? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Box(_)
            | Type::Arena
            | Type::ArenaBox(_)
            | Type::Ref(_)
            | Type::RefMut(_)
            | Type::Vec(_)
            | Type::Slice(_)
            | Type::SliceMut(_)
            | Type::Str
            | Type::Fn(_)
            | Type::Once(_)
            | Type::Bytes
            | Type::String
            | Type::Stdin
            | Type::Stdout
            | Type::I64
            | Type::Int(_)
            | Type::Float(_)
            | Type::Char => useful(
                &specialize(&rows, None, None, 0),
                &candidate[1..],
                &types[1..],
                enums,
                unions,
                budget,
                span,
            ),
            Type::Never => Ok(false),
            Type::Task(_) => Ok(false),
        },
        Pat::Or(_) => unreachable!(),
    }
}
/// The field types of one constructor of `ty`: an enum variant (when its mask
/// permits it) or one union alternative.
fn variant_fields(ty: Type, tag: usize, enums: &[Enum], unions: &[UnionType]) -> Vec<Type> {
    match ty {
        Type::Enum(id) | Type::Variants(id, _) => enums[id].variants[tag].fields.clone(),
        Type::Union(id) => vec![unions[id].members[tag]],
        _ => unreachable!(),
    }
}
