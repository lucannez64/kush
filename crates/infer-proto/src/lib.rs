//! Isolated research prototype for RES-INFERENCE-PROTOTYPE.
//!
//! A tiny lambda calculus with multi-bounded type variables in the style of
//! Simple-sub / SuperF (each variable keeps sets of lower and upper bounds
//! instead of being unified), let-polymorphism by levels, effect rows on
//! arrows as a bitset lattice, an explicit annotation escape hatch for
//! first-class polymorphic parameters, and a deterministic step budget.
//!
//! After inference, a type is coalesced into union/intersection form and
//! checked against what Kush can represent (no recursive types, no
//! intersections of distinct scalars, unions of distinct representations
//! flagged as needing a representation-changing coercion).
//!
//! The compiler does not use this crate. See `docs/inference-prototype.md`.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Surface: s-expressions
// ---------------------------------------------------------------------------

/// A parsed s-expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Parse one s-expression.
pub fn parse(source: &str) -> Result<Sexp, String> {
    let tokens = source
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let mut position = 0;
    let sexp = parse_at(&tokens, &mut position)?;
    if position != tokens.len() {
        return Err("trailing input".into());
    }
    Ok(sexp)
}

fn parse_at(tokens: &[String], position: &mut usize) -> Result<Sexp, String> {
    let token = tokens.get(*position).ok_or("unexpected end of input")?;
    *position += 1;
    match token.as_str() {
        "(" => {
            let mut items = Vec::new();
            while tokens.get(*position).map(String::as_str) != Some(")") {
                if *position >= tokens.len() {
                    return Err("unclosed '('".into());
                }
                items.push(parse_at(tokens, position)?);
            }
            *position += 1;
            Ok(Sexp::List(items))
        }
        ")" => Err("unexpected ')'".into()),
        atom => Ok(Sexp::Atom(atom.to_owned())),
    }
}

/// Source terms.
#[derive(Debug, Clone)]
pub enum Term {
    Int,
    Bool,
    Var(String),
    /// `(lam x body)` or `(lam (x : T) body)`.
    Lam(String, Option<Annot>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
    If(Box<Term>, Box<Term>, Box<Term>),
    /// `(ann e T)`: check `e` against a monotype annotation.
    Ann(Box<Term>, Annot),
}

/// Type annotations: `int`, `bool`, `a` (a `forall` variable),
/// `(-> A B)`, `(->! io A B)`, `(forall (a b) T)`.
#[derive(Debug, Clone, PartialEq)]
pub enum Annot {
    Int,
    Bool,
    Name(String),
    Fun(Box<Annot>, Box<Annot>, u16),
    Forall(Vec<String>, Box<Annot>),
}

/// Effect bits (a subset of Kush's row universe).
pub const IO: u16 = 1;
pub const ALLOC: u16 = 2;
pub const PANIC: u16 = 4;

fn effect_bit(name: &str) -> Result<u16, String> {
    match name {
        "io" => Ok(IO),
        "alloc" => Ok(ALLOC),
        "panic" => Ok(PANIC),
        _ => Err(format!("unknown effect '{name}'")),
    }
}

fn atom(sexp: &Sexp) -> Option<&str> {
    match sexp {
        Sexp::Atom(atom) => Some(atom),
        Sexp::List(_) => None,
    }
}

pub fn term(sexp: &Sexp) -> Result<Term, String> {
    match sexp {
        Sexp::Atom(a) if a.parse::<i64>().is_ok() => Ok(Term::Int),
        Sexp::Atom(a) if a == "true" || a == "false" => Ok(Term::Bool),
        Sexp::Atom(a) => Ok(Term::Var(a.clone())),
        Sexp::List(items) => match items.first().and_then(atom) {
            Some("lam") if items.len() == 3 => {
                let (name, annot) = match &items[1] {
                    Sexp::Atom(name) => (name.clone(), None),
                    Sexp::List(binder) if binder.len() == 3 && atom(&binder[1]) == Some(":") => (
                        atom(&binder[0]).ok_or("bad binder")?.to_owned(),
                        Some(annot(&binder[2])?),
                    ),
                    _ => return Err("bad lambda binder".into()),
                };
                Ok(Term::Lam(name, annot, Box::new(term(&items[2])?)))
            }
            Some("app") if items.len() >= 3 => {
                let mut result = term(&items[1])?;
                for argument in &items[2..] {
                    result = Term::App(Box::new(result), Box::new(term(argument)?));
                }
                Ok(result)
            }
            Some("let") if items.len() == 4 => Ok(Term::Let(
                atom(&items[1]).ok_or("bad let name")?.to_owned(),
                Box::new(term(&items[2])?),
                Box::new(term(&items[3])?),
            )),
            Some("if") if items.len() == 4 => Ok(Term::If(
                Box::new(term(&items[1])?),
                Box::new(term(&items[2])?),
                Box::new(term(&items[3])?),
            )),
            Some("ann") if items.len() == 3 => {
                Ok(Term::Ann(Box::new(term(&items[1])?), annot(&items[2])?))
            }
            _ => Err(format!("bad term {sexp:?}")),
        },
    }
}

pub fn annot(sexp: &Sexp) -> Result<Annot, String> {
    match sexp {
        Sexp::Atom(a) if a == "int" => Ok(Annot::Int),
        Sexp::Atom(a) if a == "bool" => Ok(Annot::Bool),
        Sexp::Atom(a) => Ok(Annot::Name(a.clone())),
        Sexp::List(items) => match items.first().and_then(atom) {
            Some("->") if items.len() == 3 => Ok(Annot::Fun(
                Box::new(annot(&items[1])?),
                Box::new(annot(&items[2])?),
                0,
            )),
            Some("->!") if items.len() == 4 => {
                let mut bits = 0;
                match &items[1] {
                    Sexp::Atom(name) => bits |= effect_bit(name)?,
                    Sexp::List(names) => {
                        for name in names {
                            bits |= effect_bit(atom(name).ok_or("bad effect")?)?;
                        }
                    }
                }
                Ok(Annot::Fun(
                    Box::new(annot(&items[2])?),
                    Box::new(annot(&items[3])?),
                    bits,
                ))
            }
            Some("forall") if items.len() == 3 => {
                let Sexp::List(names) = &items[1] else {
                    return Err("bad forall binder".into());
                };
                let names = names
                    .iter()
                    .map(|n| atom(n).map(str::to_owned).ok_or("bad forall name"))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Annot::Forall(names, Box::new(annot(&items[2])?)))
            }
            _ => Err(format!("bad annotation {sexp:?}")),
        },
    }
}

// ---------------------------------------------------------------------------
// Types with bounds
// ---------------------------------------------------------------------------

/// An effect variable: a lower bound that only grows, the effect variables it
/// must flow into, and an optional fixed upper limit from an annotation.
pub struct EffVar {
    lower: Cell<u16>,
    uppers: RefCell<Vec<Eff>>,
    limit: Cell<Option<u16>>,
}
type Eff = Rc<EffVar>;

fn fresh_eff() -> Eff {
    Rc::new(EffVar {
        lower: Cell::new(0),
        uppers: RefCell::new(Vec::new()),
        limit: Cell::new(None),
    })
}

fn fixed_eff(bits: u16) -> Eff {
    let eff = fresh_eff();
    eff.lower.set(bits);
    eff.limit.set(Some(bits));
    eff
}

pub struct VarState {
    id: usize,
    level: usize,
    lower: RefCell<Vec<Ty>>,
    upper: RefCell<Vec<Ty>>,
}

/// Simple types. `Rigid` is a skolem introduced when checking against a
/// `forall` annotation; it is only a subtype of itself. `Poly` is a
/// first-class polymorphic parameter type introduced by an annotation.
#[derive(Clone)]
pub enum Ty {
    Prim(&'static str),
    Rigid(usize),
    Fun(Rc<(Ty, Ty)>, Eff),
    Var(Rc<VarState>),
    Poly(Rc<Annot>),
}

fn level(ty: &Ty) -> usize {
    match ty {
        Ty::Prim(_) | Ty::Rigid(_) | Ty::Poly(_) => 0,
        Ty::Fun(parts, _) => level(&parts.0).max(level(&parts.1)),
        Ty::Var(var) => var.level,
    }
}

/// Why inference stopped.
#[derive(Debug, Clone, PartialEq)]
pub enum Failure {
    Type(String),
    /// The deterministic step budget ran out; never treated as success.
    Budget,
}

struct Infer {
    /// Current recursion depth of the solver; bounded like the step count
    /// so deep types fail with `Budget` instead of overflowing the stack.
    depth: usize,
    /// Types of every lambda parameter and let binding, so that each
    /// binding, not only the program result, is checked against Kush.
    binders: Vec<(String, Ty)>,
    next_id: usize,
    steps: usize,
    budget: usize,
}

type Ctx = HashMap<String, Binding>;

/// Constraint pairs already propagated, keyed by (kind, identity).
type PairCache = HashSet<((u8, usize), (u8, usize))>;

/// Recursion depth limit of the solver.
pub const MAX_DEPTH: usize = 512;

#[derive(Clone)]
enum Binding {
    Mono(Ty),
    /// A let-bound scheme: variables above `level` are generalized.
    Scheme(usize, Ty),
}

impl Infer {
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, Failure>) -> Result<T, Failure> {
        if self.depth >= MAX_DEPTH {
            return Err(Failure::Budget);
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }

    fn tick(&mut self) -> Result<(), Failure> {
        self.steps += 1;
        if self.steps > self.budget {
            Err(Failure::Budget)
        } else {
            Ok(())
        }
    }

    fn fresh(&mut self, level: usize) -> Ty {
        self.next_id += 1;
        Ty::Var(Rc::new(VarState {
            id: self.next_id,
            level,
            lower: RefCell::new(Vec::new()),
            upper: RefCell::new(Vec::new()),
        }))
    }

    fn rigid(&mut self) -> Ty {
        self.next_id += 1;
        Ty::Rigid(self.next_id)
    }

    fn eff_le(&mut self, from: &Eff, to: &Eff) -> Result<(), Failure> {
        self.tick()?;
        if Rc::ptr_eq(from, to) {
            return Ok(());
        }
        from.uppers.borrow_mut().push(to.clone());
        self.raise(to, from.lower.get())
    }

    fn raise(&mut self, eff: &Eff, bits: u16) -> Result<(), Failure> {
        self.nested(|this| this.raise_inner(eff, bits))
    }

    fn raise_inner(&mut self, eff: &Eff, bits: u16) -> Result<(), Failure> {
        self.tick()?;
        if bits & !eff.lower.get() == 0 {
            return Ok(());
        }
        let lower = eff.lower.get() | bits;
        eff.lower.set(lower);
        if let Some(limit) = eff.limit.get()
            && lower & !limit != 0
        {
            return Err(Failure::Type(format!(
                "effects {} exceed the annotated row {}",
                effects(lower),
                effects(limit)
            )));
        }
        let uppers = eff.uppers.borrow().clone();
        for upper in uppers {
            self.raise(&upper, lower)?;
        }
        Ok(())
    }

    /// `lhs <: rhs`, propagating bounds (Simple-sub's `constrain`).
    fn constrain(&mut self, lhs: &Ty, rhs: &Ty, cache: &mut PairCache) -> Result<(), Failure> {
        self.nested(|this| this.constrain_inner(lhs, rhs, cache))
    }

    fn constrain_inner(
        &mut self,
        lhs: &Ty,
        rhs: &Ty,
        cache: &mut PairCache,
    ) -> Result<(), Failure> {
        self.tick()?;
        // Cache every pair involving a variable (by variable id or arrow
        // identity) so cyclic bounds terminate, as in Simple-sub.
        let ident = |ty: &Ty| match ty {
            Ty::Var(v) => Some((0u8, v.id)),
            Ty::Fun(parts, _) => Some((1, Rc::as_ptr(parts) as usize)),
            Ty::Prim(_) | Ty::Rigid(_) | Ty::Poly(_) => None,
        };
        if (matches!(lhs, Ty::Var(_)) || matches!(rhs, Ty::Var(_)))
            && let (Some(a), Some(b)) = (ident(lhs), ident(rhs))
            && !cache.insert((a, b))
        {
            return Ok(());
        }
        match (lhs, rhs) {
            (Ty::Prim(a), Ty::Prim(b)) if a == b => Ok(()),
            (Ty::Rigid(a), Ty::Rigid(b)) if a == b => Ok(()),
            (Ty::Fun(l, le), Ty::Fun(r, re)) => {
                self.constrain(&r.0, &l.0, cache)?;
                self.constrain(&l.1, &r.1, cache)?;
                self.eff_le(le, re)
            }
            (Ty::Poly(annot), _) => {
                // Using a polymorphic parameter: instantiate it.
                let instance = self.annot_type(annot, &mut HashMap::new(), true, usize::MAX)?;
                self.constrain(&instance, rhs, cache)
            }
            (_, Ty::Poly(annot)) => {
                // Passing a value where a polymorphic type is required:
                // check it against fresh rigid variables.
                let skolem = self.annot_type(annot, &mut HashMap::new(), false, usize::MAX)?;
                self.constrain(lhs, &skolem, cache)
            }
            (Ty::Var(v), _) if level(rhs) <= v.level => {
                v.upper.borrow_mut().push(rhs.clone());
                let lowers = v.lower.borrow().clone();
                for lower in lowers {
                    self.constrain(&lower, rhs, cache)?;
                }
                Ok(())
            }
            (_, Ty::Var(v)) if level(lhs) <= v.level => {
                v.lower.borrow_mut().push(lhs.clone());
                let uppers = v.upper.borrow().clone();
                for upper in uppers {
                    self.constrain(lhs, &upper, cache)?;
                }
                Ok(())
            }
            (Ty::Var(v), _) => {
                let rhs = self.extrude(rhs, false, v.level, &mut HashMap::new())?;
                self.constrain(lhs, &rhs, cache)
            }
            (_, Ty::Var(v)) => {
                let lhs = self.extrude(lhs, true, v.level, &mut HashMap::new())?;
                self.constrain(&lhs, rhs, cache)
            }
            _ => Err(Failure::Type(format!(
                "cannot use {} as {}",
                show(lhs),
                show(rhs)
            ))),
        }
    }

    /// Copy the parts of `ty` above `lvl` down to `lvl` (Simple-sub's
    /// `extrude`), keeping the bounds connected in the given polarity.
    fn extrude(
        &mut self,
        ty: &Ty,
        positive: bool,
        lvl: usize,
        cache: &mut HashMap<usize, Ty>,
    ) -> Result<Ty, Failure> {
        self.nested(|this| this.extrude_inner(ty, positive, lvl, cache))
    }

    fn extrude_inner(
        &mut self,
        ty: &Ty,
        positive: bool,
        lvl: usize,
        cache: &mut HashMap<usize, Ty>,
    ) -> Result<Ty, Failure> {
        self.tick()?;
        if level(ty) <= lvl {
            return Ok(ty.clone());
        }
        match ty {
            Ty::Fun(parts, eff) => Ok(Ty::Fun(
                Rc::new((
                    self.extrude(&parts.0, !positive, lvl, cache)?,
                    self.extrude(&parts.1, positive, lvl, cache)?,
                )),
                eff.clone(),
            )),
            Ty::Var(v) => {
                if let Some(copy) = cache.get(&v.id) {
                    return Ok(copy.clone());
                }
                let copy = self.fresh(lvl);
                cache.insert(v.id, copy.clone());
                let Ty::Var(c) = &copy else { unreachable!() };
                if positive {
                    v.upper.borrow_mut().push(copy.clone());
                    let lowers = v.lower.borrow().clone();
                    for lower in lowers {
                        let lower = self.extrude(&lower, positive, lvl, cache)?;
                        c.lower.borrow_mut().push(lower);
                    }
                } else {
                    v.lower.borrow_mut().push(copy.clone());
                    let uppers = v.upper.borrow().clone();
                    for upper in uppers {
                        let upper = self.extrude(&upper, positive, lvl, cache)?;
                        c.upper.borrow_mut().push(upper);
                    }
                }
                Ok(copy)
            }
            _ => Ok(ty.clone()),
        }
    }

    /// Instantiate a scheme: copy every variable above `limit`.
    fn freshen(
        &mut self,
        ty: &Ty,
        limit: usize,
        lvl: usize,
        cache: &mut HashMap<usize, Ty>,
    ) -> Result<Ty, Failure> {
        self.nested(|this| this.freshen_inner(ty, limit, lvl, cache))
    }

    fn freshen_inner(
        &mut self,
        ty: &Ty,
        limit: usize,
        lvl: usize,
        cache: &mut HashMap<usize, Ty>,
    ) -> Result<Ty, Failure> {
        self.tick()?;
        if level(ty) <= limit {
            return Ok(ty.clone());
        }
        match ty {
            Ty::Fun(parts, eff) => Ok(Ty::Fun(
                Rc::new((
                    self.freshen(&parts.0, limit, lvl, cache)?,
                    self.freshen(&parts.1, limit, lvl, cache)?,
                )),
                // Effects are not generalized: every instance shares the
                // row (see docs/inference-prototype.md, limits).
                eff.clone(),
            )),
            Ty::Var(v) => {
                if let Some(copy) = cache.get(&v.id) {
                    return Ok(copy.clone());
                }
                let copy = self.fresh(lvl);
                cache.insert(v.id, copy.clone());
                let Ty::Var(c) = &copy else { unreachable!() };
                let lowers = v.lower.borrow().clone();
                for lower in lowers {
                    let lower = self.freshen(&lower, limit, lvl, cache)?;
                    c.lower.borrow_mut().push(lower);
                }
                let uppers = v.upper.borrow().clone();
                for upper in uppers {
                    let upper = self.freshen(&upper, limit, lvl, cache)?;
                    c.upper.borrow_mut().push(upper);
                }
                Ok(copy)
            }
            _ => Ok(ty.clone()),
        }
    }

    /// Lower an annotation. `flexible` instantiates `forall` variables with
    /// fresh inference variables; otherwise they become rigid skolems.
    fn annot_type(
        &mut self,
        annot: &Annot,
        names: &mut HashMap<String, Ty>,
        flexible: bool,
        lvl: usize,
    ) -> Result<Ty, Failure> {
        self.nested(|this| this.annot_type_inner(annot, names, flexible, lvl))
    }

    fn annot_type_inner(
        &mut self,
        annot: &Annot,
        names: &mut HashMap<String, Ty>,
        flexible: bool,
        lvl: usize,
    ) -> Result<Ty, Failure> {
        self.tick()?;
        Ok(match annot {
            Annot::Int => Ty::Prim("int"),
            Annot::Bool => Ty::Prim("bool"),
            Annot::Name(name) => names
                .get(name)
                .cloned()
                .ok_or_else(|| Failure::Type(format!("unbound type variable '{name}'")))?,
            Annot::Fun(a, b, bits) => Ty::Fun(
                Rc::new((
                    self.annot_type(a, names, flexible, lvl)?,
                    self.annot_type(b, names, flexible, lvl)?,
                )),
                fixed_eff(*bits),
            ),
            Annot::Forall(vars, body) => {
                let mut inner = names.clone();
                for var in vars {
                    let ty = if flexible {
                        self.fresh(if lvl == usize::MAX { 0 } else { lvl })
                    } else {
                        self.rigid()
                    };
                    inner.insert(var.clone(), ty);
                }
                self.annot_type(body, &mut inner, flexible, lvl)?
            }
        })
    }

    fn infer(&mut self, term: &Term, ctx: &Ctx, lvl: usize, eff: &Eff) -> Result<Ty, Failure> {
        self.nested(|this| this.infer_inner(term, ctx, lvl, eff))
    }

    fn infer_inner(
        &mut self,
        term: &Term,
        ctx: &Ctx,
        lvl: usize,
        eff: &Eff,
    ) -> Result<Ty, Failure> {
        self.tick()?;
        match term {
            Term::Int => Ok(Ty::Prim("int")),
            Term::Bool => Ok(Ty::Prim("bool")),
            Term::Var(name) => match ctx.get(name) {
                Some(Binding::Mono(ty)) => Ok(ty.clone()),
                Some(Binding::Scheme(limit, ty)) => {
                    let (limit, ty) = (*limit, ty.clone());
                    self.freshen(&ty, limit, lvl, &mut HashMap::new())
                }
                None => Err(Failure::Type(format!("unbound variable '{name}'"))),
            },
            Term::Lam(name, annot, body) => {
                let parameter = match annot {
                    None => self.fresh(lvl),
                    Some(annot @ Annot::Forall(..)) => Ty::Poly(Rc::new(annot.clone())),
                    Some(annot) => self.annot_type(annot, &mut HashMap::new(), true, lvl)?,
                };
                self.binders.push((name.clone(), parameter.clone()));
                let mut inner = ctx.clone();
                inner.insert(name.clone(), Binding::Mono(parameter.clone()));
                let body_eff = fresh_eff();
                let result = self.infer(body, &inner, lvl, &body_eff)?;
                Ok(Ty::Fun(Rc::new((parameter, result)), body_eff))
            }
            Term::App(function, argument) => {
                let function = self.infer(function, ctx, lvl, eff)?;
                let argument = self.infer(argument, ctx, lvl, eff)?;
                let result = self.fresh(lvl);
                let call_eff = fresh_eff();
                let expected = Ty::Fun(Rc::new((argument, result.clone())), call_eff.clone());
                self.constrain(&function, &expected, &mut HashSet::new())?;
                self.eff_le(&call_eff, eff)?;
                Ok(result)
            }
            Term::Let(name, value, body) => {
                let value = self.infer(value, ctx, lvl + 1, eff)?;
                self.binders.push((name.clone(), value.clone()));
                let mut inner = ctx.clone();
                inner.insert(name.clone(), Binding::Scheme(lvl, value));
                self.infer(body, &inner, lvl, eff)
            }
            Term::If(condition, yes, no) => {
                let condition = self.infer(condition, ctx, lvl, eff)?;
                self.constrain(&condition, &Ty::Prim("bool"), &mut HashSet::new())?;
                let result = self.fresh(lvl);
                let yes = self.infer(yes, ctx, lvl, eff)?;
                self.constrain(&yes, &result, &mut HashSet::new())?;
                let no = self.infer(no, ctx, lvl, eff)?;
                self.constrain(&no, &result, &mut HashSet::new())?;
                Ok(result)
            }
            Term::Ann(value, annot) => {
                let ty = self.infer(value, ctx, lvl, eff)?;
                let rigid = self.annot_type(annot, &mut HashMap::new(), false, lvl)?;
                self.constrain(&ty, &rigid, &mut HashSet::new())?;
                self.annot_type(annot, &mut HashMap::new(), true, lvl)
            }
        }
    }
}

fn effects(bits: u16) -> String {
    let names = [(IO, "io"), (ALLOC, "alloc"), (PANIC, "panic")]
        .into_iter()
        .filter(|(bit, _)| bits & bit != 0)
        .map(|(_, name)| name)
        .collect::<Vec<_>>();
    format!("{{{}}}", names.join(", "))
}

fn show(ty: &Ty) -> String {
    match ty {
        Ty::Prim(name) => (*name).to_owned(),
        Ty::Rigid(id) => format!("'r{id}"),
        Ty::Fun(parts, _) => format!("({} -> {})", show(&parts.0), show(&parts.1)),
        Ty::Var(v) => format!("'v{}", v.id),
        Ty::Poly(_) => "<forall>".into(),
    }
}

// ---------------------------------------------------------------------------
// Coalescing and the Kush representability check
// ---------------------------------------------------------------------------

/// A coalesced type: bounds of each variable are folded into unions
/// (positive positions) and intersections (negative positions).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Out {
    Int,
    Bool,
    /// A variable with no bounds in that polarity: a type parameter.
    Param(usize),
    Rigid(usize),
    Fun(Box<Out>, Box<Out>, u16),
    Union(BTreeSet<Out>),
    Inter(BTreeSet<Out>),
    /// A recursive occurrence: Kush has no equirecursive types.
    Recursive(usize),
    Poly,
}

impl fmt::Display for Out {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Out::Int => write!(f, "int"),
            Out::Bool => write!(f, "bool"),
            Out::Param(id) => write!(f, "'a{id}"),
            Out::Rigid(id) => write!(f, "'r{id}"),
            Out::Fun(a, b, 0) => write!(f, "({a} -> {b})"),
            Out::Fun(a, b, bits) => write!(f, "({a} ->{} {b})", effects(*bits)),
            Out::Union(items) => {
                let items = items.iter().map(ToString::to_string).collect::<Vec<_>>();
                write!(f, "({})", items.join(" | "))
            }
            Out::Inter(items) => {
                let items = items.iter().map(ToString::to_string).collect::<Vec<_>>();
                write!(f, "({})", items.join(" & "))
            }
            Out::Recursive(id) => write!(f, "rec'a{id}"),
            Out::Poly => write!(f, "<forall>"),
        }
    }
}

fn coalesce(
    infer: &mut Infer,
    ty: &Ty,
    positive: bool,
    in_progress: &mut Vec<(usize, bool)>,
) -> Result<Out, Failure> {
    infer.nested(|infer| coalesce_inner(infer, ty, positive, in_progress))
}

fn coalesce_inner(
    infer: &mut Infer,
    ty: &Ty,
    positive: bool,
    in_progress: &mut Vec<(usize, bool)>,
) -> Result<Out, Failure> {
    infer.tick()?;
    Ok(match ty {
        Ty::Prim("int") => Out::Int,
        Ty::Prim(_) => Out::Bool,
        Ty::Rigid(id) => Out::Rigid(*id),
        Ty::Poly(_) => Out::Poly,
        Ty::Fun(parts, eff) => Out::Fun(
            Box::new(coalesce(infer, &parts.0, !positive, in_progress)?),
            Box::new(coalesce(infer, &parts.1, positive, in_progress)?),
            eff.lower.get(),
        ),
        Ty::Var(v) => {
            // A variable reached again inside its own bounds, in either
            // polarity, is a cyclic constraint: an equirecursive type.
            if in_progress.iter().any(|(id, _)| *id == v.id) {
                return Ok(Out::Recursive(v.id));
            }
            in_progress.push((v.id, positive));
            let bounds = if positive {
                v.lower.borrow().clone()
            } else {
                v.upper.borrow().clone()
            };
            let mut items = BTreeSet::new();
            for bound in &bounds {
                match coalesce(infer, bound, positive, in_progress)? {
                    Out::Union(inner) if positive => items.extend(inner),
                    Out::Inter(inner) if !positive => items.extend(inner),
                    other => {
                        items.insert(other);
                    }
                }
            }
            in_progress.pop();
            let items = merge_arrows(items, positive);
            match items.len() {
                0 => Out::Param(v.id),
                1 => items.into_iter().next().expect("one item"),
                _ if positive => Out::Union(items),
                _ => Out::Inter(items),
            }
        }
    })
}

/// Several arrow bounds of one variable describe one arrow:
/// `(A1 -> B1) | (A2 -> B2)` is `(A1 & A2) -> (B1 | B2)` and
/// `(A1 -> B1) & (A2 -> B2)` is `(A1 | A2) -> (B1 & B2)`.
fn merge_arrows(items: BTreeSet<Out>, positive: bool) -> BTreeSet<Out> {
    let (arrows, mut rest): (Vec<Out>, BTreeSet<Out>) = (
        items
            .iter()
            .filter(|item| matches!(item, Out::Fun(..)))
            .cloned()
            .collect(),
        items
            .iter()
            .filter(|item| !matches!(item, Out::Fun(..)))
            .cloned()
            .collect(),
    );
    if arrows.len() < 2 {
        return items;
    }
    let mut parameters = BTreeSet::new();
    let mut results = BTreeSet::new();
    let mut bits = 0;
    for arrow in arrows {
        let Out::Fun(parameter, result, effect) = arrow else {
            unreachable!()
        };
        parameters.insert(*parameter);
        results.insert(*result);
        bits |= effect;
    }
    let combine = |set: BTreeSet<Out>, union: bool| {
        if set.len() == 1 {
            set.into_iter().next().expect("one item")
        } else if union {
            Out::Union(set)
        } else {
            Out::Inter(set)
        }
    };
    rest.insert(Out::Fun(
        Box::new(combine(parameters, !positive)),
        Box::new(combine(results, positive)),
        bits,
    ));
    rest
}

/// How a coalesced type maps onto Kush.
#[derive(Debug, Clone, PartialEq)]
pub enum Fit {
    /// Expressible as a Kush type (generic parameters, arrows, scalars).
    Direct,
    /// Expressible only with a union of distinct representations, which
    /// Kush supports through a representation-changing coercion at each
    /// injection site.
    NeedsUnionCoercion,
    /// Not expressible: recursive types, uncallable intersections of
    /// distinct scalars, functions in intersections.
    Unrepresentable(String),
}

pub fn fit(out: &Out) -> Fit {
    fn walk(out: &Out, union: &mut bool) -> Result<(), String> {
        match out {
            Out::Int | Out::Bool | Out::Param(_) | Out::Rigid(_) | Out::Poly => Ok(()),
            Out::Recursive(_) => Err("recursive type".into()),
            Out::Fun(a, b, _) => {
                walk(a, union)?;
                walk(b, union)
            }
            Out::Union(items) => {
                let scalars = items
                    .iter()
                    .filter(|i| matches!(i, Out::Int | Out::Bool))
                    .count();
                if scalars > 1 || (scalars == 1 && items.len() > 1) {
                    *union = true;
                }
                items.iter().try_for_each(|item| walk(item, union))
            }
            Out::Inter(items) => {
                let concrete = items
                    .iter()
                    .filter(|i| !matches!(i, Out::Param(_)))
                    .collect::<Vec<_>>();
                if concrete.len() > 1 {
                    return Err(format!(
                        "intersection {} has no Kush value",
                        Out::Inter(items.clone())
                    ));
                }
                items.iter().try_for_each(|item| walk(item, union))
            }
        }
    }
    let mut union = false;
    match walk(out, &mut union) {
        Err(reason) => Fit::Unrepresentable(reason),
        Ok(()) if union => Fit::NeedsUnionCoercion,
        Ok(()) => Fit::Direct,
    }
}

/// Result of checking one program.
#[derive(Debug, Clone)]
pub struct Report {
    pub outcome: Result<(Out, Fit, u16), Failure>,
    pub steps: usize,
}

fn primitives() -> Vec<(&'static str, &'static str)> {
    vec![
        ("add", "(-> int (-> int int))"),
        ("eq", "(-> int (-> int bool))"),
        ("not", "(-> bool bool)"),
        ("print", "(->! io int int)"),
        ("alloc_one", "(->! alloc int int)"),
    ]
}

/// Infer the type of a whole program with a step budget.
pub fn check(source: &str, budget: usize) -> Report {
    let mut infer = Infer {
        binders: Vec::new(),
        depth: 0,
        next_id: 0,
        steps: 0,
        budget,
    };
    let outcome = (|| {
        let sexp = parse(source).map_err(Failure::Type)?;
        let term = term(&sexp).map_err(Failure::Type)?;
        let mut ctx = Ctx::new();
        for (name, ty) in primitives() {
            let annot = annot(&parse(ty).map_err(Failure::Type)?).map_err(Failure::Type)?;
            let ty = infer.annot_type(&annot, &mut HashMap::new(), true, 0)?;
            ctx.insert(name.to_owned(), Binding::Mono(ty));
        }
        let eff = fresh_eff();
        let ty = infer.infer(&term, &ctx, 0, &eff)?;
        let out = coalesce(&mut infer, &ty, true, &mut Vec::new())?;
        let mut fit = fit(&out);
        // A binding type is read in the polarity of its uses (negative for
        // a parameter, positive for a let value); both must be expressible.
        let binders = std::mem::take(&mut infer.binders);
        for (name, ty) in &binders {
            if let Fit::Unrepresentable(_) = fit {
                break;
            }
            for positive in [true, false] {
                let out = coalesce(&mut infer, ty, positive, &mut Vec::new())?;
                if let Fit::Unrepresentable(reason) = self::fit(&out) {
                    fit = Fit::Unrepresentable(format!("binding '{name}': {reason}"));
                    break;
                }
            }
            if fit == Fit::Direct
                && matches!(
                    self::fit(&coalesce(&mut infer, ty, true, &mut Vec::new())?),
                    Fit::NeedsUnionCoercion
                )
            {
                fit = Fit::NeedsUnionCoercion;
            }
        }
        Ok((out, fit, eff.lower.get()))
    })();
    Report {
        outcome,
        steps: infer.steps,
    }
}
