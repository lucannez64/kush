//! KIK-DIFF: differential testing of the Kush kernel (`examples/kernel`)
//! against the Rust kernel, beyond the example corpus:
//!
//! - mutants: small edits of every definition of the corpus, each appended as
//!   a new definition, so most of them exercise rejection paths;
//! - generated terms: a seeded generator of well-typed closed terms (beta
//!   redexes, natural induction, equality, transport, J, higher-order
//!   functions), each checked, inferred and normalized, plus their mutants.
//!
//! Both kernels answer the same exchange files (docs/kernel-exchange.md) and
//! must give the same answer for every item, except that a budget
//! exhaustion on either side is inconclusive (they charge different steps).
//! `KUSH_KIK_SEEDS` sets the number of generated files (default 40);
//! `scripts/kernel-diff.sh` runs a larger sweep.
use kush::exchange::{self, Item};
use kush::kernel::Term as T;
use std::{path::PathBuf, process::Command};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn scratch(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush-kik-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

fn build(dir: &std::path::Path) -> PathBuf {
    let binary = dir.join("kernel");
    let build = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    binary
}

/// Outcome counts of one comparison.
#[derive(Default, Debug)]
struct Tally {
    accepted: usize,
    rejected: usize,
    inconclusive: usize,
}

/// Answer `text` with both kernels and require the same answer per item.
fn compare(binary: &std::path::Path, file: &std::path::Path, text: &str, tally: &mut Tally) {
    std::fs::write(file, text).unwrap();
    let rust = exchange::answer(text).unwrap();
    let output = Command::new(binary)
        .arg("check")
        .arg(file)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", file.display());
    let kush_answer = String::from_utf8(output.stdout).unwrap();
    let items: Vec<&str> = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    let rust_lines: Vec<&str> = rust.lines().collect();
    let kush_lines: Vec<&str> = kush_answer.lines().collect();
    assert_eq!(rust_lines.len(), kush_lines.len(), "{}", file.display());
    for (index, (rust_line, kush_line)) in rust_lines.iter().zip(&kush_lines).enumerate() {
        if rust_line.starts_with("budget") || kush_line.starts_with("budget") {
            tally.inconclusive += 1;
            continue;
        }
        assert_eq!(
            rust_line,
            kush_line,
            "item {} of {}:\n{}",
            index + 1,
            file.display(),
            items.get(index).unwrap_or(&"?")
        );
        if rust_line.starts_with("reject") {
            tally.rejected += 1;
        } else {
            tally.accepted += 1;
        }
    }
}

// ------------------------------------------------------------- mutation

fn rebuild(t: &T, f: &mut impl FnMut(&T) -> T) -> T {
    let b = |x: &T, f: &mut dyn FnMut(&T) -> T| Box::new(f(x));
    match t {
        T::Pi { domain, codomain } => T::Pi {
            domain: b(domain, f),
            codomain: b(codomain, f),
        },
        T::Lam { domain, body } => T::Lam {
            domain: b(domain, f),
            body: b(body, f),
        },
        T::App(x, y) => T::App(b(x, f), b(y, f)),
        T::Succ(x) => T::Succ(b(x, f)),
        T::NatElim {
            motive,
            zero,
            step,
            value,
        } => T::NatElim {
            motive: b(motive, f),
            zero: b(zero, f),
            step: b(step, f),
            value: b(value, f),
        },
        T::Eq { ty, left, right } => T::Eq {
            ty: b(ty, f),
            left: b(left, f),
            right: b(right, f),
        },
        T::Refl { ty, value } => T::Refl {
            ty: b(ty, f),
            value: b(value, f),
        },
        T::Transport {
            ty,
            from,
            to,
            motive,
            proof,
            value,
        } => T::Transport {
            ty: b(ty, f),
            from: b(from, f),
            to: b(to, f),
            motive: b(motive, f),
            proof: b(proof, f),
            value: b(value, f),
        },
        T::EqElim {
            ty,
            left,
            right,
            motive,
            refl,
            proof,
        } => T::EqElim {
            ty: b(ty, f),
            left: b(left, f),
            right: b(right, f),
            motive: b(motive, f),
            refl: b(refl, f),
            proof: b(proof, f),
        },
        T::IndElim {
            data,
            motive,
            branches,
            scrutinee,
        } => T::IndElim {
            data: data.clone(),
            motive: b(motive, f),
            branches: branches.iter().map(|x| f(x)).collect(),
            scrutinee: b(scrutinee, f),
        },
        other => other.clone(),
    }
}

/// The local edits of one node.
fn edits(t: &T) -> Vec<T> {
    let mut out = Vec::new();
    match t {
        T::Var(i) => {
            out.push(T::Var(i + 1));
            if *i > 0 {
                out.push(T::Var(i - 1));
            }
        }
        T::Universe(level) => {
            out.push(T::Universe(level.succ().unwrap()));
            out.push(T::Prop);
        }
        T::Prop => out.push(T::universe(0)),
        T::Nat => out.push(T::universe(0)),
        T::Zero => out.push(T::succ(T::Zero)),
        T::Literal(value) => out.push(T::natural(value.successor())),
        T::Succ(x) => out.push((**x).clone()),
        T::App(f, a) => {
            out.push((**f).clone());
            out.push(T::App(a.clone(), f.clone()));
        }
        T::Lam { domain, body } => {
            out.push(T::pi((**domain).clone(), (**body).clone()));
            out.push(T::lam(T::Nat, (**body).clone()));
        }
        T::Pi { domain, codomain } => out.push(T::lam((**domain).clone(), (**codomain).clone())),
        T::Global(name, levels) if !levels.is_empty() => {
            let mut bumped = levels.clone();
            bumped[0] = bumped[0].succ().unwrap();
            out.push(T::Global(name.clone(), bumped));
            out.push(T::Global(name.clone(), Vec::new()));
        }
        T::Refl { ty, value } => out.push(T::refl((**ty).clone(), T::succ((**value).clone()))),
        T::IndElim {
            data,
            motive,
            branches,
            scrutinee,
        } if branches.len() >= 2 => {
            let mut swapped = branches.clone();
            swapped.swap(0, 1);
            out.push(T::IndElim {
                data: data.clone(),
                motive: motive.clone(),
                branches: swapped,
                scrutinee: scrutinee.clone(),
            });
        }
        _ => {}
    }
    out
}

/// Every term obtained by one edit at one position.
fn mutants(t: &T) -> Vec<T> {
    let mut out = edits(t);
    // Children: rebuild once per (child, edit), replacing that child only.
    let mut children = Vec::new();
    rebuild(t, &mut |child| {
        children.push(child.clone());
        child.clone()
    });
    for child_index in 0..children.len() {
        for edited in mutants(&children[child_index]) {
            let mut seen = 0usize;
            out.push(rebuild(t, &mut |child| {
                let result = if seen == child_index {
                    edited.clone()
                } else {
                    child.clone()
                };
                seen += 1;
                result
            }));
        }
    }
    out
}

/// A small deterministic generator (xorshift64*).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Pick up to `count` items, deterministically.
fn sample<X: Clone>(items: &[X], count: usize, rng: &mut Rng) -> Vec<X> {
    if items.len() <= count {
        return items.to_vec();
    }
    (0..count)
        .map(|_| items[rng.below(items.len())].clone())
        .collect()
}

fn dump(name: &str) -> String {
    let source = std::fs::read_to_string(root().join(format!("examples/{name}.kush"))).unwrap();
    let checked = kush::check(&source)
        .or_else(|_| kush::executable::logical_module(&source))
        .unwrap();
    exchange::dump(&checked)
}

/// The corpus file followed by up to `per_def` mutants of each definition's
/// type and value, as fresh definitions.
fn mutated(name: &str, per_def: usize, rng: &mut Rng) -> String {
    let text = dump(name);
    let mut out = text.clone();
    let mut counter = 0;
    for item in exchange::parse(&text).unwrap() {
        let Item::Def {
            levels, ty, value, ..
        } = item
        else {
            continue;
        };
        let mut candidates: Vec<(T, T)> = mutants(&value)
            .into_iter()
            .map(|v| (ty.clone(), v))
            .collect();
        candidates.extend(mutants(&ty).into_iter().map(|t| (t, value.clone())));
        for (ty, value) in sample(&candidates, per_def, rng) {
            counter += 1;
            out +=
                &exchange::def_sexp(&format!("mutant{counter}"), levels, &ty, &value).to_string();
            out.push('\n');
        }
    }
    out
}

// ------------------------------------------------------------ generation

/// Simple (non-dependent) types of generated terms.
#[derive(Clone, PartialEq)]
enum Ty {
    Nat,
    Arrow(Box<Ty>, Box<Ty>),
}
impl Ty {
    fn term(&self) -> T {
        match self {
            Ty::Nat => T::Nat,
            Ty::Arrow(a, b) => T::pi(a.term(), shift(&b.term(), 1)),
        }
    }
}

/// Shift the free indices of a term by `amount` (generated types are closed,
/// so this only matters for terms built under binders).
fn shift(t: &T, amount: usize) -> T {
    fn go(t: &T, amount: usize, depth: usize) -> T {
        match t {
            T::Var(i) if *i >= depth => T::Var(i + amount),
            T::Pi { domain, codomain } => {
                T::pi(go(domain, amount, depth), go(codomain, amount, depth + 1))
            }
            T::Lam { domain, body } => {
                T::lam(go(domain, amount, depth), go(body, amount, depth + 1))
            }
            _ => rebuild(t, &mut |child| go(child, amount, depth)),
        }
    }
    go(t, amount, 0)
}

fn nat_to_nat() -> Ty {
    Ty::Arrow(Box::new(Ty::Nat), Box::new(Ty::Nat))
}

/// A closed-typed term of type `ty` in a context of simple types (innermost
/// last). `fuel` bounds the size.
fn generate(ctx: &mut Vec<Ty>, ty: &Ty, fuel: usize, rng: &mut Rng) -> T {
    // A variable of the right type, when there is one.
    let candidates: Vec<usize> = (0..ctx.len())
        .filter(|i| ctx[ctx.len() - 1 - i] == *ty)
        .collect();
    if fuel == 0 || (!candidates.is_empty() && rng.below(4) == 0) {
        if let Some(&index) = candidates.get(
            rng.below(candidates.len().max(1))
                .min(candidates.len().saturating_sub(1)),
        ) {
            return T::Var(index);
        }
        if *ty == Ty::Nat {
            return T::natural((rng.below(5) as u64).into());
        }
    }
    let fuel = fuel.saturating_sub(1);
    match ty {
        Ty::Arrow(a, b) => {
            ctx.push((**a).clone());
            let body = generate(ctx, b, fuel, rng);
            ctx.pop();
            T::lam(a.term(), body)
        }
        Ty::Nat => match rng.below(7) {
            0 => T::natural((rng.below(1_000_000_005) as u64).into()),
            1 => T::succ(generate(ctx, ty, fuel, rng)),
            2 => {
                // A beta redex.
                let argument_type = if rng.below(2) == 0 {
                    Ty::Nat
                } else {
                    nat_to_nat()
                };
                let function = generate(
                    ctx,
                    &Ty::Arrow(Box::new(argument_type.clone()), Box::new(Ty::Nat)),
                    fuel,
                    rng,
                );
                T::app(function, generate(ctx, &argument_type, fuel, rng))
            }
            3 => {
                // Natural induction with a constant motive, on a small value.
                let step = generate(
                    ctx,
                    &Ty::Arrow(Box::new(Ty::Nat), Box::new(nat_to_nat())),
                    fuel,
                    rng,
                );
                T::NatElim {
                    motive: Box::new(T::lam(T::Nat, T::Nat)),
                    zero: Box::new(generate(ctx, ty, fuel, rng)),
                    step: Box::new(step),
                    value: Box::new(T::natural((rng.below(6) as u64).into())),
                }
            }
            4 => {
                // Transport along refl, with a constant motive.
                let x = generate(ctx, ty, fuel / 2, rng);
                T::Transport {
                    ty: Box::new(T::Nat),
                    from: Box::new(x.clone()),
                    to: Box::new(x.clone()),
                    motive: Box::new(T::lam(T::Nat, T::Nat)),
                    proof: Box::new(T::refl(T::Nat, x)),
                    value: Box::new(generate(ctx, ty, fuel, rng)),
                }
            }
            5 => {
                // J along refl with the dependent motive y p. Nat.
                let x = generate(ctx, ty, fuel / 2, rng);
                T::EqElim {
                    ty: Box::new(T::Nat),
                    left: Box::new(x.clone()),
                    right: Box::new(x.clone()),
                    motive: Box::new(T::lam(
                        T::Nat,
                        T::lam(T::eq(T::Nat, shift(&x, 1), T::Var(0)), T::Nat),
                    )),
                    refl: Box::new(generate(ctx, ty, fuel, rng)),
                    proof: Box::new(T::refl(T::Nat, x)),
                }
            }
            _ => {
                // Apply a higher-order function.
                let function = generate(
                    ctx,
                    &Ty::Arrow(Box::new(nat_to_nat()), Box::new(Ty::Nat)),
                    fuel,
                    rng,
                );
                T::app(function, generate(ctx, &nat_to_nat(), fuel, rng))
            }
        },
    }
}

/// One generated exchange file: terms with their check, infer and normalize
/// queries, `refl t : t = t`, and mutants. Also returns the line numbers of
/// the checks of the generated terms themselves, which must be accepted.
fn generated(seed: u64) -> (String, Vec<usize>) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut out = String::new();
    let mut originals = Vec::new();
    for _ in 0..6 {
        let ty = match rng.below(3) {
            0 => Ty::Nat,
            1 => nat_to_nat(),
            _ => Ty::Arrow(Box::new(nat_to_nat()), Box::new(Ty::Nat)),
        };
        let fuel = 2 + rng.below(5);
        let t = generate(&mut Vec::new(), &ty, fuel, &mut rng);
        let ty_term = ty.term();
        let check = |t: &T, ty: &T| {
            format!(
                "(check {} {})\n",
                exchange::term_sexp(t),
                exchange::term_sexp(ty)
            )
        };
        originals.push(out.lines().count());
        out += &check(&t, &ty_term);
        out += &format!("(infer {})\n", exchange::term_sexp(&t));
        out += &format!("(normalize {})\n", exchange::term_sexp(&t));
        if ty == Ty::Nat {
            // refl n : n = n, stated against the term itself.
            out += &check(
                &T::refl(T::Nat, t.clone()),
                &T::eq(T::Nat, t.clone(), t.clone()),
            );
        }
        for mutant in sample(&mutants(&t), 6, &mut rng) {
            out += &check(&mutant, &ty_term);
            out += &format!("(normalize {})\n", exchange::term_sexp(&mutant));
        }
    }
    (out, originals)
}

#[test]
fn corpus_mutants_agree() {
    let dir = scratch("mutants");
    let binary = build(&dir);
    let mut rng = Rng(0x5EED);
    let mut tally = Tally::default();
    for name in [
        "proofs",
        "induction",
        "large-naturals",
        "logical-data",
        "finite-proofs",
        "universes",
    ] {
        let text = mutated(name, 12, &mut rng);
        compare(
            &binary,
            &dir.join(format!("{name}.kcore")),
            &text,
            &mut tally,
        );
    }
    eprintln!("corpus mutants: {tally:?}");
    assert!(tally.rejected >= 300, "{tally:?}");
    assert!(
        tally.inconclusive * 20 <= tally.accepted + tally.rejected,
        "{tally:?}"
    );
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn generated_terms_agree() {
    let seeds: u64 = std::env::var("KUSH_KIK_SEEDS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(40);
    let dir = scratch("generated");
    let binary = build(&dir);
    let mut tally = Tally::default();
    for seed in 0..seeds {
        let (text, _) = generated(seed);
        compare(
            &binary,
            &dir.join(format!("seed{seed}.kcore")),
            &text,
            &mut tally,
        );
    }
    eprintln!("generated terms ({seeds} seeds): {tally:?}");
    assert!(tally.accepted >= 10 * seeds as usize, "{tally:?}");
    assert!(tally.rejected >= 5 * seeds as usize, "{tally:?}");
    assert!(
        tally.inconclusive * 20 <= tally.accepted + tally.rejected,
        "{tally:?}"
    );
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn the_generator_produces_well_typed_terms() {
    // The checks of the generated terms themselves (not their mutants) are
    // accepted by the Rust kernel, so the generator really covers acceptance.
    for seed in 0..40 {
        let (text, originals) = generated(seed);
        let answers: Vec<String> = exchange::answer(&text)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect();
        for line in originals {
            assert!(
                answers[line] == "ok" || answers[line] == "budget",
                "seed {seed}: {}",
                text.lines().nth(line).unwrap()
            );
        }
    }
}
