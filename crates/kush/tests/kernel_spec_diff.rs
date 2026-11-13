//! KIK-SPEC-DIFF: the Kush kernel's substitution against the kernel-checked
//! specification (`examples/kernel/spec/scoped.kush`).
//!
//! For generated raw terms `b` (scope `n + 1`) and `u` (scope `n`):
//!
//! - the Rust kernel normalizes the specification's `subst0<n>(b, u)` on
//!   their encodings as `Tm` values, and the result is decoded back;
//! - the Kush kernel normalizes `λⁿ. (λ. b) u` with its own `substitute`
//!   (and the `shift` it uses under binders), at depth `n`.
//!
//! The two must be the same term. The generator never puts a lambda in
//! function position and never substitutes one, so the substitution creates
//! no new redex and the normal form is exactly one substitution. This tests
//! the implementation against a specification whose properties the kernel
//! has proved; it is not a proof that the implementation is correct.
//! `KUSH_KIK_SPEC_CASES` sets the number of cases (default 100;
//! `scripts/kernel-diff.sh` runs 1000).
use kush::kernel::Term as T;
use std::{path::PathBuf, process::Command};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Raw de Bruijn syntax, the specification's constructors.
#[derive(Clone, Debug, PartialEq)]
enum Raw {
    Var(usize),
    Sort(u64),
    App(Box<Raw>, Box<Raw>),
    Lam(Box<Raw>, Box<Raw>),
    Pi(Box<Raw>, Box<Raw>),
}

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D) % n
    }
}

/// A term in scope `scope`; `lambda` allows a lambda at the root.
fn generate(scope: usize, fuel: u64, lambda: bool, rng: &mut Rng) -> Raw {
    let leaf = |rng: &mut Rng| {
        if scope > 0 && rng.below(3) > 0 {
            Raw::Var(rng.below(scope as u64) as usize)
        } else {
            Raw::Sort(rng.below(3))
        }
    };
    if fuel == 0 {
        return leaf(rng);
    }
    let fuel = fuel - 1;
    match rng.below(if lambda { 5 } else { 4 }) {
        0 => leaf(rng),
        1 => Raw::App(
            Box::new(generate(scope, fuel, false, rng)),
            Box::new(generate(scope, fuel, true, rng)),
        ),
        2 => Raw::Pi(
            Box::new(generate(scope, fuel, true, rng)),
            Box::new(generate(scope + 1, fuel, true, rng)),
        ),
        3 => Raw::App(
            Box::new(leaf(rng)),
            Box::new(generate(scope, fuel, true, rng)),
        ),
        _ => Raw::Lam(
            Box::new(generate(scope, fuel, true, rng)),
            Box::new(generate(scope + 1, fuel, true, rng)),
        ),
    }
}

fn nat(n: usize) -> T {
    T::natural((n as u64).into())
}

fn fin_type(n: usize) -> T {
    T::app(T::global("Fin"), nat(n))
}

/// The variable `index` of a scope of `scope` binders, as a `Fin<scope>`:
/// `None` for 0, `Some` of the next one out otherwise.
fn fin(index: usize, scope: usize) -> T {
    let inner = fin_type(scope - 1);
    if index == 0 {
        T::app(T::global("Maybe::None"), inner)
    } else {
        T::app(
            T::app(T::global("Maybe::Some"), inner),
            fin(index - 1, scope - 1),
        )
    }
}

/// The encoding of a raw term of scope `scope` as a `Tm<scope>` value.
fn encode(t: &Raw, scope: usize) -> T {
    let constructor = |name: &str, n: usize| T::app(T::global(name), nat(n));
    match t {
        Raw::Var(i) => T::app(constructor("Tm::Var", scope), fin(*i, scope)),
        Raw::Sort(l) => T::app(constructor("Tm::Sort", scope), T::natural((*l).into())),
        Raw::App(f, a) => T::app(
            T::app(constructor("Tm::App", scope), encode(f, scope)),
            encode(a, scope),
        ),
        Raw::Lam(d, b) => T::app(
            T::app(constructor("Tm::Lam", scope), encode(d, scope)),
            encode(b, scope + 1),
        ),
        Raw::Pi(d, b) => T::app(
            T::app(constructor("Tm::Pi", scope), encode(d, scope)),
            encode(b, scope + 1),
        ),
    }
}

fn spine(t: &T) -> (&T, Vec<&T>) {
    let mut arguments = Vec::new();
    let mut current = t;
    while let T::App(f, a) = current {
        arguments.push(a.as_ref());
        current = f.as_ref();
    }
    arguments.reverse();
    (current, arguments)
}

fn natural_value(t: &T) -> u64 {
    match t {
        T::Zero => 0,
        T::Literal(n) => n.to_string().parse().unwrap(),
        other => panic!("not a numeral: {other:?}"),
    }
}

/// Decode a normal `Fin` value to a variable index.
fn decode_fin(t: &T) -> usize {
    let (head, arguments) = spine(t);
    match head {
        T::Global(name, _) if name == "Maybe::None" => 0,
        T::Global(name, _) if name == "Maybe::Some" => 1 + decode_fin(arguments[1]),
        other => panic!("not a Fin value: {other:?}"),
    }
}

/// Decode a normal `Tm` value (constructor arguments: scope, then fields).
fn decode(t: &T) -> Raw {
    let (head, arguments) = spine(t);
    let T::Global(name, _) = head else {
        panic!("not a Tm value: {t:?}")
    };
    match name.as_str() {
        "Tm::Var" => Raw::Var(decode_fin(arguments[1])),
        "Tm::Sort" => Raw::Sort(natural_value(arguments[1])),
        "Tm::App" => Raw::App(
            Box::new(decode(arguments[1])),
            Box::new(decode(arguments[2])),
        ),
        "Tm::Lam" => Raw::Lam(
            Box::new(decode(arguments[1])),
            Box::new(decode(arguments[2])),
        ),
        "Tm::Pi" => Raw::Pi(
            Box::new(decode(arguments[1])),
            Box::new(decode(arguments[2])),
        ),
        other => panic!("unknown constructor {other}"),
    }
}

/// A raw term as a kernel term (for the Kush kernel's own reduction).
fn kernel_term(t: &Raw) -> T {
    match t {
        Raw::Var(i) => T::Var(*i),
        Raw::Sort(l) => T::universe(*l as u32),
        Raw::App(f, a) => T::app(kernel_term(f), kernel_term(a)),
        Raw::Lam(d, b) => T::lam(kernel_term(d), kernel_term(b)),
        Raw::Pi(d, b) => T::pi(kernel_term(d), kernel_term(b)),
    }
}

fn under_binders(t: T, count: usize) -> T {
    (0..count).fold(t, |body, _| T::lam(T::universe(0), body))
}

#[test]
fn the_implementations_substitution_matches_the_specification() {
    let cases: u64 = std::env::var("KUSH_KIK_SPEC_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(100);
    // The Rust kernel checks the specification, then computes with it.
    let spec = std::fs::read_to_string(root().join("examples/kernel/spec/scoped.kush")).unwrap();
    let checked = kush::check(&spec).unwrap_or_else(|error| panic!("{error:?}"));
    let kernel = &checked.kernel;

    let mut queries = String::new();
    let mut expected = String::new();
    let mut rng = Rng(0x5EC_D1FF);
    let mut binders_crossed = 0;
    for _ in 0..cases {
        let n = rng.below(3) as usize;
        let b = generate(n + 1, 1 + rng.below(4), true, &mut rng);
        let u = generate(n, rng.below(3), false, &mut rng);
        // The specification's answer, from the Rust kernel.
        let query = T::app(
            T::app(T::app(T::global("subst0"), nat(n)), encode(&b, n + 1)),
            encode(&u, n),
        );
        let normal = kernel
            .normalize_closed(&query)
            .unwrap_or_else(|error| panic!("{b:?} {u:?}: {error}"));
        let result = decode(&normal);
        if format!("{b:?}").contains("Lam") || format!("{b:?}").contains("Pi") {
            binders_crossed += 1;
        }
        // The implementation's: one beta step at depth n.
        let redex = T::app(T::lam(T::universe(0), kernel_term(&b)), kernel_term(&u));
        queries += &format!(
            "(normalize {})\n",
            kush::exchange::term_sexp(&under_binders(redex, n))
        );
        expected += &format!(
            "= {}\n",
            kush::exchange::term_sexp(&under_binders(kernel_term(&result), n))
        );
    }
    assert!(
        binders_crossed * 3 >= cases,
        "the cases must go under binders"
    );

    let dir = std::env::temp_dir().join(format!("kush-spec-diff-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
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
    let file = dir.join("substitutions.kcore");
    std::fs::write(&file, &queries).unwrap();
    // `normalize` mode reduces without type checking: raw terms are untyped.
    let output = Command::new(&binary)
        .arg("normalize")
        .arg(&file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let answers = String::from_utf8(output.stdout).unwrap();
    for (index, (actual, wanted)) in answers.lines().zip(expected.lines()).enumerate() {
        assert_eq!(
            actual,
            wanted,
            "case {index}: {}",
            queries.lines().nth(index).unwrap()
        );
    }
    assert_eq!(answers.lines().count(), cases as usize);
    std::fs::remove_dir_all(&dir).ok();
}
