//! Call-scoped shared and exclusive nominal-record receivers.
//!
//! The supported subset is deliberately narrow: a borrowed receiver is a
//! direct local owner, a borrow lasts for one full expression, and a `&mut`
//! method may replace only copyable non-owning fields. These tests compare the
//! reference evaluator with Cranelift native execution and exercise the
//! ownership boundaries that make the subset sound.

use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("borrowed-methods-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
        let stderr = String::from_utf8(output.stderr).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap_or_else(|| panic!("missing native allocation diagnostics: {stderr:?}"));
        assert_eq!(line, stats.report(), "{source}");
    }
    stats
}

#[test]
fn inherent_shared_and_exclusive_receivers_update_in_both_backends() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        impl Point {
            fn sum(self: &Self) -> i64 ! {panic} { self.x + self.y }
            fn sugar_sum(&self) -> i64 ! {panic} { self.x + self.y }
            fn bump(&mut self, by: i64) -> Unit ! {panic} {
                self.x = self.x + by;
                self.y = self.y + by;
            }
            fn bump_y(self: &mut Self, by: i64) -> Unit ! {panic} {
                self.y = self.y + by;
            }
        }
        fn main() -> i64 ! {io, panic} {
            let mut p = Point { x: 1, y: 2 };
            print_i64(p.sum());
            print_i64(p.sugar_sum());
            p.bump(3);
            print_i64(p.sum());
            p.bump_y(1);
            print_i64(p.sum());
            p.x + p.y
        }
        "#,
        10,
        "3\n3\n9\n10\n",
    );
}

#[test]
fn ordinary_record_reference_parameters_read_and_write() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn sum(p: &Point) -> i64 ! {panic} { p.x + p.y }
        fn shift(p: &mut Point, by: i64) -> Unit ! {panic} {
            p.x = p.x + by;
            p.y = p.y + by;
        }
        fn main() -> i64 ! {io, panic} {
            let mut p = Point { x: 4, y: 5 };
            print_i64(sum(&p));
            shift(&mut p, 2);
            print_i64(sum(&p));
            p.x
        }
        "#,
        6,
        "9\n13\n",
    );
}

#[test]
fn nested_copyable_records_and_inline_arrays_are_readable() {
    agrees(
        r#"
        struct Inner { x: i64 }
        struct Outer { inner: Inner, note: i64, values: [i64; 2] }
        impl Outer {
            fn sum_all(&self) -> i64 ! {panic} {
                self.inner.x + self.note + self.values[0] + self.values[1]
            }
            fn set_inner(&mut self, value: i64) -> Unit ! {panic} {
                self.inner.x = value;
            }
        }
        fn main() -> i64 ! {io, panic} {
            let mut o = Outer { inner: Inner { x: 1 }, note: 2, values: [3, 4] };
            print_i64(o.sum_all());
            o.set_inner(10);
            print_i64(o.sum_all());
            o.inner.x + o.note
        }
        "#,
        12,
        "10\n19\n",
    );
}

#[test]
fn owning_record_metadata_is_not_duplicated_and_still_cleans_up() {
    let stats = agrees(
        r#"
        struct Meta { token: Box<i64>, x: i64 }
        impl Meta {
            fn value(&self) -> i64 ! {panic} { self.x }
            fn assign_x(&mut self, value: i64) -> Unit ! {panic} { self.x = value; }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut m = Meta { token: Box.new(40), x: 1 };
            print_i64(m.value());
            m.assign_x(2);
            print_i64(m.value());
            let Meta { token, x } = m;
            print_i64(x + Box.take(token));
            x
        }
        "#,
        2,
        "1\n2\n42\n",
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
}

#[test]
fn shared_borrows_may_alias_but_exclusive_borrows_do_not() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        fn sum(a: &Point, b: &Point) -> i64 ! {panic} {
            a.x + a.y + b.x + b.y
        }
        fn twice(a: &mut Point, b: &Point) -> Unit ! {panic} {
            a.x = a.x + b.x;
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 1, y: 2 };
            let q = Point { x: 3, y: 4 };
            let a = sum(&p, &p);
            twice(&mut p, &q);
            a + p.x
        }
        "#,
        10,
        "",
    );
}

#[test]
fn exclusive_borrows_reject_shared_aliases_moves_reads_and_replacement() {
    rejects(
        r#"
        struct P { x: i64 }
        impl P { fn bump(&mut self) -> Unit ! {panic} { self.x = self.x + 1; } }
        fn main() -> Unit ! {panic} {
            let p = P { x: 1 };
            p.bump();
        }
        "#,
        "immutable binding",
    );
    rejects(
        r#"
        struct P { x: i64 }
        impl P { fn bump(&mut self, by: i64) -> Unit ! {panic} { self.x = self.x + by; } }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            p.bump(p.x);
        }
        "#,
        "exclusive",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn take(a: &mut P, b: &P) -> Unit ! {panic} { a.x = b.x; }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            take(&mut p, &p);
        }
        "#,
        "exclusive",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn take(a: &P, b: &mut P) -> Unit ! {panic} { b.x = a.x; }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            take(&p, &mut p);
        }
        "#,
        "exclusive",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn take(a: &P, extra: i64) -> Unit ! {panic} {}
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            take(&p, { p = P { x: 2 }; 0 });
        }
        "#,
        "borrowed by a call",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn take(a: &P, extra: i64) -> Unit ! {panic} {}
        fn main() -> Unit ! {panic} {
            let p = P { x: 1 };
            take(&p, { drop(p); 0 });
        }
        "#,
        "cannot move or drop",
    );
    rejects(
        r#"
        struct P { x: i64 }
        impl P { fn probe_mut(self: &mut Self) -> Unit ! {panic} {} }
        fn main() -> Unit ! {panic} {
            let p = P { x: 1 };
            p.probe_mut();
        }
        "#,
        "immutable binding",
    );
}

#[test]
fn references_reject_temporaries_fields_storage_returns_and_owned_writes() {
    rejects(
        r#"
        struct P { x: i64 }
        impl P { fn peek_value(&self) -> i64 ! {panic} { self.x } }
        fn main() -> i64 ! {panic} { P { x: 1 }.peek_value() }
        "#,
        "direct local binding",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn peek_ref(p: &P) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} { let p = P { x: 1 }; peek_ref(&p.x) }
        "#,
        "direct local binding",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn peek_ref(p: &P) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} { let p = P { x: 1 }; let r = &p; peek_ref(r) }
        "#,
        "cannot be stored in local bindings",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn escape<'a>(p: &'a P) -> &'a P ! {panic} {
            let local = P { x: 1 };
            &local
        }
        fn main() -> Unit ! {panic} {}
        "#,
        "escapes",
    );
    rejects(
        r#"
        struct P { token: Box<i64>, x: i64 }
        impl P { fn token_value(&self) -> i64 ! {panic} { self.token.read() } }
        fn main() -> Unit ! {panic} {}
        "#,
        "owns storage",
    );
    rejects(
        r#"
        struct P { token: Box<i64>, x: i64 }
        impl P { fn replace(&mut self) -> Unit ! {alloc, panic} { self.token = Box.new(1); } }
        fn main() -> Unit ! {panic} {}
        "#,
        "owns storage",
    );
}

#[test]
fn shared_receivers_cannot_write_or_be_upgraded() {
    rejects(
        r#"
        struct P { x: i64 }
        impl P { fn bad(self: &Self) -> Unit ! {panic} { self.x = 1; } }
        fn main() -> Unit ! {panic} {}
        "#,
        "shared reference",
    );
    rejects(
        r#"
        struct P { x: i64 }
        impl P {
            fn bump(&mut self) -> Unit ! {panic} { self.x = self.x + 1; }
            fn call(&self) -> Unit ! {panic} { self.bump(); }
        }
        fn main() -> Unit ! {panic} {}
        "#,
        "existing reference",
    );
    rejects(
        r#"
        struct View<'a> { view: &'a [i64] }
        fn bad<'a>(view: &mut View<'a>) -> Unit ! {panic} {}
        fn main() -> Unit ! {panic} {}
        "#,
        "borrowed fields",
    );
}

#[test]
fn borrowed_trait_receivers_keep_exact_contracts() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        trait Describe {
            fn describe(self: &Self) -> i64 ! {panic};
            fn add(&mut self, by: i64) -> Unit ! {panic};
        }
        impl Describe for Point {
            fn describe(self: &Self) -> i64 ! {panic} { self.x * 10 + self.y }
            fn add(self: &mut Self, by: i64) -> Unit ! {panic} { self.x = self.x + by; }
        }
        fn main() -> i64 ! {io, panic} {
            let mut p = Point { x: 1, y: 2 };
            print_i64(p.describe());
            p.add(2);
            print_i64(p.describe());
            p.x
        }
        "#,
        3,
        "12\n32\n",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Get { fn value_of(self: &Self) -> i64 ! {panic}; }
        impl Get for Point { fn value_of(self: Point) -> i64 ! {panic} { self.x } }
        fn main() -> Unit ! {panic} {}
        "#,
        "does not match the trait signature",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Get { fn value_of(self: &Self) -> i64 ! {panic}; }
        impl Get for Point { fn value_of(self: &mut Self) -> i64 ! {panic} { self.x } }
        fn main() -> Unit ! {panic} {}
        "#,
        "does not match the trait signature",
    );
}

#[test]
fn generic_bounded_helpers_borrow_without_erasing_the_bound() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        trait Describe {
            fn describe(self: &Self) -> i64 ! {panic};
        }
        impl Describe for Point {
            fn describe(self: &Self) -> i64 ! {panic} { self.x * 10 + self.y }
        }
        fn describe_via<T: Describe>(value: T) -> i64 ! {panic} {
            value.describe()
        }
        fn main() -> i64 ! {panic} {
            let p = Point { x: 4, y: 2 };
            describe_via(p)
        }
        "#,
        42,
        "",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        trait Describe { fn describe(self: &Self) -> i64 ! {panic}; }
        fn describe_via<T: Describe>(value: T) -> i64 ! {panic} {
            value.describe()
        }
        fn main() -> i64 ! {panic} { describe_via(Point { x: 1 }) }
        "#,
        "does not implement trait",
    );
}

#[test]
fn borrowed_helpers_keep_noalloc_and_nosuspend_contracts() {
    agrees(
        r#"
        struct Point { x: i64, y: i64 }
        #[noalloc]
        #[nosuspend]
        fn sum(p: &Point) -> i64 ! {panic} { p.x + p.y }
        #[noalloc]
        #[nosuspend]
        fn shift(p: &mut Point, by: i64) -> Unit ! {panic} {
            p.x = p.x + by;
        }
        fn main() -> i64 ! {panic} {
            let mut p = Point { x: 20, y: 21 };
            shift(&mut p, 1);
            sum(&p)
        }
        "#,
        42,
        "",
    );
    rejects(
        r#"
        struct Point { x: i64 }
        #[noalloc]
        fn bad(p: &Point) -> i64 ! {alloc, panic} { Box.take(Box.new(1)) }
        fn main() -> Unit ! {panic} {}
        "#,
        "noalloc",
    );
}

#[test]
fn borrowed_receiver_dispatch_is_disambiguated_and_scoped() {
    agrees(
        r#"
        struct P { x: i64 }
        trait First { fn label(self: &Self) -> i64 ! {panic}; }
        trait Second { fn label(self: &Self) -> i64 ! {panic}; }
        impl First for P { fn label(self: &Self) -> i64 ! {panic} { self.x + 10 } }
        impl Second for P { fn label(self: &Self) -> i64 ! {panic} { self.x + 20 } }
        fn sum(a: &P, b: &P) -> i64 ! {panic} { a.x + b.x }
        fn main() -> i64 ! {panic} {
            let p = P { x: 1 };
            let a = p.First.label();
            let b = p.Second.label();
            let c = sum(&p, &p);
            a + b + c
        }
        "#,
        34,
        "",
    );
}

#[test]
fn borrowing_a_linear_record_does_not_consume_or_launder_it() {
    agrees(
        r#"
        #[linear]
        struct Token { id: i64 }
        impl Token { fn token_id(self: &Self) -> i64 ! {panic} { self.id } }
        fn consume(token: Token) -> i64 ! {panic} {
            match token { Token { id } => id }
        }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 7 };
            let first = token.token_id();
            let second = token.token_id();
            first + second + consume(token)
        }
        "#,
        21,
        "",
    );
    rejects(
        r#"
        #[linear]
        struct Token { id: i64 }
        impl Token { fn token_id(self: &Self) -> i64 ! {panic} { self.id } }
        fn main() -> i64 ! {panic} {
            let token = Token { id: 7 };
            token.token_id();
            0
        }
        "#,
        "linear value is not consumed",
    );
}

#[test]
fn borrowed_fields_and_temporary_reference_arguments_stay_rejected() {
    rejects(
        r#"
        struct View<'a> { view: &'a [i64], note: i64 }
        fn peek<'a>(v: &View<'a>) -> i64 ! {panic} { Slice.len(v.view) }
        fn main() -> Unit ! {panic} {}
        "#,
        "contains a borrow",
    );
    rejects(
        r#"
        #[linear]
        struct Inner { x: i64 }
        struct Holder { inner: Inner }
        fn peek(h: &Holder) -> i64 ! {panic} { h.inner.x }
        fn main() -> Unit ! {panic} {}
        "#,
        "owns storage or contains a borrow",
    );
    rejects(
        r#"
        struct P { x: i64 }
        fn peek(p: &P) -> i64 ! {panic} { p.x }
        fn main() -> i64 ! {panic} { peek(&P { x: 1 }) }
        "#,
        "direct local binding",
    );
    rejects(
        r#"
        struct P { values: [i64; 2] }
        fn peek(p: &P) -> i64 ! {panic} { p.values[0] }
        fn main() -> i64 ! {panic} {
            let p = P { values: [1, 2] };
            peek(&p.values[0])
        }
        "#,
        "direct local binding",
    );
}

#[test]
fn owner_becomes_usable_again_after_the_borrow_expression() {
    agrees(
        r#"
        struct P { x: i64, y: i64 }
        impl P {
            fn sum(&self) -> i64 ! {panic} { self.x + self.y }
            fn bump(&mut self, by: i64) -> Unit ! {panic} { self.x = self.x + by; }
        }
        fn main() -> i64 ! {io, panic} {
            let mut p = P { x: 1, y: 2 };
            let before = p.sum();
            p.bump(4);
            let after = p.sum();
            print_i64(before);
            print_i64(after);
            p.x
        }
        "#,
        5,
        "3\n7\n",
    );
}

#[test]
fn borrowed_methods_example_runs_in_both_backends() {
    agrees(
        include_str!("../../../examples/borrowed-methods.kush"),
        11,
        "3\n12\n9\n6\n",
    );
}

#[test]
fn exclusive_record_loans_block_later_method_aliases() {
    rejects(
        r#"
        struct P { x: i64 }
        impl P {
            fn bump(&mut self, by: i64) -> Unit ! {panic} { self.x = self.x + by; }
            fn peek(&self) -> i64 ! {panic} { self.x }
        }
        fn main() -> Unit ! {panic} {
            let mut p = P { x: 1 };
            p.bump(p.peek());
        }
        "#,
        "exclusive",
    );
}
