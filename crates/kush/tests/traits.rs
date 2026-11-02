//! Static trait dispatch and user-defined methods. Method calls lower to
//! ordinary checked function calls: the receiver is evaluated once before the
//! arguments, and the same coercions, proofs, effects, grades, and ownership
//! rules apply. There are no vtables, trait values, or runtime dispatch tables.
use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    assert!(source.is_char_boundary(error.span.start));
    assert!(source.is_char_boundary(error.span.end));
}

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("traits-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    if let Some(output) = native(source) {
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

const POINT: &str = r#"
struct Point { x: i64, y: i64 }
"#;

#[test]
fn inherent_methods_evaluate_the_receiver_once_before_arguments() {
    agrees(
        &format!(
            "{POINT}
            impl Point {{
                fn mix(self: Point, factor: i64) -> i64 ! {{io, panic}} {{
                    print_i64(self.x + self.y);
                    self.x * factor
                }}
            }}
            fn make(x: i64, y: i64) -> Point ! {{io, panic}} {{
                print_i64(x);
                Point {{ x: x, y: y }}
            }}
            fn argument(value: i64) -> i64 ! {{io, panic}} {{
                print_i64(value);
                value
            }}
            fn main() -> i64 ! {{io, panic}} {{
                print_i64(make(1, 2).mix(argument(3)));
                0
            }}"
        ),
        0,
        "1\n3\n3\n3\n",
    );
}

#[test]
fn inherent_methods_work_on_enums_and_owned_temporaries() {
    agrees(
        "enum Shape { Circle(i64), Square(i64) }
        impl Shape {
            fn area(self: Shape) -> i64 ! {panic} {
                match self {
                    Shape.Circle(radius) => 3 * radius * radius,
                    Shape.Square(side) => side * side,
                }
            }
        }
        fn main() -> i64 ! {panic} {
            Shape.Circle(2).area() + Shape.Square(3).area()
        }",
        21,
        "",
    );
}

#[test]
fn trait_methods_dispatch_statically_through_bounded_generics() {
    agrees(
        &format!(
            "{POINT}
            trait Describe {{
                fn describe(self: Self) -> i64 ! {{panic}};
            }}
            impl Describe for Point {{
                fn describe(self: Self) -> i64 ! {{panic}} {{ self.x * 10 + self.y }}
            }}
            fn describe_via<T: Describe>(value: T) -> i64 ! {{panic}} {{
                value.describe()
            }}
            fn main() -> i64 ! {{io, panic}} {{
                let point = Point {{ x: 4, y: 2 }};
                print_i64(describe_via(point));
                print_i64(describe_via(Point {{ x: 1, y: 9 }}));
                0
            }}"
        ),
        0,
        "42\n19\n",
    );
}

#[test]
fn traits_can_be_implemented_for_builtin_owned_buffers() {
    agrees(
        "trait ByteCount {
            fn byte_count(self: Self) -> i64 ! {};
        }
        impl ByteCount for Bytes {
            fn byte_count(self: Self) -> i64 ! {} { self.len() }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let bytes = Bytes.from(\"hé\");
            print_i64(bytes.byte_count());
            0
        }",
        0,
        "3\n",
    );
}

#[test]
fn ambiguous_trait_methods_require_explicit_trait_qualification() {
    let common = r#"
        struct Point { x: i64 }
        trait First { fn value(self: Self) -> i64 ! {panic}; }
        trait Second { fn value(self: Self) -> i64 ! {panic}; }
        impl First for Point {
            fn value(self: Self) -> i64 ! {panic} { self.x + 10 }
        }
        impl Second for Point {
            fn value(self: Self) -> i64 ! {panic} { self.x + 20 }
        }
    "#;
    agrees(
        &format!(
            "{common}
            fn main() -> i64 ! {{io, panic}} {{
                let point = Point {{ x: 1 }};
                print_i64(point.First.value());
                print_i64(point.Second.value());
                0
            }}"
        ),
        0,
        "11\n21\n",
    );
    rejects(
        &format!(
            "{common}
            fn main() -> i64 ! {{panic}} {{
                let point = Point {{ x: 1 }};
                point.value()
            }}"
        ),
        "is ambiguous",
    );
}

#[test]
fn missing_impls_are_rejected_even_when_the_body_never_calls_the_method() {
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        struct Point { x: i64 }
        fn helper<T: Describe>(value: T) -> i64 ! {} { 7 }
        fn main() -> i64 ! {panic} { helper(Point { x: 1 }) }",
        "does not implement trait",
    );
}

#[test]
fn trait_contracts_require_exact_parameters_grades_effects_and_returns() {
    let base = "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        struct Point { x: i64 }";
    rejects(
        &format!(
            "{base}
            impl Describe for Point {{
                fn describe(self: Self) -> Bool ! {{}} {{ true }}
            }}
            fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "does not match the trait signature exactly",
    );
    rejects(
        &format!(
            "{base}
            impl Describe for Point {{
                fn describe(self: Self) -> i64 ! {{panic}} {{ self.x }}
            }}
            fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "does not match the trait signature exactly",
    );
    rejects(
        "trait Count { fn add(self: Self, value: i64 @[1]) -> i64 ! {}; }
        struct Point { x: i64 }
        impl Count for Point {
            fn add(self: Self, value: i64 @[2]) -> i64 ! {} { self.x + value }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature exactly",
    );
    rejects(
        &format!(
            "{base}
            impl Describe for Point {{
                fn describe(self: Self) -> i64 ! {{}} {{ self.x }}
                fn extra(self: Self) -> i64 ! {{}} {{ 0 }}
            }}
            fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "is not declared by the implemented trait",
    );
    rejects(
        "trait Pair { fn left(self: Self) -> i64 ! {}; fn right(self: Self) -> i64 ! {}; }
        struct Point { x: i64 }
        impl Pair for Point {
            fn left(self: Self) -> i64 ! {} { self.x }
        }
        fn main() -> i64 ! {} { 0 }",
        "missing implementation of trait method 'right'",
    );
}

#[test]
fn duplicate_and_unsupported_impl_forms_are_explicit() {
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        struct Point { x: i64 }
        impl Describe for Point { fn describe(self: Self) -> i64 ! {} { 1 } }
        impl Describe for Point { fn describe(self: Self) -> i64 ! {} { 2 } }
        fn main() -> i64 ! {} { 0 }",
        "duplicate implementation of trait",
    );
    rejects(
        "struct Point { x: i64 }
        impl Point {
            fn value(self: Point) -> i64 ! {} { 1 }
            fn value(self: Point) -> i64 ! {} { 2 }
        }
        fn main() -> i64 ! {} { 0 }",
        "duplicate method 'value'",
    );
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        impl<T> Describe for T { fn describe(self: Self) -> i64 ! {} { 1 } }
        fn main() -> i64 ! {} { 0 }",
        "generic or blanket impls are not supported",
    );
    rejects(
        "trait Describe { pub fn describe(self: Self) -> i64 ! {} { 1 } }
        fn main() -> i64 ! {} { 0 }",
        "inherit the trait's visibility",
    );
    rejects(
        "trait Describe { type Output; fn describe(self: Self) -> i64 ! {}; }
        fn main() -> i64 ! {} { 0 }",
        "associated types are not supported",
    );
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        trait Wrapped<T: Describe> { fn get(self: Self) -> T ! {}; }
        fn main() -> i64 ! {} { 0 }",
        "trait parameters with trait bounds are not supported",
    );
}

#[test]
fn trait_names_are_bounds_not_runtime_types() {
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        fn f(value: Describe) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }",
        "is not a runtime type",
    );
    rejects(
        "trait Describe { fn describe(self: Self) -> i64 ! {}; }
        fn f(value: dyn Describe) -> i64 ! {} { 0 }
        fn main() -> i64 ! {} { 0 }",
        "dynamic trait objects are not supported",
    );
}

#[test]
fn reserved_names_fields_and_receiver_forms_are_rejected() {
    rejects(
        &format!(
            "{POINT}
            impl Point {{
                fn len(self: Point) -> i64 ! {{}} {{ 1 }}
            }}
            fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "reserved builtin method name",
    );
    rejects(
        "struct Point { sum: i64 }
        impl Point { fn sum(self: Point) -> i64 ! {} { self.sum } }
        fn main() -> i64 ! {} { 0 }",
        "collides with a record field",
    );
    rejects(
        "trait Count { fn add(self: Self) -> i64 ! {}; }
        struct Point { x: i64 }
        impl Count for Point {
            fn add(self: &Self) -> i64 ! {} { 1 }
        }
        fn main() -> i64 ! {} { 0 }",
        "does not match the trait signature",
    );
    rejects(
        &format!(
            "{POINT}
            impl Point {{
                fn sum(self: Point) -> i64 ! {{}} {{ self.x }}
            }}
            fn main() -> i64 ! {{}} {{
                let point = Point {{ x: 1, y: 2 }};
                point.sum::<i64>()
            }}"
        ),
        "take no explicit type arguments",
    );
    rejects(
        "struct Point { x: i64 }
        impl i64 { fn bump(self: i64) -> i64 ! {} { self + 1 } }
        fn main() -> i64 ! {} { 0 }",
        "inherent impls require a nominal record or enum",
    );
}

#[test]
fn owned_receivers_move_exactly_once_and_clean_up() {
    let source = r#"
        struct Token { text: String }
        impl Token {
            fn take_text(self: Token) -> String ! {alloc, panic} {
                let Token { text } = self;
                text
            }
        }
        fn make() -> Token ! {alloc, panic} {
            Token { text: String.from("abc") }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let first = make().take_text();
            print_i64(first.len());
            let token = make();
            let text = token.take_text();
            print_i64(text.len());
            0
        }
    "#;
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "3\n3\n");
    assert_eq!(stats.allocations, stats.deallocations);
    if let Some(output) = native(source) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"3\n3\n");
    }
    rejects(
        &format!(
            "{source}
            fn extra() -> Unit ! {{alloc, panic}} {{
                let token = make();
                let text = token.take_text();
                token.take_text();
            }}"
        ),
        "use after move",
    );
}

#[test]
fn cross_module_methods_require_public_visibility() {
    let root = std::env::temp_dir().join(format!(
        "kush-traits-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(
        root.join("demo").join("point.kush"),
        r#"module demo.point;
        pub struct Point { x: i64, y: i64 }
        pub trait Describe { fn describe(self: Self) -> i64 ! {panic}; }
        impl Point {
            pub fn sum(self: Point) -> i64 ! {panic} { self.x + self.y }
            fn hidden(self: Point) -> i64 ! {} { self.x }
        }
        impl Describe for Point {
            pub fn describe(self: Self) -> i64 ! {panic} { self.x * 10 + self.y }
        }
        "#,
    )
    .unwrap();
    std::fs::write(
        root.join("main.kush"),
        r#"use demo.point.Point;
        use demo.point.Describe;
        fn describe_via<T: Describe>(value: T) -> i64 ! {panic} { value.describe() }
        fn main() -> i64 ! {io, panic} {
            let point = Point { x: 4, y: 2 };
            print_i64(point.sum());
            let other = Point { x: 4, y: 2 };
            print_i64(describe_via(other));
            0
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "6\n42\n");
    if let Some(output) = native_program(&program) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"6\n42\n");
    }

    std::fs::write(
        root.join("main.kush"),
        r#"use demo.point.Point;
        fn main() -> i64 ! {} {
            let point = Point { x: 4, y: 2 };
            point.hidden()
        }
        "#,
    )
    .unwrap();
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let error = kush::executable::check_program(&loaded).unwrap_err();
    assert!(
        error.message.contains("is private to module 'demo.point'"),
        "{error:?}"
    );
    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn static_dispatch_does_not_allocate_and_linear_receivers_are_consumed_once() {
    let program = check(
        "struct Point { x: i64 }
        impl Point { fn value(self: Point) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {} { Point { x: 9 }.value() }",
    )
    .unwrap();
    let (status, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(status, 9);
    assert_eq!(stats.allocations, 0, "static dispatch adds no allocation");
    assert_eq!(stats.allocations, stats.deallocations);

    agrees(
        "#[linear] enum Token { Live }
        impl Token {
            fn spend(self: Token) -> i64 ! {} {
                match self { Token.Live => 7 }
            }
        }
        fn main() -> i64 ! {panic} { Token.Live.spend() }",
        7,
        "",
    );
    rejects(
        "#[linear] enum Token { Live }
        impl Token {
            fn spend(self: Token) -> i64 ! {} {
                match self { Token.Live => 7 }
            }
        }
        fn main() -> i64 ! {panic} {
            let token = Token.Live;
            token.spend();
            token.spend();
            0
        }",
        "use after move",
    );
}

#[test]
fn erased_method_parameters_are_discharged_and_cannot_be_relabelled() {
    agrees(
        "trait Positive {
            fn require(self: Self, erased positive: { 0 < self }) -> i64 ! {};
        }
        impl Positive for i64 {
            fn require(self: Self, erased positive: { 0 < self }) -> i64 ! {} { self }
        }
        fn main() -> i64 ! {} { (5).require(_) }",
        5,
        "",
    );
    rejects(
        "trait Positive {
            fn require(self: Self, erased positive: { 0 < self }) -> i64 ! {};
        }
        impl Positive for i64 {
            fn require(self: Self, erased negative: { self < 0 }) -> i64 ! {} { self }
        }
        fn main() -> i64 ! {} { (5).require(_) }",
        "does not match the trait signature exactly",
    );
}

#[test]
fn method_lifetime_returns_follow_the_normal_borrow_checks() {
    agrees(
        "struct Reader { bias: i64 }
        impl Reader {
            fn first<'a>(self: Reader, values: &'a [i64]) -> &'a [i64] ! {panic} {
                &values[..1]
            }
        }
        fn main() -> i64 ! {io, panic} {
            let values: [i64; 2] = [10, 20];
            let reader = Reader { bias: 0 };
            let view = reader.first(&values[..]);
            print_i64(view[0]);
            0
        }",
        0,
        "10\n",
    );
    rejects(
        "struct Reader { bias: i64 }
        impl Reader {
            fn first<'a>(self: Reader) -> &'a [i64] ! {panic} {
                &[1][..1]
            }
        }
        fn main() -> i64 ! {panic} { 0 }",
        "does not appear on any parameter that outlives it",
    );
}

#[test]
fn traits_example_matches_documented_output() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/traits.kush");
    let loaded = kush::program::load_path(&root).unwrap();
    let program = kush::executable::check_program(&loaded).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate(&mut output).unwrap(), 0);
    assert_eq!(String::from_utf8(output).unwrap(), "6\n18\n42\n71\n3\n");
    if let Some(output) = native_program(&program) {
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"6\n18\n42\n71\n3\n");
    }
}

fn native_program(program: &kush::executable::Executable) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("traits-multi-test");
        kush::native::build(program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}
