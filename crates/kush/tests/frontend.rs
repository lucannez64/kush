use kush::{
    Diagnostic, Span,
    ast::*,
    lexer::{Kind, lex},
    parse,
};

fn expression(text: &str) -> Expr {
    let module = parse(&format!("fn test() -> Unit ! {{}} {{ {text} }}")).unwrap();
    let ItemKind::Function(function) = module.items.into_iter().next().unwrap().item.kind else {
        panic!("not a function")
    };
    *function.body.unwrap().tail.unwrap()
}
fn binary(expr: &Expr, expected: Kind) -> (&Expr, &Expr) {
    let ExprKind::Binary { op, left, right } = &expr.kind else {
        panic!("not binary: {expr:?}")
    };
    assert_eq!(*op, expected);
    (left, right)
}

#[test]
fn parser_compiler_fixture() {
    let module = parse(include_str!("../../../examples/parser.kush")).unwrap();
    assert_eq!(module.items.len(), 13);
    let function = module
        .items
        .iter()
        .find_map(|d| match &d.item.kind {
            ItemKind::Function(f) if f.name == "classify" => Some(f),
            _ => None,
        })
        .unwrap();
    let ExprKind::Match { arms, .. } = &function.body.as_ref().unwrap().tail.as_ref().unwrap().kind
    else {
        panic!()
    };
    assert_eq!(arms.len(), 4);
    assert!(arms[1].guard.is_some());
    assert!(matches!(&arms[3].pattern.kind, PatternKind::Or(p) if p.len() == 3));
}

#[test]
fn comments_unicode_and_byte_spans() {
    let source = "/* outer /* λ */ end */ \"é🦀\" // ignored\n next";
    let tokens = lex(source).unwrap();
    assert_eq!(tokens.len(), 3);
    assert_eq!(tokens[0].kind, Kind::String("é🦀".into()));
    assert_eq!(&source[tokens[0].span.start..tokens[0].span.end], "\"é🦀\"");
    assert_eq!(tokens[1].kind, Kind::Ident("next".into()));
    assert_eq!(tokens[2].span, Span::new(source.len(), source.len()));
}

#[test]
fn comments_inside_literals_are_not_trivia() {
    let tokens = lex("\"/* x */ // y\" '/' '\\n' '\\''").unwrap();
    assert_eq!(tokens[0].kind, Kind::String("/* x */ // y".into()));
    assert_eq!(tokens[1].kind, Kind::Char('/'));
    assert_eq!(tokens[2].kind, Kind::Char('\n'));
    assert_eq!(tokens[3].kind, Kind::Char('\''));
}

#[test]
fn integer_lexing_is_lossless_and_does_not_assume_a_machine_width() {
    let tokens = lex("18_446_744_073_709_551_616").unwrap();
    assert_eq!(tokens[0].kind, Kind::Integer("18446744073709551616".into()));
    for input in ["1_", "1__0", "0x", "0b2", "12u32"] {
        assert!(lex(input).is_err(), "{input}");
    }
    // Hexadecimal, binary, and octal literals are normalized to decimal.
    let tokens = lex("0xff 0b1010 0o17").unwrap();
    assert_eq!(tokens[0].kind, Kind::Integer("255".into()));
    assert_eq!(tokens[1].kind, Kind::Integer("10".into()));
    assert_eq!(tokens[2].kind, Kind::Integer("15".into()));
}

#[test]
fn longest_operator_and_nested_generic_closing_tokens() {
    let tokens = lex("-> => :: .. && || == != <= >= >>").unwrap();
    assert_eq!(
        tokens.into_iter().map(|t| t.kind).collect::<Vec<_>>(),
        vec![
            Kind::Arrow,
            Kind::FatArrow,
            Kind::ColonColon,
            Kind::DotDot,
            Kind::AmpAmp,
            Kind::PipePipe,
            Kind::EqEq,
            Kind::Ne,
            Kind::Le,
            Kind::Ge,
            Kind::Gt,
            Kind::Gt,
            Kind::Eof,
        ]
    );
}

#[test]
fn malformed_literals_and_comments_have_source_spans() {
    for input in [
        "/* missing",
        "\"missing",
        "'ab'",
        "''",
        "\"\\x\"",
        "\"raw\nnewline\"",
        "é",
    ] {
        let error = lex(input).unwrap_err();
        assert_eq!(error.span.start, 0, "{input}");
        assert!(error.span.end > 0, "{input}");
        assert!(input.is_char_boundary(error.span.end));
    }
}

#[test]
fn diagnostic_columns_are_unicode_aware_and_tabs_expand() {
    let source = "// é\n\t\"λ\" @";
    let start = source.find('@').unwrap();
    let rendered =
        Diagnostic::new(Span::new(start, start + 1), "unexpected token").render("bad.kush", source);
    assert!(rendered.contains("bad.kush:2:9"), "{rendered}");
    assert!(rendered.contains("2 |     \"λ\" @"));
    assert!(rendered.contains("|         ^"));
    // Rendering an EOF diagnostic is also well-defined.
    let eof = Diagnostic::new(Span::new(0, 0), "empty").render("empty", "");
    assert!(eof.contains("empty:1:1"));
}

#[test]
fn precedence_and_associativity() {
    let expr = expression("a = b = 1 + 2 * 3 - 4");
    let (_, rhs) = binary(&expr, Kind::Eq);
    let (_, rhs) = binary(rhs, Kind::Eq);
    let (lhs, _) = binary(rhs, Kind::Minus);
    let (_, rhs) = binary(lhs, Kind::Plus);
    binary(rhs, Kind::Star);
    let expr = expression("a || b && c == d + e");
    let (_, rhs) = binary(&expr, Kind::PipePipe);
    let (_, rhs) = binary(rhs, Kind::AmpAmp);
    let (_, rhs) = binary(rhs, Kind::EqEq);
    binary(rhs, Kind::Plus);
    let expr = expression("8 - 3 - 1");
    let (lhs, _) = binary(&expr, Kind::Minus);
    binary(lhs, Kind::Minus);
}

#[test]
fn comparisons_do_not_chain_but_parentheses_allow_explicit_grouping() {
    for body in ["a < b < c", "a == b != c", "a <= b > c"] {
        assert!(
            parse(&format!("fn f() -> Bool ! {{}} {{ {body} }}"))
                .unwrap_err()
                .message
                .contains("do not chain")
        );
    }
    expression("(a < b) == true");
    expression("a < b && b < c");
}

#[test]
fn postfix_binds_more_tightly_than_unary() {
    let expr = expression("-factory::<i64, 3>(x).values[0]?");
    let ExprKind::Unary { operand, .. } = expr.kind else {
        panic!()
    };
    let ExprKind::Try(index) = operand.kind else {
        panic!()
    };
    let ExprKind::Index { value, .. } = index.kind else {
        panic!()
    };
    let ExprKind::Field { value, name } = value.kind else {
        panic!()
    };
    assert_eq!(name, "values");
    let ExprKind::Call { callee, .. } = value.kind else {
        panic!()
    };
    assert!(matches!(callee.kind, ExprKind::Specialize { .. }));
}

#[test]
fn tuple_grouping_unit_and_arrays_are_distinct() {
    assert!(matches!(expression("()").kind, ExprKind::Tuple(v) if v.is_empty()));
    assert!(matches!(expression("(1)").kind, ExprKind::Integer(_)));
    assert!(matches!(expression("(1,)").kind, ExprKind::Tuple(v) if v.len() == 1));
    assert!(matches!(expression("[1, 2,]").kind, ExprKind::Array(v) if v.len() == 2));
}

#[test]
fn indexed_enum_named_payload_and_nested_generics() {
    let m = parse("enum E<T: Type> { A(Box<E<i64>>): E<i64>, B { value: T }, Empty, }").unwrap();
    let ItemKind::Enum {
        variants, generics, ..
    } = &m.items[0].item.kind
    else {
        panic!()
    };
    assert_eq!(generics[0].name, "T");
    assert!(variants[0].result.is_some());
    assert!(matches!(&variants[1].payload, Payload::Record(fields) if fields[0].name == "value"));
    assert_eq!(variants[0].span.start, 18);
}

#[test]
fn type_precedence_borrows_and_grades() {
    let m = parse("type X = &mut A | B & C @[1];").unwrap();
    let ItemKind::Alias { ty, .. } = &m.items[0].item.kind else {
        panic!()
    };
    let TypeKind::Binary {
        op: Kind::Pipe,
        left,
        right,
    } = &ty.kind
    else {
        panic!()
    };
    assert!(matches!(left.kind, TypeKind::Borrow { mutable: true, .. }));
    let TypeKind::Binary {
        op: Kind::Amp,
        right,
        ..
    } = &right.kind
    else {
        panic!()
    };
    assert!(matches!(right.kind, TypeKind::Graded { .. }));
}

#[test]
fn signatures_effect_rows_erased_parameters_and_function_types() {
    let m = parse(
        "#[noalloc] pub total fn id<T: Type>(erased p: Proof, f: fn(T) -> T ! {e}) -> T ! {e};",
    )
    .unwrap();
    let declaration = &m.items[0];
    assert!(declaration.public);
    assert_eq!(declaration.attributes[0].kind, "noalloc");
    let ItemKind::Function(f) = &declaration.item.kind else {
        panic!()
    };
    assert!(f.total);
    assert!(f.body.is_none());
    assert!(f.parameters[0].erased);
    assert!(matches!(f.parameters[1].ty.kind, TypeKind::Function { .. }));
    assert_eq!(f.effects.len(), 1);
}

#[test]
fn nested_patterns_rest_alternatives_records_and_guards() {
    let expr = expression(
        "match x { Some([head, .., last]) if head > 0 => last, Pair { left: (a, b), right } => a, A | B => 0, _ => -1, }",
    );
    let ExprKind::Match { arms, .. } = expr.kind else {
        panic!()
    };
    assert_eq!(arms.len(), 4);
    assert!(arms[0].guard.is_some());
    assert!(matches!(arms[1].pattern.kind, PatternKind::Record { .. }));
    assert!(matches!(arms[2].pattern.kind, PatternKind::Or(_)));
    assert!(parse("fn f() -> Unit ! {} { match x { [.., ..] => 0 } }").is_err());
    assert!(parse("fn f() -> Unit ! {} { match x { .. => 0 } }").is_err());
}

#[test]
fn blocks_keep_statement_and_tail_distinct() {
    let m =
        parse("fn f() -> i64 ! {} { let mut x: i64 = 1; x = 2; if true { return x; } x }").unwrap();
    let ItemKind::Function(f) = &m.items[0].item.kind else {
        panic!()
    };
    let body = f.body.as_ref().unwrap();
    assert_eq!(body.statements.len(), 3);
    assert!(matches!(
        body.statements[0],
        Statement::Let { mutable: true, .. }
    ));
    assert!(matches!(
        body.tail.as_ref().unwrap().kind,
        ExprKind::Name(_)
    ));
}

#[test]
fn malformed_programs_are_rejected_without_ignoring_trailing_input() {
    for source in [
        "fn f() {}",
        "pub fn f() -> Unit {}",
        "fn f() -> Unit ! {} { let x = 1 }",
        "fn f() -> Unit ! {} { 1 2 }",
        "fn f() -> Unit ! {} {",
        "enum E { A B }",
        "struct X { x i64 }",
        "type X = Box<i64;",
        "#[noalloc fn f() -> Unit ! {};",
        "total struct X { x: i64 }",
        "fn f() -> Unit ! {} {} trailing",
        "fn f() -> Unit ! {} { async {} }",
        "type X = i64; @",
        "use thing",
        "module a..b;",
    ] {
        let error = parse(source).expect_err(source);
        assert!(source.is_char_boundary(error.span.start), "{source}");
        assert!(source.is_char_boundary(error.span.end), "{source}");
        assert!(!error.message.is_empty());
    }
}

#[test]
fn syntax_only_accepts_semantically_invalid_code_without_claiming_verification() {
    // Names, effects, linearity, and coverage belong to subsequent passes.
    parse("fn f(x: Unknown) -> Missing ! {} { match x { A => undefined } }").unwrap();
}

#[test]
fn resource_limits_produce_diagnostics() {
    let deeply_nested = format!(
        "fn f() -> Unit ! {{}} {{ {}0{} }}",
        "(".repeat(200),
        ")".repeat(200)
    );
    assert!(
        parse(&deeply_nested)
            .unwrap_err()
            .message
            .contains("nesting limit")
    );
    // The documented budget includes exactly 128 postfix extensions.
    expression(&format!("a{}", ".field".repeat(128)));
    let chain = format!("fn f() -> Unit ! {{}} {{ a{} }}", ".field".repeat(200));
    assert!(parse(&chain).unwrap_err().message.contains("chain exceeds"));
    assert!(
        lex(&" ".repeat(4 * 1024 * 1024 + 1))
            .unwrap_err()
            .message
            .contains("file limit")
    );
    assert!(
        lex(&";".repeat(100_001))
            .unwrap_err()
            .message
            .contains("token limit")
    );
}

#[test]
fn arbitrary_small_utf8_inputs_do_not_panic_or_return_invalid_spans() {
    // Deterministic mutation corpus: exercises lexer/parser failure paths without
    // introducing a fuzzing dependency or assuming arbitrary bytes are UTF-8.
    let alphabet = [
        'a', '0', '\'', '"', '\\', 'λ', '\n', '/', '*', '{', '}', '(', ')', '<', '>', '&', '|',
        ';', ':',
    ];
    let mut state = 0x5eed_u64;
    for _ in 0..2000 {
        let mut source = String::new();
        for _ in 0..32 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            source.push(alphabet[(state >> 32) as usize % alphabet.len()]);
        }
        if let Err(error) = parse(&source) {
            assert!(error.span.start <= error.span.end && error.span.end <= source.len());
            assert!(source.is_char_boundary(error.span.start));
            assert!(source.is_char_boundary(error.span.end));
            error.render("generated", &source);
        }
    }
}

#[test]
fn prop_declarations_and_logical_constructor_telescopes_parse() {
    let module = parse(
        "prop True { Trivial: True }
         total enum Fin<N: Nat> {
             FZero<n: Nat>: Fin<Nat.succ<n>>,
             FSucc<n: Nat>(pred: Fin<n>): Fin<Nat.succ<n>>,
             Cons(head: i64, tail: Fin<N>): Fin<N>,
         }
         total fn prop() -> Nat ! {} { 0 }",
    )
    .unwrap();
    let ItemKind::Prop {
        name,
        generics,
        variants,
    } = &module.items[0].item.kind
    else {
        panic!("not a prop")
    };
    assert_eq!(name, "True");
    assert!(generics.is_empty());
    assert_eq!(variants[0].name, "Trivial");
    assert!(matches!(variants[0].payload, Payload::Unit));
    let ItemKind::Enum { name, variants, .. } = &module.items[1].item.kind else {
        panic!("not an enum")
    };
    assert_eq!(name, "Fin");
    assert_eq!(variants[0].locals.len(), 1);
    assert_eq!(variants[0].locals[0].name, "n");
    assert!(matches!(&variants[1].payload, Payload::Fields(fields) if fields[0].name == "pred"));
    assert!(
        matches!(&variants[2].payload, Payload::Fields(fields) if fields.len() == 2 && fields[1].name == "tail")
    );
    // `prop` is contextual and remains a valid function name.
    assert!(matches!(&module.items[2].item.kind, ItemKind::Function(f) if f.name == "prop"));
}

// PARSE-BLOCK-CALL: a statement that starts with a block-like expression ends
// at its `}` when the next line starts with `(`, `[`, `-` or `*`.
fn block_statement_runs(source: &str, expected: i64) {
    let program = kush::executable::check(source).unwrap_or_else(|e| panic!("{e:?}\n{source}"));
    let (value, stats) = program
        .evaluate_with_stats(&mut Vec::new())
        .unwrap_or_else(|e| panic!("{e:?}\n{source}"));
    assert_eq!(value, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("block-statement");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
    }
}

#[test]
fn block_statement_ends_before_a_new_line_starting_with_paren_or_minus() {
    // `if` then a tuple on the next line.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            let mut a = 1;
            if a > 0 { a = a + 1; }
            (a, 7).1 + a
        }",
        9,
    );
    // `while` then a negative tail.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            let mut i = 0;
            while i < 3 { i = i + 1; }
            -1 + i * 10
        }",
        29,
    );
    // `match` then a negative tail.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            let n = 2;
            match n { 2 => {}, _ => {} }
            -(n - 7)
        }",
        5,
    );
    // A plain block then a parenthesized expression.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            { let x = 1; }
            (40 + 2)
        }",
        42,
    );
    // Same line: still an operator, as before.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            let c = true;
            if c { 10 } else { 20 } - 3
        }",
        7,
    );
    // Not at statement start (a let value): the next line still continues it.
    block_statement_runs(
        "fn main() -> i64 ! {panic} {
            let c = false;
            let v = if c { 10 } else { 20 }
                - 3;
            v
        }",
        17,
    );
    // A method call on the next line still continues the expression.
    block_statement_runs(
        "struct P { x: i64 }
        impl P { fn value(self: Self) -> i64 ! {} { self.x } }
        fn main() -> i64 ! {panic} {
            let c = true;
            if c { P { x: 4 } } else { P { x: 5 } }
                .value()
        }",
        4,
    );
}

#[test]
fn block_statement_parse_shape_and_rejections() {
    let tail = expression("if true { 1; }\n(2, 3)");
    assert!(matches!(tail.kind, ExprKind::Tuple(_)), "{tail:?}");
    let tail = expression("while false { }\n-1");
    assert!(
        matches!(tail.kind, ExprKind::Unary { .. } | ExprKind::Integer(_)),
        "{tail:?}"
    );
    let tail = expression("match x { _ => {} }\n[1, 2]");
    assert!(matches!(tail.kind, ExprKind::Array(_)), "{tail:?}");
    let tail = expression("loop { break; }\n*r");
    assert!(
        matches!(tail.kind, ExprKind::Unary { .. } | ExprKind::Integer(_)),
        "{tail:?}"
    );
    // A let value continues onto the next line: calling an integer is rejected.
    let error = kush::executable::check(
        "fn main() -> i64 ! {panic} {
            let v = if true { 1 } else { 2 }
                (3);
            v
        }",
    )
    .err()
    .unwrap_or_else(|| panic!("calling an integer must be rejected"));
    assert!(!error.message.is_empty());
    // A statement `if` with a non-unit value followed by `(..)` is two statements.
    let error = kush::executable::check(
        "fn main() -> i64 ! {panic} {
            if true { 1 } else { 2 }
            (true)
        }",
    )
    .err()
    .unwrap_or_else(|| panic!("a Bool tail of an i64 function must be rejected"));
    assert!(!error.message.is_empty());
}
