use kush::executable::{MemoryStats, check};

fn execute(source: &str) -> (String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    (String::from_utf8(output).unwrap(), stats)
}
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(error.message.contains(message), "{error:?}");
}
fn main_program(body: &str) -> String {
    format!("fn main()->Unit ! {{io,alloc,panic}} {{ {body} }}")
}

#[test]
fn example_and_literal_byte_encoding() {
    assert_eq!(
        execute(include_str!("../../../examples/bytes.kush")).0,
        "2\n52\n50\n3\n4\n"
    );
    let (output, stats) = execute(&main_program(
        r#"
        let empty=Bytes.from(""); print_i64(Bytes.len(&empty)); print_i64(Bytes.capacity(&empty));
        let text=Bytes.from("é\0"); print_i64(Bytes.len(&text)); print_i64(Bytes.capacity(&text));
        print_i64(Bytes.get(&text,0)); print_i64(Bytes.get(&text,1)); print_i64(Bytes.get(&text,2));
        let copy=Bytes.copy(&text); drop(text); print_i64(Bytes.get(&copy,0));
    "#,
    ));
    assert_eq!(output, "0\n0\n3\n3\n195\n169\n0\n195\n");
    assert_eq!(stats.allocations, 3);
}

#[test]
fn growth_and_reserved_append_preserve_ownership_and_capacity() {
    let mut body = "let mut b=Bytes.with_capacity(0);".to_owned();
    for _ in 0..9 {
        body.push_str("b=Bytes.push(b,255);");
    }
    body.push_str(
        "print_i64(Bytes.len(&b)); print_i64(Bytes.capacity(&b)); print_i64(Bytes.get(&b,8));",
    );
    let (output, stats) = execute(&main_program(&body));
    assert_eq!(output, "9\n16\n255\n");
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 2);
    let (output, stats) = execute(
        r#"
        #[noalloc] fn append(b:Bytes)->Bytes ! {panic} {Bytes.push_reserved(b,0)}
        #[noalloc] fn length(b:&Bytes)->i64 ! {} {Bytes.len(b)}
        fn main()->Unit ! {alloc,panic,io} {
            let b=append(Bytes.with_capacity(1)); print_i64(length(&b)); print_i64(Bytes.get(&b,0));
        }
    "#,
    );
    assert_eq!(output, "1\n0\n");
    assert_eq!(stats.buffer_growths, 0);
}

#[test]
fn nested_buffers_and_early_exits_release_every_owner() {
    let (_, stats) = execute(
        r#"
        enum Result<T,E>{Ok(T),Err(E)} enum Pair{Both(Bytes,Box<Bytes>)}
        fn fail()->Result<i64,Bytes> ! {alloc,panic} {Err(Bytes.from("error"))}
        fn pair()->Result<Pair,Bytes> ! {alloc,panic} {
            let unused=Bytes.from("local");
            Ok(Pair.Both(Bytes.from("pending"),Box.new({fail()?;Bytes.from("unreachable")})))
        }
        fn main()->Unit ! {alloc,panic} {
            let result=pair();
            let b=Box.new(Bytes.from("boxed")); let value=Box.take(b);
            let mut buffer=Bytes.from("old"); buffer=Bytes.from("replacement");
        }
    "#,
    );
    assert_eq!(stats.allocations, 7);
}

#[test]
fn buffers_are_affine_and_borrows_cannot_be_invalidated() {
    rejects(
        &main_program(r#"let b=Bytes.from("x");let c=b;drop(b);"#),
        "move",
    );
    rejects(
        &main_program(r#"let b=Bytes.from("x");drop(b);Bytes.len(&b);"#),
        "move",
    );
    rejects(
        r#"
        fn f(a:&Bytes,b:Bytes)->Unit ! {} {}
        fn main()->Unit ! {alloc,panic} {let b=Bytes.from("x");f(&b,Bytes.push(b,1));}
    "#,
        "while it is borrowed",
    );
    // A stored shared owner reference is a lexical capability, and a shared
    // owner reference may be returned from a reference parameter.
    execute(&main_program(
        r#"let b=Bytes.from("x"); let r=&b; print_i64(Bytes.len(r));"#,
    ));
    check("fn f<'a>(b:&'a Bytes)->&'a Bytes ! {} {b}").unwrap();
    rejects(
        &main_program(r#"let b=Bytes.from("x");Box.read(&b);"#),
        "requires an immutable &Box",
    );
    rejects(
        &main_program(r#"let b=Box.new(Bytes.from("x"));Box.read(&b);"#),
        "cannot copy an owned payload",
    );
    assert!(check(&main_program(r#"Bytes.from("x")==Bytes.from("x");"#)).is_err());
}

#[test]
fn literal_construction_and_effect_contracts_are_checked() {
    for body in ["Bytes.from();", "Bytes.from(1);", r#"Bytes.from("a","b");"#] {
        rejects(&main_program(body), "exactly one string literal");
    }
    for body in [
        r#"Bytes.from("x")"#,
        "Bytes.with_capacity(1)",
        "Bytes.copy(b)",
        "Bytes.push(Bytes.with_capacity(0),1)",
    ] {
        assert!(
            check(&format!(
                "#[noalloc] fn f(b:&Bytes)->Bytes ! {{panic}} {{{body}}}"
            ))
            .is_err()
        );
    }
    assert!(check("fn f(b:&Bytes)->i64 ! {} {Bytes.get(b,0)}").is_err());
    assert!(check("fn f(b:Bytes)->Bytes ! {} {Bytes.push_reserved(b,1)}").is_err());
    assert!(check("#[noalloc] fn f(b:&Bytes)->i64 ! {} {Bytes.capacity(b)}").is_ok());
}

#[test]
fn reference_checks_bounds_byte_range_and_capacity() {
    for body in [
        "Bytes.with_capacity(-1);",
        r#"let b=Bytes.from("");Bytes.get(&b,0);"#,
        r#"let b=Bytes.from("a");Bytes.get(&b,-1);"#,
        r#"let b=Bytes.from("a");Bytes.get(&b,1);"#,
        "Bytes.push(Bytes.with_capacity(0),-1);",
        "Bytes.push(Bytes.with_capacity(0),256);",
        "Bytes.push_reserved(Bytes.with_capacity(0),1);",
        r#"Bytes.push_reserved(Bytes.from("a"),1);"#,
    ] {
        let error = check(&main_program(body))
            .unwrap()
            .evaluate(&mut Vec::new())
            .unwrap_err();
        assert!(error.message.contains("panic:"), "{error:?}");
    }
    let error = check(&main_program("Bytes.with_capacity(16777217);"))
        .unwrap()
        .evaluate(&mut Vec::new())
        .unwrap_err();
    assert!(error.message.contains("capacity budget"));
}

#[test]
fn expression_parser_handles_precedence_whitespace_and_errors_without_leaks() {
    let example = include_str!("../../../examples/expression-parser.kush");
    for (input, expected) in [
        ("12 + 3 * 10", 42),
        ("2+3*4", 14),
        ("2*3+4", 10),
        (" 42 \t\r\n", 42),
        ("", 0),
        ("1 +", 3),
        ("1 ?", 2),
        ("1+2*3+", 6),
        ("9223372036854775807", i64::MAX),
        ("9223372036854775808", -1),
    ] {
        let source = example.replace(r#""12 + 3 * 10""#, &format!("{input:?}"));
        let (output, _) = execute(&source);
        assert_eq!(output, format!("{expected}\n"), "{input}");
    }
}
