use kush::executable::check;
fn rejects(source: &str, message: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message:?}, got {error:?}"
    );
}
fn balanced(source: &str) -> (i64, String, usize) {
    let p = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = p.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (
        result,
        String::from_utf8(output).unwrap(),
        stats.allocations,
    )
}
#[test]
fn owning_list_moves_borrows_and_deterministic_cleanup() {
    let result = balanced(include_str!("../../../examples/ownership.kush"));
    assert_eq!(result, (0, "42\n42\n6\n".into(), 6));
}
#[test]
fn duplicate_uses_and_conditional_moves_are_rejected() {
    for source in [
        "fn main() -> Unit ! {alloc,panic} { let b=Box.new(1); let c=b; drop(b); }",
        "fn main() -> Unit ! {alloc,panic} { let b=Box.new(1); drop(b); Box.read(&b); }",
        "fn f(b: Box<i64>) -> Unit ! {} { drop(b); drop(b); }",
        "enum E { A(Box<i64>) } fn f(e:E) -> Unit ! {} { let x=e; drop(e); }",
        "fn f(b:Box<i64>,c:Bool)->i64 ! {} { if c { drop(b); } Box.read(&b) }",
        "fn f(b:Box<i64>,c:Bool)->Unit ! {} { c && { drop(b); true }; drop(b); }",
    ] {
        let error = check(source).unwrap_err();
        assert!(
            error.message.contains("move") || error.message.contains("moved"),
            "{error:?}"
        );
    }
}
#[test]
fn borrows_cannot_outlive_or_be_invalidated_by_later_arguments() {
    let prefix = "fn f(a:&Box<i64>,b:i64)->i64 ! {} { Box.read(a) } ";
    rejects(
        &format!(
            "{prefix} fn main()->i64 ! {{alloc,panic}} {{ let b=Box.new(1); f(&b,Box.take(b)) }}"
        ),
        "while it is borrowed",
    );
    rejects(
        &format!(
            "{prefix} fn main()->i64 ! {{alloc,panic}} {{ let b=Box.new(1); let c=Box.new(2); f(if true {{ &b }} else {{ &c }},Box.take(b)) }}"
        ),
        "while it is borrowed",
    );
    rejects(
        &format!("{prefix} fn main()->i64 ! {{alloc,panic}} {{ f({{let b=Box.new(1); &b}},0) }}"),
        "escapes",
    );
    rejects(
        "fn main()->Unit ! {alloc,panic} {let b=Box.new(1);let r=&b;drop(Box.take(b));}",
        "while it is borrowed",
    );
    rejects(
        "enum E<T>{A(T)} fn f(e:E<&Box<i64>>)->Unit ! {} {}",
        "cannot store borrowed",
    );
    rejects(
        "fn f(b:Box<Box<i64>>)->Box<i64> ! {} {Box.read(&b)}",
        "cannot copy an owned payload",
    );
}
#[test]
fn guards_cannot_consume_owners_even_inside_nested_matches() {
    let prefix = "enum E{A(Box<i64>)} ";
    rejects(
        &format!(
            "{prefix} fn f(e:E)->i64 ! {{}} {{match e {{ E.A(b) if {{drop(b);false}} =>0, _=>1 }} }}"
        ),
        "guards cannot consume",
    );
    rejects(
        &format!(
            "{prefix} fn f(e:E)->i64 ! {{}} {{match e {{ E.A(b) if match true {{ _ if true => {{drop(b);false}}, _=>false }} =>0, _=>1 }} }}"
        ),
        "guards cannot consume",
    );
    rejects(
        &format!(
            "{prefix} fn use_ref(r:&Box<i64>)->i64 ! {{}} {{Box.read(r)}} fn f(e:E)->i64 ! {{}} {{use_ref(match e {{E.A(b)=>&b}})}}"
        ),
        "escapes",
    );
}
#[test]
fn reinitialization_moves_overwrite_and_box_take_transfer_ownership() {
    assert_eq!(
        balanced(
            "fn main()->i64 ! {alloc,panic} {
        let mut b=Box.new(1); let c=b; b=Box.new(2); b=b;
        let outer=Box.new(c); let inner=Box.take(outer); drop(inner);
        Box.take(b)
    }"
        ),
        (2, "".into(), 3)
    );
    balanced(
        "fn f(b:Box<i64>,c:Bool)->i64 ! {} {if c{return Box.take(b);} Box.read(&b)}
        fn main()->i64 ! {alloc,panic} {f(Box.new(2),false)}",
    );
}
#[test]
fn early_exits_release_incomplete_payloads_arguments_and_result_errors() {
    let prefix = "enum Result<T,E>{Ok(T),Err(E)} enum Pair{Both(Box<i64>,i64)}
        fn fail()->Result<i64,Box<i64>> ! {alloc,panic} {Err(Box.new(7))}
        fn pair(a:Box<i64>,b:i64)->i64 ! {} {Box.take(a)} ";
    balanced(&format!(
        "{prefix} fn make()->Result<i64,Box<i64>> ! {{alloc,panic}} {{
        let local=Box.new(8); let e=Pair.Both(Box.new(1),fail()?); Ok(0)
    }} fn main()->Unit ! {{alloc,panic}} {{drop(make());}}"
    ));
    balanced(&format!(
        "{prefix} fn make()->Result<i64,Box<i64>> ! {{alloc,panic}} {{
        let n=pair(Box.new(1),fail()?); Ok(n)
    }} fn main()->Unit ! {{alloc,panic}} {{drop(make());}}"
    ));
    balanced("enum E{Pair(Box<i64>,i64)} fn f()->i64 ! {alloc,panic} {let e=E.Pair(Box.new(1),return 9);}
        fn main()->i64 ! {alloc,panic} {f()}");
}
#[test]
fn ignored_and_unused_pattern_resources_drop_after_guard_selection() {
    let p = "enum E{A(Box<i64>,Box<i64>),B(Box<i64>)}
        fn f(e:E)->i64 ! {} {match e {
            E.A(b,_) | E.B(b) if Box.read(&b)<0 => Box.take(b),
            E.A(_,b) | E.B(b) => Box.read(&b),
        }} fn main()->i64 ! {alloc,panic} {f(E.A(Box.new(1),Box.new(2)))}";
    assert_eq!(balanced(p).0, 2);
}
#[test]
fn allocation_effect_and_noalloc_contracts_are_checked() {
    rejects("fn main()->Unit ! {} {let b=Box.new(1);}", "alloc, panic");
    rejects("#[noalloc] fn f()->Unit ! {alloc} {}", "noalloc contract");
    rejects(
        "#[noalloc] fn f()->Unit ! {panic} {let b=Box.new(1);}",
        "requires effects {alloc}",
    );
    check("#[noalloc] #[nosuspend] fn f(b:Box<i64>)->i64 ! {} {Box.take(b)}").unwrap();
    rejects("fn f(b:&mut Box<i64>)->Unit ! {} {}", "immutable &Box");
}
