//! EFF-CAP-RESUME-MULTISHOT: multishot resumption tokens (`multi fn`) and
//! multishot capabilities across calls (docs/multishot-capabilities.md).
//!
//! A `multi fn(R) -> R` token is copyable and second-class; its environment
//! lives on the task's continuation stack and is released when the token
//! call or `handle` that pushed it returns.

use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

/// A multishot handler whose body is `{body}`, around a handled body that
/// performs `Choose` once and adds the live value `base`.
fn handler_body(helpers: &str, body: &str) -> String {
    format!(
        "{helpers}
         fn main() -> i64 ! {{alloc, panic}} {{
             let base = 10;
             handle Choose: i64 -> i64 with fn(
                 n: i64,
                 resume: multi fn(i64) -> i64 ! {{}},
             ) -> i64 ! {{alloc, panic}} {{ {body} }} {{
                 let c = perform Choose(2);
                 c + base
             }}
         }}"
    )
}

// ---------------------------------------------------------------------------
// MS-TYPE: the token type and its second-class rules
// ---------------------------------------------------------------------------

#[test]
fn a_token_cannot_be_returned() {
    rejects(
        &handler_body(
            "fn pass(r: multi fn(i64) -> i64 ! {}) -> multi fn(i64) -> i64 ! {} ! {} { r }",
            "resume(0)",
        ),
        "a function cannot return it",
    );
}

#[test]
fn a_token_cannot_be_stored() {
    rejects(
        &handler_body(
            "struct Holder { r: multi fn(i64) -> i64 ! {} }",
            "let h = Holder { r: resume }; resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
    rejects(
        &handler_body(
            "enum Maybe { None, Some(multi fn(i64) -> i64 ! {}) }",
            "let m = Maybe.Some(resume); resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
    rejects(
        &handler_body(
            "",
            "let mut v: Vec<multi fn(i64) -> i64 ! {}> = Vec.new(); resume(0)",
        ),
        "it cannot be stored in a value of type",
    );
}

#[test]
fn a_token_cannot_be_captured() {
    rejects(
        &handler_body(
            "",
            "let again = fn(x: i64) -> i64 ! {} { resume(x) }; again(0)",
        ),
        "a closure cannot capture it",
    );
}

#[test]
fn a_token_is_not_a_function_pointer() {
    rejects(
        &handler_body(
            "fn apply(f: fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }",
            "apply(resume, 0)",
        ),
        "found multi fn(i64) -> i64 ! {}",
    );
    rejects(
        &handler_body(
            "fn apply(f: once fn(i64) -> i64 ! {}, x: i64) -> i64 ! {} { f(x) }",
            "apply(resume, 0)",
        ),
        "found multi fn(i64) -> i64 ! {}",
    );
}

#[test]
fn a_handler_names_the_token_forms() {
    rejects(
        "fn main() -> i64 ! {panic} {
             handle Op: i64 -> i64 with fn(
                 x: i64,
                 resume: multi fn(i64) -> Bool ! {},
             ) -> i64 ! {panic} { 0 } { perform Op(1) }
         }",
        "'multi fn(i64) -> i64'",
    );
}

#[test]
fn multi_stays_an_ordinary_name() {
    // `multi` is contextual: only `multi fn` and `cap multi Op` are special.
    let program = check(
        "fn multi(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
             let m = multi(1);
             let multi = 2;
             multi + m
         }",
    );
    assert!(program.is_ok(), "{:?}", program.err());
}
