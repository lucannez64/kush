//! FND-HANDLERS-ONE-PARAMS: a declared operation reaches a directly called
//! function as a hidden capability parameter (docs/one-handler-model.md).
//!
//! A function that performs a declared operation it does not handle gets a
//! copy taking the operation's capability after its written parameters.
//! Direct calls under a `handle` (or from another copy) call the copy, which
//! performs through the parameter instead of searching the dynamic stack.
//! Function values still reach the original. Every program runs in the
//! reference evaluator and natively with balanced allocations.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program
        .evaluate_with_stats(&mut Vec::new())
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("implicit-capabilities");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}\n{source}",
            String::from_utf8_lossy(&native.stderr)
        );
    }
}

/// The debug text of the checked function named `name`.
fn function(debug: &str, name: &str) -> String {
    let start = debug
        .find(&format!("Function {{ name: \"{name}\""))
        .unwrap_or_else(|| panic!("no function {name}"));
    let rest = &debug[start + 1..];
    let end = rest
        .find("Function { name: ")
        .map_or(rest.len(), |end| end + 1);
    debug[start..start + end].to_owned()
}

const CALLEES: &str = "effect Ask: i64 -> i64;
    fn leaf(x: i64) -> i64 ! {Ask} { perform Ask(x) + 1 }
    fn middle(x: i64) -> i64 ! {Ask} { leaf(x) * 2 }";

#[test]
fn direct_calls_perform_through_hidden_capabilities() {
    let source = format!(
        "{CALLEES}
         fn main() -> i64 ! {{}} {{
             handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{
                 k(x + 10)
             }} {{ middle(1) }}
         }}"
    );
    agrees(&source, 24);
    let debug = format!("{:?}", check(&source).unwrap());
    for name in ["leaf::capabilities", "middle::capabilities"] {
        let copy = function(&debug, name);
        assert!(!copy.contains("DynamicPerform"), "{copy}");
        assert!(copy.contains("parameter_slots: Some("), "{copy}");
    }
    assert!(function(&debug, "main").contains("Call(Function("));
}

#[test]
fn a_non_tail_handler_resumes_copies_through_their_capability() {
    // Deep handler: the second perform runs under the first activation's
    // resumption; 24 + 26 returns to the second activation (+1000), then
    // to the first (+1000).
    let source = format!(
        "{CALLEES}
         fn main() -> i64 ! {{alloc}} {{
             handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{
                 let r = k(x + 10);
                 r + 1000
             }} {{ middle(1) + middle(2) }}
         }}"
    );
    agrees(&source, 2050);
    let debug = format!("{:?}", check(&source).unwrap());
    assert!(debug.contains("middle::capabilities::resumable"));
    assert!(!function(&debug, "middle::capabilities::resumable").contains("DynamicPerform"));
}

#[test]
fn function_values_still_reach_the_handler() {
    let source = format!(
        "{CALLEES}
         fn main() -> i64 ! {{}} {{
             handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{
                 k(x + 10)
             }} {{
                 let f: fn(i64) -> i64 ! {{Ask}} = leaf;
                 f(1) + middle(2)
             }}
         }}"
    );
    agrees(&source, 38);
}
