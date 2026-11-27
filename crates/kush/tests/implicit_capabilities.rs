//! FND-HANDLERS-ONE-PARAMS: a declared operation reaches a directly called
//! function as a hidden capability parameter (docs/one-handler-model.md).
//!
//! A function that performs a declared operation it does not handle gets a
//! copy taking the operation's capability after its written parameters.
//! Direct calls under a `handle` (or from another copy) call the copy, which
//! performs through the parameter instead of searching the dynamic stack. A
//! function value takes the capabilities its arrow's row names from each
//! caller (FND-HANDLERS-ONE-VALUES). Every program runs in the reference
//! evaluator and natively with balanced allocations.
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

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

/// Handles `Ask` by resuming with the payload plus `add`.
fn handle(add: &str, body: &str) -> String {
    format!(
        "handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {{}}) -> i64 ! {{}} {{
             k(x + {add})
         }} {{ {body} }}"
    )
}

#[test]
fn a_function_value_gets_the_handler_active_at_its_call() {
    // Decision D1: `installs` calls `f` under its own handler, so `f`
    // performs there (1000 + 100000), not under `main`'s (+ 1).
    let inner = handle("100000", "f(1000)");
    let outer = handle("1", "installs(leaf) + 0");
    let source = format!(
        "{CALLEES}
         fn installs(f: fn(i64) -> i64 ! {{Ask}}) -> i64 ! {{}} {{ {inner} }}
         fn main() -> i64 ! {{}} {{ {outer} - 101000 }}"
    );
    agrees(&source, 1);
}

#[test]
fn lambdas_perform_through_their_hidden_capability() {
    let body = handle(
        "10",
        "let f = fn(x: i64) -> i64 ! {Ask} { perform Ask(x) * 3 }; f(1) + f(2)",
    );
    let source = format!("{CALLEES}\n fn main() -> i64 ! {{}} {{ {body} }}");
    agrees(&source, 33 + 36);
    let debug = format!("{:?}", check(&source).unwrap());
    let copy = function(&debug, "lambda::capabilities");
    assert!(!copy.contains("DynamicPerform"), "{copy}");
}

#[test]
fn widening_a_row_with_declared_operations_adapts_named_functions() {
    // A function without `Ask` used where the arrow allows it: an adapter
    // takes the capability and drops it.
    let body = handle("10", "apply(double, 4) + apply(leaf, 1)");
    let source = format!(
        "{CALLEES}
         fn double(x: i64) -> i64 ! {{}} {{ x * 2 }}
         fn apply(f: fn(i64) -> i64 ! {{Ask}}, x: i64) -> i64 ! {{Ask}} {{ f(x) }}
         fn main() -> i64 ! {{}} {{ {body} }}"
    );
    agrees(&source, 8 + 12);
    // A function value of unknown origin has no adapter without an
    // environment.
    rejects(
        &format!(
            "{CALLEES}
             fn widen(f: fn(i64) -> i64 ! {{}}) -> i64 ! {{Ask}} {{
                 let g: fn(i64) -> i64 ! {{Ask}} = f;
                 g(1)
             }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "representation-changing conversion of a dynamic pure function value",
    );
}

#[test]
fn trait_object_members_take_the_capabilities_of_their_key() {
    // Only `A` performs; the dispatch passes the capability to both members.
    let body = handle(
        "10",
        "let a: dyn Asker = A { k: 100 };
         let b: dyn Asker = B { u: 0 };
         use_it(&a) + use_it(&b)",
    );
    let source = format!(
        "{CALLEES}
         trait Asker {{ fn ask(self: &Self, x: i64) -> i64 ! {{Ask}}; }}
         struct A {{ k: i64 }}
         struct B {{ u: i64 }}
         impl Asker for A {{ fn ask(self: &Self, x: i64) -> i64 ! {{Ask}} {{ leaf(x) + self.k }} }}
         impl Asker for B {{ fn ask(self: &Self, x: i64) -> i64 ! {{Ask}} {{ x }} }}
         fn use_it(object: &dyn Asker) -> i64 ! {{Ask}} {{ object.ask(1) }}
         fn main() -> i64 ! {{alloc}} {{ {body} }}"
    );
    agrees(&source, 112 + 1);
    let debug = format!("{:?}", check(&source).unwrap());
    assert!(!function(&debug, "ask::capabilities").contains("DynamicPerform"));
}

#[test]
fn a_spawned_task_keeps_each_noncapturing_handler() {
    // Decision D3: the capturing `Log` handler installed inside `Ask`'s
    // handle no longer hides `Ask` from the task (it was a barrier on the
    // dynamic stack, so this panicked).
    let source = "use std.task.TaskExit;
        effect Ask: i64 -> i64;
        effect Log: i64 -> Unit;
        fn main() -> i64 ! {alloc, suspend} {
            let mut logged = 0;
            handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {
                k(x + 10)
            } {
                handle Log: i64 -> Unit with fn(x: i64, k: linear once fn(Unit) -> Unit ! {}) -> Unit ! {} {
                    logged = logged + x;
                    k(())
                } {
                    Task.scope(fn() -> i64 ! {Ask, alloc, suspend} {
                        let t: Task<i64> = Task.spawn(fn() -> i64 ! {Ask, suspend} { perform Ask(1) });
                        match Task.join(t) {
                            TaskExit.Completed(v) => v,
                            TaskExit.Cancelled => 0,
                        }
                    })
                }
            }
        }";
    agrees(source, 11);
}

#[test]
fn task_bodies_capture_the_capabilities_where_the_builtin_is_called() {
    // The scope and spawn bodies are lambdas (the checker requires it): each
    // becomes a copy receiving `Ask`'s capability as a capture, beside the
    // box the spawned body owns.
    let source = "use std.task.TaskExit;
        effect Ask: i64 -> i64;
        fn main() -> i64 ! {alloc, suspend} {
            handle Ask: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {
                k(x + 10)
            } {
                Task.scope(fn() -> i64 ! {Ask, alloc, suspend} {
                    let owned = Box.new(5);
                    let t: Task<i64> = Task.spawn(fn() -> i64 ! {Ask, alloc, suspend} {
                        perform Ask(Box.take(owned))
                    });
                    let mine = perform Ask(1);
                    match Task.join(t) {
                        TaskExit.Completed(v) => v + mine,
                        TaskExit.Cancelled => 0,
                    }
                })
            }
        }";
    agrees(source, 15 + 11);
}
