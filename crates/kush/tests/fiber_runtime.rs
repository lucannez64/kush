//! The C fiber runtime (FIBER-RUNTIME, docs/tasks-on-handlers.md), driven
//! directly by a C harness: no language surface uses it yet. The harness
//! includes the runtime with `KUSH_NO_MAIN`, plays the compiled program
//! (`kush_entry`) and prints one line per check.
use std::process::Command;

const HARNESS: &str = r#"
#include <fenv.h>
#include RUNTIME_PATH

int64_t kush_entry(void) { return 0; }

static int failures = 0;
static void check(int ok, const char *name) {
    printf("%s %s\n", ok ? "ok" : "FAILED", name);
    if (!ok) failures += 1;
}

/* A body is wrapper(code, env, result): code is a C function taking env. */
typedef void (*Body)(uint64_t env, uint64_t *result);
static void wrapper(uint64_t code, uint64_t env, uint64_t result) {
    ((Body)(uintptr_t)code)(env, (uint64_t *)(uintptr_t)result);
}
static uint64_t start(Body body, uint64_t env) {
    return kush_fiber_new((uint64_t)(uintptr_t)wrapper, (uint64_t)(uintptr_t)body, env, 8);
}

/* Requests 1, 2, 3; each reply is added up and returned. */
static void counter(uint64_t env, uint64_t *result) {
    uint64_t total = env;
    for (uint64_t request = 1; request <= 3; ++request) total += kush_fiber_suspend(request);
    *result = total;
}

static void requests_and_replies(void) {
    uint64_t f = start(counter, 1000);
    uint64_t seen = 0, status = kush_fiber_resume(f, 0);
    while (status == 0) {
        uint64_t request = kush_fiber_request(f);
        seen = seen * 10 + request;
        status = kush_fiber_resume(f, request * 100);
    }
    uint64_t result = *(uint64_t *)(uintptr_t)kush_fiber_result(f);
    kush_fiber_free(f);
    check(seen == 123 && result == 1600, "requests and replies");
}

/* Many fibers in turn, as a scheduler runs them. */
static void stepper(uint64_t env, uint64_t *result) {
    uint64_t total = 0;
    for (uint64_t i = 0; i < env; ++i) total += kush_fiber_suspend(i);
    *result = total;
}

static void round_robin(void) {
    enum { N = 100 };
    uint64_t fibers[N], results = 0;
    int live = N;
    uint64_t allocations = kush_allocations - kush_deallocations;
    for (int i = 0; i < N; ++i) fibers[i] = start(stepper, (uint64_t)i);
    for (int i = 0; live > 0; i = (i + 1) % N) {
        if (fibers[i] == 0) continue;
        if (kush_fiber_resume(fibers[i], 1) == 1) {
            results += *(uint64_t *)(uintptr_t)kush_fiber_result(fibers[i]);
            kush_fiber_free(fibers[i]);
            fibers[i] = 0;
            live -= 1;
        }
    }
    /* Fiber i adds i replies of 1. */
    check(results == (uint64_t)N * (N - 1) / 2, "round robin results");
    check(kush_allocations - kush_deallocations == allocations, "round robin frees everything");
}

/* A fiber resuming another: the inner one's suspension returns to it. */
static void inner(uint64_t env, uint64_t *result) {
    *result = kush_fiber_suspend(env) + 1;
}
static void outer(uint64_t env, uint64_t *result) {
    (void)env;
    uint64_t f = start(inner, 7);
    uint64_t first = kush_fiber_resume(f, 0);
    uint64_t request = kush_fiber_request(f);
    uint64_t mine = kush_fiber_suspend(request * 2);
    uint64_t second = kush_fiber_resume(f, mine);
    *result = first * 1000 + second * 100 + *(uint64_t *)(uintptr_t)kush_fiber_result(f);
    kush_fiber_free(f);
}

static void nested(void) {
    uint64_t f = start(outer, 0);
    uint64_t status = kush_fiber_resume(f, 0);
    uint64_t request = kush_fiber_request(f);
    status = status * 10 + kush_fiber_resume(f, 40);
    uint64_t result = *(uint64_t *)(uintptr_t)kush_fiber_result(f);
    kush_fiber_free(f);
    /* inner suspends (0), finishes (1) with 40 + 1. */
    check(status == 1 && request == 14 && result == 141, "nested fibers");
}

/* Handler chains and rounding modes are per fiber. */
static void handlers_body(uint64_t env, uint64_t *result) {
    (void)env;
    uint64_t mine = (uint64_t)(uintptr_t)kush_handlers();
    fesetround(FE_UPWARD);
    uint64_t again = kush_fiber_suspend(mine);
    *result = (again == 1 && fegetround() == FE_UPWARD
               && (uint64_t)(uintptr_t)kush_handlers() == mine) ? 1 : 0;
}

static void per_fiber_state(void) {
    uint64_t outside = (uint64_t)(uintptr_t)kush_handlers();
    uint64_t f = start(handlers_body, 0);
    kush_fiber_resume(f, 0);
    uint64_t inside = kush_fiber_request(f);
    int rounding = fegetround() == FE_TONEAREST;
    kush_fiber_resume(f, 1);
    uint64_t result = *(uint64_t *)(uintptr_t)kush_fiber_result(f);
    kush_fiber_free(f);
    check(inside != outside && kush_handlers() == (void *)(uintptr_t)outside, "own handler context");
    check(rounding && result == 1, "own rounding mode");
}

/* Discontinue: a fiber that never ran drops its closure environment. */
static int dropped = 0;
static void drop_environment(void *environment) {
    dropped += 1;
    kush_free((uint64_t)(uintptr_t)environment);
}

static void discontinue_new(void) {
    uint64_t *environment = (uint64_t *)(uintptr_t)kush_alloc(16);
    environment[0] = (uint64_t)(uintptr_t)drop_environment;
    uint64_t allocations = kush_allocations - kush_deallocations;
    uint64_t f = start(counter, (uint64_t)(uintptr_t)environment);
    kush_fiber_discontinue(f);
    check(dropped == 1 && kush_allocations - kush_deallocations == allocations - 1,
          "discontinue before start drops the closure");
}

/* Discontinue a suspended fiber: it panics where it waits, and its frames
   clean up as they unwind (here, by testing the panic word as compiled
   code does). */
static int cleaned = 0;
static void cleanup_body(uint64_t env, uint64_t *result) {
    (void)env;
    uint64_t reply = kush_fiber_suspend(5);
    if (*kush_panic_word() == 1) { cleaned += 1; return; }
    *result = reply;
}

static void discontinue_suspended(void) {
    uint64_t allocations = kush_allocations - kush_deallocations;
    uint64_t f = start(cleanup_body, 0);
    kush_fiber_resume(f, 0);
    kush_fiber_discontinue(f);
    check(cleaned == 1 && *kush_panic_word() == 0, "discontinue unwinds the fiber");
    check(kush_allocations - kush_deallocations == allocations, "discontinue frees the fiber");
}

/* A panic that unwinds a fiber is raised again in its resumer. */
static void panicking(uint64_t env, uint64_t *result) {
    (void)env; (void)result;
    KUSH_FAIL_VOID();
}

static void panic_reaches_the_resumer(void) {
    kush_catch_enter();
    uint64_t f = start(panicking, 0);
    uint64_t status = kush_fiber_resume(f, 0);
    int raised = *kush_panic_word() == 1;
    *kush_panic_word() = 0;
    kush_catch_leave();
    KushFiber *fiber = (KushFiber *)(uintptr_t)f;
    fiber->panicked = 0;
    kush_fiber_free(f);
    check(status == 1 && raised, "a panic in a fiber reaches its resumer");
}

/* A fiber suspended in one task while another task runs, and a task
   switch from inside a fiber. */
static uint64_t task_fiber = 0;
static void yielding(uint64_t env, uint64_t *result) {
    uint64_t total = env;
    total += kush_fiber_suspend(1);
    kush_task_yield();
    total += kush_fiber_suspend(2);
    *result = total;
}
static void task_body(uint64_t code, uint64_t env, uint64_t result) {
    (void)code; (void)env;
    uint64_t f = start(yielding, 10);
    uint64_t steps = 0;
    while (kush_fiber_resume(f, 100) == 0) steps += 1;
    *(uint64_t *)(uintptr_t)result = steps * 1000 + *(uint64_t *)(uintptr_t)kush_fiber_result(f);
    kush_fiber_free(f);
}
static void other_task(uint64_t code, uint64_t env, uint64_t result) {
    (void)code; (void)env;
    *(uint64_t *)(uintptr_t)result = 1;
}

static void fibers_in_tasks(void) {
    kush_task_scope_begin();
    uint64_t a = kush_task_spawn((uint64_t)(uintptr_t)task_body, 0, 0, 8, 0, 0);
    uint64_t b = kush_task_spawn((uint64_t)(uintptr_t)other_task, 0, 0, 8, 0, 0);
    uint64_t first = 0, second = 0;
    kush_task_join(a, &first);
    kush_task_join(b, &second);
    kush_task_scope_end();
    check(first == 2210 && second == 1, "fibers inside tasks");
}

/* Suspending with a scope still open from inside the fiber aborts. */
static void open_scope(uint64_t env, uint64_t *result) {
    (void)env; (void)result;
    kush_task_scope_begin();
    kush_fiber_suspend(0);
}

int main(int argc, char **argv) {
    kush_task_init();
    if (argc > 1 && strcmp(argv[1], "open-scope") == 0) {
        uint64_t f = start(open_scope, 0);
        kush_fiber_resume(f, 0);
        return 0;
    }
    requests_and_replies();
    round_robin();
    nested();
    per_fiber_state();
    discontinue_new();
    discontinue_suspended();
    panic_reaches_the_resumer();
    fibers_in_tasks();
    printf("failures %d\n", failures);
    return failures != 0;
}
"#;

fn harness() -> Option<std::path::PathBuf> {
    let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let scratch = std::env::temp_dir().join(format!("kush-fiber-runtime-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    let source = scratch.join("harness.c");
    std::fs::write(&source, HARNESS).unwrap();
    let runtime = concat!(env!("CARGO_MANIFEST_DIR"), "/runtime/kush.c");
    let binary = scratch.join("harness");
    let built = Command::new(&compiler)
        .args(["-std=c11", "-O2", "-D_GNU_SOURCE"])
        .args([
            "-DKUSH_HAS_TASKS=1",
            "-DKUSH_UNWIND=1",
            "-DKUSH_STATS=1",
            "-DKUSH_FUSION_COUNT=0",
            "-DKUSH_NO_MAIN=1",
        ])
        .arg(format!("-DRUNTIME_PATH=\"{runtime}\""))
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .arg("-lm")
        .output();
    match built {
        Ok(output) if output.status.success() => Some(binary),
        Ok(output) => panic!("{}", String::from_utf8_lossy(&output.stderr)),
        Err(_) => None,
    }
}

#[test]
fn fibers_suspend_resume_nest_and_discontinue() {
    let Some(binary) = harness() else {
        return;
    };
    let output = Command::new(&binary).output().unwrap();
    let printed = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{printed}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(printed.contains("failures 0"), "{printed}");
    assert_eq!(printed.matches("ok ").count(), 11, "{printed}");

    // A fiber may not leave a task scope it opened open across a suspension.
    let open = Command::new(&binary).arg("open-scope").output().unwrap();
    assert!(!open.status.success());
    assert!(String::from_utf8_lossy(&open.stderr).contains("panic"));
}
