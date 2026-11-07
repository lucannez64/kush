//! GPU-SUBSET (docs/gpu.md, user-approved 2026-11-07): `#[gpu]` functions,
//! the `GpuBuf<T>` type and its device-side operations. The checker admits a
//! small allowlisted subset (32-bit scalars, `Bool`, records, tuples and
//! payloadless enums, loops, calls to other `#[gpu]` functions) and rejects
//! everything else with a diagnostic. CPU code cannot call `#[gpu]` functions;
//! `Gpu.run` (GPU-SCOPE) will be the only way in.
use kush::executable::check;

fn accepts(source: &str) {
    if let Err(error) = check(source) {
        panic!("{error:?}\n{source}");
    }
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

/// A `#[gpu]` function plus a trivial CPU `main`.
fn program(gpu: &str) -> String {
    format!("{gpu}\nfn main() -> i64 ! {{}} {{ 0 }}\n")
}

const SAXPY: &str = "
#[gpu]
fn saxpy(id: u32, a: f32, x: &GpuBuf<f32>, y: &mut GpuBuf<f32>) -> Unit ! {panic} {
    GpuBuf.set(y, id, a * GpuBuf.get(x, id) + GpuBuf.get(y, id));
}
";

#[test]
fn saxpy_is_accepted() {
    accepts(&program(SAXPY));
}

#[test]
fn records_enums_loops_and_helpers_are_accepted() {
    accepts(&program(
        "
struct Point { x: f32, y: f32 }
enum Mode { Add, Scale }

#[gpu]
fn combine(mode: Mode, p: Point) -> f32 ! {panic} {
    match mode {
        Mode.Add => p.x + p.y,
        Mode.Scale => p.x * p.y,
    }
}

#[gpu]
fn kernel(id: u32, n: i32, input: &GpuBuf<f32>, out: &mut GpuBuf<f32>) -> Unit ! {panic} {
    let mut acc: f32 = 0.0;
    let mut i: i32 = 0;
    while i < n {
        acc = acc + combine(Mode.Add, Point { x: GpuBuf.get(input, i), y: 1.0 });
        i = i + 1;
    }
    let (lo, hi) = (acc, acc * 2.0);
    if GpuBuf.len(out) > id { GpuBuf.set(out, id, lo + hi); }
}
",
    ));
}

#[test]
fn wrapping_integer_builtins_are_accepted() {
    accepts(&program(
        "
#[gpu]
fn hash(id: u32, out: &mut GpuBuf<u32>) -> Unit ! {panic} {
    let x: u32 = Int.wrapping_mul(id, 2654435761);
    GpuBuf.set(out, id, x);
}
",
    ));
}

#[test]
fn programs_with_gpu_functions_still_run_on_the_cpu() {
    let source = format!("{SAXPY}\nfn main() -> i64 ! {{}} {{ 7 }}\n");
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    assert_eq!(program.evaluate_with_stats(&mut output).unwrap().0, 7);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("gpu-subset");
        kush::native::build(&program, &binary).unwrap();
        let status = std::process::Command::new(&binary).status().unwrap();
        assert_eq!(status.code(), Some(7));
    }
}

#[test]
fn buffer_element_types_are_32_bit() {
    rejects(
        &program("#[gpu] fn f(id: u32, b: &GpuBuf<i64>) -> Unit ! {panic} { }"),
        "a GPU buffer holds i32, u32 or f32 elements, found i64",
    );
    rejects(
        &program("#[gpu] fn f(id: u32, b: &GpuBuf<Bool>) -> Unit ! {panic} { }"),
        "a GPU buffer holds i32, u32 or f32 elements",
    );
}

#[test]
fn sixty_four_bit_values_are_rejected() {
    rejects(
        &program("#[gpu] fn f(x: i64) -> i64 ! {panic} { x }"),
        "#[gpu] function 'f' cannot use a value of type i64",
    );
    rejects(
        &program("#[gpu] fn f(x: f64) -> f32 ! {panic} { 1.0 }"),
        "cannot use a value of type f64",
    );
}

#[test]
fn owning_and_payload_values_are_rejected() {
    rejects(
        &program("#[gpu] fn f(b: Box<i32>) -> i32 ! {panic} { 0 }"),
        "cannot use a value of type Box<i32>",
    );
    rejects(
        &program(
            "enum Shape { Dot, Circle(f32) }
             #[gpu] fn f(s: Shape) -> f32 ! {panic} { 0.0 }",
        ),
        "cannot use a value of type Shape",
    );
    rejects(
        &program("#[gpu] fn f(v: &[i32]) -> i32 ! {panic} { 0 }"),
        "cannot use a value of type &[i32]",
    );
}

#[test]
fn effects_other_than_panic_are_rejected() {
    rejects(
        &program("#[gpu] fn f(x: i32) -> i32 ! {io, panic} { x }"),
        "may only declare the panic effect",
    );
    rejects(
        &program("#[gpu] fn f(x: i32) -> i32 ! {alloc} { x }"),
        "may only declare the panic effect",
    );
}

#[test]
fn generic_and_entry_point_gpu_functions_are_rejected() {
    rejects(
        &program("#[gpu] fn f<T: Type>(x: T) -> T ! {} { x }"),
        "cannot be generic",
    );
    rejects(
        "#[gpu] fn main() -> i32 ! {} { 0 }",
        "cannot be the program entry point",
    );
    rejects(
        &program("#[gpu] #[test] fn f() -> Unit ! {} { }"),
        "cannot also be a #[test]",
    );
}

#[test]
fn gpu_code_calls_only_gpu_functions_without_recursion() {
    rejects(
        &program(
            "fn cpu(x: i32) -> i32 ! {} { x }
             #[gpu] fn f(x: i32) -> i32 ! {panic} { cpu(x) }",
        ),
        "can only call other #[gpu] functions, not 'cpu'",
    );
    rejects(
        &program("#[gpu] fn f(x: i32) -> i32 ! {panic} { if x > 0 { f(x - 1) } else { 0 } }"),
        "is recursive through 'f'",
    );
    rejects(
        &program(
            "#[gpu] fn f(x: i32) -> i32 ! {panic} { if x > 0 { g(x - 1) } else { 0 } }
             #[gpu] fn g(x: i32) -> i32 ! {panic} { f(x) }",
        ),
        "GPU code has no recursion",
    );
}

#[test]
fn buffers_cannot_be_rebound_or_used_on_the_cpu() {
    rejects(
        &program(
            "#[gpu] fn f(id: u32, y: &mut GpuBuf<f32>) -> Unit ! {panic} { let z = y; GpuBuf.set(z, id, 1.0); }",
        ),
        "cannot use a value of type &mut GpuBuf<f32>",
    );
    rejects(
        "fn cpu(b: &GpuBuf<f32>) -> u32 ! {panic} { GpuBuf.len(b) }
         fn main() -> i64 ! {} { 0 }",
        "GpuBuf.len, GpuBuf.get and GpuBuf.set run only inside #[gpu] functions",
    );
}

#[test]
fn closures_and_text_are_rejected() {
    rejects(
        &program(
            "#[gpu] fn f(x: i32) -> i32 ! {panic} { let g = fn(y: i32) -> i32 ! {panic} { y + 1 }; g(x) }",
        ),
        "#[gpu] function 'f'",
    );
    rejects(
        &program("#[gpu] fn f(x: i32) -> Unit ! {alloc, panic} { let s = \"hi\"; }"),
        "may only declare the panic effect",
    );
}

#[test]
fn panics_and_unwrapping_buffer_reads_are_allowed() {
    accepts(&program(
        "#[gpu]
         fn f(id: u32, x: &GpuBuf<i32>, y: &mut GpuBuf<i32>) -> Unit ! {panic} {
             let v = GpuBuf.get(x, id);
             if v < 0 { panic(); }
             GpuBuf.set(y, id, v / 2);
         }",
    ));
}

#[test]
fn nan_tests_and_function_values_are_rejected() {
    rejects(
        &program("#[gpu] fn f(x: f32) -> Bool ! {} { Float.is_nan(x) }"),
        "cannot test for NaN or infinity",
    );
    rejects(
        &program(
            "#[gpu] fn g(x: i32) -> i32 ! {} { x }
             #[gpu] fn f(x: i32) -> i32 ! {} { let h = g; h(x) }",
        ),
        "cannot use a value of type fn(i32) -> i32",
    );
}

#[test]
fn buffers_are_used_only_through_gpubuf_operations() {
    rejects(
        &program(
            "#[gpu] fn g(b: &GpuBuf<f32>) -> u32 ! {panic} { GpuBuf.len(b) }
             #[gpu] fn f(id: u32, b: &GpuBuf<f32>) -> u32 ! {panic} { g(b) }",
        ),
        "can only use a buffer as the first argument of GpuBuf.len, GpuBuf.get or GpuBuf.set",
    );
    rejects(
        &program(
            "#[gpu] fn f(id: u32, b: &GpuBuf<f32>) -> Unit ! {panic} { GpuBuf.set(b, id, 1.0); }",
        ),
        "GpuBuf.set requires a read-write buffer '&mut GpuBuf<T>'",
    );
    rejects(
        &program("#[gpu] fn f(id: u32, b: &GpuBuf<f32>) -> f32 ! {panic} { GpuBuf.get(b, 1.5) }"),
        "",
    );
}

#[test]
fn buffer_indices_are_u32_or_i32() {
    rejects(
        &program(
            "#[gpu] fn f(id: u32, b: &GpuBuf<f32>) -> f32 ! {panic} { let i: Bool = true; GpuBuf.get(b, i) }",
        ),
        "a GPU buffer index is u32 or i32, found Bool",
    );
}

#[test]
fn cpu_code_cannot_call_or_take_gpu_functions() {
    rejects(
        "#[gpu] fn g(x: i32) -> i32 ! {} { x }
         fn main() -> i64 ! {} { let y: i32 = g(1); 0 }",
        "a #[gpu] function runs only on the GPU; CPU code cannot call it directly",
    );
    rejects(
        "#[gpu] fn g(x: i32) -> i32 ! {} { x }
         fn main() -> i64 ! {} { let h: fn(i32) -> i32 ! {} = g; 0 }",
        "a #[gpu] function cannot be used as a CPU function value",
    );
}

#[test]
fn text_and_io_are_rejected() {
    rejects(
        &program("#[gpu] fn f(x: i32) -> Unit ! {io, panic} { print_int(x); }"),
        "may only declare the panic effect",
    );
}
