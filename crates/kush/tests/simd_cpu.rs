//! SIMD-CPU: CPU features as capability tokens in `std.cpu`.
use kush::executable::check;

const PROBE: &str = "use std.cpu;
     use std.option.Option;
     fn bit<T>(token: Option<T>) -> i64 ! {} {
         match token { Option.Some(_) => 1, Option.None => 0 }
     }
     fn features() -> i64 ! {panic} {
         bit(cpu.ssse3()) + 2 * bit(cpu.sse41()) + 4 * bit(cpu.avx2()) + 8 * bit(cpu.sha())
     }
     fn main() -> i64 ! {io, panic} { print_i64(features()); 0 }";

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, _) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str, disable: Option<&str>) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("cpu");
    kush::native::build(&program, &binary).unwrap();
    let mut command = std::process::Command::new(&binary);
    command.env_remove("KUSH_CPU_DISABLE");
    if let Some(disable) = disable {
        command.env("KUSH_CPU_DISABLE", disable);
    }
    let output = command.output().unwrap();
    assert_eq!(output.status.code(), Some(0));
    String::from_utf8(output.stdout).unwrap()
}

/// The bits the host's /proc/cpuinfo flags predict.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn expected_from_cpuinfo() -> i64 {
    let info = std::fs::read_to_string("/proc/cpuinfo").unwrap();
    let flags: Vec<&str> = info
        .lines()
        .find(|line| line.starts_with("flags"))
        .unwrap()
        .split_whitespace()
        .collect();
    let has = |name: &str| flags.contains(&name);
    let mut bits = 0;
    if has("ssse3") {
        bits |= 1;
    }
    if has("sse4_1") {
        bits |= 2;
    }
    if has("avx2") {
        bits |= 4;
    }
    if has("sha_ni") && has("ssse3") && has("sse4_1") {
        bits |= 8;
    }
    bits
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_detection_matches_the_cpu_and_can_be_disabled() {
    let expected = expected_from_cpuinfo();
    assert_eq!(native(PROBE, None), format!("{expected}\n"));
    assert_eq!(native(PROBE, Some("sha")), format!("{}\n", expected & !8));
    assert_eq!(
        native(PROBE, Some("avx2,ssse3")),
        format!("{}\n", expected & !4 & !1 & !8)
    );
}

#[test]
fn the_evaluator_reports_every_feature() {
    // It runs every intrinsic in software (unless KUSH_CPU_DISABLE is set in
    // the test process, which the suite never does).
    if std::env::var_os("KUSH_CPU_DISABLE").is_none() {
        assert_eq!(reference(PROBE), "15\n");
    }
}

#[test]
fn detection_needs_no_effect() {
    // `cpu.sha()` is called from a function with an empty effect row.
    check(
        "use std.cpu;
         use std.option.Option;
         fn fast() -> Bool ! {} { match cpu.sha() { Option.Some(_) => true, Option.None => false } }
         fn main() -> i64 ! {} { if fast() { 1 } else { 0 } }",
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
}

#[test]
fn tokens_are_copyable_and_cannot_be_forged() {
    reference(
        "use std.cpu;
         use std.option.Option;
         fn needs(token: &cpu.Sha) -> i64 ! {} { 1 }
         fn main() -> i64 ! {panic} {
             match cpu.sha() {
                 Option.Some(sha) => { let copy = sha; needs(&sha) + needs(&copy) - 2 },
                 Option.None => 0,
             }
         }",
    );
    let rejects = |source: &str, fragment: &str| match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(error.message.contains(fragment), "{error:?}"),
    };
    rejects(
        "use std.cpu;
         fn main() -> i64 ! {} { let forged = cpu.Sha { held: true }; 0 }",
        "held",
    );
    // The io exception is only for the runtime's own detection stub.
    rejects(
        "foreign \"my_pure\" fn pure() -> i64 ! {};
         fn main() -> i64 ! {} { 0 }",
        "requires the 'io' effect",
    );
}

/// SIMD-REVIEW: a root file cannot take a std module's path. Named
/// `std.cpu`, it would be what the real `std.x86` imports, so it could forge
/// `cpu.Sha`; named `std.x86`, its functions would be taken for the SHA
/// intrinsics.
#[test]
fn a_root_module_cannot_stand_in_for_std() {
    let rejects = |source: &str| match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error
                .message
                .contains("reserved for the Kush standard library"),
            "{error:?}"
        ),
    };
    rejects(
        "module std.cpu;
         use std.x86;
         use std.simd.u32x4;
         pub struct Sha { pub held: Bool }
         fn main() -> i64 ! {} {
             let sha = Sha { held: true };
             let v = x86.sha256msg1(&sha, u32x4.zero(), u32x4.zero());
             Int.convert(u32x4.lane(v, 0, _))
         }",
    );
    rejects(
        "module std.x86;
         pub fn sha256msg1(a: i64, b: i64) -> i64 ! {panic} { a + b }
         fn main() -> i64 ! {panic} { sha256msg1(1, 2) }",
    );
    rejects("module std; fn main() -> i64 ! {} { 0 }");
}
