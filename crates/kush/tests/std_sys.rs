//! STD-SYS-FOREIGN: `std.sys` declares the runtime's one-syscall stubs as
//! foreign functions. Only std may declare or call `kush_sys_*` symbols.

use kush::executable;

fn checked(source: &str) -> Result<executable::Executable, String> {
    let program = kush::program::load_source("<std-sys-test>", source).unwrap();
    executable::check_program(&program).map_err(|error| program.sources.render(&error))
}

#[test]
fn programs_cannot_declare_runtime_symbols() {
    let error = checked(
        "use std.result.Result;\n\
         foreign \"kush_sys_close\" fn close(fd: i64) -> Result<Unit, i64> ! {io};\n\
         fn main() -> i64 ! {io} { 0 }",
    )
    .unwrap_err();
    assert!(
        error.contains("reserved for the Kush standard library"),
        "{error}"
    );
}

#[test]
fn a_root_module_named_std_is_not_std() {
    let error = checked(
        "module std.evil;\n\
         use std.result.Result;\n\
         foreign \"kush_sys_close\" fn close(fd: i64) -> Result<Unit, i64> ! {io};\n\
         fn main() -> i64 ! {io} { 0 }",
    )
    .unwrap_err();
    assert!(
        error.contains("reserved for the Kush standard library"),
        "{error}"
    );
}

#[test]
fn programs_cannot_call_std_sys() {
    let error = checked(
        "use std.result.Result;\n\
         use std.sys;\n\
         fn main() -> i64 ! {io} { match sys.close(99) { Result.Ok(_) => 0, Result.Err(e) => e } }",
    )
    .unwrap_err();
    assert!(error.contains("std-internal system call"), "{error}");
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn std_sys_links_against_the_runtime() {
    let program = checked("use std.sys;\nfn main() -> i64 ! {io} { sys.O_CREAT() }").unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("sys-program");
    kush::native::build(&program, &binary).unwrap();
    let status = std::process::Command::new(&binary).status().unwrap();
    assert_eq!(status.code(), Some(64));
}
