//! FIELD-PRIVACY (user-approved breaking change, 2026-11-06): a struct field
//! is private to the module that declares the struct unless it is marked
//! `pub`. Outside that module a private field cannot be read, written,
//! matched, converted, or supplied in a struct literal.

fn project(module: &str, main: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!(
        "kush-field-privacy-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(root.join("demo").join("permit.kush"), module).unwrap();
    std::fs::write(root.join("main.kush"), main).unwrap();
    root
}

const MODULE: &str = r#"module demo.permit;
pub struct Permit { pub label: i64, revision: i64 }
pub fn mint(revision: i64) -> Permit ! {} { Permit { label: 7, revision: revision } }
pub fn revision(permit: &Permit) -> i64 ! {} { permit.revision }
pub fn relabel(permit: Permit, label: i64) -> Permit ! {} { Permit { label: label, ..permit } }
pub fn bump(permit: Permit) -> Permit ! {panic} {
    let Permit { label, revision } = permit;
    Permit { label: label, revision: revision + 1 }
}
"#;

fn run(main: &str) -> Result<(i64, String), String> {
    let root = project(MODULE, main);
    let loaded = kush::program::load_path(&root.join("main.kush")).unwrap();
    let result = kush::executable::check_program(&loaded).map_err(|error| error.message);
    let _ = std::fs::remove_dir_all(&root);
    let program = result?;
    let mut output = Vec::new();
    let (value, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("field-privacy");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(native.status.code(), Some((value as u64 & 255) as i32));
        assert_eq!(native.stdout, output);
    }
    Ok((value, String::from_utf8(output).unwrap()))
}

#[test]
fn public_fields_and_module_functions_are_usable() {
    let (value, _) = run(r#"use demo.permit;
        use demo.permit.Permit;
        fn main() -> i64 ! {panic} {
            let p = permit.bump(permit.mint(3));
            let label = p.label;
            let current = permit.revision(&p);
            let Permit { label: again } = p;
            current * 10 + label + again - 7
        }
        "#)
    .unwrap();
    assert_eq!(value, 47);
}

#[test]
fn private_fields_are_rejected_outside_their_module() {
    for (body, what) in [
        ("let p = permit.mint(3); p.revision", "read"),
        (
            "let p = Permit { label: 1, revision: 9 }; 0",
            "struct literal",
        ),
        ("let mut p = permit.mint(3); p.revision = 9; 0", "write"),
        (
            "let Permit { label, revision } = permit.mint(3); revision",
            "pattern",
        ),
        (
            "let p = permit.mint(3); let r = &p; r.revision",
            "read through a reference",
        ),
    ] {
        let main = format!(
            "use demo.permit;
            use demo.permit.Permit;
            fn main() -> i64 ! {{panic}} {{ {body} }}
            "
        );
        let error = run(&main).expect_err(what);
        assert!(
            error.contains("field 'revision' of 'Permit' is private to its module"),
            "{what}: {error}"
        );
    }
}

/// STRUCT-UPDATE: an update needs every field visible, like a full literal;
/// inside the module it is fine.
#[test]
fn struct_update_needs_visible_fields() {
    let (value, _) = run(r#"use demo.permit;
        fn main() -> i64 ! {panic} {
            let p = permit.relabel(permit.mint(3), 9);
            p.label * 10 + permit.revision(&p)
        }
        "#)
    .unwrap();
    assert_eq!(value, 93);
    let error = run(r#"use demo.permit;
        use demo.permit.Permit;
        fn main() -> i64 ! {panic} {
            let p = Permit { label: 1, ..permit.mint(3) };
            p.label
        }
        "#)
    .unwrap_err();
    assert!(error.contains("private"), "{error}");
}
