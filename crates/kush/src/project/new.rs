//! `kush new` project scaffolding.
use super::{Failure, manifest};
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone)]
pub struct CreatedProject {
    pub directory: PathBuf,
    pub name: String,
}

pub fn create(directory: &Path, requested_name: Option<&str>) -> Result<CreatedProject, Failure> {
    let name = match requested_name {
        Some(name) => {
            manifest::validate_package_name(name)?;
            name.to_owned()
        }
        None => derive_name(directory),
    };
    manifest::validate_package_name(&name)?;
    if directory.exists() {
        return Err(Failure::new(format!(
            "cannot create {}: the path already exists",
            directory.display()
        )));
    }
    fs::create_dir_all(directory).map_err(|e| {
        Failure::new(format!(
            "cannot create project directory {}: {e}",
            directory.display()
        ))
    })?;
    let result = write_files(directory, &name);
    if result.is_err() {
        let _ = fs::remove_dir_all(directory);
    }
    result?;
    Ok(CreatedProject {
        directory: directory.to_path_buf(),
        name,
    })
}

fn write_files(directory: &Path, name: &str) -> Result<(), Failure> {
    write(
        &directory.join("Kush.toml"),
        &format!(
            "[package]\n\
             name = \"{name}\"\n\
             version = \"0.1.0\"\n\
             entry = \"src/main.kush\"\n\
             test = \"tests/main.kush\"\n\
             \n\
             # Local path dependencies use a directory containing its own Kush.toml:\n\
             # [dependencies]\n\
             # helper = {{ path = \"../helper\" }}\n\
             \n\
             # Native libraries and Rust staticlib adapters:\n\
             # [native]\n\
             # libraries = [\"m\"]\n\
             # library-paths = [\"native/lib\"]\n\
             # cargo-manifests = [\"adapters/bridge/Cargo.toml\"]\n"
        ),
    )?;
    write(
        &directory.join("src/main.kush"),
        &format!(
            "module {name};\n\
             \n\
             fn main() -> Unit ! {{io, panic}} {{\n\
             \x20   print_i64(42);\n\
             }}\n"
        ),
    )?;
    write(
        &directory.join("tests/main.kush"),
        &format!(
            "module {name}.tests.main;\n\
             \n\
             use std.test;\n\
             \n\
             #[test]\n\
             fn arithmetic_works() -> Unit ! {{panic}} {{\n\
             \x20   test.is_true(2 + 2 == 4);\n\
             }}\n\
             \n\
             #[test]\n\
             fn multiplication_works() -> Unit ! {{io, panic}} {{\n\
             \x20   test.equal_i64(6 * 7, 42);\n\
             }}\n"
        ),
    )?;
    write(&directory.join(".gitignore"), "/target/\n")?;
    write(
        &directory.join("README.md"),
        &format!(
            "# {name}\n\
             \n\
             Created with `kush new`.\n\
             \n\
             ```sh\n\
             kush check\n\
             kush test\n\
             kush run\n\
             kush build\n\
             ```\n"
        ),
    )?;
    Ok(())
}

fn write(path: &Path, contents: &str) -> Result<(), Failure> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)
            .map_err(|e| Failure::new(format!("cannot create {}: {e}", parent.display())))?;
    }
    fs::write(path, contents)
        .map_err(|e| Failure::new(format!("cannot write {}: {e}", path.display())))
}

/// Turn a directory name into a package identifier. `my-app` becomes `my_app`;
/// a leading digit is prefixed with `app_`.
fn derive_name(directory: &Path) -> String {
    let raw = directory
        .file_name()
        .filter(|part| !part.is_empty())
        .map(|part| part.to_string_lossy().into_owned())
        .unwrap_or_else(|| "app".to_owned());
    let mut name = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            name.push(ch.to_ascii_lowercase());
        } else {
            name.push('_');
        }
    }
    while name.ends_with('_') {
        name.pop();
    }
    if name.is_empty() {
        name.push_str("app");
    }
    if name.as_bytes()[0].is_ascii_digit() {
        name.insert_str(0, "app_");
    }
    name
}
