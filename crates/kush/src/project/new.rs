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
    create_project_directory(directory)?;
    let result = write_files(directory, &name);
    if result.is_err() {
        // Remove only what this scaffold wrote; `remove_dir` refuses when
        // anything else occupies the directory, so a swapped-in attacker
        // directory is never deleted through.
        remove_new_scaffold(directory);
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

/// Create the project directory and its missing parents without following
/// any symbolic link that races the creation: an existing component that is
/// a symlink, or a non-directory, stops the creation at that component.
fn create_project_directory(directory: &Path) -> Result<(), Failure> {
    let absolute = if directory.is_absolute() {
        directory.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(directory)
    };
    match fs::symlink_metadata(directory) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(Failure::new(format!(
                "cannot create project directory {}: '{}' is a symbolic link",
                directory.display(),
                directory.display()
            )));
        }
        Ok(_) => {
            return Err(Failure::new(format!(
                "cannot create {}: the path already exists",
                directory.display()
            )));
        }
        Err(_) => {}
    }
    // Keep the root component so `built` stays absolute: a relative prefix
    // would silently resolve against the caller's current directory. Missing
    // ancestors are created one by one; symlinks and non-directories stop.
    let total = absolute.components().count();
    let mut built = PathBuf::new();
    for (position, component) in absolute.components().enumerate() {
        match component {
            std::path::Component::RootDir | std::path::Component::Prefix(_) => {
                built.push(component.as_os_str());
                continue;
            }
            _ => {}
        }
        if position + 1 == total {
            break;
        }
        built.push(component.as_os_str());
        match fs::symlink_metadata(&built) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(Failure::new(format!(
                    "cannot create project directory {}: '{}' is a symbolic link",
                    directory.display(),
                    built.display()
                )));
            }
            Ok(metadata) if !metadata.is_dir() => {
                return Err(Failure::new(format!(
                    "cannot create project directory {}: '{}' already exists and is not a directory",
                    directory.display(),
                    built.display()
                )));
            }
            Ok(_) => {}
            Err(_) => {
                fs::create_dir(&built)
                    .map_err(|e| Failure::new(format!("cannot create {}: {e}", built.display())))?;
            }
        }
    }
    match fs::create_dir(&absolute) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            Err(Failure::new(format!(
                "cannot create {}: the path already exists",
                directory.display()
            )))
        }
        Err(error) => Err(Failure::new(format!(
            "cannot create {}: {error}",
            directory.display()
        ))),
    }
}

/// Remove the files the failed scaffold wrote and the empty directories it
/// may have created. A directory that still holds unexpected content is left
/// in place; a swapped-in attacker directory is never deleted recursively.
fn remove_new_scaffold(directory: &Path) {
    for relative in [
        "src/main.kush",
        "tests/main.kush",
        "Kush.toml",
        ".gitignore",
        "README.md",
    ] {
        let _ = fs::remove_file(directory.join(relative));
    }
    let _ = fs::remove_dir(directory.join("src"));
    let _ = fs::remove_dir(directory.join("tests"));
    let _ = fs::remove_dir(directory);
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
