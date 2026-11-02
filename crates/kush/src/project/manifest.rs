//! Parsing and validation for `Kush.toml` project manifests.
//!
//! Only local path dependencies are part of this first project workflow. The
//! parser is deliberately strict: unknown tables, unknown fields, non-relative
//! paths, and malformed names are reported instead of being ignored. Strictness
//! is what makes the generated `Kush.lock` and the module index deterministic.
use super::Failure;
use std::{
    collections::BTreeMap,
    fs,
    path::{Component, Path, PathBuf},
};
use toml::{Table, Value};

#[derive(Debug, Clone)]
pub struct PackageInfo {
    pub name: String,
    pub version: String,
    /// Manifest-relative entry file. Defaults to `src/main.kush`.
    pub entry: PathBuf,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NativeOptions {
    /// Opaque library names or relative paths reserved for the native bridge.
    pub libraries: Vec<String>,
    /// Existing directories reserved for the native bridge's `-L` search path.
    pub library_paths: Vec<PathBuf>,
    /// Existing Rust adapter Cargo manifests reserved for the native bridge.
    pub cargo_manifests: Vec<PathBuf>,
}

impl NativeOptions {
    pub fn is_empty(&self) -> bool {
        self.libraries.is_empty()
            && self.library_paths.is_empty()
            && self.cargo_manifests.is_empty()
    }
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub package: PackageInfo,
    /// Dependency import name -> manifest-relative directory.
    pub dependencies: BTreeMap<String, PathBuf>,
    /// Optional test target. The default is `tests/main.kush` when it exists.
    pub test: Option<PathBuf>,
    pub native: NativeOptions,
}

pub fn parse(text: &str, path: &Path) -> Result<Manifest, Failure> {
    let mut root = text
        .parse::<Table>()
        .map_err(|e| Failure::new(format!("cannot parse {}: {e}", path.display())))?;

    let package_value = root
        .remove("package")
        .ok_or_else(|| missing_table(path, "package", "name, version, entry"))?;
    let mut package = table(package_value, "package", path)?;

    let name = required_string(&mut package, "name", "package", path)?;
    validate_package_name(&name)?;
    let version = match package.remove("version") {
        Some(Value::String(version)) if !version.is_empty() => version,
        Some(Value::String(_)) => {
            return Err(field_error(path, "package.version", "must not be empty"));
        }
        Some(_) => {
            return Err(field_error(
                path,
                "package.version",
                "must be a string such as \"0.1.0\"",
            ));
        }
        None => "0.1.0".to_owned(),
    };
    let entry = match package.remove("entry") {
        Some(value) => relative_path(value, "package.entry", path, false)?,
        None => PathBuf::from("src/main.kush"),
    };
    let test = match package.remove("test") {
        Some(value) => Some(relative_path(value, "package.test", path, false)?),
        None => None,
    };
    reject_unknown(&package, "package", path)?;

    let mut dependencies = BTreeMap::new();
    if let Some(value) = root.remove("dependencies") {
        let dependencies_table = table(value, "dependencies", path)?;
        for (dependency, value) in dependencies_table {
            validate_dependency_name(&dependency)?;
            let mut options = table(value, &format!("dependencies.{dependency}"), path)?;
            let relative = match options.remove("path") {
                Some(value) => relative_path(
                    value,
                    &format!("dependencies.{dependency}.path"),
                    path,
                    true,
                )?,
                None => {
                    return Err(field_error(
                        path,
                        &format!("dependencies.{dependency}"),
                        "local dependencies require a 'path' field",
                    ));
                }
            };
            reject_unknown(&options, &format!("dependencies.{dependency}"), path)?;
            dependencies.insert(dependency, relative);
        }
    }

    let native = match root.remove("native") {
        Some(value) => parse_native(value, path)?,
        None => NativeOptions::default(),
    };

    reject_unknown(&root, "manifest", path)?;

    Ok(Manifest {
        package: PackageInfo {
            name,
            version,
            entry,
        },
        dependencies,
        test,
        native,
    })
}

fn parse_native(value: Value, path: &Path) -> Result<NativeOptions, Failure> {
    let mut table = table(value, "native", path)?;
    let mut native = NativeOptions::default();
    if let Some(value) = table.remove("libraries") {
        for item in array(value, "native.libraries", path)? {
            let Value::String(item) = item else {
                return Err(field_error(
                    path,
                    "native.libraries",
                    "every item must be a string library name or path",
                ));
            };
            if item.is_empty() || item.contains('\0') {
                return Err(field_error(
                    path,
                    "native.libraries",
                    "library names must not be empty",
                ));
            }
            native.libraries.push(item);
        }
    }
    if let Some(value) = table.remove("library-paths") {
        for item in array(value, "native.library-paths", path)? {
            native
                .library_paths
                .push(relative_path(item, "native.library-paths", path, false)?);
        }
    }
    if let Some(value) = table.remove("cargo-manifests") {
        for item in array(value, "native.cargo-manifests", path)? {
            native.cargo_manifests.push(relative_path(
                item,
                "native.cargo-manifests",
                path,
                false,
            )?);
        }
    }
    reject_unknown(&table, "native", path)?;
    Ok(native)
}

/// Resolve the reserved native paths against the package root and require the
/// files/directories that are supposed to exist. The native bridge is not part
/// of this milestone; see `docs/projects.md` for the expected integration.
pub fn resolve_native(
    relative: &NativeOptions,
    root: &Path,
    manifest_path: &Path,
) -> Result<NativeOptions, Failure> {
    let mut native = relative.clone();
    for path in &mut native.library_paths {
        let resolved = root.join(&*path);
        let resolved = fs::canonicalize(&resolved).map_err(|e| {
            Failure::new(format!(
                "{}: native.library-paths entry '{}' cannot be resolved: {e}",
                manifest_path.display(),
                path.display()
            ))
        })?;
        if !resolved.is_dir() {
            return Err(Failure::new(format!(
                "{}: native.library-paths entry '{}' is not a directory",
                manifest_path.display(),
                path.display()
            )));
        }
        *path = resolved;
    }
    for path in &mut native.cargo_manifests {
        let resolved = root.join(&*path);
        let resolved = fs::canonicalize(&resolved).map_err(|e| {
            Failure::new(format!(
                "{}: native.cargo-manifests entry '{}' cannot be resolved: {e}",
                manifest_path.display(),
                path.display()
            ))
        })?;
        if !resolved.is_file() {
            return Err(Failure::new(format!(
                "{}: native.cargo-manifests entry '{}' is not a file",
                manifest_path.display(),
                path.display()
            )));
        }
        *path = resolved;
    }
    Ok(native)
}

pub fn validate_package_name(name: &str) -> Result<(), Failure> {
    if !valid_ident(name) {
        return Err(Failure::new(format!(
            "invalid package name '{name}': use an ASCII identifier such as 'hello' or 'hello_world'"
        )));
    }
    if name == "std" {
        return Err(Failure::new(
            "invalid package name 'std': it is reserved for the standard library",
        ));
    }
    Ok(())
}

fn validate_dependency_name(name: &str) -> Result<(), Failure> {
    if !valid_ident(name) {
        return Err(Failure::new(format!(
            "invalid dependency name '{name}': use an ASCII identifier that matches the dependency's package name"
        )));
    }
    if name == "std" {
        return Err(Failure::new(
            "invalid dependency name 'std': standard-library modules are built in",
        ));
    }
    Ok(())
}

/// Module names are single ASCII identifiers. Adapters are deliberately not
/// supported yet, so the import name and the dependency package name must match.
pub fn valid_ident(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == b'_') {
        return false;
    }
    bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && crate::lexer::lex(name).is_ok_and(|tokens| {
            matches!(
                tokens.as_slice(),
                [
                    crate::lexer::Token {
                        kind: crate::lexer::Kind::Ident(_),
                        ..
                    },
                    crate::lexer::Token {
                        kind: crate::lexer::Kind::Eof,
                        ..
                    }
                ]
            )
        })
}

pub fn valid_module_component(component: &str) -> bool {
    valid_ident(component)
}

fn table(value: Value, field: &str, path: &Path) -> Result<Table, Failure> {
    match value {
        Value::Table(table) => Ok(table),
        _ => Err(field_error(path, field, "must be a table")),
    }
}

fn array(value: Value, field: &str, path: &Path) -> Result<Vec<Value>, Failure> {
    match value {
        Value::Array(values) => Ok(values),
        _ => Err(field_error(path, field, "must be an array")),
    }
}

fn required_string(
    table: &mut Table,
    field: &str,
    section: &str,
    path: &Path,
) -> Result<String, Failure> {
    match table.remove(field) {
        Some(Value::String(value)) if !value.is_empty() => Ok(value),
        Some(Value::String(_)) => Err(field_error(
            path,
            &format!("{section}.{field}"),
            "must not be empty",
        )),
        Some(_) => Err(field_error(
            path,
            &format!("{section}.{field}"),
            "must be a string",
        )),
        None => Err(field_error(
            path,
            &format!("{section}.{field}"),
            "is required",
        )),
    }
}

fn relative_path(
    value: Value,
    field: &str,
    path: &Path,
    allow_parent: bool,
) -> Result<PathBuf, Failure> {
    let Value::String(text) = value else {
        return Err(field_error(path, field, "must be a string path"));
    };
    if text.is_empty() {
        return Err(field_error(path, field, "must not be empty"));
    }
    if text.contains('\0') {
        return Err(field_error(path, field, "must not contain NUL bytes"));
    }
    let relative = Path::new(&text);
    if relative.is_absolute() {
        return Err(field_error(
            path,
            field,
            "must be relative to the manifest directory, not absolute",
        ));
    }
    for component in relative.components() {
        match component {
            Component::Normal(_) | Component::CurDir => {}
            Component::ParentDir if allow_parent => {}
            Component::ParentDir => {
                return Err(field_error(
                    path,
                    field,
                    "must stay inside the package directory",
                ));
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(field_error(path, field, "must be a relative path"));
            }
        }
    }
    let mut normalized = PathBuf::new();
    for component in relative.components() {
        match component {
            Component::Normal(part) => normalized.push(part),
            Component::ParentDir if allow_parent => normalized.push(".."),
            _ => {}
        }
    }
    Ok(normalized)
}

fn reject_unknown(table: &Table, section: &str, path: &Path) -> Result<(), Failure> {
    if table.is_empty() {
        return Ok(());
    }
    let names = table.keys().cloned().collect::<Vec<_>>().join(", ");
    Err(field_error(
        path,
        section,
        &format!("unknown field(s): {names}"),
    ))
}

fn field_error(path: &Path, field: &str, message: &str) -> Failure {
    Failure::new(format!("{}: {field}: {message}", path.display()))
}

fn missing_table(path: &Path, field: &str, fields: &str) -> Failure {
    Failure::new(format!(
        "{}: missing [{field}] table (expected fields: {fields})",
        path.display()
    ))
}
