//! Project module lookup for the existing loader.
//!
//! Single-file commands keep using `program::Directory`, which resolves a dotted
//! import below the root file's directory. A project instead builds one
//! deterministic index from every package's `src/` tree (and `tests/` for test
//! targets). No source imports are rewritten.
use super::{Failure, Package};
use crate::program::ModuleSource;
use std::{
    cell::Cell,
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

const MAX_SOURCE_FILES: usize = 4096;
const MAX_WALK_DEPTH: usize = 32;

#[derive(Debug, Clone, Default)]
pub struct ModuleIndex {
    modules: BTreeMap<String, PathBuf>,
    files: BTreeMap<PathBuf, String>,
}

struct WalkContext<'a> {
    package: &'a Package,
    entry: &'a Path,
    skip: &'a [PathBuf],
    /// Shared across packages: MAX_SOURCE_FILES bounds the project, not a
    /// single package's contribution to it.
    file_count: &'a Cell<usize>,
    tests: bool,
}

impl ModuleIndex {
    pub fn build(packages: &[Package]) -> Result<Self, Failure> {
        let mut index = Self::default();
        let file_count = Cell::new(0);
        for package in packages {
            let entry = package.entry_path();
            if !entry.is_file() {
                return Err(Failure::new(format!(
                    "{}: package '{}' entry '{}' does not exist",
                    package.manifest_path.display(),
                    package.name,
                    entry.display()
                )));
            }
            require_regular_source(&entry)?;
            let source = fs::read_to_string(&entry)
                .map_err(|e| Failure::new(format!("cannot read {}: {e}", entry.display())))?;
            let module = crate::parser::parse(&source)
                .map_err(|e| Failure::new(e.render(&entry.display().to_string(), &source)))?;
            if !matches!(module.items.first().map(|item| &item.item.kind),
                Some(crate::ast::ItemKind::Module(parts)) if parts == std::slice::from_ref(&package.name))
            {
                return Err(Failure::new(format!(
                    "{}: entry module must be declared as 'module {};': header does not match the package",
                    entry.display(),
                    package.name
                )));
            }
            let skip = packages
                .iter()
                .filter(|other| other.name != package.name)
                .map(|other| other.root.clone())
                .collect::<Vec<_>>();
            if !index.files.contains_key(&entry) {
                index.register(package, &entry, vec![package.name.clone()])?;
            }
            let mut context = WalkContext {
                package,
                entry: &entry,
                skip: &skip,
                file_count: &file_count,
                tests: false,
            };
            for (base, tests) in [
                (package.root.join("src"), false),
                (package.root.join("tests"), true),
            ] {
                if fs::symlink_metadata(&base).is_ok_and(|m| m.file_type().is_symlink()) {
                    return Err(Failure::new(format!(
                        "{}: symlinked source directories are not followed",
                        base.display()
                    )));
                }
                if base.is_dir() {
                    context.tests = tests;
                    index.walk(&mut context, &base, 0)?;
                }
            }
        }
        Ok(index)
    }

    fn walk(
        &mut self,
        context: &mut WalkContext<'_>,
        directory: &Path,
        depth: usize,
    ) -> Result<(), Failure> {
        if depth > MAX_WALK_DEPTH {
            return Err(Failure::new(format!(
                "{}: source tree is deeper than {MAX_WALK_DEPTH} directories",
                directory.display()
            )));
        }
        let mut entries = fs::read_dir(directory)
            .map_err(|e| {
                Failure::new(format!(
                    "{}: cannot read project source directory: {e}",
                    directory.display()
                ))
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| {
                Failure::new(format!(
                    "{}: cannot read project source entry: {e}",
                    directory.display()
                ))
            })?;
        entries.sort_by_key(|entry| entry.file_name());
        for dir_entry in entries {
            let path = dir_entry.path();
            let metadata = fs::symlink_metadata(&path)
                .map_err(|e| Failure::new(format!("{}: cannot inspect: {e}", path.display())))?;
            if metadata.file_type().is_symlink() {
                // Following symlinks could escape the package or create cycles.
                continue;
            }
            if metadata.is_dir() {
                let name = dir_entry.file_name();
                let name = name.to_string_lossy();
                if name == "target"
                    || name.starts_with('.')
                    || context.skip.iter().any(|p| p == &path)
                {
                    continue;
                }
                self.walk(context, &path, depth + 1)?;
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("kush") {
                continue;
            }
            if self.files.contains_key(&path) {
                // The entry file was registered under the package name above.
                continue;
            }
            context.file_count.set(context.file_count.get() + 1);
            if context.file_count.get() > MAX_SOURCE_FILES {
                return Err(Failure::new(format!(
                    "project contains more than {MAX_SOURCE_FILES} Kush source files"
                )));
            }
            let module = if path == context.entry {
                vec![context.package.name.clone()]
            } else {
                module_for(&path, context.package, context.tests)?
            };
            self.register(context.package, &path, module)?;
        }
        Ok(())
    }

    fn register(
        &mut self,
        package: &Package,
        file: &Path,
        parts: Vec<String>,
    ) -> Result<(), Failure> {
        let module = parts.join(".");
        if let Some(previous) = self.modules.get(&module) {
            return Err(Failure::new(format!(
                "{}: source files '{}' and '{}' both declare module '{module}'",
                package.manifest_path.display(),
                previous.display(),
                file.display()
            )));
        }
        if let Some(previous) = self.files.get(file) {
            return Err(Failure::new(format!(
                "{}: source file '{}' maps to both module '{}' and module '{module}'",
                package.manifest_path.display(),
                file.display(),
                previous
            )));
        }
        self.modules.insert(module.clone(), file.to_path_buf());
        self.files.insert(file.to_path_buf(), module);
        Ok(())
    }

    pub fn register_test(&mut self, package: &Package, file: &Path) -> Result<(), Failure> {
        require_regular_source(file)?;
        if self.files.contains_key(file) {
            return Ok(());
        }
        let relative = file
            .strip_prefix(&package.root)
            .map_err(|_| Failure::new("test target must be inside its package"))?;
        let mut parts = vec![package.name.clone()];
        for component in relative.components() {
            let text = component.as_os_str().to_string_lossy();
            let name = text.strip_suffix(".kush").unwrap_or(&text);
            if !super::manifest::valid_module_component(name) {
                return Err(Failure::new(format!(
                    "invalid test module component '{name}'"
                )));
            }
            parts.push(name.to_owned());
        }
        self.register(package, file, parts)
    }
    pub fn module_for_file(&self, file: &Path) -> Option<&str> {
        self.files.get(file).map(String::as_str)
    }

    pub fn path_for_module(&self, module: &str) -> Option<&Path> {
        self.modules.get(module).map(PathBuf::as_path)
    }

    pub fn len(&self) -> usize {
        self.modules.len()
    }

    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }
}

fn require_regular_source(path: &Path) -> Result<(), Failure> {
    let resolved = path
        .canonicalize()
        .map_err(|e| Failure::new(format!("cannot resolve {}: {e}", path.display())))?;
    if resolved != path {
        return Err(Failure::new(format!(
            "{}: symlinked source paths are not followed",
            path.display()
        )));
    }
    Ok(())
}

fn module_for(file: &Path, package: &Package, tests: bool) -> Result<Vec<String>, Failure> {
    let base = if tests {
        package.root.join("tests")
    } else {
        package.root.join("src")
    };
    let relative = file.strip_prefix(&base).map_err(|_| {
        Failure::new(format!(
            "{}: cannot derive a module path for '{}'",
            package.manifest_path.display(),
            file.display()
        ))
    })?;
    let mut parts = vec![package.name.clone()];
    if tests {
        parts.push("tests".to_owned());
    }
    let components = relative.components().collect::<Vec<_>>();
    for (index, component) in components.iter().enumerate() {
        let mut text = component.as_os_str().to_string_lossy().into_owned();
        if index + 1 == components.len()
            && let Some(stem) = text.strip_suffix(".kush")
        {
            text = stem.to_owned();
        }
        if !super::manifest::valid_module_component(&text) {
            return Err(Failure::new(format!(
                "{}: file '{}' maps to invalid module component '{text}'; use ASCII identifiers for file and directory names",
                package.manifest_path.display(),
                file.display()
            )));
        }
        parts.push(text);
    }
    Ok(parts)
}

impl ModuleSource for ModuleIndex {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        let file = self.path_for_module(&path.join("."))?;
        let text = fs::read_to_string(file).ok()?;
        Some((file.display().to_string(), text))
    }
}
