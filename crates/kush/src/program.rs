//! Multi-file programs. A root file plus every module reachable through `use`
//! is parsed into one program-wide span space, so diagnostics, resolution, and
//! checking can treat the program as a single unit while keeping file origins.
use crate::{Diagnostic, Span, ast};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

/// Standard-library modules embedded in the compiler. They are ordinary Kush
/// source checked by the same pipeline as user code.
pub const STD: &[(&str, &str)] = &[
    ("std.result", include_str!("../std/result.kush")),
    ("std.option", include_str!("../std/option.kush")),
    ("std.ascii", include_str!("../std/ascii.kush")),
    ("std.math", include_str!("../std/math.kush")),
    ("std.task", include_str!("../std/task.kush")),
    ("std.json", include_str!("../std/json.kush")),
    ("std.test", include_str!("../std/test.kush")),
    ("std.text", include_str!("../std/text.kush")),
    ("std.path", include_str!("../std/path.kush")),
    ("std.sort", include_str!("../std/sort.kush")),
    ("std.http", include_str!("../std/http.kush")),
    ("std.collections", include_str!("../std/collections.kush")),
    ("std.file", include_str!("../std/file.kush")),
    ("std.crc32", include_str!("../std/crc32.kush")),
    ("std.bytemap", include_str!("../std/bytemap.kush")),
    ("std.sys", include_str!("../std/sys.kush")),
    ("std.fs", include_str!("../std/fs.kush")),
    ("std.env", include_str!("../std/env.kush")),
    ("std.time", include_str!("../std/time.kush")),
    ("std.os", include_str!("../std/os.kush")),
    ("std.io", include_str!("../std/io.kush")),
];
const MAX_MODULES: usize = 256;
const MAX_TOTAL_SOURCE: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub name: String,
    pub text: String,
    pub base: usize,
}

/// Every file occupies a disjoint byte range `[base, base + len]` of one span space.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    pub files: Vec<SourceFile>,
}
impl SourceMap {
    fn add(&mut self, name: String, text: String) -> usize {
        let base = self.files.last().map_or(0, |f| f.base + f.text.len() + 1);
        self.files.push(SourceFile { name, text, base });
        self.files.len() - 1
    }
    pub fn file(&self, span: Span) -> Option<&SourceFile> {
        self.files
            .iter()
            .rev()
            .find(|f| f.base <= span.start && span.start <= f.base + f.text.len())
    }
    /// Render a diagnostic and its notes against the file that contains each span.
    pub fn render(&self, diagnostic: &Diagnostic) -> String {
        let Some(file) = self.file(diagnostic.span).or(self.files.first()) else {
            return format!("error: {}\n", diagnostic.message);
        };
        let local = |span: Span, file: &SourceFile| {
            Span::new(
                span.start.saturating_sub(file.base),
                span.end.saturating_sub(file.base),
            )
        };
        let mut primary = diagnostic.clone();
        primary.span = local(diagnostic.span, file);
        primary.notes.clear();
        let mut out = primary.render(&file.name, &file.text);
        for (span, message) in &diagnostic.notes {
            let note_file = self.file(*span).unwrap_or(file);
            let rendered = Diagnostic::new(local(*span, note_file), message.clone())
                .render(&note_file.name, &note_file.text);
            out.push_str(&rendered.replacen("error:", "note:", 1));
        }
        out
    }
}

#[derive(Debug, Clone)]
pub struct Unit {
    /// Module path such as `app.lexer`; empty for an anonymous root file.
    pub path: Vec<String>,
    pub file: usize,
    /// Number of items in `Program::module` contributed by this unit.
    pub items: std::ops::Range<usize>,
    /// For each `use` item (keyed by its span start): target unit and an
    /// optional imported item name (None imports the whole module).
    pub imports: BTreeMap<usize, (usize, Option<String>)>,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub sources: SourceMap,
    /// All declarations, root unit first, in one span space.
    pub module: ast::Module,
    pub units: Vec<Unit>,
}

/// Finds module source text by module path.
pub trait ModuleSource {
    fn find(&self, path: &[String]) -> Option<(String, String)>;
}
/// Resolves `use a.b.c` to `<root>/a/b/c.kush`.
pub struct Directory(pub PathBuf);
impl ModuleSource for Directory {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        let mut file = self.0.clone();
        for part in path {
            file.push(part);
        }
        file.set_extension("kush");
        let text = fs::read_to_string(&file).ok()?;
        Some((file.display().to_string(), text))
    }
}
/// In-memory modules keyed by dotted module path, for tests and tooling.
pub struct Memory(pub Vec<(String, String)>);
impl ModuleSource for Memory {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        let key = path.join(".");
        self.0
            .iter()
            .find(|(name, _)| *name == key)
            .map(|(name, text)| (format!("{}.kush", name.replace('.', "/")), text.clone()))
    }
}
struct NoModules;
impl ModuleSource for NoModules {
    fn find(&self, _: &[String]) -> Option<(String, String)> {
        None
    }
}

/// Load a root file and its imports from the root file's directory.
pub fn load_path(path: &Path) -> Result<Program, (Option<SourceMap>, Diagnostic)> {
    let text = fs::read_to_string(path).map_err(|e| {
        (
            None,
            Diagnostic::new(
                Span::default(),
                format!("cannot read {}: {e}", path.display()),
            ),
        )
    })?;
    let root = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    load(&path.display().to_string(), &text, &Directory(root))
}
/// Load one in-memory root file; only standard-library imports are available.
pub fn load_source(name: &str, text: &str) -> Result<Program, (Option<SourceMap>, Diagnostic)> {
    load(name, text, &NoModules)
}

pub fn load(
    name: &str,
    text: &str,
    modules: &dyn ModuleSource,
) -> Result<Program, (Option<SourceMap>, Diagnostic)> {
    let mut loader = Loader {
        sources: SourceMap::default(),
        units: Vec::new(),
        items: Vec::new(),
        by_path: BTreeMap::new(),
        modules,
    };
    match loader.run(name, text) {
        Ok(()) => Ok(Program {
            sources: loader.sources,
            module: ast::Module {
                items: loader.items,
            },
            units: loader.units,
        }),
        Err(error) => Err((Some(loader.sources), error)),
    }
}

struct Loader<'a> {
    sources: SourceMap,
    units: Vec<Unit>,
    items: Vec<ast::Declaration>,
    by_path: BTreeMap<Vec<String>, usize>,
    modules: &'a dyn ModuleSource,
}
impl Loader<'_> {
    fn parse(&mut self, name: String, text: String) -> Result<(usize, ast::Module), Diagnostic> {
        let total = self
            .sources
            .files
            .iter()
            .map(|f| f.text.len() + 1)
            .sum::<usize>();
        if total + text.len() > MAX_TOTAL_SOURCE {
            return Err(Diagnostic::new(
                Span::default(),
                "program exceeds the 16 MiB total source limit",
            ));
        }
        let file = self.sources.add(name, text);
        let source = &self.sources.files[file];
        let module = crate::parser::parse_at(&source.text, source.base)?;
        Ok((file, module))
    }
    fn header(module: &ast::Module) -> Option<Vec<String>> {
        match module.items.first().map(|d| &d.item.kind) {
            Some(ast::ItemKind::Module(path)) => Some(path.clone()),
            _ => None,
        }
    }
    fn run(&mut self, name: &str, text: &str) -> Result<(), Diagnostic> {
        let (file, module) = self.parse(name.to_owned(), text.to_owned())?;
        let path = Self::header(&module).unwrap_or_default();
        let mut queue = vec![self.push_unit(path.clone(), file, module)];
        if !path.is_empty() {
            self.by_path.insert(path, 0);
        }
        while let Some(unit) = queue.pop() {
            let uses = self.items[self.units[unit].items.clone()]
                .iter()
                .filter_map(|d| match &d.item.kind {
                    ast::ItemKind::Use(path) => Some((d.item.span, d.public, path.clone())),
                    _ => None,
                })
                .collect::<Vec<_>>();
            for (span, public, path) in uses {
                if public {
                    return Err(Diagnostic::new(
                        span,
                        "re-exports ('pub use') are not supported yet",
                    ));
                }
                let (target, item) = if let Some(target) = self.module(&path, span, &mut queue)? {
                    (target, None)
                } else if path.len() >= 2
                    && let Some(target) = self.module(&path[..path.len() - 1], span, &mut queue)?
                {
                    (target, Some(path[path.len() - 1].clone()))
                } else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot find module '{}' (looked for {}.kush{} relative to the root file, and the standard library)",
                            path.join("."),
                            path.join("/"),
                            if path.len() >= 2 {
                                format!(" and {}.kush", path[..path.len() - 1].join("/"))
                            } else {
                                String::new()
                            }
                        ),
                    ));
                };
                if target == unit {
                    return Err(Diagnostic::new(span, "a module cannot import itself"));
                }
                self.units[unit].imports.insert(span.start, (target, item));
            }
        }
        Ok(())
    }
    fn push_unit(&mut self, path: Vec<String>, file: usize, module: ast::Module) -> usize {
        let start = self.items.len();
        self.items.extend(module.items);
        self.units.push(Unit {
            path,
            file,
            items: start..self.items.len(),
            imports: BTreeMap::new(),
        });
        self.units.len() - 1
    }
    fn module(
        &mut self,
        path: &[String],
        span: Span,
        queue: &mut Vec<usize>,
    ) -> Result<Option<usize>, Diagnostic> {
        if let Some(unit) = self.by_path.get(path) {
            return Ok(Some(*unit));
        }
        let key = path.join(".");
        let found = if path.first().is_some_and(|p| p == "std") {
            STD.iter()
                .find(|(name, _)| *name == key)
                .map(|(name, text)| (format!("<{name}>"), (*text).to_owned()))
        } else {
            self.modules.find(path)
        };
        let Some((name, text)) = found else {
            return Ok(None);
        };
        if self.units.len() >= MAX_MODULES {
            return Err(Diagnostic::new(
                span,
                "program exceeds the 256-module limit",
            ));
        }
        let (file, module) = self.parse(name, text)?;
        if Self::header(&module).as_deref() != Some(path) {
            return Err(Diagnostic::new(
                span,
                format!("module file for '{key}' must begin with 'module {key};'"),
            ));
        }
        let unit = self.push_unit(path.to_vec(), file, module);
        self.by_path.insert(path.to_vec(), unit);
        queue.push(unit);
        Ok(Some(unit))
    }
}
