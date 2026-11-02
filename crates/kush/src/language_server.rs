//! A small stdio language server for the existing Kush frontend.
//!
//! The server deliberately reuses `program`, `parser`, `resolve`, and
//! `executable::check_program` rather than reimplementing the language in the
//! editor. It never links or executes a program and never writes `Kush.lock`:
//! diagnostics are computed from in-memory overlays of open documents.
//!
//! Supported LSP surface:
//! - initialize / initialized / shutdown / exit and protocol error responses;
//! - full-document `didOpen`/`didChange`/`didClose` with versioned diagnostics;
//! - `textDocument/definition` for lexical bindings, project imports, and
//!   imported module names;
//! - `textDocument/formatting` using the existing whitespace-only formatter.
//!
//! Not implemented: completion, hover, rename, references, semantic tokens,
//! incremental sync, and type-directed method dispatch beyond the resolver's
//! explicit bindings. See `docs/language-server.md` for the precise limits.

use crate::{
    Diagnostic, Span,
    ast::ItemKind,
    lexer::{self, Kind},
    program::{self, ModuleSource, Program, SourceFile, SourceMap},
    project::{self, Project},
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs,
    io::{self, BufRead, BufReader, Read, Write},
    path::{Path, PathBuf},
};

/// Largest accepted LSP message body. The program loader itself rejects
/// programs over 16 MiB, so a larger editor message cannot produce useful work.
pub const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;
const MAX_HEADER_BYTES: usize = 64 * 1024;

/// Run the language server on this process's stdin/stdout.
///
/// `0` means a clean shutdown or end of input; `1` means the client sent
/// `exit` without a preceding `shutdown`.
pub fn run_stdio() -> io::Result<u8> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut server = Server::new(stdout.lock(), env_current_dir());
    let mut input = BufReader::new(stdin.lock());
    server.serve(&mut input)
}

fn env_current_dir() -> PathBuf {
    std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

#[derive(Debug, Clone)]
struct Document {
    uri: String,
    path: PathBuf,
    text: String,
    version: i64,
}

struct Server<W: Write> {
    out: W,
    launch_dir: PathBuf,
    documents: BTreeMap<PathBuf, Document>,
    project: Option<Project>,
    published: BTreeMap<PathBuf, String>,
    /// Files the client closed. Their diagnostics stay cleared until a later
    /// didOpen explicitly opens them again, even if they remain imported.
    closed: BTreeSet<PathBuf>,
    initialized: bool,
    shutdown_requested: bool,
    exit_received: bool,
}

impl<W: Write> Server<W> {
    fn new(out: W, launch_dir: PathBuf) -> Self {
        Self {
            out,
            launch_dir,
            documents: BTreeMap::new(),
            project: None,
            published: BTreeMap::new(),
            closed: BTreeSet::new(),
            initialized: false,
            shutdown_requested: false,
            exit_received: false,
        }
    }

    fn serve<R: BufRead>(&mut self, input: &mut R) -> io::Result<u8> {
        loop {
            match read_frame(input)? {
                Frame::Eof => break,
                Frame::Message(message) => {
                    if self.handle(message)? {
                        break;
                    }
                }
                Frame::InvalidJson(message) => {
                    // A JSON-RPC parse error is a valid protocol message, not
                    // stray output. The request id is unknown at this point.
                    self.respond_error(None, -32700, &format!("Parse error: {message}"))?;
                }
                Frame::InvalidHeader(message) => {
                    // Header bytes cannot be resynchronised reliably. Report on
                    // stderr and stop; stdout never receives diagnostics text.
                    eprintln!("kush lsp: invalid message header: {message}");
                    return Ok(1);
                }
            }
        }
        Ok(if self.exit_received && !self.shutdown_requested {
            1
        } else {
            0
        })
    }

    /// Returns true when the server should stop reading.
    fn handle(&mut self, message: Value) -> io::Result<bool> {
        let Some(method) = message.get("method").and_then(Value::as_str) else {
            if let Some(id) = message.get("id") {
                self.respond_error(Some(id), -32600, "Invalid Request: missing string method")?;
            } else {
                eprintln!("kush lsp: ignoring notification without a method");
            }
            return Ok(false);
        };
        let id = message.get("id").cloned();
        let params = message.get("params").cloned().unwrap_or(Value::Null);

        if method != "exit" {
            let error = if self.shutdown_requested {
                Some((-32600, "Invalid Request: server has shut down"))
            } else if !self.initialized && method != "initialize" {
                Some((-32002, "Server not initialized"))
            } else if self.initialized && method == "initialize" {
                Some((-32600, "Invalid Request: server already initialized"))
            } else {
                None
            };
            if let Some((code, message)) = error {
                if let Some(id) = id {
                    self.respond_error(Some(&id), code, message)?;
                }
                return Ok(false);
            }
        }
        match method {
            "initialize" => {
                self.initialized = true;
                self.initialize_project(&params);
                if let Some(id) = id {
                    self.respond(
                        &id,
                        json!({
                            "capabilities": {
                                "positionEncoding": "utf-16",
                                "textDocumentSync": 1,
                                "definitionProvider": true,
                                "documentFormattingProvider": true
                            },
                            "serverInfo": {
                                "name": "kush-lsp",
                                "version": env!("CARGO_PKG_VERSION")
                            }
                        }),
                    )?;
                }
            }
            "initialized" => {}
            "shutdown" => {
                self.shutdown_requested = true;
                if let Some(id) = id {
                    self.respond(&id, Value::Null)?;
                }
            }
            "exit" => {
                self.exit_received = true;
                return Ok(true);
            }
            "textDocument/didOpen" => {
                self.did_open(&params)?;
            }
            "textDocument/didChange" => {
                self.did_change(&params)?;
            }
            "textDocument/didClose" => {
                self.did_close(&params)?;
            }
            "textDocument/didSave" => {}
            "textDocument/definition" => {
                if let Some(id) = id {
                    let mut result = self.definition(&params);
                    self.remap_location_uris(&mut result);
                    self.respond(&id, result)?;
                }
            }
            "textDocument/formatting" => {
                if let Some(id) = id {
                    let result = self.formatting(&params);
                    self.respond(&id, result)?;
                }
            }
            "workspace/didChangeConfiguration"
            | "workspace/didChangeWorkspaceFolders"
            | "$/cancelRequest"
            | "$/setTrace"
            | "window/workDoneProgress/cancel" => {}
            other => {
                if let Some(id) = id {
                    self.respond_error(Some(&id), -32601, &format!("Method not found: {other}"))?;
                }
            }
        }
        Ok(false)
    }

    fn initialize_project(&mut self, params: &Value) {
        let start = params
            .get("rootUri")
            .and_then(Value::as_str)
            .and_then(file_uri_to_path)
            .or_else(|| {
                params
                    .get("rootPath")
                    .and_then(Value::as_str)
                    .filter(|path| !path.is_empty())
                    .map(PathBuf::from)
            })
            .or_else(|| {
                params
                    .get("workspaceFolders")
                    .and_then(Value::as_array)
                    .and_then(|folders| folders.first())
                    .and_then(|folder| folder.get("uri"))
                    .and_then(Value::as_str)
                    .and_then(file_uri_to_path)
            })
            .unwrap_or_else(|| self.launch_dir.clone());
        let Some(manifest) = project::find_manifest(&start) else {
            if let Some(root) = &self.project {
                eprintln!(
                    "kush lsp: no {} found from {}; project was {}",
                    project::MANIFEST_NAME,
                    start.display(),
                    root.manifest_path.display()
                );
            }
            return;
        };
        match project::load(&manifest) {
            Ok(project) => self.project = Some(project),
            Err(error) => {
                eprintln!(
                    "kush lsp: cannot load project {}: {error}",
                    manifest.display()
                );
            }
        }
    }

    fn did_open(&mut self, params: &Value) -> io::Result<()> {
        let Some(text_document) = params.get("textDocument") else {
            return Ok(());
        };
        let Some(uri) = text_document.get("uri").and_then(Value::as_str) else {
            return Ok(());
        };
        let Some(path) = file_uri_to_path(uri) else {
            eprintln!("kush lsp: ignoring non-file document uri {uri}");
            return Ok(());
        };
        let Some(text) = text_document.get("text").and_then(Value::as_str) else {
            return Ok(());
        };
        let version = text_document
            .get("version")
            .and_then(Value::as_i64)
            .unwrap_or(0);
        let path = normalize_path(&path);
        self.closed.remove(&path);
        self.documents.insert(
            path.clone(),
            Document {
                uri: uri.to_owned(),
                path,
                text: text.to_owned(),
                version,
            },
        );
        self.refresh_diagnostics()
    }

    fn did_change(&mut self, params: &Value) -> io::Result<()> {
        let Some(text_document) = params.get("textDocument") else {
            return Ok(());
        };
        let Some(uri) = text_document.get("uri").and_then(Value::as_str) else {
            return Ok(());
        };
        let Some(path) = file_uri_to_path(uri).map(|path| normalize_path(&path)) else {
            return Ok(());
        };
        let Some(version) = text_document.get("version").and_then(Value::as_i64) else {
            return Ok(());
        };
        let Some(document) = self.documents.get_mut(&path) else {
            return Ok(());
        };
        // LSP versions are monotonic. Ignore an old outgoing request so a slow
        // client cannot replace newer unsaved text or publish old diagnostics.
        if version < document.version {
            return Ok(());
        }
        let Some(content_changes) = params.get("contentChanges").and_then(Value::as_array) else {
            return Ok(());
        };
        // The server advertises full sync. Applying the last full text is
        // correct even when a client also includes previous changes.
        if let Some(text) = content_changes
            .iter()
            .rev()
            .find_map(|change| change.get("text").and_then(Value::as_str))
        {
            document.text = text.to_owned();
        }
        document.version = version;
        self.refresh_diagnostics()
    }

    fn did_close(&mut self, params: &Value) -> io::Result<()> {
        let Some(uri) = params
            .get("textDocument")
            .and_then(|document| document.get("uri"))
            .and_then(Value::as_str)
        else {
            return Ok(());
        };
        let Some(path) = file_uri_to_path(uri).map(|path| normalize_path(&path)) else {
            return Ok(());
        };
        let removed = self.documents.remove(&path);
        let publish_uri = removed
            .as_ref()
            .map_or(uri, |document| document.uri.as_str());
        // Clear immediately even if the file remains imported by an open root.
        self.publish_diagnostics(&path, publish_uri, None, Vec::new())?;
        self.published.remove(&path);
        self.closed.insert(path);
        self.refresh_diagnostics()
    }

    fn refresh_diagnostics(&mut self) -> io::Result<()> {
        let analysis = self.analyze();
        let mut targets = self.documents.keys().cloned().collect::<BTreeSet<_>>();
        targets.extend(self.published.keys().cloned());
        // Imported project files can have diagnostics without being open. Show
        // them in the Problems panel, but never resurrect a closed file.
        targets.extend(analysis.diagnostics.keys().cloned());
        for path in targets {
            if self.closed.contains(&path) && !self.documents.contains_key(&path) {
                continue;
            }
            let diagnostics = analysis.diagnostics.get(&path).cloned().unwrap_or_default();
            let (uri, version) = if let Some(document) = self.documents.get(&path) {
                (document.uri.clone(), Some(document.version))
            } else {
                (
                    self.published
                        .get(&path)
                        .cloned()
                        .unwrap_or_else(|| path_to_uri(&path)),
                    None,
                )
            };
            if let Some(previous) = self.published.get(&path).cloned()
                && previous != uri
            {
                self.publish_diagnostics(&path, &previous, None, Vec::new())?;
            }
            self.publish_diagnostics(&path, &uri, version, diagnostics.clone())?;
            if diagnostics.is_empty() {
                self.published.remove(&path);
            } else {
                self.published.insert(path, uri);
            }
        }
        Ok(())
    }

    fn analyze(&self) -> Analysis {
        let mut analysis = Analysis::default();
        if self.documents.is_empty() {
            return analysis;
        }
        match &self.project {
            Some(project) => {
                let entry = normalize_path(&project.package.entry_path());
                analysis.merge(self.analyze_root(&entry));
                // An open file that is not reachable from the entry still gets
                // independent diagnostics rather than silently showing none.
                for path in self.documents.keys() {
                    if *path != entry && !analysis.loaded.contains(path) {
                        analysis.merge(self.analyze_root(path));
                    }
                }
            }
            None => {
                for path in self.documents.keys() {
                    analysis.merge(self.analyze_root(path));
                }
            }
        }
        analysis
    }

    fn analyze_root(&self, root: &Path) -> Analysis {
        let root = normalize_path(root);
        let text = match self
            .document_text(&root)
            .or_else(|| fs::read_to_string(&root).ok())
        {
            Some(text) => text,
            None => return Analysis::default(),
        };
        if let Some(project) = &self.project
            && root == normalize_path(&project.package.entry_path())
            && let (header, span) = parsed_entry_header(&text)
            && header != std::slice::from_ref(&project.package.name)
        {
            let mut analysis = Analysis::default();
            analysis.add_local_diagnostic(&root, &text, &Diagnostic::new(
                span,
                format!("entry module must be declared as 'module {};': header does not match the package", project.package.name),
            ));
            return analysis;
        }
        let modules = OverlayModules {
            project: self.project.as_ref(),
            documents: &self.documents,
            root: &root,
        };
        let result = program::load(&root.display().to_string(), &text, &modules);
        let mut analysis = Analysis::default();
        match result {
            Ok(program) => {
                analysis.record_loaded(&program);
                if has_executable_items(&program) {
                    if let Err(diagnostic) = crate::executable::check_program(&program) {
                        analysis.add_diagnostic(&program.sources, &diagnostic);
                    }
                } else if let Err(diagnostic) = crate::check::check(&text) {
                    analysis.add_local_diagnostic(&root, &text, &diagnostic);
                }
            }
            Err((sources, diagnostic)) => {
                if let Some(sources) = &sources {
                    analysis.record_loaded_sources(sources);
                    analysis.add_diagnostic(sources, &diagnostic);
                } else {
                    analysis.add_local_diagnostic(&root, &text, &diagnostic);
                }
            }
        }
        analysis
    }

    fn document_text(&self, path: &Path) -> Option<String> {
        self.documents
            .get(&normalize_path(path))
            .map(|document| document.text.clone())
    }

    fn definition(&self, params: &Value) -> Value {
        let Some(document) = self.document_from_params(params) else {
            return Value::Null;
        };
        let Some(position) = params.get("position") else {
            return Value::Null;
        };
        let line = position.get("line").and_then(Value::as_u64).unwrap_or(0);
        let character = position
            .get("character")
            .and_then(Value::as_u64)
            .unwrap_or(0);
        let Some(offset) = position_to_offset(&document.text, line, character) else {
            return Value::Null;
        };
        let mut roots = Vec::new();
        if let Some(project) = &self.project {
            let entry = normalize_path(&project.package.entry_path());
            let in_project = project
                .all_packages()
                .any(|package| document.path.starts_with(normalize_path(&package.root)));
            if in_project {
                roots.push(entry);
            }
        }
        if !roots.contains(&document.path) {
            roots.push(document.path.clone());
        }
        for root in roots {
            if let Some(location) = self.definition_at_root(&root, document, offset) {
                return location;
            }
        }
        Value::Null
    }

    fn document_from_params(&self, params: &Value) -> Option<&Document> {
        let uri = params.get("textDocument")?.get("uri")?.as_str()?;
        let path = normalize_path(&file_uri_to_path(uri)?);
        self.documents.get(&path)
    }

    fn definition_at_root(&self, root: &Path, document: &Document, offset: usize) -> Option<Value> {
        let text = self
            .document_text(root)
            .or_else(|| fs::read_to_string(root).ok())?;
        let modules = OverlayModules {
            project: self.project.as_ref(),
            documents: &self.documents,
            root,
        };
        let program = program::load(&root.display().to_string(), &text, &modules).ok()?;
        let file_index =
            program.sources.files.iter().position(|file| {
                source_file_path(file).as_deref() == Some(document.path.as_path())
            })?;
        let base = program.sources.files[file_index].base;
        let global = base.saturating_add(offset);
        if let Some(location) = use_definition(&program, file_index, document, offset) {
            return Some(location);
        }
        let resolution = crate::resolve::resolve_program(&program).ok()?;
        let token = token_at(&document.text, offset);
        if let Some(reference) = resolution
            .references
            .iter()
            .filter(|reference| {
                // A cursor immediately after an identifier (before `(` or `.`)
                // is a common go-to-definition position; accept both edges.
                (reference.span.start <= global && global <= reference.span.end)
                    || token.is_some_and(|token| {
                        reference.span.start <= base + token.start
                            && base + token.end <= reference.span.end
                    })
            })
            .min_by_key(|reference| reference.span.end.saturating_sub(reference.span.start))
            && let Some(location) = binding_location(&program, &resolution, reference.binding)
        {
            return Some(location);
        }
        if let Some(token) = token {
            let token_span = Span::new(base + token.start, base + token.end);
            if let Some(binding) = resolution.binder(token_span)
                && let Some(location) = binding_location(&program, &resolution, binding)
            {
                return Some(location);
            }
            if let Some(binding) = resolution.method(token_span)
                && let Some(location) = binding_location(&program, &resolution, binding)
            {
                return Some(location);
            }
            let token_text = document
                .text
                .get(token.start..token.end)
                .unwrap_or_default();
            let mut candidates = resolution
                .bindings
                .iter()
                .enumerate()
                .filter(|(_, binding)| {
                    !matches!(binding.kind, crate::resolve::BindingKind::Builtin)
                        && binding.span != Span::default()
                        && span_contains_point(binding.span, global)
                        && binding_name_matches(&binding.name, token_text)
                })
                .collect::<Vec<_>>();
            candidates
                .sort_by_key(|(_, binding)| binding.span.end.saturating_sub(binding.span.start));
            if let Some((id, _)) = candidates.first()
                && let Some(location) = binding_location(&program, &resolution, *id)
            {
                return Some(location);
            }
        }
        None
    }

    fn formatting(&self, params: &Value) -> Value {
        let Some(document) = self.document_from_params(params) else {
            return Value::Null;
        };
        let Ok(formatted) =
            project::format::format_source(&document.path.display().to_string(), &document.text)
        else {
            return Value::Null;
        };
        if formatted == document.text {
            return json!([]);
        }
        json!([{
            "range": {
                "start": { "line": 0, "character": 0 },
                "end": offset_to_position(&document.text, document.text.len())
            },
            "newText": formatted
        }])
    }

    fn respond(&mut self, id: &Value, result: Value) -> io::Result<()> {
        write_message(
            &mut self.out,
            &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
        )
    }

    fn respond_error(&mut self, id: Option<&Value>, code: i64, message: &str) -> io::Result<()> {
        write_message(
            &mut self.out,
            &json!({
                "jsonrpc": "2.0",
                "id": id.cloned().unwrap_or(Value::Null),
                "error": { "code": code, "message": message }
            }),
        )
    }

    fn remap_location_uris(&self, value: &mut Value) {
        match value {
            Value::Array(values) => {
                for value in values {
                    self.remap_location_uris(value);
                }
            }
            Value::Object(fields) => {
                if let Some(path) = fields
                    .get("uri")
                    .and_then(Value::as_str)
                    .and_then(file_uri_to_path)
                    .map(|path| normalize_path(&path))
                    && let Some(document) = self.documents.get(&path)
                {
                    fields.insert("uri".to_owned(), json!(document.uri));
                }
                for value in fields.values_mut() {
                    self.remap_location_uris(value);
                }
            }
            _ => {}
        }
    }

    fn publish_diagnostics(
        &mut self,
        _path: &Path,
        uri: &str,
        version: Option<i64>,
        mut diagnostics: Vec<Value>,
    ) -> io::Result<()> {
        for diagnostic in &mut diagnostics {
            self.remap_location_uris(diagnostic);
        }
        let mut params = json!({
            "uri": uri,
            "diagnostics": diagnostics
        });
        if let Some(version) = version {
            params["version"] = json!(version);
        }
        write_message(
            &mut self.out,
            &json!({
                "jsonrpc": "2.0",
                "method": "textDocument/publishDiagnostics",
                "params": params
            }),
        )
    }
}

#[derive(Default)]
struct Analysis {
    diagnostics: BTreeMap<PathBuf, Vec<Value>>,
    loaded: BTreeSet<PathBuf>,
}

impl Analysis {
    fn merge(&mut self, other: Analysis) {
        self.loaded.extend(other.loaded);
        for (path, diagnostics) in other.diagnostics {
            let entry = self.diagnostics.entry(path).or_default();
            for diagnostic in diagnostics {
                if !entry.contains(&diagnostic) {
                    entry.push(diagnostic);
                }
            }
        }
    }

    fn record_loaded(&mut self, program: &Program) {
        self.record_loaded_sources(&program.sources);
    }

    fn record_loaded_sources(&mut self, sources: &SourceMap) {
        for file in &sources.files {
            if let Some(path) = source_file_path(file) {
                self.loaded.insert(path);
            }
        }
    }

    fn add_diagnostic(&mut self, sources: &SourceMap, diagnostic: &Diagnostic) {
        let Some(file) = sources.file(diagnostic.span) else {
            return;
        };
        let Some(path) = source_file_path(file) else {
            // Standard-library files are virtual (`<std.result>`); never emit
            // diagnostics for a path that does not exist on disk.
            return;
        };
        let range = span_to_range(&file.text, local_span(diagnostic.span, file.base));
        let mut value = json!({
            "range": range,
            "severity": 1,
            "source": "kush",
            "message": diagnostic.message
        });
        let related = diagnostic
            .notes
            .iter()
            .filter_map(|(span, message)| {
                let note_file = sources.file(*span)?;
                let note_path = source_file_path(note_file)?;
                let range = span_to_range(&note_file.text, local_span(*span, note_file.base));
                Some(json!({
                    "location": {
                        "uri": path_to_uri(&note_path),
                        "range": range
                    },
                    "message": message
                }))
            })
            .collect::<Vec<_>>();
        if !related.is_empty() {
            value["relatedInformation"] = Value::Array(related);
        }
        let entry = self.diagnostics.entry(path).or_default();
        if !entry.contains(&value) {
            entry.push(value);
        }
    }

    fn add_local_diagnostic(&mut self, path: &Path, text: &str, diagnostic: &Diagnostic) {
        let path = normalize_path(path);
        let value = json!({
            "range": span_to_range(text, diagnostic.span),
            "severity": 1,
            "source": "kush",
            "message": diagnostic.message
        });
        let entry = self.diagnostics.entry(path).or_default();
        if !entry.contains(&value) {
            entry.push(value);
        }
    }
}

struct OverlayModules<'a> {
    project: Option<&'a Project>,
    documents: &'a BTreeMap<PathBuf, Document>,
    root: &'a Path,
}

impl ModuleSource for OverlayModules<'_> {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        if let Some(project) = self.project
            && let Some(file) = project.modules.path_for_module(&path.join("."))
        {
            let normalized = normalize_path(file);
            if let Some(document) = self.documents.get(&normalized) {
                return Some((file.display().to_string(), document.text.clone()));
            }
            let text = fs::read_to_string(file).ok()?;
            return Some((file.display().to_string(), text));
        }
        // An unsaved module that is not in the on-disk project index still
        // resolves by its would-be module path. Its text stays in memory.
        for (document_path, document) in self.documents {
            if module_path_for(document_path, self.project, self.root).as_deref() == Some(path) {
                return Some((document_path.display().to_string(), document.text.clone()));
            }
        }
        // Source modules of a project are indexed by ModuleIndex. A new module
        // can be added while the server is running; fall back to the package's
        // ordinary directory layout without touching the disk.
        let base = match self.project {
            Some(project) => {
                let package = project
                    .all_packages()
                    .find(|package| path.first() == Some(&package.name));
                let package = package?;
                package.root.join("src")
            }
            None => self.root.parent()?.to_path_buf(),
        };
        let relative = if self.project.is_some() {
            &path[1..]
        } else {
            path
        };
        program::Directory(base).find(relative)
    }
}

fn module_path_for(path: &Path, project: Option<&Project>, root: &Path) -> Option<Vec<String>> {
    if let Some(project) = project {
        if let Some(module) = project.modules.module_for_file(path) {
            return Some(module.split('.').map(str::to_owned).collect());
        }
        for package in project.all_packages() {
            for (base, prefix) in [
                (package.root.join("src"), vec![package.name.clone()]),
                (
                    package.root.join("tests"),
                    vec![package.name.clone(), "tests".to_owned()],
                ),
            ] {
                let Ok(relative) = path.strip_prefix(&base) else {
                    continue;
                };
                let mut parts = prefix;
                let components = relative.components().collect::<Vec<_>>();
                for (index, component) in components.iter().enumerate() {
                    let mut text = component.as_os_str().to_string_lossy().into_owned();
                    if index + 1 == components.len() {
                        text = text.strip_suffix(".kush").unwrap_or(&text).to_owned();
                    }
                    parts.push(text);
                }
                return Some(parts);
            }
        }
        return None;
    }
    // Without a project, module lookup is relative to the root file's parent.
    let base = root.parent()?;
    let relative = path.strip_prefix(base).ok()?;
    let components = relative.components().collect::<Vec<_>>();
    let mut parts = Vec::with_capacity(components.len());
    for (index, component) in components.iter().enumerate() {
        let mut text = component.as_os_str().to_string_lossy().into_owned();
        if index + 1 == components.len() {
            text = text.strip_suffix(".kush").unwrap_or(&text).to_owned();
        }
        parts.push(text);
    }
    Some(parts)
}

/// The leading `module <path>;` header of an entry across a successful or
/// failed parse. Returning `(Vec::new(), _)` means no header is present so a
/// missing one still fails the package name check. A failed parse falls back
/// to the next tokens, so unsaved files with later syntax errors keep their
/// entry-header diagnostic instead of losing it to the parse error.
fn parsed_entry_header(text: &str) -> (Vec<String>, Span) {
    if let Ok(module) = crate::parser::parse(text) {
        return match module.items.first() {
            Some(item) => {
                let parts = match &item.item.kind {
                    ItemKind::Module(parts) => parts.clone(),
                    _ => Vec::new(),
                };
                (parts, item.item.span)
            }
            None => (Vec::new(), Span::default()),
        };
    }
    let Ok(tokens) = lexer::lex(text) else {
        return (Vec::new(), Span::default());
    };
    if !matches!(&tokens.first().map(|token| &token.kind), Some(Kind::Module)) {
        return (Vec::new(), Span::default());
    }
    let mut parts = Vec::new();
    let mut index = 1;
    let last = loop {
        let Kind::Ident(name) = tokens
            .get(index)
            .map_or(Kind::Eof, |token| token.kind.clone())
        else {
            return (Vec::new(), Span::default());
        };
        parts.push(name);
        index += 1;
        let next = tokens
            .get(index)
            .map_or(Kind::Eof, |token| token.kind.clone());
        if next != Kind::Dot {
            break tokens
                .get(index)
                .map_or(Span::default(), |token| token.span);
        }
        index += 1;
    };
    (parts, tokens[0].span.through(last))
}

fn has_executable_items(program: &Program) -> bool {
    let Some(root) = program.units.first() else {
        return false;
    };
    program.module.items[root.items.clone()]
        .iter()
        .any(|declaration| {
            matches!(
                &declaration.item.kind,
                ItemKind::Enum { total: false, .. }
                    | ItemKind::Struct { .. }
                    | ItemKind::Use(_)
                    | ItemKind::Trait { .. }
                    | ItemKind::Impl { .. }
            ) || matches!(&declaration.item.kind, ItemKind::Function(function) if !function.total)
        })
}

fn use_definition(
    program: &Program,
    file_index: usize,
    document: &Document,
    offset: usize,
) -> Option<Value> {
    let unit_index = program
        .units
        .iter()
        .position(|unit| unit.file == file_index)?;
    let file = &program.sources.files[file_index];
    let tokens = crate::lexer::lex(&document.text).ok()?;
    for declaration in &program.module.items[program.units[unit_index].items.clone()] {
        let ItemKind::Use(path) = &declaration.item.kind else {
            continue;
        };
        let item_span = local_span(declaration.item.span, file.base);
        if !span_contains_point(item_span, offset) {
            continue;
        }
        let identifiers = tokens
            .iter()
            .filter(|token| {
                token.span.start >= item_span.start
                    && token.span.end <= item_span.end
                    && matches!(token.kind, Kind::Ident(_))
            })
            .collect::<Vec<_>>();
        let Some(segment) = identifiers
            .iter()
            .position(|token| token.span.start <= offset && offset <= token.span.end)
        else {
            // The cursor may be on `use` or a dot; the module target is still
            // the useful answer for the whole declaration.
            continue;
        };
        let (target_unit, imported_item) = program.units[unit_index]
            .imports
            .get(&declaration.item.span.start)?;
        if imported_item.is_some() && segment + 1 == path.len() {
            let target = named_item_span(program, *target_unit, imported_item.as_deref()?)?;
            return location_for_span(program, target);
        }
        let target_file_index = program.units[*target_unit].file;
        let target_file = &program.sources.files[target_file_index];
        let target_path = source_file_path(target_file)?;
        return Some(location_value(
            &target_path,
            span_to_range(&target_file.text, module_anchor(program, *target_unit)),
        ));
    }
    None
}

fn module_anchor(program: &Program, unit: usize) -> Span {
    let file = &program.sources.files[program.units[unit].file];
    let Some(declaration) = program.module.items.get(program.units[unit].items.start) else {
        return Span::default();
    };
    let local = local_span(declaration.item.span, file.base);
    let Ok(tokens) = crate::lexer::lex(&file.text) else {
        return local;
    };
    let names = tokens
        .iter()
        .filter(|token| {
            token.span.start >= local.start
                && token.span.end <= local.end
                && matches!(token.kind, Kind::Ident(_))
        })
        .collect::<Vec<_>>();
    match (names.first(), names.last()) {
        (Some(first), Some(last)) => Span::new(first.span.start, last.span.end),
        _ => local,
    }
}

fn named_item_span(program: &Program, unit: usize, name: &str) -> Option<Span> {
    for declaration in &program.module.items[program.units[unit].items.clone()] {
        let matches = match &declaration.item.kind {
            ItemKind::Function(function) => function.name == name,
            ItemKind::Struct { name: item, .. }
            | ItemKind::Enum { name: item, .. }
            | ItemKind::Prop { name: item, .. }
            | ItemKind::Alias { name: item, .. }
            | ItemKind::Effect { name: item, .. }
            | ItemKind::EffectRow { name: item, .. }
            | ItemKind::Trait { name: item, .. } => item == name,
            ItemKind::GradeAlgebra(algebra) => algebra.name == name,
            _ => false,
        };
        if matches {
            let file = &program.sources.files[program.units[unit].file];
            let local = local_span(declaration.item.span, file.base);
            let tokens = crate::lexer::lex(&file.text).ok()?;
            let token = tokens.iter().find(|token| {
                token.span.start >= local.start
                    && token.span.end <= local.end
                    && matches!(&token.kind, Kind::Ident(candidate) if candidate == name)
            })?;
            return Some(Span::new(
                token.span.start + file.base,
                token.span.end + file.base,
            ));
        }
    }
    None
}

fn binding_location(
    program: &Program,
    resolution: &crate::resolve::Resolution,
    binding: usize,
) -> Option<Value> {
    let binding = resolution.bindings.get(binding)?;
    if matches!(binding.kind, crate::resolve::BindingKind::Builtin)
        || binding.span == Span::default()
    {
        // Builtins have no source location. Returning the first file would be a
        // bogus go-to-definition target.
        return None;
    }
    let file = program.sources.file(binding.span)?;
    let path = source_file_path(file)?;
    let local = local_span(binding.span, file.base);
    let local = refined_binding_span(file, binding, local);
    Some(location_value(&path, span_to_range(&file.text, local)))
}

fn refined_binding_span(file: &SourceFile, binding: &crate::resolve::Binding, local: Span) -> Span {
    use crate::resolve::BindingKind;
    if matches!(
        binding.kind,
        BindingKind::Local | BindingKind::Parameter | BindingKind::Generic
    ) {
        return local;
    }
    let wanted = binding
        .name
        .rsplit('.')
        .next()
        .unwrap_or(binding.name.as_str());
    let Ok(tokens) = crate::lexer::lex(&file.text) else {
        return local;
    };
    tokens
        .iter()
        .find(|token| {
            token.span.start >= local.start
                && token.span.end <= local.end
                && matches!(&token.kind, Kind::Ident(name) if name == wanted)
        })
        .map_or(local, |token| token.span)
}

fn binding_name_matches(binding: &str, token: &str) -> bool {
    binding == token || binding.rsplit('.').next() == Some(token)
}

fn location_for_span(program: &Program, span: Span) -> Option<Value> {
    let file = program.sources.file(span)?;
    let path = source_file_path(file)?;
    Some(location_value(
        &path,
        span_to_range(&file.text, local_span(span, file.base)),
    ))
}

fn location_value(path: &Path, range: Value) -> Value {
    json!({
        "uri": path_to_uri(path),
        "range": range
    })
}

fn local_span(span: Span, base: usize) -> Span {
    Span::new(
        span.start.saturating_sub(base),
        span.end.saturating_sub(base),
    )
}

fn span_contains_point(span: Span, point: usize) -> bool {
    span.start <= point && point < span.end
}

fn token_at(text: &str, offset: usize) -> Option<Span> {
    let tokens = crate::lexer::lex(text).ok()?;
    let mut previous = None;
    for token in tokens {
        if token.span.start <= offset && offset < token.span.end {
            return Some(token.span);
        }
        if token.span.end <= offset {
            previous = Some(token.span);
        }
        if token.span.start > offset {
            break;
        }
    }
    previous.filter(|span| span.end == offset)
}

fn source_file_path(file: &SourceFile) -> Option<PathBuf> {
    if file.name.starts_with('<') {
        return None;
    }
    let path = Path::new(&file.name);
    Some(normalize_path(path))
}

fn normalize_path(path: &Path) -> PathBuf {
    if let Ok(canonical) = fs::canonicalize(path) {
        return canonical;
    }
    if let (Some(parent), Some(name)) = (path.parent(), path.file_name()) {
        return normalize_path(parent).join(name);
    }
    if path.is_absolute() {
        return path.to_path_buf();
    }
    std::env::current_dir()
        .map(|directory| directory.join(path))
        .unwrap_or_else(|_| path.to_path_buf())
}

/// Convert an LSP UTF-16 `(line, character)` position to a UTF-8 byte offset.
/// Surrogate pairs count as two UTF-16 units; a position inside a pair snaps
/// backwards to the start of that scalar instead of splitting it.
pub fn position_to_offset(text: &str, line: u64, character: u64) -> Option<usize> {
    let mut line_start = 0usize;
    for _ in 0..line {
        let newline = text[line_start..].find('\n')?;
        line_start += newline + 1;
    }
    let line_end = text[line_start..]
        .find('\n')
        .map_or(text.len(), |newline| line_start + newline);
    let line_end = if line_end > line_start && text.as_bytes()[line_end - 1] == b'\r' {
        line_end - 1
    } else {
        line_end
    };
    let mut units = 0u64;
    for (index, character_value) in text[line_start..line_end].char_indices() {
        if units == character {
            return Some(line_start + index);
        }
        let next = units + character_value.len_utf16() as u64;
        if next > character {
            return Some(line_start + index);
        }
        units = next;
    }
    (units == character).then_some(line_end)
}

/// Convert a UTF-8 byte offset to an LSP UTF-16 position. Invalid external
/// offsets are clamped backwards to a scalar boundary.
pub fn offset_to_position(text: &str, offset: usize) -> Value {
    let mut offset = offset.min(text.len());
    while offset > 0 && !text.is_char_boundary(offset) {
        offset -= 1;
    }
    let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count();
    let line_start = text[..offset].rfind('\n').map_or(0, |newline| newline + 1);
    let mut end = offset;
    if end > line_start && text.as_bytes()[end - 1] == b'\r' {
        end -= 1;
    }
    let character = text[line_start..end].encode_utf16().count();
    json!({ "line": line as u64, "character": character as u64 })
}

fn span_to_range(text: &str, span: Span) -> Value {
    json!({
        "start": offset_to_position(text, span.start),
        "end": offset_to_position(text, span.end)
    })
}

fn read_frame<R: BufRead>(input: &mut R) -> io::Result<Frame> {
    let mut header_bytes = 0usize;
    let mut content_length = None;
    let mut saw_header = false;
    loop {
        let mut line = Vec::new();
        // Bound one header line as well as the accumulated header block: a
        // peer must not be able to force an allocation larger than the limit.
        let remaining = MAX_HEADER_BYTES.saturating_sub(header_bytes);
        let read = (&mut *input)
            .take(remaining as u64 + 1)
            .read_until(b'\n', &mut line)?;
        if read == 0 {
            return Ok(if saw_header {
                Frame::InvalidHeader("unexpected end of input in headers".to_owned())
            } else {
                Frame::Eof
            });
        }
        saw_header = true;
        header_bytes += read;
        if header_bytes > MAX_HEADER_BYTES {
            return Ok(Frame::InvalidHeader(
                "message headers exceed the 64 KiB limit".to_owned(),
            ));
        }
        let line = trim_line_ending(&line);
        if line.is_empty() {
            break;
        }
        let Ok(line) = std::str::from_utf8(line) else {
            return Ok(Frame::InvalidHeader(
                "message header is not valid UTF-8".to_owned(),
            ));
        };
        let Some((name, value)) = line.split_once(':') else {
            return Ok(Frame::InvalidHeader(format!("malformed header '{line}'")));
        };
        if name.eq_ignore_ascii_case("content-length") {
            if content_length.is_some() {
                return Ok(Frame::InvalidHeader(
                    "duplicate Content-Length header".to_owned(),
                ));
            }
            match value.trim().parse::<usize>() {
                Ok(length) => content_length = Some(length),
                Err(_) => {
                    return Ok(Frame::InvalidHeader(
                        "Content-Length is not a decimal byte count".to_owned(),
                    ));
                }
            }
        }
    }
    let Some(length) = content_length else {
        return Ok(Frame::InvalidHeader(
            "message is missing Content-Length".to_owned(),
        ));
    };
    if length > MAX_MESSAGE_BYTES {
        return Ok(Frame::InvalidHeader(format!(
            "message body of {length} bytes exceeds the {MAX_MESSAGE_BYTES}-byte limit"
        )));
    }
    let mut body = vec![0u8; length];
    if let Err(error) = input.read_exact(&mut body) {
        return Ok(Frame::InvalidHeader(format!(
            "truncated message body: {error}"
        )));
    }
    match serde_json::from_slice(&body) {
        Ok(message) => Ok(Frame::Message(message)),
        Err(error) => Ok(Frame::InvalidJson(error.to_string())),
    }
}

fn trim_line_ending(mut line: &[u8]) -> &[u8] {
    if line.ends_with(b"\n") {
        line = &line[..line.len() - 1];
    }
    if line.ends_with(b"\r") {
        line = &line[..line.len() - 1];
    }
    line
}

fn write_message<W: Write>(out: &mut W, message: &Value) -> io::Result<()> {
    let body = serde_json::to_vec(message).map_err(io::Error::other)?;
    write!(out, "Content-Length: {}\r\n\r\n", body.len())?;
    out.write_all(&body)?;
    out.flush()
}

enum Frame {
    Eof,
    Message(Value),
    InvalidJson(String),
    InvalidHeader(String),
}

fn file_uri_to_path(uri: &str) -> Option<PathBuf> {
    let encoded = uri.strip_prefix("file://").or_else(|| {
        // Tolerate `file:/absolute/path`; both forms identify a local file.
        uri.strip_prefix("file:")
            .filter(|rest| rest.starts_with('/'))
    })?;
    let encoded = encoded.split(['?', '#']).next().unwrap_or(encoded);
    let bytes = percent_decode(encoded)?;
    if !bytes.starts_with(b"/") {
        // `file://host/path`: only an empty or localhost authority is local.
        let rest = String::from_utf8_lossy(&bytes);
        let (authority, path) = rest.split_once('/')?;
        if !authority.is_empty() && authority != "localhost" {
            return None;
        }
        let bytes = format!("/{path}").into_bytes();
        return Some(PathBuf::from(String::from_utf8(bytes).ok()?));
    }
    Some(PathBuf::from(String::from_utf8(bytes).ok()?))
}

fn percent_decode(text: &str) -> Option<Vec<u8>> {
    let bytes = text.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            let high = *bytes.get(index + 1)?;
            let low = *bytes.get(index + 2)?;
            let value = (hex_value(high)? << 4) | hex_value(low)?;
            decoded.push(value);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    Some(decoded)
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn path_to_uri(path: &Path) -> String {
    let path = normalize_path(path);
    let text = path.to_string_lossy();
    let mut uri = String::from("file://");
    for byte in text.as_bytes() {
        let unreserved =
            byte.is_ascii_alphanumeric() || matches!(*byte, b'-' | b'.' | b'_' | b'~' | b'/');
        if unreserved {
            uri.push(*byte as char);
        } else {
            uri.push('%');
            uri.push_str(&format!("{byte:02X}"));
        }
    }
    uri
}

/// Entry point used by `main` so the command line ownership of stdout stays
/// outside the server (the server writes framed JSON, not ordinary output).
pub fn parse_stdio_args(args: &[OsString]) -> Result<(), String> {
    if args.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "lsp: unexpected argument '{}'",
            args[0].to_string_lossy()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(body: &str) -> Vec<u8> {
        format!("Content-Length: {}\r\n\r\n{body}", body.len()).into_bytes()
    }

    fn read_all(mut input: &[u8]) -> Vec<Value> {
        let mut values = Vec::new();
        let mut reader = BufReader::new(&mut input);
        loop {
            match read_frame(&mut reader).unwrap() {
                Frame::Eof => break,
                Frame::Message(value) => values.push(value),
                Frame::InvalidJson(message) => panic!("invalid JSON: {message}"),
                Frame::InvalidHeader(message) => panic!("invalid header: {message}"),
            }
        }
        values
    }

    #[test]
    fn content_length_framing_accepts_crlf_and_extra_headers() {
        let mut input = Vec::new();
        input.extend_from_slice(
            b"Content-Type: application/vscode-jsonrpc; charset=utf-8\r\nContent-Length: 2\r\n\r\n{}",
        );
        input.extend_from_slice(&frame(r#"{"jsonrpc":"2.0","method":"exit"}"#));
        let frames = read_all(&input);
        assert_eq!(frames.len(), 2);
        assert_eq!(frames[0], json!({}));
    }

    #[test]
    fn invalid_json_is_reported_then_later_frames_still_parse() {
        let mut input = frame("{not json");
        input.extend_from_slice(&frame(r#"{"jsonrpc":"2.0","method":"exit"}"#));
        let mut reader = BufReader::new(input.as_slice());
        assert!(matches!(
            read_frame(&mut reader).unwrap(),
            Frame::InvalidJson(_)
        ));
        assert!(matches!(
            read_frame(&mut reader).unwrap(),
            Frame::Message(_)
        ));
    }

    #[test]
    fn oversized_and_missing_lengths_are_rejected_without_allocation() {
        let mut reader = BufReader::new(b"Content-Length: 999999999999\r\n\r\n".as_slice());
        assert!(matches!(
            read_frame(&mut reader).unwrap(),
            Frame::InvalidHeader(_)
        ));
        let mut reader = BufReader::new(b"Content-Type: x\r\n\r\n".as_slice());
        assert!(matches!(
            read_frame(&mut reader).unwrap(),
            Frame::InvalidHeader(_)
        ));
        let huge_header = format!("X: {}\r\n\r\n", "a".repeat(MAX_HEADER_BYTES));
        let mut reader = BufReader::new(huge_header.as_bytes());
        assert!(matches!(
            read_frame(&mut reader).unwrap(),
            Frame::InvalidHeader(_)
        ));
    }

    #[test]
    fn utf16_positions_account_for_surrogate_pairs() {
        let text = "a😀b\nsecond";
        // 😀 is U+1F600: two UTF-16 units and four UTF-8 bytes.
        assert_eq!(position_to_offset(text, 0, 0), Some(0));
        assert_eq!(position_to_offset(text, 0, 1), Some(1));
        assert_eq!(position_to_offset(text, 0, 2), Some(1)); // inside pair snaps back
        assert_eq!(position_to_offset(text, 0, 3), Some(5));
        assert_eq!(position_to_offset(text, 1, 2), Some(9));
        assert_eq!(offset_to_position(text, 5)["character"], 3);
        assert_eq!(offset_to_position(text, 9)["line"], 1);
    }

    #[test]
    fn utf16_ranges_clamp_invalid_byte_offsets() {
        let text = "😀x";
        assert_eq!(offset_to_position(text, 2)["character"], 0);
        let range = span_to_range(text, Span::new(4, 5));
        assert_eq!(range["start"]["character"], 2);
        assert_eq!(range["end"]["character"], 3);
    }

    #[test]
    fn file_uris_round_trip_spaces_and_percent_escapes() {
        let path = PathBuf::from("/tmp/kush lsp/é%name.kush");
        let uri = path_to_uri(&path);
        assert!(uri.contains("%20"));
        assert!(uri.contains("%C3%A9"));
        assert!(uri.contains("%25"));
        assert_eq!(file_uri_to_path(&uri).unwrap(), path);
        assert!(file_uri_to_path("https://example.com/x.kush").is_none());
        assert!(file_uri_to_path("file:///tmp/bad%ZZ").is_none());
    }

    #[test]
    fn server_handles_shutdown_unknown_methods_and_malformed_json() {
        let mut input = Vec::new();
        input.extend_from_slice(&frame(
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        ));
        input.extend_from_slice(&frame(r#"{bad"#));
        input.extend_from_slice(&frame(
            r#"{"jsonrpc":"2.0","id":2,"method":"unknown/method","params":{}}"#,
        ));
        input.extend_from_slice(&frame(r#"{"jsonrpc":"2.0","id":3,"method":"shutdown"}"#));
        input.extend_from_slice(&frame(r#"{"jsonrpc":"2.0","method":"exit"}"#));
        let mut out = Vec::new();
        {
            let mut server = Server::new(&mut out, PathBuf::from("."));
            let status = server.serve(&mut BufReader::new(input.as_slice())).unwrap();
            assert_eq!(status, 0);
        }
        let messages = read_all(&out);
        assert_eq!(messages[0]["id"], 1);
        assert_eq!(messages[1]["error"]["code"], -32700);
        assert_eq!(messages[2]["error"]["code"], -32601);
        assert_eq!(messages[3]["id"], 3);
        assert_eq!(messages[3]["result"], Value::Null);
    }

    #[test]
    fn exit_before_shutdown_reports_a_protocol_failure() {
        let mut out = Vec::new();
        let mut server = Server::new(&mut out, PathBuf::from("."));
        let input = frame(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        let status = server.serve(&mut BufReader::new(input.as_slice())).unwrap();
        assert_eq!(status, 1);
    }
    #[test]
    fn lifecycle_rejects_requests_outside_initialized_session() {
        let mut out = Vec::new();
        let input = [
            r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/definition"}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":3,"method":"initialize"}"#,
            r#"{"jsonrpc":"2.0","id":4,"method":"shutdown"}"#,
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/definition"}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        ]
        .into_iter()
        .flat_map(frame)
        .collect::<Vec<_>>();
        let status = Server::new(&mut out, PathBuf::from("."))
            .serve(&mut BufReader::new(input.as_slice()))
            .unwrap();
        assert_eq!(status, 0);
        let messages = read_all(&out);
        assert_eq!(messages[0]["error"]["code"], -32002);
        assert_eq!(messages[2]["error"]["code"], -32600);
        assert_eq!(messages[4]["error"]["code"], -32600);
    }

    #[test]
    fn malformed_framing_returns_failure_status() {
        let mut out = Vec::new();
        let input = b"Content-Length: nope\r\n\r\n";
        let status = Server::new(&mut out, PathBuf::from("."))
            .serve(&mut BufReader::new(input.as_slice()))
            .unwrap();
        assert_eq!(status, 1);
        assert!(out.is_empty());
    }
}
