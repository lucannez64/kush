use serde_json::{Value, json};
use std::{
    fs,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc::{self, Receiver, RecvTimeoutError},
    },
    thread,
    time::Duration,
};

struct Scratch {
    path: PathBuf,
}

impl Scratch {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "kush lsp {label} {} {} with space é",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, contents).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn project() -> (Scratch, PathBuf, PathBuf, PathBuf) {
    let scratch = Scratch::new("project");
    scratch.write(
        "Kush.toml",
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nentry = \"src/main.kush\"\n",
    );
    let main = scratch.write(
        "src/main.kush",
        "module demo;\n\nuse demo.util;\n\nfn main() -> i64 ! {panic} {\n    util.answer()\n}\n",
    );
    let util = scratch.write(
        "src/util.kush",
        "module demo.util;\n\npub fn answer() -> i64 ! {panic} {\n    42\n}\n",
    );
    let root = scratch.path.clone();
    (scratch, root, main, util)
}

fn path_to_uri(path: &Path) -> String {
    let text = path.to_string_lossy();
    let mut uri = String::from("file://");
    for byte in text.as_bytes() {
        if byte.is_ascii_alphanumeric() || matches!(*byte, b'-' | b'.' | b'_' | b'~' | b'/') {
            uri.push(*byte as char);
        } else {
            uri.push('%');
            uri.push_str(&format!("{byte:02X}"));
        }
    }
    uri
}

struct Client {
    child: Child,
    stdin: ChildStdin,
    messages: Receiver<Value>,
}

impl Client {
    fn spawn(directory: &Path) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_kush"))
            .arg("lsp")
            .current_dir(directory)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (sender, messages) = mpsc::channel();
        thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            while let Some(value) = read_message(&mut reader) {
                if sender.send(value).is_err() {
                    break;
                }
            }
        });
        Self {
            child,
            stdin,
            messages,
        }
    }

    fn send(&mut self, value: &Value) {
        let body = serde_json::to_vec(value).unwrap();
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.stdin.write_all(&body).unwrap();
        self.stdin.flush().unwrap();
    }

    fn send_raw(&mut self, body: &[u8]) {
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.stdin.write_all(body).unwrap();
        self.stdin.flush().unwrap();
    }

    fn receive(&self) -> Value {
        self.messages
            .recv_timeout(Duration::from_secs(30))
            .unwrap_or_else(|error| {
                if matches!(error, RecvTimeoutError::Timeout) {
                    panic!("language server did not respond within 30 seconds")
                } else {
                    panic!("language server closed stdout")
                }
            })
    }

    fn receive_diagnostics_for(&self, uri: &str) -> Value {
        loop {
            let message = self.receive();
            if message["method"] == "textDocument/publishDiagnostics"
                && message["params"]["uri"] == uri
            {
                return message;
            }
        }
    }

    fn initialize(&mut self, root: &Path) {
        self.send(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": null,
                "rootUri": path_to_uri(root),
                "capabilities": {}
            }
        }));
        let response = self.receive();
        assert_eq!(response["id"], 1);
        assert_eq!(
            response["result"]["capabilities"]["definitionProvider"],
            true
        );
        assert_eq!(
            response["result"]["capabilities"]["documentFormattingProvider"],
            true
        );
        self.send(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        }));
    }

    fn open(&mut self, uri: &str, version: i64, text: &str) {
        self.send(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "kush",
                    "version": version,
                    "text": text
                }
            }
        }));
    }

    fn change(&mut self, uri: &str, version: i64, text: &str) {
        self.send(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didChange",
            "params": {
                "textDocument": { "uri": uri, "version": version },
                "contentChanges": [{ "text": text }]
            }
        }));
    }

    fn shutdown(mut self) {
        self.send(&json!({
            "jsonrpc": "2.0",
            "id": 99,
            "method": "shutdown",
            "params": null
        }));
        let response = self.receive();
        assert_eq!(response["id"], 99);
        assert_eq!(response["result"], Value::Null);
        self.send(&json!({ "jsonrpc": "2.0", "method": "exit" }));
        let status = self.child.wait().unwrap();
        assert!(status.success(), "language server exit status: {status}");
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_message<R: BufRead>(reader: &mut R) -> Option<Value> {
    let mut content_length = None;
    loop {
        let mut line = String::new();
        let read = reader.read_line(&mut line).ok()?;
        if read == 0 {
            return None;
        }
        let line = line.trim_end_matches(['\r', '\n']);
        if line.is_empty() {
            break;
        }
        if let Some(value) = line.strip_prefix("Content-Length:") {
            content_length = value.trim().parse::<usize>().ok();
        }
    }
    let length = content_length?;
    let mut body = vec![0u8; length];
    reader.read_exact(&mut body).ok()?;
    serde_json::from_slice(&body).ok()
}

#[test]
fn project_diagnostics_definition_unicode_and_clean_shutdown() {
    let (scratch, root, main, util) = project();
    let main_text = fs::read_to_string(&main).unwrap();
    let util_text = fs::read_to_string(&util).unwrap();
    let main_uri = path_to_uri(&main);
    let util_uri = path_to_uri(&util);

    let mut client = Client::spawn(&root);
    client.initialize(&root);

    // Unsaved broken text must be diagnosed against the open document and its
    // version, without writing it to disk.
    let broken =
        "module demo;\n\nuse demo.util;\n\nfn main() -> i64 ! {panic} {\n    util.missing()\n}\n";
    client.open(&main_uri, 1, broken);
    let published = client.receive();
    assert_eq!(published["method"], "textDocument/publishDiagnostics");
    assert_eq!(published["params"]["uri"], main_uri);
    assert_eq!(published["params"]["version"], 1);
    let diagnostics = published["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{published}");
    assert!(
        diagnostics[0]["message"]
            .as_str()
            .unwrap()
            .contains("missing"),
        "{published}"
    );
    assert_eq!(fs::read_to_string(&main).unwrap(), main_text);

    // Full-sync replacement clears the old diagnostic.
    client.change(&main_uri, 2, &main_text);
    let published = client.receive();
    assert_eq!(published["params"]["version"], 2);
    assert!(
        published["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    // Definition through a project import: `util.answer()`.
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            // Immediately after `answer`, before the call parentheses.
            "position": { "line": 5, "character": 15 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["id"], 2);
    assert_eq!(response["result"]["uri"], util_uri);
    assert_eq!(response["result"]["range"]["start"]["line"], 2);

    // Definition on the imported module path in `use demo.util;`.
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 2, "character": 9 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["id"], 3);
    assert_eq!(response["result"]["uri"], util_uri);

    // Definition for a local binding in the same file.
    let local =
        "module demo;\n\nfn main() -> i64 ! {panic} {\n    let answer = 42;\n    answer\n}\n";
    client.change(&main_uri, 3, local);
    assert!(
        client.receive()["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 4, "character": 5 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["id"], 4);
    assert_eq!(response["result"]["uri"], main_uri);
    assert_eq!(response["result"]["range"]["start"]["line"], 3);

    // Unknown requests receive a protocol error, not stray stdout.
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "textDocument/hover",
        "params": {}
    }));
    let response = client.receive();
    assert_eq!(response["id"], 5);
    assert_eq!(response["error"]["code"], -32601);

    // A stale version must not replace version 3's unsaved text.
    client.change(&main_uri, 2, "module demo;\nthis is not kush\n");
    // No publish is emitted for an ignored stale version.
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 6,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 4, "character": 5 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["id"], 6);
    assert_eq!(response["result"]["uri"], main_uri);

    // Unicode before an identifier: the published UTF-16 column must count the
    // surrogate pair in the preceding string literal.
    let unicode_bad =
        "module demo;\nfn main() -> i64 ! {panic} {\n    let text = \"😀\"; missing()\n}\n";
    client.change(&main_uri, 4, unicode_bad);
    let published = client.receive();
    assert_eq!(published["params"]["version"], 4);
    let diagnostics = published["params"]["diagnostics"].as_array().unwrap();
    assert!(!diagnostics.is_empty());
    let prefix = "    let text = \"😀\"; ";
    let expected_column = prefix.encode_utf16().count();
    assert_eq!(diagnostics[0]["range"]["start"]["line"], 2, "{published}");
    assert_eq!(
        diagnostics[0]["range"]["start"]["character"]
            .as_u64()
            .unwrap() as usize,
        expected_column,
        "{published}"
    );
    // JSON escaping round-trips through the frame reader: the message contains
    // single quotes and the path contains spaces and non-ASCII characters.
    assert!(
        diagnostics[0]["message"]
            .as_str()
            .unwrap()
            .contains("missing"),
        "{published}"
    );

    // didClose clears the file's diagnostics.
    client.send(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didClose",
        "params": { "textDocument": { "uri": main_uri } }
    }));
    let cleared = client.receive();
    assert_eq!(cleared["params"]["uri"], main_uri);
    assert!(
        cleared["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(cleared["params"].get("version").is_none());

    // Diagnostics and definition never write the project or create a lockfile.
    assert_eq!(fs::read_to_string(&main).unwrap(), main_text);
    assert_eq!(fs::read_to_string(&util).unwrap(), util_text);
    assert!(!root.join("Kush.lock").exists());
    assert!(!root.join("target").exists());

    client.shutdown();
    drop(scratch);
}

#[test]
fn unsaved_imported_module_diagnostics_are_published_and_cleared() {
    let (scratch, root, main, util) = project();
    let main_text = fs::read_to_string(&main).unwrap();
    let util_text = fs::read_to_string(&util).unwrap();
    let main_uri = path_to_uri(&main);
    let util_uri = path_to_uri(&util);

    let mut client = Client::spawn(&root);
    client.initialize(&root);
    client.open(&main_uri, 1, &main_text);
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    // The imported module is open with invalid unsaved text. The entry is not
    // rewritten; its project analysis reports the error on the utility module.
    let broken = "module demo.util;\n\npub fn answer() -> i64 ! {panic} {\n    missing()\n}\n";
    client.open(&util_uri, 1, broken);
    let published = client.receive_diagnostics_for(&util_uri);
    assert_eq!(published["params"]["version"], 1);
    assert_eq!(
        published["params"]["diagnostics"].as_array().unwrap().len(),
        1
    );
    assert_eq!(fs::read_to_string(&util).unwrap(), util_text);

    client.send(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didClose",
        "params": { "textDocument": { "uri": util_uri } }
    }));
    let cleared = client.receive_diagnostics_for(&util_uri);
    assert!(
        cleared["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    // didClose also refreshes the still-open entry.
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    // Even while the entry remains open and still imports the module, a later
    // refresh does not resurrect diagnostics for the closed file.
    client.change(&main_uri, 2, &main_text);
    let entry = client.receive_diagnostics_for(&main_uri);
    assert!(
        entry["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(fs::read_to_string(&main).unwrap(), main_text);

    client.shutdown();
    drop(scratch);
}

#[test]
fn unsaved_imported_module_resolves_without_touching_disk() {
    let (scratch, root, main, _util) = project();
    let main_uri = path_to_uri(&main);
    let extra = root.join("src/extra.kush");
    let extra_uri = path_to_uri(&extra);
    let main_text =
        "module demo;\n\nuse demo.extra;\n\nfn main() -> i64 ! {panic} {\n    extra.value()\n}\n";
    let extra_text = "module demo.extra;\n\npub fn value() -> i64 ! {panic} {\n    7\n}\n";

    let mut client = Client::spawn(&root);
    client.initialize(&root);
    client.open(&main_uri, 1, main_text);
    let missing = client.receive_diagnostics_for(&main_uri);
    assert!(
        !missing["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{missing}"
    );
    assert!(!extra.exists());

    client.open(&extra_uri, 1, extra_text);
    // Publication order follows the sorted file paths; `extra.kush` sorts
    // before `main.kush`, so receive the extra notification first.
    assert!(
        client.receive_diagnostics_for(&extra_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 5, "character": 15 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["result"]["uri"], extra_uri);
    assert_eq!(response["result"]["range"]["start"]["line"], 2);
    assert!(!extra.exists());

    client.shutdown();
    drop(scratch);
}

#[test]
fn local_dependencies_supply_definitions_and_unsaved_diagnostics() {
    let scratch = Scratch::new("dependency");
    scratch.write(
        "Kush.toml",
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nentry = \"src/main.kush\"\n\n[dependencies]\nwords = { path = \"deps/words\" }\n",
    );
    let main = scratch.write(
        "src/main.kush",
        "module demo;\n\nuse words;\n\nfn main() -> i64 ! {panic} {\n    words.answer()\n}\n",
    );
    scratch.write(
        "deps/words/Kush.toml",
        "[package]\nname = \"words\"\nversion = \"0.1.0\"\nentry = \"src/lib.kush\"\n",
    );
    let words = scratch.write(
        "deps/words/src/lib.kush",
        "module words;\n\npub fn answer() -> i64 ! {panic} {\n    42\n}\n",
    );
    let root = scratch.path.clone();
    let main_text = fs::read_to_string(&main).unwrap();
    let words_text = fs::read_to_string(&words).unwrap();
    let main_uri = path_to_uri(&main);
    let words_uri = path_to_uri(&words);

    let mut client = Client::spawn(&root);
    client.initialize(&root);
    client.open(&main_uri, 1, &main_text);
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 5, "character": 10 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["result"]["uri"], words_uri);
    assert_eq!(response["result"]["range"]["start"]["line"], 2);

    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": 2, "character": 6 }
        }
    }));
    let response = client.receive();
    assert_eq!(response["result"]["uri"], words_uri);

    // A dependency file can be open with unsaved broken text; the root project
    // analysis uses the overlay and reports it on the dependency URI.
    client.open(
        &words_uri,
        1,
        "module words;\n\npub fn answer() -> i64 ! {panic} {\n    missing()\n}\n",
    );
    let published = client.receive_diagnostics_for(&words_uri);
    assert_eq!(published["params"]["version"], 1);
    assert_eq!(
        published["params"]["diagnostics"].as_array().unwrap().len(),
        1
    );
    // Opening the dependency also refreshed the open root's empty diagnostics.
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(fs::read_to_string(&words).unwrap(), words_text);

    client.shutdown();
    drop(scratch);
}

#[test]
fn formatting_is_the_documented_whitespace_only_edit() {
    let (scratch, root, main, _util) = project();
    let original = fs::read_to_string(&main).unwrap();
    let main_uri = path_to_uri(&main);
    let unformatted = "module demo;\n\nfn main() -> i64 ! {panic} {\n    42   \n}";
    let mut client = Client::spawn(&root);
    client.initialize(&root);
    client.open(&main_uri, 1, unformatted);
    assert!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/formatting",
        "params": {
            "textDocument": { "uri": main_uri },
            "options": { "tabSize": 4, "insertSpaces": true }
        }
    }));
    let response = client.receive();
    assert_eq!(response["id"], 2);
    let edits = response["result"].as_array().unwrap();
    assert_eq!(edits.len(), 1);
    assert_eq!(
        edits[0]["newText"],
        "module demo;\n\nfn main() -> i64 ! {panic} {\n    42\n}\n"
    );
    assert_eq!(fs::read_to_string(&main).unwrap(), original);

    client.shutdown();
    drop(scratch);
}

#[test]
fn malformed_json_and_unknown_methods_keep_the_protocol_stream_clean() {
    let scratch = Scratch::new("protocol");
    let mut client = Client::spawn(&scratch.path);
    client.initialize(&scratch.path);

    client.send_raw(b"{ this is not json");
    let response = client.receive();
    assert_eq!(response["id"], Value::Null);
    assert_eq!(response["error"]["code"], -32700);

    client.send(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "workspace/unknown",
        "params": {}
    }));
    let response = client.receive();
    assert_eq!(response["id"], 2);
    assert_eq!(response["error"]["code"], -32601);

    client.shutdown();
}

#[test]
fn unsaved_entry_headers_and_named_import_name_ranges_match_project_checks() {
    let (_scratch, root, main, util) = project();
    let main_uri = path_to_uri(&main);
    let mut client = Client::spawn(&root);
    client.initialize(&root);
    client.open(&main_uri, 1, "module other;\nfn main() -> i64 { 0 }\n");
    let diagnostic = client.receive_diagnostics_for(&main_uri);
    assert!(
        diagnostic["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("entry module must be declared")
    );
    client.change(&main_uri, 2, "fn main() -> i64 { 0 }\n");
    let diagnostic = client.receive_diagnostics_for(&main_uri);
    assert!(
        diagnostic["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("entry module must be declared")
    );
    client.change(
        &main_uri,
        3,
        "module demo;\nuse demo.util.answer;\nfn main() -> i64 ! {panic} { answer() }\n",
    );
    assert_eq!(
        client.receive_diagnostics_for(&main_uri)["params"]["diagnostics"],
        json!([])
    );
    client.send(&json!({"jsonrpc":"2.0","id":8,"method":"textDocument/definition","params":{"textDocument":{"uri":main_uri},"position":{"line":1,"character":18}}}));
    let response = client.receive();
    assert_eq!(response["result"]["uri"], path_to_uri(&util));
    assert_eq!(
        response["result"]["range"],
        json!({"start":{"line":2,"character":7},"end":{"line":2,"character":13}})
    );
    client.shutdown();
}

#[test]
fn symlink_aliases_clear_old_diagnostics_and_keep_unsaved_document_identity() {
    use std::os::unix::fs::symlink;
    let (scratch, root, main, util) = project();
    let alias = scratch.path.join("linked");
    symlink(&root, &alias).unwrap();
    let main_uri = path_to_uri(&alias.join("src/main.kush"));
    let util_uri = path_to_uri(&alias.join("src/util.kush"));
    let real_util_uri = path_to_uri(&util);
    let clean = fs::read_to_string(&util).unwrap();
    fs::write(
        &util,
        "module demo.util;\npub fn answer() -> i64 { missing() }\n",
    )
    .unwrap();
    let mut client = Client::spawn(&alias);
    client.initialize(&alias);
    client.open(&main_uri, 1, &fs::read_to_string(&main).unwrap());
    assert!(
        !client.receive_diagnostics_for(&real_util_uri)["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    client.open(&util_uri, 1, &clean);
    assert_eq!(
        client.receive_diagnostics_for(&real_util_uri)["params"]["diagnostics"],
        json!([])
    );
    assert_eq!(
        client.receive_diagnostics_for(&util_uri)["params"]["diagnostics"],
        json!([])
    );
    client.send(&json!({"jsonrpc":"2.0","id":8,"method":"textDocument/definition","params":{"textDocument":{"uri":main_uri},"position":{"line":5,"character":12}}}));
    assert_eq!(client.receive()["result"]["uri"], util_uri);

    let new_path = alias.join("src/new.kush");
    let new_uri = path_to_uri(&new_path);
    let new_text = "module demo.new;\npub fn value() -> i64 ! {panic} { 42 }\n";
    client.open(&new_uri, 1, new_text);
    client.receive_diagnostics_for(&new_uri);
    fs::write(&new_path, new_text).unwrap();
    client.change(
        &new_uri,
        2,
        "module demo.new;\npub fn value() -> i64 ! {panic} { missing() }\n",
    );
    let diagnostic = client.receive_diagnostics_for(&new_uri);
    assert_eq!(diagnostic["params"]["version"], 2);
    assert!(
        diagnostic["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("missing")
    );
    client.send(&json!({"jsonrpc":"2.0","id":9,"method":"textDocument/formatting","params":{"textDocument":{"uri":new_uri},"options":{}}}));
    loop {
        let response = client.receive();
        if response["id"] == 9 {
            assert!(response["result"].is_array());
            break;
        }
    }
    client.shutdown();
}
