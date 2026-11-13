//! Conservative source formatting.
//!
//! The formatter is deliberately not a reflowing pretty-printer. The AST does
//! not retain comments, so an AST-based rewrite would delete them. Instead this
//! pass removes trailing spaces/tabs outside string literals, character
//! literals, and block comments, and ensures exactly one final newline. It never
//! changes indentation or token order. Every rewrite is lexed before and after
//! and rejected unless the token kinds are identical, so a scanner mistake
//! cannot silently change program text.
use super::{Failure, Project};
use crate::lexer;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

const MAX_FILES: usize = 4096;
const MAX_DEPTH: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Code,
    LineComment,
    BlockComment(usize),
    String,
    Char,
}

#[derive(Debug, Clone, Default)]
pub struct FormatOutcome {
    /// Files that were (or, in check mode, would be) rewritten.
    pub changed: Vec<PathBuf>,
    pub unchanged: usize,
}

pub fn format_source(name: &str, source: &str) -> Result<String, Failure> {
    let before =
        lexer::lex(source).map_err(|diagnostic| Failure::new(diagnostic.render(name, source)))?;
    // The layout pass emits `\n`; restore the file's own line ending.
    let crlf = source
        .find('\n')
        .is_some_and(|newline| newline > 0 && source.as_bytes()[newline - 1] == b'\r');
    let laid_out = super::layout::layout(source, &before);
    let laid_out = if crlf {
        laid_out.replace("\r\n", "\n").replace('\n', "\r\n")
    } else {
        laid_out
    };
    let candidate = normalize(&laid_out);
    let after = lexer::lex(&candidate).map_err(|diagnostic| {
        Failure::new(format!(
            "formatter safety check failed for {name}; file not changed\n{}",
            diagnostic.render(name, &candidate)
        ))
    })?;
    let same = before
        .iter()
        .map(|token| &token.kind)
        .eq(after.iter().map(|token| &token.kind));
    if !same {
        return Err(Failure::new(format!(
            "formatter safety check failed for {name}: token stream changed; file not changed"
        )));
    }
    Ok(candidate)
}

pub fn format_file(path: &Path, check: bool) -> Result<bool, Failure> {
    let name = path.display().to_string();
    // One write policy for explicit paths and walked files: symlinks are
    // refused (never written through) and only regular files are touched.
    let metadata =
        fs::symlink_metadata(path).map_err(|e| Failure::new(format!("cannot read {name}: {e}")))?;
    if metadata.file_type().is_symlink() {
        return Err(Failure::new(format!(
            "cannot format {name}: symbolic links are not followed; format the target file directly"
        )));
    }
    if !metadata.is_file() {
        return Err(Failure::new(format!(
            "cannot format {name}: not a regular file"
        )));
    }
    let source =
        fs::read_to_string(path).map_err(|e| Failure::new(format!("cannot read {name}: {e}")))?;
    let formatted = format_source(&name, &source)?;
    if formatted == source {
        return Ok(false);
    }
    if !check {
        write_source_atomically(path, &formatted)?;
    }
    Ok(true)
}

/// Exclusive temporary file in the source's directory, then an atomic rename:
/// a crash cannot truncate the source and concurrent runs never share state.
pub fn write_source_atomically(path: &Path, formatted: &str) -> Result<(), Failure> {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let name = path.file_name().map_or_else(
        || "source".to_owned(),
        |name| name.to_string_lossy().into_owned(),
    );
    let temporary = path.with_file_name(format!(
        ".{name}.{}-{}.tmp",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let result = (|| -> Result<(), Failure> {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|e| Failure::new(format!("cannot write {}: {e}", path.display())))?;
        file.write_all(formatted.as_bytes())
            .map_err(|e| Failure::new(format!("cannot write {}: {e}", path.display())))?;
        drop(file);
        fs::rename(&temporary, path)
            .map_err(|e| Failure::new(format!("cannot replace {}: {e}", path.display())))
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

pub fn format_project(project: &Project, check: bool) -> Result<FormatOutcome, Failure> {
    let files = project_files(project)?;
    let mut outcome = FormatOutcome::default();
    for file in files {
        if format_file(&file, check)? {
            outcome.changed.push(file);
        } else {
            outcome.unchanged += 1;
        }
    }
    Ok(outcome)
}

/// All root-package `.kush` files, excluding `target/`, hidden directories, and
/// dependency package roots. Sorted for deterministic reports and writes.
pub fn project_files(project: &Project) -> Result<Vec<PathBuf>, Failure> {
    let skip = project
        .dependencies
        .iter()
        .map(|package| package.root.clone())
        .collect::<Vec<_>>();
    let mut files = Vec::new();
    walk(&project.root, &skip, 0, &mut files)?;
    files.sort();
    Ok(files)
}

fn walk(
    directory: &Path,
    skip: &[PathBuf],
    depth: usize,
    files: &mut Vec<PathBuf>,
) -> Result<(), Failure> {
    if depth > MAX_DEPTH {
        return Err(Failure::new(format!(
            "{}: source tree is deeper than {MAX_DEPTH} directories",
            directory.display()
        )));
    }
    let mut entries = fs::read_dir(directory)
        .map_err(|e| {
            Failure::new(format!(
                "{}: cannot read directory: {e}",
                directory.display()
            ))
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| {
            Failure::new(format!(
                "{}: cannot read directory entry: {e}",
                directory.display()
            ))
        })?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|e| Failure::new(format!("{}: cannot inspect: {e}", path.display())))?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name == "target" || name.starts_with('.') || skip.iter().any(|p| p == &path) {
                continue;
            }
            walk(&path, skip, depth + 1, files)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("kush") {
            files.push(path);
            if files.len() > MAX_FILES {
                return Err(Failure::new(format!(
                    "project contains more than {MAX_FILES} Kush source files"
                )));
            }
        }
    }
    Ok(())
}

fn normalize(source: &str) -> String {
    if source.is_empty() {
        return String::new();
    }
    let mut out = String::with_capacity(source.len() + 1);
    let mut state = State::Code;
    for segment in source.split_inclusive('\n') {
        let (content, ending) = if let Some(content) = segment.strip_suffix("\r\n") {
            (content, "\r\n")
        } else if let Some(content) = segment.strip_suffix('\n') {
            (content, "\n")
        } else {
            (segment, "")
        };
        let trim_start = content.trim_end_matches([' ', '\t']).len();
        let state_at_trim = scan(content, trim_start, &mut state);
        let keep_trailing = matches!(
            state_at_trim,
            State::BlockComment(_) | State::String | State::Char
        );
        if keep_trailing {
            out.push_str(content);
        } else {
            out.push_str(&content[..trim_start]);
        }
        if state == State::LineComment {
            state = State::Code;
        }
        out.push_str(ending);
    }
    if !source.ends_with('\n') {
        out.push('\n');
    }
    if out.is_empty() {
        // The input was non-empty but consisted of no kept characters; keep a
        // newline so the file is still a valid, non-empty source file.
        out.push('\n');
    }
    out
}

/// Scan the whole line, update `state`, and return the state observed just
/// before byte `mark` (or the final state when `mark` is at the end).
fn scan(content: &str, mark: usize, state: &mut State) -> State {
    let mut index = 0;
    let mut at_mark = *state;
    while index < content.len() {
        if index == mark {
            at_mark = *state;
        }
        let rest = &content[index..];
        match *state {
            State::Code => {
                if rest.starts_with("//") {
                    *state = State::LineComment;
                    index += 2;
                } else if rest.starts_with("/*") {
                    *state = State::BlockComment(1);
                    index += 2;
                } else if let Some(ch) = rest.chars().next() {
                    if ch == '"' {
                        *state = State::String;
                        index += 1;
                    } else if ch == '\'' {
                        if is_char_literal(rest) {
                            *state = State::Char;
                        }
                        index += 1;
                    } else {
                        index += ch.len_utf8();
                    }
                }
            }
            State::LineComment => {
                if let Some(ch) = rest.chars().next() {
                    index += ch.len_utf8();
                }
            }
            State::BlockComment(depth) => {
                if rest.starts_with("/*") {
                    *state = State::BlockComment(depth + 1);
                    index += 2;
                } else if rest.starts_with("*/") {
                    *state = if depth == 1 {
                        State::Code
                    } else {
                        State::BlockComment(depth - 1)
                    };
                    index += 2;
                } else if let Some(ch) = rest.chars().next() {
                    index += ch.len_utf8();
                }
            }
            State::String => {
                if rest.starts_with('\\') {
                    if let Some(ch) = rest.chars().nth(1) {
                        index += 1 + ch.len_utf8();
                    } else {
                        index += 1;
                    }
                } else if let Some(ch) = rest.chars().next() {
                    if ch == '"' {
                        *state = State::Code;
                    }
                    index += ch.len_utf8();
                }
            }
            State::Char => {
                if rest.starts_with('\\') {
                    if let Some(ch) = rest.chars().nth(1) {
                        index += 1 + ch.len_utf8();
                    } else {
                        index += 1;
                    }
                } else if let Some(ch) = rest.chars().next() {
                    if ch == '\'' {
                        *state = State::Code;
                    }
                    index += ch.len_utf8();
                }
            }
        }
    }
    if mark >= content.len() {
        at_mark = *state;
    }
    at_mark
}

/// Distinguish `'x'` / `'\n'` from a lifetime such as `'a` in `&'a [T]`.
fn is_char_literal(rest: &str) -> bool {
    let mut chars = rest.chars();
    if chars.next() != Some('\'') {
        return false;
    }
    match chars.next() {
        Some('\\') => chars.next().is_some() && chars.next() == Some('\''),
        Some(_) => chars.next() == Some('\''),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_lifetime_tokens_and_crlf_line_endings() {
        let source = "fn f<'a>(value: &'a i64) -> i64 ! {panic} {\r\n    *value   \r\n}\r\n";
        let formatted = format_source("<test>", source).unwrap();
        assert!(formatted.contains("<'a>"));
        assert!(formatted.contains("&'a i64"));
        assert!(formatted.contains("*value\r\n"));
        assert!(formatted.ends_with("}\r\n"));
        assert!(!formatted.contains("   \r\n"));
    }

    #[test]
    fn keeps_string_and_character_contents_while_trimming_code_whitespace() {
        let source = "fn main() -> Unit ! {panic} {\n    let text = \"a // b /* c */ \\\"  \";   \n    let ch = '\\n';   \n    let lt = 'a;   \n}\n";
        let formatted = format_source("<test>", source).unwrap();
        assert!(formatted.contains("\"a // b /* c */ \\\"  \";"));
        assert!(formatted.contains("'\\n';"));
        assert!(formatted.contains("'a;"));
        assert!(!formatted.contains(";   \n"));
    }

    #[test]
    fn indents_struct_fields_and_keeps_generic_brackets_closed() {
        let source = "struct Document {\nnode:Box<Node>, text:Bytes, children:Vec<i64>\n}\n";
        let formatted = format_source("<test>", source).unwrap();
        assert_eq!(
            formatted,
            "struct Document {\n    node: Box<Node>, text: Bytes, children: Vec<i64>\n}\n"
        );
        // `>` in a field list must not read as a comparison continuation.
        assert!(formatted.lines().last() == Some("}"));
    }

    #[test]
    fn generic_heads_stay_closed_up() {
        for needle in [
            "impl<T> Scaled for Wrapper<T>",
            "Fin<Nat.succ<n>>",
            "add<1, 1>",
        ] {
            let source = format!("{needle} ! {{}}");
            let formatted = format_source("<test>", &source).unwrap();
            assert!(formatted.contains(needle), "{formatted}");
            assert!(!formatted.contains(" < "), "{formatted}");
            assert!(!formatted.contains(" >"), "{formatted}");
            assert_eq!(format_source("<test>", &formatted).unwrap(), formatted);
        }
    }

    #[test]
    fn one_blank_line_separates_top_level_groups() {
        let source = "module app;\nuse std.result.Result;\nfn main() -> Unit ! {panic} {}\n";
        let formatted = format_source("<test>", source).unwrap();
        assert_eq!(
            formatted,
            "module app;\nuse std.result.Result;\n\nfn main() -> Unit ! {panic} {}\n"
        );
        let twice = format_source("<test>", &formatted).unwrap();
        assert_eq!(twice, formatted);
    }

    #[test]
    fn comments_and_single_blank_lines_survive_layout() {
        let source = "module app;\n\n// explains the entry\nfn main() -> Unit ! {panic} {\n    // body note\n    0;\n}\n";
        let formatted = format_source("<test>", source).unwrap();
        assert!(formatted.contains("// explains the entry"));
        assert!(formatted.contains("    // body note\n"));
        assert_eq!(format_source("<test>", &formatted).unwrap(), formatted);
    }

    fn formats_to(source: &str, expected: &str) {
        let formatted = format_source("<test>", source).unwrap();
        assert_eq!(formatted, expected);
        assert_eq!(format_source("<test>", &formatted).unwrap(), formatted);
    }

    #[test]
    fn shifts_are_operators_not_generic_brackets() {
        formats_to(
            "fn f(v: i64) -> i64 ! {} { ((v<<1)|(v>>7)) & (v >>(2)) }\n",
            "fn f(v: i64) -> i64 ! {} { ((v << 1) | (v >> 7)) & (v >> (2)) }\n",
        );
    }

    #[test]
    fn refinements_invariants_and_clauses_keep_their_layout() {
        formats_to(
            "struct M { io: Vec<u8>   where len>=0x80 }\n\
             fn f(io:&mut Vec<u8> where len>=8)->i64!{panic}\n\
             ensures{0<=result}\n\
             {\n\
             let mut c=0;\n\
             while c<10 invariant{c<=10}{\n\
             c=c+1;\n\
             }\n\
             c\n\
             }\n",
            "struct M { io: Vec<u8> where len >= 0x80 }\n\
             fn f(io: &mut Vec<u8> where len >= 8) -> i64 ! {panic}\n\
             \x20   ensures { 0 <= result }\n\
             {\n\
             \x20   let mut c = 0;\n\
             \x20   while c < 10 invariant { c <= 10 } {\n\
             \x20       c = c + 1;\n\
             \x20   }\n\
             \x20   c\n\
             }\n",
        );
    }

    #[test]
    fn a_handled_body_follows_its_handler_on_the_same_line() {
        formats_to(
            "fn f() -> i64 ! {panic} {\n\
             let handle = 1;\n\
             handle Op: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {\n\
             k(x)\n\
             } {\n\
             go(handle)\n\
             }\n\
             }\n",
            "fn f() -> i64 ! {panic} {\n\
             \x20   let handle = 1;\n\
             \x20   handle Op: i64 -> i64 with fn(x: i64, k: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {\n\
             \x20       k(x)\n\
             \x20   } {\n\
             \x20       go(handle)\n\
             \x20   }\n\
             }\n",
        );
    }

    #[test]
    fn operators_after_a_try_are_binary() {
        // `?` is postfix: what follows it is a binary operator, not a borrow
        // or a negation.
        formats_to(
            "fn f() -> Result<Bool, i64> ! {} { Ok(a()? && b()?) }\nfn g() -> Result<i64, i64> ! {} { Ok(c()? - 1) }\n",
            "fn f() -> Result<Bool, i64> ! {} { Ok(a()? && b()?) }\nfn g() -> Result<i64, i64> ! {} { Ok(c()? - 1) }\n",
        );
    }

    #[test]
    fn a_comment_alone_in_a_block_stays_inside_it() {
        formats_to(
            "fn f(c: i64) -> Unit ! {} {\n    if c > 3 {\n        // nothing yet\n    }\n}\n",
            "fn f(c: i64) -> Unit ! {} {\n    if c > 3 {\n        // nothing yet\n    }\n}\n",
        );
    }
}
