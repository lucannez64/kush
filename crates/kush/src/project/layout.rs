//! Token-level layout for `kush fmt`.
//!
//! The AST does not keep comments, so instead of pretty-printing the AST this
//! pass re-emits the lexer's tokens verbatim and only decides the whitespace
//! between them: indentation, line breaks, and spacing. Comments are recovered
//! from the source text between tokens. The caller re-lexes the result and
//! rejects it unless the token stream is unchanged.
//!
//! Layout rules, in short:
//! - `{ ... }` is a multi-line block when the source spread it over several
//!   lines; otherwise it stays on one line as `{ a, b }` or `{ return x; }`. An effect row after `!` is always `{io, panic}`.
//! - In a multi-line block every statement (`;`), comma-separated item (struct
//!   fields, enum variants, match arms) and completed nested block ends a line.
//! - `( ... )` and `[ ... ]` stay on one line unless the source broke the line
//!   right after the opening delimiter; then each top-level item gets a line.
//! - Comments, single blank lines, and attribute lines are preserved.
use crate::lexer::{Kind, Token};

const INDENT: &str = "    ";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Group {
    /// Multi-line `{ }` block.
    Block,
    /// Single-line `{ }`.
    Inline,
    /// Effect row `! {io, panic}`.
    Row,
    /// Multi-line `(` / `[` with one item per line.
    ListMulti,
    /// Single-line `(` / `[`.
    ListInline,
    /// `#[ ... ]` attribute.
    Attribute,
}

pub(super) fn layout(source: &str, tokens: &[Token]) -> String {
    let tokens: Vec<&Token> = tokens.iter().filter(|t| t.kind != Kind::Eof).collect();
    let matching = match_delimiters(&tokens);
    let mut out = Output::default();
    let mut stack: Vec<Group> = Vec::new();
    // Generic angle brackets currently open (`Vec<`), so `>` closes them.
    let (generic_open, generic_close) = generic_brackets(&tokens);
    let mut prev: Option<usize> = None;
    let mut force_newline = false;
    let mut blank_after_item = false;
    let mut last_item_group: Option<u8> = None;

    for (index, token) in tokens.iter().enumerate() {
        let gap_start = prev.map_or(0, |p| tokens[p].span.end);
        let gap = &source[gap_start..token.span.start];
        let indent = indent_level(&stack);

        // Comments and blank lines in the gap before this token.
        let comments = split_gap(gap);
        let mut newline_seen = prev.is_none();
        for piece in &comments {
            match piece {
                Gap::Newlines(count) => {
                    if *count >= 2 {
                        out.blank_wanted = true;
                    }
                    newline_seen = true;
                }
                Gap::Comment(text) => {
                    if newline_seen || out.is_empty() {
                        if out.blank_wanted || (blank_after_item && stack.is_empty()) {
                            out.blank_line();
                        } else {
                            out.newline();
                        }
                        out.blank_wanted = false;
                        blank_after_item = false;
                        out.indent(indent_for_closer(&stack, token, indent));
                    } else {
                        out.space();
                    }
                    out.push(text);
                    if text.starts_with("//") {
                        out.newline();
                    }
                    newline_seen = false;
                }
            }
        }

        let kind = &token.kind;
        let text = &source[token.span.start..token.span.end];
        let prev_kind = prev.map(|p| &tokens[p].kind);
        let adjacent_in_source = gap.is_empty();

        // Closing delimiters pop first so they indent at the outer level.
        let closing = matches!(kind, Kind::RBrace | Kind::RParen | Kind::RBracket);
        let closed = if closing { stack.pop() } else { None };
        let indent = indent_level(&stack);

        // An author's line break next to a binary operator or `.` inside a
        // statement is kept as a continuation line, one level deeper.
        // `<`/`>` are excluded: next to a line break they are almost always
        // generic brackets (`Vec<i64>` at the end of a field list).
        let comparison = |k: &Kind| is_binary_operator(k) && !matches!(k, Kind::Lt | Kind::Gt);
        let continuation = !force_newline
            && !closing
            && gap.contains('\n')
            && matches!(stack.last(), None | Some(Group::Block | Group::ListMulti))
            && (comparison(kind)
                || *kind == Kind::Dot
                || prev_kind.is_some_and(|p| comparison(p) || *p == Kind::Dot));
        let starts_line = force_newline
            || continuation
            || matches!(closed, Some(Group::Block | Group::ListMulti))
            || out.at_line_start();
        let indent = if continuation { indent + 1 } else { indent };
        // Top-level items: a blank line between groups (imports, foreign
        // declarations, everything else) even if the source had none.
        let declaration_head =
            matches!(
                kind,
                Kind::Module
                    | Kind::Use
                    | Kind::Fn
                    | Kind::Struct
                    | Kind::Enum
                    | Kind::Type
                    | Kind::Pub
                    | Kind::Total
                    | Kind::Hash
            ) || ident_is(Some(kind), &["foreign", "trait", "impl", "effect", "prop"]);
        let item_start = stack.is_empty()
            && declaration_head
            && prev_kind.is_none_or(|p| matches!(p, Kind::Semi | Kind::RBrace | Kind::RBracket));
        if item_start {
            let group = match kind {
                Kind::Module | Kind::Use => 0,
                Kind::Ident(name) if name == "foreign" => 1,
                Kind::Hash | Kind::Pub => last_item_group.unwrap_or(2).max(2),
                _ => 2,
            };
            if last_item_group.is_some_and(|last| last != group) {
                blank_after_item = true;
            }
            last_item_group = Some(group);
        }
        if starts_line && !out.is_empty() {
            let blank = (out.blank_wanted && stack.iter().all(|g| *g == Group::Block) && !closing)
                || (blank_after_item && stack.is_empty() && !closing);
            if blank {
                out.blank_line();
            } else {
                out.newline();
            }
            out.indent(indent);
        } else if !out.is_empty() && !out.at_line_start() {
            let generic_close = generic_close[index];
            if needs_space(
                &tokens,
                index,
                prev_kind,
                generic_close,
                &generic_open,
                &stack,
                closed,
            ) && !(adjacent_in_source && glued_pair(prev_kind, kind))
            {
                out.space();
            }
        } else if out.at_line_start() && !out.is_empty() {
            out.indent(indent);
        }
        out.blank_wanted = false;
        blank_after_item = false;
        force_newline = false;
        out.push(text);

        // Opening delimiters push a group and maybe break the line.
        match kind {
            Kind::LBrace => {
                let group = if prev_kind == Some(&Kind::Bang) {
                    Group::Row
                } else if block_is_multiline(source, &tokens, index, matching[index]) {
                    Group::Block
                } else {
                    Group::Inline
                };
                stack.push(group);
                if group == Group::Block {
                    force_newline = true;
                }
            }
            Kind::LParen | Kind::LBracket => {
                let group = if prev_kind == Some(&Kind::Hash) {
                    Group::Attribute
                } else if list_is_multiline(source, &tokens, index, matching[index]) {
                    Group::ListMulti
                } else {
                    Group::ListInline
                };
                stack.push(group);
                if group == Group::ListMulti {
                    force_newline = true;
                }
            }
            _ => {}
        }

        // Line ends after statements and items.
        let next = tokens.get(index + 1).map(|t| &t.kind);
        match (kind, stack.last()) {
            (Kind::Semi, None | Some(Group::Block)) => force_newline = true,
            // Items keep the author's grouping: a comma ends the line only
            // where the source broke the line after it.
            (Kind::Comma, Some(Group::Block | Group::ListMulti))
                if break_after(source, &tokens, index) =>
            {
                force_newline = true;
            }
            (Kind::RBracket, _)
                if closed == Some(Group::Attribute) && break_after(source, &tokens, index) =>
            {
                force_newline = true;
            }
            (Kind::RBrace, top) if matches!(closed, Some(Group::Block | Group::Inline)) => {
                let continues = matches!(
                    next,
                    Some(
                        Kind::Else
                            | Kind::RParen
                            | Kind::RBracket
                            | Kind::Comma
                            | Kind::Semi
                            | Kind::Dot
                            | Kind::Question
                            | Kind::RBrace
                    )
                ) || next.is_some_and(is_binary_operator);
                if !continues && matches!(top, None | Some(Group::Block)) {
                    force_newline = true;
                    if top.is_none() && closed == Some(Group::Block) {
                        blank_after_item = true;
                    }
                }
            }
            _ => {}
        }
        prev = Some(index);
    }
    // Trailing comments after the last token.
    let tail_start = prev.map_or(0, |p| tokens[p].span.end);
    let mut newline_seen = false;
    for piece in split_gap(&source[tail_start..]) {
        match piece {
            Gap::Newlines(_) => newline_seen = true,
            Gap::Comment(text) => {
                if newline_seen {
                    out.newline();
                } else {
                    out.space();
                }
                out.push(&text);
                newline_seen = false;
            }
        }
    }
    let mut result = out.text;
    while result.ends_with(['\n', ' ']) {
        result.pop();
    }
    result.push('\n');
    result
}

fn indent_level(stack: &[Group]) -> usize {
    stack
        .iter()
        .filter(|g| matches!(g, Group::Block | Group::ListMulti))
        .count()
}

/// A comment before a closing brace belongs inside the block.
fn indent_for_closer(stack: &[Group], token: &Token, indent: usize) -> usize {
    let _ = (stack, token);
    indent
}

/// `<<` / `>>` written without a space are shift operators to the parser.
fn glued_pair(prev: Option<&Kind>, kind: &Kind) -> bool {
    matches!(
        (prev, kind),
        (Some(Kind::Lt), Kind::Lt) | (Some(Kind::Gt), Kind::Gt) | (Some(Kind::Minus), Kind::Gt)
    )
}

fn is_binary_operator(kind: &Kind) -> bool {
    matches!(
        kind,
        Kind::Plus
            | Kind::Minus
            | Kind::Star
            | Kind::Slash
            | Kind::Percent
            | Kind::Caret
            | Kind::AmpAmp
            | Kind::PipePipe
            | Kind::EqEq
            | Kind::Ne
            | Kind::Lt
            | Kind::Le
            | Kind::Gt
            | Kind::Ge
            | Kind::Pipe
            | Kind::Amp
            | Kind::FatArrow
            | Kind::Arrow
            | Kind::Eq
    )
}

fn ident_is(kind: Option<&Kind>, names: &[&str]) -> bool {
    matches!(kind, Some(Kind::Ident(name)) if names.contains(&name.as_str()))
}

fn is_keyword(kind: &Kind) -> bool {
    matches!(
        kind,
        Kind::Fn
            | Kind::Total
            | Kind::Pub
            | Kind::Let
            | Kind::Mut
            | Kind::Return
            | Kind::If
            | Kind::Else
            | Kind::Match
            | Kind::Enum
            | Kind::Struct
            | Kind::Type
            | Kind::Module
            | Kind::Use
            | Kind::Erased
            | Kind::While
            | Kind::Loop
            | Kind::Break
            | Kind::Continue
            | Kind::Handle
            | Kind::Perform
            | Kind::With
    )
}

/// A token after which a following operator is a prefix (unary) operator.
fn expects_operand(prev: Option<&Kind>) -> bool {
    match prev {
        None => true,
        Some(kind) => {
            is_binary_operator(kind)
                || matches!(
                    kind,
                    Kind::LParen
                        | Kind::LBracket
                        | Kind::LBrace
                        | Kind::Comma
                        | Kind::Semi
                        | Kind::Colon
                        | Kind::Bang
                        | Kind::Return
                        | Kind::If
                        | Kind::While
                        | Kind::Match
                        | Kind::Else
                        | Kind::Let
                        | Kind::Mut
                        | Kind::Break
                        | Kind::Question
                        | Kind::At
                )
                || ident_is(Some(kind), &["in", "as", "from"])
        }
    }
}

/// Precompute which `<`/`>` pairs are generic brackets. A `<` inside an
/// already-open generic list is generic too (`Fin<Nat.succ<n>>`); otherwise the
/// lexical head decides (`Vec<`, `impl<`, `fn f<`, `Trait<`).
fn generic_brackets(tokens: &[&Token]) -> (Vec<bool>, Vec<bool>) {
    let mut opens = vec![false; tokens.len()];
    let mut closes = vec![false; tokens.len()];
    let mut depth = 0usize;
    for index in 0..tokens.len() {
        match tokens[index].kind {
            Kind::Lt
                if depth > 0
                    || is_generic_open(tokens, index)
                    || adjacent_generic(tokens, index) =>
            {
                opens[index] = true;
                depth += 1;
            }
            Kind::Gt if depth > 0 => {
                closes[index] = true;
                depth -= 1;
            }
            _ => {}
        }
    }
    (opens, closes)
}

/// A `<` written flush against the previous token with a matching `>` before
/// any statement terminator is generic, which catches const generics such as
/// `add<1, 1>` and `Bytes.from<...>`. Comparisons keep their spacing (`a < b`)
/// or stop at `&&`, `||`, `==`, `{`, or `;` before a matching `>` appears.
fn adjacent_generic(tokens: &[&Token], index: usize) -> bool {
    let Some(previous) = index.checked_sub(1) else {
        return false;
    };
    if tokens[previous].span.end != tokens[index].span.start {
        return false;
    }
    let mut depth = 1usize;
    for token in &tokens[index + 1..] {
        match token.kind {
            Kind::Lt => depth += 1,
            Kind::Gt => {
                depth -= 1;
                if depth == 0 {
                    return true;
                }
            }
            Kind::Semi
            | Kind::LBrace
            | Kind::RBrace
            | Kind::AmpAmp
            | Kind::PipePipe
            | Kind::EqEq
            | Kind::Ne
            | Kind::Arrow => return false,
            _ => {}
        }
    }
    false
}

fn is_generic_open(tokens: &[&Token], index: usize) -> bool {
    let prev = index.checked_sub(1).map(|i| &tokens[i].kind);
    let before = index.checked_sub(2).map(|i| &tokens[i].kind);
    match prev {
        Some(Kind::ColonColon) => true,
        Some(Kind::Ident(name)) => {
            name.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                || name == "str"
                // `impl<T> ...`: the contextual keyword heads a generic list.
                || name == "impl"
                || matches!(
                    before,
                    Some(Kind::Fn | Kind::Struct | Kind::Enum | Kind::Type)
                ) || ident_is(before, &["trait", "effect", "impl"])
        }
        // `f: fn<'a>(...)`: generics directly after the keyword are a type.
        Some(Kind::Fn) => true,
        _ => ident_is(prev, &["impl"]),
    }
}

#[allow(clippy::too_many_arguments)]
fn needs_space(
    tokens: &[&Token],
    index: usize,
    prev: Option<&Kind>,
    generic_close: bool,
    generic_open: &[bool],
    stack: &[Group],
    closed: Option<Group>,
) -> bool {
    let kind = &tokens[index].kind;
    let Some(prev_kind) = prev else {
        return false;
    };
    let prev_index = index - 1;
    let before_prev = prev_index.checked_sub(1).map(|i| &tokens[i].kind);
    let effect_marker = *prev_kind == Kind::Bang && *kind == Kind::LBrace;
    let prev_is_unary = !effect_marker
        && matches!(
            prev_kind,
            Kind::Minus | Kind::Amp | Kind::Star | Kind::Bang | Kind::AmpAmp
        )
        && expects_operand(before_prev);

    // Never a space after these.
    if matches!(
        prev_kind,
        Kind::Dot | Kind::ColonColon | Kind::Hash | Kind::DotDot
    ) {
        return false;
    }
    if prev_is_unary {
        // `&mut x`, `&'a T`: the keyword/lifetime after a borrow still needs a space after it,
        // but not between `&` and it.
        return false;
    }
    if *prev_kind == Kind::Lt && generic_open[prev_index] {
        return false;
    }
    if matches!(prev_kind, Kind::LParen | Kind::LBracket) {
        return false;
    }
    if *prev_kind == Kind::LBrace {
        return !matches!(stack.last(), Some(Group::Row)) && *kind != Kind::RBrace;
    }
    // Never a space before these.
    match kind {
        Kind::Comma | Kind::Semi | Kind::Colon | Kind::Dot | Kind::ColonColon | Kind::Question => {
            return false;
        }
        Kind::RParen | Kind::RBracket => return false,
        Kind::RBrace => {
            return !matches!(closed, Some(Group::Row)) && *prev_kind != Kind::LBrace;
        }
        Kind::DotDot => {
            return matches!(prev_kind, Kind::Comma | Kind::LBrace)
                || is_binary_operator(prev_kind);
        }
        Kind::Lt if generic_open.get(index).copied().unwrap_or(false) => {
            return false;
        }
        Kind::Gt if generic_close => return false,
        Kind::LParen => {
            return !(matches!(
                prev_kind,
                Kind::Ident(_) | Kind::RParen | Kind::RBracket | Kind::Gt | Kind::Fn
            ) || (*prev_kind == Kind::Gt));
        }
        Kind::LBracket => {
            return !matches!(
                prev_kind,
                Kind::Ident(_) | Kind::RParen | Kind::RBracket | Kind::At | Kind::String(_)
            ) || is_keyword(prev_kind);
        }
        Kind::At => return true,
        _ => {}
    }
    *prev_kind != Kind::At
}

/// A `{` opens a multi-line block when its body has a top-level `;`, a nested
/// block that must be multi-line, or a line break in the source.
fn block_is_multiline(source: &str, tokens: &[&Token], open: usize, close: Option<usize>) -> bool {
    let Some(close) = close else {
        return true;
    };
    if close == open + 1 {
        return false;
    }
    // Short blocks written on one line (`if m > n { return false; }`) stay
    // on one line; anything the author spread over lines is re-indented.
    let inner = &source[tokens[open].span.end..tokens[close].span.start];
    inner.contains('\n')
}

/// A `(`/`[` list is multi-line when the source broke the line right after it.
fn list_is_multiline(source: &str, tokens: &[&Token], open: usize, close: Option<usize>) -> bool {
    let Some(close) = close else {
        return false;
    };
    if close == open + 1 {
        return false;
    }
    let after_open = &source[tokens[open].span.end..tokens[open + 1].span.start];
    after_open.contains('\n') && !after_open.trim_start().starts_with("//")
        || after_open.contains('\n')
}

/// Whether the source has a line break between this token and the next.
fn break_after(source: &str, tokens: &[&Token], index: usize) -> bool {
    tokens
        .get(index + 1)
        .is_some_and(|next| source[tokens[index].span.end..next.span.start].contains('\n'))
}

fn match_delimiters(tokens: &[&Token]) -> Vec<Option<usize>> {
    let mut result = vec![None; tokens.len()];
    let mut stack = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        match token.kind {
            Kind::LBrace | Kind::LParen | Kind::LBracket => stack.push(index),
            Kind::RBrace | Kind::RParen | Kind::RBracket => {
                if let Some(open) = stack.pop() {
                    result[open] = Some(index);
                }
            }
            _ => {}
        }
    }
    result
}

enum Gap {
    Newlines(usize),
    Comment(String),
}

/// Split the text between two tokens into comments and newline runs.
fn split_gap(gap: &str) -> Vec<Gap> {
    let mut pieces = Vec::new();
    let bytes = gap.as_bytes();
    let mut i = 0;
    let mut newlines = 0;
    while i < bytes.len() {
        if gap[i..].starts_with("//") {
            if newlines > 0 {
                pieces.push(Gap::Newlines(newlines));
                newlines = 0;
            }
            let end = gap[i..].find('\n').map_or(gap.len(), |n| i + n);
            pieces.push(Gap::Comment(gap[i..end].trim_end().to_string()));
            i = end;
        } else if gap[i..].starts_with("/*") {
            if newlines > 0 {
                pieces.push(Gap::Newlines(newlines));
                newlines = 0;
            }
            let mut depth = 0;
            let start = i;
            while i < bytes.len() {
                if gap[i..].starts_with("/*") {
                    depth += 1;
                    i += 2;
                } else if gap[i..].starts_with("*/") {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += gap[i..].chars().next().map_or(1, char::len_utf8);
                }
            }
            pieces.push(Gap::Comment(gap[start..i].to_string()));
        } else {
            if bytes[i] == b'\n' {
                newlines += 1;
            }
            i += 1;
        }
    }
    if newlines > 0 {
        pieces.push(Gap::Newlines(newlines));
    }
    pieces
}

#[derive(Default)]
struct Output {
    text: String,
    blank_wanted: bool,
}

impl Output {
    fn is_empty(&self) -> bool {
        self.text.is_empty()
    }
    fn at_line_start(&self) -> bool {
        self.text.is_empty() || self.text.ends_with('\n')
    }
    fn trim_trailing_spaces(&mut self) {
        while self.text.ends_with(' ') {
            self.text.pop();
        }
    }
    fn newline(&mut self) {
        self.trim_trailing_spaces();
        if !self.text.is_empty() && !self.text.ends_with('\n') {
            self.text.push('\n');
        }
    }
    fn blank_line(&mut self) {
        self.newline();
        if !self.text.is_empty() && !self.text.ends_with("\n\n") {
            self.text.push('\n');
        }
    }
    fn indent(&mut self, level: usize) {
        if self.at_line_start() {
            for _ in 0..level {
                self.text.push_str(INDENT);
            }
        }
    }
    fn space(&mut self) {
        if !self.text.ends_with([' ', '\n']) && !self.text.is_empty() {
            self.text.push(' ');
        }
    }
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
    }
}
