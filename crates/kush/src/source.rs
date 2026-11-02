use std::fmt::Write;

/// Half-open UTF-8 byte offsets in one source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
    pub fn through(self, other: Self) -> Self {
        Self::new(self.start, other.end)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
    /// Secondary locations, e.g. where a value was moved or borrowed.
    pub notes: Vec<(Span, String)>,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            notes: Vec::new(),
        }
    }
    pub fn with_note(mut self, span: Span, message: impl Into<String>) -> Self {
        self.notes.push((span, message.into()));
        self
    }

    /// Render a source excerpt with one-based Unicode-scalar columns. Tabs use
    /// four-column stops. Invalid external spans are clamped to UTF-8 boundaries.
    pub fn render(&self, name: &str, source: &str) -> String {
        let mut start = self.span.start.min(source.len());
        while !source.is_char_boundary(start) {
            start -= 1;
        }
        let mut end = self.span.end.max(start).min(source.len());
        while !source.is_char_boundary(end) {
            end -= 1;
        }
        let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
        let line_end = source[start..]
            .find('\n')
            .map_or(source.len(), |i| start + i);
        let line = source[..start].bytes().filter(|&b| b == b'\n').count() + 1;
        fn expanded(s: &str) -> String {
            let mut out = String::new();
            let mut col = 0;
            for c in s.chars() {
                if c == '\t' {
                    let n = 4 - col % 4;
                    out.extend(std::iter::repeat_n(' ', n));
                    col += n;
                } else if !c.is_control() {
                    out.push(c);
                    col += 1;
                }
            }
            out
        }
        let prefix = expanded(&source[line_start..start]);
        let marked = expanded(&source[line_start..end.min(line_end)]);
        let column = prefix.chars().count();
        let width = marked.chars().count().saturating_sub(column).max(1);
        let gutter = line.to_string().len();
        let mut out = format!(
            "error: {}\n --> {name}:{line}:{}\n",
            self.message,
            column + 1
        );
        let _ = writeln!(out, "{:gutter$} |", "");
        let _ = writeln!(out, "{line} | {}", expanded(&source[line_start..line_end]));
        let _ = writeln!(
            out,
            "{:gutter$} | {}{}",
            "",
            " ".repeat(column),
            "^".repeat(width)
        );
        for (span, message) in &self.notes {
            let note = Diagnostic::new(*span, message.clone()).render(name, source);
            out.push_str(&note.replacen("error:", "note:", 1));
        }
        out
    }
}
