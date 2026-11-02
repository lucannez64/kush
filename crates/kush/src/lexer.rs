use crate::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Ident(String),
    Integer(String),
    /// A decimal float literal with a fraction and/or exponent, normalized by
    /// removing separators. Its width comes from context (default `f64`).
    Float(String),
    String(String),
    Char(char),
    /// A lifetime name such as `'a`, distinct from a character literal.
    Lifetime(String),
    Fn,
    Total,
    Pub,
    Let,
    Mut,
    Return,
    If,
    Else,
    Match,
    Enum,
    Struct,
    Type,
    Module,
    Use,
    Erased,
    While,
    Loop,
    Break,
    Continue,
    /// Lexical tail-resumptive effect handler and operation perform.
    Handle,
    Perform,
    With,
    True,
    False,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    Hash,
    At,
    Arrow,
    FatArrow,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    /// `<<`, formed by the parser from two adjacent `<` in expressions.
    Shl,
    /// `>>`, formed by the parser from two adjacent `>` in expressions.
    Shr,
    Bang,
    Amp,
    Pipe,
    AmpAmp,
    PipePipe,
    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Question,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: Kind,
    pub span: Span,
}

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    // Keep malformed or adversarial inputs bounded before AST allocation.
    if source.len() > 4 * 1024 * 1024 {
        return Err(Diagnostic::new(
            Span::default(),
            "source exceeds the initial 4 MiB file limit",
        ));
    }
    let mut lexer = Lexer {
        source,
        pos: 0,
        after_dot: false,
    };
    let mut tokens = Vec::new();
    loop {
        lexer.trivia()?;
        let start = lexer.pos;
        let kind = lexer.token()?;
        let eof = kind == Kind::Eof;
        let is_dot = kind == Kind::Dot;
        tokens.push(Token {
            kind,
            span: Span::new(start, lexer.pos),
        });
        lexer.after_dot = is_dot;
        if eof {
            return Ok(tokens);
        }
        if tokens.len() > 100_000 {
            return Err(Diagnostic::new(
                Span::new(start, lexer.pos),
                "token limit exceeded (100000)",
            ));
        }
    }
}

struct Lexer<'a> {
    source: &'a str,
    pos: usize,
    /// The previous token was `.`, so a following digit run is a positional
    /// field projection (`pair.0`, `nested.0.1`), never a float fraction.
    after_dot: bool,
}
impl Lexer<'_> {
    fn rest(&self) -> &str {
        &self.source[self.pos..]
    }
    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }
    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }
    fn error(&self, start: usize, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(Span::new(start, self.pos), message)
    }
    fn trivia(&mut self) -> Result<(), Diagnostic> {
        loop {
            while self.peek().is_some_and(|c| c.is_ascii_whitespace()) {
                self.bump();
            }
            if self.rest().starts_with("//") {
                while self.peek().is_some_and(|c| c != '\n') {
                    self.bump();
                }
            } else if self.rest().starts_with("/*") {
                let start = self.pos;
                self.pos += 2;
                let mut depth = 1;
                while depth > 0 {
                    if self.rest().starts_with("/*") {
                        self.pos += 2;
                        depth += 1;
                    } else if self.rest().starts_with("*/") {
                        self.pos += 2;
                        depth -= 1;
                    } else if self.bump().is_none() {
                        return Err(self.error(start, "unterminated block comment"));
                    }
                }
            } else {
                return Ok(());
            }
        }
    }
    fn escaped(&mut self, start: usize) -> Result<char, Diagnostic> {
        match self.bump() {
            Some('n') => Ok('\n'),
            Some('r') => Ok('\r'),
            Some('t') => Ok('\t'),
            Some('0') => Ok('\0'),
            Some('\\') => Ok('\\'),
            Some('"') => Ok('"'),
            Some('\'') => Ok('\''),
            _ => Err(self.error(
                start,
                "unsupported escape; use \\n, \\r, \\t, \\0, \\\\, \\\" or \\'",
            )),
        }
    }
    fn token(&mut self) -> Result<Kind, Diagnostic> {
        let start = self.pos;
        let Some(c) = self.bump() else {
            return Ok(Kind::Eof);
        };
        if c.is_ascii_alphabetic() || c == '_' {
            while self
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.bump();
            }
            return Ok(match &self.source[start..self.pos] {
                "fn" => Kind::Fn,
                "total" => Kind::Total,
                "pub" => Kind::Pub,
                "let" => Kind::Let,
                "mut" => Kind::Mut,
                "return" => Kind::Return,
                "if" => Kind::If,
                "else" => Kind::Else,
                "match" => Kind::Match,
                "enum" => Kind::Enum,
                "struct" => Kind::Struct,
                "type" => Kind::Type,
                "module" => Kind::Module,
                "use" => Kind::Use,
                "erased" => Kind::Erased,
                "true" => Kind::True,
                "false" => Kind::False,
                "while" => Kind::While,
                "loop" => Kind::Loop,
                "break" => Kind::Break,
                "continue" => Kind::Continue,
                "handle" => Kind::Handle,
                "perform" => Kind::Perform,
                "with" => Kind::With,
                text => Kind::Ident(text.to_owned()),
            });
        }
        if c == '0' && matches!(self.peek(), Some('x' | 'b' | 'o')) {
            // `0x`, `0b`, `0o` literals are normalized to decimal text, so
            // every later stage sees one integer spelling.
            let radix = match self.bump() {
                Some('x') => 16,
                Some('b') => 2,
                _ => 8,
            };
            let digits_start = self.pos;
            while self
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.bump();
            }
            let raw = &self.source[digits_start..self.pos];
            if raw.is_empty() || raw.starts_with('_') || raw.ends_with('_') || raw.contains("__") {
                return Err(self.error(start, "malformed integer literal"));
            }
            let value = u128::from_str_radix(&raw.replace('_', ""), radix).map_err(|_| {
                self.error(
                    start,
                    "invalid digit for this integer base (integer suffixes are not supported; the type comes from context)",
                )
            })?;
            if value > u128::from(u64::MAX) {
                return Err(self.error(start, "integer literal exceeds 64 bits"));
            }
            return Ok(Kind::Integer(value.to_string()));
        }
        if c.is_ascii_digit() {
            while self.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
                self.bump();
            }
            // A decimal point is part of the number only when a digit follows
            // it. This keeps `1..2` a range and `pair.0` a projection.
            let mut float = false;
            if !self.after_dot
                && self.peek() == Some('.')
                && self
                    .rest()
                    .chars()
                    .nth(1)
                    .is_some_and(|next| next.is_ascii_digit())
            {
                self.bump();
                while self.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
                    self.bump();
                }
                float = true;
            }
            if !self.after_dot && matches!(self.peek(), Some('e' | 'E')) {
                self.bump();
                if matches!(self.peek(), Some('+' | '-')) {
                    self.bump();
                }
                if !self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    return Err(self.error(start, "float exponent requires at least one digit"));
                }
                while self.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
                    self.bump();
                }
                float = true;
            }
            if self.peek().is_some_and(|c| c.is_alphabetic()) {
                while self.peek().is_some_and(|c| c.is_alphanumeric() || c == '_') {
                    self.bump();
                }
                return Err(self.error(
                    start,
                    "integer and float suffixes are not supported; a literal takes its type from context (annotate the binding, e.g. let x: u8 = 1 or let y: f32 = 1.5)",
                ));
            }
            let raw = &self.source[start..self.pos];
            if raw.ends_with('_')
                || raw.contains("__")
                || raw.contains("._")
                || raw.contains("_.")
                || raw.contains("e_")
                || raw.contains("E_")
                || raw.contains("+_")
                || raw.contains("-_")
            {
                return Err(
                    self.error(start, "numeric separators must occur singly between digits")
                );
            }
            let normalized = raw.replace('_', "");
            return Ok(if float {
                Kind::Float(normalized)
            } else {
                Kind::Integer(normalized)
            });
        }
        if c == '"' {
            let mut value = String::new();
            loop {
                match self.bump() {
                    Some('"') => return Ok(Kind::String(value)),
                    Some('\\') => value.push(self.escaped(start)?),
                    Some('\n' | '\r') | None => {
                        return Err(self.error(start, "unterminated string literal"));
                    }
                    Some(c) => value.push(c),
                }
            }
        }
        if c == '\'' {
            // `'a` is a lifetime token; `'a'` is a character literal. Scan the
            // identifier run and only take the lifetime path when the run is
            // not immediately closed by another quote.
            let rest = self.rest();
            let run = rest
                .char_indices()
                .take_while(|(_, c)| c.is_ascii_alphanumeric() || *c == '_')
                .collect::<Vec<_>>();
            if let Some((_, first)) = run.first()
                && (first.is_ascii_alphabetic() || *first == '_')
            {
                let length = run
                    .last()
                    .map(|(index, c)| index + c.len_utf8())
                    .unwrap_or(0);
                if !rest[length..].starts_with('\'') {
                    let name = rest[..length].to_owned();
                    for _ in 0..length {
                        self.bump();
                    }
                    return Ok(Kind::Lifetime(name));
                }
            }
            let value = match self.bump() {
                Some('\\') => self.escaped(start)?,
                Some('\'' | '\n' | '\r') | None => {
                    return Err(self.error(start, "expected one character in character literal"));
                }
                Some(c) => c,
            };
            if self.bump() != Some('\'') {
                return Err(self.error(
                    start,
                    "character literal must contain exactly one Unicode scalar",
                ));
            }
            return Ok(Kind::Char(value));
        }
        let pairs = [
            ('-', '>', Kind::Arrow),
            ('=', '>', Kind::FatArrow),
            (':', ':', Kind::ColonColon),
            ('.', '.', Kind::DotDot),
            ('&', '&', Kind::AmpAmp),
            ('|', '|', Kind::PipePipe),
            ('=', '=', Kind::EqEq),
            ('!', '=', Kind::Ne),
            ('<', '=', Kind::Le),
            ('>', '=', Kind::Ge),
        ];
        for (first, second, kind) in pairs {
            if c == first && self.peek() == Some(second) {
                self.bump();
                return Ok(kind);
            }
        }
        Ok(match c {
            '(' => Kind::LParen,
            ')' => Kind::RParen,
            '{' => Kind::LBrace,
            '}' => Kind::RBrace,
            '[' => Kind::LBracket,
            ']' => Kind::RBracket,
            ',' => Kind::Comma,
            ';' => Kind::Semi,
            ':' => Kind::Colon,
            '.' => Kind::Dot,
            '#' => Kind::Hash,
            '@' => Kind::At,
            '+' => Kind::Plus,
            '-' => Kind::Minus,
            '*' => Kind::Star,
            '/' => Kind::Slash,
            '%' => Kind::Percent,
            '^' => Kind::Caret,
            '!' => Kind::Bang,
            '&' => Kind::Amp,
            '|' => Kind::Pipe,
            '=' => Kind::Eq,
            '<' => Kind::Lt,
            '>' => Kind::Gt,
            '?' => Kind::Question,
            _ => return Err(self.error(start, format!("unexpected character {c:?}"))),
        })
    }
}
