//! The stable text form of a [`Body`]: `kush mir FILE` prints it, and
//! [`parse`] reads it back to the same body.
//!
//! ```text
//! fn "add_one"(_0: i64) -> i64 {
//!     temp _1: i64;
//!     bb0: {
//!         _1 = Add(copy _0, const 1: i64) @20..25;
//!         return move _1 @20..25;
//!     }
//! }
//! ```
//!
//! Source locals are declared with `let`, temporaries with `temp`, and both
//! may be `mut`. A block that names a cleanup block for its statements'
//! panics says so as `bb3 (unwind bb7):`. Every statement and terminator
//! ends in its source span. `//` starts a comment that runs to the end of
//! the line.

use super::*;
use crate::float::FloatKind;
use std::fmt::Write;

pub(crate) fn print(body: &Body) -> String {
    let mut out = String::new();
    let parameters = (0..body.parameters)
        .map(|local| {
            let decl = body.locals[local];
            format!(
                "{}_{local}: {}",
                if decl.mutable { "mut " } else { "" },
                type_name(decl.ty)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        out,
        "fn {:?}({parameters}) -> {} {{",
        body.name,
        type_name(body.result)
    );
    for (local, decl) in body.locals.iter().enumerate().skip(body.parameters) {
        let _ = writeln!(
            out,
            "    {} {}_{local}: {};",
            if decl.temporary { "temp" } else { "let" },
            if decl.mutable { "mut " } else { "" },
            type_name(decl.ty)
        );
    }
    for (index, block) in body.blocks.iter().enumerate() {
        match block.unwind {
            Some(unwind) => {
                let _ = writeln!(out, "    bb{index} (unwind bb{unwind}): {{");
            }
            None => {
                let _ = writeln!(out, "    bb{index}: {{");
            }
        }
        for statement in &block.statements {
            let StatementKind::Assign(local, rvalue) = &statement.kind;
            let _ = writeln!(
                out,
                "        _{local} = {} {};",
                rvalue_text(rvalue),
                span(statement.span)
            );
        }
        let _ = writeln!(
            out,
            "        {} {};",
            terminator_text(&block.terminator.kind),
            span(block.terminator.span)
        );
        out.push_str("    }\n");
    }
    out.push_str("}\n");
    out
}

fn span(span: Span) -> String {
    format!("@{}..{}", span.start, span.end)
}

fn type_name(ty: Type) -> String {
    match ty {
        Type::I64 => "i64".into(),
        Type::Int(kind) => kind.name().into(),
        Type::Float(kind) => kind.name().into(),
        Type::Char => "char".into(),
        Type::Bool => "bool".into(),
        Type::Unit => "unit".into(),
        Type::Never => "never".into(),
        other => format!("?{other:?}"),
    }
}

fn operand_text(operand: Operand) -> String {
    match operand {
        Operand::Copy(local) => format!("copy _{local}"),
        Operand::Move(local) => format!("move _{local}"),
        Operand::Constant(value, ty) => format!("const {value}: {}", type_name(ty)),
    }
}

fn rvalue_text(rvalue: &Rvalue) -> String {
    match rvalue {
        Rvalue::Use(operand) => operand_text(*operand),
        Rvalue::Unary(op, operand) => format!("{}({})", op.name(), operand_text(*operand)),
        Rvalue::Binary(op, left, right) => format!(
            "{}({}, {})",
            op.name(),
            operand_text(*left),
            operand_text(*right)
        ),
        Rvalue::Int(op, source, target, operands) => format!(
            "int {} {} {}({})",
            int_op_name(*op).unwrap_or_else(|| format!("?{op:?}")),
            source.name(),
            target.name(),
            operands
                .iter()
                .map(|operand| operand_text(*operand))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn unwind_text(unwind: Option<BlockId>) -> String {
    match unwind {
        Some(block) => format!("unwind bb{block}"),
        None => "unwind continue".into(),
    }
}

fn terminator_text(kind: &TerminatorKind) -> String {
    match kind {
        TerminatorKind::Goto(target) => format!("goto bb{target}"),
        TerminatorKind::Switch {
            value,
            targets,
            otherwise,
        } => {
            let targets = targets
                .iter()
                .map(|(value, target)| format!("{value} -> bb{target}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "switch {} [{targets}] otherwise bb{otherwise}",
                operand_text(*value)
            )
        }
        TerminatorKind::Call {
            callee,
            args,
            destination,
            next,
            unwind,
        } => {
            let callee = match callee {
                Callee::Function(index) => format!("fn {index}"),
                Callee::PrintInt(kind) => format!("print_int {}", kind.name()),
            };
            let args = args
                .iter()
                .map(|operand| operand_text(*operand))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "_{destination} = call {callee}({args}) -> bb{next} {}",
                unwind_text(*unwind)
            )
        }
        TerminatorKind::Return(operand) => format!("return {}", operand_text(*operand)),
        TerminatorKind::Panic { unwind } => format!("panic {}", unwind_text(*unwind)),
        TerminatorKind::Unreachable => "unreachable".into(),
    }
}

/// Read one body in the text form back.
pub(crate) fn parse(text: &str) -> Result<Body, String> {
    let mut parser = Parser {
        tokens: tokens(text)?,
        at: 0,
    };
    let body = parser.body()?;
    if parser.at != parser.tokens.len() {
        return Err(format!("unexpected '{}' after the body", parser.tokens[parser.at]));
    }
    Ok(body)
}

fn tokens(text: &str) -> Result<Vec<String>, String> {
    let mut tokens = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((start, c)) = chars.next() {
        if c.is_whitespace() {
            continue;
        }
        if c == '/' && chars.peek().is_some_and(|(_, next)| *next == '/') {
            for (_, c) in chars.by_ref() {
                if c == '\n' {
                    break;
                }
            }
            continue;
        }
        if c == '"' {
            let mut end = None;
            let mut escaped = false;
            for (index, c) in chars.by_ref() {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    end = Some(index);
                    break;
                }
            }
            let end = end.ok_or("an unterminated string")?;
            tokens.push(text[start..=end].to_string());
            continue;
        }
        if c == '-' && chars.peek().is_some_and(|(_, next)| *next == '>') {
            chars.next();
            tokens.push("->".into());
            continue;
        }
        if c == '.' && chars.peek().is_some_and(|(_, next)| *next == '.') {
            chars.next();
            tokens.push("..".into());
            continue;
        }
        let word = |c: char| c.is_alphanumeric() || c == '_' || c == '-';
        if word(c) {
            let mut end = start + c.len_utf8();
            while let Some((index, c)) = chars.peek().copied() {
                // `-` only starts a word: `5-` is never written.
                if !word(c) || c == '-' {
                    break;
                }
                end = index + c.len_utf8();
                chars.next();
            }
            tokens.push(text[start..end].to_string());
            continue;
        }
        tokens.push(c.to_string());
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<String>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.at).map(String::as_str)
    }
    fn next(&mut self) -> Result<String, String> {
        let token = self
            .tokens
            .get(self.at)
            .cloned()
            .ok_or("unexpected end of text")?;
        self.at += 1;
        Ok(token)
    }
    fn expect(&mut self, token: &str) -> Result<(), String> {
        let found = self.next()?;
        if found == token {
            Ok(())
        } else {
            Err(format!("expected '{token}', found '{found}'"))
        }
    }
    fn eat(&mut self, token: &str) -> bool {
        if self.peek() == Some(token) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn number<T: std::str::FromStr>(&mut self) -> Result<T, String> {
        let token = self.next()?;
        token
            .parse()
            .map_err(|_| format!("expected a number, found '{token}'"))
    }
    fn prefixed(&mut self, prefix: &str) -> Result<usize, String> {
        let token = self.next()?;
        token
            .strip_prefix(prefix)
            .and_then(|rest| rest.parse().ok())
            .ok_or_else(|| format!("expected '{prefix}N', found '{token}'"))
    }
    fn local(&mut self) -> Result<LocalId, String> {
        self.prefixed("_")
    }
    fn block_id(&mut self) -> Result<BlockId, String> {
        self.prefixed("bb")
    }
    fn ty(&mut self) -> Result<Type, String> {
        let name = self.next()?;
        Ok(match name.as_str() {
            "i64" => Type::I64,
            "f32" => Type::Float(FloatKind::F32),
            "f64" => Type::Float(FloatKind::F64),
            "char" => Type::Char,
            "bool" => Type::Bool,
            "unit" => Type::Unit,
            "never" => Type::Never,
            other => match IntKind::named(other) {
                Some(kind) => Type::int(kind),
                None => return Err(format!("unknown type '{other}'")),
            },
        })
    }
    fn int_kind(&mut self) -> Result<IntKind, String> {
        let name = self.next()?;
        IntKind::named(&name).ok_or_else(|| format!("unknown integer type '{name}'"))
    }
    fn span(&mut self) -> Result<Span, String> {
        self.expect("@")?;
        let start = self.number()?;
        self.expect("..")?;
        let end = self.number()?;
        Ok(Span::new(start, end))
    }
    fn body(&mut self) -> Result<Body, String> {
        self.expect("fn")?;
        let name = self.next()?;
        let name = name
            .strip_prefix('"')
            .and_then(|name| name.strip_suffix('"'))
            .ok_or_else(|| format!("expected a quoted name, found '{name}'"))?;
        let name = unescape(name)?;
        let mut locals = Vec::new();
        self.expect("(")?;
        while !self.eat(")") {
            if !locals.is_empty() {
                self.expect(",")?;
            }
            let mutable = self.eat("mut");
            self.declared(locals.len())?;
            self.expect(":")?;
            let ty = self.ty()?;
            locals.push(LocalDecl {
                ty,
                mutable,
                temporary: false,
            });
        }
        let parameters = locals.len();
        self.expect("->")?;
        let result = self.ty()?;
        self.expect("{")?;
        while matches!(self.peek(), Some("let" | "temp")) {
            let temporary = self.next()? == "temp";
            let mutable = self.eat("mut");
            self.declared(locals.len())?;
            self.expect(":")?;
            let ty = self.ty()?;
            self.expect(";")?;
            locals.push(LocalDecl {
                ty,
                mutable,
                temporary,
            });
        }
        let mut blocks = Vec::new();
        while !self.eat("}") {
            let index = self.block_id()?;
            if index != blocks.len() {
                return Err(format!("expected bb{}, found bb{index}", blocks.len()));
            }
            let unwind = if self.eat("(") {
                self.expect("unwind")?;
                let target = self.block_id()?;
                self.expect(")")?;
                Some(target)
            } else {
                None
            };
            self.expect(":")?;
            self.expect("{")?;
            let mut statements = Vec::new();
            let terminator = loop {
                if let Some(terminator) = self.terminator()? {
                    break terminator;
                }
                let local = self.local()?;
                self.expect("=")?;
                let rvalue = self.rvalue()?;
                let span = self.span()?;
                self.expect(";")?;
                statements.push(Statement {
                    kind: StatementKind::Assign(local, rvalue),
                    span,
                });
            };
            self.expect("}")?;
            blocks.push(BasicBlock {
                statements,
                terminator,
                unwind,
            });
        }
        Ok(Body {
            name,
            parameters,
            locals,
            blocks,
            result,
        })
    }
    fn declared(&mut self, expected: usize) -> Result<(), String> {
        let local = self.local()?;
        if local == expected {
            Ok(())
        } else {
            Err(format!("expected _{expected}, found _{local}"))
        }
    }
    fn operand(&mut self) -> Result<Operand, String> {
        match self.next()?.as_str() {
            "copy" => Ok(Operand::Copy(self.local()?)),
            "move" => Ok(Operand::Move(self.local()?)),
            "const" => {
                let value = self.number()?;
                self.expect(":")?;
                Ok(Operand::Constant(value, self.ty()?))
            }
            other => Err(format!("expected an operand, found '{other}'")),
        }
    }
    fn rvalue(&mut self) -> Result<Rvalue, String> {
        let Some(name) = self.peek() else {
            return Err("unexpected end of text".into());
        };
        if name == "int" {
            self.at += 1;
            let op = self.next()?;
            let op = int_op_named(&op).ok_or_else(|| format!("unknown integer builtin '{op}'"))?;
            let source = self.int_kind()?;
            let target = self.int_kind()?;
            self.expect("(")?;
            let mut operands = Vec::new();
            while !self.eat(")") {
                if !operands.is_empty() {
                    self.expect(",")?;
                }
                operands.push(self.operand()?);
            }
            return Ok(Rvalue::Int(op, source, target, operands));
        }
        if let Some(op) = UnOp::ALL.into_iter().find(|op| op.name() == name) {
            self.at += 1;
            self.expect("(")?;
            let operand = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::Unary(op, operand));
        }
        if let Some(op) = BinOp::ALL.into_iter().find(|op| op.name() == name) {
            self.at += 1;
            self.expect("(")?;
            let left = self.operand()?;
            self.expect(",")?;
            let right = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::Binary(op, left, right));
        }
        Ok(Rvalue::Use(self.operand()?))
    }
    fn unwind(&mut self) -> Result<Option<BlockId>, String> {
        self.expect("unwind")?;
        if self.eat("continue") {
            Ok(None)
        } else {
            Ok(Some(self.block_id()?))
        }
    }
    /// A terminator, or `None` when the next tokens start a statement.
    fn terminator(&mut self) -> Result<Option<Terminator>, String> {
        let kind = match self.peek() {
            Some("goto") => {
                self.at += 1;
                TerminatorKind::Goto(self.block_id()?)
            }
            Some("switch") => {
                self.at += 1;
                let value = self.operand()?;
                self.expect("[")?;
                let mut targets = Vec::new();
                while !self.eat("]") {
                    if !targets.is_empty() {
                        self.expect(",")?;
                    }
                    let value = self.number()?;
                    self.expect("->")?;
                    targets.push((value, self.block_id()?));
                }
                self.expect("otherwise")?;
                TerminatorKind::Switch {
                    value,
                    targets,
                    otherwise: self.block_id()?,
                }
            }
            Some("return") => {
                self.at += 1;
                TerminatorKind::Return(self.operand()?)
            }
            Some("panic") => {
                self.at += 1;
                TerminatorKind::Panic {
                    unwind: self.unwind()?,
                }
            }
            Some("unreachable") => {
                self.at += 1;
                TerminatorKind::Unreachable
            }
            Some(_) if self.tokens.get(self.at + 2).is_some_and(|t| t == "call") => {
                let destination = self.local()?;
                self.expect("=")?;
                self.expect("call")?;
                let callee = match self.next()?.as_str() {
                    "fn" => Callee::Function(self.number()?),
                    "print_int" => {
                        let name = self.next()?;
                        Callee::PrintInt(
                            IntKind::named(&name)
                                .ok_or_else(|| format!("unknown integer type '{name}'"))?,
                        )
                    }
                    other => return Err(format!("unknown callee '{other}'")),
                };
                self.expect("(")?;
                let mut args = Vec::new();
                while !self.eat(")") {
                    if !args.is_empty() {
                        self.expect(",")?;
                    }
                    args.push(self.operand()?);
                }
                self.expect("->")?;
                let next = self.block_id()?;
                let unwind = self.unwind()?;
                TerminatorKind::Call {
                    callee,
                    args,
                    destination,
                    next,
                    unwind,
                }
            }
            _ => return Ok(None),
        };
        let span = self.span()?;
        self.expect(";")?;
        Ok(Some(Terminator { kind, span }))
    }
}

/// Undo the escapes `{:?}` writes in a function name.
fn unescape(text: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('\'') => out.push('\''),
            other => return Err(format!("unsupported escape '\\{}'", other.unwrap_or(' '))),
        }
    }
    Ok(out)
}
