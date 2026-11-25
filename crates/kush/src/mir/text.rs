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
    // Builtins and coercions are data with many shapes; their JSON form
    // is exact and stable, written as one string.
    for (index, target) in body.builtins.0.iter().enumerate() {
        let json = serde_json::to_string(target).expect("a builtin serializes");
        let _ = writeln!(out, "    builtin {index} = {json:?};");
    }
    for (index, coercion) in body.coercions.0.iter().enumerate() {
        let json = serde_json::to_string(coercion).expect("a coercion serializes");
        let _ = writeln!(out, "    coercion {index} = {json:?};");
    }
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
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            let _ = writeln!(
                out,
                "        {} = {} {};",
                place_text(*place),
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

/// Types without a payload, by text name.
const PLAIN_TYPES: [(&str, Type); 15] = [
    ("i64", Type::I64),
    ("char", Type::Char),
    ("bool", Type::Bool),
    ("unit", Type::Unit),
    ("never", Type::Never),
    ("bytes", Type::Bytes),
    ("string", Type::String),
    ("str", Type::Str),
    ("strmut", Type::StrMut),
    ("stdin", Type::Stdin),
    ("stdout", Type::Stdout),
    ("atomic", Type::Atomic),
    ("arena", Type::Arena),
    ("allocator", Type::Allocator),
    ("allocator_context", Type::AllocatorContext),
];

/// Types with one table index (a layout, pointee or signature), written
/// `name#index`. [`indexed_type`] is the inverse.
fn type_index(ty: Type) -> Option<(&'static str, usize)> {
    Some(match ty {
        Type::Enum(id) => ("enum", id),
        Type::Union(id) => ("union", id),
        Type::DynObj(id) => ("dyn", id),
        Type::Box(id) => ("box", id),
        Type::Vec(id) => ("vec", id),
        Type::Ref(id) => ("ref", id),
        Type::RefMut(id) => ("refmut", id),
        Type::Slice(id) => ("slice", id),
        Type::SliceMut(id) => ("slicemut", id),
        Type::Fn(id) => ("fn", id),
        Type::Once(id) => ("once", id),
        Type::Multi(id) => ("multi", id),
        Type::Task(id) => ("task", id),
        Type::Channel(id) => ("channel", id),
        Type::Thread(id) => ("thread", id),
        Type::ArenaBox(id) => ("arena_box", id),
        Type::AllocBox(id) => ("alloc_box", id),
        Type::AllocVec(id) => ("alloc_vec", id),
        Type::GpuBuf(id) => ("gpu_buf", id),
        _ => return None,
    })
}

fn indexed_type(name: &str, id: usize) -> Option<Type> {
    Some(match name {
        "enum" => Type::Enum(id),
        "union" => Type::Union(id),
        "dyn" => Type::DynObj(id),
        "box" => Type::Box(id),
        "vec" => Type::Vec(id),
        "ref" => Type::Ref(id),
        "refmut" => Type::RefMut(id),
        "slice" => Type::Slice(id),
        "slicemut" => Type::SliceMut(id),
        "fn" => Type::Fn(id),
        "once" => Type::Once(id),
        "multi" => Type::Multi(id),
        "task" => Type::Task(id),
        "channel" => Type::Channel(id),
        "thread" => Type::Thread(id),
        "arena_box" => Type::ArenaBox(id),
        "alloc_box" => Type::AllocBox(id),
        "alloc_vec" => Type::AllocVec(id),
        "gpu_buf" => Type::GpuBuf(id),
        _ => return None,
    })
}

fn type_name(ty: Type) -> String {
    if let Some((name, _)) = PLAIN_TYPES.iter().find(|(_, plain)| *plain == ty) {
        return (*name).into();
    }
    if let Some((name, id)) = type_index(ty) {
        return format!("{name}#{id}");
    }
    match ty {
        Type::Int(kind) => kind.name().into(),
        Type::Float(kind) => kind.name().into(),
        Type::Variants(id, mask) => format!("variants#{id}#{mask}"),
        Type::Annotated(pointee, annotation) => format!("annotated#{pointee}#{annotation}"),
        other => unreachable!("every type has a text name: {other:?}"),
    }
}

fn place_text(place: Place) -> String {
    let deref = if place.deref { "*" } else { "" };
    match place.field {
        Some(field) => format!(
            "{deref}_{}.{}:{}",
            place.local,
            field.offset,
            type_name(field.ty)
        ),
        None => format!("{deref}_{}", place.local),
    }
}

fn operands_text(operands: &[Operand]) -> String {
    operands
        .iter()
        .map(|operand| operand_text(*operand))
        .collect::<Vec<_>>()
        .join(", ")
}

fn operand_text(operand: Operand) -> String {
    match operand {
        Operand::Copy(place) => format!("copy {}", place_text(place)),
        Operand::Move(place) => format!("move {}", place_text(place)),
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
            operands_text(operands)
        ),
        Rvalue::Aggregate(ty, tag, operands) => format!(
            "aggregate {} {tag}({})",
            type_name(*ty),
            operands_text(operands)
        ),
        Rvalue::BoxNew(operand) => format!("box_new({})", operand_text(*operand)),
        Rvalue::BoxTake(operand) => format!("box_take({})", operand_text(*operand)),
        Rvalue::Ref(place) => format!("&{}", place_text(*place)),
        Rvalue::ElementAddress(base, index) => match base {
            ElementBase::Slice(view) => {
                format!(
                    "element slice {}[{}]",
                    operand_text(*view),
                    operand_text(*index)
                )
            }
            ElementBase::Stored(place) => {
                format!(
                    "element stored {}[{}]",
                    place_text(*place),
                    operand_text(*index)
                )
            }
        },
        Rvalue::ByteAt(handle, index) => format!(
            "byte_at({}, {})",
            operand_text(*handle),
            operand_text(*index)
        ),
        Rvalue::Buffer(vector, word) => format!(
            "buffer {}({})",
            match word {
                BufferWord::Length => "length",
                BufferWord::Capacity => "capacity",
            },
            operand_text(*vector)
        ),
        Rvalue::StructEq(left, right, negated) => format!(
            "{}({}, {})",
            if *negated { "struct_ne" } else { "struct_eq" },
            operand_text(*left),
            operand_text(*right)
        ),
        Rvalue::Coerce(operand, index) => format!("coerce {index}({})", operand_text(*operand)),
        Rvalue::FnValue { function, captures } => {
            let captures = captures
                .iter()
                .map(|capture| match capture {
                    Capture::Value(operand) => operand_text(*operand),
                    Capture::Address(local) => format!("addr _{local}"),
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("fn_value {function}({captures})")
        }
        Rvalue::View {
            source,
            start,
            end,
            element,
            check,
            text,
        } => {
            let bound = |operand: &Option<Operand>| operand.map_or("none".into(), operand_text);
            let source = match source {
                ViewSource::Array(local) => format!("array _{local}"),
                ViewSource::Value(operand) => format!("value {}", operand_text(*operand)),
                ViewSource::DynArray(place) => format!("dynarray {}", place_text(*place)),
            };
            format!(
                "view{}{} {source} [{} .. {}] of {}",
                if *check { " check" } else { "" },
                if *text { " text" } else { "" },
                bound(start),
                bound(end),
                type_name(*element)
            )
        }
        Rvalue::Alloc(op, operands) => {
            let json = serde_json::to_string(op).expect("an allocator operation serializes");
            format!("alloc {json:?}({})", operands_text(operands))
        }
        Rvalue::Array(op, operands) => {
            let json = serde_json::to_string(op).expect("an array operation serializes");
            format!("array {json:?}({})", operands_text(operands))
        }
        Rvalue::Map(op, operands) => {
            let json = serde_json::to_string(op).expect("a map operation serializes");
            format!("map {json:?}({})", operands_text(operands))
        }
        Rvalue::Runtime(op, operands) => {
            let json = serde_json::to_string(op).expect("a runtime operation serializes");
            format!("runtime {json:?}({})", operands_text(operands))
        }
        Rvalue::Task(op, operands) => {
            let json = serde_json::to_string(op).expect("a task operation serializes");
            format!("task {json:?}({})", operands_text(operands))
        }
        Rvalue::Bytes(bytes) => {
            let hex = bytes
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            format!("bytes \"{hex}\"")
        }
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
                Callee::Builtin { index, hint } => {
                    let hint = match hint {
                        CallHint::None => String::new(),
                        CallHint::Below => " below".into(),
                        CallHint::Shadow(length, capacity) => {
                            format!(" shadow _{length} _{capacity}")
                        }
                    };
                    format!("builtin {index}{hint}")
                }
                Callee::Indirect(operand) => format!("indirect {}", operand_text(*operand)),
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
        TerminatorKind::Drop {
            place,
            next,
            unwind,
        } => format!(
            "drop {} -> bb{next} {}",
            place_text(*place),
            unwind_text(*unwind)
        ),
        TerminatorKind::Resume => "resume".into(),
        TerminatorKind::Abort => "abort".into(),
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
        return Err(format!(
            "unexpected '{}' after the body",
            parser.tokens[parser.at]
        ));
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
        if let Some((_, ty)) = PLAIN_TYPES.iter().find(|(plain, _)| *plain == name) {
            return Ok(*ty);
        }
        if name == "f32" || name == "f64" {
            let kind = if name == "f32" {
                FloatKind::F32
            } else {
                FloatKind::F64
            };
            return Ok(Type::Float(kind));
        }
        if let Some(kind) = IntKind::named(&name) {
            return Ok(Type::int(kind));
        }
        if !self.eat("#") {
            return Err(format!("unknown type '{name}'"));
        }
        let id = self.number()?;
        match name.as_str() {
            "variants" => {
                self.expect("#")?;
                Ok(Type::Variants(id, self.number()?))
            }
            "annotated" => {
                self.expect("#")?;
                Ok(Type::Annotated(id, self.number()?))
            }
            other => indexed_type(other, id).ok_or_else(|| format!("unknown type '{other}'")),
        }
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
        let mut builtins = Vec::new();
        let mut coercions = Vec::new();
        while matches!(self.peek(), Some("builtin" | "coercion")) {
            let builtin = self.next()? == "builtin";
            let index = self.number::<usize>()?;
            let expected = if builtin {
                builtins.len()
            } else {
                coercions.len()
            };
            if index != expected {
                return Err(format!("expected entry {expected}, found {index}"));
            }
            self.expect("=")?;
            let json = self.string()?;
            if builtin {
                builtins.push(
                    serde_json::from_str(&json).map_err(|e| format!("builtin {index}: {e}"))?,
                );
            } else {
                coercions.push(
                    serde_json::from_str(&json).map_err(|e| format!("coercion {index}: {e}"))?,
                );
            }
            self.expect(";")?;
        }
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
                let place = self.place()?;
                self.expect("=")?;
                let rvalue = self.rvalue()?;
                let span = self.span()?;
                self.expect(";")?;
                statements.push(Statement {
                    kind: StatementKind::Assign(place, rvalue),
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
            builtins: Builtins(builtins),
            coercions: Coercions(coercions),
        })
    }
    /// A quoted string token, unescaped.
    fn string(&mut self) -> Result<String, String> {
        let token = self.next()?;
        let inner = token
            .strip_prefix('"')
            .and_then(|token| token.strip_suffix('"'))
            .ok_or_else(|| format!("expected a string, found '{token}'"))?;
        unescape(inner)
    }
    fn declared(&mut self, expected: usize) -> Result<(), String> {
        let local = self.local()?;
        if local == expected {
            Ok(())
        } else {
            Err(format!("expected _{expected}, found _{local}"))
        }
    }
    fn place(&mut self) -> Result<Place, String> {
        let deref = self.eat("*");
        let local = self.local()?;
        let field = if self.eat(".") {
            let offset = self.number()?;
            self.expect(":")?;
            Some(Field {
                offset,
                ty: self.ty()?,
            })
        } else {
            None
        };
        if deref && field.is_none() {
            return Err(format!("the deref place *_{local} names no field"));
        }
        Ok(Place {
            local,
            deref,
            field,
        })
    }
    fn operands(&mut self) -> Result<Vec<Operand>, String> {
        self.expect("(")?;
        let mut operands = Vec::new();
        while !self.eat(")") {
            if !operands.is_empty() {
                self.expect(",")?;
            }
            operands.push(self.operand()?);
        }
        Ok(operands)
    }
    fn operand(&mut self) -> Result<Operand, String> {
        match self.next()?.as_str() {
            "copy" => Ok(Operand::Copy(self.place()?)),
            "move" => Ok(Operand::Move(self.place()?)),
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
            return Ok(Rvalue::Int(op, source, target, self.operands()?));
        }
        if let Some(op) = ["box_new", "box_take"].into_iter().find(|op| *op == name) {
            self.at += 1;
            self.expect("(")?;
            let operand = self.operand()?;
            self.expect(")")?;
            return Ok(if op == "box_new" {
                Rvalue::BoxNew(operand)
            } else {
                Rvalue::BoxTake(operand)
            });
        }
        if name == "bytes" {
            self.at += 1;
            let text = self.next()?;
            let hex = text
                .strip_prefix('"')
                .and_then(|text| text.strip_suffix('"'))
                .ok_or_else(|| format!("expected quoted hex bytes, found '{text}'"))?;
            if hex.len() % 2 != 0 {
                return Err(format!("odd-length hex bytes '{hex}'"));
            }
            let bytes = (0..hex.len())
                .step_by(2)
                .map(|at| u8::from_str_radix(&hex[at..at + 2], 16))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| format!("invalid hex bytes '{hex}'"))?;
            return Ok(Rvalue::Bytes(bytes));
        }
        if name == "element" {
            self.at += 1;
            let base = match self.next()?.as_str() {
                "slice" => ElementBase::Slice(self.operand()?),
                "stored" => ElementBase::Stored(self.place()?),
                other => return Err(format!("expected an element base, found '{other}'")),
            };
            self.expect("[")?;
            let index = self.operand()?;
            self.expect("]")?;
            return Ok(Rvalue::ElementAddress(base, index));
        }
        if name == "alloc" {
            self.at += 1;
            let json = self.string()?;
            let op =
                serde_json::from_str(&json).map_err(|e| format!("allocator operation: {e}"))?;
            return Ok(Rvalue::Alloc(op, self.operands()?));
        }
        if name == "array" {
            self.at += 1;
            let json = self.string()?;
            let op = serde_json::from_str(&json).map_err(|e| format!("array operation: {e}"))?;
            return Ok(Rvalue::Array(op, self.operands()?));
        }
        if name == "map" {
            self.at += 1;
            let json = self.string()?;
            let op = serde_json::from_str(&json).map_err(|e| format!("map operation: {e}"))?;
            return Ok(Rvalue::Map(op, self.operands()?));
        }
        if name == "runtime" {
            self.at += 1;
            let json = self.string()?;
            let op = serde_json::from_str(&json).map_err(|e| format!("runtime operation: {e}"))?;
            return Ok(Rvalue::Runtime(op, self.operands()?));
        }
        if name == "task" {
            self.at += 1;
            let json = self.string()?;
            let op = serde_json::from_str(&json).map_err(|e| format!("task operation: {e}"))?;
            return Ok(Rvalue::Task(op, self.operands()?));
        }
        if name == "byte_at" {
            self.at += 1;
            self.expect("(")?;
            let handle = self.operand()?;
            self.expect(",")?;
            let index = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::ByteAt(handle, index));
        }
        if name == "buffer" {
            self.at += 1;
            let word = match self.next()?.as_str() {
                "length" => BufferWord::Length,
                "capacity" => BufferWord::Capacity,
                other => return Err(format!("expected a buffer word, found '{other}'")),
            };
            self.expect("(")?;
            let vector = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::Buffer(vector, word));
        }
        if name == "struct_eq" || name == "struct_ne" {
            let negated = name == "struct_ne";
            self.at += 1;
            self.expect("(")?;
            let left = self.operand()?;
            self.expect(",")?;
            let right = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::StructEq(left, right, negated));
        }
        if name == "coerce" {
            self.at += 1;
            let index = self.number()?;
            self.expect("(")?;
            let operand = self.operand()?;
            self.expect(")")?;
            return Ok(Rvalue::Coerce(operand, index));
        }
        if name == "fn_value" {
            self.at += 1;
            let function = self.number()?;
            self.expect("(")?;
            let mut captures = Vec::new();
            while !self.eat(")") {
                if !captures.is_empty() {
                    self.expect(",")?;
                }
                captures.push(if self.eat("addr") {
                    Capture::Address(self.local()?)
                } else {
                    Capture::Value(self.operand()?)
                });
            }
            return Ok(Rvalue::FnValue { function, captures });
        }
        if name == "view" {
            self.at += 1;
            let check = self.eat("check");
            let text = self.eat("text");
            let source = match self.next()?.as_str() {
                "array" => ViewSource::Array(self.local()?),
                "value" => ViewSource::Value(self.operand()?),
                "dynarray" => ViewSource::DynArray(self.place()?),
                other => return Err(format!("expected a view source, found '{other}'")),
            };
            self.expect("[")?;
            let start = if self.eat("none") {
                None
            } else {
                Some(self.operand()?)
            };
            self.expect("..")?;
            let end = if self.eat("none") {
                None
            } else {
                Some(self.operand()?)
            };
            self.expect("]")?;
            self.expect("of")?;
            let element = self.ty()?;
            return Ok(Rvalue::View {
                source,
                start,
                end,
                element,
                check,
                text,
            });
        }
        if name == "&" {
            self.at += 1;
            return Ok(Rvalue::Ref(self.place()?));
        }
        if name == "aggregate" {
            self.at += 1;
            let ty = self.ty()?;
            let tag = self.number()?;
            return Ok(Rvalue::Aggregate(ty, tag, self.operands()?));
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
            Some("resume") => {
                self.at += 1;
                TerminatorKind::Resume
            }
            Some("abort") => {
                self.at += 1;
                TerminatorKind::Abort
            }
            Some("drop") => {
                self.at += 1;
                let place = self.place()?;
                self.expect("->")?;
                let next = self.block_id()?;
                TerminatorKind::Drop {
                    place,
                    next,
                    unwind: self.unwind()?,
                }
            }
            Some(_) if self.tokens.get(self.at + 2).is_some_and(|t| t == "call") => {
                let destination = self.local()?;
                self.expect("=")?;
                self.expect("call")?;
                let callee = match self.next()?.as_str() {
                    "fn" => Callee::Function(self.number()?),
                    "builtin" => Callee::Builtin {
                        index: self.number()?,
                        hint: if self.eat("below") {
                            CallHint::Below
                        } else if self.eat("shadow") {
                            CallHint::Shadow(self.local()?, self.local()?)
                        } else {
                            CallHint::None
                        },
                    },
                    "indirect" => Callee::Indirect(self.operand()?),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_type_kind_reads_back_from_its_name() {
        let mut types = PLAIN_TYPES.iter().map(|(_, ty)| *ty).collect::<Vec<_>>();
        types.extend([
            Type::int(IntKind::U8),
            Type::Float(FloatKind::F32),
            Type::Variants(3, 5),
            Type::Annotated(2, 7),
        ]);
        for name in [
            "enum",
            "union",
            "dyn",
            "box",
            "vec",
            "ref",
            "refmut",
            "slice",
            "slicemut",
            "fn",
            "once",
            "multi",
            "task",
            "channel",
            "thread",
            "arena_box",
            "alloc_box",
            "alloc_vec",
            "gpu_buf",
        ] {
            let ty = indexed_type(name, 4).unwrap();
            assert_eq!(type_index(ty), Some((name, 4)));
            types.push(ty);
        }
        for ty in types {
            let text = type_name(ty);
            let mut parser = Parser {
                tokens: tokens(&text).unwrap(),
                at: 0,
            };
            assert_eq!(parser.ty(), Ok(ty), "{text}");
        }
    }
}
