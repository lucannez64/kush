use crate::{
    Diagnostic, Span,
    ast::*,
    lexer::{self, Kind, Token},
};
use std::mem::discriminant;

type Result<T> = std::result::Result<T, Diagnostic>;
const LIMIT: usize = 128;

/// Parse syntax only. This does not resolve names, check types, or verify proofs.
pub fn parse(source: &str) -> Result<Module> {
    parse_at(source, 0)
}

/// Parse one file whose text starts at `base` in a program-wide source map.
/// Every span in the result (and in a returned diagnostic) is shifted by `base`.
pub fn parse_at(source: &str, base: usize) -> Result<Module> {
    let shift = |mut d: Diagnostic| {
        d.span = Span::new(d.span.start + base, d.span.end + base);
        d
    };
    let mut tokens = lexer::lex(source).map_err(shift)?;
    for token in &mut tokens {
        token.span = Span::new(token.span.start + base, token.span.end + base);
    }
    Parser {
        tokens,
        pos: 0,
        depth: 0,
    }
    .module()
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    depth: usize,
}
impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }
    fn at(&self, kind: &Kind) -> bool {
        discriminant(&self.current().kind) == discriminant(kind)
    }
    fn bump(&mut self) -> Token {
        let token = self.current().clone();
        if !self.at(&Kind::Eof) {
            self.pos += 1;
        }
        token
    }
    fn eat(&mut self, kind: &Kind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, kind: &Kind, label: &str) -> Result<Token> {
        if self.at(kind) {
            Ok(self.bump())
        } else {
            Err(self.error(format!("expected {label}, found {:?}", self.current().kind)))
        }
    }
    fn error(&self, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(self.current().span, message)
    }
    fn since(&self, start: Span) -> Span {
        start.through(self.tokens[self.pos.saturating_sub(1)].span)
    }
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= LIMIT {
            return Err(self.error("syntax nesting limit exceeded (128)"));
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    fn ident(&mut self) -> Result<String> {
        match self.current().kind.clone() {
            Kind::Ident(name) => {
                self.bump();
                Ok(name)
            }
            _ => Err(self.error("expected an identifier")),
        }
    }
    /// The `prop` declaration keyword is contextual, so existing code may still
    /// use `prop` as an ordinary identifier or module-path segment.
    fn prop_keyword(&self) -> bool {
        matches!(&self.current().kind, Kind::Ident(name) if name == "prop")
    }
    /// Contextual declaration words such as `trait` and `impl`. They remain
    /// ordinary identifiers everywhere else.
    fn word_keyword(&self, word: &str) -> bool {
        matches!(&self.current().kind, Kind::Ident(name) if name == word)
    }
    fn path(&mut self) -> Result<Vec<String>> {
        let mut parts = vec![self.ident()?];
        while self.eat(&Kind::Dot) {
            parts.push(self.ident()?);
        }
        Ok(parts)
    }
    fn separated<T>(
        &mut self,
        end: Kind,
        mut f: impl FnMut(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        let mut out = Vec::new();
        while !self.at(&end) {
            out.push(f(self)?);
            if !self.eat(&Kind::Comma) {
                break;
            }
        }
        self.expect(&end, &format!("{end:?}"))?;
        Ok(out)
    }
    fn module(&mut self) -> Result<Module> {
        let mut items = Vec::new();
        while !self.at(&Kind::Eof) {
            let mut attributes = Vec::new();
            while self.eat(&Kind::Hash) {
                let start = self.tokens[self.pos - 1].span;
                self.expect(&Kind::LBracket, "'[' after '#'")?;
                let name = self.ident()?;
                let argument = if self.eat(&Kind::LParen) {
                    let value = match self.current().kind.clone() {
                        Kind::String(value) => {
                            self.bump();
                            value
                        }
                        _ => {
                            return Err(
                                self.error("attribute arguments must be one string literal")
                            );
                        }
                    };
                    self.expect(&Kind::RParen, "')' after an attribute argument")?;
                    Some(value)
                } else {
                    None
                };
                self.expect(&Kind::RBracket, "']' after attribute name")?;
                attributes.push(Attribute {
                    kind: name,
                    argument,
                    span: self.since(start),
                });
            }
            let public = self.eat(&Kind::Pub);
            let start = self.current().span;
            let total = self.eat(&Kind::Total);
            // `foreign "symbol" fn name(...) -> T ! { ... };` is contextual so
            // `foreign` remains an ordinary identifier elsewhere. The string is
            // the exact C symbol and is not re-derived from the Kush name.
            let kind = if self.word_keyword("foreign")
                && self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|token| matches!(token.kind, Kind::String(_)))
            {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                let symbol = match self.current().kind.clone() {
                    Kind::String(symbol) => {
                        self.bump();
                        symbol
                    }
                    _ => unreachable!("checked above"),
                };
                self.expect(&Kind::Fn, "'fn' after a foreign symbol")?;
                let mut function = self.function(false)?;
                if function.body.is_some() {
                    return Err(Diagnostic::new(
                        self.since(start),
                        "a foreign declaration has no body; replace '{ ... }' with ';'",
                    ));
                }
                function.foreign = Some(symbol);
                ItemKind::Function(function)
            } else if self.eat(&Kind::Fn) {
                ItemKind::Function(self.function(total)?)
            } else if self.eat(&Kind::Module) {
                let path = self.path()?;
                self.expect(&Kind::Semi, "';' after module path")?;
                ItemKind::Module(path)
            } else if self.eat(&Kind::Use) {
                let path = self.path()?;
                self.expect(&Kind::Semi, "';' after import")?;
                ItemKind::Use(path)
            } else if self.word_keyword("trait") {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                let (name, generics, associated, methods) = self.trait_declaration()?;
                ItemKind::Trait {
                    name,
                    generics,
                    associated,
                    methods,
                }
            } else if self.word_keyword("effect") {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                if self.word_keyword("row") {
                    self.bump();
                    let name = self.ident()?;
                    self.expect(&Kind::Eq, "'=' in an effect row alias")?;
                    self.expect(&Kind::LBrace, "'{' before an effect row alias body")?;
                    let effects = self.separated(Kind::RBrace, |p| p.ty())?;
                    self.expect(&Kind::Semi, "';' after an effect row alias")?;
                    ItemKind::EffectRow { name, effects }
                } else {
                    let name = self.ident()?;
                    self.expect(&Kind::Colon, "':' after the effect operation name")?;
                    let parameter = self.ty()?;
                    self.expect(&Kind::Arrow, "'->' in an effect operation signature")?;
                    let result = self.ty()?;
                    self.expect(&Kind::Semi, "';' after an effect declaration")?;
                    ItemKind::Effect {
                        name,
                        parameter,
                        result,
                    }
                }
            } else if self.word_keyword("impl") {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                let (generics, trait_path, self_ty, associated, methods) =
                    self.impl_declaration()?;
                ItemKind::Impl {
                    generics,
                    trait_path,
                    self_ty,
                    associated,
                    methods,
                }
            } else if self.word_keyword("algebra") {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                ItemKind::GradeAlgebra(self.grade_algebra()?)
            } else if self.eat(&Kind::Struct) {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                let name = self.ident()?;
                let (lifetimes, generics) = self.function_generics()?;
                self.expect(&Kind::LBrace, "'{' before record fields")?;
                ItemKind::Struct {
                    name,
                    lifetimes,
                    generics,
                    fields: self.fields()?,
                }
            } else if self.eat(&Kind::Enum) {
                let name = self.ident()?;
                let generics = self.generics()?;
                self.expect(&Kind::LBrace, "'{' before enum variants")?;
                let variants = self.separated(Kind::RBrace, |p| p.variant())?;
                ItemKind::Enum {
                    total,
                    name,
                    generics,
                    variants,
                }
            } else if self.prop_keyword() {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                self.bump();
                let name = self.ident()?;
                let generics = self.generics()?;
                self.expect(&Kind::LBrace, "'{' before proposition constructors")?;
                let variants = self.separated(Kind::RBrace, |p| p.variant())?;
                ItemKind::Prop {
                    name,
                    generics,
                    variants,
                }
            } else if self.eat(&Kind::Type) {
                if total {
                    return Err(self.error("'total' applies only to fn and enum declarations"));
                }
                let name = self.ident()?;
                let (lifetimes, generics) = self.function_generics()?;
                self.expect(&Kind::Eq, "'=' in type alias")?;
                let ty = self.ty()?;
                self.expect(&Kind::Semi, "';' after type alias")?;
                ItemKind::Alias {
                    name,
                    lifetimes,
                    generics,
                    ty,
                }
            } else {
                if total {
                    return Err(self.error("expected 'fn' or 'enum' after 'total'"));
                }
                return Err(self.error("expected a declaration; this frontend supports fn, struct, enum, type, module, and use"));
            };
            items.push(Declaration {
                public,
                attributes,
                item: Node::new(kind, self.since(start)),
            });
        }
        Ok(Module { items })
    }
    fn generics(&mut self) -> Result<Vec<Generic>> {
        if !self.eat(&Kind::Lt) {
            return Ok(Vec::new());
        }
        self.separated(Kind::Gt, |p| p.generic_binder())
    }
    /// One ordinary generic binder: `T`, `N: Nat`, `G: Grade`, `e: Effects`,
    /// or a bounded effect form such as `e: Effects + io - alloc`. The `+` and
    /// `-` lists are parsed here because neither is part of the ordinary type
    /// grammar; the resolver validates that they are attached to a direct
    /// `Effects` binder and name only concrete effects.
    fn generic_binder(&mut self) -> Result<Generic> {
        let start = self.current().span;
        let name = self.ident()?;
        let bound = if self.eat(&Kind::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        let includes = if self.eat(&Kind::Plus) {
            Some(self.ty()?)
        } else {
            None
        };
        let excludes = if self.eat(&Kind::Minus) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(Generic {
            name,
            bound,
            excludes,
            includes,
            span: self.since(start),
        })
    }
    fn fields(&mut self) -> Result<Vec<Field>> {
        self.field_list(Kind::RBrace)
    }
    fn field_list(&mut self, end: Kind) -> Result<Vec<Field>> {
        self.separated(end, |p| {
            let start = p.current().span;
            let name = p.ident()?;
            p.expect(&Kind::Colon, "':' after field name")?;
            let ty = p.ty()?;
            Ok(Field {
                name,
                source: None,
                ty,
                span: p.since(start),
            })
        })
    }
    fn named_fields_ahead(&self) -> bool {
        matches!(self.current().kind, Kind::Ident(_))
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == Kind::Colon)
    }
    fn variant(&mut self) -> Result<Variant> {
        let start = self.current().span;
        let name = self.ident()?;
        // Binders written on the constructor itself are constructor-local:
        // `FSucc<n: Nat>(pred: Fin<n>): Fin<succ n>`. They are deliberately
        // parsed in the same place as function generics, not on the family.
        let locals = self.generics()?;
        let payload = if self.eat(&Kind::LParen) {
            if self.at(&Kind::RParen) {
                self.bump();
                Payload::Tuple(Vec::new())
            } else if self.named_fields_ahead() {
                Payload::Fields(self.field_list(Kind::RParen)?)
            } else {
                Payload::Tuple(self.separated(Kind::RParen, |p| p.ty())?)
            }
        } else if self.eat(&Kind::LBrace) {
            Payload::Record(self.fields()?)
        } else {
            Payload::Unit
        };
        let result = if self.eat(&Kind::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(Variant {
            name,
            locals,
            payload,
            result,
            span: self.since(start),
        })
    }
    /// `algebra Name { elements { A, B } zero = A; one = B; add { ... } mul { ... } }`.
    fn grade_algebra(&mut self) -> Result<GradeAlgebra> {
        let name = self.ident()?;
        self.expect(&Kind::LBrace, "'{' before grade algebra body")?;
        if !self.word_keyword("elements") {
            return Err(self.error("expected 'elements' in a grade algebra declaration"));
        }
        self.bump();
        self.expect(&Kind::LBrace, "'{' before grade algebra elements")?;
        let elements = self.separated(Kind::RBrace, |p| {
            let start = p.current().span;
            let name = p.ident()?;
            Ok(GradeElement {
                name,
                span: p.since(start),
            })
        })?;
        let zero = self.algebra_identity("zero")?;
        let one = self.algebra_identity("one")?;
        let add = self.algebra_table("add", Kind::Plus)?;
        let mul = self.algebra_table("mul", Kind::Star)?;
        self.expect(&Kind::RBrace, "'}' after grade algebra")?;
        Ok(GradeAlgebra {
            name,
            elements,
            zero,
            one,
            add,
            mul,
        })
    }
    fn algebra_identity(&mut self, which: &str) -> Result<String> {
        if !self.word_keyword(which) {
            return Err(self.error(format!("expected '{which}' in a grade algebra declaration")));
        }
        self.bump();
        self.expect(&Kind::Eq, "'=' after grade algebra identity")?;
        let name = self.ident()?;
        self.expect(&Kind::Semi, "';' after grade algebra identity")?;
        Ok(name)
    }
    fn algebra_table(&mut self, which: &str, op: Kind) -> Result<Vec<GradeEquation>> {
        if !self.word_keyword(which) {
            return Err(self.error(format!(
                "expected '{which}' table in a grade algebra declaration"
            )));
        }
        self.bump();
        self.expect(&Kind::LBrace, "'{' before grade algebra operation table")?;
        self.separated(Kind::RBrace, |p| {
            let start = p.current().span;
            let left = p.ident()?;
            p.expect(&op, "operation symbol in a grade algebra table")?;
            let right = p.ident()?;
            p.expect(&Kind::Eq, "'=' before a grade algebra table result")?;
            let result = p.ident()?;
            Ok(GradeEquation {
                left,
                right,
                result,
                span: p.since(start),
            })
        })
    }
    /// One method item. Methods use ordinary function syntax with an explicit
    /// first receiver parameter named `self`, as in
    /// `fn distance(self: Point, other: Point) -> i64 ! { panic } { ... }`.
    fn method(&mut self) -> Result<Method> {
        let start = self.current().span;
        let public = self.eat(&Kind::Pub);
        if self.eat(&Kind::Total) {
            return Err(self.error("'total' applies only to fn and enum declarations"));
        }
        self.expect(&Kind::Fn, "'fn' in a trait or impl method")?;
        let function = self.function_with_receiver(false)?;
        Ok(Method {
            public,
            function,
            span: self.since(start),
        })
    }
    #[allow(clippy::type_complexity)]
    fn trait_declaration(
        &mut self,
    ) -> Result<(String, Vec<Generic>, Vec<Associated>, Vec<Method>)> {
        let name = self.ident()?;
        let (lifetimes, generics) = self.function_generics()?;
        if let Some(lifetime) = lifetimes.first() {
            return Err(Diagnostic::new(
                lifetime.span,
                "traits do not take lifetime parameters in this subset; lifetimes belong on method signatures",
            ));
        }
        let mut seen = std::collections::BTreeSet::new();
        for generic in &generics {
            if !seen.insert(generic.name.clone()) {
                return Err(Diagnostic::new(
                    generic.span,
                    format!("duplicate trait parameter '{}'", generic.name),
                ));
            }
        }
        self.expect(&Kind::LBrace, "'{' before trait methods")?;
        let mut associated = Vec::new();
        let mut methods = Vec::new();
        let mut associated_names = std::collections::BTreeSet::new();
        while !self.at(&Kind::RBrace) {
            if self.at(&Kind::Eof) {
                return Err(self.error("expected '}' to close the trait declaration"));
            }
            if self.at(&Kind::Type) || self.word_keyword("const") {
                let item = self.associated_item(true)?;
                if !associated_names.insert(item.name().to_owned()) {
                    return Err(Diagnostic::new(
                        item.span(),
                        format!(
                            "duplicate associated item '{}' in trait '{name}'",
                            item.name()
                        ),
                    ));
                }
                associated.push(item);
                continue;
            }
            let method = self.method()?;
            if method.public {
                return Err(Diagnostic::new(
                    method.span,
                    "trait methods inherit the trait's visibility; remove 'pub'",
                ));
            }
            if !associated_names.insert(method.function.name.clone()) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "duplicate associated item '{}' in trait '{name}'",
                        method.function.name
                    ),
                ));
            }
            methods.push(method);
        }
        self.expect(&Kind::RBrace, "'}' to close the trait declaration")?;
        Ok((name, generics, associated, methods))
    }
    /// `type Name;` / `type Name = Type;` and `const NAME: Type [= value];`.
    fn associated_item(&mut self, declaration: bool) -> Result<Associated> {
        let start = self.current().span;
        if self.eat(&Kind::Type) {
            let name = self.ident()?;
            let value = if self.eat(&Kind::Eq) {
                Some(self.ty()?)
            } else {
                if !declaration {
                    return Err(Diagnostic::new(
                        self.current().span,
                        "an associated type in an impl requires a value: 'type Name = Type;'",
                    ));
                }
                None
            };
            self.expect(&Kind::Semi, "';' after associated type")?;
            return Ok(Associated::Type {
                name,
                value,
                span: self.since(start),
            });
        }
        if self.word_keyword("const") {
            self.bump();
            let name = self.ident()?;
            self.expect(&Kind::Colon, "':' after associated constant name")?;
            let ty = self.ty()?;
            let value = if self.eat(&Kind::Eq) {
                Some(self.expr()?)
            } else {
                if !declaration {
                    return Err(Diagnostic::new(
                        self.current().span,
                        "an associated constant in an impl requires a value: 'const NAME: Type = value;'",
                    ));
                }
                None
            };
            self.expect(&Kind::Semi, "';' after associated constant")?;
            return Ok(Associated::Const {
                name,
                ty,
                value,
                span: self.since(start),
            });
        }
        Err(self.error("expected an associated type or constant"))
    }
    #[allow(clippy::type_complexity)]
    fn impl_declaration(
        &mut self,
    ) -> Result<(
        Vec<Generic>,
        Option<Type>,
        Type,
        Vec<Associated>,
        Vec<Method>,
    )> {
        let start = self.current().span;
        let (lifetimes, generics) = self.function_generics()?;
        if let Some(lifetime) = lifetimes.first() {
            return Err(Diagnostic::new(
                lifetime.span,
                "lifetime-parameterized impls are not supported; write 'impl Trait for Type' or a generic 'impl<T> Trait for Type'",
            ));
        }
        let mut seen = std::collections::BTreeSet::new();
        for generic in &generics {
            if !seen.insert(generic.name.clone()) {
                return Err(Diagnostic::new(
                    generic.span,
                    format!("duplicate impl parameter '{}'", generic.name),
                ));
            }
        }
        let first = self.ty()?;
        let (trait_path, self_ty) = if self.word_keyword("for") {
            self.bump();
            if !matches!(&first.kind, TypeKind::Named { .. }) {
                return Err(Diagnostic::new(
                    first.span,
                    "an implemented trait must be named, as in 'impl Trait<Arguments> for Type'",
                ));
            }
            (Some(first), self.ty()?)
        } else {
            (None, first)
        };
        self.expect(&Kind::LBrace, "'{' before impl methods")?;
        let mut associated = Vec::new();
        let mut methods = Vec::new();
        let mut item_names = std::collections::BTreeSet::new();
        while !self.at(&Kind::RBrace) {
            if self.at(&Kind::Eof) {
                return Err(self.error("expected '}' to close the impl declaration"));
            }
            if self.at(&Kind::Type) || self.word_keyword("const") {
                let item = self.associated_item(false)?;
                if !item_names.insert(item.name().to_owned()) {
                    return Err(Diagnostic::new(
                        item.span(),
                        format!("duplicate item '{}' in one impl", item.name()),
                    ));
                }
                associated.push(item);
                continue;
            }
            let method = self.method()?;
            if method.function.body.is_none() {
                return Err(Diagnostic::new(
                    method.span,
                    "impl methods require a body; a method signature without a body is only valid in a trait",
                ));
            }
            if !item_names.insert(method.function.name.clone()) {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate item '{}' in one impl", method.function.name),
                ));
            }
            methods.push(method);
        }
        self.expect(&Kind::RBrace, "'}' to close the impl declaration")?;
        if methods.is_empty() && associated.is_empty() && trait_path.is_none() {
            return Err(Diagnostic::new(
                self.since(start),
                "an inherent impl must define at least one method or associated constant",
            ));
        }
        Ok((generics, trait_path, self_ty, associated, methods))
    }
    fn function(&mut self, total: bool) -> Result<Function> {
        self.function_body(total, false)
    }
    /// Method declarations additionally accept the ergonomic receiver sugar
    /// `&self` and `&mut self`, lowered to `self: &Self` / `self: &mut Self`.
    /// Ordinary functions keep the explicit `name: type` parameter grammar.
    fn function_with_receiver(&mut self, total: bool) -> Result<Function> {
        self.function_body(total, true)
    }
    fn function_body(&mut self, total: bool, method: bool) -> Result<Function> {
        let name = self.ident()?;
        let (lifetimes, generics) = self.function_generics()?;
        self.expect(&Kind::LParen, "'(' before parameters")?;
        let parameters = self.separated(Kind::RParen, |p| {
            let start = p.current().span;
            if method && p.at(&Kind::Amp) {
                p.bump();
                let mutable = p.eat(&Kind::Mut);
                let receiver = p.ident()?;
                if receiver != "self" {
                    return Err(Diagnostic::new(
                        p.since(start),
                        "borrowed receiver sugar is only valid for '&self' or '&mut self'",
                    ));
                }
                let ty = Node::new(
                    TypeKind::Borrow {
                        lifetime: None,
                        mutable,
                        inner: Box::new(Node::new(TypeKind::SelfType, p.since(start))),
                    },
                    p.since(start),
                );
                return Ok(Parameter {
                    erased: false,
                    name: receiver,
                    ty,
                    span: p.since(start),
                });
            }
            let erased = p.eat(&Kind::Erased);
            let name = p.ident()?;
            p.expect(&Kind::Colon, "':' after parameter name")?;
            let ty = p.ty()?;
            Ok(Parameter {
                erased,
                name,
                ty,
                span: p.since(start),
            })
        })?;
        self.expect(&Kind::Arrow, "'->' and an explicit return type")?;
        let result = self.ty()?;
        let effects = self.effects()?;
        let body = if self.eat(&Kind::Semi) {
            None
        } else {
            Some(self.block()?)
        };
        Ok(Function {
            total,
            name,
            lifetimes,
            generics,
            parameters,
            result,
            effects,
            body,
            foreign: None,
        })
    }
    /// Function generic binders may mix lifetime parameters with ordinary
    /// type/natural/grade/effect binders: `< 'a, 'b, T >`.
    fn function_generics(&mut self) -> Result<(Vec<Lifetime>, Vec<Generic>)> {
        if !self.eat(&Kind::Lt) {
            return Ok((Vec::new(), Vec::new()));
        }
        let mut lifetimes = Vec::new();
        let mut generics = Vec::new();
        self.separated(Kind::Gt, |p| {
            let start = p.current().span;
            if let Kind::Lifetime(name) = &p.current().kind {
                let name = name.clone();
                p.bump();
                let mut bounds = Vec::new();
                if p.eat(&Kind::Colon) {
                    loop {
                        let bound_start = p.current().span;
                        let target = match &p.current().kind {
                            Kind::Lifetime(target) => target.clone(),
                            _ => {
                                return Err(p.error(
                                    "expected a lifetime after ':' in an outlives bound, as in <'long: 'short>",
                                ));
                            }
                        };
                        p.bump();
                        bounds.push(LifetimeBound {
                            name: target,
                            span: p.since(bound_start),
                        });
                        if !p.eat(&Kind::Plus) {
                            break;
                        }
                    }
                }
                lifetimes.push(Lifetime {
                    name,
                    span: p.since(start),
                    bounds,
                });
            } else {
                generics.push(p.generic_binder()?);
            }
            Ok(())
        })?;
        Ok((lifetimes, generics))
    }
    fn effects(&mut self) -> Result<Vec<Type>> {
        self.expect(&Kind::Bang, "an explicit effect row '! { ... }'")?;
        self.expect(&Kind::LBrace, "'{' in effect row")?;
        self.separated(Kind::RBrace, |p| p.effect_row())
    }
    /// One effect-row element. Subtraction is a row operation, not part of the
    /// ordinary type grammar: `e - io` removes `io` from the row expression
    /// before it is checked against the finite four-effect universe. It binds
    /// looser than `|`, so `(a | b) - c` needs parentheses for the other order.
    fn effect_row(&mut self) -> Result<Type> {
        let start = self.current().span;
        let mut left = self.ty()?;
        let mut steps = 0;
        while self.eat(&Kind::Minus) {
            steps += 1;
            if steps > LIMIT {
                return Err(self.error("effect row exceeds limit (128) subtractions"));
            }
            let right = self.ty()?;
            left = Node::new(
                TypeKind::Binary {
                    op: Kind::Minus,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                self.since(start),
            );
        }
        Ok(left)
    }
    fn ty(&mut self) -> Result<Type> {
        self.type_bp(0)
    }
    /// One trait bound of a `dyn` type: a trait path with optional arguments,
    /// where `Name = Type` binds an associated type, as in
    /// `Convert<i64, Out = Text>`. Bindings follow the trait arguments.
    fn dyn_bound(&mut self) -> Result<crate::ast::DynBound> {
        let start = self.current().span;
        if !matches!(self.current().kind, Kind::Ident(_)) {
            return Err(self.error(
                "a trait object must name one declared trait, as in 'dyn Describe' or 'dyn Convert<i64>'",
            ));
        }
        let path = self.path()?;
        let mut arguments = Vec::new();
        let mut bindings: Vec<(String, Type)> = Vec::new();
        if self.eat(&Kind::Lt) {
            while !self.at(&Kind::Gt) {
                let binding = matches!(self.current().kind, Kind::Ident(_))
                    && self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|token| matches!(token.kind, Kind::Eq));
                if binding {
                    let name_span = self.current().span;
                    let name = self.ident()?;
                    self.bump();
                    if bindings.iter().any(|(bound, _)| *bound == name) {
                        return Err(Diagnostic::new(
                            name_span,
                            format!("associated type '{name}' is bound twice in this trait object"),
                        ));
                    }
                    bindings.push((name, self.ty()?));
                } else {
                    if !bindings.is_empty() {
                        return Err(self.error(
                            "trait arguments must come before associated-type bindings, as in 'dyn Convert<i64, Out = Text>'",
                        ));
                    }
                    arguments.push(self.specialization_argument()?);
                }
                if !self.eat(&Kind::Comma) {
                    break;
                }
            }
            self.expect(&Kind::Gt, "'>' after trait object arguments")?;
        }
        Ok(crate::ast::DynBound {
            trait_ref: Node::new(TypeKind::Named { path, arguments }, self.since(start)),
            bindings,
        })
    }
    /// A usage grade inside `@[ ... ]`:
    ///
    /// ```text
    /// grade   = product ("+" product)*
    /// product = atom ("*" atom)*
    /// atom    = natural | path | "(" grade ")"
    /// ```
    ///
    /// This is deliberately a separate grammar from types so that `+` and `*`
    /// cannot leak into ordinary type syntax. `many` and grade variables parse
    /// as one-segment paths; the executable checker decides which names are
    /// legal.
    fn grade(&mut self) -> Result<Type> {
        self.nested(|p| p.grade_bp(0))
    }
    fn grade_bp(&mut self, min: u8) -> Result<Type> {
        let start = self.current().span;
        let mut left = self.grade_atom()?;
        let mut steps = 0;
        loop {
            let bp = match self.current().kind {
                Kind::Plus => 1,
                Kind::Star => 2,
                _ => break,
            };
            if bp < min {
                break;
            }
            steps += 1;
            if steps > LIMIT {
                return Err(self.error("grade expression exceeds limit (128)"));
            }
            let op = self.bump().kind;
            let right = self.grade_bp(bp + 1)?;
            left = Node::new(
                TypeKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                self.since(start),
            );
        }
        Ok(left)
    }
    fn grade_atom(&mut self) -> Result<Type> {
        let start = self.current().span;
        if self.eat(&Kind::LParen) {
            let inner = self.grade()?;
            self.expect(&Kind::RParen, "')' after grade")?;
            return Ok(Node::new(inner.kind, self.since(start)));
        }
        if let Kind::Integer(value) = self.current().kind.clone() {
            self.bump();
            return Ok(Node::new(TypeKind::Integer(value), self.since(start)));
        }
        if matches!(self.current().kind, Kind::Ident(_)) {
            let path = self.path()?;
            return Ok(Node::new(
                TypeKind::Named {
                    path,
                    arguments: Vec::new(),
                },
                self.since(start),
            ));
        }
        Err(self.error(
            "expected a usage grade: a natural number, 'many', a grade variable, or a '+'/'*' expression",
        ))
    }
    /// An argument in `callee::<...>`. It is a type unless the argument
    /// continues with grade arithmetic, which lets explicit specialization use
    /// `f::<1 + 1>` and `f::<G * 2>` without introducing a separate syntax for
    /// the argument list.
    fn specialization_argument(&mut self) -> Result<Type> {
        let start = self.current().span;
        // A lifetime argument is erased and is deliberately not a runtime type.
        // It appears only in type-argument positions such as `Window<'a, i64>`.
        if let Kind::Lifetime(name) = &self.current().kind {
            let name = name.clone();
            self.bump();
            return Ok(Node::new(TypeKind::Lifetime(name), self.since(start)));
        }
        let mut argument = self.ty()?;
        let mut steps = 0;
        loop {
            let bp = match self.current().kind {
                Kind::Plus | Kind::Minus => 1,
                Kind::Star => 2,
                _ => break,
            };
            steps += 1;
            if steps > LIMIT {
                return Err(self.error("grade expression exceeds limit (128)"));
            }
            let op = self.bump().kind;
            let right = self.grade_bp(bp + 1)?;
            argument = Node::new(
                TypeKind::Binary {
                    op,
                    left: Box::new(argument),
                    right: Box::new(right),
                },
                self.since(start),
            );
        }
        Ok(argument)
    }
    fn type_bp(&mut self, min: u8) -> Result<Type> {
        self.nested(|p| p.type_inner(min))
    }
    fn type_inner(&mut self, min: u8) -> Result<Type> {
        let start = self.current().span;
        let mut left = if self.eat(&Kind::Amp) {
            let lifetime = match &self.current().kind {
                Kind::Lifetime(name) => {
                    let name = name.clone();
                    self.bump();
                    Some(name)
                }
                _ => None,
            };
            let mutable = self.eat(&Kind::Mut);
            let inner = self.type_bp(4)?;
            Node::new(
                TypeKind::Borrow {
                    lifetime,
                    mutable,
                    inner: Box::new(inner),
                },
                self.since(start),
            )
        } else if self.eat(&Kind::LParen) {
            let first = if self.at(&Kind::RParen) {
                None
            } else {
                Some(self.ty()?)
            };
            if let Some(first) = first {
                if self.eat(&Kind::Comma) {
                    let mut types = vec![first];
                    types.extend(self.separated(Kind::RParen, |p| p.ty())?);
                    Node::new(TypeKind::Tuple(types), self.since(start))
                } else {
                    self.expect(&Kind::RParen, "')' after type")?;
                    Node::new(first.kind, self.since(start))
                }
            } else {
                self.bump();
                Node::new(TypeKind::Tuple(vec![]), self.since(start))
            }
        } else if self.at(&Kind::LBrace) {
            self.bump();
            let proposition = self.expr()?;
            self.expect(&Kind::RBrace, "'}' after proposition")?;
            Node::new(
                TypeKind::Predicate(Box::new(proposition)),
                self.since(start),
            )
        } else if self.eat(&Kind::Struct) {
            self.expect(
                &Kind::LBrace,
                "'{' after 'struct' in an anonymous structural record type",
            )?;
            let mut fields = Vec::new();
            let mut open = false;
            let mut row = None;
            while !self.at(&Kind::RBrace) {
                if self.eat(&Kind::DotDot) {
                    open = true;
                    // `..r` names a row variable; a bare `..` is an erased
                    // open row. The row variable is an ordinary single-segment
                    // type path so the resolver binds it like a type generic.
                    if let Kind::Ident(name) = &self.current().kind {
                        let name = name.clone();
                        let row_start = self.current().span;
                        self.bump();
                        row = Some(Box::new(Node::new(
                            TypeKind::Named {
                                path: vec![name],
                                arguments: vec![],
                            },
                            self.since(row_start),
                        )));
                    }
                    if self.at(&Kind::Comma) {
                        self.bump();
                    }
                    break;
                }
                let field_start = self.current().span;
                let name = self.ident()?;
                self.expect(&Kind::Colon, "':' after structural record field name")?;
                let ty = self.ty()?;
                let source = if matches!(&self.current().kind, Kind::Ident(word) if word == "from")
                {
                    self.bump();
                    Some(self.ident()?)
                } else {
                    None
                };
                fields.push(Field {
                    name,
                    source,
                    ty,
                    span: self.since(field_start),
                });
                if !self.eat(&Kind::Comma) {
                    break;
                }
            }
            self.expect(&Kind::RBrace, "'}' after structural record type")?;
            Node::new(
                TypeKind::Structural { fields, open, row },
                self.since(start),
            )
        } else if self.eat(&Kind::LBracket) {
            let inner = self.ty()?;
            let kind = if self.eat(&Kind::Semi) {
                let length = self.array_length()?;
                TypeKind::Array(Box::new(inner), Box::new(length))
            } else {
                TypeKind::Slice(Box::new(inner))
            };
            self.expect(&Kind::RBracket, "']' after array/slice type")?;
            Node::new(kind, self.since(start))
        } else if self.linear_once_fn_ahead() {
            self.bump(); // linear
            self.bump(); // once
            self.bump(); // fn
            self.function_type(start, true, true)?
        } else if self.once_linear_fn_ahead() {
            self.bump(); // once
            self.bump(); // linear
            self.bump(); // fn
            self.function_type(start, true, true)?
        } else if self.once_fn_ahead() {
            self.bump(); // once
            self.bump(); // fn
            self.function_type(start, true, false)?
        } else if self.eat(&Kind::Fn) {
            self.function_type(start, false, false)?
        } else if let Kind::Integer(value) = self.current().kind.clone() {
            self.bump();
            Node::new(TypeKind::Integer(value), self.since(start))
        } else if matches!(self.current().kind, Kind::True | Kind::False) {
            let value = self.bump().kind == Kind::True;
            Node::new(TypeKind::Bool(value), self.since(start))
        } else if self.at(&Kind::Minus) {
            // Negative machine indices. Natural literals reject a leading sign
            // later; this keeps the type grammar usable for `i64` indices.
            self.bump();
            let Kind::Integer(value) = self.current().kind.clone() else {
                return Err(self.error("expected an integer literal after '-' in a type index"));
            };
            self.bump();
            Node::new(TypeKind::Integer(format!("-{value}")), self.since(start))
        } else {
            let path_start = self.current().span;
            let path = self.path()?;
            if path == ["Self"] {
                if self.at(&Kind::Lt) {
                    return Err(self.error(
                        "generic 'Self' is not supported; traits are monomorphic in this subset",
                    ));
                }
                return Ok(Node::new(TypeKind::SelfType, self.since(path_start)));
            }
            if path == ["dyn"] {
                let mut bounds = vec![self.dyn_bound()?];
                while self.eat(&Kind::Plus) {
                    if matches!(self.current().kind, Kind::Lifetime(_)) {
                        return Err(self.error(
                            "trait objects do not take lifetime bounds; object values own their payload",
                        ));
                    }
                    bounds.push(self.dyn_bound()?);
                }
                return Ok(Node::new(TypeKind::Dyn(bounds), self.since(path_start)));
            }
            if path == ["impl"] {
                return Err(self.error(
                    "'impl Trait' types are not supported; name a declared type and use a generic bound for static dispatch",
                ));
            }
            let arguments = if self.eat(&Kind::Lt) {
                self.separated(Kind::Gt, |p| p.specialization_argument())?
            } else {
                Vec::new()
            };
            Node::new(TypeKind::Named { path, arguments }, self.since(start))
        };
        let mut steps = 0;
        loop {
            // Index predicates and arithmetic are deliberately a future grammar
            // extension. '<' is unambiguously generic application in this slice.
            let bp = match self.current().kind {
                Kind::Pipe => 1,
                Kind::Amp => 2,
                Kind::At => 3,
                _ => break,
            };
            if bp < min {
                break;
            }
            steps += 1;
            if steps > LIMIT {
                return Err(self.error("type operator chain exceeds limit (128)"));
            }
            let op = self.bump().kind;
            let kind = if op == Kind::At {
                self.expect(&Kind::LBracket, "'[' after '@'")?;
                let grade = self.grade()?;
                self.expect(&Kind::RBracket, "']' after grade")?;
                TypeKind::Graded {
                    inner: Box::new(left),
                    grade: Box::new(grade),
                }
            } else {
                let right = self.type_bp(bp + 1)?;
                TypeKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            };
            left = Node::new(kind, self.since(start));
        }
        Ok(left)
    }
    /// `once fn(...)`: an owning once-consuming closure type. `once` is not a
    /// reserved keyword; only the two-token sequence `once fn` is special.
    fn once_fn_ahead(&self) -> bool {
        matches!(&self.current().kind, Kind::Ident(name) if name == "once")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|token| token.kind == Kind::Fn)
    }
    /// `linear once fn(...)`: a linear-once callable type. At most one call
    /// consumes its captured linear obligations, and the callable itself is a
    /// linear value.
    fn linear_once_fn_ahead(&self) -> bool {
        matches!(&self.current().kind, Kind::Ident(name) if name == "linear")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|token| matches!(&token.kind, Kind::Ident(name) if name == "once"))
            && self
                .tokens
                .get(self.pos + 2)
                .is_some_and(|token| token.kind == Kind::Fn)
    }
    /// `once linear fn(...)`: accepted spelling of the same linear-once type.
    fn once_linear_fn_ahead(&self) -> bool {
        matches!(&self.current().kind, Kind::Ident(name) if name == "once")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|token| matches!(&token.kind, Kind::Ident(name) if name == "linear"))
            && self
                .tokens
                .get(self.pos + 2)
                .is_some_and(|token| token.kind == Kind::Fn)
    }
    fn function_type(&mut self, start: Span, call_once: bool, call_linear: bool) -> Result<Type> {
        let binder_start = self.current().span;
        let (lifetimes, generics) = self.function_generics()?;
        if !generics.is_empty() {
            return Err(Diagnostic::new(
                binder_start,
                "a function arrow type binds only lifetimes, as in fn<'a>(&'a [T]) -> &'a [T]; type parameters belong to named functions",
            ));
        }
        self.expect(&Kind::LParen, "'(' in function type")?;
        let parameters = self.separated(Kind::RParen, |p| {
            let start = p.current().span;
            let named = matches!(p.current().kind, Kind::Ident(_))
                && p.tokens
                    .get(p.pos + 1)
                    .is_some_and(|t| t.kind == Kind::Colon);
            let name = if named {
                let name = p.ident()?;
                p.expect(&Kind::Colon, "':' after function-type binder")?;
                Some(name)
            } else {
                None
            };
            let ty = p.ty()?;
            Ok(TypeParameter {
                name,
                ty,
                span: p.since(start),
            })
        })?;
        self.expect(&Kind::Arrow, "'->' in function type")?;
        let result = Box::new(self.ty()?);
        let effects = self.effects()?;
        Ok(Node::new(
            TypeKind::Function {
                lifetimes,
                parameters,
                result,
                effects,
                call_once,
                call_linear,
            },
            self.since(start),
        ))
    }
    /// A compile-time array length expression. The grammar is deliberately a
    /// natural-arithmetic subset of types so that a length may name a
    /// `N: Nat` const parameter, an admitted total logical function applied to
    /// constant arguments, and `+`/`-`/`*`/`/`/`%` over those. Evaluation and
    /// rejection of runtime-dependent lengths happen during type lowering.
    fn array_length(&mut self) -> Result<Type> {
        self.nested(|p| {
            let start = p.current().span;
            let length = p.array_length_bp(0)?;
            // `[T; n <= C]`: a runtime-length array whose length is the
            // immutable scalar `n` and whose inline capacity is `C`.
            if p.eat(&Kind::Le) {
                let capacity = p.array_length_bp(0)?;
                return Ok(Node::new(
                    TypeKind::Binary {
                        op: Kind::Le,
                        left: Box::new(length),
                        right: Box::new(capacity),
                    },
                    p.since(start),
                ));
            }
            Ok(length)
        })
    }
    fn array_length_bp(&mut self, min: u8) -> Result<Type> {
        let start = self.current().span;
        let mut left = self.array_length_atom()?;
        let mut steps = 0;
        loop {
            let bp = match self.current().kind {
                Kind::Plus | Kind::Minus => 1,
                Kind::Star | Kind::Slash | Kind::Percent => 2,
                _ => break,
            };
            if bp < min {
                break;
            }
            steps += 1;
            if steps > LIMIT {
                return Err(self.error("array length expression exceeds limit (128)"));
            }
            let op = self.bump().kind;
            let right = self.array_length_bp(bp + 1)?;
            left = Node::new(
                TypeKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                self.since(start),
            );
        }
        Ok(left)
    }
    fn array_length_atom(&mut self) -> Result<Type> {
        let start = self.current().span;
        if self.eat(&Kind::LParen) {
            let inner = self.array_length()?;
            self.expect(&Kind::RParen, "')' after array length")?;
            return Ok(Node::new(inner.kind, self.since(start)));
        }
        if let Kind::Integer(value) = self.current().kind.clone() {
            self.bump();
            return Ok(Node::new(TypeKind::Integer(value), self.since(start)));
        }
        if matches!(self.current().kind, Kind::Ident(_)) {
            let path = self.path()?;
            let arguments = if self.eat(&Kind::Lt) {
                self.separated(Kind::Gt, |p| p.specialization_argument())?
            } else {
                Vec::new()
            };
            return Ok(Node::new(
                TypeKind::Named { path, arguments },
                self.since(start),
            ));
        }
        Err(self.error(
            "array length must be a compile-time expression of nonnegative natural literals, const parameters, or total logical functions",
        ))
    }
    fn block(&mut self) -> Result<Block> {
        self.nested(|p| p.block_inner())
    }
    fn block_inner(&mut self) -> Result<Block> {
        let start = self
            .expect(&Kind::LBrace, "'{' before function or block body")?
            .span;
        let mut statements = Vec::new();
        let mut tail = None;
        while !self.at(&Kind::RBrace) {
            if self.at(&Kind::Eof) {
                return Err(self.error("expected '}' to close block"));
            }
            if self.eat(&Kind::Let) {
                let start = self.tokens[self.pos - 1].span;
                let mutable = self.eat(&Kind::Mut);
                let pattern = self.pattern()?;
                let ty = if self.eat(&Kind::Colon) {
                    Some(self.ty()?)
                } else {
                    None
                };
                self.expect(&Kind::Eq, "'=' in let binding")?;
                let value = self.expr()?;
                self.expect(&Kind::Semi, "';' after let binding")?;
                statements.push(Statement::Let {
                    mutable,
                    pattern,
                    ty,
                    value,
                    span: self.since(start),
                });
            } else {
                let expr = self.expr()?;
                if self.eat(&Kind::Semi) {
                    statements.push(Statement::Expr(expr));
                } else if self.at(&Kind::RBrace) {
                    tail = Some(Box::new(expr));
                    break;
                } else if matches!(
                    expr.kind,
                    ExprKind::If { .. }
                        | ExprKind::Match { .. }
                        | ExprKind::Block(_)
                        | ExprKind::Handle { .. }
                        | ExprKind::While { .. }
                        | ExprKind::Loop(_)
                ) {
                    statements.push(Statement::Expr(expr));
                } else {
                    return Err(self.error("expected ';' or '}' after expression"));
                }
            }
        }
        self.expect(&Kind::RBrace, "'}' to close block")?;
        Ok(Block {
            statements,
            tail,
            span: self.since(start),
        })
    }
    fn expr(&mut self) -> Result<Expr> {
        self.expr_bp(0)
    }
    fn expr_bp(&mut self, min: u8) -> Result<Expr> {
        self.nested(|p| p.expr_inner(min))
    }
    fn expr_inner(&mut self, min: u8) -> Result<Expr> {
        let start = self.current().span;
        let mut left = self.prefix()?;
        let mut compared = false;
        let mut steps = 0;
        loop {
            if steps > LIMIT {
                return Err(self.error("expression chain exceeds limit (128)"));
            }
            steps += 1;
            if 12 >= min {
                if self.eat(&Kind::LParen) {
                    let arguments = self.separated(Kind::RParen, |p| p.expr())?;
                    left = Node::new(
                        ExprKind::Call {
                            callee: Box::new(left),
                            arguments,
                        },
                        self.since(start),
                    );
                    continue;
                }
                if self.eat(&Kind::LBracket) {
                    let start_bound = if self.eat(&Kind::DotDot) {
                        None
                    } else {
                        let bound = self.expr()?;
                        if self.eat(&Kind::DotDot) {
                            Some(Box::new(bound))
                        } else {
                            self.expect(&Kind::RBracket, "']' after index")?;
                            left = Node::new(
                                ExprKind::Index {
                                    value: Box::new(left),
                                    index: Box::new(bound),
                                },
                                self.since(start),
                            );
                            continue;
                        }
                    };
                    let end_bound = if self.at(&Kind::RBracket) {
                        None
                    } else {
                        Some(Box::new(self.expr()?))
                    };
                    self.expect(&Kind::RBracket, "']' after slice range")?;
                    left = Node::new(
                        ExprKind::Slice {
                            value: Box::new(left),
                            start: start_bound,
                            end: end_bound,
                        },
                        self.since(start),
                    );
                    continue;
                }
                if self.eat(&Kind::Dot) {
                    // `pair.0`: tuple fields are named by position.
                    let name = if let Kind::Integer(index) = &self.current().kind {
                        let index = index.clone();
                        self.bump();
                        index
                    } else {
                        self.ident()?
                    };
                    left = Node::new(
                        ExprKind::Field {
                            value: Box::new(left),
                            name,
                        },
                        self.since(start),
                    );
                    continue;
                }
                if self.eat(&Kind::Question) {
                    left = Node::new(ExprKind::Try(Box::new(left)), self.since(start));
                    continue;
                }
                if matches!(&self.current().kind, Kind::Ident(word) if word == "as") {
                    self.bump();
                    let ty = self.ty()?;
                    left = Node::new(
                        ExprKind::Cast {
                            value: Box::new(left),
                            ty,
                        },
                        self.since(start),
                    );
                    continue;
                }
                if self.record_literal_ahead(&left) {
                    self.bump();
                    let fields = self.separated(Kind::RBrace, |p| {
                        let name = p.ident()?;
                        p.expect(&Kind::Colon, "':' after record field name")?;
                        Ok((name, p.expr()?))
                    })?;
                    left = Node::new(
                        ExprKind::Record {
                            ty: Box::new(left),
                            fields,
                        },
                        self.since(start),
                    );
                    continue;
                }
                if self.eat(&Kind::ColonColon) {
                    self.expect(&Kind::Lt, "'<' after '::'; paths use '.'")?;
                    let arguments = self.separated(Kind::Gt, |p| p.specialization_argument())?;
                    left = Node::new(
                        ExprKind::Specialize {
                            callee: Box::new(left),
                            arguments,
                        },
                        self.since(start),
                    );
                    continue;
                }
            }
            // `<<` and `>>` are two adjacent `<`/`>` tokens, so generic
            // arguments such as `Vec<Vec<T>>` keep lexing as separate `>`.
            let shift = self.adjacent_pair();
            // A block-like expression (`if`, `match`, `while`, `loop`, block)
            // followed by `&` or `|` ends there: the next token starts a new
            // statement such as `&mut view[..]`. Parenthesize to combine.
            let block_like = matches!(
                left.kind,
                ExprKind::If { .. }
                    | ExprKind::Match { .. }
                    | ExprKind::Block(_)
                    | ExprKind::While { .. }
                    | ExprKind::Loop(_)
            );
            if block_like && matches!(self.current().kind, Kind::Amp | Kind::Pipe) {
                break;
            }
            let (lbp, rbp) = match (&self.current().kind, shift) {
                (Kind::Eq, _) => (1, 1),
                (Kind::PipePipe, _) => (2, 3),
                (Kind::AmpAmp, _) => (3, 4),
                (Kind::Lt | Kind::Gt, true) => (8, 9),
                (Kind::EqEq | Kind::Ne | Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge, _) => (4, 5),
                (Kind::Pipe, _) => (5, 6),
                (Kind::Caret, _) => (6, 7),
                (Kind::Amp, _) => (7, 8),
                (Kind::Plus | Kind::Minus, _) => (9, 10),
                (Kind::Star | Kind::Slash | Kind::Percent, _) => (10, 11),
                _ => break,
            };
            if lbp < min {
                break;
            }
            if lbp == 4 && compared {
                return Err(self.error("comparisons do not chain; combine comparisons with '&&'"));
            }
            compared |= lbp == 4;
            let op = if shift && lbp == 8 {
                let first = self.bump().kind;
                self.bump();
                if first == Kind::Lt {
                    Kind::Shl
                } else {
                    Kind::Shr
                }
            } else {
                self.bump().kind
            };
            let right = self.expr_bp(rbp)?;
            left = Node::new(
                ExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                self.since(start),
            );
        }
        Ok(left)
    }
    /// Two touching `<` or `>` tokens form a shift operator.
    fn adjacent_pair(&self) -> bool {
        let current = self.current();
        matches!(current.kind, Kind::Lt | Kind::Gt)
            && self.tokens.get(self.pos + 1).is_some_and(|next| {
                next.kind == current.kind && next.span.start == current.span.end
            })
    }
    /// `Name { field: ...` starts a record literal only after a capitalized path,
    /// so `if flag { x }` and `match value { ... }` keep their block meaning.
    fn record_literal_ahead(&self, left: &Expr) -> bool {
        let last = match &left.kind {
            ExprKind::Name(name) | ExprKind::Field { name, .. } => name,
            ExprKind::Specialize { callee, .. } => match &callee.kind {
                ExprKind::Name(name) | ExprKind::Field { name, .. } => name,
                _ => return false,
            },
            _ => return false,
        };
        last.starts_with(|c: char| c.is_ascii_uppercase())
            && self.at(&Kind::LBrace)
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(Kind::Ident(_))
            )
            && self
                .tokens
                .get(self.pos + 2)
                .is_some_and(|t| t.kind == Kind::Colon)
    }
    fn prefix(&mut self) -> Result<Expr> {
        let start = self.current().span;
        let kind = match self.current().kind.clone() {
            Kind::Ident(name) => {
                self.bump();
                ExprKind::Name(name)
            }
            Kind::Integer(value) => {
                self.bump();
                ExprKind::Integer(value)
            }
            Kind::Float(value) => {
                self.bump();
                ExprKind::Float(value)
            }
            Kind::String(value) => {
                self.bump();
                ExprKind::String(value)
            }
            Kind::Char(value) => {
                self.bump();
                ExprKind::Char(value)
            }
            Kind::True | Kind::False => ExprKind::Bool(self.bump().kind == Kind::True),
            Kind::Minus | Kind::Bang | Kind::Amp | Kind::Star => {
                let op = self.bump().kind;
                let mutable = op == Kind::Amp && self.eat(&Kind::Mut);
                let operand = Box::new(self.expr_bp(11)?);
                ExprKind::Unary {
                    op,
                    mutable,
                    operand,
                }
            }
            Kind::Return => {
                self.bump();
                let value = if self.at(&Kind::Semi) || self.at(&Kind::RBrace) {
                    None
                } else {
                    Some(Box::new(self.expr()?))
                };
                ExprKind::Return(value)
            }
            Kind::LParen => {
                self.bump();
                if self.eat(&Kind::RParen) {
                    ExprKind::Tuple(vec![])
                } else {
                    let first = self.expr()?;
                    if self.eat(&Kind::Comma) {
                        let mut values = vec![first];
                        values.extend(self.separated(Kind::RParen, |p| p.expr())?);
                        ExprKind::Tuple(values)
                    } else {
                        self.expect(&Kind::RParen, "')' after expression")?;
                        return Ok(Node::new(first.kind, self.since(start)));
                    }
                }
            }
            Kind::LBracket => {
                self.bump();
                ExprKind::Array(self.separated(Kind::RBracket, |p| p.expr())?)
            }
            Kind::Struct => {
                self.bump();
                self.expect(
                    &Kind::LBrace,
                    "'{' after 'struct' in a structural record literal",
                )?;
                let mut fields = Vec::new();
                while !self.eat(&Kind::RBrace) {
                    let name = self.ident()?;
                    self.expect(&Kind::Colon, "':' after a structural record field name")?;
                    fields.push((name, self.expr()?));
                    if self.eat(&Kind::RBrace) {
                        break;
                    }
                    self.expect(&Kind::Comma, "',' between structural record fields")?;
                }
                if fields.is_empty() {
                    return Err(Diagnostic::new(
                        self.since(start),
                        "a structural record literal needs at least one field",
                    ));
                }
                ExprKind::StructuralLiteral(fields)
            }
            Kind::LBrace => ExprKind::Block(self.block()?),
            Kind::Handle => {
                self.bump();
                let operation = self.ident()?;
                self.expect(&Kind::Colon, "':' after the handled operation name")?;
                let parameter = Box::new(self.ty()?);
                self.expect(&Kind::Arrow, "'->' in a handled operation signature")?;
                let result = Box::new(self.ty()?);
                self.expect(&Kind::With, "'with' before the handler expression")?;
                let handler = Box::new(self.expr()?);
                let body = Box::new(self.block()?);
                ExprKind::Handle {
                    operation,
                    parameter,
                    result,
                    handler,
                    body,
                }
            }
            Kind::Perform => {
                self.bump();
                let operation = self.ident()?;
                self.expect(&Kind::LParen, "'(' after the performed operation name")?;
                let value = Box::new(self.expr()?);
                self.expect(&Kind::RParen, "')' after the performed operation payload")?;
                ExprKind::Perform { operation, value }
            }
            Kind::Fn => ExprKind::Lambda(Box::new(self.lambda()?)),
            Kind::While => {
                self.bump();
                let condition = Box::new(self.expr()?);
                let body = self.block()?;
                ExprKind::While { condition, body }
            }
            Kind::Loop => {
                self.bump();
                ExprKind::Loop(self.block()?)
            }
            Kind::Break => {
                self.bump();
                let value = if self.at(&Kind::Semi) || self.at(&Kind::RBrace) {
                    None
                } else {
                    Some(Box::new(self.expr()?))
                };
                ExprKind::Break(value)
            }
            Kind::Continue => {
                self.bump();
                ExprKind::Continue
            }
            Kind::If => {
                self.bump();
                let condition = Box::new(self.expr()?);
                let then = self.block()?;
                let otherwise = if self.eat(&Kind::Else) {
                    if self.at(&Kind::If) {
                        Some(Box::new(self.nested(|p| p.prefix())?))
                    } else {
                        let block = self.block()?;
                        let span = block.span;
                        Some(Box::new(Node::new(ExprKind::Block(block), span)))
                    }
                } else {
                    None
                };
                ExprKind::If {
                    condition,
                    then,
                    otherwise,
                }
            }
            Kind::Match => {
                self.bump();
                let value = Box::new(self.expr()?);
                self.expect(&Kind::LBrace, "'{' before match arms")?;
                let arms = self.separated(Kind::RBrace, |p| {
                    let start = p.current().span;
                    let pattern = p.pattern()?;
                    let guard = if p.eat(&Kind::If) {
                        Some(p.expr()?)
                    } else {
                        None
                    };
                    p.expect(&Kind::FatArrow, "'=>' after match pattern or guard")?;
                    let body = p.expr()?;
                    Ok(Arm {
                        pattern,
                        guard,
                        body,
                        span: p.since(start),
                    })
                })?;
                ExprKind::Match { value, arms }
            }
            _ => {
                return Err(
                    self.error("expected an expression; this syntax may not be implemented yet")
                );
            }
        };
        Ok(Node::new(kind, self.since(start)))
    }
    /// Parse an explicitly typed lambda. Kept out of `prefix` so the nested
    /// parenthesis budget is not consumed by this branch's large locals.
    #[inline(never)]
    fn lambda(&mut self) -> Result<Lambda> {
        self.bump();
        self.expect(&Kind::LParen, "'(' before lambda parameters")?;
        let parameters = self.separated(Kind::RParen, |p| {
            let start = p.current().span;
            let name = p.ident()?;
            p.expect(&Kind::Colon, "':' after lambda parameter name")?;
            let ty = p.ty()?;
            Ok(Parameter {
                erased: false,
                name,
                ty,
                span: p.since(start),
            })
        })?;
        self.expect(&Kind::Arrow, "'->' and an explicit lambda result type")?;
        let result = self.ty()?;
        let effects = self.effects()?;
        let body = self.block()?;
        Ok(Lambda {
            parameters,
            result,
            effects,
            body,
        })
    }
    fn pattern(&mut self) -> Result<Pattern> {
        self.nested(|p| p.pattern_inner())
    }
    fn pattern_inner(&mut self) -> Result<Pattern> {
        let start = self.current().span;
        let mut alternatives = vec![self.pattern_atom()?];
        while self.eat(&Kind::Pipe) {
            alternatives.push(self.pattern_atom()?);
        }
        if alternatives.len() == 1 {
            Ok(alternatives.pop().unwrap())
        } else {
            Ok(Node::new(PatternKind::Or(alternatives), self.since(start)))
        }
    }
    fn pattern_atom(&mut self) -> Result<Pattern> {
        let start = self.current().span;
        // Try `Type @ pattern` first. A full type is attempted with
        // backtracking so array, generic, and float-free type forms work in
        // pattern position without changing the meaning of ordinary patterns.
        let saved = (self.pos, self.depth);
        if let Ok(ty) = self.type_bp(4)
            && self.eat(&Kind::At)
        {
            let inner = Box::new(self.pattern()?);
            return Ok(Node::new(
                PatternKind::Type { ty, inner },
                self.since(start),
            ));
        }
        self.pos = saved.0;
        self.depth = saved.1;
        let kind = match self.current().kind.clone() {
            Kind::Float(_) => {
                return Err(self.error(
                    "floating-point literal patterns are not supported; compare with == in a match guard",
                ));
            }
            Kind::Integer(value) => {
                self.bump();
                PatternKind::Integer(value)
            }
            Kind::Minus => {
                self.bump();
                let next = self.bump().kind;
                if matches!(next, Kind::Float(_)) {
                    return Err(self.error(
                        "floating-point literal patterns are not supported; compare with == in a match guard",
                    ));
                }
                let Kind::Integer(value) = next else {
                    return Err(self.error("expected integer after '-' in pattern"));
                };
                PatternKind::Integer(format!("-{value}"))
            }
            Kind::String(value) => {
                self.bump();
                PatternKind::String(value)
            }
            Kind::Char(value) => {
                self.bump();
                PatternKind::Char(value)
            }
            Kind::True | Kind::False => PatternKind::Bool(self.bump().kind == Kind::True),
            Kind::DotDot => {
                return Err(
                    self.error("rest patterns are only supported directly inside slice patterns")
                );
            }
            Kind::LParen => {
                self.bump();
                if self.eat(&Kind::RParen) {
                    PatternKind::Tuple(vec![])
                } else {
                    let first = self.pattern()?;
                    if self.eat(&Kind::Comma) {
                        let mut patterns = vec![first];
                        patterns.extend(self.separated(Kind::RParen, |p| p.pattern())?);
                        PatternKind::Tuple(patterns)
                    } else {
                        self.expect(&Kind::RParen, "')' after pattern")?;
                        return Ok(Node::new(first.kind, self.since(start)));
                    }
                }
            }
            Kind::LBracket => {
                self.bump();
                let elements = self.separated(Kind::RBracket, |p| {
                    if p.at(&Kind::DotDot) {
                        let span = p.bump().span;
                        let name = if matches!(p.current().kind, Kind::Ident(_)) {
                            Some(p.ident()?)
                        } else {
                            None
                        };
                        Ok(Node::new(PatternKind::Rest(name), span))
                    } else {
                        p.pattern()
                    }
                })?;
                if elements
                    .iter()
                    .filter(|p| matches!(p.kind, PatternKind::Rest(_)))
                    .count()
                    > 1
                {
                    return Err(Diagnostic::new(
                        self.since(start),
                        "slice pattern can contain at most one '..'",
                    ));
                }
                PatternKind::Slice(elements)
            }
            Kind::Struct => {
                self.bump();
                self.expect(&Kind::LBrace, "'{' after 'struct' in a structural pattern")?;
                let mut fields = Vec::new();
                let mut rest = false;
                while !self.eat(&Kind::RBrace) {
                    if self.eat(&Kind::DotDot) {
                        rest = true;
                        self.eat(&Kind::Comma);
                        self.expect(&Kind::RBrace, "'}' after structural rest pattern")?;
                        break;
                    }
                    let field_span = self.current().span;
                    let name = self.ident()?;
                    let value = if self.eat(&Kind::Colon) {
                        self.pattern()?
                    } else {
                        Node::new(PatternKind::Name(vec![name.clone()]), field_span)
                    };
                    fields.push((name, value));
                    if self.eat(&Kind::RBrace) {
                        break;
                    }
                    self.expect(&Kind::Comma, "',' between structural pattern fields")?;
                }
                PatternKind::Structural { fields, rest }
            }
            Kind::Ident(_) => {
                let path = self.path()?;
                if path == ["_"] {
                    PatternKind::Wildcard
                } else if self.eat(&Kind::LParen) {
                    let fields = self.separated(Kind::RParen, |p| p.pattern())?;
                    PatternKind::Constructor { path, fields }
                } else if self.eat(&Kind::LBrace) {
                    let mut fields = Vec::new();
                    while !self.eat(&Kind::RBrace) {
                        if self.eat(&Kind::DotDot) {
                            // Omitted fields already have checked drop
                            // semantics; a final '..' spells that explicitly.
                            self.eat(&Kind::Comma);
                            self.expect(&Kind::RBrace, "'}' after final record rest pattern")?;
                            break;
                        }
                        let start = self.current().span;
                        let name = self.ident()?;
                        let value = if self.eat(&Kind::Colon) {
                            self.pattern()?
                        } else {
                            Node::new(PatternKind::Name(vec![name.clone()]), start)
                        };
                        fields.push((name, value));
                        if self.eat(&Kind::RBrace) {
                            break;
                        }
                        self.expect(&Kind::Comma, "',' between record pattern fields")?;
                    }
                    PatternKind::Record { path, fields }
                } else {
                    PatternKind::Name(path)
                }
            }
            _ => return Err(self.error("expected a pattern")),
        };
        Ok(Node::new(kind, self.since(start)))
    }
}
