//! A recursive-descent parser for the phase-1 subset. Constructs from later phases are
//! recognized and reported as not implemented (E0901), so a program never fails silently.

use std::collections::HashSet;

use crate::arena::Arena;
use crate::ast::*;
use crate::diag::{Code, Diagnostics, Planned, codes};
use crate::intern::Interner;
use crate::lexer::tokenize;
use crate::source::{SourceFile, Span};
use crate::token::{FPart, Keyword as Kw, Token, TokenKind as T, TokenValue, opener, track};

/// Parse failures are already reported when this is `Err`; callers only recover.
type PResult<X> = Result<X, ()>;

/// How deeply expressions and blocks may nest. Each operator of a chain such as `a + b + c`,
/// and each link of a call chain such as `a.f().g()`, counts as a level, because the checker
/// and interpreter recurse once per level. Deeper code is rejected instead of overflowing
/// the stack (OPEN_QUESTIONS P5).
pub const MAX_NESTING: u32 = 1_000;

/// Where error recovery stops: at the end of a statement or of an item.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stop {
    Stmt,
    Item,
}

/// Where a function is declared, which decides whether it takes `self` and has a body.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FnKind {
    /// A module's function, which takes no `self`.
    Free,
    /// A method or associated function in an `impl` block.
    Method,
    /// A method of an interface, declared without a body (Q13).
    Signature,
}

pub fn parse_module(file: &SourceFile, name: &str, diags: &mut Diagnostics) -> Module {
    let tokens = tokenize(&file.text, 0, diags);
    let module = Module {
        name: name.to_string(),
        items: Vec::new(),
        exprs: Arena::new(),
        stmts: Arena::new(),
        types: Arena::new(),
        pats: Arena::new(),
        interner: Interner::default(),
        poisoned: HashSet::new(),
        impls: HashSet::new(),
        tuple_impls: false,
    };
    let mut parser = Parser {
        file,
        tokens,
        pos: 0,
        diags,
        m: module,
        depth: 0,
        stmt_indent: 0,
        item_indent: 0,
        recovered: false,
        unclosed_reported: false,
        unclosed_blocks: 0,
        too_deep_reported: false,
        field_indent: None,
        arm_depth: 0,
    };
    parser.items();
    parser.m
}

struct Parser<'a> {
    file: &'a SourceFile,
    tokens: Vec<Token>,
    pos: usize,
    diags: &'a mut Diagnostics,
    m: Module,
    /// The nesting level being parsed, limited by [`MAX_NESTING`].
    depth: u32,
    /// The indentation of the line where the current statement or item starts. A block
    /// should close at the same indentation.
    stmt_indent: usize,
    /// The indentation of the line where the current item starts.
    item_indent: usize,
    /// Set when the current function body needed error recovery.
    recovered: bool,
    /// Set once an unclosed `{` has been reported in the current item, so the blocks around
    /// it close without reporting it again.
    unclosed_reported: bool,
    /// How many blocks have ended without being closed, so a `match` arm whose body is one
    /// statement knows that a block inside it ended before the next arm.
    unclosed_blocks: usize,
    /// Set once a statement of a body, or an item outside one, has nested too deeply, so the
    /// code left at that depth after recovery isn't reported again (§15.1).
    too_deep_reported: bool,
    /// The indentation of the record field being parsed. A line of a block in its `where`
    /// that is no deeper starts the next field, so the block was never closed.
    field_indent: Option<usize>,
    /// How many `match`es' arms are being parsed. Within them, a line with `=>` starts an arm
    /// (see [`Parser::starts_arm`]).
    arm_depth: u32,
}

impl Parser<'_> {
    // ---- token helpers ----

    fn peek(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn kind(&self) -> T {
        self.peek().kind
    }

    fn nth(&self, n: usize) -> T {
        self.tokens.get(self.pos + n).map_or(T::Eof, |t| t.kind)
    }

    fn at(&self, kind: T) -> bool {
        self.kind() == kind
    }

    fn at_kw(&self, kw: Kw) -> bool {
        self.kind() == T::Keyword(kw)
    }

    fn bump(&mut self) -> Token {
        let token = self.peek().clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        token
    }

    fn eat(&mut self, kind: T) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn prev_span(&self) -> Span {
        if self.pos == 0 { Span::default() } else { self.tokens[self.pos - 1].span }
    }

    fn skip_newlines(&mut self) {
        while self.at(T::Newline) {
            self.bump();
        }
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.diags.error(code, span, message);
    }

    fn unexpected<X>(&mut self, expected: &str) -> PResult<X> {
        let (span, found) = (self.peek().span, self.kind().describe());
        self.error(codes::UNEXPECTED_TOKEN, span, format!("expected {expected}, found {found}"));
        Err(())
    }

    fn expect(&mut self, kind: T, expected: &str) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { self.unexpected(expected) }
    }

    /// Reports `what` (a plural phrase) as not implemented yet, at the current token.
    fn not_implemented<X>(&mut self, what: &str, planned: Planned) -> PResult<X> {
        let span = self.peek().span;
        self.diags.not_implemented(span, what, planned);
        Err(())
    }

    fn intern(&mut self, span: Span) -> Ident {
        let file = self.file;
        Ident { sym: self.m.interner.intern(file.slice(span)), span }
    }

    fn ident(&mut self, expected: &str) -> PResult<Ident> {
        if self.at(T::Ident) {
            let token = self.bump();
            Ok(self.intern(token.span))
        } else {
            self.unexpected(expected)
        }
    }

    /// A name after `.` or in a module path, where keywords are allowed (REFERENCE §2).
    fn member_name(&mut self, expected: &str) -> PResult<Ident> {
        match self.kind() {
            T::Ident | T::Keyword(_) => {
                let token = self.bump();
                Ok(self.intern(token.span))
            }
            _ => self.unexpected(expected),
        }
    }

    fn alloc(&mut self, kind: ExprKind, span: Span) -> ExprId {
        self.m.exprs.alloc(Expr { kind, span })
    }

    fn span_of(&self, e: ExprId) -> Span {
        self.m.exprs[e].span
    }

    /// The indentation of the line holding `span`, with tabs at every fourth column.
    fn indent(&self, span: Span) -> usize {
        let text = self.file.text.as_bytes();
        let line_start = text[..span.lo as usize].iter().rposition(|&b| b == b'\n').map_or(0, |i| i + 1);
        let mut width = 0;
        for &b in &text[line_start..] {
            match b {
                b' ' => width += 1,
                b'\t' => width = (width / 4 + 1) * 4,
                _ => break,
            }
        }
        width
    }

    /// Whether the current token is a keyword that starts an item, such as `fn`, `pub` or
    /// `record`, at the start of a line no deeper than the current item. One nested in a
    /// later-phase item such as an `impl` block is deeper.
    fn starts_item(&self) -> bool {
        let T::Keyword(kw) = self.kind() else { return false };
        let item = kw == Kw::Pub || item_keyword(kw);
        let span = self.peek().span;
        item && self.starts_line(span) && self.indent(span) <= self.item_indent
    }

    /// Whether `span` is the first token on its line.
    fn starts_line(&self, span: Span) -> bool {
        let text = &self.file.text.as_bytes()[..span.lo as usize];
        text.iter().rev().take_while(|&&b| b != b'\n').all(|&b| b == b' ' || b == b'\t')
    }

    fn unclosed<X>(&mut self, open: &Token) -> PResult<X> {
        let what = open.kind.describe();
        self.error(codes::UNEXPECTED_TOKEN, open.span, format!("this {what} is never closed"));
        Err(())
    }

    /// Whether the current line is a `match` arm: it starts a line and has a `=>` outside
    /// brackets. Nothing but an arm has one, so in an arm's block that was never closed, such
    /// a line starts the next arm.
    fn starts_arm(&self) -> bool {
        if self.arm_depth == 0 || !self.starts_line(self.peek().span) {
            return false;
        }
        let mut depth = 0usize;
        for token in &self.tokens[self.pos..] {
            match token.kind {
                T::LParen | T::LBracket | T::LBrace => depth += 1,
                T::RParen | T::RBracket | T::RBrace if depth == 0 => return false,
                T::RParen | T::RBracket | T::RBrace => depth -= 1,
                T::FatArrow if depth == 0 => return true,
                T::Newline | T::Eof if depth == 0 => return false,
                _ => {}
            }
        }
        false
    }

    /// Expects the bracket that closes `open`. When the next token starts a line no deeper
    /// than the line that opened the bracket, the bracket was most likely never closed, so
    /// that is what is reported.
    fn close(&mut self, open: &Token, kind: T, expected: &str) -> PResult<Token> {
        if self.at(kind) {
            return Ok(self.bump());
        }
        let next = self.peek().span;
        if self.at(T::Eof) || (self.starts_line(next) && self.indent(next) <= self.indent(open.span)) {
            return self.unclosed(open);
        }
        self.unexpected(expected)
    }

    /// Skips a bracketed group, such as type arguments, whose contents phase 1 doesn't parse.
    fn skip_group(&mut self) -> PResult<()> {
        let open = self.bump();
        let mut stack = vec![open.kind];
        loop {
            let kind = self.kind();
            match kind {
                T::LParen | T::LBracket | T::LBrace => stack.push(kind),
                T::RParen | T::RBracket | T::RBrace => {
                    // A closer that matches nothing open here belongs to an enclosing construct.
                    if stack.last() != Some(&opener(kind)) {
                        return self.unclosed(&open);
                    }
                    stack.pop();
                    if stack.is_empty() {
                        self.bump();
                        return Ok(());
                    }
                }
                T::Eof => return self.unclosed(&open),
                _ => {}
            }
            self.bump();
        }
    }

    /// Enters one more level of nesting; see [`MAX_NESTING`].
    fn deeper(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > MAX_NESTING {
            if std::mem::replace(&mut self.too_deep_reported, true) {
                return Err(());
            }
            let span = self.peek().span;
            self.error(
                codes::NESTING_TOO_DEEP,
                span,
                format!("this nests more than {MAX_NESTING} levels deep; split it into smaller expressions"),
            );
            return Err(());
        }
        Ok(())
    }

    /// Parses `f` one level deeper, and restores the level afterwards.
    fn nested<X>(&mut self, f: impl FnOnce(&mut Self) -> PResult<X>) -> PResult<X> {
        let base = self.depth;
        let result = match self.deeper() {
            Ok(()) => f(self),
            Err(()) => Err(()),
        };
        self.depth = base;
        result
    }

    /// Skips the rest of a statement or item that failed to parse, which began at token
    /// `start`. Brackets opened since `start` are skipped to their close, wherever inside
    /// them the error was. A statement also ends before the `}` that closes its block, and
    /// both end before the next item (see [`Parser::starts_item`]).
    fn recover(&mut self, start: usize, stop: Stop) {
        self.recovered = true;
        let mut open = Vec::new();
        for token in &self.tokens[start..self.pos] {
            track(&mut open, token.kind);
        }
        loop {
            let kind = self.kind();
            match kind {
                T::Eof => return,
                T::Newline if open.is_empty() => return,
                T::RBrace if stop == Stop::Stmt && !open.contains(&T::LBrace) => return,
                T::Keyword(_) if self.pos > start && self.starts_item() => return,
                _ => track(&mut open, kind),
            }
            self.bump();
        }
    }

    // ---- items ----

    fn items(&mut self) {
        loop {
            self.skip_newlines();
            if self.at(T::Eof) {
                break;
            }
            let start = self.pos;
            self.depth = 0;
            (self.unclosed_reported, self.too_deep_reported) = (false, false);
            self.stmt_indent = self.indent(self.peek().span);
            self.item_indent = self.stmt_indent;
            match self.item() {
                Ok(Some(item)) => {
                    self.m.items.push(item);
                    // A doc comment may follow an item on its line; it documents the next one.
                    // An item whose block was never closed ends right before the next item.
                    if !matches!(self.kind(), T::Newline | T::Eof | T::DocComment) && !self.starts_item() {
                        let _ = self.unexpected::<()>("end of line after the item");
                        self.recover(start, Stop::Item);
                    }
                }
                Ok(None) => {}
                Err(()) => self.recover(start, Stop::Item),
            }
            if self.pos == start {
                self.bump();
            }
        }
    }

    fn item(&mut self) -> PResult<Option<Item>> {
        let mut doc: Option<String> = None;
        let mut doc_span = None;
        while self.at(T::DocComment) {
            let token = self.bump();
            doc_span = Some(token.span);
            if let TokenValue::Doc(text) = token.value {
                match &mut doc {
                    Some(d) => {
                        d.push('\n');
                        d.push_str(&text);
                    }
                    None => doc = Some(text),
                }
            }
            self.skip_newlines();
        }
        if self.at(T::Eof) {
            if let Some(span) = doc_span {
                self.error(codes::UNEXPECTED_TOKEN, span, "a doc comment documents the next item, but none follows");
            }
            return Ok(None);
        }
        let start = self.peek().span;
        let (vis, written) = self.visibility()?;
        let kind = match self.kind() {
            T::Keyword(Kw::Fn) => ItemKind::Fn(self.fn_decl()?),
            T::Keyword(Kw::Use) if vis != Visibility::Private => {
                return self.not_implemented("re-exports (`pub use`)", Planned::Unscheduled);
            }
            T::Keyword(Kw::Use) => ItemKind::Use(self.use_decl()?),
            T::Keyword(Kw::Record) => ItemKind::Record(self.record_decl()?),
            T::Keyword(Kw::Unique) if self.nth(1) == T::Keyword(Kw::Record) => {
                self.bump();
                ItemKind::Record(RecordDecl { unique: true, ..self.record_decl()? })
            }
            T::Keyword(Kw::Unique) => {
                self.poison_declared_type();
                let span = self.peek().span;
                self.error(codes::UNEXPECTED_TOKEN, span, "`unique` marks a record, as in `unique record Token { … }`");
                return Err(());
            }
            T::Keyword(Kw::Enum) => ItemKind::Enum(self.enum_decl()?),
            T::Keyword(Kw::Impl) => {
                // The block is kept, so its methods are still checked.
                if vis != Visibility::Private && written {
                    let span = start.to(self.prev_span());
                    self.error(
                        codes::UNEXPECTED_TOKEN,
                        span,
                        "an `impl` block has no visibility of its own; mark its methods `pub` instead",
                    );
                }
                ItemKind::Impl(self.impl_decl()?)
            }
            T::Keyword(Kw::Interface) => ItemKind::Interface(self.interface_decl()?),
            T::Keyword(Kw::Example) => {
                // The example is kept, so it is still checked.
                if vis != Visibility::Private && written {
                    let span = start.to(self.prev_span());
                    self.error(codes::UNEXPECTED_TOKEN, span, "an example has no name, so it is never exported");
                }
                ItemKind::Example(self.example_decl()?)
            }
            T::Keyword(kw) => match planned_item(kw) {
                Some((what, planned)) => {
                    self.poison_declared_type();
                    return self.not_implemented(what, planned);
                }
                None => return self.unexpected("an item such as `fn` or `use`"),
            },
            _ => return self.unexpected("an item such as `fn` or `use`"),
        };
        Ok(Some(Item { kind, vis, doc, span: start.to(self.prev_span()) }))
    }

    /// `pub`, `pub(pkg)` or nothing, and whether it was written without a mistake.
    fn visibility(&mut self) -> PResult<(Visibility, bool)> {
        if !self.eat(T::Keyword(Kw::Pub)) {
            return Ok((Visibility::Private, true));
        }
        if !self.eat(T::LParen) {
            return Ok((Visibility::Pub, true));
        }
        // A broken `pub(…)` is reported once, and the rest of it is skipped through its `)` or
        // up to the item's keyword, so the item is still declared (§15.1). It most likely
        // meant `pub(pkg)`, the only restricted visibility.
        let written = match self.pub_scope() {
            Ok(written) => written,
            Err(()) if self.skip_broken_visibility() => false,
            Err(()) => return Err(()),
        };
        Ok((Visibility::PubPkg, written))
    }

    /// The `pkg)` of `pub(pkg)`, and whether it says `pkg`.
    fn pub_scope(&mut self) -> PResult<bool> {
        let scope = self.ident("`pkg`")?;
        let pkg = self.m.text(scope.sym) == "pkg";
        if !pkg {
            self.error(codes::UNEXPECTED_TOKEN, scope.span, "the only restricted visibility is `pub(pkg)`");
        }
        self.expect(T::RParen, "`)`")?;
        Ok(pkg)
    }

    /// Skips what is left of a broken `pub(…)` on its line, through its `)` or up to an item's
    /// keyword. `false` when the line has neither, so the item is lost.
    fn skip_broken_visibility(&mut self) -> bool {
        loop {
            match self.kind() {
                T::RParen => {
                    self.bump();
                    return true;
                }
                T::Keyword(kw) if item_keyword(kw) => return true,
                T::Newline | T::Eof => return false,
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// Marks the type a later-phase declaration such as `unique record Token`, `enum Shape`
    /// or `cap interface Logger` names, so that its uses aren't reported as unknown types.
    fn poison_declared_type(&mut self) {
        let declares_type = |kind| {
            matches!(
                kind,
                T::Keyword(
                    Kw::Unique
                        | Kw::Opaque
                        | Kw::Resource
                        | Kw::Record
                        | Kw::Enum
                        | Kw::Type
                        | Kw::Distinct
                        | Kw::Interface
                        | Kw::Cap
                )
            )
        };
        let mut i = self.pos;
        while self.tokens.get(i).is_some_and(|t| declares_type(t.kind)) {
            i += 1;
        }
        if i > self.pos
            && let Some(token) = self.tokens.get(i).filter(|t| t.kind == T::Ident)
        {
            let name = self.intern(token.span);
            self.m.poisoned.insert(name.sym);
        }
    }

    /// Notes the type a rejected `impl` block, whose keyword is token `at`, is for: `Point`
    /// in `impl Point` and in `impl Show for Point`, or any tuple type in `impl Show for (A, B)`.
    fn note_impl_target(&mut self, at: usize) {
        let mut i = at + 1;
        let mut target = None;
        while let Some(token) = self.tokens.get(i) {
            match token.kind {
                T::Ident => target = Some(token.span),
                T::Keyword(Kw::For) => {}
                T::LParen => {
                    self.m.tuple_impls = true;
                    return;
                }
                T::LBracket => {
                    // Skips type parameters and arguments, such as `impl[T] Show for Box[T]`.
                    let mut depth = 0;
                    while let Some(token) = self.tokens.get(i) {
                        match token.kind {
                            T::LBracket => depth += 1,
                            T::RBracket => depth -= 1,
                            T::Newline | T::LBrace | T::Eof => break,
                            _ => {}
                        }
                        if depth == 0 {
                            break;
                        }
                        i += 1;
                    }
                }
                _ => break,
            }
            i += 1;
        }
        if let Some(span) = target {
            let name = self.intern(span);
            self.m.impls.insert(name.sym);
        }
    }

    fn use_decl(&mut self) -> PResult<UseDecl> {
        self.bump();
        let mut path = vec![self.member_name("a module name")?];
        while self.eat(T::Dot) {
            path.push(self.member_name("a module name")?);
        }
        let mut names = Vec::new();
        if self.at(T::LBrace) {
            let open = self.bump();
            loop {
                self.skip_newlines();
                if self.eat(T::RBrace) {
                    break;
                }
                let name = self.ident("an imported name")?;
                let alias = if self.eat(T::Keyword(Kw::As)) { Some(self.ident("a name after `as`")?) } else { None };
                names.push(UseName { name, alias });
                self.skip_newlines();
                if !self.eat(T::Comma) {
                    self.skip_newlines();
                    self.close(&open, T::RBrace, "`,` or `}`")?;
                    break;
                }
            }
        }
        Ok(UseDecl { path, names })
    }

    fn record_decl(&mut self) -> PResult<RecordDecl> {
        self.bump();
        let name = self.ident("a record name")?;
        let decl = self.record_rest(name);
        if decl.is_err() {
            self.m.poisoned.insert(name.sym);
        }
        decl
    }

    fn record_rest(&mut self, name: Ident) -> PResult<RecordDecl> {
        if self.at(T::LBracket) {
            return self.not_implemented("generic records", Planned::Phase(2));
        }
        let derives = self.derives()?;
        let open = self.expect(T::LBrace, "`{` and the record's fields")?;
        let mut fields = Vec::new();
        loop {
            while matches!(self.kind(), T::Newline | T::DocComment) {
                self.bump();
            }
            if self.eat(T::RBrace) {
                break;
            }
            if self.at(T::Eof) || self.starts_item() {
                return self.unclosed(&open);
            }
            let indent = self.indent(self.peek().span);
            let saved = (self.stmt_indent, self.field_indent);
            (self.stmt_indent, self.field_indent) = (indent, Some(indent));
            let field = self.field_decl();
            (self.stmt_indent, self.field_indent) = saved;
            fields.push(field?);
            // A field's `where` block that was never closed ends before the next field's line.
            let next = self.peek().span;
            if !self.eat(T::Comma) && !self.at(T::Newline) && !(self.unclosed_reported && self.starts_line(next)) {
                self.close(&open, T::RBrace, "`,`, a new line or `}`")?;
                break;
            }
        }
        let refinement = if self.eat(T::Keyword(Kw::Where)) { Some(self.expr()?) } else { None };
        Ok(RecordDecl { name, unique: false, derives, fields, refinement })
    }

    /// `derives(Eq, Show)`, or nothing.
    fn derives(&mut self) -> PResult<Vec<Ident>> {
        let mut derives = Vec::new();
        if self.eat(T::Keyword(Kw::Derives)) {
            let open = self.expect(T::LParen, "`(` and the interfaces to derive")?;
            while !self.at(T::RParen) {
                derives.push(self.ident("an interface name")?);
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.close(&open, T::RParen, "`,` or `)`")?;
        }
        Ok(derives)
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.bump();
        let name = self.ident("an enum name")?;
        let decl = self.enum_rest(name);
        if decl.is_err() {
            self.m.poisoned.insert(name.sym);
        }
        decl
    }

    fn enum_rest(&mut self, name: Ident) -> PResult<EnumDecl> {
        if self.at(T::LBracket) {
            return self.not_implemented("generic enums", Planned::Phase(2));
        }
        let derives = self.derives()?;
        let open = self.expect(T::LBrace, "`{` and the enum's variants")?;
        let mut variants = Vec::new();
        loop {
            while matches!(self.kind(), T::Newline | T::DocComment) {
                self.bump();
            }
            if self.eat(T::RBrace) {
                break;
            }
            if self.at(T::Eof) || self.starts_item() {
                return self.unclosed(&open);
            }
            let saved = self.stmt_indent;
            self.stmt_indent = self.indent(self.peek().span);
            let variant = self.variant_decl();
            self.stmt_indent = saved;
            variants.push(variant?);
            let next = self.peek().span;
            if !self.eat(T::Comma) && !self.at(T::Newline) && !(self.unclosed_reported && self.starts_line(next)) {
                self.close(&open, T::RBrace, "`,`, a new line or `}`")?;
                break;
            }
        }
        Ok(EnumDecl { name, derives, variants })
    }

    /// `Circle(radius: Float)` or `Empty`.
    fn variant_decl(&mut self) -> PResult<VariantDecl> {
        let name = self.ident("a variant name")?;
        let mut fields = Vec::new();
        if self.at(T::LParen) {
            let open = self.bump();
            if self.at(T::RParen) {
                let span = open.span.to(self.peek().span);
                self.error(codes::UNEXPECTED_TOKEN, span, "a variant without fields is written without parentheses");
                return Err(());
            }
            loop {
                let indent = self.indent(self.peek().span);
                let saved = (self.stmt_indent, self.field_indent);
                (self.stmt_indent, self.field_indent) = (indent, Some(indent));
                let field = self.field_decl();
                (self.stmt_indent, self.field_indent) = saved;
                fields.push(field?);
                if !self.eat(T::Comma) || self.at(T::RParen) {
                    break;
                }
            }
            // A field's `where` block that was never closed ends before the next line, and
            // has been reported, so the parentheses around it are not.
            if self.at(T::RParen) || !(self.unclosed_reported && self.starts_line(self.peek().span)) {
                self.close(&open, T::RParen, "`,` or `)`")?;
            }
        }
        Ok(VariantDecl { name, fields })
    }

    fn field_decl(&mut self) -> PResult<FieldDecl> {
        let name = self.ident("a field name")?;
        self.expect(T::Colon, "`:` and the field's type")?;
        let ty = self.type_expr()?;
        let refinement = if self.eat(T::Keyword(Kw::Where)) { Some(self.expr()?) } else { None };
        Ok(FieldDecl { name, ty, refinement })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        self.bump();
        let name = self.ident("a function name")?;
        let decl = self.fn_rest(name, FnKind::Free);
        if decl.is_err() {
            self.m.poisoned.insert(name.sym);
        }
        decl
    }

    /// `impl Span { … }` or `impl Show for Span { … }`. When the block is rejected, the
    /// methods it may have given its type aren't reported where they are used (§15.1).
    fn impl_decl(&mut self) -> PResult<ImplDecl> {
        let at = self.pos;
        let decl = self.impl_rest();
        if decl.is_err() {
            self.note_impl_target(at);
        }
        decl
    }

    fn impl_rest(&mut self) -> PResult<ImplDecl> {
        self.bump();
        if self.at(T::LBracket) {
            return self.not_implemented("generic `impl` blocks", Planned::Phase(2));
        }
        let first = self.type_expr()?;
        let (iface, target) = if self.eat(T::Keyword(Kw::For)) {
            if let TypeExprKind::Applied { args: Some(_), .. } = self.m.types[first].kind {
                let span = self.m.types[first].span;
                self.diags.not_implemented(span, "generic interfaces", Planned::Phase(2));
                return Err(());
            }
            let TypeExprKind::Named(iface) = self.m.types[first].kind else {
                let span = self.m.types[first].span;
                self.error(codes::UNEXPECTED_TOKEN, span, "expected the name of an interface before `for`");
                return Err(());
            };
            (Some(iface), self.type_expr()?)
        } else {
            (None, first)
        };
        if let TypeExprKind::Tuple(_) = self.m.types[target].kind {
            let span = self.m.types[target].span;
            self.diags.not_implemented(span, "implementations for tuple types", Planned::Phase(2));
            return Err(());
        }
        if let TypeExprKind::Applied { args: Some(_), .. } = self.m.types[target].kind {
            let span = self.m.types[target].span;
            self.diags.not_implemented(
                span,
                "implementations for generic types, such as `Option[Int]`,",
                Planned::Phase(2),
            );
            return Err(());
        }
        let open = self.expect(T::LBrace, "`{` and the block's methods")?;
        let (methods, recovered) = self.members(&open, Self::method)?;
        Ok(ImplDecl { iface, target, methods, recovered })
    }

    /// The members of an `impl` block or interface after its `{`, and whether a syntax error
    /// lost one. Each member starts a line. One that fails to parse is skipped up to the end
    /// of its line or the block's `}`, and the block keeps the others (§15.1).
    fn members<M>(&mut self, open: &Token, member: fn(&mut Self) -> PResult<M>) -> PResult<(Vec<M>, bool)> {
        let mut members = Vec::new();
        let mut recovered = false;
        let block_indent = self.item_indent;
        // When the block's braces balance, an item keyword in its own column, such as a
        // method written at column 0, is a member (§16). Otherwise it starts the next item,
        // and the block was never closed.
        let closed = self.closes();
        loop {
            while matches!(self.kind(), T::Newline | T::DocComment) {
                self.bump();
            }
            if self.eat(T::RBrace) {
                break;
            }
            if self.at(T::Eof) || (!closed && self.starts_item()) {
                return self.unclosed(open);
            }
            let start = self.pos;
            let indent = self.indent(self.peek().span);
            // A method's body that is never closed ends before the next method.
            (self.stmt_indent, self.item_indent, self.unclosed_reported) = (indent, indent, false);
            match member(self) {
                Ok(m) => {
                    members.push(m);
                    if !matches!(self.kind(), T::Newline | T::RBrace | T::Eof | T::DocComment) && !self.starts_item() {
                        let _ = self.unexpected::<()>("end of line after the method");
                        recovered = true;
                        self.recover(start, Stop::Stmt);
                    }
                }
                Err(()) => {
                    recovered = true;
                    self.recover(start, Stop::Stmt);
                }
            }
            self.item_indent = block_indent;
            if self.pos == start {
                self.bump();
            }
        }
        Ok((members, recovered))
    }

    /// Whether the block whose `{` was just read has a matching `}`.
    fn closes(&self) -> bool {
        let mut depth = 0usize;
        for token in &self.tokens[self.pos..] {
            match token.kind {
                T::LBrace => depth += 1,
                T::RBrace if depth == 0 => return true,
                T::RBrace => depth -= 1,
                _ => {}
            }
        }
        false
    }

    fn method(&mut self) -> PResult<Method> {
        let start = self.peek().span;
        let (vis, _) = self.visibility()?;
        if !self.at_kw(Kw::Fn) {
            return self.unexpected("a method, starting with `fn`");
        }
        self.bump();
        let name = self.ident("a method name")?;
        let decl = self.fn_rest(name, FnKind::Method)?;
        Ok(Method { vis, decl, span: start.to(self.prev_span()) })
    }

    /// `example f(…) == v` or `example f(…) fails P` (REFERENCE §14).
    fn example_decl(&mut self) -> PResult<ExampleDecl> {
        self.bump();
        let call = self.nested(Self::range)?;
        // Whether it builds a value instead, as `Some(1)` does, the checker tells.
        if !matches!(self.m.exprs[call].kind, ExprKind::Call { .. } | ExprKind::MethodCall { .. }) {
            let span = self.span_of(call);
            self.error(
                codes::UNEXPECTED_TOKEN,
                span,
                "an example tests a function or method call, as in `example f(…) == v`",
            );
            return Err(());
        }
        let expect = match self.kind() {
            T::EqEq => {
                self.bump();
                // The expected value is an operand of `==`, as the call is, or an `else` form
                // on one, so `f(x) == o else 0` compares with `o else 0` (OPEN_QUESTIONS P5).
                let value = self.nested(Self::range)?;
                if self.comparison_op()?.is_some() {
                    let span = self.peek().span;
                    self.error(
                        codes::CHAINED_COMPARISON,
                        span,
                        "comparisons cannot be chained; parenthesize the expected value",
                    );
                    return Err(());
                }
                if self.eat(T::Keyword(Kw::Else)) {
                    let fallback = self.fallback()?;
                    let span = self.span_of(value).to(self.prev_span());
                    Expectation::Equals(self.alloc(ExprKind::Else { value, fallback }, span))
                } else {
                    Expectation::Equals(value)
                }
            }
            T::Keyword(Kw::Fails) => {
                self.bump();
                Expectation::Fails(self.pattern()?)
            }
            _ => return self.unexpected("`==` or `fails` after the example's call"),
        };
        Ok(ExampleDecl { call, expect })
    }

    /// `interface Shape { fn area(self) -> Int }` (REFERENCE §4.9).
    fn interface_decl(&mut self) -> PResult<InterfaceDecl> {
        self.bump();
        let name = self.ident("an interface name")?;
        let decl = self.interface_rest(name);
        if decl.is_err() {
            self.m.poisoned.insert(name.sym);
        }
        decl
    }

    fn interface_rest(&mut self, name: Ident) -> PResult<InterfaceDecl> {
        if self.at(T::LBracket) {
            return self.not_implemented("generic interfaces", Planned::Phase(2));
        }
        let open = self.expect(T::LBrace, "`{` and the interface's methods")?;
        let (methods, recovered) = self.members(&open, |p| {
            if !p.at_kw(Kw::Fn) {
                return p.unexpected("a method, starting with `fn`");
            }
            p.bump();
            let name = p.ident("a method name")?;
            p.fn_rest(name, FnKind::Signature)
        })?;
        Ok(InterfaceDecl { name, methods, recovered })
    }

    /// `[T: Ord + Copy, U]` after a function's name (REFERENCE §4.8).
    fn generics(&mut self) -> PResult<Vec<GenericParam>> {
        let open = self.bump();
        let mut params = Vec::new();
        while !self.at(T::RBracket) {
            if self.at_kw(Kw::Effect) {
                return self.not_implemented("effect parameters", Planned::Phase(3));
            }
            let name = self.ident("a type parameter")?;
            let mut bounds = Vec::new();
            if self.eat(T::Colon) {
                loop {
                    if self.at_kw(Kw::Tag) {
                        return self.not_implemented("units and tags", Planned::PastV1);
                    }
                    bounds.push(self.ident("an interface")?);
                    if self.at(T::LBracket) {
                        return self.not_implemented("generic interfaces", Planned::Phase(2));
                    }
                    if !self.eat(T::Plus) {
                        break;
                    }
                }
            }
            params.push(GenericParam { name, bounds });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.close(&open, T::RBracket, "`,` or `]`")?;
        Ok(params)
    }

    /// `self`, `inout self` or `take self` at the start of a parameter list.
    fn receiver(&mut self, kind: FnKind) -> PResult<Option<Receiver>> {
        let start = self.peek().span;
        let mode = match (self.kind(), self.nth(1)) {
            (T::Keyword(Kw::SelfValue), _) => ParamMode::Borrow,
            (T::Keyword(Kw::Inout), T::Keyword(Kw::SelfValue)) => ParamMode::Inout,
            (T::Keyword(Kw::Take), T::Keyword(Kw::SelfValue)) => ParamMode::Take,
            _ => return Ok(None),
        };
        if mode != ParamMode::Borrow {
            self.bump();
        }
        self.bump();
        let span = start.to(self.prev_span());
        if kind == FnKind::Free {
            self.error(
                codes::UNEXPECTED_TOKEN,
                span,
                "only a method, in an `impl` block or an interface, takes `self`",
            );
            return Err(());
        }
        Ok(Some(Receiver { mode, span }))
    }

    fn fn_rest(&mut self, name: Ident, kind: FnKind) -> PResult<FnDecl> {
        let generics = match kind {
            _ if !self.at(T::LBracket) => Vec::new(),
            FnKind::Signature => return self.not_implemented("generic interface methods", Planned::Unscheduled),
            _ => self.generics()?,
        };
        let open = self.expect(T::LParen, "`(`")?;
        let receiver = self.receiver(kind)?;
        if receiver.is_some() && !self.at(T::RParen) {
            self.expect(T::Comma, "`,` or `)`")?;
        }
        let mut params = Vec::new();
        while !self.at(T::RParen) {
            params.push(self.param()?);
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.close(&open, T::RParen, "`,` or `)`")?;
        let ret = if self.eat(T::Arrow) { Some(self.type_expr()?) } else { None };
        let mut fails = None;
        loop {
            match self.kind() {
                T::Keyword(Kw::Fails) => {
                    let keyword = self.bump();
                    let ty = self.type_expr()?;
                    if fails.is_some() {
                        self.error(
                            codes::UNEXPECTED_TOKEN,
                            keyword.span,
                            "a function declares at most one `fails` clause (Q1)",
                        );
                    }
                    fails = Some(ty);
                }
                T::Keyword(Kw::Requires | Kw::Ensures) => {
                    return self.not_implemented("`requires` and `ensures` clauses", Planned::Phase(4));
                }
                T::Keyword(Kw::Needs | Kw::Uses | Kw::With) => {
                    return self.not_implemented("`needs`, `uses` and `with` clauses", Planned::Phase(3));
                }
                T::Keyword(Kw::Observes | Kw::Effects) => {
                    return self.not_implemented("`observes` and `effects` permissions", Planned::Phase(3));
                }
                T::Keyword(Kw::Where | Kw::Invariant) => {
                    return self.not_implemented("refinement clauses", Planned::Phase(5));
                }
                T::Keyword(Kw::Trusted) => return self.not_implemented("`trusted` clauses", Planned::Unscheduled),
                _ => break,
            }
        }
        if kind != FnKind::Signature {
            self.recovered = false;
            let body = self.block()?;
            return Ok(FnDecl {
                name,
                generics,
                receiver,
                params,
                ret,
                fails,
                body: Some(body),
                recovered: self.recovered,
            });
        }
        if receiver.is_none() {
            self.diags.not_implemented(name.span, "interface functions without `self`", Planned::Unscheduled);
            return Err(());
        }
        // The method is kept, so its implementations aren't reported again.
        if self.at(T::LBrace) {
            let span = self.peek().span;
            self.error(
                codes::UNEXPECTED_TOKEN,
                span,
                "an interface declares its methods without bodies; there are no default methods (Q13)",
            );
            self.block()?;
        }
        Ok(FnDecl { name, generics, receiver, params, ret, fails, body: None, recovered: false })
    }

    fn param(&mut self) -> PResult<Param> {
        if self.at_kw(Kw::SelfValue) {
            let span = self.peek().span;
            self.error(codes::UNEXPECTED_TOKEN, span, "a method's `self` comes before its other parameters");
            return Err(());
        }
        let name = self.ident("a parameter name")?;
        self.expect(T::Colon, "`:` and the parameter's type")?;
        let mode = match self.kind() {
            T::Keyword(Kw::Inout) => {
                self.bump();
                let partial = self.at(T::LParen)
                    && self.nth(1) == T::Ident
                    && self.file.slice(self.tokens[self.pos + 1].span) == "partial"
                    && self.nth(2) == T::RParen;
                if partial {
                    self.bump();
                    self.bump();
                    self.bump();
                    ParamMode::InoutPartial
                } else {
                    ParamMode::Inout
                }
            }
            T::Keyword(Kw::Take) => {
                self.bump();
                ParamMode::Take
            }
            T::Keyword(Kw::Keep) => {
                self.bump();
                ParamMode::Keep
            }
            _ => ParamMode::Borrow,
        };
        let ty = self.type_expr()?;
        let span = name.span.to(self.prev_span());
        Ok(Param { name, mode, ty, span })
    }

    fn type_expr(&mut self) -> PResult<TypeId> {
        let start = self.peek().span;
        let kind = match self.kind() {
            T::Ident => {
                let name = self.ident("a type")?;
                if self.at(T::LBracket) {
                    // A numeric type takes a unit, and `Array[T, N]` a length, which are not
                    // types (REFERENCE §4.2, §4.7).
                    let args = if takes_non_type_args(self.m.text(name.sym)) {
                        self.skip_group()?;
                        None
                    } else {
                        Some(self.type_args()?)
                    };
                    TypeExprKind::Applied { name, args }
                } else {
                    TypeExprKind::Named(name)
                }
            }
            T::Keyword(Kw::Fn) => return self.not_implemented("function types", Planned::Phase(2)),
            T::Keyword(Kw::Scoped) => return self.not_implemented("`scoped` function types", Planned::Phase(3)),
            T::Keyword(Kw::Any) => return self.not_implemented("`any` types", Planned::PastV1),
            T::Keyword(Kw::SelfType) => {
                self.bump();
                TypeExprKind::SelfType
            }
            T::LParen => TypeExprKind::Tuple(self.tuple(Self::type_expr, "tuple type")?),
            _ => return self.unexpected("a type"),
        };
        let span = start.to(self.prev_span());
        Ok(self.m.types.alloc(TypeExpr { kind, span }))
    }

    /// `[A, B]` after a type's name.
    fn type_args(&mut self) -> PResult<Vec<TypeId>> {
        let open = self.expect(T::LBracket, "`[`")?;
        let mut args = Vec::new();
        while !self.at(T::RBracket) {
            args.push(self.nested(Self::type_expr)?);
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.close(&open, T::RBracket, "`,` or `]`")?;
        Ok(args)
    }

    // ---- statements ----

    fn block(&mut self) -> PResult<Block> {
        let open = self.expect(T::LBrace, "`{`")?;
        let indent = self.stmt_indent;
        self.nested(|p| Ok(p.block_rest(&open, indent)))
    }

    /// Parses statements up to the `}` that closes `open`. A block that is never closed is
    /// reported where it opens, and ends where its enclosing block or item does: before a
    /// `}` indented less than the statement that opened it, before an item, in a field's
    /// `where` before the next field, in a `match` arm before the next arm, or at the end of
    /// the file.
    fn block_rest(&mut self, open: &Token, indent: usize) -> Block {
        let mut stmts = Vec::new();
        let mut lost = false;
        loop {
            // Each statement of a body may nest too deeply on its own.
            if self.depth <= 1 {
                self.too_deep_reported = false;
            }
            // A doc comment documents an item, so there is nothing for it to do in a block.
            while matches!(self.kind(), T::Newline | T::DocComment) {
                self.bump();
            }
            let next = self.peek().span;
            let unclosed = match self.kind() {
                T::RBrace if self.indent(next) >= indent || !self.starts_line(next) => {
                    self.bump();
                    break;
                }
                T::RBrace | T::Eof => true,
                _ if self.field_indent.is_some_and(|field| self.starts_line(next) && self.indent(next) <= field) => {
                    true
                }
                _ => self.starts_item() || self.starts_arm(),
            };
            if unclosed {
                self.recovered = true;
                if !self.unclosed_reported {
                    self.unclosed_reported = true;
                    let _ = self.unclosed::<()>(open);
                }
                self.unclosed_blocks += 1;
                return Block { stmts, span: open.span.to(self.prev_span()), unclosed: true, lost };
            }
            let start = self.pos;
            let saved = (self.depth, self.stmt_indent);
            self.stmt_indent = self.indent(next);
            let stmt = match self.stmt() {
                Ok(stmt) => {
                    // A statement whose block was never closed ends before the next item.
                    if !matches!(self.kind(), T::Newline | T::RBrace | T::Eof) && !self.starts_item() {
                        let _ = self.unexpected::<()>("end of statement");
                        self.recover(start, Stop::Stmt);
                        lost = true;
                    }
                    stmt
                }
                Err(()) => {
                    lost = true;
                    self.recover(start, Stop::Stmt);
                    if self.pos == start {
                        self.bump();
                    }
                    self.placeholder(start)
                }
            };
            (self.depth, self.stmt_indent) = saved;
            stmts.push(stmt);
        }
        Block { stmts, span: open.span.to(self.prev_span()), unclosed: false, lost }
    }

    /// Stands in for a statement that failed to parse. A `let` still binds the names its
    /// pattern has, with an unknown type, so later uses of them aren't reported again.
    fn placeholder(&mut self, start: usize) -> StmtId {
        let span = self.tokens[start].span.to(self.prev_span());
        let init = self.alloc(ExprKind::Error, span);
        let kind = match self.tokens[start].kind {
            T::Keyword(kw @ (Kw::Let | Kw::Var)) => {
                let pat = self.placeholder_pattern(start + 1);
                StmtKind::Let { mutable: kw == Kw::Var, pat, ty: None, init }
            }
            // A `check`'s `is` bindings scope over the rest of the block, so they are bound
            // here as a broken `let`'s are.
            T::Keyword(Kw::Check) => {
                let pat = self.placeholder_is_pattern(start + 1);
                StmtKind::Let { mutable: false, pat, ty: None, init }
            }
            _ => StmtKind::Expr(init),
        };
        self.m.stmts.alloc(Stmt { kind, span })
    }

    /// The names a broken `let` pattern starting at token `start` binds: its snake_case
    /// names up to the `=`, other than field labels, constructors and its type's names. A
    /// name alone binds whatever its case, as [`Parser::let_stmt`] reads it.
    fn placeholder_pattern(&mut self, start: usize) -> PatId {
        if let Some(name) = self.lone_let_name(start) {
            let kind = if self.m.text(name.sym) == "_" { PatKind::Wild } else { PatKind::Bind(name) };
            return self.m.pats.alloc(Pat { kind, span: name.span });
        }
        let mut names: Vec<Ident> = Vec::new();
        let mut depth = 0usize;
        let mut i = start;
        while let Some(token) = self.tokens.get(i) {
            match token.kind {
                T::LParen | T::LBracket | T::LBrace => depth += 1,
                T::RParen | T::RBracket | T::RBrace => depth = depth.saturating_sub(1),
                T::Eq | T::Newline | T::Eof => break,
                T::Colon if depth == 0 => break,
                T::Ident => {
                    let next = self.nth_from(i + 1);
                    let label = depth > 0 && next == T::Colon;
                    let after_dot = i > 0 && self.tokens[i - 1].kind == T::Dot;
                    let text = self.file.slice(token.span);
                    let snake = text.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') && text != "_";
                    if snake && !label && !after_dot && !matches!(next, T::Dot | T::LParen) {
                        let name = self.intern(token.span);
                        if !names.iter().any(|n| n.sym == name.sym) {
                            names.push(name);
                        }
                    }
                }
                _ => {}
            }
            i += 1;
        }
        let span = self.tokens.get(start).map_or(self.prev_span(), |t| t.span);
        let lone = names.len() == 1 && self.tokens.get(start).is_some_and(|t| t.span == names[0].span);
        let kind = if lone {
            PatKind::Bind(names[0])
        } else {
            let parts = names
                .into_iter()
                .map(|name| self.m.pats.alloc(Pat { kind: PatKind::Bind(name), span: name.span }))
                .collect();
            PatKind::Tuple(parts)
        };
        self.m.pats.alloc(Pat { kind, span })
    }

    /// The names the `is` tests of a broken `check` condition starting at token `start`
    /// bind, as [`Parser::placeholder_pattern`] reads a pattern's names, up to the `else` or
    /// the end of the line. An `is` under `not` binds nothing, and neither does any when the
    /// condition is an `or` (OPEN_QUESTIONS P5).
    fn placeholder_is_pattern(&mut self, start: usize) -> PatId {
        let mut names: Vec<Ident> = Vec::new();
        let mut depth = 0usize;
        let mut in_pattern = false;
        // The depth of a `not` whose operand is still being read.
        let mut negated: Option<usize> = None;
        // For each open bracket, how many names were bound before it, and whether an `or`
        // in it means its group binds none.
        let mut groups: Vec<(usize, bool)> = Vec::new();
        // Whether a `match` in the condition has yet to open its arms.
        let mut arms_next = false;
        let mut i = start;
        while let Some(token) = self.tokens.get(i) {
            match token.kind {
                // A `{` on the line of a `check` that lacks its `else` opens the block meant
                // for it, whose names the condition doesn't bind.
                T::LBrace if depth == 0 && !arms_next => break,
                T::Keyword(Kw::Match) => arms_next = true,
                T::LParen | T::LBracket | T::LBrace => {
                    arms_next &= token.kind != T::LBrace;
                    depth += 1;
                    groups.push((names.len(), false));
                }
                T::RParen | T::RBracket | T::RBrace => {
                    depth = depth.saturating_sub(1);
                    if let Some((before, true)) = groups.pop() {
                        names.truncate(before);
                    }
                    if negated.is_some_and(|d| depth < d) {
                        negated = None;
                    }
                }
                T::Eof => break,
                // A newline inside brackets, as in a multi-line `match`, doesn't end it.
                T::Newline if depth == 0 => break,
                T::Keyword(Kw::Else) if depth == 0 => break,
                T::Keyword(Kw::Or) if depth == 0 => {
                    names.clear();
                    break;
                }
                T::Keyword(Kw::Or) => {
                    in_pattern = false;
                    if let Some(group) = groups.last_mut() {
                        group.1 = true;
                    }
                }
                T::Keyword(Kw::Not) => negated = negated.or(Some(depth)),
                T::Keyword(Kw::Is) => in_pattern = negated.is_none() && !groups.iter().any(|g| g.1),
                T::Keyword(Kw::And) => {
                    in_pattern = false;
                    if negated.is_some_and(|d| depth <= d) {
                        negated = None;
                    }
                }
                T::Ident if in_pattern => {
                    let next = self.nth_from(i + 1);
                    let label = depth > 0 && next == T::Colon;
                    let after_dot = self.tokens[i - 1].kind == T::Dot;
                    let text = self.file.slice(token.span);
                    let snake = text.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') && text != "_";
                    if snake && !label && !after_dot && !matches!(next, T::Dot | T::LParen) {
                        let name = self.intern(token.span);
                        if !names.iter().any(|n| n.sym == name.sym) {
                            names.push(name);
                        }
                    }
                }
                _ => {}
            }
            i += 1;
        }
        let parts = names
            .into_iter()
            .map(|name| self.m.pats.alloc(Pat { kind: PatKind::Bind(name), span: name.span }))
            .collect();
        let span = self.tokens.get(start).map_or(self.prev_span(), |t| t.span);
        self.m.pats.alloc(Pat { kind: PatKind::Tuple(parts), span })
    }

    fn nth_from(&self, i: usize) -> T {
        self.tokens.get(i).map_or(T::Eof, |t| t.kind)
    }

    fn stmt(&mut self) -> PResult<StmtId> {
        let start = self.peek().span;
        let kind = match self.kind() {
            T::Keyword(Kw::Let | Kw::Var) => self.let_stmt()?,
            T::Keyword(Kw::Return) => {
                self.bump();
                let value = if matches!(self.kind(), T::Newline | T::Comma | T::RBrace | T::Eof) {
                    None
                } else {
                    Some(self.expr()?)
                };
                StmtKind::Return(value)
            }
            T::Keyword(Kw::Break) => {
                self.bump();
                StmtKind::Break(self.label_ref()?)
            }
            T::Keyword(Kw::Continue) => {
                self.bump();
                StmtKind::Continue(self.label_ref()?)
            }
            T::Keyword(Kw::Assert) => {
                self.bump();
                StmtKind::Assert(self.expr()?)
            }
            T::Keyword(Kw::Check) => {
                self.bump();
                let cond = self.nested(Self::logical)?;
                if !self.eat(T::Keyword(Kw::Else)) {
                    return self.unexpected("`else` and what to do when the check fails");
                }
                StmtKind::Check { cond, fallback: self.fallback()? }
            }
            T::Keyword(Kw::Expect) => return self.not_implemented("`expect` statements", Planned::Phase(2)),
            T::Ident
                if self.nth(1) == T::Colon && matches!(self.nth(2), T::Keyword(Kw::For | Kw::While | Kw::Loop)) =>
            {
                let label = self.ident("a label")?;
                self.bump();
                StmtKind::Expr(self.loop_expr(Some(label))?)
            }
            _ => {
                let target = self.expr()?;
                let op = match self.kind() {
                    T::Eq => Some(AssignOp::Set),
                    T::PlusEq => Some(AssignOp::Add),
                    T::MinusEq => Some(AssignOp::Sub),
                    T::StarEq => Some(AssignOp::Mul),
                    T::SlashEq => Some(AssignOp::Div),
                    _ => None,
                };
                match op {
                    Some(op) => {
                        self.bump();
                        let value = self.expr()?;
                        StmtKind::Assign { target, op, value }
                    }
                    None => StmtKind::Expr(target),
                }
            }
        };
        let span = start.to(self.prev_span());
        Ok(self.m.stmts.alloc(Stmt { kind, span }))
    }

    fn label_ref(&mut self) -> PResult<Option<Ident>> {
        if self.at(T::Ident) { Ok(Some(self.ident("a label")?)) } else { Ok(None) }
    }

    /// The name a `let` whose pattern starts at token `at` binds when the pattern is that name
    /// alone. It binds it whatever its case, so a misnamed variable is reported as misnamed
    /// rather than as an unknown constructor. A snake_case name before a `.`, as in the
    /// mistaken `let p.q = 5`, is one too, since no constructor is written that way.
    fn lone_let_name(&mut self, at: usize) -> Option<Ident> {
        let token = self.tokens.get(at).filter(|t| t.kind == T::Ident)?;
        let snake = self.file.slice(token.span).starts_with(|c: char| c.is_ascii_lowercase() || c == '_');
        match self.nth_from(at + 1) {
            T::Eq | T::Colon => {}
            T::Dot if snake => {}
            _ => return None,
        }
        Some(self.intern(token.span))
    }

    fn let_stmt(&mut self) -> PResult<StmtKind> {
        let mutable = self.bump().kind == T::Keyword(Kw::Var);
        let pat = match self.lone_let_name(self.pos) {
            Some(name) => {
                self.bump();
                let kind = if self.m.text(name.sym) == "_" { PatKind::Wild } else { PatKind::Bind(name) };
                self.m.pats.alloc(Pat { kind, span: name.span })
            }
            None => self.pattern()?,
        };
        let ty = if self.eat(T::Colon) { Some(self.type_expr()?) } else { None };
        self.expect(T::Eq, "`=`")?;
        let init = self.expr()?;
        Ok(StmtKind::Let { mutable, pat, ty, init })
    }

    // ---- expressions, from lowest precedence to highest (REFERENCE §6.1) ----

    fn expr(&mut self) -> PResult<ExprId> {
        self.nested(|p| {
            let value = p.logical()?;
            if !p.eat(T::Keyword(Kw::Else)) {
                return Ok(value);
            }
            let fallback = p.fallback()?;
            let span = p.span_of(value).to(p.prev_span());
            Ok(p.alloc(ExprKind::Else { value, fallback }, span))
        })
    }

    /// What follows the `else` of an `else` form or a `check`: a block, or an expression,
    /// which may itself be an `else` form.
    fn fallback(&mut self) -> PResult<Fallback> {
        if self.at(T::LBrace) { Ok(Fallback::Block(self.block()?)) } else { Ok(Fallback::Value(self.expr()?)) }
    }

    /// `(a, b)`, a tuple of at least two of what `element` parses, after its `(`. A trailing
    /// comma is allowed after the second element (OPEN_QUESTIONS P5).
    fn tuple<X>(&mut self, element: fn(&mut Self) -> PResult<X>, what: &str) -> PResult<Vec<X>> {
        let open = self.bump();
        if self.at(T::RParen) && what == "tuple type" {
            let span = open.span.to(self.peek().span);
            self.error(codes::UNEXPECTED_TOKEN, span, "the unit type is written `Unit`");
            return Err(());
        }
        let first = self.nested(element)?;
        self.tuple_rest(&open, first, element, what)
    }

    /// The rest of a tuple after its `(` and first element.
    fn tuple_rest<X>(
        &mut self,
        open: &Token,
        first: X,
        element: fn(&mut Self) -> PResult<X>,
        what: &str,
    ) -> PResult<Vec<X>> {
        let mut elements = vec![first];
        while self.eat(T::Comma) {
            if self.at(T::RParen) {
                break;
            }
            elements.push(self.nested(element)?);
        }
        let close = self.close(open, T::RParen, "`,` or `)`")?;
        if elements.len() < 2 {
            let span = open.span.to(close.span);
            let message = if what == "tuple" {
                "a tuple has at least two elements; without the comma, parentheses only group".to_string()
            } else {
                format!("a {what} has at least two elements, and parentheses do not group here")
            };
            self.error(codes::UNEXPECTED_TOKEN, span, message);
            return Err(());
        }
        Ok(elements)
    }

    /// A condition of `if` or `while`, which stops before `{`. An `else` form there must
    /// be parenthesized, since its own block would be ambiguous with the body.
    fn condition(&mut self) -> PResult<ExprId> {
        let cond = self.nested(Self::logical)?;
        if self.at_kw(Kw::Else) {
            let span = self.peek().span;
            self.error(
                codes::UNEXPECTED_TOKEN,
                span,
                "an `else` form in a condition must be parenthesized, as in `if (x else false) {`",
            );
            return Err(());
        }
        Ok(cond)
    }

    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId) -> ExprId {
        let span = self.span_of(lhs).to(self.span_of(rhs));
        self.alloc(ExprKind::Binary { op, lhs, rhs }, span)
    }

    fn logical(&mut self) -> PResult<ExprId> {
        let base = self.depth;
        let mut lhs = self.not_expr()?;
        let mut first: Option<BinOp> = None;
        let mut mixed = false;
        loop {
            let op = match self.kind() {
                T::Keyword(Kw::And) => BinOp::And,
                T::Keyword(Kw::Or) => BinOp::Or,
                _ => {
                    self.depth = base;
                    return Ok(lhs);
                }
            };
            let token = self.bump();
            match first {
                None => first = Some(op),
                Some(f) if f != op && !mixed => {
                    self.error(
                        codes::MIXED_AND_OR,
                        token.span,
                        "`and` and `or` cannot be mixed without parentheses (H2)",
                    );
                    mixed = true;
                }
                Some(_) => {}
            }
            self.deeper()?;
            let rhs = self.not_expr()?;
            lhs = self.binary(op, lhs, rhs);
        }
    }

    fn not_expr(&mut self) -> PResult<ExprId> {
        if self.at_kw(Kw::Not) {
            let token = self.bump();
            let operand = self.nested(Self::not_expr)?;
            let span = token.span.to(self.span_of(operand));
            return Ok(self.alloc(ExprKind::Unary { op: UnaryOp::Not, operand }, span));
        }
        self.comparison()
    }

    /// The comparison at the current token: an operator, or `None` for `is`.
    fn comparison_op(&mut self) -> PResult<Option<Option<BinOp>>> {
        Ok(Some(Some(match self.kind() {
            T::EqEq => BinOp::Eq,
            T::NotEq => BinOp::Ne,
            T::Lt => BinOp::Lt,
            T::Le => BinOp::Le,
            T::Gt => BinOp::Gt,
            T::Ge => BinOp::Ge,
            T::Keyword(Kw::Is) => return Ok(Some(None)),
            T::Keyword(Kw::In) => return self.not_implemented("`in` tests", Planned::Phase(2)),
            _ => return Ok(None),
        })))
    }

    fn comparison(&mut self) -> PResult<ExprId> {
        let lhs = self.range()?;
        let Some(op) = self.comparison_op()? else { return Ok(lhs) };
        self.bump();
        let e = match op {
            Some(op) => {
                let rhs = self.range()?;
                self.binary(op, lhs, rhs)
            }
            None => {
                let pat = self.pattern()?;
                let span = self.span_of(lhs).to(self.prev_span());
                self.alloc(ExprKind::Is { value: lhs, pat }, span)
            }
        };
        if self.comparison_op()?.is_some() {
            let span = self.peek().span;
            self.error(codes::CHAINED_COMPARISON, span, "comparisons cannot be chained; write `a < b and b < c`");
            while let Some(op) = self.comparison_op()? {
                self.bump();
                match op {
                    Some(_) => self.range().map(|_| ())?,
                    None => self.pattern().map(|_| ())?,
                }
            }
        }
        Ok(e)
    }

    fn range(&mut self) -> PResult<ExprId> {
        let lo = self.additive()?;
        let inclusive = match self.kind() {
            T::DotDot => false,
            T::DotDotEq => true,
            _ => return Ok(lo),
        };
        self.bump();
        let hi = self.additive()?;
        let span = self.span_of(lo).to(self.span_of(hi));
        Ok(self.alloc(ExprKind::Range { lo, hi, inclusive }, span))
    }

    fn additive(&mut self) -> PResult<ExprId> {
        let base = self.depth;
        let mut lhs = self.multiplicative()?;
        loop {
            let op = match self.kind() {
                T::Plus => BinOp::Add,
                T::Minus => BinOp::Sub,
                _ => {
                    self.depth = base;
                    return Ok(lhs);
                }
            };
            self.bump();
            self.deeper()?;
            let rhs = self.multiplicative()?;
            lhs = self.binary(op, lhs, rhs);
        }
    }

    fn multiplicative(&mut self) -> PResult<ExprId> {
        let base = self.depth;
        let mut lhs = self.prefix()?;
        loop {
            let op = match self.kind() {
                T::Star => BinOp::Mul,
                T::Slash => BinOp::Div,
                T::Percent => BinOp::Rem,
                _ => {
                    self.depth = base;
                    return Ok(lhs);
                }
            };
            self.bump();
            self.deeper()?;
            let rhs = self.prefix()?;
            lhs = self.binary(op, lhs, rhs);
        }
    }

    fn prefix(&mut self) -> PResult<ExprId> {
        match self.kind() {
            T::Minus => {
                let token = self.bump();
                let operand = self.nested(Self::prefix)?;
                let span = token.span.to(self.span_of(operand));
                Ok(self.alloc(ExprKind::Unary { op: UnaryOp::Neg, operand }, span))
            }
            T::Keyword(Kw::Try) => {
                // `try` covers the whole postfix chain to its right.
                let token = self.bump();
                let inner = self.nested(Self::postfix)?;
                let span = token.span.to(self.span_of(inner));
                Ok(self.alloc(ExprKind::Try(inner), span))
            }
            T::Keyword(Kw::Attempt) => {
                // `attempt` covers the whole postfix chain to its right, as `try` does.
                let token = self.bump();
                let inner = self.nested(Self::postfix)?;
                let span = token.span.to(self.span_of(inner));
                Ok(self.alloc(ExprKind::Attempt(inner), span))
            }
            _ => self.postfix(),
        }
    }

    fn postfix(&mut self) -> PResult<ExprId> {
        let base = self.depth;
        let mut e = self.primary()?;
        loop {
            if matches!(self.kind(), T::LParen | T::Dot | T::LBracket) {
                self.deeper()?;
            }
            match self.kind() {
                T::LParen => {
                    let args = self.args()?;
                    let span = self.span_of(e).to(self.prev_span());
                    e = self.alloc(ExprKind::Call { callee: e, targs: None, args }, span);
                }
                T::ColonColon => {
                    self.deeper()?;
                    let targs = Some(self.explicit_type_args()?);
                    let args = self.args()?;
                    let span = self.span_of(e).to(self.prev_span());
                    e = self.alloc(ExprKind::Call { callee: e, targs, args }, span);
                }
                T::Dot => {
                    self.bump();
                    let name = self.member_name("a field or method name")?;
                    let targs = if self.at(T::ColonColon) { Some(self.explicit_type_args()?) } else { None };
                    if self.at(T::LParen) || targs.is_some() {
                        let args = self.args()?;
                        let span = self.span_of(e).to(self.prev_span());
                        e = self.alloc(ExprKind::MethodCall { receiver: e, method: name, targs, args }, span);
                    } else {
                        let span = self.span_of(e).to(name.span);
                        e = self.alloc(ExprKind::Field { base: e, name }, span);
                    }
                }
                T::LBracket if matches!(self.m.exprs[e].kind, ExprKind::Int(_) | ExprKind::Float(_)) => {
                    return self.not_implemented("units of measure", Planned::PastV1);
                }
                T::LBracket => {
                    let open = self.bump();
                    let index = self.expr()?;
                    self.close(&open, T::RBracket, "`]`")?;
                    let span = self.span_of(e).to(self.prev_span());
                    e = self.alloc(ExprKind::Index { base: e, index }, span);
                }
                _ => {
                    self.depth = base;
                    return Ok(e);
                }
            }
        }
    }

    /// `::[Int, Text]` before a call's arguments (REFERENCE §4.8). Without a call, as in
    /// `let f = max::[Int]`, it names a function as a value, which comes later.
    fn explicit_type_args(&mut self) -> PResult<Vec<TypeId>> {
        let start = self.peek().span;
        self.bump();
        if !self.at(T::LBracket) {
            return self.unexpected("`[` and type arguments after `::`");
        }
        let targs = self.type_args()?;
        if !self.at(T::LParen) {
            let span = start.to(self.prev_span());
            self.diags.not_implemented(span, "functions used as values", Planned::Phase(2));
            return Err(());
        }
        Ok(targs)
    }

    fn args(&mut self) -> PResult<Vec<Arg>> {
        let open = self.expect(T::LParen, "`(`")?;
        let mut args = Vec::new();
        while !self.at(T::RParen) {
            let label = if self.at(T::Ident) && self.nth(1) == T::Colon {
                let label = self.ident("a label")?;
                self.bump();
                Some(label)
            } else {
                None
            };
            let inout = self.eat(T::Amp);
            let value = self.expr()?;
            args.push(Arg { label, inout, value });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.close(&open, T::RParen, "`,` or `)`")?;
        Ok(args)
    }

    fn primary(&mut self) -> PResult<ExprId> {
        let start = self.peek().span;
        let kind = match self.kind() {
            T::Int | T::Float | T::Text | T::Char => match self.bump().value {
                TokenValue::Int(v) => ExprKind::Int(v),
                TokenValue::Float(text) => ExprKind::Float(text),
                TokenValue::Text(text) => ExprKind::Text(text),
                TokenValue::Char(c) => ExprKind::Char(c),
                _ => unreachable!("literal tokens carry values"),
            },
            T::FText => {
                let TokenValue::FText(parts) = self.bump().value else { unreachable!("f-strings carry parts") };
                return self.interpolated_text(parts, start);
            }
            T::Keyword(Kw::True) => {
                self.bump();
                ExprKind::Bool(true)
            }
            T::Keyword(Kw::False) => {
                self.bump();
                ExprKind::Bool(false)
            }
            T::Ident => ExprKind::Name(self.ident("a name")?),
            T::LParen => {
                let open = self.bump();
                if self.eat(T::RParen) {
                    ExprKind::Unit
                } else {
                    let inner = self.expr()?;
                    if self.at(T::Comma) {
                        let elements = self.tuple_rest(&open, inner, Self::expr, "tuple")?;
                        let span = start.to(self.prev_span());
                        return Ok(self.alloc(ExprKind::Tuple(elements), span));
                    }
                    let close = self.close(&open, T::RParen, "`)`")?;
                    // The parentheses belong to the expression, so its text quoted in a
                    // message, such as a refinement's, keeps them balanced.
                    self.m.exprs[inner].span = open.span.to(close.span);
                    return Ok(inner);
                }
            }
            T::Keyword(Kw::If) => return self.if_expr(),
            T::Keyword(Kw::While | Kw::Loop | Kw::For) => return self.loop_expr(None),
            T::Keyword(Kw::Todo) => {
                self.bump();
                let mut message = None;
                if self.eat(T::LParen) {
                    if let TokenValue::Text(text) = self.expect(T::Text, "a text literal")?.value {
                        message = Some(text);
                    }
                    self.expect(T::RParen, "`)`")?;
                }
                ExprKind::Todo(message)
            }
            T::Keyword(Kw::Unreachable) => {
                self.bump();
                ExprKind::Unreachable
            }
            T::Keyword(Kw::Debug) => {
                self.bump();
                let open = self.expect(T::LParen, "`(`")?;
                let mut values = Vec::new();
                while !self.at(T::RParen) {
                    values.push(self.expr()?);
                    if !self.eat(T::Comma) {
                        break;
                    }
                }
                self.close(&open, T::RParen, "`,` or `)`")?;
                ExprKind::Debug(values)
            }
            T::LBracket => return self.collection(),
            T::Pipe => return self.not_implemented("closures", Planned::Phase(2)),
            T::Keyword(Kw::Match) => return self.match_expr(),
            T::Keyword(Kw::Scope) => return self.not_implemented("`scope` blocks", Planned::Phase(6)),
            // As the operand of `try` or `attempt`, which covers only its own chain.
            T::Keyword(Kw::Try | Kw::Attempt) => return self.prefix(),
            T::Keyword(Kw::Fail) => {
                // `fail e` takes everything to its right (REFERENCE §6.1).
                self.bump();
                let value = self.expr()?;
                ExprKind::Fail(value)
            }
            T::Keyword(Kw::It) => {
                self.bump();
                ExprKind::It
            }
            T::Keyword(Kw::SelfValue) => {
                let token = self.bump();
                ExprKind::Name(self.intern(token.span))
            }
            T::Keyword(Kw::SelfType) => {
                return self.not_implemented("uses of `Self` in expressions", Planned::Unscheduled);
            }
            T::Keyword(Kw::All | Kw::Any) => return self.not_implemented("quantifiers", Planned::Phase(5)),
            _ => return self.unexpected("an expression"),
        };
        let span = start.to(self.prev_span());
        Ok(self.alloc(kind, span))
    }

    /// `[a, b]`, `["k": v]`, `[]` or `[:]` (REFERENCE §2). The first element says which: a
    /// map's has a `:` after its key. A trailing comma may follow the last element or entry.
    fn collection(&mut self) -> PResult<ExprId> {
        let open = self.bump();
        let kind = if self.at(T::Colon) && self.nth(1) == T::RBracket {
            self.bump();
            self.bump();
            ExprKind::Map(Vec::new())
        } else if self.eat(T::RBracket) {
            ExprKind::List(Vec::new())
        } else {
            let first = self.expr()?;
            if self.eat(T::Colon) {
                let mut entries = vec![(first, self.expr()?)];
                while self.eat(T::Comma) && !self.at(T::RBracket) {
                    self.still_open(&open)?;
                    let key = self.expr()?;
                    self.expect(T::Colon, "`:` and the value for this key")?;
                    entries.push((key, self.expr()?));
                }
                self.close(&open, T::RBracket, "`,` or `]`")?;
                ExprKind::Map(entries)
            } else {
                let mut elements = vec![first];
                while self.eat(T::Comma) && !self.at(T::RBracket) {
                    self.still_open(&open)?;
                    elements.push(self.expr()?);
                }
                self.close(&open, T::RBracket, "`,` or `]`")?;
                ExprKind::List(elements)
            }
        };
        let span = open.span.to(self.prev_span());
        Ok(self.alloc(kind, span))
    }

    /// Reports `open` as never closed when what follows a comma can only start a statement
    /// or an item, or close a block, on a line no deeper than the line that opened it, so a
    /// trailing comma before a missing `]` doesn't make the next statement an element. An
    /// element may start any line, since the bracket continues the statement (REFERENCE §2).
    fn still_open(&mut self, open: &Token) -> PResult<()> {
        let next = self.peek().span;
        let statement = matches!(
            self.kind(),
            T::RBrace
                | T::Keyword(
                    Kw::Let
                        | Kw::Var
                        | Kw::Return
                        | Kw::Break
                        | Kw::Continue
                        | Kw::Check
                        | Kw::Assert
                        | Kw::For
                        | Kw::While
                        | Kw::Loop
                )
        ) || self.starts_item();
        if self.at(T::Eof) || (statement && self.starts_line(next) && self.indent(next) <= self.indent(open.span)) {
            return self.unclosed(open);
        }
        Ok(())
    }

    /// Parses each interpolation of an f-string from its own source span.
    fn interpolated_text(&mut self, parts: Vec<FPart>, start: Span) -> PResult<ExprId> {
        let span = start.to(self.prev_span());
        let file = self.file;
        let mut out = Vec::new();
        for part in parts {
            match part {
                FPart::Lit(text) => out.push(FTextPart::Lit(text)),
                FPart::Expr(inner) => {
                    let tokens = tokenize(file.slice(inner), inner.lo, self.diags);
                    let saved_tokens = std::mem::replace(&mut self.tokens, tokens);
                    let saved_pos = std::mem::replace(&mut self.pos, 0);
                    let result = self.interpolation();
                    self.tokens = saved_tokens;
                    self.pos = saved_pos;
                    out.push(FTextPart::Expr(result?));
                }
            }
        }
        Ok(self.alloc(ExprKind::FText(out), span))
    }

    fn interpolation(&mut self) -> PResult<ExprId> {
        self.skip_newlines();
        let e = self.expr()?;
        self.skip_newlines();
        if self.at(T::Eof) { Ok(e) } else { self.unexpected("`}` to end the interpolation") }
    }

    fn match_expr(&mut self) -> PResult<ExprId> {
        let start = self.bump().span;
        let scrutinee = self.condition()?;
        let open = self.expect(T::LBrace, "`{` and the arms of the `match`")?;
        let indent = self.stmt_indent;
        self.arm_depth += 1;
        let arms = self.nested(|p| Ok(p.arms(&open, indent)));
        self.arm_depth -= 1;
        let (arms, complete) = arms?;
        let span = start.to(self.prev_span());
        Ok(self.alloc(ExprKind::Match { scrutinee, arms, complete }, span))
    }

    /// Parses arms up to the `}` that closes `open`, one per line or separated by commas. A
    /// `match` that is never closed ends as a block does (see [`Parser::block_rest`]). Also
    /// returns whether every arm parsed and the braces closed.
    fn arms(&mut self, open: &Token, indent: usize) -> (Vec<Arm>, bool) {
        let mut arms = Vec::new();
        let mut complete = true;
        loop {
            while matches!(self.kind(), T::Newline | T::DocComment) {
                self.bump();
            }
            let next = self.peek().span;
            let unclosed = match self.kind() {
                T::RBrace if self.indent(next) >= indent || !self.starts_line(next) => {
                    self.bump();
                    break;
                }
                T::RBrace | T::Eof => true,
                _ if self.field_indent.is_some_and(|field| self.starts_line(next) && self.indent(next) <= field) => {
                    true
                }
                _ => self.starts_item(),
            };
            if unclosed {
                self.recovered = true;
                if !self.unclosed_reported {
                    self.unclosed_reported = true;
                    let _ = self.unclosed::<()>(open);
                }
                return (arms, false);
            }
            let start = self.pos;
            let saved = (self.depth, self.stmt_indent);
            self.stmt_indent = self.indent(next);
            match self.arm() {
                Ok(arm) => {
                    // A body that was never closed may have swallowed arms, and ends before
                    // the next one.
                    let unclosed = arm.body.unclosed;
                    complete &= !unclosed;
                    arms.push(arm);
                    if !unclosed
                        && !self.eat(T::Comma)
                        && !matches!(self.kind(), T::Newline | T::RBrace | T::Eof)
                        && !self.starts_item()
                    {
                        let _ = self.unexpected::<()>("the end of the arm");
                        self.recover(start, Stop::Stmt);
                        complete = false;
                    }
                }
                Err(()) => {
                    self.recover(start, Stop::Stmt);
                    if self.pos == start {
                        self.bump();
                    }
                    complete = false;
                }
            }
            (self.depth, self.stmt_indent) = saved;
        }
        (arms, complete)
    }

    /// `pattern if guard => body`, where the body is a block or one statement.
    fn arm(&mut self) -> PResult<Arm> {
        let pat = self.pattern()?;
        // A guard ends at `=>`, so it may be an `else` form unparenthesized (§6.1).
        let guard = if self.eat(T::Keyword(Kw::If)) { Some(self.expr()?) } else { None };
        self.expect(T::FatArrow, "`=>` and the arm's body")?;
        let body = if self.at(T::LBrace) {
            self.block()?
        } else {
            if matches!(self.kind(), T::Keyword(Kw::Let | Kw::Var)) {
                return self.unexpected("an expression or `{` after `=>`");
            }
            let start = self.peek().span;
            let before = self.unclosed_blocks;
            let stmt = self.stmt()?;
            let unclosed = self.unclosed_blocks != before;
            Block { stmts: vec![stmt], span: start.to(self.prev_span()), unclosed, lost: false }
        };
        Ok(Arm { pat, guard, body })
    }

    // ---- patterns (REFERENCE §6.4) ----

    fn pattern(&mut self) -> PResult<PatId> {
        self.nested(Self::pattern_kind)
    }

    fn pattern_kind(&mut self) -> PResult<PatId> {
        let start = self.peek().span;
        let kind = match self.kind() {
            T::Ident => {
                let name = self.ident("a pattern")?;
                let text = self.m.text(name.sym);
                let upper = text.starts_with(|c: char| c.is_ascii_uppercase());
                if text == "_" {
                    PatKind::Wild
                } else if upper || matches!(self.kind(), T::Dot | T::LParen) {
                    self.ctor_pattern(name)?
                } else {
                    PatKind::Bind(name)
                }
            }
            T::Int | T::Float | T::Char | T::Text | T::Minus | T::Keyword(Kw::True | Kw::False) => {
                let lo = self.literal_pattern()?;
                let inclusive = match self.kind() {
                    T::DotDot => false,
                    T::DotDotEq => true,
                    _ => {
                        let span = start.to(self.prev_span());
                        return Ok(self.m.pats.alloc(Pat { kind: PatKind::Lit(lo), span }));
                    }
                };
                self.bump();
                let hi = self.literal_pattern()?;
                PatKind::Range { lo, hi, inclusive }
            }
            T::LParen if self.nth(1) == T::RParen => {
                self.bump();
                self.bump();
                let span = start.to(self.prev_span());
                PatKind::Lit(self.alloc(ExprKind::Unit, span))
            }
            T::LParen => PatKind::Tuple(self.tuple(Self::pattern_kind, "tuple pattern")?),
            T::Keyword(Kw::SelfType) => {
                return self.not_implemented("uses of `Self` in patterns", Planned::Unscheduled);
            }
            _ => return self.unexpected("a pattern"),
        };
        let span = start.to(self.prev_span());
        Ok(self.m.pats.alloc(Pat { kind, span }))
    }

    /// `Empty`, `Shape.Circle(r)` or `Rect(w: width, ..)`, after its first name.
    fn ctor_pattern(&mut self, first: Ident) -> PResult<PatKind> {
        let (qualifier, name) =
            if self.eat(T::Dot) { (Some(first), self.member_name("a variant name")?) } else { (None, first) };
        let mut rest = false;
        let fields = if self.at(T::LParen) {
            let open = self.bump();
            let mut fields = Vec::new();
            while !self.at(T::RParen) {
                if self.eat(T::DotDot) {
                    rest = true;
                    break;
                }
                let label = if self.at(T::Ident) && self.nth(1) == T::Colon {
                    let label = self.ident("a field name")?;
                    self.bump();
                    Some(label)
                } else {
                    None
                };
                let pat = self.pattern()?;
                fields.push(FieldPat { label, pat });
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.close(&open, T::RParen, "`,` or `)`")?;
            Some(fields)
        } else {
            None
        };
        Ok(PatKind::Ctor { qualifier, name, fields, rest })
    }

    /// A literal in a pattern, possibly a negated number.
    fn literal_pattern(&mut self) -> PResult<ExprId> {
        if self.at(T::Minus) {
            let minus = self.bump();
            if !matches!(self.kind(), T::Int | T::Float) {
                return self.unexpected("a number after `-`");
            }
            let operand = self.number_pattern()?;
            let span = minus.span.to(self.prev_span());
            return Ok(self.alloc(ExprKind::Unary { op: UnaryOp::Neg, operand }, span));
        }
        match self.kind() {
            T::Int | T::Float => self.number_pattern(),
            T::Char | T::Text | T::Keyword(Kw::True | Kw::False) => self.primary(),
            _ => self.unexpected("a literal"),
        }
    }

    /// A number in a pattern, which may not carry a unit yet.
    fn number_pattern(&mut self) -> PResult<ExprId> {
        let number = self.primary()?;
        if self.at(T::LBracket) {
            return self.not_implemented("units of measure", Planned::PastV1);
        }
        Ok(number)
    }

    fn if_expr(&mut self) -> PResult<ExprId> {
        let start = self.bump().span;
        let cond = self.condition()?;
        let then_block = self.block()?;
        let else_branch = if self.eat(T::Keyword(Kw::Else)) {
            if self.at_kw(Kw::If) {
                Some(ElseBranch::If(self.nested(Self::if_expr)?))
            } else {
                Some(ElseBranch::Block(self.block()?))
            }
        } else {
            None
        };
        let span = start.to(self.prev_span());
        Ok(self.alloc(ExprKind::If { cond, then_block, else_branch }, span))
    }

    fn loop_expr(&mut self, label: Option<Ident>) -> PResult<ExprId> {
        let start = label.map_or(self.peek().span, |l| l.span);
        let kind = match self.kind() {
            T::Keyword(Kw::While) => {
                self.bump();
                let cond = self.condition()?;
                self.no_invariant()?;
                let body = self.block()?;
                ExprKind::While { label, cond, body }
            }
            T::Keyword(Kw::Loop) => {
                self.bump();
                let body = self.block()?;
                ExprKind::Loop { label, body }
            }
            T::Keyword(Kw::For) => {
                self.bump();
                // A pattern that is one name binds it whatever its case, as in a `let`
                // (OPEN_QUESTIONS P5).
                let pat = if self.at(T::Ident) && self.nth(1) == T::Keyword(Kw::In) {
                    let name = self.ident("a loop variable")?;
                    let kind = if self.m.text(name.sym) == "_" { PatKind::Wild } else { PatKind::Bind(name) };
                    self.m.pats.alloc(Pat { kind, span: name.span })
                } else {
                    self.pattern()?
                };
                self.expect(T::Keyword(Kw::In), "`in`")?;
                let consume = self.eat(T::Keyword(Kw::Take));
                let iter = self.nested(Self::logical)?;
                self.no_invariant()?;
                let body = self.block()?;
                ExprKind::For { label, pat, iter, consume, body }
            }
            _ => return self.unexpected("`for`, `while` or `loop`"),
        };
        let span = start.to(self.prev_span());
        Ok(self.alloc(kind, span))
    }

    fn no_invariant(&mut self) -> PResult<()> {
        if self.at_kw(Kw::Invariant) {
            return self.not_implemented("loop invariants", Planned::Phase(5));
        }
        Ok(())
    }
}

/// A keyword that begins an item. `let` also begins a statement, so it never ends one.
fn item_keyword(kw: Kw) -> bool {
    matches!(kw, Kw::Fn | Kw::Use | Kw::Record | Kw::Enum | Kw::Impl | Kw::Interface | Kw::Example)
        || (kw != Kw::Let && planned_item(kw).is_some())
}

/// Item keywords that belong to later phases, with what to call them.
fn planned_item(kw: Kw) -> Option<(&'static str, Planned)> {
    Some(match kw {
        Kw::Type => ("`type` declarations", Planned::Phase(2)),
        Kw::Distinct => ("distinct types", Planned::Phase(2)),
        // `unique record` is implemented, so only a `unique` that starts no record gets here, and
        // the parser reports it before asking.
        Kw::Unique => ("`unique` declarations", Planned::Phase(2)),
        Kw::Opaque => ("`opaque` records", Planned::Phase(2)),
        Kw::Resource => ("`resource` records", Planned::Phase(2)),
        Kw::Test => ("`test` blocks", Planned::Phase(2)),
        Kw::Cap => ("capability declarations", Planned::Phase(3)),
        Kw::Effect => ("effect parameters", Planned::Phase(3)),
        Kw::Pred => ("`pred` functions", Planned::Phase(5)),
        Kw::Unit | Kw::Tag => ("units and tags", Planned::PastV1),
        Kw::Extern => ("`extern` functions", Planned::Unscheduled),
        Kw::Property => ("`property` tests", Planned::Unscheduled),
        Kw::Let => ("top-level constants", Planned::Unscheduled),
        _ => return None,
    })
}

/// The types whose brackets hold something other than types: a unit, as in `Float[m]`
/// (REFERENCE §4.7), or the length of an `Array[T, N]` (§4.2).
fn takes_non_type_args(name: &str) -> bool {
    matches!(
        name,
        "Array"
            | "Int"
            | "Int8"
            | "Int16"
            | "Int32"
            | "Int64"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "Byte"
            | "Float"
            | "Float32"
    )
}
