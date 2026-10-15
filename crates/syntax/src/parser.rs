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

pub fn parse_module(file: &SourceFile, name: &str, diags: &mut Diagnostics) -> Module {
    let tokens = tokenize(&file.text, 0, diags);
    let module = Module {
        name: name.to_string(),
        items: Vec::new(),
        exprs: Arena::new(),
        stmts: Arena::new(),
        types: Arena::new(),
        interner: Interner::default(),
        poisoned: HashSet::new(),
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

    /// Whether the current token is a `fn` or `pub` that starts an item, not one nested in
    /// a later-phase item such as an `impl` block.
    fn starts_item(&self) -> bool {
        let span = self.peek().span;
        self.starts_line(span) && self.indent(span) <= self.item_indent
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
    /// both end before a `fn` or `pub` that starts a line no deeper than the current item,
    /// since that starts the next item.
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
                T::Keyword(Kw::Fn | Kw::Pub) if self.pos > start && self.starts_item() => return,
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
            self.unclosed_reported = false;
            self.stmt_indent = self.indent(self.peek().span);
            self.item_indent = self.stmt_indent;
            match self.item() {
                Ok(Some(item)) => {
                    self.m.items.push(item);
                    // A doc comment may follow an item on its line; it documents the next one.
                    if !matches!(self.kind(), T::Newline | T::Eof | T::DocComment) {
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
        let mut vis = Visibility::Private;
        if self.eat(T::Keyword(Kw::Pub)) {
            vis = Visibility::Pub;
            if self.eat(T::LParen) {
                let scope = self.ident("`pkg`")?;
                if self.m.text(scope.sym) != "pkg" {
                    self.error(codes::UNEXPECTED_TOKEN, scope.span, "the only restricted visibility is `pub(pkg)`");
                }
                self.expect(T::RParen, "`)`")?;
                vis = Visibility::PubPkg;
            }
        }
        let kind = match self.kind() {
            T::Keyword(Kw::Fn) => ItemKind::Fn(self.fn_decl()?),
            T::Keyword(Kw::Use) if vis != Visibility::Private => {
                return self.not_implemented("re-exports (`pub use`)", Planned::Unscheduled);
            }
            T::Keyword(Kw::Use) => ItemKind::Use(self.use_decl()?),
            T::Keyword(kw) => match planned_item(kw) {
                Some((what, planned)) => return self.not_implemented(what, planned),
                None => return self.unexpected("an item such as `fn` or `use`"),
            },
            _ => return self.unexpected("an item such as `fn` or `use`"),
        };
        Ok(Some(Item { kind, vis, doc, span: start.to(self.prev_span()) }))
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

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        self.bump();
        let name = self.ident("a function name")?;
        let decl = self.fn_rest(name);
        if decl.is_err() {
            self.m.poisoned.insert(name.sym);
        }
        decl
    }

    fn fn_rest(&mut self, name: Ident) -> PResult<FnDecl> {
        if self.at(T::LBracket) {
            return self.not_implemented("generic functions", Planned::Phase(2));
        }
        let open = self.expect(T::LParen, "`(`")?;
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
        self.recovered = false;
        let body = self.block()?;
        Ok(FnDecl { name, params, ret, fails, body, recovered: self.recovered })
    }

    fn param(&mut self) -> PResult<Param> {
        if self.at_kw(Kw::SelfValue) {
            return self.not_implemented("methods (`self` parameters)", Planned::Phase(2));
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
                    self.skip_group()?;
                    TypeExprKind::Applied(name)
                } else {
                    TypeExprKind::Named(name)
                }
            }
            T::Keyword(Kw::Fn) => return self.not_implemented("function types", Planned::Phase(2)),
            T::Keyword(Kw::Scoped) => return self.not_implemented("`scoped` function types", Planned::Phase(3)),
            T::Keyword(Kw::Any) => return self.not_implemented("`any` types", Planned::PastV1),
            T::Keyword(Kw::SelfType) => return self.not_implemented("methods and `Self`", Planned::Phase(2)),
            T::LParen => return self.not_implemented("tuple types", Planned::Phase(2)),
            _ => return self.unexpected("a type"),
        };
        let span = start.to(self.prev_span());
        Ok(self.m.types.alloc(TypeExpr { kind, span }))
    }

    // ---- statements ----

    fn block(&mut self) -> PResult<Block> {
        let open = self.expect(T::LBrace, "`{`")?;
        let indent = self.stmt_indent;
        self.nested(|p| Ok(p.block_rest(&open, indent)))
    }

    /// Parses statements up to the `}` that closes `open`. A block that is never closed is
    /// reported where it opens, and ends where its enclosing block or item does: before a
    /// `}` indented less than the statement that opened it, before an item, or at the end of
    /// the file.
    fn block_rest(&mut self, open: &Token, indent: usize) -> Block {
        let mut stmts = Vec::new();
        loop {
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
                T::Keyword(Kw::Fn | Kw::Pub) => self.starts_item(),
                _ => false,
            };
            if unclosed {
                self.recovered = true;
                if !self.unclosed_reported {
                    self.unclosed_reported = true;
                    let _ = self.unclosed::<()>(open);
                }
                break;
            }
            let start = self.pos;
            let saved = (self.depth, self.stmt_indent);
            self.stmt_indent = self.indent(next);
            let stmt = match self.stmt() {
                Ok(stmt) => {
                    if !matches!(self.kind(), T::Newline | T::RBrace | T::Eof) {
                        let _ = self.unexpected::<()>("end of statement");
                        self.recover(start, Stop::Stmt);
                    }
                    stmt
                }
                Err(()) => {
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
        Block { stmts, span: open.span.to(self.prev_span()) }
    }

    /// Stands in for a statement that failed to parse. A `let` still binds its name, with
    /// an unknown type, so later uses of it aren't reported again.
    fn placeholder(&mut self, start: usize) -> StmtId {
        let span = self.tokens[start].span.to(self.prev_span());
        let init = self.alloc(ExprKind::Error, span);
        let kind = match (self.tokens[start].kind, self.tokens.get(start + 1)) {
            (T::Keyword(kw @ (Kw::Let | Kw::Var)), Some(next)) if next.kind == T::Ident => {
                let name = self.intern(next.span);
                StmtKind::Let { mutable: kw == Kw::Var, name, ty: None, init }
            }
            _ => StmtKind::Expr(init),
        };
        self.m.stmts.alloc(Stmt { kind, span })
    }

    fn stmt(&mut self) -> PResult<StmtId> {
        let start = self.peek().span;
        let kind = match self.kind() {
            T::Keyword(Kw::Let | Kw::Var) => self.let_stmt()?,
            T::Keyword(Kw::Return) => {
                self.bump();
                let value =
                    if matches!(self.kind(), T::Newline | T::RBrace | T::Eof) { None } else { Some(self.expr()?) };
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
            T::Keyword(Kw::Fail) => return self.not_implemented("`fail` statements", Planned::Phase(2)),
            T::Keyword(Kw::Check) => return self.not_implemented("`check` statements", Planned::Phase(2)),
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

    fn let_stmt(&mut self) -> PResult<StmtKind> {
        let mutable = self.bump().kind == T::Keyword(Kw::Var);
        if self.at(T::LParen) {
            return self.not_implemented("destructuring `let` statements", Planned::Phase(2));
        }
        let name = self.ident("a variable name")?;
        let ty = if self.eat(T::Colon) { Some(self.type_expr()?) } else { None };
        self.expect(T::Eq, "`=`")?;
        let init = self.expr()?;
        Ok(StmtKind::Let { mutable, name, ty, init })
    }

    // ---- expressions, from lowest precedence to highest (REFERENCE §6.1) ----

    fn expr(&mut self) -> PResult<ExprId> {
        self.nested(|p| {
            let e = p.logical()?;
            if p.at_kw(Kw::Else) {
                return p.not_implemented("`else` unwrapping forms", Planned::Phase(2));
            }
            Ok(e)
        })
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

    fn comparison_op(&mut self) -> PResult<Option<BinOp>> {
        Ok(Some(match self.kind() {
            T::EqEq => BinOp::Eq,
            T::NotEq => BinOp::Ne,
            T::Lt => BinOp::Lt,
            T::Le => BinOp::Le,
            T::Gt => BinOp::Gt,
            T::Ge => BinOp::Ge,
            T::Keyword(Kw::In) => return self.not_implemented("`in` tests", Planned::Phase(2)),
            T::Keyword(Kw::Is) => return self.not_implemented("`is` tests", Planned::Phase(2)),
            _ => return Ok(None),
        }))
    }

    fn comparison(&mut self) -> PResult<ExprId> {
        let lhs = self.range()?;
        let Some(op) = self.comparison_op()? else { return Ok(lhs) };
        self.bump();
        let rhs = self.range()?;
        let e = self.binary(op, lhs, rhs);
        if self.comparison_op()?.is_some() {
            let span = self.peek().span;
            self.error(codes::CHAINED_COMPARISON, span, "comparisons cannot be chained; write `a < b and b < c`");
            while self.comparison_op()?.is_some() {
                self.bump();
                self.range()?;
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
            T::Keyword(Kw::Attempt) => self.not_implemented("`attempt` expressions", Planned::Phase(2)),
            _ => self.postfix(),
        }
    }

    fn postfix(&mut self) -> PResult<ExprId> {
        let base = self.depth;
        let mut e = self.primary()?;
        loop {
            if matches!(self.kind(), T::LParen | T::Dot) {
                self.deeper()?;
            }
            match self.kind() {
                T::LParen => {
                    let args = self.args()?;
                    let span = self.span_of(e).to(self.prev_span());
                    e = self.alloc(ExprKind::Call { callee: e, args }, span);
                }
                T::Dot => {
                    self.bump();
                    let name = self.member_name("a field or method name")?;
                    if self.at(T::ColonColon) {
                        return self.not_implemented("explicit type arguments (`::[…]`)", Planned::Phase(2));
                    }
                    if self.at(T::LParen) {
                        let args = self.args()?;
                        let span = self.span_of(e).to(self.prev_span());
                        e = self.alloc(ExprKind::MethodCall { receiver: e, method: name, args }, span);
                    } else {
                        let span = self.span_of(e).to(name.span);
                        e = self.alloc(ExprKind::Field { base: e, name }, span);
                    }
                }
                T::LBracket if matches!(self.m.exprs[e].kind, ExprKind::Int(_) | ExprKind::Float(_)) => {
                    return self.not_implemented("units of measure", Planned::PastV1);
                }
                T::LBracket => return self.not_implemented("indexing expressions", Planned::Phase(2)),
                T::ColonColon => return self.not_implemented("explicit type arguments (`::[…]`)", Planned::Phase(2)),
                _ => {
                    self.depth = base;
                    return Ok(e);
                }
            }
        }
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
                        return self.not_implemented("tuples", Planned::Phase(2));
                    }
                    self.close(&open, T::RParen, "`)`")?;
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
            T::LBracket => return self.not_implemented("list and map literals", Planned::Phase(2)),
            T::Pipe => return self.not_implemented("closures", Planned::Phase(2)),
            T::Keyword(Kw::Match) => return self.not_implemented("`match` expressions", Planned::Phase(2)),
            T::Keyword(Kw::Scope) => return self.not_implemented("`scope` blocks", Planned::Phase(6)),
            T::Keyword(Kw::Attempt) => return self.not_implemented("`attempt` expressions", Planned::Phase(2)),
            T::Keyword(Kw::Fail) => return self.not_implemented("`fail` expressions", Planned::Phase(2)),
            T::Keyword(Kw::It) => return self.not_implemented("`it` bindings", Planned::Phase(2)),
            T::Keyword(Kw::SelfValue | Kw::SelfType) => {
                return self.not_implemented("methods and `self`", Planned::Phase(2));
            }
            T::Keyword(Kw::All | Kw::Any) => return self.not_implemented("quantifiers", Planned::Phase(5)),
            _ => return self.unexpected("an expression"),
        };
        let span = start.to(self.prev_span());
        Ok(self.alloc(kind, span))
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
                if self.at(T::LParen) {
                    return self.not_implemented("tuple patterns", Planned::Phase(2));
                }
                let binding = self.ident("a loop variable")?;
                self.expect(T::Keyword(Kw::In), "`in`")?;
                if self.at_kw(Kw::Take) {
                    return self.not_implemented("consuming loops (`for … in take`)", Planned::Phase(2));
                }
                let iter = self.nested(Self::logical)?;
                self.no_invariant()?;
                let body = self.block()?;
                ExprKind::For { label, binding, iter, body }
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

/// Item keywords that belong to later phases, with what to call them.
fn planned_item(kw: Kw) -> Option<(&'static str, Planned)> {
    Some(match kw {
        Kw::Record => ("`record` declarations", Planned::Phase(2)),
        Kw::Enum => ("`enum` declarations", Planned::Phase(2)),
        Kw::Type => ("`type` declarations", Planned::Phase(2)),
        Kw::Distinct => ("distinct types", Planned::Phase(2)),
        Kw::Unique | Kw::Opaque | Kw::Resource => ("`unique`, `opaque` and `resource` records", Planned::Phase(2)),
        Kw::Impl => ("`impl` blocks", Planned::Phase(2)),
        Kw::Interface => ("interfaces", Planned::Phase(2)),
        Kw::Example => ("`example` declarations", Planned::Phase(2)),
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
