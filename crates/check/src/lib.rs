//! Name resolution and type checking for the phase-1 subset: scalar types, functions,
//! control flow, `fails` and `try`, and the stub `System` with only `stdout`.
//!
//! The checker never rewrites the tree. It records what it learns in side tables of
//! [`Program`], which the interpreter reads.

pub mod types;

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use proviso_syntax::arena::SideTable;
use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, Planned, codes};
use proviso_syntax::intern::Symbol;
use proviso_syntax::source::Span;

use crate::types::{FloatTy, IntTy, Ty};

#[derive(Clone, Copy, Default, Debug)]
pub struct Options {
    /// Accept `todo` holes (REFERENCE §15.2, Q25).
    pub incomplete: bool,
    /// The module is about to run, so it must have a `main`.
    pub needs_main: bool,
}

/// A local variable or parameter, numbered within its function.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocalId(pub u32);

impl LocalId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

pub type FnId = usize;

/// Operations the toolchain provides directly in phase 1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Builtin {
    /// `Out.write_line(text: Text) fails IoError`
    WriteLine,
    /// `show()` on any type with `Show`
    Show,
    /// `Text.byte_len() -> Int`
    ByteLen,
    /// `Text.is_empty() -> Bool`
    IsEmpty,
}

/// What a name, call or member access resolved to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Res {
    Local(LocalId),
    Fn(FnId),
    Method(Builtin),
    /// `System.stdout`
    Stdout,
}

pub struct FnInfo {
    /// Index of the declaring item in `Module::items`.
    pub item: usize,
    pub name: Symbol,
    pub params: Vec<ParamInfo>,
    pub ret: Ty,
    pub fails: Option<Ty>,
    /// Number of local slots, parameters first.
    pub locals: usize,
}

pub struct ParamInfo {
    pub name: Symbol,
    pub ty: Ty,
    pub mode: ParamMode,
}

/// What the checker learned about a module.
#[derive(Default)]
pub struct Program {
    pub fns: Vec<FnInfo>,
    pub main: Option<FnId>,
    pub expr_ty: SideTable<Expr, Ty>,
    pub res: SideTable<Expr, Res>,
    pub let_local: SideTable<Stmt, LocalId>,
    pub for_local: SideTable<Expr, LocalId>,
    /// The loop each `break` or `continue` leaves.
    pub jump_target: SideTable<Stmt, ExprId>,
}

impl Program {
    pub fn ty(&self, e: ExprId) -> Ty {
        self.expr_ty.get(e).copied().unwrap_or(Ty::Error)
    }

    pub fn res(&self, e: ExprId) -> Option<Res> {
        self.res.get(e).copied()
    }
}

pub fn check_module(m: &Module, opts: Options, diags: &mut Diagnostics) -> Program {
    let mut checker = Checker {
        m,
        opts,
        diags,
        p: Program::default(),
        fn_names: HashMap::new(),
        imports: HashMap::new(),
        f: FnState::new(Ty::Unit, None),
        in_chain: false,
        tries: Vec::new(),
    };
    checker.imports();
    checker.signatures();
    checker.check_main();
    for id in 0..checker.p.fns.len() {
        checker.body(id);
    }
    checker.p
}

#[derive(Clone, Copy)]
enum Import {
    Type(Ty),
    /// `use a.b` makes `b` usable as a qualifier.
    Module,
}

struct Local {
    ty: Ty,
    mutable: bool,
}

struct LoopState {
    expr: ExprId,
    label: Option<Symbol>,
    broken: bool,
}

struct FnState {
    ret: Ty,
    fails: Option<Ty>,
    scopes: Vec<Vec<(Symbol, LocalId)>>,
    locals: Vec<Local>,
    loops: Vec<LoopState>,
}

impl FnState {
    fn new(ret: Ty, fails: Option<Ty>) -> FnState {
        FnState { ret, fails, scopes: Vec::new(), locals: Vec::new(), loops: Vec::new() }
    }
}

/// Whether an `if` is used for its value, as a statement, or as the last statement of a
/// function that returns this type.
#[derive(Clone, Copy)]
enum Mode {
    Stmt,
    Value(Option<Ty>),
    Tail(Ty),
}

const NO_PARAMS: &[(&str, Ty)] = &[];
const WRITE_LINE_PARAMS: &[(&str, Ty)] = &[("text", Ty::Text)];

struct Checker<'a> {
    m: &'a Module,
    opts: Options,
    diags: &'a mut Diagnostics,
    p: Program,
    fn_names: HashMap<Symbol, FnId>,
    imports: HashMap<Symbol, Import>,
    /// The function being checked.
    f: FnState,
    /// Set while checking the postfix chain a `try` covers (REFERENCE §6.1).
    in_chain: bool,
    /// For each enclosing `try`, the error types of the fallible calls it marks.
    tries: Vec<Vec<Ty>>,
}

impl Checker<'_> {
    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.diags.error(code, span, message);
    }

    fn not_implemented(&mut self, span: Span, what: &str, planned: Planned) {
        self.diags.not_implemented(span, what, planned);
    }

    fn span(&self, e: ExprId) -> Span {
        self.m.exprs[e].span
    }

    // ---- module level ----

    fn imports(&mut self) {
        let m = self.m;
        for item in &m.items {
            if let ItemKind::Use(decl) = &item.kind {
                self.use_decl(decl);
            }
        }
    }

    /// Whether another name in the module's scope is spelled like `name`, so that importing
    /// `name` needs `as` (REFERENCE §3, Q24).
    fn collides(&self, name: &UseName) -> bool {
        let m = self.m;
        let text = m.text(name.name.sym);
        let mut others = m.items.iter().flat_map(|item| match &item.kind {
            ItemKind::Fn(decl) => vec![decl.name],
            ItemKind::Use(decl) if decl.names.is_empty() => vec![decl.path[decl.path.len() - 1]],
            ItemKind::Use(decl) => decl
                .names
                .iter()
                .filter(|other| !std::ptr::eq(*other, name))
                .flat_map(|other| [Some(other.name), other.alias].into_iter().flatten())
                .collect(),
        });
        prelude_type(text) || others.any(|other| m.text(other.sym) == text)
    }

    fn use_decl(&mut self, decl: &UseDecl) {
        let m = self.m;
        let path: Vec<&str> = decl.path.iter().map(|i| m.text(i.sym)).collect();
        let joined = path.join(".");
        let span = decl.path[0].span.to(decl.path[decl.path.len() - 1].span);
        let available: Option<&[(&str, Ty)]> = match path.as_slice() {
            ["std", "io"] => Some(&[("IoError", Ty::IoError), ("Out", Ty::Out)]),
            ["std", module] => {
                let planned = match *module {
                    "fs" | "test" => Planned::Phase(3),
                    "pool" | "text" => Planned::Phase(2),
                    "task" => Planned::Phase(6),
                    _ => Planned::Unscheduled,
                };
                self.not_implemented(span, &format!("the `{joined}` module and its items"), planned);
                None
            }
            _ => {
                self.error(
                    codes::UNKNOWN_IMPORT,
                    span,
                    format!("unknown module `{joined}`; phase 1 checks one file at a time, and the standard library provides only `std.io`"),
                );
                None
            }
        };
        if decl.names.is_empty() {
            let last = decl.path[decl.path.len() - 1];
            self.bind_import(last, Import::Module);
            return;
        }
        for name in &decl.names {
            let text = m.text(name.name.sym);
            let ty = match available {
                Some(items) => match items.iter().find(|(n, _)| *n == text) {
                    Some((_, ty)) => *ty,
                    None => {
                        self.error(codes::UNKNOWN_IMPORT, name.name.span, format!("`{joined}` has no item `{text}`"));
                        Ty::Error
                    }
                },
                None => Ty::Error,
            };
            let bound = name.alias.unwrap_or(name.name);
            let bound_text = m.text(bound.sym);
            if prelude_type(bound_text) {
                self.error(
                    codes::SHADOWING,
                    bound.span,
                    format!("this import would shadow the prelude type `{bound_text}` (H4)"),
                );
                continue;
            }
            if let Some(alias) = name.alias {
                if !self.collides(name) {
                    self.error(
                        codes::NEEDLESS_ALIAS,
                        alias.span,
                        format!("nothing else here is named `{text}`, so it needs no `as` (Q24)"),
                    );
                } else if bound_text.is_ascii() && !is_pascal(bound_text) {
                    self.error(codes::WRONG_CASE, bound.span, format!("type names are PascalCase: `{bound_text}`"));
                }
            }
            self.bind_import(bound, Import::Type(ty));
        }
    }

    fn bind_import(&mut self, name: Ident, import: Import) {
        match self.imports.entry(name.sym) {
            Entry::Occupied(_) => {
                let text = self.m.text(name.sym);
                self.error(codes::DUPLICATE_ITEM, name.span, format!("`{text}` is imported twice"));
            }
            Entry::Vacant(slot) => {
                slot.insert(import);
            }
        }
    }

    fn signatures(&mut self) {
        let m = self.m;
        for (index, item) in m.items.iter().enumerate() {
            let ItemKind::Fn(decl) = &item.kind else { continue };
            let name = m.text(decl.name.sym);
            // A wrongly cased name is reported once, not again for what it collides with.
            let cased = self.snake_case(decl.name, "function");
            let id = self.p.fns.len();
            if self.fn_names.contains_key(&decl.name.sym) || self.imports.contains_key(&decl.name.sym) {
                if cased {
                    self.error(
                        codes::DUPLICATE_ITEM,
                        decl.name.span,
                        format!("`{name}` is defined twice in this module"),
                    );
                }
            } else {
                self.fn_names.insert(decl.name.sym, id);
                if name == "main" {
                    self.p.main = Some(id);
                }
            }
            let mut params: Vec<ParamInfo> = Vec::new();
            for param in &decl.params {
                let cased = self.snake_case(param.name, "parameter");
                if cased && params.iter().any(|p| p.name == param.name.sym) {
                    let text = m.text(param.name.sym);
                    self.error(codes::SHADOWING, param.name.span, format!("parameter `{text}` is declared twice"));
                }
                let ty = self.resolve_type(param.ty);
                match param.mode {
                    ParamMode::Borrow => {}
                    ParamMode::Keep if matches!(ty, Ty::System | Ty::Error) => {}
                    ParamMode::Keep => {
                        self.not_implemented(param.span, "`keep` parameters other than `System`", Planned::Phase(3))
                    }
                    ParamMode::Inout | ParamMode::InoutPartial => {
                        self.not_implemented(param.span, "`inout` parameters", Planned::Phase(2))
                    }
                    ParamMode::Take => self.not_implemented(param.span, "`take` parameters", Planned::Phase(2)),
                }
                params.push(ParamInfo { name: param.name.sym, ty, mode: param.mode });
            }
            let ret = decl.ret.map_or(Ty::Unit, |t| self.resolve_type(t));
            // `Never` has no values, so a function that fails with it cannot fail.
            let fails = decl.fails.map(|t| self.resolve_type(t)).filter(|&t| t != Ty::Never);
            self.p.fns.push(FnInfo { item: index, name: decl.name.sym, params, ret, fails, locals: 0 });
        }
    }

    fn check_main(&mut self) {
        let Some(id) = self.p.main else {
            if self.opts.needs_main {
                self.error(
                    codes::INVALID_MAIN,
                    Span::default(),
                    "there is no `main` to run; declare `pub fn main(sys: keep System)`",
                );
            }
            return;
        };
        let info = &self.p.fns[id];
        let item = &self.m.items[info.item];
        let span = item.name().map_or(item.span, |n| n.span);
        let signature_ok = item.vis == Visibility::Pub
            && info.params.len() == 1
            && matches!(info.params[0].ty, Ty::System | Ty::Error)
            && info.params[0].mode == ParamMode::Keep
            && matches!(info.ret, Ty::Unit | Ty::Error);
        let fails = info.fails;
        if !signature_ok {
            self.error(
                codes::INVALID_MAIN,
                span,
                "`main` must be declared `pub fn main(sys: keep System)`, optionally followed by `fails E`",
            );
        }
        if let Some(err) = fails
            && !err.is_show()
            && err != Ty::Error
        {
            self.error(
                codes::MAIN_ERROR_NOT_SHOW,
                span,
                format!("`main` fails with `{err}`, which does not implement `Show`"),
            );
        }
    }

    fn resolve_type(&mut self, t: TypeId) -> Ty {
        let m = self.m;
        let te = &m.types[t];
        match te.kind {
            TypeExprKind::Named(name) => self.type_name(name),
            TypeExprKind::Applied(name) => {
                let text = m.text(name.sym);
                match builtin_type(text) {
                    Some(Ty::Int(_) | Ty::Float(_)) => {
                        self.not_implemented(te.span, "units of measure", Planned::PastV1)
                    }
                    Some(_) => self.error(codes::UNKNOWN_TYPE, te.span, format!("`{text}` takes no type arguments")),
                    None => match later_type(text) {
                        Some(planned) => self.not_implemented(name.span, &format!("`{text}` types"), planned),
                        None => self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown type `{text}`")),
                    },
                }
                Ty::Error
            }
        }
    }

    fn type_name(&mut self, name: Ident) -> Ty {
        let text = self.m.text(name.sym);
        if let Some(ty) = builtin_type(text) {
            return ty;
        }
        match self.imports.get(&name.sym) {
            Some(Import::Type(ty)) => return *ty,
            Some(Import::Module) => {
                self.error(codes::UNKNOWN_TYPE, name.span, format!("`{text}` is a module, not a type"));
                return Ty::Error;
            }
            None => {}
        }
        match later_type(text) {
            Some(planned) => self.not_implemented(name.span, &format!("`{text}` types"), planned),
            None => self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown type `{text}`")),
        }
        Ty::Error
    }

    /// Reports a name that isn't snake_case, and returns whether it is. A non-ASCII name is
    /// already reported by the lexer.
    fn snake_case(&mut self, name: Ident, what: &str) -> bool {
        let text = self.m.text(name.sym);
        if !text.is_ascii() {
            return false;
        }
        if !is_snake(text) {
            self.error(codes::WRONG_CASE, name.span, format!("{what} names are snake_case: `{text}`"));
            return false;
        }
        true
    }

    // ---- functions ----

    fn body(&mut self, id: FnId) {
        let m = self.m;
        let info = &self.p.fns[id];
        let Some(decl) = m.fn_decl(info.item) else { return };
        let mut state = FnState::new(info.ret, info.fails);
        let mut scope = Vec::new();
        for (i, param) in info.params.iter().enumerate() {
            state.locals.push(Local { ty: param.ty, mutable: false });
            scope.push((param.name, LocalId(i as u32)));
        }
        state.scopes.push(scope);
        self.f = state;
        for param in &decl.params {
            self.shadows_item(param.name);
        }
        self.fn_body(decl);
        self.p.fns[id].locals = self.f.locals.len();
    }

    fn fn_body(&mut self, decl: &FnDecl) {
        let m = self.m;
        let ret = self.f.ret;
        self.f.scopes.push(Vec::new());
        let diverges = if ret == Ty::Unit {
            decl.body.stmts.iter().fold(false, |diverges, &s| self.stmt(s) | diverges)
        } else {
            self.tail_stmts(&decl.body, ret)
        };
        self.f.scopes.pop();
        // A body that needed parse recovery has unknown control flow.
        if ret != Ty::Unit && ret != Ty::Error && !diverges && !decl.recovered {
            let name = m.text(decl.name.sym);
            self.error(
                codes::MISSING_RETURN,
                decl.body.span.end(),
                format!("`{name}` returns `{ret}`, so every path must end with `return`"),
            );
        }
    }

    /// Checks the statements of a body that returns `ret`, or of a branch that ends one. A
    /// final value there is a missing `return`, not an unused value. Returns whether the
    /// statements always diverge, counting such a value as a return.
    fn tail_stmts(&mut self, block: &Block, ret: Ty) -> bool {
        let m = self.m;
        let mut diverges = false;
        let count = block.stmts.len();
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == count
                && let StmtKind::Expr(e) = m.stmts[s].kind
            {
                if is_bare_value(&m.exprs[e].kind) {
                    self.check(e, ret);
                    let span = self.span(e);
                    self.error(
                        codes::MISSING_RETURN,
                        span,
                        "function bodies have no implicit final value; write `return` before it",
                    );
                    return true;
                }
                if let ExprKind::If { .. } = m.exprs[e].kind {
                    return diverges | diverges_ty(self.if_expr(e, Mode::Tail(ret)));
                }
            }
            diverges |= self.stmt(s);
        }
        diverges
    }

    /// Declares a local in the innermost scope.
    fn declare(&mut self, name: Ident, ty: Ty, mutable: bool, what: &str) -> LocalId {
        let id = LocalId(self.f.locals.len() as u32);
        self.f.locals.push(Local { ty, mutable });
        if self.m.text(name.sym) == "_" {
            return id;
        }
        // A wrongly cased name is reported once, not again as a shadow.
        if self.snake_case(name, what) {
            if self.lookup_local(name.sym).is_some() {
                let text = self.m.text(name.sym);
                self.error(
                    codes::SHADOWING,
                    name.span,
                    format!("`{text}` is already defined in this function, and Proviso does not allow shadowing (H4)"),
                );
            } else {
                self.shadows_item(name);
            }
        }
        self.f.scopes.last_mut().expect("a scope is open").push((name.sym, id));
        id
    }

    /// Reports a binding that reuses the name of a function or import in this module. A
    /// wrongly cased name has been reported already, so it isn't reported again.
    fn shadows_item(&mut self, name: Ident) {
        let text = self.m.text(name.sym);
        if !is_snake(text) {
            return;
        }
        let kind = if self.fn_names.contains_key(&name.sym) {
            "function"
        } else if self.imports.contains_key(&name.sym) {
            "import"
        } else {
            return;
        };
        self.error(codes::SHADOWING, name.span, format!("`{text}` would shadow the {kind} `{text}` (H4)"));
    }

    fn lookup_local(&self, sym: Symbol) -> Option<LocalId> {
        self.f.scopes.iter().rev().flat_map(|scope| scope.iter().rev()).find(|(s, _)| *s == sym).map(|&(_, id)| id)
    }

    // ---- statements ----

    /// Checks a statement and returns whether it always diverges.
    fn stmt(&mut self, s: StmtId) -> bool {
        let m = self.m;
        let stmt = &m.stmts[s];
        match &stmt.kind {
            StmtKind::Let { mutable, name, ty, init } => {
                let declared = ty.map(|t| self.resolve_type(t));
                let (ty, init_ty) = match declared {
                    Some(declared) => (declared, self.check(*init, declared)),
                    None => {
                        let ty = self.infer(*init);
                        (ty, ty)
                    }
                };
                let what = if *mutable { "variable" } else { "binding" };
                let id = self.declare(*name, ty, *mutable, what);
                self.p.let_local.insert(s, id);
                diverges_ty(init_ty)
            }
            StmtKind::Assign { target, op, value } => diverges_ty(self.assign(*target, *op, *value)),
            StmtKind::Expr(e) => diverges_ty(self.expr_stmt(*e)),
            StmtKind::Return(value) => {
                let ret = self.f.ret;
                match value {
                    Some(value) => {
                        self.check(*value, ret);
                    }
                    None if ret != Ty::Unit && ret != Ty::Error => {
                        self.error(codes::TYPE_MISMATCH, stmt.span, format!("`return` needs a value of type `{ret}`"));
                    }
                    None => {}
                }
                true
            }
            StmtKind::Break(label) => {
                self.jump(s, *label, true);
                true
            }
            StmtKind::Continue(label) => {
                self.jump(s, *label, false);
                true
            }
            StmtKind::Assert(cond) => diverges_ty(self.check(*cond, Ty::Bool)),
        }
    }

    fn expr_stmt(&mut self, e: ExprId) -> Ty {
        let kind = &self.m.exprs[e].kind;
        if let ExprKind::If { .. } = kind {
            return self.if_expr(e, Mode::Stmt);
        }
        if is_bare_value(kind) {
            let span = self.span(e);
            self.error(
                codes::BARE_VALUE_STATEMENT,
                span,
                "this value is unused; a statement must be a call, an assignment or a control expression",
            );
        }
        self.infer(e)
    }

    /// Checks an assignment and returns the type of the assigned value.
    fn assign(&mut self, target: ExprId, op: AssignOp, value: ExprId) -> Ty {
        let m = self.m;
        let span = self.span(target);
        let ExprKind::Name(name) = m.exprs[target].kind else {
            match m.exprs[target].kind {
                ExprKind::Field { .. } => self.not_implemented(span, "assignments to fields", Planned::Phase(2)),
                _ => self.error(codes::INVALID_ASSIGNMENT_TARGET, span, "only variables can be assigned"),
            }
            return self.infer(value);
        };
        let text = m.text(name.sym);
        let Some(id) = self.lookup_local(name.sym) else {
            if !m.poisoned.contains(&name.sym) {
                self.error(codes::UNKNOWN_NAME, span, format!("unknown variable `{text}`"));
            }
            return self.infer(value);
        };
        self.p.res.insert(target, Res::Local(id));
        let Local { ty, mutable } = self.f.locals[id.index()];
        self.p.expr_ty.insert(target, ty);
        if !mutable {
            self.error(
                codes::IMMUTABLE_ASSIGNMENT,
                span,
                format!("`{text}` is a `let` binding or a parameter; declare it with `var` to assign to it"),
            );
        }
        let value_ty = self.check(value, ty);
        if let Some(bin) = op.bin_op()
            && !arithmetic_defined(bin, ty)
        {
            let symbol = bin.symbol();
            self.error(codes::UNSUPPORTED_OPERATOR, span, format!("`{symbol}=` is not defined for `{ty}`"));
        }
        value_ty
    }

    fn jump(&mut self, s: StmtId, label: Option<Ident>, is_break: bool) {
        let span = self.m.stmts[s].span;
        let keyword = if is_break { "break" } else { "continue" };
        let index = match label {
            None if self.f.loops.is_empty() => {
                self.error(codes::MISPLACED_JUMP, span, format!("`{keyword}` outside a loop"));
                return;
            }
            None => self.f.loops.len() - 1,
            Some(label) => match self.f.loops.iter().rposition(|l| l.label == Some(label.sym)) {
                Some(index) => index,
                None => {
                    let text = self.m.text(label.sym);
                    self.error(codes::MISPLACED_JUMP, label.span, format!("no enclosing loop is labelled `{text}`"));
                    return;
                }
            },
        };
        if is_break {
            self.f.loops[index].broken = true;
        }
        let target = self.f.loops[index].expr;
        self.p.jump_target.insert(s, target);
    }

    /// Checks a block whose value is unused. Returns `Never` if it always diverges. With
    /// `tail`, the block ends a function that returns that type.
    fn block_stmt(&mut self, block: &Block, tail: Option<Ty>) -> Ty {
        self.f.scopes.push(Vec::new());
        let diverges = match tail {
            Some(ret) => self.tail_stmts(block, ret),
            None => block.stmts.iter().fold(false, |diverges, &s| self.stmt(s) | diverges),
        };
        self.f.scopes.pop();
        if diverges { Ty::Never } else { Ty::Unit }
    }

    /// Checks a block used for its value: the final expression, if there is one.
    fn block_value(&mut self, block: &Block, expected: Option<Ty>) -> Ty {
        let m = self.m;
        self.f.scopes.push(Vec::new());
        let mut diverges = false;
        let mut value = None;
        let count = block.stmts.len();
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == count
                && let StmtKind::Expr(e) = m.stmts[s].kind
            {
                let ty = match expected {
                    Some(expected) => self.check(e, expected),
                    None => self.infer(e),
                };
                diverges |= diverges_ty(ty);
                value = Some(ty);
                continue;
            }
            diverges |= self.stmt(s);
        }
        self.f.scopes.pop();
        if diverges {
            return Ty::Never;
        }
        match (value, expected) {
            (Some(ty), _) => ty,
            (None, Some(expected)) if expected != Ty::Unit && expected != Ty::Error => {
                self.error(
                    codes::TYPE_MISMATCH,
                    block.span.end(),
                    format!("expected a value of type `{expected}`, but this block ends without one"),
                );
                Ty::Error
            }
            (None, _) => Ty::Unit,
        }
    }

    // ---- expressions ----

    fn infer(&mut self, e: ExprId) -> Ty {
        self.expr(e, None)
    }

    /// Checks `e` against `expected`, reports a mismatch, and returns the actual type.
    fn check(&mut self, e: ExprId, expected: Ty) -> Ty {
        let actual = self.expr(e, Some(expected));
        if !expected.accepts(actual) {
            let span = self.span(e);
            self.error(codes::TYPE_MISMATCH, span, format!("expected `{expected}`, found `{actual}`"));
        }
        actual
    }

    /// Infers the type of `e`. `expected` guides literals and `if` branches, but mismatches
    /// against it are reported by [`Checker::check`].
    fn expr(&mut self, e: ExprId, expected: Option<Ty>) -> Ty {
        let chain = std::mem::replace(&mut self.in_chain, false);
        let ty = self.expr_kind(e, expected, chain);
        self.p.expr_ty.insert(e, ty);
        ty
    }

    fn expr_kind(&mut self, e: ExprId, expected: Option<Ty>, chain: bool) -> Ty {
        let m = self.m;
        let span = self.span(e);
        match &m.exprs[e].kind {
            ExprKind::Int(value) => self.int_literal(*value, false, expected, span),
            ExprKind::Float(text) => {
                let ft = match expected {
                    Some(Ty::Float(ft)) => ft,
                    _ => FloatTy::F64,
                };
                if !ft.holds(text) {
                    self.error(codes::LITERAL_OUT_OF_RANGE, span, format!("`{text}` is too large for `{}`", ft.name()));
                }
                Ty::Float(ft)
            }
            ExprKind::Bool(_) => Ty::Bool,
            ExprKind::Char(_) => Ty::Char,
            ExprKind::Text(_) => Ty::Text,
            ExprKind::Unit => Ty::Unit,
            ExprKind::FText(parts) => {
                for part in parts {
                    if let FTextPart::Expr(x) = part {
                        let ty = self.infer(*x);
                        if !ty.is_show() && !ty.is_unknown() {
                            let span = self.span(*x);
                            self.error(
                                codes::UNSUPPORTED_OPERATOR,
                                span,
                                format!("`{ty}` does not implement `Show`, so it cannot be interpolated"),
                            );
                        }
                    }
                }
                Ty::Text
            }
            ExprKind::Name(name) => self.name(e, *name),
            ExprKind::Call { callee, args } => self.call(*callee, args, span, chain),
            ExprKind::MethodCall { receiver, method, args } => {
                self.method_call(e, *receiver, *method, args, span, chain)
            }
            ExprKind::Field { base, name } => {
                self.in_chain = chain;
                let base_ty = self.infer(*base);
                self.field(e, base_ty, *name)
            }
            ExprKind::Unary { op: UnaryOp::Not, operand } => {
                self.check(*operand, Ty::Bool);
                Ty::Bool
            }
            ExprKind::Unary { op: UnaryOp::Neg, operand } => self.negate(*operand, expected, span),
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, *lhs, *rhs, expected, span),
            ExprKind::Range { .. } => {
                self.not_implemented(span, "ranges outside `for` loops", Planned::Phase(2));
                Ty::Error
            }
            ExprKind::Try(inner) => self.try_expr(*inner, expected, span),
            ExprKind::If { .. } => self.if_expr(e, Mode::Value(expected)),
            ExprKind::While { label, cond, body } => {
                self.check(*cond, Ty::Bool);
                self.loop_body(e, *label, body);
                Ty::Unit
            }
            ExprKind::Loop { label, body } => {
                if self.loop_body(e, *label, body) {
                    Ty::Unit
                } else {
                    Ty::Never
                }
            }
            ExprKind::For { label, binding, iter, body } => self.for_loop(e, *label, *binding, *iter, body),
            ExprKind::Todo(_) if self.opts.incomplete => Ty::Never,
            ExprKind::Todo(_) => {
                self.error(
                    codes::TODO_REQUIRES_INCOMPLETE,
                    span,
                    "`todo` holes are accepted only with `--incomplete` (Q25)",
                );
                Ty::Error
            }
            ExprKind::Unreachable => Ty::Never,
            ExprKind::Debug(values) => {
                for value in values {
                    self.infer(*value);
                }
                Ty::Unit
            }
            ExprKind::Error => Ty::Error,
        }
    }

    fn int_literal(&mut self, magnitude: u128, negative: bool, expected: Option<Ty>, span: Span) -> Ty {
        let it = match expected {
            Some(Ty::Int(it)) => it,
            Some(Ty::Float(ft)) => {
                self.error(
                    codes::TYPE_MISMATCH,
                    span,
                    format!(
                        "an integer literal cannot become `{}`; write it with a decimal point, such as `1.0`",
                        ft.name()
                    ),
                );
                return Ty::Error;
            }
            _ => IntTy::I64,
        };
        let value = i128::try_from(magnitude).ok().map(|v| if negative { -v } else { v });
        if !value.is_some_and(|v| it.contains(v)) {
            let sign = if negative { "-" } else { "" };
            self.error(
                codes::LITERAL_OUT_OF_RANGE,
                span,
                format!(
                    "`{sign}{magnitude}` does not fit in `{}`, whose range is {}..={}",
                    it.name(),
                    it.min(),
                    it.max()
                ),
            );
        }
        Ty::Int(it)
    }

    fn negate(&mut self, operand: ExprId, expected: Option<Ty>, span: Span) -> Ty {
        // A negative integer literal is one value, so `-128` fits in `Int8`.
        if let ExprKind::Int(value) = self.m.exprs[operand].kind {
            let ty = self.int_literal(value, true, expected, span);
            self.p.expr_ty.insert(operand, ty);
            return ty;
        }
        let ty = self.expr(operand, expected.filter(|t| t.is_numeric()));
        match ty {
            Ty::Int(it) if it.is_signed() => ty,
            Ty::Float(_) | Ty::Error | Ty::Never => ty,
            _ => {
                self.error(codes::UNSUPPORTED_OPERATOR, span, format!("unary `-` is not defined for `{ty}`"));
                Ty::Error
            }
        }
    }

    /// Checks the operands of a binary operator. An untyped literal takes its type from the
    /// other operand (REFERENCE §2), so the non-literal side is checked first.
    fn operands(&mut self, lhs: ExprId, rhs: ExprId, hint: Option<Ty>) -> (Ty, Ty) {
        // An operand that already has an error gives the other no type, so a literal there
        // isn't reported again against the hint.
        let numeric_or = |ty: Ty| match ty {
            Ty::Error => None,
            ty if ty.is_numeric() => Some(ty),
            _ => hint,
        };
        if self.is_untyped_literal(lhs) && !self.is_untyped_literal(rhs) {
            let rt = self.expr(rhs, hint);
            let lt = self.expr(lhs, numeric_or(rt));
            (lt, rt)
        } else {
            let lt = self.expr(lhs, hint);
            let rt = self.expr(rhs, numeric_or(lt));
            (lt, rt)
        }
    }

    /// A literal, or arithmetic on literals such as `(1 + 2)`, which takes its type from
    /// context like a single literal (OPEN_QUESTIONS P5).
    fn is_untyped_literal(&self, e: ExprId) -> bool {
        match &self.m.exprs[e].kind {
            ExprKind::Int(_) | ExprKind::Float(_) => true,
            ExprKind::Unary { op: UnaryOp::Neg, operand } => self.is_untyped_literal(*operand),
            ExprKind::Binary { op, lhs, rhs } if op.is_arithmetic() => {
                self.is_untyped_literal(*lhs) && self.is_untyped_literal(*rhs)
            }
            _ => false,
        }
    }

    fn unify_operands(&mut self, lt: Ty, rt: Ty, span: Span) -> Ty {
        match (lt, rt) {
            (Ty::Error, _) | (_, Ty::Error) => Ty::Error,
            _ if lt == rt => lt,
            (Ty::Never, other) | (other, Ty::Never) => other,
            _ => {
                self.error(
                    codes::TYPE_MISMATCH,
                    span,
                    format!("mismatched operand types `{lt}` and `{rt}`; Proviso has no implicit conversions"),
                );
                Ty::Error
            }
        }
    }

    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, expected: Option<Ty>, span: Span) -> Ty {
        let symbol = op.symbol();
        match op {
            BinOp::And | BinOp::Or => {
                self.check(lhs, Ty::Bool);
                self.check(rhs, Ty::Bool);
                Ty::Bool
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let (lt, rt) = self.operands(lhs, rhs, expected.filter(|t| t.is_numeric()));
                let ty = self.unify_operands(lt, rt, span);
                if !arithmetic_defined(op, ty) {
                    self.error(codes::UNSUPPORTED_OPERATOR, span, format!("`{symbol}` is not defined for `{ty}`"));
                    return Ty::Error;
                }
                ty
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (lt, rt) = self.operands(lhs, rhs, None);
                let ty = self.unify_operands(lt, rt, span);
                let defined = match op {
                    BinOp::Eq | BinOp::Ne => ty.has_equality(),
                    _ => ty.has_ordering(),
                };
                if !defined && !ty.is_unknown() {
                    self.error(codes::UNSUPPORTED_OPERATOR, span, format!("`{symbol}` is not defined for `{ty}`"));
                }
                Ty::Bool
            }
        }
    }

    fn name(&mut self, e: ExprId, name: Ident) -> Ty {
        let m = self.m;
        let text = m.text(name.sym);
        if let Some(id) = self.lookup_local(name.sym) {
            self.p.res.insert(e, Res::Local(id));
            return self.f.locals[id.index()].ty;
        }
        if self.fn_names.contains_key(&name.sym) {
            self.not_implemented(name.span, "functions used as values", Planned::Phase(3));
        } else if self.imports.contains_key(&name.sym) || builtin_type(text).is_some() {
            self.error(codes::UNKNOWN_NAME, name.span, format!("`{text}` is a type or module, not a value"));
        } else if !m.poisoned.contains(&name.sym) {
            self.error(codes::UNKNOWN_NAME, name.span, format!("unknown name `{text}`"));
        }
        Ty::Error
    }

    fn call(&mut self, callee: ExprId, args: &[Arg], span: Span, chain: bool) -> Ty {
        let m = self.m;
        let resolved = match m.exprs[callee].kind {
            ExprKind::Name(name) => match self.fn_names.get(&name.sym) {
                Some(&id) => Ok(id),
                None => Err(Some(name)),
            },
            _ => Err(None),
        };
        let id = match resolved {
            Ok(id) => id,
            Err(name) => {
                let callee_span = self.span(callee);
                match name {
                    Some(name) if self.lookup_local(name.sym).is_some() => {
                        self.not_implemented(callee_span, "calls of function values", Planned::Phase(3))
                    }
                    Some(name) if builtin_type(m.text(name.sym)).is_some() => {
                        self.not_implemented(callee_span, "conversions such as `Int64(x)`", Planned::Phase(2))
                    }
                    Some(name) if m.poisoned.contains(&name.sym) => {}
                    Some(name) => {
                        let text = m.text(name.sym);
                        self.error(codes::UNKNOWN_NAME, name.span, format!("unknown function `{text}`"));
                    }
                    None => self.not_implemented(callee_span, "calls of function values", Planned::Phase(3)),
                }
                for arg in args {
                    self.infer(arg.value);
                }
                return Ty::Error;
            }
        };
        self.p.res.insert(callee, Res::Fn(id));
        let info = &self.p.fns[id];
        let name = m.text(info.name);
        let params: Vec<(&str, Ty)> = info.params.iter().map(|p| (m.text(p.name), p.ty)).collect();
        let (ret, fails) = (info.ret, info.fails);
        self.args(name, &params, args, span);
        if let Some(err) = fails {
            self.fallible_call(name, err, span, chain);
        }
        ret
    }

    fn method_call(&mut self, e: ExprId, receiver: ExprId, method: Ident, args: &[Arg], span: Span, chain: bool) -> Ty {
        self.in_chain = chain;
        let receiver_ty = self.infer(receiver);
        let name = self.m.text(method.sym);
        let signature = match (receiver_ty, name) {
            (Ty::Out, "write_line") => Some((Builtin::WriteLine, WRITE_LINE_PARAMS, Ty::Unit, Some(Ty::IoError))),
            (ty, "show") if ty.is_show() => Some((Builtin::Show, NO_PARAMS, Ty::Text, None)),
            (Ty::Text, "byte_len") => Some((Builtin::ByteLen, NO_PARAMS, Ty::INT, None)),
            (Ty::Text, "is_empty") => Some((Builtin::IsEmpty, NO_PARAMS, Ty::Bool, None)),
            _ => None,
        };
        let Some((builtin, params, ret, fails)) = signature else {
            if receiver_ty != Ty::Error {
                self.error(codes::UNKNOWN_MEMBER, method.span, format!("`{receiver_ty}` has no method `{name}`"));
            }
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        };
        self.p.res.insert(e, Res::Method(builtin));
        self.args(name, params, args, span);
        if let Some(err) = fails {
            self.fallible_call(name, err, span, chain);
        }
        ret
    }

    fn field(&mut self, e: ExprId, base_ty: Ty, name: Ident) -> Ty {
        let text = self.m.text(name.sym);
        match (base_ty, text) {
            (Ty::System, "stdout") => {
                self.p.res.insert(e, Res::Stdout);
                Ty::Out
            }
            (Ty::System, "fs" | "net" | "clock" | "random" | "env" | "stdin" | "stderr" | "process") => {
                self.not_implemented(
                    name.span,
                    &format!("`System` fields other than `stdout`, such as `{text}`,"),
                    Planned::Phase(3),
                );
                Ty::Error
            }
            (Ty::Error, _) => Ty::Error,
            (ty, _) => {
                self.error(codes::UNKNOWN_MEMBER, name.span, format!("`{ty}` has no field `{text}`"));
                Ty::Error
            }
        }
    }

    /// Checks arguments against parameters, including the label rules (REFERENCE §3, H3).
    fn args(&mut self, callee: &str, params: &[(&str, Ty)], args: &[Arg], span: Span) {
        let m = self.m;
        if args.len() != params.len() {
            let (n, given) = (params.len(), args.len());
            let noun = if n == 1 { "argument" } else { "arguments" };
            let verb = if given == 1 { "was" } else { "were" };
            self.error(
                codes::WRONG_ARGUMENT_COUNT,
                span,
                format!("`{callee}` takes {n} {noun}, but {given} {verb} given"),
            );
            for arg in args {
                self.infer(arg.value);
            }
            return;
        }
        // One label problem is reported per call, with the labels the call needs.
        let labelled = params.iter().map(|(param, _)| format!("{param}: …")).collect::<Vec<_>>().join(", ");
        let mut labels_reported = false;
        for (i, (arg, &(param, ty))) in args.iter().zip(params).enumerate() {
            if arg.inout {
                let span = self.span(arg.value);
                self.not_implemented(span, "`&` (inout) arguments", Planned::Phase(2));
            }
            match arg.label {
                _ if labels_reported => {}
                Some(label) if m.text(label.sym) != param => {
                    let text = m.text(label.sym);
                    self.error(
                        codes::WRONG_LABEL,
                        label.span,
                        format!(
                            "expected the label `{param}:` here, found `{text}:`; labels follow the declaration order, as in `{callee}({labelled})`"
                        ),
                    );
                    labels_reported = true;
                }
                None if params.len() >= 2 => {
                    let span = self.span(arg.value);
                    self.error(
                        codes::MISSING_LABEL,
                        span,
                        format!(
                            "argument {} of `{callee}` needs the label `{param}:`; write `{callee}({labelled})` (H3)",
                            i + 1
                        ),
                    );
                    labels_reported = true;
                }
                _ => {}
            }
            self.check(arg.value, ty);
        }
    }

    fn fallible_call(&mut self, callee: &str, err: Ty, span: Span, chain: bool) {
        match self.tries.last_mut() {
            Some(errors) if chain => errors.push(err),
            _ => self.error(
                codes::UNMARKED_FALLIBLE_CALL,
                span,
                format!("`{callee}` can fail with `{err}`, so the call must be marked, for example with `try` (§7.2)"),
            ),
        }
    }

    fn try_expr(&mut self, inner: ExprId, expected: Option<Ty>, span: Span) -> Ty {
        self.tries.push(Vec::new());
        self.in_chain = true;
        let ty = self.expr(inner, expected);
        let mut errors = self.tries.pop().unwrap_or_default();
        errors.dedup();
        // A chain with an error may hold the fallible call that didn't resolve.
        if errors.is_empty() && ty != Ty::Error {
            self.error(codes::TRY_WITHOUT_FAILURE, span, "`try` marks no call that can fail");
        }
        for err in errors {
            match self.f.fails {
                None => self.error(
                    codes::TRY_ERROR_MISMATCH,
                    span,
                    format!("`try` propagates `{err}`, but this function does not declare `fails {err}`"),
                ),
                Some(own) if own != err && own != Ty::Error && err != Ty::Error => self.error(
                    codes::TRY_ERROR_MISMATCH,
                    span,
                    format!("`try` needs equal error types, but the call fails with `{err}` and this function fails with `{own}`"),
                ),
                Some(_) => {}
            }
        }
        ty
    }

    fn if_expr(&mut self, e: ExprId, mode: Mode) -> Ty {
        let m = self.m;
        let ExprKind::If { cond, then_block, else_branch } = &m.exprs[e].kind else {
            unreachable!("if_expr is called on `if` expressions")
        };
        self.check(*cond, Ty::Bool);
        let ty = match (mode, else_branch) {
            (Mode::Stmt | Mode::Tail(_), _) => {
                let tail = match mode {
                    Mode::Tail(ret) => Some(ret),
                    _ => None,
                };
                let then_ty = self.block_stmt(then_block, tail);
                let else_ty = match else_branch {
                    Some(ElseBranch::Block(block)) => self.block_stmt(block, tail),
                    Some(ElseBranch::If(nested)) => self.if_expr(*nested, mode),
                    None => Ty::Unit,
                };
                if then_ty == Ty::Never && else_ty == Ty::Never { Ty::Never } else { Ty::Unit }
            }
            (Mode::Value(_), None) => {
                self.block_value(then_block, None);
                let span = self.span(e);
                self.error(codes::TYPE_MISMATCH, span, "an `if` without `else` has no value; add an `else` branch");
                Ty::Error
            }
            (Mode::Value(expected), Some(branch)) => {
                let then_ty = self.block_value(then_block, expected);
                let expected = expected.or(Some(then_ty).filter(|t| !t.is_unknown()));
                let else_ty = match branch {
                    ElseBranch::Block(block) => self.block_value(block, expected),
                    ElseBranch::If(nested) => self.if_expr(*nested, Mode::Value(expected)),
                };
                if then_ty == Ty::Never && else_ty == Ty::Never { Ty::Never } else { expected.unwrap_or(else_ty) }
            }
        };
        self.p.expr_ty.insert(e, ty);
        ty
    }

    /// Checks a loop body and returns whether a `break` leaves the loop.
    fn loop_body(&mut self, e: ExprId, label: Option<Ident>, body: &Block) -> bool {
        if let Some(label) = label {
            self.snake_case(label, "label");
        }
        self.f.loops.push(LoopState { expr: e, label: label.map(|l| l.sym), broken: false });
        self.block_stmt(body, None);
        self.f.loops.pop().is_some_and(|l| l.broken)
    }

    fn for_loop(&mut self, e: ExprId, label: Option<Ident>, binding: Ident, iter: ExprId, body: &Block) -> Ty {
        let m = self.m;
        let element = match m.exprs[iter].kind {
            ExprKind::Range { lo, hi, .. } => {
                let (lt, rt) = self.operands(lo, hi, None);
                let span = self.span(iter);
                match self.unify_operands(lt, rt, span) {
                    Ty::Int(it) => Ty::Int(it),
                    ty if ty.is_unknown() => Ty::Error,
                    ty => {
                        self.error(
                            codes::UNSUPPORTED_OPERATOR,
                            span,
                            format!("a `for` range needs integer bounds, not `{ty}`"),
                        );
                        Ty::Error
                    }
                }
            }
            _ => {
                self.infer(iter);
                let span = self.span(iter);
                self.not_implemented(span, "`for` loops over collections", Planned::Phase(2));
                Ty::Error
            }
        };
        self.p.expr_ty.insert(iter, element);
        self.f.scopes.push(Vec::new());
        let id = self.declare(binding, element, false, "loop variable");
        self.p.for_local.insert(e, id);
        self.loop_body(e, label, body);
        self.f.scopes.pop();
        Ty::Unit
    }
}

/// An expression whose only effect is its value, so it is not a statement on its own.
fn is_bare_value(kind: &ExprKind) -> bool {
    matches!(
        kind,
        ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Text(_)
            | ExprKind::Unit
            | ExprKind::FText(_)
            | ExprKind::Name(_)
            | ExprKind::Field { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Range { .. }
    )
}

/// Whether a statement or block of this type may never finish. An error counts, because the
/// code it stands for might diverge, and reporting a missing `return` would depend on it.
fn diverges_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Never | Ty::Error)
}

fn arithmetic_defined(op: BinOp, ty: Ty) -> bool {
    match ty {
        Ty::Int(_) => true,
        // Floats have no `%` (OPEN_QUESTIONS P5).
        Ty::Float(_) => op != BinOp::Rem,
        Ty::Error | Ty::Never => true,
        _ => false,
    }
}

/// The scalar types and `System` from the prelude (REFERENCE §3, §4.1).
fn builtin_type(name: &str) -> Option<Ty> {
    Some(match name {
        "Int" | "Int64" => Ty::Int(IntTy::I64),
        "Int8" => Ty::Int(IntTy::I8),
        "Int16" => Ty::Int(IntTy::I16),
        "Int32" => Ty::Int(IntTy::I32),
        "UInt8" | "Byte" => Ty::Int(IntTy::U8),
        "UInt16" => Ty::Int(IntTy::U16),
        "UInt32" => Ty::Int(IntTy::U32),
        "UInt64" => Ty::Int(IntTy::U64),
        "Float" => Ty::Float(FloatTy::F64),
        "Float32" => Ty::Float(FloatTy::F32),
        "Bool" => Ty::Bool,
        "Char" => Ty::Char,
        "Text" => Ty::Text,
        "Unit" => Ty::Unit,
        "Never" => Ty::Never,
        "System" => Ty::System,
        _ => return None,
    })
}

fn prelude_type(name: &str) -> bool {
    builtin_type(name).is_some() || later_type(name).is_some()
}

/// Prelude types that later phases implement.
fn later_type(name: &str) -> Option<Planned> {
    match name {
        "List" | "Map" | "Set" | "Array" | "Option" | "Result" | "Bytes" | "Ordering" | "Rounding" | "Invalid" => {
            Some(Planned::Phase(2))
        }
        "Eq" | "Ord" | "Hash" | "Show" | "Copy" | "Index" | "Abandon" | "Add" | "Sub" | "Mul" | "Div" | "Neg" => {
            Some(Planned::Phase(2))
        }
        "Outcome" | "Defect" => Some(Planned::Phase(6)),
        _ => None,
    }
}

fn is_snake(name: &str) -> bool {
    name.chars().next().is_some_and(|c| c.is_ascii_lowercase() || c == '_')
        && name.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

fn is_pascal(name: &str) -> bool {
    name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && name.chars().all(|c| c.is_ascii_alphanumeric())
}
