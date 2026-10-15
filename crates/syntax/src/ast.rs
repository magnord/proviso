//! The syntax tree. Nodes live in arenas owned by [`Module`] and refer to each other by id.

use std::collections::HashSet;

use crate::arena::{Arena, Id};
use crate::intern::{Interner, Symbol};
use crate::source::Span;

pub type ExprId = Id<Expr>;
pub type StmtId = Id<Stmt>;
pub type TypeId = Id<TypeExpr>;

pub struct Module {
    /// The module path, such as `users` for `users.proviso`.
    pub name: String,
    pub items: Vec<Item>,
    pub exprs: Arena<Expr>,
    pub stmts: Arena<Stmt>,
    pub types: Arena<TypeExpr>,
    pub interner: Interner,
    /// Functions whose declarations failed to parse. Calls of them are not reported again.
    pub poisoned: HashSet<Symbol>,
}

impl Module {
    pub fn text(&self, sym: Symbol) -> &str {
        self.interner.resolve(sym)
    }

    pub fn fn_decl(&self, item: usize) -> Option<&FnDecl> {
        match &self.items.get(item)?.kind {
            ItemKind::Fn(decl) => Some(decl),
            ItemKind::Use(_) => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Ident {
    pub sym: Symbol,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Visibility {
    Private,
    Pub,
    PubPkg,
}

pub struct Item {
    pub kind: ItemKind,
    pub vis: Visibility,
    pub doc: Option<String>,
    pub span: Span,
}

impl Item {
    pub fn name(&self) -> Option<Ident> {
        match &self.kind {
            ItemKind::Fn(decl) => Some(decl.name),
            ItemKind::Use(_) => None,
        }
    }
}

pub enum ItemKind {
    Fn(FnDecl),
    Use(UseDecl),
}

pub struct FnDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: Option<TypeId>,
    pub fails: Option<TypeId>,
    pub body: Block,
    /// The body needed error recovery, so its control flow is unknown.
    pub recovered: bool,
}

pub struct Param {
    pub name: Ident,
    pub mode: ParamMode,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParamMode {
    Borrow,
    Inout,
    InoutPartial,
    Take,
    Keep,
}

/// `use a.b { X, y as z }`, or `use a.b` with no names.
pub struct UseDecl {
    pub path: Vec<Ident>,
    pub names: Vec<UseName>,
}

pub struct UseName {
    pub name: Ident,
    pub alias: Option<Ident>,
}

pub struct TypeExpr {
    pub kind: TypeExprKind,
    pub span: Span,
}

pub enum TypeExprKind {
    /// `Int`, `System`
    Named(Ident),
    /// `List[Int]` or `Float[m]`. The arguments are skipped until generics and units exist.
    Applied(Ident),
}

pub struct Block {
    pub stmts: Vec<StmtId>,
    pub span: Span,
}

pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

pub enum StmtKind {
    Let { mutable: bool, name: Ident, ty: Option<TypeId>, init: ExprId },
    Assign { target: ExprId, op: AssignOp, value: ExprId },
    Expr(ExprId),
    Return(Option<ExprId>),
    Break(Option<Ident>),
    Continue(Option<Ident>),
    Assert(ExprId),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AssignOp {
    Set,
    Add,
    Sub,
    Mul,
    Div,
}

impl AssignOp {
    /// The arithmetic a compound assignment performs.
    pub fn bin_op(self) -> Option<BinOp> {
        match self {
            AssignOp::Set => None,
            AssignOp::Add => Some(BinOp::Add),
            AssignOp::Sub => Some(BinOp::Sub),
            AssignOp::Mul => Some(BinOp::Mul),
            AssignOp::Div => Some(BinOp::Div),
        }
    }
}

pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub enum ExprKind {
    Int(u128),
    /// The literal's digits; its type decides whether it is parsed as binary32 or binary64.
    Float(String),
    Bool(bool),
    Char(char),
    Text(String),
    Unit,
    FText(Vec<FTextPart>),
    Name(Ident),
    Call {
        callee: ExprId,
        args: Vec<Arg>,
    },
    MethodCall {
        receiver: ExprId,
        method: Ident,
        args: Vec<Arg>,
    },
    Field {
        base: ExprId,
        name: Ident,
    },
    Unary {
        op: UnaryOp,
        operand: ExprId,
    },
    Binary {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Range {
        lo: ExprId,
        hi: ExprId,
        inclusive: bool,
    },
    Try(ExprId),
    If {
        cond: ExprId,
        then_block: Block,
        else_branch: Option<ElseBranch>,
    },
    While {
        label: Option<Ident>,
        cond: ExprId,
        body: Block,
    },
    Loop {
        label: Option<Ident>,
        body: Block,
    },
    For {
        label: Option<Ident>,
        binding: Ident,
        iter: ExprId,
        body: Block,
    },
    Todo(Option<String>),
    Unreachable,
    Debug(Vec<ExprId>),
    /// Stands in for code that failed to parse, which is already reported.
    Error,
}

pub enum ElseBranch {
    Block(Block),
    If(ExprId),
}

pub enum FTextPart {
    Lit(String),
    Expr(ExprId),
}

pub struct Arg {
    pub label: Option<Ident>,
    /// Written with the `&` mutation marker (H5).
    pub inout: bool,
    pub value: ExprId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
        }
    }

    pub fn is_arithmetic(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem)
    }
}
