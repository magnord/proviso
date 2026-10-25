//! The syntax tree. Nodes live in arenas owned by [`Module`] and refer to each other by id.

use std::collections::HashSet;

use crate::arena::{Arena, Id};
use crate::intern::{Interner, Symbol};
use crate::source::Span;

pub type ExprId = Id<Expr>;
pub type StmtId = Id<Stmt>;
pub type TypeId = Id<TypeExpr>;
pub type PatId = Id<Pat>;

pub struct Module {
    /// The module path, such as `users` for `users.proviso`.
    pub name: String,
    pub items: Vec<Item>,
    pub exprs: Arena<Expr>,
    pub stmts: Arena<Stmt>,
    pub types: Arena<TypeExpr>,
    pub pats: Arena<Pat>,
    pub interner: Interner,
    /// Names of items whose declarations were rejected, such as a function that failed to
    /// parse or a later-phase `impl`. Uses of them are not reported again.
    pub poisoned: HashSet<Symbol>,
    /// Types named by a rejected `impl` block, such as `Point` in `impl Show for Point`. The
    /// block may have given them methods and interfaces, so uses of those aren't reported.
    pub impls: HashSet<Symbol>,
    /// Whether a rejected `impl` block was for a tuple type, which has no name to note in
    /// `impls`. Every tuple type may then have methods and interfaces we don't know.
    pub tuple_impls: bool,
}

impl Module {
    pub fn text(&self, sym: Symbol) -> &str {
        self.interner.resolve(sym)
    }

    pub fn fn_decl(&self, item: usize) -> Option<&FnDecl> {
        match &self.items.get(item)?.kind {
            ItemKind::Fn(decl) => Some(decl),
            _ => None,
        }
    }

    /// Method `method` of the `impl` block at `item`.
    pub fn method_decl(&self, item: usize, method: usize) -> Option<&FnDecl> {
        match &self.items.get(item)?.kind {
            ItemKind::Impl(decl) => Some(&decl.methods.get(method)?.decl),
            _ => None,
        }
    }

    pub fn record_decl(&self, item: usize) -> Option<&RecordDecl> {
        match &self.items.get(item)?.kind {
            ItemKind::Record(decl) => Some(decl),
            _ => None,
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
            ItemKind::Record(decl) => Some(decl.name),
            ItemKind::Enum(decl) => Some(decl.name),
            ItemKind::Interface(decl) => Some(decl.name),
            ItemKind::Use(_) | ItemKind::Impl(_) | ItemKind::Example(_) => None,
        }
    }
}

pub enum ItemKind {
    Fn(FnDecl),
    Use(UseDecl),
    Record(RecordDecl),
    Enum(EnumDecl),
    Impl(ImplDecl),
    Interface(InterfaceDecl),
    /// `example f(…) == v` or `example f(…) fails P`, run by `proviso test` (REFERENCE §14).
    Example(ExampleDecl),
}

pub struct ExampleDecl {
    pub call: ExprId,
    pub expect: Expectation,
}

/// What an example asserts about its call.
pub enum Expectation {
    /// `== v`: the call succeeds with a value equal to `v`.
    Equals(ExprId),
    /// `fails P`: the call fails with an error that matches `P`.
    Fails(PatId),
}

pub struct FnDecl {
    pub name: Ident,
    /// `[T: Ord + Copy, U]` (REFERENCE §4.8).
    pub generics: Vec<GenericParam>,
    /// A method's `self`, which comes before its other parameters (REFERENCE §5.2).
    pub receiver: Option<Receiver>,
    pub params: Vec<Param>,
    pub ret: Option<TypeId>,
    pub fails: Option<TypeId>,
    /// `None` for an interface's method, which has no body (Q13).
    pub body: Option<Block>,
    /// The body needed error recovery, so its control flow is unknown.
    pub recovered: bool,
}

/// `T: Ord + Copy`, a type parameter and the interfaces it must implement.
pub struct GenericParam {
    pub name: Ident,
    pub bounds: Vec<Ident>,
}

/// `self`, `inout self` or `take self`.
#[derive(Clone, Copy, Debug)]
pub struct Receiver {
    pub mode: ParamMode,
    pub span: Span,
}

/// `impl Span { … }` or `impl Show for Span { … }` (REFERENCE §3, §4.9).
pub struct ImplDecl {
    /// The interface it implements, or `None` for the type's own methods.
    pub iface: Option<Ident>,
    pub target: TypeId,
    pub methods: Vec<Method>,
    /// A method failed to parse, so one the block meant to have may be missing.
    pub recovered: bool,
}

/// A method or associated function of an `impl` block.
pub struct Method {
    pub vis: Visibility,
    pub decl: FnDecl,
    pub span: Span,
}

/// `interface Show { fn show(self) -> Text }` (REFERENCE §4.9).
pub struct InterfaceDecl {
    pub name: Ident,
    pub methods: Vec<FnDecl>,
    /// A method's declaration was rejected, so implementations may have methods it doesn't
    /// list, and calls of them aren't reported.
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

/// `record Span derives(Eq) { lo: Int, hi: Int } where lo <= hi` (REFERENCE §4.4).
pub struct RecordDecl {
    pub name: Ident,
    /// Declared `unique record`, so its values move instead of being copied (REFERENCE §5.1).
    pub unique: bool,
    /// Declared `resource record`, a base resource whose values must be consumed (§10).
    pub resource: bool,
    /// The interfaces named in `derives(…)`, which the checker resolves.
    pub derives: Vec<Ident>,
    pub fields: Vec<FieldDecl>,
    /// The record-level `where` predicate, which sees every field.
    pub refinement: Option<ExprId>,
}

/// `enum Shape derives(Show) { Circle(radius: Float), Empty }` (REFERENCE §4.5).
pub struct EnumDecl {
    pub name: Ident,
    pub derives: Vec<Ident>,
    pub variants: Vec<VariantDecl>,
}

/// `Rect(w: Int, h: Int)`, or `Empty` with no fields.
pub struct VariantDecl {
    pub name: Ident,
    pub fields: Vec<FieldDecl>,
}

/// `name: Text where not name.is_empty()`
pub struct FieldDecl {
    pub name: Ident,
    pub ty: TypeId,
    /// The field's `where` predicate, which sees only this field.
    pub refinement: Option<ExprId>,
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
    /// `Option[Int]` or `Float[m]`. The arguments of a numeric type are units, which are
    /// skipped until units exist, so they are `None`.
    Applied { name: Ident, args: Option<Vec<TypeId>> },
    /// `Self`, the type of an `impl` block, or the implementing type in an interface.
    SelfType,
    /// `(A, B)`, with at least two elements.
    Tuple(Vec<TypeId>),
}

pub struct Block {
    pub stmts: Vec<StmtId>,
    pub span: Span,
    /// The block was never closed, so the code that ended it is missing.
    pub unclosed: bool,
    /// A statement in it failed to parse, so part of it is missing, perhaps the end.
    pub lost: bool,
}

pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

pub enum StmtKind {
    /// `let pattern: T = init`. A `var` makes each name the pattern binds mutable.
    Let {
        mutable: bool,
        pat: PatId,
        ty: Option<TypeId>,
        init: ExprId,
    },
    Assign {
        target: ExprId,
        op: AssignOp,
        value: ExprId,
    },
    Expr(ExprId),
    Return(Option<ExprId>),
    Break(Option<Ident>),
    Continue(Option<Ident>),
    Assert(ExprId),
    /// `check cond else fallback`, whose fallback must leave (REFERENCE §8.4).
    Check {
        cond: ExprId,
        fallback: Fallback,
    },
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
        /// Explicit type arguments, as in `max::[Int](a: 1, b: 2)` (REFERENCE §4.8).
        targs: Option<Vec<TypeId>>,
        args: Vec<Arg>,
    },
    MethodCall {
        receiver: ExprId,
        method: Ident,
        targs: Option<Vec<TypeId>>,
        args: Vec<Arg>,
    },
    Field {
        base: ExprId,
        name: Ident,
    },
    /// `xs[i]`, which reads element `i` of a list (STD.md).
    Index {
        base: ExprId,
        index: ExprId,
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
    /// `attempt f(…)`, which reifies the outcome of the calls in the chain as a `Result`
    /// (REFERENCE §7.2).
    Attempt(ExprId),
    /// `fail e`, which exits the function with error `e` (REFERENCE §7.1).
    Fail(ExprId),
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
    /// `for pat in iter`, whose pattern matches every element, or `for pat in take iter`,
    /// which consumes the collection element by element (REFERENCE §6.5).
    For {
        label: Option<Ident>,
        pat: PatId,
        iter: ExprId,
        consume: bool,
        body: Block,
    },
    Todo(Option<String>),
    Unreachable,
    Debug(Vec<ExprId>),
    /// `match scrutinee { arms }` (REFERENCE §6.3).
    Match {
        scrutinee: ExprId,
        arms: Vec<Arm>,
        /// False when an arm failed to parse or the braces were never closed, so the arms
        /// that would have made it exhaustive may be missing.
        complete: bool,
    },
    /// `value is pattern` (REFERENCE §6.4).
    Is {
        value: ExprId,
        pat: PatId,
    },
    /// `(a, b)`, with at least two elements.
    Tuple(Vec<ExprId>),
    /// `[a, b]`, a list literal, or `[]` (REFERENCE §2).
    List(Vec<ExprId>),
    /// `["k": v]`, a map literal, or `[:]` with no entries (REFERENCE §2).
    Map(Vec<(ExprId, ExprId)>),
    /// `value else fallback`, which unwraps an `Option` or handles the failure of the calls
    /// in `value`'s chain (REFERENCE §6.6).
    Else {
        value: ExprId,
        fallback: Fallback,
    },
    /// `it`, the error in the fallback of an `else` form (Q33).
    It,
    /// Stands in for code that failed to parse, which is already reported.
    Error,
}

/// What an `else` form or a `check` falls back to: a value, or a block.
pub enum Fallback {
    Value(ExprId),
    Block(Block),
}

/// `pattern if guard => body`. A body written without braces is one statement.
pub struct Arm {
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: Block,
}

pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

/// The patterns of REFERENCE §6.4.
pub enum PatKind {
    /// `_`
    Wild,
    /// A snake_case name, which binds the value.
    Bind(Ident),
    /// A literal, possibly negated, such as `-1`, `'a'` or `"ada"`. It is an expression so
    /// that the checker types it as it types any literal.
    Lit(ExprId),
    /// `lo..hi` or `lo..=hi`, with literal bounds.
    Range { lo: ExprId, hi: ExprId, inclusive: bool },
    /// A variant or record: `Empty`, `Shape.Circle(r)`, `Rect(w: width, ..)`.
    Ctor {
        qualifier: Option<Ident>,
        name: Ident,
        /// `None` when written without parentheses.
        fields: Option<Vec<FieldPat>>,
        /// Ends with `..`, which skips the remaining fields.
        rest: bool,
    },
    /// `(a, b)`, with at least two elements.
    Tuple(Vec<PatId>),
}

/// One field of a constructor pattern: `w`, `w: width` or a pattern with no label.
pub struct FieldPat {
    pub label: Option<Ident>,
    pub pat: PatId,
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
