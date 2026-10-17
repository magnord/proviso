//! Name resolution and type checking for the phase-1 subset (scalar types, functions,
//! control flow, `fails` and `try`, and the prelude's `System` with only `stdout`), for
//! records, for enums, `match` and patterns, for `Option`, `Result`, `fail` and `attempt`,
//! for methods, interfaces and generic functions, and for tuples, `let` patterns, the `else`
//! forms, `check`, the text operations and `example` declarations.
//!
//! The checker never rewrites the tree. It records what it learns in side tables of
//! [`Program`], which the interpreter reads.

pub mod decls;
pub mod exhaust;
pub mod infer;
pub mod types;

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use proviso_syntax::arena::SideTable;
use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, Planned, codes};
use proviso_syntax::intern::Symbol;
use proviso_syntax::source::Span;

use crate::decls::{
    AdtDef, AdtId, AdtKind, Decls, FieldDef, FieldIdx, IfaceDef, IfaceId, IfaceMethod, ImplDef, ImplKey, Inhabited,
    Pred, VariantDef, VariantIdx,
};
use crate::exhaust::{Ctor, Space};
use crate::infer::{Kind, Origin, Vars};
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
    /// `Text.byte_len() -> Int`
    ByteLen,
    /// `Text.is_empty() -> Bool`
    IsEmpty,
    /// `Text.trim() -> Text`
    Trim,
    /// `Text.split_once(sep: Text) -> Option[(Text, Text)]`
    SplitOnce,
    /// `Text.starts_with(prefix: Text) -> Bool`
    StartsWith,
    /// `Text.strip_prefix(prefix: Text) -> Option[Text]`
    StripPrefix,
    /// `Int.parse(text: Text) -> Int fails ParseError`, and the same for each integer type.
    /// It is called on the type, so it has no receiver.
    Parse(IntTy),
}

/// What a name, call or member access resolved to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Res {
    Local(LocalId),
    Fn(FnId),
    Method(Builtin),
    /// `base.name` on a record.
    Field(FieldIdx),
    /// A record's constructor, called as in `Span(lo: 1, hi: 4)`, or an enum's variant, as
    /// in `Shape.Circle(radius: 2)` or `Shape.Empty`.
    Ctor(AdtId, VariantIdx),
    /// `r.with(...)`. The fields it replaces are in `Program::with_fields`.
    With,
    /// A method of interface `iface`, which the implementation for the receiver's type runs
    /// (REFERENCE §4.9). Written `I.f(x)`, it is `qualified`, and its first argument is the
    /// receiver.
    Dispatch {
        iface: IfaceId,
        method: usize,
        qualified: bool,
    },
}

pub struct FnInfo {
    /// Index of the declaring item in `Module::items`.
    pub item: usize,
    /// The method's index in the `impl` block at `item`, or `None` for a module's function.
    pub method: Option<usize>,
    pub name: Symbol,
    /// The type parameters, which its types write as `Ty::Param(i)` (REFERENCE §4.8).
    pub generics: Vec<GenericInfo>,
    /// The type of `self`, which is local 0, for a method; `None` for a function or an
    /// associated function.
    pub receiver: Option<Ty>,
    /// The type of the `impl` block that declares it, which `Self` names there.
    pub owner: Option<Ty>,
    pub params: Vec<ParamInfo>,
    pub ret: Ty,
    pub fails: Option<Ty>,
    /// Number of local slots, `self` and the parameters first.
    pub locals: usize,
    /// Its declaration was rejected, so its body isn't checked and its calls aren't reported
    /// (REFERENCE §15.1).
    pub rejected: bool,
}

/// Why an `impl` block's interface was rejected: `unknown` when the block may have given its
/// type methods and interfaces, and `bodies` when its methods are still checked (§15.1).
#[derive(Clone, Copy)]
struct Rejected {
    unknown: bool,
    bodies: bool,
}

/// A type parameter.
pub struct GenericInfo {
    /// How diagnostics write it: its name, or for a parameter of interface type such as
    /// `x: Show`, `type of x`.
    pub name: Box<str>,
    /// The name the signature and body use for it. `None` for a parameter declared twice,
    /// and for the one an interface type stands for, which nothing can name.
    pub sym: Option<Symbol>,
    /// For the type parameter that a parameter of interface type stands for (REFERENCE
    /// §4.9), that parameter's name. `::[…]` gives only the others.
    pub param: Option<Symbol>,
    /// The interfaces its argument must implement.
    pub bounds: Vec<IfaceId>,
    /// The declaration or a constraint was rejected, so it stands for an unknown type.
    pub rejected: bool,
}

pub struct ParamInfo {
    pub name: Symbol,
    pub ty: Ty,
    pub mode: ParamMode,
}

/// A constructor pattern: the variant it matches, and the field each of its parts matches,
/// in the order written.
pub struct CtorPat {
    pub adt: AdtId,
    pub variant: VariantIdx,
    pub fields: Box<[FieldIdx]>,
}

/// What the checker learned about a module.
#[derive(Default)]
pub struct Program {
    pub decls: Decls,
    pub fns: Vec<FnInfo>,
    pub main: Option<FnId>,
    pub expr_ty: SideTable<Expr, Ty>,
    pub res: SideTable<Expr, Res>,
    /// The fields each `with` replaces, in the order of its arguments.
    pub with_fields: SideTable<Expr, Box<[FieldIdx]>>,
    /// The local each binding pattern binds.
    pub pat_local: SideTable<Pat, LocalId>,
    /// What each constructor pattern matches.
    pub pat_ctor: SideTable<Pat, CtorPat>,
    pub for_local: SideTable<Expr, LocalId>,
    /// The loop each `break` or `continue` leaves.
    pub jump_target: SideTable<Stmt, ExprId>,
    /// What handles the failure of each fallible call that is marked other than by `try`:
    /// the `attempt`, which reifies it as an `Err` (REFERENCE §7.2), the `else` form, which
    /// runs its fallback (§6.6), or the call of an `example`, which reports it (§14).
    pub handler_of: SideTable<Expr, ExprId>,
    /// The local that holds `it` in the fallback of each `else` form on a call that can
    /// fail. An `else` form without one unwraps an `Option`.
    pub it_local: SideTable<Expr, LocalId>,
    /// The module's examples, in declaration order.
    pub examples: Vec<ExampleInfo>,
}

/// An `example` declaration (REFERENCE §14).
pub struct ExampleInfo {
    /// Index of the declaring item in `Module::items`.
    pub item: usize,
    /// Number of local slots its expressions need.
    pub locals: usize,
}

static ERROR: Ty = Ty::Error;

impl Program {
    pub fn ty(&self, e: ExprId) -> &Ty {
        self.expr_ty.get(e).unwrap_or(&ERROR)
    }

    pub fn res(&self, e: ExprId) -> Option<Res> {
        self.res.get(e).copied()
    }

    /// The declaration of function `f`: an item, or a method of an `impl` block.
    pub fn decl<'m>(&self, m: &'m Module, f: FnId) -> &'m FnDecl {
        let info = &self.fns[f];
        let decl = match info.method {
            Some(method) => m.method_decl(info.item, method),
            None => m.fn_decl(info.item),
        };
        decl.expect("functions are declared by `fn` items and `impl` blocks")
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
        adt_names: HashMap::new(),
        poisoned: m.poisoned.clone(),
        adts: Vec::new(),
        iface_names: HashMap::new(),
        ifaces: Vec::new(),
        inherent: HashMap::new(),
        unknown_tys: Vec::new(),
        f: FnState::new(Ty::Unit, None),
        in_chain: false,
        markers: Vec::new(),
        inhabited: None,
        self_ty: None,
        generic_scope: Vec::new(),
        param_names: Vec::new(),
        copying: false,
        tail_copying: false,
        pattern_borrowed: false,
        pattern_mutable: false,
        let_pattern: false,
        its: Vec::new(),
        option_fallbacks: 0,
        borrowed_values: HashSet::new(),
        vars: Vars::default(),
        pending: Vec::new(),
        stmt_start: (0, 0),
        typed: Vec::new(),
    };
    checker.imports();
    checker.adt_names();
    checker.iface_names();
    checker.unknown_impl_targets();
    checker.adt_fields();
    checker.inhabited = Some(checker.p.decls.inhabited());
    checker.iface_methods();
    checker.adt_derives();
    checker.signatures();
    checker.impls();
    checker.collisions();
    checker.derived_fields();
    checker.adt_predicates();
    checker.check_main();
    for id in 0..checker.p.fns.len() {
        checker.body(id);
    }
    checker.examples();
    debug_assert!(!checker.p.expr_ty.values().any(holds_var), "an inference variable was left in `expr_ty`");
    checker.p
}

/// Whether `ty` has an inference variable in it, which [`Program`] never does.
fn holds_var(ty: &Ty) -> bool {
    match ty {
        Ty::Var(_) => true,
        Ty::Adt(_, args) => args.iter().any(holds_var),
        _ => false,
    }
}

#[derive(Clone)]
enum Import {
    Type(Ty),
    /// `use a.b` makes `b` usable as a qualifier.
    Module,
}

/// A record or enum declaration, with the parts the checker reads the same way for both.
struct AdtSrc<'a> {
    id: AdtId,
    name: Ident,
    vis: Visibility,
    derives: &'a [Ident],
    /// The variants the declaration keeps, in order: a record's one, named like it, or the
    /// first of each name in an enum.
    variants: Vec<(Ident, &'a [FieldDecl])>,
    /// A record's record-level `where`.
    refinement: Option<ExprId>,
}

struct Local {
    ty: Ty,
    mutable: bool,
    /// A parameter, or a part of one bound by a pattern, which the function borrows, so
    /// copying it needs `Copy` (REFERENCE §4.8).
    borrowed: bool,
}

/// A module interface's declaration.
#[derive(Clone, Copy)]
struct IfaceSrc<'a> {
    id: IfaceId,
    decl: &'a InterfaceDecl,
    vis: Visibility,
}

/// A method or associated function of a record or enum, from an `impl` block of its own.
struct Inherent {
    name: Symbol,
    f: FnId,
    /// Declared twice, or named like a method of an interface the type implements. Calls of
    /// the name don't resolve to it (REFERENCE §3).
    rejected: bool,
}

/// What a method call resolves to.
#[derive(Clone, Copy)]
enum Callee {
    Fn(FnId),
    Iface(IfaceId, usize),
}

/// A function's signature, as [`Checker::signature`] resolves it.
struct Signature {
    generics: Vec<GenericInfo>,
    receiver: Option<Ty>,
    params: Vec<ParamInfo>,
    ret: Ty,
    fails: Option<Ty>,
    rejected: bool,
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
    /// False in a refinement or an example, which are expressions with no function to return
    /// from or fail.
    returns: bool,
    /// Set in an example, so diagnostics name it.
    example: bool,
    /// The interfaces each of the function's type parameters implements.
    bounds: Vec<Vec<IfaceId>>,
    /// For each type parameter that a parameter of interface type stands for, that
    /// parameter's name and the interface, which diagnostics suggest a declaration with.
    anonymous: Vec<Option<(Box<str>, Box<str>)>>,
}

impl FnState {
    fn new(ret: Ty, fails: Option<Ty>) -> FnState {
        FnState {
            ret,
            fails,
            scopes: Vec::new(),
            locals: Vec::new(),
            loops: Vec::new(),
            returns: true,
            example: false,
            bounds: Vec::new(),
            anonymous: Vec::new(),
        }
    }
}

/// An enclosing `try`, `attempt`, `else` form or example, and the error types of the
/// fallible calls it marks.
struct Marker {
    /// What handles their failure (see [`Program::handler_of`]), or `None` for a `try`.
    handler: Option<ExprId>,
    errors: Vec<Ty>,
}

/// Whether an `if` is used for its value, as a statement, or as the last statement of a
/// function that returns this type.
#[derive(Clone, Copy)]
enum Mode<'t> {
    Stmt,
    Value(Option<&'t Ty>),
    Tail(&'t Ty),
}

/// Whether code always leaves (REFERENCE §6.6; OPEN_QUESTIONS P5, `check`). It `Waits` on an open variable that the
/// expression around it still gives, such as the error type of `it` in a fallback, and
/// leaves if that settles as `Never` (OPEN_QUESTIONS P5; issue #30).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Flow {
    Leaves,
    Finishes,
    Waits(u32),
}

/// The fields of `System` that phase 3 adds (REFERENCE §9.1).
const LATER_SYSTEM_FIELDS: &[&str] = &["fs", "net", "clock", "random", "env", "stdin", "stderr", "process"];

struct Checker<'a> {
    m: &'a Module,
    opts: Options,
    diags: &'a mut Diagnostics,
    p: Program,
    fn_names: HashMap<Symbol, FnId>,
    imports: HashMap<Symbol, Import>,
    /// The module's records and enums.
    adt_names: HashMap<Symbol, AdtId>,
    /// Names whose declarations were rejected, so their uses aren't reported again: those the
    /// parser rejected, and records and enums whose names the checker rejects.
    poisoned: HashSet<Symbol>,
    /// Every record and enum declaration, including those whose name is rejected.
    adts: Vec<AdtSrc<'a>>,
    /// The function being checked, or the record whose refinements are.
    f: FnState,
    /// Set while checking the postfix chain a `try` or `attempt` covers (REFERENCE §6.1).
    in_chain: bool,
    /// The enclosing `try` and `attempt` markers, innermost last.
    markers: Vec<Marker>,
    /// Which types have values (see [`Decls::inhabited`]), once every declaration is known.
    inhabited: Option<Inhabited>,
    /// The module's interfaces.
    iface_names: HashMap<Symbol, IfaceId>,
    ifaces: Vec<IfaceSrc<'a>>,
    /// The methods and associated functions of each record and enum, in declaration order.
    inherent: HashMap<AdtId, Vec<Inherent>>,
    /// Types without an [`ImplKey`], such as `Never` and `Out`, that a rejected `impl` block
    /// is for. They may have methods and interfaces that nothing records (REFERENCE §15.1).
    unknown_tys: Vec<Ty>,
    /// What `Self` means here: the type of an `impl` block, or `Param(0)` in an interface.
    self_ty: Option<Ty>,
    /// The type parameters in scope, by name, with their indices; `None` for one whose
    /// constraint is rejected, which stands for an unknown type.
    generic_scope: Vec<(Symbol, Option<u32>)>,
    /// How diagnostics write each type parameter in scope.
    param_names: Vec<Box<str>>,
    /// Set while checking an expression whose value is copied: bound to a name, stored in a
    /// value or returned (REFERENCE §4.8).
    copying: bool,
    /// [`Checker::copying`], handed from an `if` or `match` to the values of its branches.
    tail_copying: bool,
    /// Set while checking a pattern that matches a borrowed value, so its bindings are too.
    pattern_borrowed: bool,
    /// Set while checking the pattern of a `var`, whose bindings are mutable.
    pattern_mutable: bool,
    /// Set while checking the pattern of a `let`, which must match every value, so a literal
    /// it holds covers only some even where a `match` counts it as `_`.
    let_pattern: bool,
    /// The `it` of each enclosing fallback of an `else` form on a call that can fail,
    /// innermost last (Q33).
    its: Vec<LocalId>,
    /// How many fallbacks of `else` forms on an `Option` enclose the expression, where `it`
    /// would be an `Option`'s, which has no error.
    option_fallbacks: u32,
    /// The `if` and `match` expressions whose value may be a borrowed value, because a
    /// branch's value may be.
    borrowed_values: HashSet<ExprId>,
    /// The inference variables of the body being checked (OPEN_QUESTIONS P5; issue #10).
    vars: Vars,
    /// Checks that wait until the variables they read are solved.
    pending: Vec<Pending>,
    /// Where the statement being checked began: the variable count and the trail mark that
    /// [`Checker::solve`] takes.
    stmt_start: (u32, usize),
    /// The expressions whose recorded type has a variable, which the side table gets
    /// without once the body is checked.
    typed: Vec<ExprId>,
}

/// A check on a type with a variable in it, made once the statement has solved it.
enum Pending {
    /// An integer literal of `magnitude`, negated or not, that must fit its type.
    Int { ty: Ty, magnitude: u128, negative: bool, span: Span },
    /// A float literal that must be finite in its type.
    Float { ty: Ty, lit: ExprId },
    /// A type argument of a call of `callee` that must implement each of `ifaces`, which the
    /// callee's parameter `param` is constrained by. The first it misses is reported.
    Bound { ty: Ty, ifaces: Vec<IfaceId>, callee: Box<str>, param: Box<str>, span: Span },
    /// The operand of unary `-`, which must be a signed integer or a float.
    Neg { ty: Ty, span: Span },
    /// The operands of arithmetic operator `op`.
    Arith { op: BinOp, ty: Ty, span: Span },
    /// A call of `callee` that can fail with `ty` but has no marker, which is reported with
    /// the error type the statement settles (E0701).
    Unmarked { ty: Ty, callee: Box<str>, span: Span },
    /// A `try` that propagates `errs` where there is no `fails` to take them (E0702). Its
    /// chain was `rejected` when its value has an error.
    Try { errs: Vec<Ty>, rejected: bool, span: Span },
    /// An `attempt` or `else` form whose calls fail with `err`, which must not settle as
    /// `Never` (E0706, E0707; OPEN_QUESTIONS P5, `fails Never`). An example's error type is
    /// settled where it is checked.
    CanFail { err: Ty, handler: Handler, span: Span },
    /// Code that leaves if `ty` does, which must not finish: the fallback of a `check`
    /// (E0415), or a block that ends without the value it is `expected` to give (E0301).
    Leaves { ty: Ty, must: Must },
}

/// Code that must not finish, and what reports it if it can.
enum Must {
    Check(Span),
    Value { expected: Ty, span: Span },
}

/// What handles the failure of the calls it marks, other than `try`.
#[derive(Clone, Copy)]
enum Handler {
    Attempt,
    Else,
    Example,
}

impl Pending {
    /// The types whose variables the check waits on.
    fn tys(&self) -> &[Ty] {
        match self {
            Pending::Int { ty, .. }
            | Pending::Float { ty, .. }
            | Pending::Bound { ty, .. }
            | Pending::Neg { ty, .. }
            | Pending::Arith { ty, .. }
            | Pending::Unmarked { ty, .. }
            | Pending::Leaves { ty, .. }
            | Pending::CanFail { err: ty, .. } => std::slice::from_ref(ty),
            Pending::Try { errs, .. } => errs,
        }
    }
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

    /// How diagnostics write `ty`. A literal's type that nothing has settled yet is written
    /// as its default, and a type argument that nothing has given yet as `_` (issue #22).
    fn show(&self, ty: &Ty) -> String {
        self.p.decls.display_in(&self.vars.defaulted(ty), &self.param_names).to_string()
    }

    /// Whether `ty` implements `iface`, where a type parameter implements its constraints.
    fn implements(&self, ty: &Ty, iface: IfaceId) -> bool {
        let ty = self.vars.defaulted(ty);
        self.p.decls.implements(&ty, iface, &self.f.bounds) || self.unknown_tys.contains(&ty)
    }

    /// Whether a rejected declaration may have given `ty` interfaces that nothing records.
    fn unknown_interfaces(&self, ty: &Ty) -> bool {
        let ty = self.vars.resolve(ty);
        self.p.decls.unknown_interfaces(&ty) || self.unknown_tys.contains(&ty)
    }

    // ---- inference variables (OPEN_QUESTIONS P5; issue #10) ----

    /// Settles the open variables made since `vars`, and runs the checks queued since
    /// `pending`, which wait on them. An integer literal's variable becomes `Int`, a float
    /// literal's `Float` (REFERENCE §2), and one that only `Never` reached `Never` (OPEN_QUESTIONS P5). Any other
    /// is a type argument that nothing gave, which [`Checker::settle_vars`] reports once.
    ///
    /// A variable that an older one was bound to a type with, such as a `None` met with `it`
    /// in a fallback's statement, belongs to the expression around the statement, which
    /// solves it. A check that waits on an open variable waits for that solve too.
    fn solve(&mut self, vars: u32, pending: usize, bound: usize) {
        let outer = self.vars.outer(vars, bound);
        let open: Vec<u32> =
            (vars..self.vars.count()).filter(|&v| self.vars.root(v) == v && !outer.contains(&v)).collect();
        self.settle_vars(open);
        let checks = self.pending.split_off(pending.min(self.pending.len()));
        for check in checks {
            if check.tys().iter().any(|ty| self.vars.has_open(ty)) {
                self.pending.push(check);
            } else {
                self.run_pending(check);
            }
        }
    }

    /// Settles the open variables in `ty` as [`Checker::solve`] does, where its type must be
    /// known now: a binding's, a receiver's, or what a pattern or `Show` reads.
    fn force(&mut self, ty: &Ty) -> Ty {
        let mut open = Vec::new();
        self.vars.open_in(ty, &mut open);
        self.settle_vars(open);
        self.vars.zonk(ty)
    }

    /// Reports the fallback of a `check`, of type `ty`, if it can finish (E0415). An error
    /// counts as leaving, since it was reported where it went wrong. A value built from
    /// parts, such as `Some(it)`, finishes whatever its parts are (issue #30).
    fn check_leaves(&mut self, ty: &Ty, span: Span) {
        if self.flow(ty) != Flow::Leaves {
            self.error(
                codes::CHECK_FALLS_THROUGH,
                span,
                "the `else` of a `check` must not finish; use `fail`, or a block that returns, breaks or continues",
            );
        }
    }

    /// Settles the open variables in `ty` that the statement being checked made, as its end
    /// would, so a type argument that only `Never` gave is `Never` when it is asked whether
    /// the statement can finish. Those the expression around the statement may still give
    /// stay open, such as the error type of `it`, which the `let` around a fallback settles
    /// (OPEN_QUESTIONS P5). A statement whose type is one waits for it (issue #30).
    fn settle_own(&mut self, ty: &Ty) -> Ty {
        if !self.vars.has_var(ty) {
            return ty.clone();
        }
        let (since, mark) = self.stmt_start;
        let outer = self.vars.outer(since, mark);
        let mut open = Vec::new();
        self.vars.open_in(ty, &mut open);
        open.retain(|&v| v >= since && !outer.contains(&v));
        self.settle_vars(open);
        self.vars.zonk(ty)
    }

    /// Whether code of type `ty` leaves. An error counts as leaving, since it was reported
    /// where it went wrong, and a variable that is still open waits.
    fn flow(&self, ty: &Ty) -> Flow {
        match self.vars.resolve(ty) {
            Ty::Never | Ty::Error => Flow::Leaves,
            Ty::Var(v) => Flow::Waits(self.vars.root(v)),
            _ => Flow::Finishes,
        }
    }

    /// `flow` with the variable it waits on as it is now.
    fn now(&self, flow: Flow) -> Flow {
        match flow {
            Flow::Waits(v) => self.flow(&Ty::Var(v)),
            flow => flow,
        }
    }

    /// The flow of `a` followed by `b`, which leaves if either does. Code that waits on two
    /// variables counts as finishing, which at worst reports a block that leaves.
    fn then(&self, a: Flow, b: Flow) -> Flow {
        match (self.now(a), self.now(b)) {
            (Flow::Leaves, _) | (_, Flow::Leaves) => Flow::Leaves,
            (Flow::Finishes, flow) | (flow, Flow::Finishes) => flow,
            (Flow::Waits(a), Flow::Waits(b)) if a == b => Flow::Waits(a),
            _ => Flow::Finishes,
        }
    }

    /// The type of branches of types `a` and `b` whose values are unused, which leave only
    /// if both do. Only `Never` counts as leaving here, not an error.
    fn branches(&self, a: &Ty, b: &Ty) -> Ty {
        let flow = |ty: &Ty| match self.vars.resolve(ty) {
            Ty::Never => Flow::Leaves,
            Ty::Var(v) => Flow::Waits(self.vars.root(v)),
            _ => Flow::Finishes,
        };
        match (flow(a), flow(b)) {
            (Flow::Leaves, Flow::Leaves) => Ty::Never,
            (Flow::Leaves, Flow::Waits(v)) | (Flow::Waits(v), Flow::Leaves) => Ty::Var(v),
            (Flow::Waits(x), Flow::Waits(y)) if x == y => Ty::Var(x),
            _ => Ty::Unit,
        }
    }

    /// The statements of a block, checked in order.
    fn stmts(&mut self, stmts: &[StmtId]) -> Flow {
        let mut flow = Flow::Finishes;
        for &s in stmts {
            let next = self.stmt(s);
            flow = self.then(flow, next);
        }
        self.now(flow)
    }

    /// Whether a value of type `expected` may be `()`: it is `Unit`, an error, or a variable
    /// that isn't a literal's.
    fn takes_unit(&self, expected: &Ty) -> bool {
        match self.vars.resolve(expected) {
            Ty::Unit | Ty::Error => true,
            Ty::Var(v) => self.vars.open(v).is_some_and(|open| open.kind == Kind::Any),
            _ => false,
        }
    }

    /// Reports a block that ends without the value of type `expected` it must give.
    fn ends_without_value(&mut self, expected: &Ty, span: Span) {
        self.error(
            codes::TYPE_MISMATCH,
            span,
            format!("expected a value of type `{}`, but this block ends without one", self.show(expected)),
        );
    }

    /// Settles `vars` as their defaults, or as errors where nothing gave them a type.
    ///
    /// Which error stands for a type argument that nothing gave, so each mistake is reported
    /// once (REFERENCE §15.1; issue #20):
    /// - One a rejected value was to give (quiet) is that value's error, never E0312. It is
    ///   not `Never`, even where a `Never` reached it too, since the value may have been of
    ///   any type (issue #30).
    /// - One a `todo` hole met is `Never`, as the hole is (Q25).
    /// - The error type of a call without a marker (unmarked) is that call's E0701, unless a
    ///   `try` with no `fails` to take it also needs it (owed). Then it is E0312.
    /// - Any other is E0312.
    ///
    /// A `try` with no `fails` to take its error then reports each error type the statement
    /// settles in [`Checker::try_without_fails`].
    fn settle_vars(&mut self, vars: Vec<u32>) {
        let mut unknown: Vec<Origin> = Vec::new();
        for v in vars {
            let Some(open) = self.vars.open(v).cloned() else { continue };
            if open.hole && !open.quiet {
                self.vars.settled_hole(v);
            }
            let ty = match open.kind {
                Kind::Int => Ty::INT,
                Kind::Float => Ty::Float(FloatTy::F64),
                Kind::Any if open.quiet => Ty::Error,
                Kind::Any if open.never || open.hole => Ty::Never,
                Kind::Any if open.unmarked && !open.owed => Ty::Error,
                Kind::Any => {
                    unknown.push(open.origin);
                    Ty::Error
                }
            };
            self.vars.settle(v, ty);
        }
        // The type arguments of one variant or call that nothing gave make one error.
        let mut reported: Vec<Span> = Vec::new();
        for origin in &unknown {
            let message = match *origin {
                Origin::Variant { span, .. } | Origin::Call { span, .. } if reported.contains(&span) => continue,
                Origin::Variant { adt, span } => {
                    let name = self.p.decls.adt(adt).name.clone();
                    let count =
                        unknown.iter().filter(|o| matches!(o, Origin::Variant { span: s, .. } if *s == span)).count();
                    let noun = if count == 1 { "type argument" } else { "type arguments" };
                    reported.push(span);
                    (
                        span,
                        format!(
                            "the {noun} of this `{name}` can't be inferred; give the binding a type, such as `{}`",
                            example_type(&name)
                        ),
                    )
                }
                Origin::Call { f, span, .. } => {
                    let info = &self.p.fns[f];
                    let name = self.m.text(info.name);
                    let missing: Vec<String> = (unknown.iter())
                        .filter_map(|o| match o {
                            Origin::Call { param, span: s, .. } if *s == span => {
                                Some(format!("`{}`", info.generics[*param].name))
                            }
                            _ => None,
                        })
                        .collect();
                    let noun = if missing.len() == 1 { "type argument" } else { "type arguments" };
                    reported.push(span);
                    (
                        span,
                        format!(
                            "the {noun} {} of `{name}` can't be inferred; give the binding a type, or write `{name}::[…](…)`",
                            missing.join(", ")
                        ),
                    )
                }
                Origin::Defaulted => continue,
            };
            self.error(codes::CANNOT_INFER, message.0, message.1);
        }
    }

    fn run_pending(&mut self, check: Pending) {
        match check {
            Pending::Int { ty, magnitude, negative, span } => {
                if let Ty::Int(it) = self.vars.zonk(&ty) {
                    self.int_range(it, magnitude, negative, span);
                }
            }
            Pending::Float { ty, lit } => {
                if let (Ty::Float(ft), ExprKind::Float(text)) = (self.vars.zonk(&ty), &self.m.exprs[lit].kind)
                    && !ft.holds(text)
                {
                    let span = self.span(lit);
                    self.error(codes::LITERAL_OUT_OF_RANGE, span, format!("`{text}` is too large for `{}`", ft.name()));
                }
            }
            Pending::Bound { ty, ifaces, callee, param, span } => {
                let ty = self.vars.zonk(&ty);
                if ty.is_unknown() || self.vars.has_open(&ty) {
                    return;
                }
                if let Some(&iface) = ifaces.iter().find(|&&iface| !self.implements(&ty, iface)) {
                    let message = format!(
                        "`{}` does not implement `{}`, which `{callee}` needs of `{param}`",
                        self.show(&ty),
                        self.iface_name(iface)
                    );
                    self.error(codes::MISSING_IMPLEMENTATION, span, message);
                }
            }
            Pending::Neg { ty, span } => {
                let ty = self.vars.zonk(&ty);
                self.negated(&ty, span);
            }
            Pending::Arith { op, ty, span } => {
                let ty = self.vars.zonk(&ty);
                self.arithmetic(op, &ty, span);
            }
            Pending::Unmarked { ty, callee, span } => {
                let ty = self.vars.zonk(&ty);
                self.unmarked(&callee, &ty, span);
            }
            Pending::Try { errs, rejected, span } => self.try_without_fails(errs, rejected, span),
            Pending::CanFail { err, handler, span } => self.can_fail(&err, handler, span),
            Pending::Leaves { ty, must: Must::Check(span) } => self.check_leaves(&ty, span),
            Pending::Leaves { ty, must: Must::Value { expected, span } } => {
                if self.flow(&ty) != Flow::Leaves {
                    self.ends_without_value(&expected, span);
                }
            }
        }
    }

    /// Solves what a body, refinement or example left open, and writes the side table
    /// without variables, so the interpreter never sees one.
    fn settle(&mut self) {
        self.solve(0, 0, 0);
        for e in std::mem::take(&mut self.typed) {
            if let Some(ty) = self.p.expr_ty.get(e) {
                let ty = self.vars.zonk(ty);
                self.p.expr_ty.insert(e, ty);
            }
        }
        for local in &mut self.f.locals {
            local.ty = self.vars.zonk(&local.ty);
        }
        self.vars.clear();
    }

    fn iface_name(&self, iface: IfaceId) -> &str {
        &self.p.decls.iface(iface).name
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
            ItemKind::Record(decl) => vec![decl.name],
            ItemKind::Enum(decl) => vec![decl.name],
            ItemKind::Interface(decl) => vec![decl.name],
            ItemKind::Impl(_) | ItemKind::Example(_) => vec![],
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
        let available: Option<Vec<(&str, Ty)>> = match path.as_slice() {
            ["std", "io"] => Some(vec![("IoError", Ty::IoError), ("Out", Ty::out())]),
            // `ParseError` is the only item `std.text` declares (STD.md).
            ["std", "text"] => Some(vec![("ParseError", Ty::adt(AdtId::PARSE_ERROR))]),
            ["std", module] => {
                let planned = match *module {
                    "fs" | "test" => Planned::Phase(3),
                    "pool" => Planned::Phase(2),
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
                    format!("unknown module `{joined}`; phase 1 checks one file at a time, and the standard library provides only `std.io` and `std.text`"),
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
            let ty = match &available {
                Some(items) => match items.iter().find(|(n, _)| *n == text) {
                    Some((_, ty)) => ty.clone(),
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
                    format!("this import would shadow the prelude name `{bound_text}` (H4)"),
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
                } else {
                    self.pascal_case(bound, "type");
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

    fn adt_names(&mut self) {
        let m = self.m;
        for item in &m.items {
            let (name, derives, refinement, kind) = match &item.kind {
                ItemKind::Record(decl) => (decl.name, &decl.derives[..], decl.refinement, AdtKind::Record),
                ItemKind::Enum(decl) => (decl.name, &decl.derives[..], None, AdtKind::Enum),
                _ => continue,
            };
            let text = m.text(name.sym);
            let mut def = match kind {
                AdtKind::Record => AdtDef::record(text, Vec::new()),
                AdtKind::Enum => AdtDef::enumeration(text),
            };
            let mut variants: Vec<(Ident, &[FieldDecl])> = Vec::new();
            let mut variant_index: HashMap<Symbol, usize> = HashMap::new();
            match &item.kind {
                ItemKind::Record(decl) => variants.push((decl.name, &decl.fields)),
                ItemKind::Enum(decl) => {
                    for variant in &decl.variants {
                        let cased = self.pascal_case(variant.name, "variant");
                        let vtext = m.text(variant.name.sym);
                        if let Some(&first) = variant_index.get(&variant.name.sym) {
                            if cased {
                                let message = format!("variant `{vtext}` is declared twice");
                                self.error(codes::DUPLICATE_NAME, variant.name.span, message);
                            }
                            // Which one a use means is unclear, so uses of either aren't checked.
                            def.variants[first].rejected = true;
                            def.unknown_variants = true;
                            continue;
                        }
                        variant_index.insert(variant.name.sym, variants.len());
                        variants.push((variant.name, &variant.fields));
                        def.variants.push(VariantDef::new(vtext, Vec::new()));
                    }
                }
                _ => {}
            }
            let what = if kind == AdtKind::Enum { "enum" } else { "record" };
            let id = self.p.decls.push(def);
            self.adts.push(AdtSrc { id, name, vis: item.vis, derives, variants, refinement });
            // A rejected name is reported once. Its uses, and what it collides with, are not.
            let cased = self.pascal_case(name, "type");
            if !cased || prelude_type(text) {
                if cased {
                    let message = format!("this {what} would shadow the prelude name `{text}` (H4)");
                    self.error(codes::SHADOWING, name.span, message);
                }
                self.poisoned.insert(name.sym);
            } else if self.adt_names.contains_key(&name.sym) || self.imports.contains_key(&name.sym) {
                self.error(codes::DUPLICATE_ITEM, name.span, format!("`{text}` is defined twice in this module"));
            } else {
                self.adt_names.insert(name.sym, id);
            }
            if m.impls.contains(&name.sym) {
                let def = self.p.decls.adt_mut(id);
                def.unknown_interfaces = true;
                def.unknown_methods = true;
            }
        }
    }

    /// Resolves the fields of every variant once every record and enum has a name, so a
    /// field's type may be declared later in the file (OPEN_QUESTIONS P5).
    fn adt_fields(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let (id, name, vis) = (self.adts[k].id, self.adts[k].name, self.adts[k].vis);
            for v in 0..self.adts[k].variants.len() {
                let decls = self.adts[k].variants[v].1;
                let mut fields: Vec<FieldDef> = Vec::new();
                let mut index: HashMap<Symbol, usize> = HashMap::new();
                for field in decls {
                    let text = m.text(field.name.sym);
                    let cased = self.snake_case(field.name, "field");
                    let ty = self.resolve_type(field.ty);
                    if let Some(&first) = index.get(&field.name.sym) {
                        if cased {
                            let message = format!("field `{text}` is declared twice");
                            self.error(codes::DUPLICATE_NAME, field.name.span, message);
                        }
                        // The variant keeps the first, but which one a use means is unclear,
                        // so its uses aren't checked.
                        fields[first].ty = Ty::Error;
                        continue;
                    }
                    self.exposes(name, vis, &ty, field.ty);
                    index.insert(field.name.sym, fields.len());
                    fields.push(FieldDef { name: text.into(), ty });
                }
                let variant = &mut self.p.decls.adt_mut(id).variants[v];
                variant.locals = fields.len();
                variant.fields = fields;
            }
        }
    }

    /// Reports a type that `item`, declared with `vis`, may not mention because it is less
    /// visible (REFERENCE §3).
    fn exposes(&mut self, item: Ident, vis: Visibility, ty: &Ty, at: TypeId) {
        let Some((record, record_vis)) = self.least_visible(ty) else { return };
        if reach(record_vis) < reach(vis) {
            let name = self.p.decls.adt(record).name.clone();
            let span = self.m.types[at].span;
            self.too_visible(item, vis, &name, record_vis, span);
        }
    }

    /// Reports that `item`, declared with `vis`, mentions `name`, which is only `other_vis`.
    fn too_visible(&mut self, item: Ident, vis: Visibility, name: &str, other_vis: Visibility, span: Span) {
        let describe = |vis| match vis {
            Visibility::Private => "private",
            Visibility::PubPkg => "`pub(pkg)`",
            Visibility::Pub => "`pub`",
        };
        let message = format!(
            "`{}` is {}, so it may not mention `{name}`, which is {} (§3)",
            self.m.text(item.sym),
            describe(vis),
            describe(other_vis),
        );
        self.error(codes::PRIVATE_IN_PUBLIC, span, message);
    }

    /// The least visible module record or enum that `ty` mentions.
    fn least_visible(&self, ty: &Ty) -> Option<(AdtId, Visibility)> {
        let Ty::Adt(id, args) = ty else { return None };
        let own = self.adts.iter().find(|adt| adt.id == *id).map(|adt| (*id, adt.vis));
        let inner = args.iter().filter_map(|arg| self.least_visible(arg));
        own.into_iter().chain(inner).min_by_key(|&(_, vis)| reach(vis))
    }

    /// Declares the module's interfaces, whose methods are resolved once every type has a
    /// name.
    fn iface_names(&mut self) {
        let m = self.m;
        for item in &m.items {
            let ItemKind::Interface(decl) = &item.kind else { continue };
            let text = m.text(decl.name.sym);
            let def = IfaceDef { name: text.into(), methods: Vec::new(), incomplete: decl.recovered };
            let id = self.p.decls.push_iface(def);
            self.ifaces.push(IfaceSrc { id, decl, vis: item.vis });
            let cased = self.pascal_case(decl.name, "interface");
            if !cased || prelude_type(text) {
                if cased {
                    let message = format!("this interface would shadow the prelude name `{text}` (H4)");
                    self.error(codes::SHADOWING, decl.name.span, message);
                }
                self.poisoned.insert(decl.name.sym);
            } else if self.adt_names.contains_key(&decl.name.sym)
                || self.imports.contains_key(&decl.name.sym)
                || self.iface_names.contains_key(&decl.name.sym)
            {
                // A use of the name may mean either declaration, so neither is checked (§15.1).
                self.error(codes::DUPLICATE_ITEM, decl.name.span, format!("`{text}` is defined twice in this module"));
                self.poisoned.insert(decl.name.sym);
            } else {
                self.iface_names.insert(decl.name.sym, id);
            }
        }
    }

    /// Marks the prelude and standard library types that an `impl` block the parser rejected
    /// names, as `adt_names` marks the module's.
    fn unknown_impl_targets(&mut self) {
        let m = self.m;
        if m.tuple_impls {
            self.p.decls.poison_tuples();
        }
        for &sym in &m.impls {
            if !self.adt_names.contains_key(&sym) {
                self.unknown_target(sym);
            }
        }
    }

    /// Notes that a rejected `impl` block is for the type `sym` names, if any.
    fn unknown_target(&mut self, sym: Symbol) {
        let text = self.m.text(sym);
        let ty = match (self.adt_names.get(&sym), builtin_type(text), prelude_adt(text), self.imports.get(&sym)) {
            (Some(&id), ..) => Ty::adt(id),
            (_, Some(ty), _, _) => ty,
            (_, _, Some(id), _) => Ty::adt(id),
            (_, _, _, Some(Import::Type(ty))) => ty.clone(),
            _ => return,
        };
        self.unknown_ty(&ty);
    }

    /// Notes that a rejected `impl` block is for `ty`, which may then have methods and
    /// interfaces that nothing records, so their uses aren't reported (REFERENCE §15.1).
    fn unknown_ty(&mut self, ty: &Ty) {
        match ImplKey::of(ty) {
            Some(key) => self.p.decls.mark_unknown(key),
            None => self.unknown_tys.push(ty.clone()),
        }
    }

    /// Resolves the methods of each module interface, where `Self` is `Param(0)`.
    fn iface_methods(&mut self) {
        let m = self.m;
        self.self_ty = Some(Ty::Param(0));
        self.param_names = vec!["Self".into()];
        for k in 0..self.ifaces.len() {
            let IfaceSrc { id, decl, vis } = self.ifaces[k];
            let mut methods: Vec<IfaceMethod> = Vec::new();
            let mut incomplete = decl.recovered;
            'methods: for method in &decl.methods {
                let text = m.text(method.name.sym);
                // A wrongly cased name stands for the one it misspells, which an `impl` or a
                // call may use, so neither is checked against this interface (§15.1). Its
                // signature is still checked, as a duplicate's is.
                let cased = self.snake_case(method.name, "method");
                let duplicate = cased && methods.iter().any(|other| *other.name == *text);
                if !cased {
                    incomplete = true;
                } else if duplicate {
                    self.error(codes::DUPLICATE_NAME, method.name.span, format!("method `{text}` is declared twice"));
                }
                let receiver = method.receiver.expect("the parser keeps only interface methods with `self`");
                if receiver.mode != ParamMode::Borrow {
                    self.not_implemented(receiver.span, "`inout self` and `take self` methods", Planned::Phase(2));
                    incomplete = true;
                    continue;
                }
                let mut params: Vec<(Box<str>, Ty)> = Vec::new();
                let mut modes = Vec::new();
                for param in &method.params {
                    let cased = self.snake_case(param.name, "parameter");
                    let name = m.text(param.name.sym);
                    if cased && params.iter().any(|(other, _)| **other == *name) {
                        self.error(codes::SHADOWING, param.name.span, format!("parameter `{name}` is declared twice"));
                    }
                    if self.param_iface(param.ty).is_some() {
                        let span = m.types[param.ty].span;
                        self.not_implemented(span, "generic interface methods", Planned::Unscheduled);
                        incomplete = true;
                        continue 'methods;
                    }
                    let ty = self.resolve_type(param.ty);
                    if !self.param_mode(param, &ty) {
                        incomplete = true;
                        continue 'methods;
                    }
                    self.exposes(decl.name, vis, &ty, param.ty);
                    params.push((name.into(), ty));
                    modes.push(param.mode);
                }
                let ret = method.ret.map_or(Ty::Unit, |t| self.resolve_type(t));
                let fails = method.fails.map(|t| self.resolve_type(t)).filter(|t| *t != Ty::Never);
                if let Some(at) = method.ret {
                    self.exposes(decl.name, vis, &ret, at);
                }
                if let Some(at) = method.fails {
                    self.exposes(decl.name, vis, &fails.clone().unwrap_or(Ty::Never), at);
                }
                if cased && !duplicate {
                    methods.push(IfaceMethod { name: text.into(), params, modes, ret, fails });
                }
            }
            let def = self.p.decls.iface_mut(id);
            def.methods = methods;
            def.incomplete = incomplete;
        }
        self.self_ty = None;
        self.param_names.clear();
    }

    /// Resolves every `derives` list. Whether each field implements what its record or enum
    /// derives is checked once the `impl` blocks are known.
    fn adt_derives(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let (id, derives_of) = (self.adts[k].id, self.adts[k].derives);
            let mut seen: Vec<&str> = Vec::new();
            let mut derives = Vec::new();
            // A rejected entry may have named any interface, so it is taken to name each.
            let mut unknown = false;
            for name in derives_of {
                let text = m.text(name.sym);
                if seen.contains(&text) {
                    self.error(codes::DUPLICATE_NAME, name.span, format!("`{text}` is derived twice"));
                    continue;
                }
                seen.push(text);
                match IfaceId::prelude(text) {
                    Some(iface) if iface.derivable() => derives.push(iface),
                    Some(_) => {
                        unknown = true;
                        self.error(
                            codes::NOT_DERIVABLE,
                            name.span,
                            format!(
                                "`{text}` can't be derived; the derivable interfaces are `Eq`, `Ord`, `Hash` and `Show`"
                            ),
                        );
                    }
                    None if self.iface_names.contains_key(&name.sym) => {
                        unknown = true;
                        self.error(
                            codes::NOT_DERIVABLE,
                            name.span,
                            format!(
                                "`{text}` can't be derived, since it is not the prelude's; implement it with `impl {text} for …`"
                            ),
                        );
                    }
                    None => {
                        unknown = true;
                        self.error(
                            codes::UNKNOWN_TYPE,
                            name.span,
                            format!("unknown interface `{text}`; the derivable interfaces are `Eq`, `Ord`, `Hash` and `Show`"),
                        );
                    }
                }
            }
            let def = self.p.decls.adt_mut(id);
            def.derives = derives;
            def.unknown_interfaces |= unknown;
        }
    }

    /// Checks that each field implements what its record or enum derives, by `derives` or
    /// an `impl`, so a field's type answers wherever it is declared.
    fn derived_fields(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let adt = &self.adts[k];
            let def = self.p.decls.adt(adt.id);
            let mut missing = Vec::new();
            for &iface in &def.derives {
                for (variant, (_, decls)) in def.variants.iter().zip(&adt.variants) {
                    for (field, field_decl) in variant.fields.iter().zip(kept_fields(decls)) {
                        if !field.ty.is_unknown() && !self.p.decls.implements(&field.ty, iface, &[]) {
                            let message = format!(
                                "field `{}` has type `{}`, which does not implement `{}`, so `{}` cannot derive it",
                                field.name,
                                self.show(&field.ty),
                                self.iface_name(iface),
                                def.name
                            );
                            missing.push((m.types[field_decl.ty].span, message));
                        }
                    }
                }
            }
            for (span, message) in missing {
                self.error(codes::MISSING_IMPLEMENTATION, span, message);
            }
        }
    }

    /// Checks each refinement as a `Bool` in a scope of the fields it sees: its own field for
    /// a field's `where`, every field for a record's (OPEN_QUESTIONS P5).
    fn adt_predicates(&mut self) {
        for k in 0..self.adts.len() {
            let id = self.adts[k].id;
            for v in 0..self.adts[k].variants.len() {
                let kept = kept_fields(self.adts[k].variants[v].1);
                let fields = &self.p.decls.adt(id).variants[v].fields;
                let mut state = FnState::new(Ty::Unit, None);
                state.returns = false;
                state.locals =
                    fields.iter().map(|f| Local { ty: f.ty.clone(), mutable: false, borrowed: false }).collect();
                self.f = state;
                let mut preds = Vec::new();
                for (i, field) in kept.iter().enumerate() {
                    if let Some(expr) = field.refinement {
                        self.f.scopes = vec![vec![(field.name.sym, LocalId(i as u32))]];
                        self.check(expr, &Ty::Bool);
                        self.settle();
                        preds.push(Pred { expr, field: Some(FieldIdx(i as u32)) });
                    }
                }
                if let Some(expr) = self.adts[k].refinement {
                    let all = kept.iter().enumerate().map(|(i, f)| (f.name.sym, LocalId(i as u32)));
                    self.f.scopes = vec![all.collect()];
                    self.check(expr, &Ty::Bool);
                    self.settle();
                    preds.push(Pred { expr, field: None });
                }
                let variant = &mut self.p.decls.adt_mut(id).variants[v];
                variant.preds = preds;
                variant.locals = self.f.locals.len();
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
            if self.fn_names.contains_key(&decl.name.sym)
                || self.imports.contains_key(&decl.name.sym)
                || self.adt_names.contains_key(&decl.name.sym)
                || self.iface_names.contains_key(&decl.name.sym)
            {
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
            // `main` is `pub` so the runtime can call it, not to export it (OPEN_QUESTIONS P5).
            let vis = if name == "main" { Visibility::Private } else { item.vis };
            let sig = self.signature(decl, vis, None);
            self.p.fns.push(FnInfo {
                item: index,
                method: None,
                name: decl.name.sym,
                generics: sig.generics,
                receiver: None,
                owner: None,
                params: sig.params,
                ret: sig.ret,
                fails: sig.fails,
                locals: 0,
                rejected: sig.rejected,
            });
        }
    }

    /// Resolves the signature of a function, or of a method of an `impl` block for `owner`,
    /// and reports a type that a declaration with `vis` may not mention.
    fn signature(&mut self, decl: &FnDecl, vis: Visibility, owner: Option<Ty>) -> Signature {
        let m = self.m;
        let mut generics: Vec<GenericInfo> = Vec::new();
        self.generic_scope.clear();
        for param in &decl.generics {
            let text = m.text(param.name.sym);
            // A wrongly cased name is reported once, not again for what it collides with.
            let cased = self.pascal_case(param.name, "type parameter");
            // A rejected parameter keeps its place, so `::[…]` still gives it, and stands for
            // an unknown type (§15.1). Its name means the first declaration of it.
            let rejected =
                GenericInfo { name: text.into(), sym: None, param: None, bounds: Vec::new(), rejected: true };
            if self.generic_scope.iter().any(|(sym, _)| *sym == param.name.sym) {
                if cased {
                    let message = format!("type parameter `{text}` is declared twice");
                    self.error(codes::DUPLICATE_NAME, param.name.span, message);
                }
                generics.push(rejected);
                continue;
            }
            if cased && self.names_type(param.name.sym) {
                let message = format!("type parameter `{text}` would shadow the type `{text}` (H4)");
                self.error(codes::SHADOWING, param.name.span, message);
                self.generic_scope.push((param.name.sym, None));
                generics.push(GenericInfo { sym: Some(param.name.sym), ..rejected });
                continue;
            }
            let mut bounds = Vec::new();
            let mut rejected = false;
            for &bound in &param.bounds {
                match self.bound(bound, decl.name, vis) {
                    Some(iface) if !bounds.contains(&iface) => bounds.push(iface),
                    Some(_) => {}
                    None => rejected = true,
                }
            }
            let index = generics.len() as u32;
            self.generic_scope.push((param.name.sym, (!rejected).then_some(index)));
            generics.push(GenericInfo { name: text.into(), sym: Some(param.name.sym), param: None, bounds, rejected });
        }
        self.param_names = generics.iter().map(|g| g.name.clone()).collect();
        self.self_ty = owner.clone();
        let mut rejected = false;
        if let Some(receiver) = decl.receiver
            && receiver.mode != ParamMode::Borrow
        {
            self.not_implemented(receiver.span, "`inout self` and `take self` methods", Planned::Phase(2));
            rejected = true;
        }
        let receiver = decl.receiver.and(owner);
        let mut params: Vec<ParamInfo> = Vec::new();
        for param in &decl.params {
            let cased = self.snake_case(param.name, "parameter");
            if cased && params.iter().any(|p| p.name == param.name.sym) {
                let text = m.text(param.name.sym);
                self.error(codes::SHADOWING, param.name.span, format!("parameter `{text}` is declared twice"));
            }
            // A parameter of interface type, `x: Show`, means `[T: Show](x: T)` (REFERENCE §4.9).
            let ty = match self.param_iface(param.ty) {
                Some(name) => match self.bound(name, decl.name, vis) {
                    Some(iface) => {
                        let index = generics.len() as u32;
                        let name: Box<str> = format!("type of {}", m.text(param.name.sym)).into();
                        self.param_names.push(name.clone());
                        let sym = Some(param.name.sym);
                        generics.push(GenericInfo {
                            name,
                            sym: None,
                            param: sym,
                            bounds: vec![iface],
                            rejected: false,
                        });
                        Ty::Param(index)
                    }
                    None => Ty::Error,
                },
                None => self.resolve_type(param.ty),
            };
            self.param_mode(param, &ty);
            params.push(ParamInfo { name: param.name.sym, ty, mode: param.mode });
        }
        let ret = decl.ret.map_or(Ty::Unit, |t| self.resolve_type(t));
        // `Never` has no values, so a function that fails with it cannot fail.
        let fails = decl.fails.map(|t| self.resolve_type(t)).filter(|t| *t != Ty::Never);
        let typed = decl.params.iter().map(|p| p.ty).chain(decl.ret).chain(decl.fails);
        let types = params.iter().map(|p| p.ty.clone()).chain(decl.ret.map(|_| ret.clone()));
        let types: Vec<(Ty, TypeId)> =
            types.chain(decl.fails.map(|_| fails.clone().unwrap_or(Ty::Never))).zip(typed).collect();
        for (ty, at) in types {
            self.exposes(decl.name, vis, &ty, at);
        }
        self.generic_scope.clear();
        self.param_names.clear();
        self.self_ty = None;
        Signature { generics, receiver, params, ret, fails, rejected }
    }

    /// Reports a parameter mode that phase 2 doesn't support yet, and returns whether the
    /// mode is supported.
    fn param_mode(&mut self, param: &Param, ty: &Ty) -> bool {
        let what = match param.mode {
            ParamMode::Borrow => return true,
            ParamMode::Keep if matches!(ty, Ty::Adt(AdtId::SYSTEM, _) | Ty::Error) => return true,
            ParamMode::Keep => "`keep` parameters other than `System`",
            ParamMode::Inout | ParamMode::InoutPartial => "`inout` parameters",
            ParamMode::Take => "`take` parameters",
        };
        self.not_implemented(param.span, what, Planned::Phase(2));
        false
    }

    /// Whether `sym` names a type here, which a type parameter may not reuse (H4).
    fn names_type(&self, sym: Symbol) -> bool {
        prelude_type(self.m.text(sym))
            || self.adt_names.contains_key(&sym)
            || matches!(self.imports.get(&sym), Some(Import::Type(_)))
            || self.iface_names.contains_key(&sym)
    }

    /// Whether `sym` names a capability interface such as `Out`, which phase 3 lets programs
    /// implement and use as constraints (REFERENCE §9.6).
    fn names_cap(&self, sym: Symbol) -> bool {
        matches!(self.imports.get(&sym), Some(Import::Type(Ty::Cap(_))))
    }

    /// The interface a parameter's type names, when it is one, which makes the parameter
    /// generic (REFERENCE §4.9).
    fn param_iface(&self, t: TypeId) -> Option<Ident> {
        let TypeExprKind::Named(name) = self.m.types[t].kind else { return None };
        if self.poisoned.contains(&name.sym) || self.generic_scope.iter().any(|(sym, _)| *sym == name.sym) {
            return None;
        }
        let iface = self.iface_names.contains_key(&name.sym) || IfaceId::prelude(self.m.text(name.sym)).is_some();
        iface.then_some(name)
    }

    /// Resolves a constraint, which `item`, declared with `vis`, places on a type parameter.
    /// Returns `None` once it is reported, or when it names a rejected declaration.
    fn bound(&mut self, name: Ident, item: Ident, vis: Visibility) -> Option<IfaceId> {
        let text = self.m.text(name.sym);
        if self.poisoned.contains(&name.sym) {
            return None;
        }
        if let Some(&id) = self.iface_names.get(&name.sym) {
            let own = self.ifaces.iter().find(|src| src.id == id).map_or(Visibility::Pub, |src| src.vis);
            if reach(own) < reach(vis) {
                self.too_visible(item, vis, text, own, name.span);
            }
            return Some(id);
        }
        if self.names_cap(name.sym) {
            self.not_implemented(
                name.span,
                "constraints that name capability interfaces such as `Out`",
                Planned::Phase(3),
            );
            return None;
        }
        match IfaceId::prelude(text) {
            Some(iface @ (IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::HASH | IfaceId::COPY)) => Some(iface),
            Some(_) => {
                self.not_implemented(name.span, &format!("`{text}` constraints"), Planned::Phase(2));
                None
            }
            None if self.names_type(name.sym) || self.generic_scope.iter().any(|(sym, _)| *sym == name.sym) => {
                let message = format!("`{text}` is a type, not an interface, so it can't be a constraint");
                self.error(codes::UNKNOWN_TYPE, name.span, message);
                None
            }
            None => {
                self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown interface `{text}`"));
                None
            }
        }
    }

    /// Declares the methods of each `impl` block, and records which interfaces each type
    /// implements (REFERENCE §3, §4.9).
    fn impls(&mut self) {
        let m = self.m;
        for (index, item) in m.items.iter().enumerate() {
            if let ItemKind::Impl(decl) = &item.kind {
                self.impl_block(index, item.span, decl);
            }
        }
    }

    fn impl_block(&mut self, item: usize, span: Span, decl: &ImplDecl) {
        let m = self.m;
        let target_span = m.types[decl.target].span;
        let header = span.to(target_span);
        let target = self.resolve_type(decl.target);
        if target == Ty::Error {
            if let TypeExprKind::Named(name) | TypeExprKind::Applied { name, .. } = m.types[decl.target].kind {
                self.unknown_target(name.sym);
            }
            // The interface is checked on its own, and so are the bodies (§15.1).
            let rejected = match decl.iface {
                Some(name) => self.impl_iface(name).and_then(|iface| self.implementable(iface, name)).err(),
                None => None,
            };
            if rejected.is_none_or(|r| r.bodies) {
                self.declare_rejected(item, decl, &Ty::Error);
            }
            return;
        }
        let own = matches!(&target, Ty::Adt(id, _) if self.adts.iter().any(|adt| adt.id == *id));
        let target_text = self.show(&target).to_string();
        let key = ImplKey::of(&target);
        let Some(iface_name) = decl.iface else {
            let (Some(ImplKey::Adt(adt)), true) = (key, own) else {
                let message = format!(
                    "`{target_text}` isn't declared in this module, so its methods can't be declared here; declare an interface for them instead (§4.9)"
                );
                self.error(codes::ORPHAN_IMPL, target_span, message);
                self.declare_rejected(item, decl, &target);
                self.unknown_ty(&target);
                return;
            };
            // A method that didn't parse may have any name, so calls of unknown methods on the
            // type aren't reported (REFERENCE §15.1).
            if decl.recovered {
                self.p.decls.adt_mut(adt).unknown_methods = true;
            }
            let adt_vis = self.adts.iter().find(|src| src.id == adt).map_or(Visibility::Pub, |src| src.vis);
            for (i, method) in decl.methods.iter().enumerate() {
                // A method is visible no further than its type (§3).
                let vis = if reach(method.vis) > reach(adt_vis) { adt_vis } else { method.vis };
                let f = self.method_fn(item, i, method, &target, vis);
                let name = method.decl.name;
                let text = m.text(name.sym);
                // A wrongly cased name stands for the one it misspells, which calls may use.
                if !is_snake(text) {
                    self.p.decls.adt_mut(adt).unknown_methods = true;
                }
                let entries = self.inherent.entry(adt).or_default();
                let duplicate = entries.iter().any(|entry| entry.name == name.sym);
                entries.push(Inherent { name: name.sym, f, rejected: duplicate });
                if duplicate && is_snake(text) {
                    let message = format!("`{target_text}` already has a method `{text}`");
                    self.error(codes::DUPLICATE_NAME, name.span, message);
                }
            }
            return;
        };
        let iface = match self.impl_iface(iface_name) {
            Ok(iface) => iface,
            Err(rejected) => {
                self.reject_impl(item, decl, &target, rejected);
                return;
            }
        };
        let iface_text = self.iface_name(iface).to_string();
        if !own && !self.ifaces.iter().any(|src| src.id == iface) {
            let message = format!(
                "this module declares neither `{iface_text}` nor `{target_text}`, so it can't implement one for the other (§4.9)"
            );
            self.error(codes::ORPHAN_IMPL, target_span, message);
            self.declare_rejected(item, decl, &target);
            self.unknown_ty(&target);
            return;
        }
        if let Err(rejected) = self.implementable(iface, iface_name) {
            self.reject_impl(item, decl, &target, rejected);
            return;
        }
        // Dispatch reads the type of the receiver's value, which `Never` has none of, and
        // capabilities come in phase 3.
        let Some(key) = key else {
            let (what, planned) = match target {
                Ty::Cap(_) => ("implementations for capability types such as `Out`", Planned::Phase(3)),
                _ => ("implementations for `Never`", Planned::Unscheduled),
            };
            self.not_implemented(target_span, what, planned);
            self.unknown_ty(&target);
            return;
        };
        if let Ty::Adt(id, _) = &target
            && self.p.decls.adt(*id).derives.contains(&iface)
        {
            let message = format!("`{target_text}` derives `{iface_text}`, so it implements it already");
            self.error(codes::DUPLICATE_IMPLEMENTATION, header, message);
            self.declare_rejected(item, decl, &target);
            return;
        }
        if self.p.decls.impl_of(iface, key).is_some() {
            let message = format!("`{target_text}` already implements `{iface_text}`");
            self.error(codes::DUPLICATE_IMPLEMENTATION, header, message);
            self.declare_rejected(item, decl, &target);
            return;
        }
        let incomplete = self.p.decls.iface(iface).incomplete;
        let count = self.p.decls.iface(iface).methods.len();
        let mut fns: Vec<Option<FnId>> = vec![None; count];
        let mut named = vec![false; count];
        // A wrongly cased method name stands for the one it misspells (§15.1).
        let mut miscased = false;
        for (i, method) in decl.methods.iter().enumerate() {
            let f = self.method_fn(item, i, method, &target, Visibility::Private);
            let name = method.decl.name;
            let text = m.text(name.sym);
            if !is_snake(text) {
                miscased = true;
                continue;
            }
            match self.p.decls.iface(iface).method(text) {
                None if incomplete => {}
                None => {
                    let message = format!(
                        "`{iface_text}` has no method `{text}`; an `impl` gives its type exactly the methods its interface declares"
                    );
                    self.error(codes::IMPL_MISMATCH, name.span, message);
                }
                Some(j) if named[j] => {
                    self.error(codes::DUPLICATE_NAME, name.span, format!("`{text}` is declared twice in this block"));
                }
                Some(j) => {
                    named[j] = true;
                    if builtin_method(&target, text).is_some() {
                        let message = format!(
                            "`{text}` is also a built-in method of `{target_text}`, so calls of it would be ambiguous (§3)"
                        );
                        self.error(codes::AMBIGUOUS_METHOD, name.span, message);
                    }
                    if self.conforms(f, iface, j, &target, name) {
                        fns[j] = Some(f);
                    }
                }
            }
        }
        let def = self.p.decls.iface(iface);
        let missing: Vec<String> =
            (0..count).filter(|&j| !named[j]).map(|j| format!("`{}`", def.methods[j].name)).collect();
        if !missing.is_empty() && !incomplete && !decl.recovered && !miscased {
            let message = format!(
                "`{target_text}` must have every method of `{iface_text}`, but this block lacks {}",
                missing.join(", ")
            );
            self.error(codes::IMPL_MISMATCH, header, message);
        }
        self.p.decls.add_impl(iface, key, ImplDef { methods: fns });
    }

    /// Records an `impl` block for `target` that names an interface it can't implement.
    fn reject_impl(&mut self, item: usize, decl: &ImplDecl, target: &Ty, rejected: Rejected) {
        if rejected.unknown {
            self.unknown_ty(target);
        }
        if rejected.bodies {
            self.declare_rejected(item, decl, target);
        }
    }

    /// Declares the methods of a rejected `impl` block for `target`, so that their bodies are
    /// checked, without giving them to the type.
    fn declare_rejected(&mut self, item: usize, decl: &ImplDecl, target: &Ty) {
        for (i, method) in decl.methods.iter().enumerate() {
            self.method_fn(item, i, method, target, Visibility::Private);
        }
    }

    /// The interface that `impl I for T` names, or why the block is rejected once that is
    /// reported (REFERENCE §15.1).
    fn impl_iface(&mut self, name: Ident) -> Result<IfaceId, Rejected> {
        let text = self.m.text(name.sym);
        // A rejected declaration may have been any interface.
        if self.poisoned.contains(&name.sym) {
            return Err(Rejected { unknown: true, bodies: true });
        }
        if let Some(&id) = self.iface_names.get(&name.sym) {
            return Ok(id);
        }
        if self.names_cap(name.sym) {
            let what = "implementations of capability interfaces such as `Out`";
            self.not_implemented(name.span, what, Planned::Phase(3));
            return Err(Rejected { unknown: true, bodies: false });
        }
        let Some(iface) = IfaceId::prelude(text) else {
            let message = if self.names_type(name.sym) {
                format!("`{text}` is a type, not an interface")
            } else {
                format!("unknown interface `{text}`")
            };
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return Err(Rejected { unknown: true, bodies: true });
        };
        Ok(iface)
    }

    /// Whether this slice lets a module implement `iface` by hand, reported when it doesn't.
    /// The bodies of a later phase's implementation wait for it.
    fn implementable(&mut self, iface: IfaceId, name: Ident) -> Result<(), Rejected> {
        if self.ifaces.iter().any(|src| src.id == iface) {
            return Ok(());
        }
        let later = Rejected { unknown: true, bodies: false };
        match iface {
            IfaceId::EQ | IfaceId::SHOW => Ok(()),
            IfaceId::COPY => {
                let message =
                    "`Copy` holds by itself for copyable types with no reach, so it can't be implemented (§5.1)";
                self.error(codes::NOT_IMPLEMENTABLE, name.span, message);
                Err(Rejected { unknown: false, bodies: true })
            }
            IfaceId::ORD => {
                let what = "hand-written `Ord` implementations, whose `cmp` returns an `Ordering`,";
                self.not_implemented(name.span, what, Planned::Phase(2));
                Err(later)
            }
            IfaceId::HASH => {
                self.not_implemented(name.span, "hand-written `Hash` implementations", Planned::Unscheduled);
                Err(later)
            }
            _ => {
                let text = self.m.text(name.sym);
                self.not_implemented(name.span, &format!("`{text}` implementations"), Planned::Phase(2));
                Err(later)
            }
        }
    }

    /// Declares method `index` of the `impl` block at `item`, for `owner`.
    fn method_fn(&mut self, item: usize, index: usize, method: &Method, owner: &Ty, vis: Visibility) -> FnId {
        self.snake_case(method.decl.name, "method");
        let sig = self.signature(&method.decl, vis, Some(owner.clone()));
        let id = self.p.fns.len();
        self.p.fns.push(FnInfo {
            item,
            method: Some(index),
            name: method.decl.name.sym,
            generics: sig.generics,
            receiver: sig.receiver,
            owner: Some(owner.clone()),
            params: sig.params,
            ret: sig.ret,
            fails: sig.fails,
            locals: 0,
            rejected: sig.rejected,
        });
        id
    }

    /// Whether method `f` of an `impl` for `target` is declared as method `j` of `iface`
    /// is, reading `Self` as `target`, and reports it if not (REFERENCE §4.9). A part with an
    /// error is taken to agree.
    fn conforms(&mut self, f: FnId, iface: IfaceId, j: usize, target: &Ty, name: Ident) -> bool {
        let m = self.m;
        let info = &self.p.fns[f];
        if info.rejected {
            return false;
        }
        let want = &self.p.decls.iface(iface).methods[j];
        let args = [target.clone()];
        let same = |want: &Ty, have: &Ty| {
            let want = want.subst(&args);
            want == *have || want == Ty::Error || *have == Ty::Error
        };
        let params_agree = info.params.len() == want.params.len()
            && info.params.iter().zip(want.params.iter().zip(&want.modes)).all(|(have, ((name, ty), mode))| {
                m.text(have.name) == &**name && have.mode == *mode && same(ty, &have.ty)
            });
        let fails_agree = match (&want.fails, &info.fails) {
            (None, None) => true,
            (Some(want), Some(have)) => same(want, have),
            _ => false,
        };
        if info.generics.is_empty()
            && info.receiver.is_some()
            && params_agree
            && same(&want.ret, &info.ret)
            && fails_agree
        {
            return true;
        }
        let decls = &self.p.decls;
        let mut declared = format!("fn {}(self", want.name);
        for ((param, ty), mode) in want.params.iter().zip(&want.modes) {
            let mode = match mode {
                ParamMode::Borrow => "",
                ParamMode::Keep => "keep ",
                ParamMode::Take => "take ",
                ParamMode::Inout | ParamMode::InoutPartial => "inout ",
            };
            declared.push_str(&format!(", {param}: {mode}{}", decls.display(&ty.subst(&args))));
        }
        declared.push(')');
        if want.ret != Ty::Unit {
            declared.push_str(&format!(" -> {}", decls.display(&want.ret.subst(&args))));
        }
        if let Some(err) = &want.fails {
            declared.push_str(&format!(" fails {}", decls.display(&err.subst(&args))));
        }
        let message = format!(
            "`{}` must be declared as `{}` declares it, with `Self` as `{}`: `{declared}`",
            m.text(name.sym),
            decls.iface(iface).name,
            decls.display(target)
        );
        self.error(codes::IMPL_MISMATCH, name.span, message);
        false
    }

    /// Reports a method of a type's own that shares its name with a method of an interface
    /// the type implements, by `derives` or by an `impl` (REFERENCE §3). Calls of the name
    /// may mean either, so they aren't reported (§15.1).
    fn collisions(&mut self) {
        let m = self.m;
        let mut adts: Vec<AdtId> = self.inherent.keys().copied().collect();
        adts.sort_by_key(|id| id.index());
        for adt in adts {
            let mut ifaces: Vec<IfaceId> = self.p.decls.adt(adt).derives.clone();
            ifaces.extend(self.p.decls.impls_for(ImplKey::Adt(adt)));
            ifaces.sort_by_key(|iface| iface.index());
            for k in 0..self.inherent[&adt].len() {
                let entry = &self.inherent[&adt][k];
                let text = m.text(entry.name);
                if entry.rejected {
                    continue;
                }
                let Some(&iface) = ifaces.iter().find(|&&iface| self.p.decls.iface(iface).method(text).is_some())
                else {
                    continue;
                };
                let span = self.p.decl(m, entry.f).name.span;
                let message = format!(
                    "`{text}` is also a method of `{}`, which `{}` implements, so calls of it would be ambiguous (§3)",
                    self.iface_name(iface),
                    self.p.decls.adt(adt).name
                );
                self.error(codes::AMBIGUOUS_METHOD, span, message);
                if let Some(entries) = self.inherent.get_mut(&adt) {
                    entries[k].rejected = true;
                }
            }
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
        // The runtime gives `main` no type arguments.
        let generic = !info.generics.is_empty();
        let signature_ok = item.vis == Visibility::Pub
            && !generic
            && info.params.len() == 1
            && matches!(info.params[0].ty, Ty::Adt(AdtId::SYSTEM, _) | Ty::Error)
            && info.params[0].mode == ParamMode::Keep
            && matches!(info.ret, Ty::Unit | Ty::Error);
        let fails = info.fails.clone();
        if !signature_ok {
            self.error(
                codes::INVALID_MAIN,
                span,
                "`main` must be declared `pub fn main(sys: keep System)`, optionally followed by `fails E`",
            );
        }
        if let Some(err) = fails
            && !generic
            && !self.p.decls.implements(&err, IfaceId::SHOW, &[])
            && err != Ty::Error
        {
            self.error(
                codes::MAIN_ERROR_NOT_SHOW,
                span,
                format!("`main` fails with `{}`, which does not implement `Show`", self.show(&err)),
            );
        }
    }

    fn resolve_type(&mut self, t: TypeId) -> Ty {
        let m = self.m;
        let te = &m.types[t];
        match te.kind {
            TypeExprKind::Named(name) => self.type_name(name),
            TypeExprKind::Tuple(ref elements) => {
                let tys = elements.iter().map(|&t| self.resolve_type(t)).collect();
                self.p.decls.tuple_ty(tys)
            }
            TypeExprKind::SelfType => match &self.self_ty {
                Some(ty) => ty.clone(),
                None => {
                    let message = "`Self` is the type of an `impl` block, or the implementing type in an interface, so it exists only there";
                    self.error(codes::UNKNOWN_TYPE, te.span, message);
                    Ty::Error
                }
            },
            TypeExprKind::Applied { name, ref args } => {
                let text = m.text(name.sym);
                if self.poisoned.contains(&name.sym) {
                    return Ty::Error;
                }
                if self.generic_scope.iter().any(|(sym, _)| *sym == name.sym)
                    || self.iface_names.contains_key(&name.sym)
                    || IfaceId::prelude(text).is_some()
                {
                    self.error(codes::UNKNOWN_TYPE, te.span, format!("`{text}` takes no type arguments"));
                    return Ty::Error;
                }
                if let Some(id) = prelude_adt(text) {
                    let args = args.as_deref().unwrap_or_default();
                    let tys: Vec<Ty> = args.iter().map(|&arg| self.resolve_type(arg)).collect();
                    let n = self.p.decls.adt(id).params;
                    if tys.len() != n {
                        let verb = if tys.len() == 1 { "was" } else { "were" };
                        let message = format!("`{text}` takes {}, but {} {verb} given", type_args(n), tys.len());
                        self.error(codes::UNKNOWN_TYPE, te.span, message);
                        return Ty::Error;
                    }
                    return Ty::applied(id, tys);
                }
                if self.adt_names.contains_key(&name.sym)
                    || matches!(self.imports.get(&name.sym), Some(Import::Type(_)))
                {
                    self.error(codes::UNKNOWN_TYPE, te.span, format!("`{text}` takes no type arguments"));
                    return Ty::Error;
                }
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
        // Before the prelude, which a rejected record may have tried to shadow.
        if self.poisoned.contains(&name.sym) {
            return Ty::Error;
        }
        if let Some(&(_, index)) = self.generic_scope.iter().find(|(sym, _)| *sym == name.sym) {
            return index.map_or(Ty::Error, Ty::Param);
        }
        if let Some(ty) = builtin_type(text) {
            return ty;
        }
        if let Some(&id) = self.adt_names.get(&name.sym) {
            return Ty::adt(id);
        }
        if let Some(id) = prelude_adt(text) {
            let n = self.p.decls.adt(id).params;
            let message = format!("`{text}` takes {}, as in `{}`", type_args(n), example_type(text));
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return Ty::Error;
        }
        match self.imports.get(&name.sym) {
            Some(Import::Type(ty)) => return ty.clone(),
            Some(Import::Module) => {
                self.error(codes::UNKNOWN_TYPE, name.span, format!("`{text}` is a module, not a type"));
                return Ty::Error;
            }
            None => {}
        }
        if self.iface_names.contains_key(&name.sym) || IfaceId::prelude(text).is_some() {
            let message = format!(
                "`{text}` is an interface, not a type; only a parameter may have an interface type, which makes it generic (§4.9)"
            );
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return Ty::Error;
        }
        match later_type(text) {
            Some(planned) => self.not_implemented(name.span, &format!("`{text}` types"), planned),
            None => self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown type `{text}`")),
        }
        Ty::Error
    }

    /// Reports a type or variant name that isn't PascalCase, and returns whether it is. A
    /// non-ASCII name is already reported by the lexer.
    fn pascal_case(&mut self, name: Ident, what: &str) -> bool {
        let text = self.m.text(name.sym);
        if !text.is_ascii() {
            return false;
        }
        if !is_pascal(text) {
            self.error(codes::WRONG_CASE, name.span, format!("{what} names are PascalCase: `{text}`"));
            return false;
        }
        true
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
        let decl = self.p.decl(m, id);
        let Some(body) = &decl.body else { return };
        if info.rejected {
            return;
        }
        let mut state = FnState::new(info.ret.clone(), info.fails.clone());
        state.bounds = info.generics.iter().map(|g| g.bounds.clone()).collect();
        state.anonymous = (info.generics.iter())
            .map(|g| Some((m.text(g.param?).into(), self.iface_name(*g.bounds.first()?).into())))
            .collect();
        self.generic_scope = (info.generics.iter().enumerate())
            .filter_map(|(i, g)| Some((g.sym?, (!g.rejected).then_some(i as u32))))
            .collect();
        self.param_names = info.generics.iter().map(|g| g.name.clone()).collect();
        self.self_ty = info.owner.clone();
        // The function borrows `self` and its parameters (REFERENCE §5.2). A `take` parameter
        // is owned instead, and an `inout` one is rejected in this phase.
        let mut scope = Vec::new();
        if let Some(ty) = &info.receiver {
            state.locals.push(Local { ty: ty.clone(), mutable: false, borrowed: true });
            if let Some(sym) = m.interner.lookup("self") {
                scope.push((sym, LocalId(0)));
            }
        }
        for param in &info.params {
            scope.push((param.name, LocalId(state.locals.len() as u32)));
            let borrowed = matches!(param.mode, ParamMode::Borrow | ParamMode::Keep);
            state.locals.push(Local { ty: param.ty.clone(), mutable: false, borrowed });
        }
        state.scopes.push(scope);
        self.f = state;
        for param in &decl.params {
            self.shadows_item(param.name);
        }
        self.fn_body(decl, body);
        self.settle();
        self.p.fns[id].locals = self.f.locals.len();
        self.generic_scope.clear();
        self.param_names.clear();
        self.self_ty = None;
    }

    /// Checks each `example f(…) == v` and `example f(…) fails P` (REFERENCE §14). The
    /// example marks the fallible calls of its postfix chain, as `attempt` does (§7.2).
    /// `== v` needs `v` to have the call's type, and that type `Eq`, or to be a float,
    /// compared by IEEE `==` (§12.2). `fails P` needs a call that can fail, and a pattern
    /// for its error (OPEN_QUESTIONS P5).
    fn examples(&mut self) {
        let m = self.m;
        for (index, item) in m.items.iter().enumerate() {
            let ItemKind::Example(decl) = &item.kind else { continue };
            let mut state = FnState::new(Ty::Unit, None);
            (state.returns, state.example) = (false, true);
            state.scopes.push(Vec::new());
            self.f = state;
            if self.names_construction(decl.call) {
                let span = self.span(decl.call);
                let message = "an example tests a function or method call, not a construction";
                self.error(codes::UNEXPECTED_TOKEN, span, message);
                continue;
            }
            self.example(decl);
            self.settle();
            self.p.examples.push(ExampleInfo { item: index, locals: self.f.locals.len() });
        }
    }

    /// Checks one example. `call == v` reads its operands as `==` does, so either may give
    /// the other its type (OPEN_QUESTIONS P5; issue #10).
    fn example(&mut self, decl: &ExampleDecl) {
        self.markers.push(Marker { handler: Some(decl.call), errors: Vec::new() });
        self.in_chain = true;
        let ty = self.expr(decl.call, None);
        let errors = self.markers.pop().map(|m| m.errors).unwrap_or_default();
        let span = self.span(decl.call);
        let hole = self.met_hole(&errors);
        let err = self.one_error(errors, span, "example", "an example expects one error type");
        match &decl.expect {
            Expectation::Equals(value) => {
                // A call that was rejected has nothing to compare with (§15.1).
                if ty == Ty::Error {
                    self.rejected_value(*value);
                    return;
                }
                // As in `operands`, the call gives the value what it knows of its type, and the
                // type compared is their join, which a `Never` part of either may widen (§9.2; OPEN_QUESTIONS P5).
                let hint = (ty.is_numeric() || matches!(ty, Ty::Adt(..) | Ty::Var(_))).then_some(&ty);
                let value_ty = self.expr(*value, hint);
                let ty = match self.vars.join(&value_ty, &ty) {
                    Some(joined) => self.force(&joined),
                    None => {
                        let message = format!("expected `{}`, found `{}`", self.show(&ty), self.show(&value_ty));
                        self.error(codes::TYPE_MISMATCH, self.span(*value), message);
                        self.vars.poison(&ty);
                        self.vars.poison(&value_ty);
                        Ty::Error
                    }
                };
                let defined = matches!(ty, Ty::Float(_)) || self.implements(&ty, IfaceId::EQ);
                if !defined && !ty.is_unknown() {
                    let message =
                        format!("`==` is not defined for `{}`, so an example can't compare it", self.show(&ty));
                    let at = span.to(self.span(*value));
                    self.error(codes::UNSUPPORTED_OPERATOR, at, message);
                }
            }
            Expectation::Fails(pat) => {
                let err = match err {
                    Some(err) => {
                        let forced = self.force(&err);
                        if ty != Ty::Error && !hole {
                            self.can_fail(&err, Handler::Example, span);
                        }
                        forced
                    }
                    None => {
                        if !ty.is_unknown() {
                            let message = "`fails` needs a call that can fail, and this one can't";
                            self.error(codes::EXAMPLE_CANNOT_FAIL, span, message);
                        }
                        Ty::Error
                    }
                };
                self.pattern(*pat, &err);
            }
        }
    }

    /// Whether `e` is an `if`, or a chain of `else if`s, that ends without an `else`.
    fn lacks_final_else(&self, mut e: ExprId) -> bool {
        loop {
            match &self.m.exprs[e].kind {
                ExprKind::If { else_branch: None, .. } => return true,
                ExprKind::If { else_branch: Some(ElseBranch::If(nested)), .. } => e = *nested,
                _ => return false,
            }
        }
    }

    /// Whether an example's call builds a value, as `Some(1)`, `Point(x: 1)` and
    /// `Shape.Circle(r: 1)` do. Only the checker knows whether `Sure(1)` calls a misnamed
    /// function instead, so the parser leaves this to it (REFERENCE §14). It is told from
    /// the names alone, so a rejected construction isn't checked.
    fn names_construction(&self, call: ExprId) -> bool {
        let m = self.m;
        match m.exprs[call].kind {
            ExprKind::Call { callee, .. } => match m.exprs[callee].kind {
                ExprKind::Name(name) => {
                    !self.fn_names.contains_key(&name.sym)
                        && (bare_variant(m.text(name.sym)).is_some()
                            || self.adt_named(name.sym).is_some_and(|id| !self.p.decls.adt(id).is_enum()))
                }
                _ => false,
            },
            ExprKind::MethodCall { receiver, method, .. } => self
                .enum_named(receiver)
                .is_some_and(|id| self.p.decls.adt(id).variant_named(m.text(method.sym)).is_some()),
            _ => false,
        }
    }

    fn fn_body(&mut self, decl: &FnDecl, body: &Block) {
        let m = self.m;
        let ret = self.f.ret.clone();
        self.f.scopes.push(Vec::new());
        // A body's own statements wait on no variable, since nothing is around them.
        let flow = if ret == Ty::Unit { self.stmts(&body.stmts) } else { self.tail_stmts(body, &ret) };
        self.f.scopes.pop();
        // A body that needed parse recovery has unknown control flow.
        if ret != Ty::Unit && ret != Ty::Error && flow != Flow::Leaves && !decl.recovered {
            let name = m.text(decl.name.sym);
            self.error(
                codes::MISSING_RETURN,
                body.span.end(),
                format!("`{name}` returns `{}`, so every path must end with `return`", self.show(&ret)),
            );
        }
    }

    /// Checks the statements of a body that returns `ret`, or of a branch that ends one. A
    /// final value there is a missing `return`, not an unused value. Returns whether the
    /// statements always leave, counting such a value as a return.
    fn tail_stmts(&mut self, block: &Block, ret: &Ty) -> Flow {
        let m = self.m;
        let mut flow = Flow::Finishes;
        let count = block.stmts.len();
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == count
                && let StmtKind::Expr(e) = m.stmts[s].kind
            {
                if self.is_bare_value(e) {
                    self.check(e, ret);
                    let span = self.span(e);
                    self.error(
                        codes::MISSING_RETURN,
                        span,
                        "function bodies have no implicit final value; write `return` before it",
                    );
                    return Flow::Leaves;
                }
                let last = match m.exprs[e].kind {
                    ExprKind::If { .. } => self.if_expr(e, Mode::Tail(ret)),
                    ExprKind::Match { .. } => self.match_expr(e, Mode::Tail(ret)),
                    _ => {
                        let next = self.stmt(s);
                        return self.then(flow, next);
                    }
                };
                let last = self.flow(&last);
                return self.then(flow, last);
            }
            let next = self.stmt(s);
            flow = self.then(flow, next);
        }
        self.now(flow)
    }

    /// Declares a local in the innermost scope. A `borrowed` one is part of a parameter.
    fn declare(&mut self, name: Ident, ty: Ty, mutable: bool, what: &str, borrowed: bool) -> LocalId {
        let id = LocalId(self.f.locals.len() as u32);
        self.f.locals.push(Local { ty, mutable, borrowed });
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

    /// Checks a statement and returns whether it always leaves. What it leaves open is
    /// solved at its end, since nothing after it can give it (OPEN_QUESTIONS P5).
    fn stmt(&mut self, s: StmtId) -> Flow {
        let (vars, pending, bound) = (self.vars.count(), self.pending.len(), self.vars.bound());
        let outer = std::mem::replace(&mut self.stmt_start, (vars, bound));
        let flow = self.stmt_kind(s);
        self.stmt_start = outer;
        self.solve(vars, pending, bound);
        self.now(flow)
    }

    fn stmt_kind(&mut self, s: StmtId) -> Flow {
        let m = self.m;
        let stmt = &m.stmts[s];
        match &stmt.kind {
            StmtKind::Let { mutable, pat, ty, init } => {
                let declared = ty.map(|t| self.resolve_type(t));
                // Binding a value to a new name copies it (REFERENCE §4.8). Taking it apart
                // matches it, which borrows its parts when it is borrowed, as in a `match` (§6.4).
                let destructures = !matches!(self.m.pats[*pat].kind, PatKind::Bind(_) | PatKind::Wild);
                self.copying = !destructures;
                let (ty, init_ty) = match declared {
                    Some(declared) => {
                        let init_ty = self.check(*init, &declared);
                        (declared, init_ty)
                    }
                    // The binding has its value's type, so a later use doesn't give it, and
                    // `let x = None` is an error (OPEN_QUESTIONS P5).
                    None => {
                        let ty = self.infer(*init);
                        let ty = self.force(&ty);
                        (ty.clone(), ty)
                    }
                };
                self.pattern_borrowed = destructures && self.borrowed_value(*init);
                self.let_pattern(*pat, &ty, *mutable);
                self.pattern_borrowed = false;
                self.flow(&init_ty)
            }
            StmtKind::Check { cond, fallback } => {
                // The fallback runs when the condition is false, so the bindings of its `is`
                // tests don't reach it. The code after it runs only when the condition holds,
                // so they scope over the rest of the block (§6.4, §8.4; OPEN_QUESTIONS P5).
                self.f.scopes.push(Vec::new());
                self.condition(*cond);
                let bindings = self.f.scopes.pop().unwrap_or_default();
                let (ty, span) = match fallback {
                    Fallback::Value(value) => {
                        let ty = self.infer(*value);
                        (self.settle_own(&ty), self.span(*value))
                    }
                    Fallback::Block(block) => (self.block_stmt(block, None), block.span),
                };
                // What the `let` around a fallback still gives, such as the error type of
                // `it`, is waited for (OPEN_QUESTIONS P5).
                if self.vars.has_open(&ty) {
                    self.pending.push(Pending::Leaves { ty, must: Must::Check(span) });
                } else {
                    self.check_leaves(&ty, span);
                }
                if let Some(scope) = self.f.scopes.last_mut() {
                    scope.extend(bindings);
                }
                Flow::Finishes
            }
            StmtKind::Assign { target, op, value } => {
                let ty = self.assign(*target, *op, *value);
                self.flow(&ty)
            }
            StmtKind::Expr(e) => {
                let ty = self.expr_stmt(*e);
                let ty = self.settle_own(&ty);
                self.flow(&ty)
            }
            StmtKind::Return(value) if !self.f.returns => {
                if let Some(value) = value {
                    self.rejected_value(*value);
                }
                self.error(
                    codes::MISPLACED_RETURN,
                    stmt.span,
                    if self.f.example {
                        "`return` outside a function body; an example is an expression"
                    } else {
                        "`return` outside a function body; a `where` clause is an expression"
                    },
                );
                Flow::Leaves
            }
            StmtKind::Return(value) => {
                let ret = self.f.ret.clone();
                match value {
                    Some(value) => {
                        self.copying = true;
                        self.check(*value, &ret);
                    }
                    None if ret != Ty::Unit && ret != Ty::Error => {
                        let message = format!("`return` needs a value of type `{}`", self.show(&ret));
                        self.error(codes::TYPE_MISMATCH, stmt.span, message);
                    }
                    None => {}
                }
                Flow::Leaves
            }
            StmtKind::Break(label) => {
                self.jump(s, *label, true);
                Flow::Leaves
            }
            StmtKind::Continue(label) => {
                self.jump(s, *label, false);
                Flow::Leaves
            }
            StmtKind::Assert(cond) => {
                let ty = self.check(*cond, &Ty::Bool);
                self.flow(&ty)
            }
        }
    }

    /// Binds the names of a `let` or `var` pattern for a value of type `ty`. The pattern must
    /// match every value (REFERENCE §6.4; OPEN_QUESTIONS P5).
    fn let_pattern(&mut self, pat: PatId, ty: &Ty, mutable: bool) {
        let m = self.m;
        if let PatKind::Bind(name) = m.pats[pat].kind {
            let what = if mutable { "variable" } else { "binding" };
            let id = self.declare(name, ty.clone(), mutable, what, false);
            self.p.pat_local.insert(pat, id);
            return;
        }
        (self.pattern_mutable, self.let_pattern) = (mutable, true);
        let space = self.pattern(pat, ty);
        (self.pattern_mutable, self.let_pattern) = (false, false);
        if ty.is_unknown() {
            return;
        }
        let inhabited = self.inhabited.as_ref().expect("bodies are checked after the declarations");
        let missing = match exhaust::uncovered(&self.p.decls, inhabited, ty, &[space]) {
            Ok(None) => return,
            Ok(Some(missing)) => format!("this pattern does not match `{missing}`"),
            Err(exhaust::TooComplex) => "this pattern is too complex to check".to_string(),
        };
        let span = m.pats[pat].span;
        let message =
            format!("{missing}, and a `let` pattern must match every value; use `match`, `is` or an `else` form");
        self.error(codes::REFUTABLE_PATTERN, span, message);
    }

    fn expr_stmt(&mut self, e: ExprId) -> Ty {
        match self.m.exprs[e].kind {
            ExprKind::If { .. } => return self.if_expr(e, Mode::Stmt),
            ExprKind::Match { .. } => return self.match_expr(e, Mode::Stmt),
            _ => {}
        }
        let bare = self.is_bare_value(e);
        // An unused value needs no type, so a `None` there isn't also reported as one whose
        // type can't be inferred.
        let ty = self.expr(e, bare.then_some(&Ty::Error));
        if bare {
            let span = self.span(e);
            self.error(
                codes::BARE_VALUE_STATEMENT,
                span,
                "this value is unused; a statement must be a call, an assignment or a control expression",
            );
        }
        ty
    }

    /// Checks an assignment and returns the type of the assigned value.
    fn assign(&mut self, target: ExprId, op: AssignOp, value: ExprId) -> Ty {
        let span = self.span(target);
        let Some((root, id, ty)) = self.place(target) else { return self.infer(value) };
        if !self.f.locals[id.index()].mutable {
            let text = self.m.text(root.sym);
            self.error(
                codes::IMMUTABLE_ASSIGNMENT,
                span,
                format!("`{text}` is a `let` binding or a parameter; declare it with `var` to assign to it"),
            );
        }
        self.copying = true;
        let value_ty = self.check(value, &ty);
        if let Some(bin) = op.bin_op()
            && !arithmetic_defined(bin, &ty)
        {
            let symbol = bin.symbol();
            self.error(
                codes::UNSUPPORTED_OPERATOR,
                span,
                format!("`{symbol}=` is not defined for `{}`", self.show(&ty)),
            );
        }
        value_ty
    }

    /// Resolves an assignment target, which is a variable or a chain of fields rooted at one.
    /// Returns the variable and the type of the place, or `None` once it is reported.
    fn place(&mut self, target: ExprId) -> Option<(Ident, LocalId, Ty)> {
        let m = self.m;
        let (root, id, ty) = match m.exprs[target].kind {
            ExprKind::Name(name) => {
                let Some(id) = self.lookup_local(name.sym) else {
                    if !self.poisoned.contains(&name.sym) {
                        let text = m.text(name.sym);
                        let span = self.span(target);
                        self.error(codes::UNKNOWN_NAME, span, format!("unknown variable `{text}`"));
                    }
                    return None;
                };
                self.p.res.insert(target, Res::Local(id));
                (name, id, self.f.locals[id.index()].ty.clone())
            }
            ExprKind::Field { base, name } => {
                let (root, id, base_ty) = self.place(base)?;
                (root, id, self.field(target, &base_ty, name))
            }
            _ => {
                let span = self.span(target);
                self.error(codes::INVALID_ASSIGNMENT_TARGET, span, "only variables and their fields can be assigned");
                return None;
            }
        };
        self.record(target, ty.clone());
        Some((root, id, ty))
    }

    /// An expression whose only effect is its value, so it is not a statement on its own.
    /// Constructions and `with` are calls (REFERENCE §2, H3), which may be statements.
    fn is_bare_value(&self, e: ExprId) -> bool {
        matches!(
            &self.m.exprs[e].kind,
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
                | ExprKind::Is { .. }
                | ExprKind::Attempt(_)
                | ExprKind::Tuple(_)
                | ExprKind::It
        ) || matches!(self.m.exprs[e].kind, ExprKind::Else { value, .. } if self.is_bare_value(value))
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

    /// Checks a block whose value is unused. Returns `Never` if it always diverges, and the
    /// variable it waits on if it may (see [`Flow`]). With `tail`, the block ends a function
    /// that returns that type.
    fn block_stmt(&mut self, block: &Block, tail: Option<&Ty>) -> Ty {
        self.f.scopes.push(Vec::new());
        let flow = match tail {
            Some(ret) => self.tail_stmts(block, ret),
            None => self.stmts(&block.stmts),
        };
        self.f.scopes.pop();
        match flow {
            Flow::Leaves => Ty::Never,
            // How it ends may be in the code that is missing.
            _ if block.unclosed || block.lost => Ty::Error,
            Flow::Waits(v) => Ty::Var(v),
            Flow::Finishes => Ty::Unit,
        }
    }

    /// Checks a block used for its value: the final expression, if there is one, which is
    /// copied when `copying` says so. A block without one that waits on a variable (see
    /// [`Flow`]) is `Never` for now, and is reported once the variable settles if it can
    /// finish.
    fn block_value(&mut self, block: &Block, expected: Option<&Ty>, copying: bool) -> Ty {
        let m = self.m;
        self.f.scopes.push(Vec::new());
        let mut flow = Flow::Finishes;
        let mut value = None;
        let count = block.stmts.len();
        // The last statement of a block that is never closed, or lost one, may not be its end,
        // so the expected type only guides it, and a mismatch isn't reported.
        let missing = block.unclosed || block.lost;
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == count
                && let StmtKind::Expr(e) = m.stmts[s].kind
            {
                self.copying = copying;
                // A block that gives `()` may end in an `if` without `else`, which is then the
                // statement §6.2 makes it, as in a fallback that only sometimes leaves.
                if expected == Some(&Ty::Unit) && self.lacks_final_else(e) {
                    let ty = self.expr_stmt(e);
                    flow = self.then(flow, self.flow(&ty));
                    value = Some(Ty::Unit);
                    continue;
                }
                let ty = match expected {
                    Some(_) if missing => self.expr(e, expected),
                    Some(expected) => self.joined(e, expected),
                    None => self.infer(e),
                };
                // A value with an error stays one, so the branches it meets know it was
                // rejected (§15.1).
                if ty == Ty::Never {
                    flow = Flow::Leaves;
                }
                value = Some(ty);
                continue;
            }
            let next = self.stmt(s);
            flow = self.then(flow, next);
        }
        self.f.scopes.pop();
        let flow = self.now(flow);
        if flow == Flow::Leaves {
            return Ty::Never;
        }
        // Its value may have come from the code that is missing.
        if missing {
            return Ty::Error;
        }
        // A block without a final value gives `()`, which settles a type argument that
        // expected it (issue #10).
        match (value, expected) {
            (Some(ty), _) => ty,
            // Whether it leaves waits for the variable, so it gives no type for now, and is
            // reported then if it can finish (issue #30).
            (None, Some(expected))
                if let Flow::Waits(v) = flow
                    && !self.takes_unit(expected) =>
            {
                let must = Must::Value { expected: expected.clone(), span: block.span.end() };
                self.pending.push(Pending::Leaves { ty: Ty::Var(v), must });
                Ty::Never
            }
            (None, Some(expected)) if !self.vars.subsume(expected, &Ty::Unit) => {
                self.ends_without_value(expected, block.span.end());
                Ty::Error
            }
            (None, _) => Ty::Unit,
        }
    }

    // ---- expressions ----

    fn infer(&mut self, e: ExprId) -> Ty {
        self.expr(e, None)
    }

    /// Infers the type of `e`, a part of an expression that was rejected, which was the one
    /// to give the type arguments `e` leaves open, so they are not reported again (§15.1).
    fn rejected_value(&mut self, e: ExprId) -> Ty {
        let ty = self.infer(e);
        self.vars.quiet(&ty);
        ty
    }

    /// [`Checker::rejected_value`] for each argument of a rejected call.
    fn rejected_args(&mut self, args: &[Arg]) {
        for arg in args {
            self.rejected_value(arg.value);
        }
    }

    /// Checks `e` against `expected`, reports a mismatch, and returns the actual type.
    fn check(&mut self, e: ExprId, expected: &Ty) -> Ty {
        let actual = self.expr(e, Some(expected));
        if !self.vars.subsume(expected, &actual) {
            let span = self.span(e);
            let message = format!("expected `{}`, found `{}`", self.show(expected), self.show(&actual));
            self.error(codes::TYPE_MISMATCH, span, message);
            // What the value leaves open has no other way to be given, and what the expected
            // type leaves open may have been the value's to give (§15.1).
            self.vars.poison(&actual);
            self.vars.quiet(expected);
        }
        self.vars.resolve(&actual)
    }

    /// Infers the type of `e`. `expected` guides literals, variants, calls and branches, but
    /// mismatches against it are reported by [`Checker::check`]. A `Never` in it stands for
    /// a type the value may widen, as a field widens it (OPEN_QUESTIONS P5).
    fn expr(&mut self, e: ExprId, expected: Option<&Ty>) -> Ty {
        let chain = std::mem::replace(&mut self.in_chain, false);
        let copying = std::mem::replace(&mut self.copying, false);
        let expected = expected.map(|ty| {
            let ty = self.vars.resolve(ty);
            if self.vars.shape(&ty).never { self.vars.open_nevers(&ty) } else { ty }
        });
        let ty = self.expr_kind(e, expected.as_ref(), chain, copying);
        let ty = self.vars.resolve(&ty);
        if copying {
            self.copied(e, &ty);
        }
        self.record(e, ty.clone());
        ty
    }

    /// Writes `ty` as the type of `e`. One with a variable in it is zonked when the body is
    /// settled, so the interpreter never sees the variable.
    fn record(&mut self, e: ExprId, ty: Ty) {
        if self.vars.count() > 0 && self.vars.has_var(&ty) {
            self.typed.push(e);
        }
        self.p.expr_ty.insert(e, ty);
    }

    /// Reports a copy of a borrowed value whose type has a type parameter that isn't `Copy`,
    /// such as `x` or `o` in `return x` or `let y = o` (REFERENCE §4.8).
    fn copied(&mut self, e: ExprId, ty: &Ty) {
        // Only a generic function's types mention type parameters, and the borrowed place is
        // the cheap test, so a deep type is walked only where it can matter.
        if self.f.bounds.is_empty() || !self.borrowed_place(e) {
            return;
        }
        let ty = &self.vars.zonk(ty);
        let Some(param) = self.uncopyable(ty) else { return };
        let message = match self.f.anonymous.get(param as usize).cloned().flatten() {
            Some((name, iface)) => format!(
                "this copies a borrowed `{}`, which needs `Copy`; pass it on instead, or declare the parameter as `[T: {iface} + Copy]({name}: T)` (§4.8)",
                self.show(ty)
            ),
            None => {
                let name = self.param_names.get(param as usize).cloned().unwrap_or_else(|| "_".into());
                format!(
                    "this copies a borrowed `{}`, which needs `{name}: Copy`; pass it on instead, or add the constraint (§4.8)",
                    self.show(ty)
                )
            }
        };
        let span = self.span(e);
        self.error(codes::NOT_COPYABLE, span, message);
    }

    /// A type parameter in `ty` that isn't `Copy`.
    fn uncopyable(&self, ty: &Ty) -> Option<u32> {
        match ty {
            Ty::Param(i) if !self.f.bounds.get(*i as usize).is_some_and(|b| b.contains(&IfaceId::COPY)) => Some(*i),
            Ty::Adt(_, args) => args.iter().find_map(|arg| self.uncopyable(arg)),
            _ => None,
        }
    }

    /// Whether `e` is a parameter, a part of one bound by a pattern, or a field of either.
    fn borrowed_place(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) => matches!(self.p.res(e), Some(Res::Local(id)) if self.f.locals[id.index()].borrowed),
            ExprKind::Field { base, .. } => matches!(self.p.res(e), Some(Res::Field(_))) && self.borrowed_place(base),
            _ => false,
        }
    }

    /// Whether the value of `e` may be a borrowed value: a borrowed place, or an `if` or
    /// `match` with a branch whose value may be one. Copying an `if` or `match` copies the
    /// value of each branch, which [`Checker::copied`] checks there, so only a pattern that
    /// matches the value asks this (OPEN_QUESTIONS P5).
    fn borrowed_value(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::If { .. } | ExprKind::Match { .. } | ExprKind::Else { .. } => self.borrowed_values.contains(&e),
            _ => self.borrowed_place(e),
        }
    }

    /// Whether a branch whose block ends with `tail` may have a borrowed value.
    fn borrowed_tail(&self, tail: Option<ExprId>) -> bool {
        tail.is_some_and(|tail| self.borrowed_value(tail))
    }

    /// The expression a block ends with, which is its value.
    fn tail(&self, block: &Block) -> Option<ExprId> {
        let &last = block.stmts.last()?;
        match self.m.stmts[last].kind {
            StmtKind::Expr(e) => Some(e),
            _ => None,
        }
    }

    fn expr_kind(&mut self, e: ExprId, expected: Option<&Ty>, chain: bool, copying: bool) -> Ty {
        let m = self.m;
        let span = self.span(e);
        match &m.exprs[e].kind {
            ExprKind::Int(value) => self.int_literal(*value, false, expected, span),
            ExprKind::Float(text) => {
                let ft = match expected {
                    Some(Ty::Float(ft)) => *ft,
                    Some(Ty::Var(v)) if self.vars.open(*v).is_some_and(|open| open.kind != Kind::Int) => {
                        let ty = match self.vars.open(*v).map(|open| open.kind) {
                            Some(Kind::Float) => Ty::Var(*v),
                            _ => self.vars.fresh(Kind::Float, Origin::Defaulted),
                        };
                        self.pending.push(Pending::Float { ty: ty.clone(), lit: e });
                        return ty;
                    }
                    None => {
                        let ty = self.vars.fresh(Kind::Float, Origin::Defaulted);
                        self.pending.push(Pending::Float { ty: ty.clone(), lit: e });
                        return ty;
                    }
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
                        let ty = self.force(&ty);
                        if !self.implements(&ty, IfaceId::SHOW) && !ty.is_unknown() {
                            let span = self.span(*x);
                            self.error(
                                codes::UNSUPPORTED_OPERATOR,
                                span,
                                format!("`{}` does not implement `Show`, so it cannot be interpolated", self.show(&ty)),
                            );
                        }
                    }
                }
                Ty::Text
            }
            ExprKind::Name(name) => self.name(e, *name, expected),
            ExprKind::Call { callee, targs, args } => {
                self.call(e, *callee, targs.as_deref(), args, span, chain, expected)
            }
            ExprKind::MethodCall { receiver, method, targs, args } => {
                self.method_call(e, *receiver, *method, targs.as_deref(), args, span, chain, expected)
            }
            ExprKind::Field { base, name } => {
                if let Some(id) = self.enum_named(*base) {
                    return self.unit_variant(e, id, *name, expected);
                }
                self.in_chain = chain;
                let base_ty = self.infer(*base);
                let base_ty = self.force(&base_ty);
                self.field(e, &base_ty, *name)
            }
            ExprKind::Unary { op: UnaryOp::Not, operand } => {
                self.check(*operand, &Ty::Bool);
                Ty::Bool
            }
            ExprKind::Unary { op: UnaryOp::Neg, operand } => self.negate(*operand, expected, span),
            ExprKind::Binary { op: BinOp::And, .. } => {
                self.f.scopes.push(Vec::new());
                self.condition(e);
                self.f.scopes.pop();
                Ty::Bool
            }
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, *lhs, *rhs, expected, span),
            ExprKind::Range { .. } => {
                self.not_implemented(span, "ranges outside `for` loops", Planned::Phase(2));
                Ty::Error
            }
            ExprKind::Try(inner) => self.try_expr(*inner, expected, span),
            ExprKind::Attempt(inner) => self.attempt_expr(e, *inner, expected, span),
            ExprKind::Fail(value) => {
                self.copying = true;
                match self.f.fails.clone() {
                    Some(err) => {
                        self.check(*value, &err);
                    }
                    None => {
                        self.rejected_value(*value);
                        let message = if self.f.returns {
                            "`fail` needs a `fails` clause, and this function declares none"
                        } else if self.f.example {
                            "`fail` in an example, which has no function to fail"
                        } else {
                            "`fail` in a `where` clause, which has no function to fail"
                        };
                        self.error(codes::FAIL_WITHOUT_FAILS, span, message);
                    }
                }
                Ty::Never
            }
            ExprKind::If { .. } => {
                self.tail_copying = copying;
                self.if_expr(e, Mode::Value(expected))
            }
            ExprKind::Match { .. } => {
                self.tail_copying = copying;
                self.match_expr(e, Mode::Value(expected))
            }
            ExprKind::Is { value, pat } => {
                self.f.scopes.push(Vec::new());
                self.is_test(*value, *pat);
                self.f.scopes.pop();
                Ty::Bool
            }
            ExprKind::While { label, cond, body } => {
                // The bindings of an `is` in the condition scope over the body (OPEN_QUESTIONS P5).
                self.f.scopes.push(Vec::new());
                self.condition(*cond);
                self.loop_body(e, *label, body);
                self.f.scopes.pop();
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
            // What the hole meets may be given its type by the code that fills it (Q25).
            ExprKind::Todo(_) if self.opts.incomplete => {
                if let Some(expected) = expected {
                    self.vars.hole(expected);
                }
                Ty::Never
            }
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
            ExprKind::Tuple(elements) => self.tuple(elements, expected),
            ExprKind::Else { value, fallback } => self.else_expr(e, *value, fallback, expected, copying),
            ExprKind::It => match self.its.last() {
                Some(&id) => {
                    self.p.res.insert(e, Res::Local(id));
                    self.f.locals[id.index()].ty.clone()
                }
                None => {
                    let message = if self.option_fallbacks > 0 {
                        "`it` is the error of a call that can fail, and an `Option` has none (Q33)"
                    } else {
                        "`it` exists only in the fallback of an `else` form on a call that can fail (Q33)"
                    };
                    self.error(codes::UNKNOWN_NAME, span, message);
                    Ty::Error
                }
            },
            ExprKind::Error => Ty::Error,
        }
    }

    /// `(a, b)`. A tuple stores its elements, so it copies them (REFERENCE §4.8). An element
    /// takes its type from the expected one, which reports a mismatch at the element.
    fn tuple(&mut self, elements: &[ExprId], expected: Option<&Ty>) -> Ty {
        let expected_args = match expected {
            Some(Ty::Adt(id, args)) if self.p.decls.adt(*id).tuple && args.len() == elements.len() => {
                Some(args.clone())
            }
            _ => None,
        };
        let mut tys = Vec::new();
        for (i, &element) in elements.iter().enumerate() {
            self.copying = true;
            // A mismatch is reported at the element, not again for the whole tuple.
            let ty = match expected_args.as_ref().map(|args| &args[i]) {
                Some(expected) => self.joined(element, expected),
                None => self.infer(element),
            };
            tys.push(ty);
        }
        // An element with an error gives the tuple a part that a later value may still give a
        // type, so a tuple that meets another is not reported again. It gives the others no
        // type, so what they leave open is still reported (§15.1; issue #30).
        let tys = tys.into_iter().map(|ty| if ty == Ty::Error { self.vars.rejected() } else { ty }).collect();
        self.p.decls.tuple_ty(tys)
    }

    /// Marks the type arguments that `tys` leave open as a rejected value's when one of them
    /// is an error: the branches of an `if` or `match`, one of which may have given them
    /// (§15.1).
    fn rejected_parts(&mut self, tys: &[Ty]) {
        if tys.contains(&Ty::Error) {
            tys.iter().for_each(|ty| self.vars.quiet(ty));
        }
    }

    /// `value else fallback` (REFERENCE §6.6). It marks the fallible calls of `value`'s chain,
    /// as `try` does, and their failure runs the fallback with the error as `it`. Without
    /// one, `value` is an `Option`, which it unwraps (OPEN_QUESTIONS P5). The unwrapped type
    /// and the fallback's are joined, so either may give the other its type arguments and
    /// literal types, and so may the type the form is expected to have (issue #10).
    fn else_expr(&mut self, e: ExprId, value: ExprId, fallback: &Fallback, expected: Option<&Ty>, copying: bool) -> Ty {
        self.markers.push(Marker { handler: Some(e), errors: Vec::new() });
        self.in_chain = true;
        self.copying = copying;
        let value_ty = self.expr(value, None);
        let errors = self.markers.pop().map(|m| m.errors).unwrap_or_default();
        let span = self.span(e);
        let hole = self.met_hole(&errors);
        let it = match self.one_error(errors, span, "`else`", "`it` has one type") {
            // It may have been a call that can fail, so `it` is not reported again (§15.1).
            None if value_ty == Ty::Error => Some(Ty::Error),
            it => it,
        };
        if let Some(err) = &it
            && value_ty != Ty::Error
            && !hole
        {
            self.wait_can_fail(err, Handler::Else, span);
        }
        let unwrapped = match (&it, &value_ty) {
            (Some(_), ty) => ty.clone(),
            (None, Ty::Adt(AdtId::OPTION, args)) => self.vars.resolve(&args[0]),
            (None, ty) if ty.is_unknown() => ty.clone(),
            (None, ty) => {
                let hint = match ty {
                    Ty::Adt(AdtId::RESULT, _) => "; match a `Result` instead",
                    _ => "",
                };
                let message = format!(
                    "`else` needs an `Option` or a call that can fail on its left, but this is a `{}`{hint}",
                    self.show(ty)
                );
                self.error(codes::NOTHING_TO_UNWRAP, span, message);
                Ty::Error
            }
        };
        match &it {
            Some(err) => {
                let id = LocalId(self.f.locals.len() as u32);
                self.f.locals.push(Local { ty: err.clone(), mutable: false, borrowed: false });
                self.p.it_local.insert(e, id);
                self.its.push(id);
            }
            None => self.option_fallbacks += 1,
        }
        // The form's own expected type gives the fallback its type when the value doesn't.
        let expected = match &unwrapped {
            Ty::Never => expected.cloned().filter(|ty| !ty.is_unknown()),
            ty => Some(ty.clone()),
        };
        let expected = expected.as_ref();
        let (fallback_ty, tail) = match fallback {
            Fallback::Value(x) => {
                self.copying = copying;
                let ty = match expected {
                    Some(expected) => self.joined(*x, expected),
                    None => self.infer(*x),
                };
                (ty, Some(*x))
            }
            Fallback::Block(block) => (self.block_value(block, expected, copying), self.tail(block)),
        };
        match &it {
            Some(_) => {
                self.its.pop();
            }
            None => self.option_fallbacks -= 1,
        }
        if (it.is_none() && self.borrowed_value(value)) || self.borrowed_tail(tail) {
            self.borrowed_values.insert(e);
        }
        match (&unwrapped, &fallback_ty) {
            (Ty::Never, ty) => ty.clone(),
            (ty, Ty::Never | Ty::Error) => ty.clone(),
            // The fallback's value was joined with the unwrapped one, which it may widen.
            (_, ty) => ty.clone(),
        }
    }

    /// The one error type of the fallible calls a `try`, `attempt`, `else` form or example
    /// marks, which a variable not known yet joins. Several are an error (E0301), since
    /// the error they give has one type. `None` when they mark none.
    fn one_error(&mut self, errors: Vec<Ty>, span: Span, what: &str, why: &str) -> Option<Ty> {
        let mut errors = errors.into_iter();
        let mut one = errors.next()?;
        for err in errors {
            if one == Ty::Error || err == Ty::Error {
                self.vars.poison(&one);
                self.vars.poison(&err);
                one = Ty::Error;
            } else if self.vars.subsume(&one, &err) && self.vars.subsume(&err, &one) {
                one = self.vars.zonk(&one);
            } else {
                let message = format!(
                    "the calls this {what} marks fail with `{}` and `{}`, but {why}",
                    self.show(&one),
                    self.show(&err)
                );
                self.error(codes::TYPE_MISMATCH, span, message);
                self.vars.poison(&one);
                self.vars.poison(&err);
                return Some(Ty::Error);
            }
        }
        Some(self.vars.resolve(&one))
    }

    /// An integer literal takes the type it meets (REFERENCE §2). One that meets nothing
    /// known yet is a variable, whose range is checked once the statement settles it.
    fn int_literal(&mut self, magnitude: u128, negative: bool, expected: Option<&Ty>, span: Span) -> Ty {
        let it = match expected {
            Some(Ty::Int(it)) => *it,
            Some(Ty::Var(v)) if self.vars.open(*v).is_some_and(|open| open.kind != Kind::Float) => {
                let ty = match self.vars.open(*v).map(|open| open.kind) {
                    Some(Kind::Int) => Ty::Var(*v),
                    _ => self.vars.fresh(Kind::Int, Origin::Defaulted),
                };
                self.pending.push(Pending::Int { ty: ty.clone(), magnitude, negative, span });
                return ty;
            }
            None => {
                let ty = self.vars.fresh(Kind::Int, Origin::Defaulted);
                self.pending.push(Pending::Int { ty: ty.clone(), magnitude, negative, span });
                return ty;
            }
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
        self.int_range(it, magnitude, negative, span);
        Ty::Int(it)
    }

    /// Reports an integer literal that doesn't fit `it`.
    fn int_range(&mut self, it: IntTy, magnitude: u128, negative: bool, span: Span) {
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
    }

    fn negate(&mut self, operand: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        // A negative integer literal is one value, so `-128` fits in `Int8`.
        if let ExprKind::Int(value) = self.m.exprs[operand].kind {
            let ty = self.int_literal(value, true, expected, span);
            self.record(operand, ty.clone());
            return ty;
        }
        let ty = self.expr(operand, expected.filter(|t| t.is_numeric() || matches!(t, Ty::Var(_))));
        if let Ty::Var(v) = ty {
            // An integer that isn't known yet may turn out unsigned.
            if self.vars.open(v).is_some_and(|open| open.kind != Kind::Float) {
                self.pending.push(Pending::Neg { ty: ty.clone(), span });
            }
            return ty;
        }
        if self.negated(&ty, span) { ty } else { Ty::Error }
    }

    /// Reports unary `-` on a type that doesn't have it, and returns whether it does.
    fn negated(&mut self, ty: &Ty, span: Span) -> bool {
        match ty {
            Ty::Int(it) if it.is_signed() => true,
            Ty::Float(_) | Ty::Error | Ty::Never => true,
            // A rejected `impl` block may have been the type's `impl Neg` (§15.1).
            _ if self.unknown_interfaces(ty) => false,
            _ => {
                let message = format!("unary `-` is not defined for `{}`", self.show(ty));
                self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                false
            }
        }
    }

    /// Checks the operands of a binary operator and joins their types. An untyped literal
    /// takes its type from the other operand (REFERENCE §2), and so do `None` and a generic
    /// call, in either position, since what neither gives stays a variable until they meet
    /// (OPEN_QUESTIONS P5; issue #10). Returns the joined type, or an error once reported.
    fn operands(&mut self, lhs: ExprId, rhs: ExprId, hint: Option<&Ty>, span: Span) -> Ty {
        let lt = self.expr(lhs, hint);
        // An operand that already has an error gives the other no type, so a literal there
        // isn't reported again against it, and one of another kind gives none either.
        let other = match &lt {
            Ty::Error => None,
            ty if ty.is_numeric() || matches!(ty, Ty::Adt(..) | Ty::Var(_)) => Some(ty.clone()),
            _ => hint.cloned(),
        };
        let rt = self.expr(rhs, other.as_ref());
        match self.vars.join(&lt, &rt) {
            Some(ty) => ty,
            None => {
                let message = format!(
                    "mismatched operand types `{}` and `{}`; Proviso has no implicit conversions",
                    self.show(&lt),
                    self.show(&rt)
                );
                self.error(codes::TYPE_MISMATCH, span, message);
                self.vars.poison(&lt);
                self.vars.poison(&rt);
                Ty::Error
            }
        }
    }

    /// Reports arithmetic operator `op` on operands of type `ty` that don't have it, and
    /// returns whether they do. An integer or float not known yet has every operator its
    /// kind has, and a type argument not known yet waits for the statement to settle it.
    fn arithmetic(&mut self, op: BinOp, ty: &Ty, span: Span) -> bool {
        let defined = match ty {
            Ty::Var(v) => match self.vars.open(*v).map(|open| open.kind) {
                Some(Kind::Int) => true,
                Some(Kind::Float) => op != BinOp::Rem,
                _ => {
                    self.pending.push(Pending::Arith { op, ty: ty.clone(), span });
                    true
                }
            },
            ty => arithmetic_defined(op, ty),
        };
        // A rejected `impl` block may have been the type's `impl Add` (§15.1).
        if !defined && !self.unknown_interfaces(ty) {
            let message = format!("`{}` is not defined for `{}`", op.symbol(), self.show(ty));
            self.error(codes::UNSUPPORTED_OPERATOR, span, message);
        }
        defined
    }

    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        let symbol = op.symbol();
        match op {
            BinOp::And | BinOp::Or => {
                self.check(lhs, &Ty::Bool);
                self.check(rhs, &Ty::Bool);
                Ty::Bool
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let hint = expected.filter(|t| t.is_numeric() || matches!(t, Ty::Var(_)));
                let ty = self.operands(lhs, rhs, hint, span);
                if self.arithmetic(op, &ty, span) { ty } else { Ty::Error }
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                // The operands' type goes nowhere else, so whatever they leave open is
                // settled here, before asking what it implements.
                let ty = self.operands(lhs, rhs, None, span);
                let ty = self.force(&ty);
                let defined = match op {
                    // Floats have IEEE `==` and `<` without implementing `Eq` or `Ord` (REFERENCE §12.2).
                    BinOp::Eq | BinOp::Ne => matches!(ty, Ty::Float(_)) || self.implements(&ty, IfaceId::EQ),
                    _ => matches!(ty, Ty::Float(_)) || self.implements(&ty, IfaceId::ORD),
                };
                if !defined && !ty.is_unknown() {
                    let message = format!("`{symbol}` is not defined for `{}`", self.show(&ty));
                    self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                }
                Ty::Bool
            }
        }
    }

    fn name(&mut self, e: ExprId, name: Ident, expected: Option<&Ty>) -> Ty {
        let m = self.m;
        let text = m.text(name.sym);
        if let Some(id) = self.lookup_local(name.sym) {
            self.p.res.insert(e, Res::Local(id));
            return self.f.locals[id.index()].ty.clone();
        }
        // A module item that reuses a variant's name has been reported, and so are its uses.
        if let Some(id) = bare_variant(text) {
            if self.poisoned.contains(&name.sym) {
                return Ty::Error;
            }
            return self.unit_variant(e, id, name, expected);
        }
        if self.fn_names.contains_key(&name.sym) {
            self.not_implemented(name.span, "functions used as values", Planned::Phase(2));
        } else if self.unqualified_variant(name) || self.poisoned.contains(&name.sym) {
        } else if self.imports.contains_key(&name.sym)
            || self.adt_named(name.sym).is_some()
            || self.iface_names.contains_key(&name.sym)
            || prelude_type(text)
        {
            self.error(codes::UNKNOWN_NAME, name.span, format!("`{text}` is a type or module, not a value"));
        } else if text == "self" {
            self.error(codes::UNKNOWN_NAME, name.span, "`self` exists only in a method, which takes it first");
        } else {
            self.error(codes::UNKNOWN_NAME, name.span, format!("unknown name `{text}`"));
        }
        Ty::Error
    }

    #[allow(clippy::too_many_arguments)]
    fn call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        expected: Option<&Ty>,
    ) -> Ty {
        let m = self.m;
        if let Some(id) = self.fn_named(callee) {
            self.p.res.insert(callee, Res::Fn(id));
            return self.fn_call(e, id, targs, args, span, chain, expected);
        }
        // A variant or record takes no type arguments. A name that resolves to nothing or to
        // a rejected declaration may have, and a call of a local is a later phase's (§15.1).
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && !self.poisoned.contains(&name.sym)
            && self.lookup_local(name.sym).is_none()
            && (bare_variant(m.text(name.sym)).is_some() || self.adt_named(name.sym).is_some())
        {
            self.no_targs(targs, m.text(name.sym), span);
        }
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && self.lookup_local(name.sym).is_none()
            && let Some(id) = bare_variant(m.text(name.sym))
        {
            if self.poisoned.contains(&name.sym) {
                self.rejected_args(args);
                return Ty::Error;
            }
            return self.construct_variant(callee, id, name, args, span, expected);
        }
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && let Some(id) = self.adt_named(name.sym)
        {
            if self.p.decls.adt(id).is_enum() {
                let text = m.text(name.sym);
                let message = format!("`{text}` is an enum; build one of its variants, as in `{text}.Variant(…)`");
                self.error(codes::UNKNOWN_NAME, name.span, message);
                self.rejected_args(args);
                return Ty::Error;
            }
            return self.construct(callee, id, args, span);
        }
        let callee_span = self.span(callee);
        match m.exprs[callee].kind {
            ExprKind::Name(name) if self.lookup_local(name.sym).is_some() => {
                self.not_implemented(callee_span, "calls of function values", Planned::Phase(2))
            }
            ExprKind::Name(name) if self.unqualified_variant(name) => {}
            ExprKind::Name(name) if self.poisoned.contains(&name.sym) => {}
            // Phase 3 gives `System` the rest of its fields (REFERENCE §9.1).
            ExprKind::Name(name) if m.text(name.sym) == "System" => {
                self.not_implemented(callee_span, "constructions of `System`", Planned::Phase(3))
            }
            ExprKind::Name(name) if builtin_type(m.text(name.sym)).is_some() => {
                self.not_implemented(callee_span, "conversions such as `Int64(x)`", Planned::Phase(2))
            }
            ExprKind::Name(name) => {
                let text = m.text(name.sym);
                self.error(codes::UNKNOWN_NAME, name.span, format!("unknown function `{text}`"));
            }
            _ => self.not_implemented(callee_span, "calls of function values", Planned::Phase(2)),
        }
        self.rejected_args(args);
        Ty::Error
    }

    /// The module function that `callee` names. A variant of the prelude is never one, even
    /// when a wrongly cased function has its name.
    fn fn_named(&self, callee: ExprId) -> Option<FnId> {
        let ExprKind::Name(name) = self.m.exprs[callee].kind else { return None };
        if bare_variant(self.m.text(name.sym)).is_some() {
            return None;
        }
        self.fn_names.get(&name.sym).copied()
    }

    /// Reports explicit type arguments given to `what`, which takes none.
    fn no_targs(&mut self, targs: Option<&[TypeId]>, what: &str, span: Span) {
        let Some(targs) = targs else { return };
        let m = self.m;
        let span = match (targs.first(), targs.last()) {
            (Some(&first), Some(&last)) => m.types[first].span.to(m.types[last].span),
            _ => span,
        };
        self.error(codes::TYPE_ARGUMENT_COUNT, span, format!("`{what}` takes no type arguments"));
    }

    /// A call of function `f`, a module's or a method. Its type arguments come from
    /// `targs`, or else from the type the call is expected to have and then from the
    /// arguments, and each must implement its parameter's constraints (REFERENCE §4.8;
    /// OPEN_QUESTIONS P5).
    #[allow(clippy::too_many_arguments)]
    fn fn_call(
        &mut self,
        e: ExprId,
        f: FnId,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        expected: Option<&Ty>,
    ) -> Ty {
        let m = self.m;
        let info = &self.p.fns[f];
        if info.rejected {
            self.rejected_args(args);
            return Ty::Error;
        }
        let name = m.text(info.name);
        let params: Vec<(&str, Ty)> = info.params.iter().map(|p| (m.text(p.name), p.ty.clone())).collect();
        let (ret, fails) = (info.ret.clone(), info.fails.clone());
        let generics: Vec<(Box<str>, Vec<IfaceId>)> =
            info.generics.iter().map(|g| (g.name.clone(), g.bounds.clone())).collect();
        // A parameter whose declaration or constraint is rejected stands for an unknown type,
        // and any other is a variable until `::[…]`, the expected type or an argument gives it.
        let rejected: Vec<bool> = info.generics.iter().map(|g| g.rejected).collect();
        let mut tvars: Vec<Option<Ty>> = rejected.iter().map(|&rejected| rejected.then_some(Ty::Error)).collect();
        // `::[…]` gives the declared parameters, which come before those of interface types.
        let declared = info.generics.iter().filter(|g| g.param.is_none()).count();
        // A parameter declared twice may have been meant as one, so a count without it is
        // also right.
        let duplicates = info.generics.iter().filter(|g| g.sym.is_none() && g.param.is_none()).count();
        if let Some(targs) = targs {
            let tys: Vec<Ty> = targs.iter().map(|&t| self.resolve_type(t)).collect();
            let fewest = declared - duplicates;
            if tys.len() != declared && (fewest..declared).contains(&tys.len()) {
                tvars.fill(Some(Ty::Error));
            } else if tys.len() != declared {
                let at = match (targs.first(), targs.last()) {
                    (Some(&first), Some(&last)) => m.types[first].span.to(m.types[last].span),
                    _ => span,
                };
                let message = match (declared, tys.len() < fewest) {
                    (0, _) => format!("`{name}` takes no type arguments"),
                    (n, short) => {
                        let verb = if tys.len() == 1 { "was" } else { "were" };
                        let n = if short { fewest } else { n };
                        format!("`{name}` takes {}, but {} {verb} given", type_args(n), tys.len())
                    }
                };
                self.error(codes::TYPE_ARGUMENT_COUNT, at, message);
                self.rejected_args(args);
                return Ty::Error;
            } else {
                for (slot, ty) in tvars.iter_mut().zip(tys) {
                    slot.get_or_insert(ty);
                }
            }
        }
        let tvars: Vec<Ty> = (tvars.into_iter().enumerate())
            .map(|(param, ty)| ty.unwrap_or_else(|| self.vars.fresh(Kind::Any, Origin::Call { f, param, span })))
            .collect();
        // The type the call is expected to have gives what it can first, so a mismatch is
        // reported at the argument (OPEN_QUESTIONS P5). A `Never` in it is known only in part,
        // and the arguments may widen it.
        if targs.is_none()
            && let Some(expected) = expected.filter(|t| !t.is_unknown())
        {
            self.vars.subsume(expected, &ret.subst(&tvars));
        }
        let counted = self.generic_args(name, &params, &tvars, args, span, false);
        // An expected type with an error may have given them, and arguments that don't
        // match their parameters leave them to nothing (§15.1).
        if expected == Some(&Ty::Error) || !counted {
            for ty in &tvars {
                self.vars.poison(ty);
            }
        }
        for (ty, (param, bounds)) in tvars.iter().zip(&generics) {
            let ty = self.vars.resolve(ty);
            if ty.is_unknown() {
                continue;
            }
            // One with a variable in it is checked once the statement settles it, which
            // also walks a deep argument once rather than at each call around it.
            if self.vars.has_var(&ty) {
                if !bounds.is_empty() {
                    let (ifaces, callee, param) = (bounds.clone(), name.into(), param.clone());
                    self.pending.push(Pending::Bound { ty: ty.clone(), ifaces, callee, param, span });
                }
                continue;
            }
            if let Some(&iface) = bounds.iter().find(|&&iface| !self.implements(&ty, iface)) {
                let message = format!(
                    "`{}` does not implement `{}`, which `{name}` needs of `{param}`",
                    self.show(&ty),
                    self.iface_name(iface)
                );
                self.error(codes::MISSING_IMPLEMENTATION, span, message);
            }
        }
        if let Some(err) = fails {
            self.fallible_call(e, name, &err.subst(&tvars), span, chain);
        }
        ret.subst(&tvars)
    }

    /// A record's constructor takes its fields as parameters, so a construction follows the
    /// rules of a call (REFERENCE §4.4). It stores its arguments, so it copies them.
    fn construct(&mut self, callee: ExprId, id: AdtId, args: &[Arg], span: Span) -> Ty {
        self.p.res.insert(callee, Res::Ctor(id, VariantIdx::RECORD));
        let def = self.p.decls.adt(id);
        let name = def.name.clone();
        let params: Vec<(Box<str>, Ty)> = def.variant().fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        self.generic_args(&name, &params, &[], args, span, true);
        Ty::adt(id)
    }

    #[allow(clippy::too_many_arguments)]
    fn method_call(
        &mut self,
        e: ExprId,
        receiver: ExprId,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        expected: Option<&Ty>,
    ) -> Ty {
        let m = self.m;
        let name = m.text(method.sym);
        if let Some(id) = self.enum_named(receiver)
            && (self.p.decls.adt(id).variant_named(name).is_some() || is_pascal(name))
        {
            if self.p.decls.adt(id).variant_named(name).is_some() {
                self.no_targs(targs, name, span);
            }
            return self.construct_variant(e, id, method, args, span, expected);
        }
        if let ExprKind::Name(receiver_name) = m.exprs[receiver].kind
            && self.lookup_local(receiver_name.sym).is_none()
        {
            if let Some(id) = self.adt_named(receiver_name.sym) {
                return self.associated_call(e, id, method, targs, args, span, chain, expected);
            }
            if let Some(iface) = self.iface_named(receiver_name.sym) {
                return self.iface_call(e, iface, method, targs, args, span, chain);
            }
            if let Some(ty) = builtin_type(m.text(receiver_name.sym)).filter(|ty| ty.is_numeric() || is_scalar(ty)) {
                return self.scalar_call(e, &ty, receiver_name, method, targs, args, span, chain);
            }
            let cap = self.names_cap(receiver_name.sym);
            if cap {
                let what = "calls of capability interface methods such as `Out.write_line(…)`";
                self.not_implemented(receiver_name.span, what, Planned::Phase(3));
            }
            // A rejected declaration may have had the name.
            if cap || self.poisoned.contains(&receiver_name.sym) {
                self.rejected_args(args);
                return Ty::Error;
            }
        }
        self.in_chain = chain;
        // Which method this is depends on the receiver's type, so it must be known here.
        let receiver_ty = self.infer(receiver);
        let receiver_ty = self.force(&receiver_ty);
        if let (Ty::Adt(id, _), "with") = (&receiver_ty, name)
            && !self.p.decls.adt(*id).is_enum()
            && !self.p.decls.adt(*id).tuple
        {
            self.no_targs(targs, name, span);
            self.p.res.insert(e, Res::With);
            self.with_args(e, *id, args, span);
            return receiver_ty;
        }
        // The `Text` methods of §12.3 that STD.md doesn't declare yet.
        let planned = match name {
            "lines" | "split" => Some(("that return a `List`", Planned::Phase(2))),
            "chars" | "find" | "find_last" | "slice" | "normalize_nfc" => Some(("of §12.3", Planned::Unscheduled)),
            _ => None,
        };
        if receiver_ty == Ty::Text
            && let Some((which, planned)) = planned
        {
            self.not_implemented(method.span, &format!("`Text` methods {which}, such as `{name}`,"), planned);
            self.rejected_args(args);
            return Ty::Error;
        }
        if let Some((builtin, params, ret, fails)) = builtin_method(&receiver_ty, name) {
            self.no_targs(targs, name, span);
            self.p.res.insert(e, Res::Method(builtin));
            self.args(name, &params, args, span);
            if let Some(err) = fails {
                self.fallible_call(e, name, &err, span, chain);
            }
            return ret;
        }
        match self.resolve_method(&receiver_ty, method) {
            Some(Callee::Fn(f)) => {
                self.p.res.insert(e, Res::Fn(f));
                self.fn_call(e, f, targs, args, span, chain, expected)
            }
            Some(Callee::Iface(iface, j)) => {
                self.dispatch_call(e, iface, j, &receiver_ty, method, targs, args, span, chain, false)
            }
            None => {
                self.rejected_args(args);
                Ty::Error
            }
        }
    }

    /// `Int.parse(text)`: an associated function of a scalar type (STD.md). Only the integer
    /// types have one, `parse`. The conversions of REFERENCE §12.1 come later.
    #[allow(clippy::too_many_arguments)]
    fn scalar_call(
        &mut self,
        e: ExprId,
        ty: &Ty,
        type_name: Ident,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
    ) -> Ty {
        let m = self.m;
        let (type_text, name) = (m.text(type_name.sym), m.text(method.sym));
        match (ty, name) {
            (Ty::Int(it), "parse") => {
                let callee = format!("{type_text}.parse");
                self.no_targs(targs, &callee, span);
                self.p.res.insert(e, Res::Method(Builtin::Parse(*it)));
                self.args(&callee, &[("text", Ty::Text)], args, span);
                self.fallible_call(e, &callee, &Ty::adt(AdtId::PARSE_ERROR), span, chain);
                return ty.clone();
            }
            (Ty::Int(_) | Ty::Float(_), "from" | "try_from" | "wrapping_from" | "saturating_from") => {
                let what = format!("numeric conversions such as `{type_text}.{name}`");
                self.not_implemented(span, &what, Planned::Unscheduled);
            }
            (Ty::Text, "from_utf8") => {
                self.not_implemented(span, "conversions from `Bytes`, such as `Text.from_utf8`,", Planned::Unscheduled);
            }
            _ => {
                let message = format!("`{type_text}` has no associated function `{name}`");
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
        }
        self.rejected_args(args);
        Ty::Error
    }

    /// The method `x.name(…)` calls on a value of type `ty`: one of the type's own, or one of
    /// an interface it implements, which must be the only one (REFERENCE §3). Reports a
    /// call that resolves to none or to several.
    fn resolve_method(&mut self, ty: &Ty, method: Ident) -> Option<Callee> {
        let m = self.m;
        let name = m.text(method.sym);
        if *ty == Ty::Error {
            return None;
        }
        let mut found: Vec<Callee> = Vec::new();
        if let Ty::Adt(id, _) = ty
            && let Some(entries) = self.inherent.get(id)
        {
            let mut named = entries.iter().filter(|e| e.name == method.sym);
            // A rejected declaration of the name, a duplicate or one named like an interface's
            // method, may be the one the call means, and it has been reported (§15.1).
            if named.clone().any(|e| e.rejected) {
                return None;
            }
            if let Some(entry) = named.next() {
                found.push(Callee::Fn(entry.f));
            }
        }
        // A rejected `impl` block or method declaration may have declared the method.
        let mut unknown = self.p.decls.unknown_methods(ty) || self.unknown_tys.contains(ty);
        // A rejected `derives` entry or `impl` block makes the type implement every interface,
        // so only its own method is known to exist.
        let interfaces_known = !self.unknown_interfaces(ty);
        unknown |= !interfaces_known;
        for (iface, def) in self.p.decls.ifaces() {
            if !self.implements(ty, iface) || (!interfaces_known && !found.is_empty()) {
                continue;
            }
            unknown |= def.incomplete;
            if let Some(j) = def.method(name) {
                found.push(Callee::Iface(iface, j));
            }
        }
        match found.as_slice() {
            [] => {
                if !unknown {
                    let message = format!("`{}` has no method `{name}`", self.show(ty));
                    self.error(codes::UNKNOWN_MEMBER, method.span, message);
                }
                None
            }
            [Callee::Fn(f)] if self.p.fns[*f].receiver.is_none() => {
                let message = format!(
                    "`{name}` is an associated function, so it is called on the type, as in `{}.{name}(…)`",
                    self.show(ty)
                );
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
                None
            }
            [Callee::Iface(IfaceId::ORD, _)] => {
                self.not_implemented(method.span, "`cmp` and the `Ordering` it returns", Planned::Phase(2));
                None
            }
            [callee] => Some(*callee),
            _ if unknown => None,
            _ => {
                let owners: Vec<String> = (found.iter())
                    .filter_map(|callee| match callee {
                        Callee::Iface(iface, _) => Some(format!("`{}`", self.iface_name(*iface))),
                        Callee::Fn(_) => None,
                    })
                    .collect();
                let message = format!(
                    "`{}` has more than one method `{name}`, from {}; call one as `{}.{name}(…)` (§3)",
                    self.show(ty),
                    owners.join(" and "),
                    owners[0].trim_matches('`')
                );
                self.error(codes::AMBIGUOUS_METHOD, method.span, message);
                None
            }
        }
    }

    /// `Span.unit(…)`: an associated function, which takes no `self` (REFERENCE §3).
    #[allow(clippy::too_many_arguments)]
    fn associated_call(
        &mut self,
        e: ExprId,
        adt: AdtId,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        expected: Option<&Ty>,
    ) -> Ty {
        let name = self.m.text(method.sym);
        let def = self.p.decls.adt(adt);
        let entries = self.inherent.get(&adt).map_or(&[][..], Vec::as_slice);
        // A rejected declaration of the name may be the one the call means, and it has been
        // reported (§15.1).
        let rejected = entries.iter().any(|entry| entry.name == method.sym && entry.rejected);
        match entries.iter().find(|entry| entry.name == method.sym).map(|entry| entry.f) {
            Some(_) if rejected => {}
            Some(f) if self.p.fns[f].receiver.is_none() => {
                self.p.res.insert(e, Res::Fn(f));
                return self.fn_call(e, f, targs, args, span, chain, expected);
            }
            Some(_) => {
                let message =
                    format!("`{name}` is a method, so it is called on a value of `{}`, as in `x.{name}(…)`", def.name);
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
            None if def.unknown_methods => {}
            // A record with refinements gets a validator (REFERENCE §4.4).
            None if name == "validate" && !def.is_enum() && def.variants.iter().any(|v| !v.preds.is_empty()) => {
                let what = format!("generated validators such as `{}.validate`", def.name);
                self.not_implemented(span, &what, Planned::Phase(2));
            }
            None => {
                let message = format!("`{}` has no associated function `{name}`", def.name);
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
        }
        self.rejected_args(args);
        Ty::Error
    }

    /// The interface that `sym` names, the module's or the prelude's.
    fn iface_named(&self, sym: Symbol) -> Option<IfaceId> {
        if self.poisoned.contains(&sym) {
            return None;
        }
        self.iface_names.get(&sym).copied().or_else(|| IfaceId::prelude(self.m.text(sym)))
    }

    /// `I.f(x, …)`, which calls `I`'s method on `x`, unlabelled (REFERENCE §3, H3).
    #[allow(clippy::too_many_arguments)]
    fn iface_call(
        &mut self,
        e: ExprId,
        iface: IfaceId,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
    ) -> Ty {
        let name = self.m.text(method.sym);
        let iface_text = self.iface_name(iface).to_string();
        let def = self.p.decls.iface(iface);
        let found = def.method(name);
        let rejected = match found {
            None if iface.methods_later() => {
                self.not_implemented(method.span, &format!("calls of `{iface_text}`'s methods"), Planned::Phase(2));
                true
            }
            None if def.incomplete => true,
            None => {
                let message = format!("`{iface_text}` has no method `{name}`");
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
                true
            }
            Some(_) if iface == IfaceId::ORD => {
                self.not_implemented(method.span, "`cmp` and the `Ordering` it returns", Planned::Phase(2));
                true
            }
            Some(_) => false,
        };
        let (Some(j), Some((first, rest)), false) = (found, args.split_first(), rejected) else {
            if !rejected {
                let message = format!("`{iface_text}.{name}` takes its receiver first, as in `{iface_text}.{name}(x)`");
                self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            }
            self.rejected_args(args);
            return Ty::Error;
        };
        if let Some(label) = first.label {
            let message = format!("the receiver of `{iface_text}.{name}` takes no label (H3)");
            self.error(codes::WRONG_LABEL, label.span, message);
        }
        let receiver_ty = self.infer(first.value);
        let receiver_ty = self.force(&receiver_ty);
        if !receiver_ty.is_unknown() && !self.implements(&receiver_ty, iface) {
            let message = format!("`{}` does not implement `{iface_text}`", self.show(&receiver_ty));
            let at = self.span(first.value);
            self.error(codes::MISSING_IMPLEMENTATION, at, message);
            self.rejected_args(rest);
            return Ty::Error;
        }
        self.dispatch_call(e, iface, j, &receiver_ty, method, targs, rest, span, chain, true)
    }

    /// A call of method `j` of `iface` on a receiver of type `receiver_ty`, with `Self` read
    /// as that type. The implementation for the receiver's value runs it (REFERENCE §4.9).
    #[allow(clippy::too_many_arguments)]
    fn dispatch_call(
        &mut self,
        e: ExprId,
        iface: IfaceId,
        j: usize,
        receiver_ty: &Ty,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        qualified: bool,
    ) -> Ty {
        let name = self.m.text(method.sym);
        self.no_targs(targs, name, span);
        let def = &self.p.decls.iface(iface).methods[j];
        let receiver = [receiver_ty.clone()];
        let params: Vec<(Box<str>, Ty)> = def.params.iter().map(|(n, t)| (n.clone(), t.subst(&receiver))).collect();
        let ret = def.ret.subst(&receiver);
        let fails = def.fails.as_ref().map(|t| t.subst(&receiver));
        self.p.res.insert(e, Res::Dispatch { iface, method: j, qualified });
        self.args(name, &params, args, span);
        if let Some(err) = fails {
            self.fallible_call(e, name, &err, span, chain);
        }
        ret
    }

    fn field(&mut self, e: ExprId, base_ty: &Ty, name: Ident) -> Ty {
        let text = self.m.text(name.sym);
        if let Ty::Adt(id, _) = base_ty
            && let Some((i, field)) = self.p.decls.adt(*id).field(text)
        {
            let ty = field.ty.clone();
            self.p.res.insert(e, Res::Field(i));
            return ty;
        }
        match (base_ty, text) {
            (Ty::Adt(AdtId::SYSTEM, _), text) if LATER_SYSTEM_FIELDS.contains(&text) => {
                self.not_implemented(
                    name.span,
                    &format!("`System` fields other than `stdout`, such as `{text}`,"),
                    Planned::Phase(3),
                );
                Ty::Error
            }
            (Ty::Error, _) => Ty::Error,
            (ty, _) => {
                let message = format!("`{}` has no field `{text}`", self.show(ty));
                self.error(codes::UNKNOWN_MEMBER, name.span, message);
                Ty::Error
            }
        }
    }

    /// Checks the arguments of `with`. They label the fields they replace, at least one, once
    /// each and in declaration order, even on a one-field record (OPEN_QUESTIONS P5). One
    /// label problem is reported per call.
    fn with_args(&mut self, e: ExprId, id: AdtId, args: &[Arg], span: Span) {
        let m = self.m;
        let def = self.p.decls.adt(id);
        let record = def.name.clone();
        let fields: Vec<(Box<str>, Ty)> = def.variant().fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        if args.is_empty() {
            let message = format!("`with` names at least one field of `{record}` to replace");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            return;
        }
        let labelled = fields.iter().map(|(name, _)| format!("{name}: …")).collect::<Vec<_>>().join(", ");
        let mut replaced: Vec<FieldIdx> = Vec::new();
        let mut labels_reported = false;
        for arg in args {
            if arg.inout {
                let span = self.span(arg.value);
                self.not_implemented(span, "`&` (inout) arguments", Planned::Phase(2));
            }
            let label = arg.label.map(|label| (label, m.text(label.sym)));
            let index = label.and_then(|(_, text)| fields.iter().position(|(name, _)| **name == *text));
            let problem = match (label, index) {
                _ if labels_reported => None,
                (None, _) => Some((
                    codes::MISSING_LABEL,
                    self.span(arg.value),
                    "each argument of `with` is labelled with the field it replaces".to_string(),
                )),
                (Some((label, text)), None) if id == AdtId::SYSTEM && LATER_SYSTEM_FIELDS.contains(&text) => {
                    let what = format!("`System` fields other than `stdout`, such as `{text}`,");
                    self.not_implemented(label.span, &what, Planned::Phase(3));
                    labels_reported = true;
                    None
                }
                (Some((label, text)), None) => {
                    Some((codes::UNKNOWN_MEMBER, label.span, format!("`{record}` has no field `{text}`")))
                }
                (Some((label, text)), Some(i)) if replaced.iter().any(|r| r.index() == i) => {
                    Some((codes::DUPLICATE_NAME, label.span, format!("`with` replaces `{text}` twice")))
                }
                (Some((label, text)), Some(i)) if replaced.last().is_some_and(|r| r.index() > i) => Some((
                    codes::WRONG_LABEL,
                    label.span,
                    format!(
                        "`{text}:` is out of order; labels follow the declaration order, as in `{record}({labelled})`"
                    ),
                )),
                _ => None,
            };
            if let Some((code, span, message)) = problem {
                self.error(code, span, message);
                labels_reported = true;
            }
            match index {
                Some(i) => {
                    replaced.push(FieldIdx(i as u32));
                    self.copying = true;
                    self.check(arg.value, &fields[i].1);
                }
                None => {
                    self.rejected_value(arg.value);
                }
            }
        }
        if !labels_reported {
            self.p.with_fields.insert(e, replaced.into());
        }
    }

    /// Checks arguments against parameters, including the label rules (REFERENCE §3, H3).
    fn args<S: AsRef<str>>(&mut self, callee: &str, params: &[(S, Ty)], args: &[Arg], span: Span) {
        self.generic_args(callee, params, &[], args, span, false);
    }

    /// Checks arguments against parameters whose types may mention the type parameters
    /// `targs` gives, which may be variables, so an argument in any position may give them
    /// (OPEN_QUESTIONS P5; issue #10). A construction, which stores its arguments, `copy`s
    /// them. Returns whether the number of arguments was right.
    fn generic_args<S: AsRef<str>>(
        &mut self,
        callee: &str,
        params: &[(S, Ty)],
        targs: &[Ty],
        args: &[Arg],
        span: Span,
        copy: bool,
    ) -> bool {
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
            self.rejected_args(args);
            return false;
        }
        // One label problem is reported per call, with the labels the call needs.
        let labelled = params.iter().map(|(param, _)| format!("{}: …", param.as_ref())).collect::<Vec<_>>().join(", ");
        let mut labels_reported = false;
        for (i, (arg, (param, _))) in args.iter().zip(params).enumerate() {
            let param = param.as_ref();
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
        }
        for (arg, (_, ty)) in args.iter().zip(params) {
            self.copying = copy;
            // A type parameter that `targs` doesn't cover is the caller's own, such as the `T`
            // that `Self` stands for in `x.bigger(y)` where `x: T`, so it is a type like any.
            if mentions_targ(ty, targs) {
                self.check(arg.value, &ty.subst(targs));
            } else {
                self.check(arg.value, ty);
            }
        }
        true
    }

    fn fallible_call(&mut self, call: ExprId, callee: &str, err: &Ty, span: Span, chain: bool) {
        // A call whose error type is `Never`, as `::[Never]` gives it, can't fail, as one that
        // declares `fails Never` can't (OPEN_QUESTIONS P5).
        if self.vars.resolve(err) == Ty::Never {
            return;
        }
        match self.markers.last_mut() {
            Some(marker) if chain => {
                marker.errors.push(err.clone());
                if let Some(handler) = marker.handler {
                    self.p.handler_of.insert(call, handler);
                }
            }
            _ => {
                // A later value may still give the error type, so the message waits for the
                // statement to settle it, and this E0701 stands for one nothing gives.
                self.vars.unmarked(err);
                if self.vars.has_var(err) {
                    self.pending.push(Pending::Unmarked { ty: err.clone(), callee: callee.into(), span });
                } else {
                    self.unmarked(callee, err, span);
                }
            }
        }
    }

    fn unmarked(&mut self, callee: &str, err: &Ty, span: Span) {
        // An error type that settled as `Never` can't happen, so the call can't fail.
        if *err == Ty::Never {
            return;
        }
        let with = if *err == Ty::Error { String::new() } else { format!(" with `{}`", self.show(err)) };
        let message =
            format!("`{callee}` can fail{with}, so the call must be marked with `try`, `else` or `attempt` (§7.2)");
        self.error(codes::UNMARKED_FALLIBLE_CALL, span, message);
    }

    fn try_expr(&mut self, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        self.markers.push(Marker { handler: None, errors: Vec::new() });
        self.in_chain = true;
        let ty = self.expr(inner, expected);
        let errors = self.markers.pop().map(|m| m.errors).unwrap_or_default();
        // A chain with an error may hold the fallible call that didn't resolve.
        let rejected = ty == Ty::Error;
        if errors.is_empty() && !rejected {
            self.error(codes::TRY_WITHOUT_FAILURE, span, "`try` marks no call that can fail");
        }
        if self.f.fails.is_none() && !errors.is_empty() {
            // Error types the statement has yet to settle are reported with the types it
            // settles, and nothing else reports one that nothing gives.
            if errors.iter().any(|err| self.vars.has_var(err)) {
                errors.iter().for_each(|err| self.vars.owe(err));
                self.pending.push(Pending::Try { errs: errors, rejected, span });
            } else {
                self.try_without_fails(errors, rejected, span);
            }
            return ty;
        }
        // Calls that fail with one type are one mistake (§15.1).
        let mut reported: Vec<String> = Vec::new();
        for err in errors {
            let err = self.vars.resolve(&err);
            let message = match &self.f.fails {
                None => unreachable!("a `try` without `fails` is reported above"),
                // The function's error type gives one the call leaves open (issue #20).
                Some(own) if *own == Ty::Error || err == Ty::Error => continue,
                Some(own) if self.vars.subsume(own, &err) && self.vars.subsume(&err, own) => continue,
                Some(own) => format!(
                    "`try` needs equal error types, but the call fails with `{}` and this function fails with `{}`",
                    self.show(&err),
                    self.show(own)
                ),
            };
            self.vars.poison(&err);
            if !reported.contains(&message) {
                self.error(codes::TRY_ERROR_MISMATCH, span, message.clone());
                reported.push(message);
            }
        }
        ty
    }

    /// Reports a `try` whose calls fail with `errs` where there is no `fails` to take them.
    /// An error type that is an error was reported where it went wrong, as the rule on
    /// [`Checker::settle_vars`] says. One that is `Never` can't happen, so a `try` whose calls
    /// all fail with `Never` marks no call that can fail (OPEN_QUESTIONS P5), unless its chain
    /// was `rejected` or a call's error type has an error, which may have been one that can
    /// fail (§15.1; issue #30). Calls that fail with one type are one mistake.
    fn try_without_fails(&mut self, errs: Vec<Ty>, rejected: bool, span: Span) {
        let mut settled: Vec<Ty> = Vec::new();
        for err in errs.iter().map(|err| self.vars.zonk(err)) {
            if !settled.contains(&err) {
                settled.push(err);
            }
        }
        let unknown = rejected || settled.contains(&Ty::Error);
        let errs: Vec<Ty> = settled.into_iter().filter(|err| *err != Ty::Error).collect();
        if errs.is_empty() {
            return;
        }
        if errs.iter().all(|err| *err == Ty::Never) {
            if unknown {
                return;
            }
            self.error(codes::TRY_WITHOUT_FAILURE, span, "`try` marks no call that can fail");
            return;
        }
        for err in errs.iter().filter(|err| **err != Ty::Never) {
            let message = if self.f.returns {
                let err = self.show(err);
                format!("`try` propagates `{err}`, but this function does not declare `fails {err}`")
            } else {
                let place = if self.f.example { "an example" } else { "a `where` clause" };
                format!("`try` in {place}, which has no function to propagate `{}` to", self.show(err))
            };
            self.error(codes::TRY_ERROR_MISMATCH, span, message);
        }
    }

    /// `attempt f(…)`: a `Result` of the chain's value and the error of the calls it marks
    /// (REFERENCE §7.2).
    fn attempt_expr(&mut self, e: ExprId, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        let value_expected = match expected {
            Some(Ty::Adt(AdtId::RESULT, args)) => Some(args[0].clone()),
            _ => None,
        };
        self.markers.push(Marker { handler: Some(e), errors: Vec::new() });
        self.in_chain = true;
        let ty = self.expr(inner, value_expected.as_ref());
        let errors = self.markers.pop().map(|m| m.errors).unwrap_or_default();
        let hole = self.met_hole(&errors);
        match self.one_error(errors, span, "`attempt`", "its `Result` has one error type") {
            // A chain with an error may hold the fallible call that didn't resolve.
            None => {
                if ty != Ty::Error {
                    self.error(codes::ATTEMPT_WITHOUT_FAILURE, span, "`attempt` marks no call that can fail");
                }
                Ty::Error
            }
            Some(err) => {
                if ty != Ty::Error && !hole {
                    self.wait_can_fail(&err, Handler::Attempt, span);
                }
                Ty::result(ty, err)
            }
        }
    }

    /// Reports the `attempt` or `else` form at `span` if its calls fail with `Never`, which
    /// can't happen, once the statement settles `err` (OPEN_QUESTIONS P5, `fails Never`).
    /// Whether a `todo` hole met one of `errors`, the error types of the calls a handler
    /// marks, which a chain may have settled before [`Checker::one_error`] joins them, as a
    /// receiver's type is (Q25).
    fn met_hole(&self, errors: &[Ty]) -> bool {
        errors.iter().any(|err| self.vars.from_hole(err))
    }

    fn wait_can_fail(&mut self, err: &Ty, handler: Handler, span: Span) {
        if self.vars.has_open(err) {
            self.pending.push(Pending::CanFail { err: err.clone(), handler, span });
        } else {
            self.can_fail(err, handler, span);
        }
    }

    fn can_fail(&mut self, err: &Ty, handler: Handler, span: Span) {
        // A `todo` hole that met the error type may be filled with a value of another type
        // (Q25; issue #30).
        if self.vars.zonk(err) != Ty::Never || self.vars.from_hole(err) {
            return;
        }
        match handler {
            Handler::Attempt => {
                self.error(codes::ATTEMPT_WITHOUT_FAILURE, span, "`attempt` marks no call that can fail");
            }
            Handler::Else => {
                let message = "`else` needs an `Option` or a call that can fail on its left, but this call fails with `Never`, so it can't";
                self.error(codes::NOTHING_TO_UNWRAP, span, message);
            }
            Handler::Example => {
                let message = "`fails` needs a call that can fail, and this one fails with `Never`, so it can't";
                self.error(codes::EXAMPLE_CANNOT_FAIL, span, message);
            }
        }
    }

    fn if_expr(&mut self, e: ExprId, mode: Mode) -> Ty {
        let m = self.m;
        let ExprKind::If { cond, then_block, else_branch } = &m.exprs[e].kind else {
            unreachable!("if_expr is called on `if` expressions")
        };
        let copying = std::mem::take(&mut self.tail_copying);
        // The bindings of an `is` in the condition scope over the then-block (REFERENCE §6.4).
        self.f.scopes.push(Vec::new());
        self.condition(*cond);
        let then_ty = match (mode, else_branch) {
            (Mode::Stmt | Mode::Tail(_), _) => {
                let tail = match mode {
                    Mode::Tail(ret) => Some(ret),
                    _ => None,
                };
                self.block_stmt(then_block, tail)
            }
            (Mode::Value(_), None) => self.block_value(then_block, None, copying),
            (Mode::Value(expected), Some(_)) => self.block_value(then_block, expected, copying),
        };
        self.f.scopes.pop();
        let ty = match (mode, else_branch) {
            (Mode::Stmt | Mode::Tail(_), _) => {
                let tail = match mode {
                    Mode::Tail(ret) => Some(ret),
                    _ => None,
                };
                let else_ty = match else_branch {
                    Some(ElseBranch::Block(block)) => self.block_stmt(block, tail),
                    Some(ElseBranch::If(nested)) => self.if_expr(*nested, mode),
                    None => Ty::Unit,
                };
                self.branches(&then_ty, &else_ty)
            }
            (Mode::Value(_), None) => {
                // A block that was never closed may have been followed by an `else`, and one
                // that lost code may have ended in it. One that diverges, or whose value has an
                // error, still gives the `if` no value when the condition is false.
                if !then_block.unclosed && !(then_block.lost && then_ty == Ty::Error) {
                    let span = self.span(e);
                    self.error(codes::TYPE_MISMATCH, span, "an `if` without `else` has no value; add an `else` branch");
                }
                Ty::Error
            }
            (Mode::Value(expected), Some(branch)) => {
                // The branches' types are joined, so either may give the other its type
                // arguments and literal types (OPEN_QUESTIONS P5; issue #10). The then-branch's
                // type, joined with the expected one, is what the else-branch meets.
                let known = if then_ty.is_unknown() { expected.cloned() } else { Some(then_ty.clone()) };
                let expected = known.as_ref();
                let else_ty = match branch {
                    ElseBranch::Block(block) => self.block_value(block, expected, copying),
                    ElseBranch::If(nested) => {
                        self.tail_copying = copying;
                        self.if_expr(*nested, Mode::Value(expected))
                    }
                };
                let else_tail = match branch {
                    ElseBranch::Block(block) => self.tail(block),
                    ElseBranch::If(nested) => Some(*nested),
                };
                self.rejected_parts(&[then_ty.clone(), else_ty.clone()]);
                if self.borrowed_tail(self.tail(then_block)) || self.borrowed_tail(else_tail) {
                    self.borrowed_values.insert(e);
                }
                match expected {
                    _ if then_ty == Ty::Never && else_ty == Ty::Never => Ty::Never,
                    // The else-branch's type is the join, unless it has none of its own.
                    Some(known) if else_ty.is_unknown() => known.clone(),
                    _ => else_ty,
                }
            }
        };
        self.record(e, ty.clone());
        ty
    }

    /// Checks `e`, a branch's value or a tuple's element, where the others give `known`,
    /// and returns the type of either: their join, where a `Never` part of `known` gives way
    /// (OPEN_QUESTIONS P5). A mismatch is reported at `e`.
    fn joined(&mut self, e: ExprId, known: &Ty) -> Ty {
        let ty = self.expr(e, Some(known));
        if ty == Ty::Error {
            self.vars.quiet(known);
        }
        if diverges_ty(&ty) {
            return ty;
        }
        self.vars.join(known, &ty).unwrap_or_else(|| {
            let message = format!("expected `{}`, found `{}`", self.show(known), self.show(&ty));
            self.error(codes::TYPE_MISMATCH, self.span(e), message);
            self.vars.poison(&ty);
            self.vars.quiet(known);
            Ty::Error
        })
    }

    /// Checks a `Bool` whose `is` bindings scope over what follows it: the rest of an `and`
    /// chain, and the block an `if` or `while` condition guards. The caller opens the scope
    /// they go in (REFERENCE §6.4).
    fn condition(&mut self, e: ExprId) {
        match self.m.exprs[e].kind {
            ExprKind::Is { value, pat } => self.is_test(value, pat),
            ExprKind::Binary { op: BinOp::And, lhs, rhs } => {
                self.condition(lhs);
                self.condition(rhs);
            }
            _ => {
                self.check(e, &Ty::Bool);
                return;
            }
        }
        self.record(e, Ty::Bool);
    }

    /// `value is pat`, whose bindings go in the innermost scope.
    fn is_test(&mut self, value: ExprId, pat: PatId) {
        let ty = self.infer(value);
        let ty = self.force(&ty);
        self.pattern_borrowed = self.borrowed_value(value);
        self.pattern(pat, &ty);
        self.pattern_borrowed = false;
    }

    /// The record or enum named `sym`: the module's, or `Option` or `Result` from the prelude.
    fn adt_named(&self, sym: Symbol) -> Option<AdtId> {
        if self.poisoned.contains(&sym) {
            return None;
        }
        let imported = || match self.imports.get(&sym) {
            Some(Import::Type(Ty::Adt(id, args))) if args.is_empty() => Some(*id),
            _ => None,
        };
        self.adt_names.get(&sym).copied().or_else(|| prelude_adt(self.m.text(sym))).or_else(imported)
    }

    /// The enum that `e` names, when it is a name that is not a local.
    fn enum_named(&self, e: ExprId) -> Option<AdtId> {
        let ExprKind::Name(name) = self.m.exprs[e].kind else { return None };
        if self.lookup_local(name.sym).is_some() {
            return None;
        }
        let id = self.adt_named(name.sym)?;
        self.p.decls.adt(id).is_enum().then_some(id)
    }

    /// The type arguments of a variant of `id` built at `span`: those `expected` gives, and a
    /// variable for each it doesn't, which the fields or the values it meets may give
    /// (OPEN_QUESTIONS P5; issue #10).
    fn variant_args(&mut self, id: AdtId, expected: Option<&Ty>, span: Span) -> Vec<Ty> {
        match expected {
            Some(Ty::Adt(other, args)) if *other == id => args.to_vec(),
            _ => {
                let origin = Origin::Variant { adt: id, span };
                (0..self.p.decls.adt(id).params).map(|_| self.vars.fresh(Kind::Any, origin)).collect()
            }
        }
    }

    /// The type of a variant of `id` built with type arguments `targs`. One left open where
    /// the expected type is of another type is reported as that mismatch, rather than as
    /// one that can't be inferred, and so is none where `reported` says the construction
    /// already has an error (§15.1).
    fn variant_type(&mut self, id: AdtId, targs: Vec<Ty>, expected: Option<&Ty>, span: Span, reported: bool) -> Ty {
        let ty = Ty::applied(id, targs);
        // A literal's type has a default, so a mismatch can name the whole type.
        let mut open = Vec::new();
        self.vars.open_in(&ty, &mut open);
        if open.iter().all(|&v| self.vars.open(v).is_some_and(|open| open.kind != Kind::Any)) {
            return ty;
        }
        let name = self.p.decls.adt(id).name.clone();
        match expected {
            _ if reported => {}
            Some(Ty::Error) => {}
            Some(expected)
                if !matches!(expected, Ty::Adt(other, _) if *other == id) && !matches!(expected, Ty::Var(_)) =>
            {
                let article = if &*name == "Option" { "an" } else { "a" };
                let message = format!("expected `{}`, found {article} `{name}`", self.show(expected));
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            _ => return ty,
        }
        self.vars.poison(&ty);
        Ty::Error
    }

    /// `Shape.Empty` or `None`, a variant without fields (REFERENCE §4.5).
    fn unit_variant(&mut self, e: ExprId, id: AdtId, name: Ident, expected: Option<&Ty>) -> Ty {
        let text = self.m.text(name.sym);
        let def = self.p.decls.adt(id);
        let Some((v, variant)) = def.variant_named(text) else {
            let message = format!("`{}` has no variant `{text}`", def.name);
            self.error(codes::UNKNOWN_MEMBER, name.span, message);
            return Ty::Error;
        };
        if !variant.fields.is_empty() && !variant.rejected {
            let what = format!("variants with fields used as values, such as `{}`,", def.ctor_name(v));
            self.not_implemented(name.span, &what, Planned::Phase(2));
            return Ty::Error;
        }
        self.p.res.insert(e, Res::Ctor(id, v));
        let span = self.span(e);
        let targs = self.variant_args(id, expected, span);
        self.variant_type(id, targs, expected, span, false)
    }

    /// `Shape.Circle(radius: 2)` or `Some(3)`: a variant's fields are passed as the arguments
    /// of a call (REFERENCE §4.5, §3). The type arguments of `Option` and `Result` come from
    /// the expected type, or else from the fields.
    fn construct_variant(
        &mut self,
        e: ExprId,
        id: AdtId,
        name: Ident,
        args: &[Arg],
        span: Span,
        expected: Option<&Ty>,
    ) -> Ty {
        let text = self.m.text(name.sym);
        let def = self.p.decls.adt(id);
        let Some((v, variant)) = def.variant_named(text) else {
            let message = format!("`{}` has no variant `{text}`", def.name);
            self.error(codes::UNKNOWN_MEMBER, name.span, message);
            self.rejected_args(args);
            return Ty::Error;
        };
        let ctor = def.ctor_name(v);
        let (rejected, fieldless) = (variant.rejected, variant.fields.is_empty());
        let params: Vec<(Box<str>, Ty)> = variant.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        let targs = self.variant_args(id, expected, span);
        if rejected {
            self.rejected_args(args);
            return self.variant_type(id, targs, expected, span, true);
        }
        if fieldless {
            let message = format!("`{ctor}` has no fields, so it is written without parentheses");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.rejected_args(args);
            return self.variant_type(id, targs, expected, span, true);
        }
        self.p.res.insert(e, Res::Ctor(id, v));
        let counted = self.generic_args(&ctor, &params, &targs, args, span, true);
        self.variant_type(id, targs, expected, span, !counted)
    }

    /// Reports a variant of the module's enums used without its enum, and returns whether
    /// `name` is one. Only `Some`, `None`, `Ok` and `Err` may be (REFERENCE §3, §4.5).
    fn unqualified_variant(&mut self, name: Ident) -> bool {
        let m = self.m;
        let text = m.text(name.sym);
        let owner = self.adts.iter().find(|adt| {
            self.adt_names.get(&adt.name.sym) == Some(&adt.id) && self.p.decls.adt(adt.id).variant_named(text).is_some()
        });
        let Some(owner) = owner else { return false };
        let qualified = format!("{}.{text}", m.text(owner.name.sym));
        let message = format!("variants are qualified in expressions; write `{qualified}`");
        self.error(codes::UNKNOWN_NAME, name.span, message);
        true
    }

    // ---- match and patterns (REFERENCE §6.3, §6.4) ----

    fn match_expr(&mut self, e: ExprId, mode: Mode) -> Ty {
        let m = self.m;
        let ExprKind::Match { scrutinee, arms, complete } = &m.exprs[e].kind else {
            unreachable!("match_expr is called on `match` expressions")
        };
        let copying = std::mem::take(&mut self.tail_copying);
        let scrutinee_ty = self.infer(*scrutinee);
        let scrutinee_ty = self.force(&scrutinee_ty);
        // The parts of a borrowed value are borrowed too.
        let borrowed = self.borrowed_value(*scrutinee);
        let mut rows = Vec::new();
        let mut expected = match mode {
            Mode::Value(expected) => expected.cloned(),
            _ => None,
        };
        let mut diverges = true;
        let mut leaves = Ty::Never;
        let mut tys = Vec::new();
        for arm in arms {
            // An arm's bindings scope over its guard and body.
            self.f.scopes.push(Vec::new());
            self.pattern_borrowed = borrowed;
            let space = self.pattern(arm.pat, &scrutinee_ty);
            self.pattern_borrowed = false;
            match arm.guard {
                Some(guard) => {
                    self.check(guard, &Ty::Bool);
                }
                // A guarded arm may not match, so it covers nothing.
                None => rows.push(space),
            }
            let ty = match mode {
                Mode::Stmt => self.block_stmt(&arm.body, None),
                Mode::Tail(ret) => self.block_stmt(&arm.body, Some(ret)),
                Mode::Value(_) => {
                    // Each arm's type is joined with what the others gave, in any order
                    // (OPEN_QUESTIONS P5; issue #10).
                    let ty = self.block_value(&arm.body, expected.as_ref(), copying);
                    if !ty.is_unknown() {
                        expected = Some(ty.clone());
                    }
                    ty
                }
            };
            diverges &= ty == Ty::Never;
            leaves = self.branches(&leaves, &ty);
            tys.push(ty);
            self.f.scopes.pop();
        }
        if matches!(mode, Mode::Value(_)) {
            self.rejected_parts(&tys);
        }
        // An arm that failed to parse may have covered what seems to be missing.
        if *complete && !scrutinee_ty.is_unknown() {
            let span = m.exprs[e].span;
            let inhabited = self.inhabited.as_ref().expect("match is checked after the declarations");
            match exhaust::uncovered(&self.p.decls, inhabited, &scrutinee_ty, &rows) {
                Ok(None) => {}
                Ok(Some(missing)) => {
                    let message = format!("this `match` does not cover `{missing}`; add an arm for it, or `_`");
                    self.error(codes::NON_EXHAUSTIVE_MATCH, span, message);
                }
                Err(exhaust::TooComplex) => {
                    let message =
                        "this `match` is too complex to check for exhaustiveness; split it into smaller matches";
                    self.error(codes::MATCH_TOO_COMPLEX, span, message);
                }
            }
        }
        // A value that no arm matches is a defect (OPEN_QUESTIONS P5), so a `match` whose
        // arms all diverge does too.
        if matches!(mode, Mode::Value(_)) && arms.iter().any(|arm| self.borrowed_tail(self.tail(&arm.body))) {
            self.borrowed_values.insert(e);
        }
        let ty = match mode {
            _ if diverges => Ty::Never,
            Mode::Stmt | Mode::Tail(_) => leaves,
            Mode::Value(_) if !complete => Ty::Error,
            Mode::Value(_) => expected.unwrap_or(Ty::Error),
        };
        self.record(e, ty.clone());
        ty
    }

    /// Checks `pat` against a value of type `ty`, declares its bindings in the innermost
    /// scope, and returns what it covers. A pattern with an error covers everything, so the
    /// `match` around it isn't reported as well (REFERENCE §15.1).
    fn pattern(&mut self, pat: PatId, ty: &Ty) -> Space {
        let m = self.m;
        let span = m.pats[pat].span;
        match &m.pats[pat].kind {
            PatKind::Wild => Space::Wild,
            PatKind::Bind(name) => {
                let (mutable, what) = if self.pattern_mutable { (true, "variable") } else { (false, "binding") };
                let id = self.declare(*name, ty.clone(), mutable, what, self.pattern_borrowed);
                self.p.pat_local.insert(pat, id);
                Space::Wild
            }
            PatKind::Tuple(parts) => self.tuple_pattern(pat, parts, ty),
            PatKind::Lit(lit) => self.literal_pattern(*lit, ty),
            PatKind::Range { lo, hi, .. } => match ty {
                Ty::Int(_) | Ty::Char => {
                    let lo_ty = self.check(*lo, ty);
                    let hi_ty = self.check(*hi, ty);
                    match ty {
                        _ if lo_ty != *ty || hi_ty != *ty => Space::Error,
                        Ty::Char => Space::Some,
                        _ if self.let_pattern => Space::Some,
                        // Integers are covered by facts, which the v1 profile checks at run time.
                        _ => Space::Wild,
                    }
                }
                _ => {
                    self.infer(*lo);
                    self.infer(*hi);
                    if !ty.is_unknown() {
                        let message = format!("a range pattern needs integer or char bounds, not `{}`", self.show(ty));
                        self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                    }
                    Space::Error
                }
            },
            PatKind::Ctor { qualifier, name, fields, rest } => {
                self.ctor_pattern(pat, ty, *qualifier, *name, fields.as_deref(), *rest)
            }
        }
    }

    fn literal_pattern(&mut self, lit: ExprId, ty: &Ty) -> Space {
        if let Ty::Float(_) = ty {
            self.infer(lit);
            let message = format!(
                "`{}` has no `Eq`, so its values can't be matched against literals (REFERENCE §12.2)",
                self.show(ty)
            );
            let span = self.span(lit);
            self.error(codes::UNSUPPORTED_OPERATOR, span, message);
            return Space::Error;
        }
        let actual = self.check(lit, ty);
        if actual != *ty {
            return Space::Error;
        }
        match (ty, &self.m.exprs[lit].kind) {
            (Ty::Bool, ExprKind::Bool(b)) => Space::Ctor(Ctor::Bool(*b), Vec::new()),
            (Ty::Unit, _) => Space::Ctor(Ctor::Unit, Vec::new()),
            (Ty::Char | Ty::Text, _) => Space::Some,
            // A `let` can't wait for a fact to cover it.
            _ if self.let_pattern => Space::Some,
            // Integers are covered by facts, which the v1 profile checks at run time.
            _ => Space::Wild,
        }
    }

    /// `(a, b)`, which matches a tuple of as many elements, each against its part.
    fn tuple_pattern(&mut self, pat: PatId, parts: &[PatId], ty: &Ty) -> Space {
        let span = self.m.pats[pat].span;
        let args = match ty {
            Ty::Adt(id, args) if self.p.decls.adt(*id).tuple && args.len() == parts.len() => Some((*id, args.clone())),
            _ => None,
        };
        let Some((id, args)) = args else {
            if !ty.is_unknown() {
                let message = match ty {
                    Ty::Adt(id, args) if self.p.decls.adt(*id).tuple => {
                        format!("`{}` has {} elements, but the pattern has {}", self.show(ty), args.len(), parts.len())
                    }
                    _ => format!("expected a pattern for `{}`, found a tuple pattern", self.show(ty)),
                };
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            for &part in parts {
                self.pattern(part, &Ty::Error);
            }
            return Space::Error;
        };
        let spaces: Vec<Space> = parts.iter().zip(args.iter()).map(|(&part, arg)| self.pattern(part, arg)).collect();
        let fields = (0..parts.len()).map(|i| FieldIdx(i as u32)).collect();
        self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: VariantIdx::RECORD, fields });
        if spaces.iter().any(|space| matches!(space, Space::Error)) {
            return Space::Error;
        }
        Space::Ctor(Ctor::Variant(VariantIdx::RECORD), spaces)
    }

    /// Checks the parts of a pattern that has an error, so that its names are still bound.
    fn unknown_parts(&mut self, fields: Option<&[FieldPat]>) -> Space {
        for field in fields.unwrap_or_default() {
            self.pattern(field.pat, &Ty::Error);
        }
        Space::Error
    }

    /// `Empty`, `Shape.Circle(r)` or `User(name, age: a, ..)` (REFERENCE §6.4).
    fn ctor_pattern(
        &mut self,
        pat: PatId,
        ty: &Ty,
        qualifier: Option<Ident>,
        name: Ident,
        fields: Option<&[FieldPat]>,
        rest: bool,
    ) -> Space {
        let m = self.m;
        let text = m.text(name.sym);
        let span = m.pats[pat].span;
        let Ty::Adt(id, targs) = ty else {
            if !ty.is_unknown() && !qualifier.is_some_and(|q| self.poisoned.contains(&q.sym)) {
                let message = format!("expected a pattern for `{}`, found the variant pattern `{text}`", self.show(ty));
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            return self.unknown_parts(fields);
        };
        let id = *id;
        if self.p.decls.adt(id).tuple {
            let message = format!("expected a tuple pattern for `{}`, found the pattern `{text}`", self.show(ty));
            self.error(codes::TYPE_MISMATCH, span, message);
            return self.unknown_parts(fields);
        }
        if let Some(q) = qualifier {
            let q_text = m.text(q.sym);
            let def = self.p.decls.adt(id);
            let problem = match self.adt_named(q.sym) {
                _ if self.poisoned.contains(&q.sym) => None,
                Some(other) if other == id && def.is_enum() => None,
                Some(other) => Some((
                    codes::TYPE_MISMATCH,
                    q.span,
                    format!(
                        "expected a pattern for `{}`, found one for `{}`",
                        self.p.decls.name(id),
                        self.p.decls.name(other)
                    ),
                )),
                None if self.imports.contains_key(&q.sym) || builtin_type(q_text).is_some() => Some((
                    codes::TYPE_MISMATCH,
                    q.span,
                    format!("expected a pattern for `{}`, found one for `{q_text}`", self.p.decls.name(id)),
                )),
                None => Some((codes::UNKNOWN_TYPE, q.span, format!("unknown type `{q_text}`"))),
            };
            let rejected = problem.is_some() || self.poisoned.contains(&q.sym);
            if let Some((code, span, message)) = problem {
                self.error(code, span, message);
            }
            if rejected {
                return self.unknown_parts(fields);
            }
        }
        let def = self.p.decls.adt(id);
        let found = match def.kind {
            AdtKind::Enum => def.variant_named(text).map(|(v, _)| v),
            AdtKind::Record => (*def.name == *text).then_some(VariantIdx::RECORD),
        };
        let Some(v) = found else {
            if self.poisoned.contains(&name.sym) {
            } else if let Some(&other) =
                self.adt_names.get(&name.sym).filter(|&&other| !def.is_enum() || !self.p.decls.adt(other).is_enum())
            {
                let (expected, found) = (self.p.decls.name(id), self.p.decls.name(other));
                let message = format!("expected a pattern for `{expected}`, found one for `{found}`");
                self.error(codes::TYPE_MISMATCH, span, message);
            } else if def.is_enum() {
                let message = format!("`{}` has no variant `{text}`", self.p.decls.name(id));
                self.error(codes::UNKNOWN_MEMBER, name.span, message);
            } else {
                let message = format!("`{text}` is not `{}`; its pattern is written `{}(…)`", def.name, def.name);
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            return self.unknown_parts(fields);
        };
        let variant = &def.variants[v.index()];
        if variant.rejected {
            return self.unknown_parts(fields);
        }
        let ctor = def.ctor_name(v);
        let declared: Vec<(Box<str>, Ty)> =
            variant.fields.iter().map(|f| (f.name.clone(), f.ty.subst(targs))).collect();
        let Some(fields) = fields else {
            if declared.is_empty() {
                self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: v, fields: Box::new([]) });
                return Space::Ctor(Ctor::Variant(v), Vec::new());
            }
            let n = declared.len();
            let noun = if n == 1 { "field" } else { "fields" };
            let message = format!("`{ctor}` has {n} {noun}; match them, or write `{ctor}(..)` to skip them");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            return Space::Error;
        };
        if declared.is_empty() && def.is_enum() {
            let message = format!("`{ctor}` has no fields, so its pattern is written without parentheses");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            return self.unknown_parts(Some(fields));
        }
        let problem = self.field_pattern_problem(&ctor, &declared, fields, rest, span);
        let mut parts = vec![Space::Wild; declared.len()];
        let mut targets = Vec::new();
        for (field, target) in fields.iter().zip(self.field_targets(&declared, fields)) {
            match target {
                Some(i) => {
                    parts[i] = self.pattern(field.pat, &declared[i].1);
                    targets.push(FieldIdx(i as u32));
                }
                None => {
                    self.pattern(field.pat, &Ty::Error);
                }
            }
        }
        if let Some((code, span, message)) = problem {
            self.error(code, span, message);
            return Space::Error;
        }
        self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: v, fields: targets.into() });
        // An error inside the pattern makes all of it count as `_`.
        if parts.iter().any(|part| matches!(part, Space::Error)) {
            return Space::Error;
        }
        Space::Ctor(Ctor::Variant(v), parts)
    }

    /// The field each part of a constructor pattern matches. One unlabelled part of a
    /// one-field variant matches that field whatever it is called; otherwise a part names
    /// its field with a label or, when it is a bare name, with that name (REFERENCE §6.4).
    fn field_targets(&self, declared: &[(Box<str>, Ty)], fields: &[FieldPat]) -> Vec<Option<usize>> {
        let m = self.m;
        let index: HashMap<&str, usize> = declared.iter().enumerate().map(|(i, (name, _))| (&**name, i)).collect();
        fields
            .iter()
            .map(|field| match (field.label, &m.pats[field.pat].kind) {
                (None, _) if declared.len() == 1 && fields.len() == 1 => Some(0),
                (Some(name), _) | (None, &PatKind::Bind(name)) => index.get(m.text(name.sym)).copied(),
                (None, _) => None,
            })
            .collect()
    }

    /// The first problem with how a constructor pattern names its fields. They follow the
    /// labels of a construction (H3): in declaration order, each once, all of them unless
    /// the pattern ends with `..` (OPEN_QUESTIONS P5).
    fn field_pattern_problem(
        &self,
        ctor: &str,
        declared: &[(Box<str>, Ty)],
        fields: &[FieldPat],
        rest: bool,
        span: Span,
    ) -> Option<(Code, Span, String)> {
        let m = self.m;
        let labelled = declared.iter().map(|(name, _)| format!("{name}: …")).collect::<Vec<_>>().join(", ");
        let n = declared.len();
        let noun = if n == 1 { "field" } else { "fields" };
        if fields.len() > n {
            let message = format!("`{ctor}` has {n} {noun}, but the pattern has {} parts", fields.len());
            return Some((codes::WRONG_ARGUMENT_COUNT, span, message));
        }
        let mut seen = vec![false; n];
        let (mut last, mut count) = (None, 0);
        for (field, target) in fields.iter().zip(self.field_targets(declared, fields)) {
            let at = field.label.map_or(m.pats[field.pat].span, |label| label.span);
            let named = field.label.or(match m.pats[field.pat].kind {
                PatKind::Bind(name) => Some(name),
                _ => None,
            });
            let Some(i) = target else {
                return Some(match named {
                    Some(name) => {
                        let text = m.text(name.sym);
                        let hint = if field.label.is_none() {
                            format!("; a bare name is a field name, and `field: {text}` binds another")
                        } else {
                            String::new()
                        };
                        (codes::UNKNOWN_MEMBER, at, format!("`{ctor}` has no field `{text}`{hint}"))
                    }
                    None => (
                        codes::MISSING_LABEL,
                        at,
                        format!("each part of a pattern with several fields is labelled, as in `{ctor}({labelled})`"),
                    ),
                });
            };
            let field_name = &declared[i].0;
            if seen[i] {
                return Some((codes::DUPLICATE_NAME, at, format!("the pattern matches `{field_name}` twice")));
            }
            if last.is_some_and(|last| last > i) {
                let message = format!(
                    "`{field_name}` is out of order; fields follow the declaration order, as in `{ctor}({labelled})`"
                );
                return Some((codes::WRONG_LABEL, at, message));
            }
            (seen[i], last, count) = (true, Some(i), count + 1);
        }
        if !rest && count < n {
            let message = format!(
                "`{ctor}` has {n} {noun}, but the pattern matches {count}; match the rest, or end it with `..`"
            );
            return Some((codes::WRONG_ARGUMENT_COUNT, span, message));
        }
        None
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
                let span = self.span(iter);
                let ty = self.operands(lo, hi, None, span);
                match self.force(&ty) {
                    Ty::Int(it) => Ty::Int(it),
                    ty if ty.is_unknown() => Ty::Error,
                    ty => {
                        let message = format!("a `for` range needs integer bounds, not `{}`", self.show(&ty));
                        self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                        Ty::Error
                    }
                }
            }
            _ => {
                self.rejected_value(iter);
                let span = self.span(iter);
                self.not_implemented(span, "`for` loops over collections", Planned::Phase(2));
                Ty::Error
            }
        };
        self.record(iter, element.clone());
        self.f.scopes.push(Vec::new());
        let id = self.declare(binding, element, false, "loop variable", false);
        self.p.for_local.insert(e, id);
        self.loop_body(e, label, body);
        self.f.scopes.pop();
        Ty::Unit
    }
}

/// Whether `ty` mentions one of the type parameters `targs` stands for.
fn mentions_targ(ty: &Ty, targs: &[Ty]) -> bool {
    match ty {
        Ty::Param(i) => (*i as usize) < targs.len(),
        Ty::Adt(_, args) => args.iter().any(|arg| mentions_targ(arg, targs)),
        _ => false,
    }
}

/// Whether a value of this type may never be produced. An error counts, because the code it
/// stands for might diverge.
fn diverges_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Never | Ty::Error)
}

fn arithmetic_defined(op: BinOp, ty: &Ty) -> bool {
    match ty {
        Ty::Int(_) => true,
        // Floats have no `%` (OPEN_QUESTIONS P5).
        Ty::Float(_) => op != BinOp::Rem,
        Ty::Error | Ty::Never => true,
        _ => false,
    }
}

/// The scalar types and `System` from the prelude (REFERENCE §3, §4.1).
/// A built-in method's parameters, return type and error.
type BuiltinSig = (Builtin, Vec<(&'static str, Ty)>, Ty, Option<Ty>);

/// The method `name` that values of `ty` have built in (STD.md).
fn builtin_method(ty: &Ty, name: &str) -> Option<BuiltinSig> {
    Some(match (ty, name) {
        (Ty::Cap(cap), "write_line") if cap.iface == IfaceId::OUT => {
            (Builtin::WriteLine, vec![("text", Ty::Text)], Ty::Unit, Some(Ty::IoError))
        }
        (Ty::Text, "byte_len") => (Builtin::ByteLen, vec![], Ty::INT, None),
        (Ty::Text, "is_empty") => (Builtin::IsEmpty, vec![], Ty::Bool, None),
        (Ty::Text, "trim") => (Builtin::Trim, vec![], Ty::Text, None),
        (Ty::Text, "split_once") => {
            let pair = Ty::applied(AdtId::PAIR, vec![Ty::Text, Ty::Text]);
            (Builtin::SplitOnce, vec![("sep", Ty::Text)], Ty::option(pair), None)
        }
        (Ty::Text, "starts_with") => (Builtin::StartsWith, vec![("prefix", Ty::Text)], Ty::Bool, None),
        (Ty::Text, "strip_prefix") => (Builtin::StripPrefix, vec![("prefix", Ty::Text)], Ty::option(Ty::Text), None),
        _ => return None,
    })
}

/// A scalar type other than a number, whose name a call such as `Text.parse(t)` may use.
fn is_scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Char | Ty::Text | Ty::Unit)
}

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
        "System" => Ty::system(),
        _ => return None,
    })
}

/// How far an item's visibility reaches, so that a wider one is greater.
fn reach(vis: Visibility) -> u8 {
    match vis {
        Visibility::Private => 0,
        Visibility::PubPkg => 1,
        Visibility::Pub => 2,
    }
}

/// The fields a record or variant keeps: the first of each name, in order.
fn kept_fields(fields: &[FieldDecl]) -> Vec<&FieldDecl> {
    let mut seen = HashSet::new();
    fields.iter().filter(|field| seen.insert(field.name.sym)).collect()
}

/// `Option` and `Result`, the prelude's generic enums (STD.md).
fn prelude_adt(name: &str) -> Option<AdtId> {
    match name {
        "Option" => Some(AdtId::OPTION),
        "Result" => Some(AdtId::RESULT),
        _ => None,
    }
}

/// The enum of `Some`, `None`, `Ok` and `Err`, the variants that may be used unqualified in
/// expressions (REFERENCE §3).
fn bare_variant(name: &str) -> Option<AdtId> {
    match name {
        "Some" | "None" => Some(AdtId::OPTION),
        "Ok" | "Err" => Some(AdtId::RESULT),
        _ => None,
    }
}

/// How to write the prelude's generic type `name` with its type arguments.
fn example_type(name: &str) -> &'static str {
    if name == "Result" { "Result[T, E]" } else { "Option[T]" }
}

fn type_args(n: usize) -> String {
    match n {
        1 => "1 type argument".to_string(),
        n => format!("{n} type arguments"),
    }
}

/// A type, interface or variant name the prelude declares (REFERENCE §3). A module item or
/// import may not reuse one (H4).
fn prelude_type(name: &str) -> bool {
    builtin_type(name).is_some()
        || prelude_adt(name).is_some()
        || bare_variant(name).is_some()
        || later_type(name).is_some()
        || IfaceId::prelude(name).is_some()
}

/// Prelude types that later phases implement.
fn later_type(name: &str) -> Option<Planned> {
    match name {
        "List" | "Map" | "Set" | "Array" | "Bytes" | "Ordering" | "Rounding" | "Invalid" => Some(Planned::Phase(2)),
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
