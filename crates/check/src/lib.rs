//! Name resolution and type checking for the phase-1 subset (scalar types, functions,
//! control flow, `fails` and `try`, and the prelude's `System` with only `stdout`), for
//! records, for enums, `match` and patterns, for `Option`, `Result`, `fail` and `attempt`,
//! for methods, interfaces and generic functions, for tuples, `let` patterns, the `else`
//! forms, `check`, the text operations and `example` declarations, for collections, and for
//! kinds, moves, `take` and `inout` parameters and `std.pool`, and for function types,
//! function values and closures.
//!
//! The checker never rewrites the tree. It records what it learns in side tables of
//! [`Program`], which the interpreter reads.

pub mod decls;
pub mod exhaust;
pub mod infer;
mod moves;
pub mod types;

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use proviso_syntax::arena::SideTable;
use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, Planned, Severity, codes};
use proviso_syntax::intern::Symbol;
use proviso_syntax::source::Span;

use crate::decls::{
    AdtDef, AdtId, AdtKind, CapDef, Decls, FieldDef, FieldIdx, IfaceDef, IfaceId, IfaceMethod, ImplDef, ImplKey,
    Inhabited, Pred, VariantDef, VariantIdx, matches_target,
};
use crate::exhaust::{Ctor, Space};
use crate::infer::{Kind, Origin, Vars};
use crate::types::{CapTy, FN_PARAMS, FloatTy, IntTy, Perms, Reach, Ty};

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
    /// `x.only::[p, …]()` on a capability, which narrows its type (REFERENCE §9.2).
    Only,
    /// `X.of(r)`, which makes a capability of interface `X` of a `cap record` that implements
    /// it (REFERENCE §9.6). It is called on the interface, so it has no receiver.
    Of,
    /// `Text.byte_len() -> Int`
    ByteLen,
    /// `Text.is_empty() -> Bool`, and the same for `List` and `Map`.
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
    /// `Text.lines() -> List[Text]`
    Lines,
    /// `List.len() -> Int`, `Map.len() -> Int` and `Pool.len() -> Int`
    Len,
    /// `List.push(inout self, value: take T)`
    Push,
    /// `List.pop(inout self) -> Option[T]`
    Pop,
    /// `List.get(index: Int) -> Option[T]`, `Map.get(key: K) -> Option[V]` and
    /// `Pool.get(handle: Handle[T]) -> Option[T]`
    Get,
    /// `List.enumerate() -> List[(Int, T)]`
    Enumerate,
    /// `List.contains(value: T) -> Bool`
    Contains,
    /// `Map.contains_key(key: K) -> Bool`
    ContainsKey,
    /// `Map.set(inout self, key: take K, value: take V) -> Option[V]`
    Set,
    /// `Map.remove(inout self, key: K) -> Option[V]`, and `Pool.remove(inout self, handle:
    /// Handle[T]) -> Option[T]`
    Remove,
    /// `Pool.new() -> Pool[T]`, which is called on the type, so it has no receiver.
    PoolNew,
    /// `Pool.insert(inout self, value: take T) -> Handle[T]`
    Insert,
    /// `Pool.duplicate(self) -> Pool[T]`
    Duplicate,
    /// `Pool.update(inout self, handle: Handle[T], change: fn(take T) -> T) -> Bool`
    Update,
    /// `T(x)`, a conversion that keeps every value, and `Float.from(x)` and `Float32.from(x)`
    /// from any integer type, which round to the nearest value, ties to even (STD.md).
    Convert(Num),
    /// `T.try_from(x) -> T fails ConversionError` from any integer type, for each integer
    /// type `T`. It is called on the type, so it has no receiver.
    TryFrom(IntTy),
    /// `T.wrapping_from(x) -> T` from any integer type, which keeps the low bits of `x`.
    WrappingFrom(IntTy),
    /// `Float.to_int(self, rounding: Rounding) -> Int fails ConversionError`, and the same for
    /// `Float32`.
    ToInt,
}

/// A numeric type, which a conversion makes a value of.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Num {
    Int(IntTy),
    Float(FloatTy),
}

impl Builtin {
    /// Whether it takes `inout self`, so its receiver is a variable or a part of one that it
    /// changes (STD.md, REFERENCE §5.2).
    pub fn changes_receiver(self) -> bool {
        matches!(
            self,
            Builtin::Push | Builtin::Pop | Builtin::Set | Builtin::Remove | Builtin::Insert | Builtin::Update
        )
    }
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
    /// The type parameters, which its types write as `Ty::Param(i)` (REFERENCE §4.8). A
    /// method of a generic `impl` has the block's first.
    pub generics: Vec<GenericInfo>,
    /// How many of `generics` are its `impl` block's, which the receiver's type gives by
    /// matching `owner` rather than `::[…]` (OPEN_QUESTIONS P5).
    pub impl_params: usize,
    /// The type of `self`, which is local 0, for a method; `None` for a function or an
    /// associated function.
    pub receiver: Option<Ty>,
    /// How a method takes `self`: borrowed, `inout self` or `take self` (REFERENCE §5.2).
    pub self_mode: ParamMode,
    /// The type of the `impl` block that declares it, which `Self` names there.
    pub owner: Option<Ty>,
    pub params: Vec<ParamInfo>,
    pub ret: Ty,
    pub fails: Option<Ty>,
    /// Number of local slots, `self` and the parameters first.
    pub locals: usize,
    /// The resource parameters it owns, which a failure exit abandons, with their spans:
    /// `take` ones, and a `take self` other than an `abandon`'s, which can't abandon itself.
    pub owned: Vec<(LocalId, Span)>,
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
#[derive(Clone)]
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
    /// The loop each `break` or `continue` leaves.
    pub jump_target: SideTable<Stmt, ExprId>,
    /// What handles the failure of each fallible call that is marked other than by `try`:
    /// the `attempt`, which reifies it as an `Err` (REFERENCE §7.2), the `else` form, which
    /// runs its fallback (§6.6), or the call of an `example`, which reports it (§14).
    pub handler_of: SideTable<Expr, ExprId>,
    /// The local that holds `it` in the fallback of each `else` form on a call that can
    /// fail. An `else` form without one unwraps an `Option`.
    pub it_local: SideTable<Expr, LocalId>,
    /// The locals and fields whose values move out of their places, which nothing reads
    /// again before they are assigned (REFERENCE §5.1), so the interpreter may take the
    /// value out.
    pub moves_out: SideTable<Expr, ()>,
    /// The `match` arms whose patterns move the whole local or field their scrutinee names,
    /// which leaves its place when the arm is chosen.
    pub arms_out: SideTable<Pat, ()>,
    /// The expressions whose resource a call, construction, literal or `match` holds while
    /// the rest of it runs, which a failure exit then abandons (REFERENCE §10).
    pub held: SideTable<Expr, ()>,
    /// The bindings that own a resource, which a failure exit abandons.
    pub owned_binds: SideTable<Pat, ()>,
    /// The resource parts each pattern moves out of the place its value is in, as paths of
    /// fields from that place, which the interpreter takes out when the pattern matches.
    pub parts_out: SideTable<Pat, Box<[Box<[FieldIdx]>]>>,
    /// The module's examples, in declaration order.
    pub examples: Vec<ExampleInfo>,
    /// What each closure takes and captures (REFERENCE §6.7).
    pub closures: SideTable<Expr, ClosureInfo>,
    /// How `debug` writes each function value it is given: as its type, with the names of
    /// the type parameters of the function it is in (OPEN_QUESTIONS P5).
    pub debug_fns: SideTable<Expr, Box<str>>,
}

/// A closure's parameters and their modes, and the locals of the frame it is made in that it
/// captures, which it reads there (REFERENCE §6.7).
pub struct ClosureInfo {
    pub params: Vec<LocalId>,
    pub modes: Vec<ParamMode>,
    /// What it captures, with each one's name.
    pub captures: Vec<(LocalId, Box<str>)>,
    /// The resource parameters it owns, its `take` ones, which a failure exit abandons, with
    /// their spans.
    pub owned: Vec<(LocalId, Span)>,
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
        aliases: HashMap::new(),
        poisoned: m.poisoned.clone(),
        main_lost: m.lost_fns.iter().any(|&sym| m.text(sym) == "main"),
        adts: Vec::new(),
        adt_vis: HashMap::new(),
        cap_vis: HashMap::new(),
        only_declared: HashSet::new(),
        iface_names: HashMap::new(),
        ifaces: Vec::new(),
        cap_decls: HashSet::new(),
        inherent: HashMap::new(),
        rejected_abandon: HashSet::new(),
        rejected_abandon_for: Vec::new(),
        unknown_tys: Vec::new(),
        operators: Vec::new(),
        f: FnState::new(Ty::Unit, None),
        in_chain: false,
        sibling_closure: false,
        siblings: HashSet::new(),
        markers: Vec::new(),
        inhabited: None,
        self_ty: None,
        cap_self: false,
        generic_scope: Vec::new(),
        param_names: Vec::new(),
        impl_generics: Vec::new(),
        copying: false,
        consumed: HashSet::new(),
        rejected: HashSet::new(),
        mismatched: HashSet::new(),
        method_values: HashSet::new(),
        errors: 0,
        inner_errors: 0,
        tail_copying: false,
        pattern_borrowed: false,
        pattern_mutable: false,
        pattern_in_loop: false,
        let_pattern: false,
        its: Vec::new(),
        option_fallbacks: 0,
        borrowed_values: HashSet::new(),
        vars: Vars::default(),
        pending: Vec::new(),
        stmt_start: (0, 0),
        typed: Vec::new(),
        written_keys: Some(Vec::new()),
        closure_scopes: Vec::new(),
        builders: Vec::new(),
        escaped: Vec::new(),
    };
    checker.imports();
    checker.adt_names();
    checker.iface_names();
    checker.unknown_impl_targets();
    checker.adt_generics();
    checker.resolve_aliases();
    checker.adt_fields();
    checker.cap_record_reach();
    checker.expanding_types();
    checker.p.decls.settle_kinds();
    checker.opaque_reach();
    checker.cap_record_fields();
    checker.inhabited = Some(checker.p.decls.inhabited());
    checker.iface_methods();
    checker.adt_derives();
    checker.signatures();
    checker.impls();
    checker.operator_derives();
    checker.abandon_impls();
    checker.written_keys();
    checker.collisions();
    checker.derived_fields();
    checker.adt_predicates();
    checker.check_main();
    for id in 0..checker.p.fns.len() {
        checker.body(id);
    }
    checker.examples();
    // Parts shared between expressions are walked once, so a chain of `let`s that each wrap
    // the one before costs each its own level.
    let mut seen = HashSet::new();
    debug_assert!(
        !checker.p.expr_ty.values().any(|ty| holds_var(ty, &mut seen)),
        "an inference variable was left in `expr_ty`"
    );
    checker.p
}

/// Whether `ty` has an inference variable in it, which [`Program`] never does. `seen` holds
/// the addresses of the argument lists already walked, so a type that shares a part, as
/// `(t, t)` does, costs each part once.
fn holds_var(ty: &Ty, seen: &mut HashSet<usize>) -> bool {
    match ty {
        Ty::Var(_) => true,
        _ if let Some(args) = ty.parts() => {
            seen.insert(Arc::as_ptr(args) as *const Ty as usize) && args.iter().any(|arg| holds_var(arg, seen))
        }
        _ => false,
    }
}

#[derive(Clone)]
enum Import {
    Type(Ty),
    /// `use a.b` makes `b` usable as a qualifier.
    Module,
}

/// An alias, by how far it is resolved.
enum Alias {
    /// Declared with this type and name.
    Pending(TypeId, Ident),
    /// Being resolved after the aliases its type names.
    Resolving(TypeId, Ident),
    Done(Ty),
}

/// A record or enum declaration, with the parts the checker reads the same way for both.
struct AdtSrc<'a> {
    id: AdtId,
    name: Ident,
    vis: Visibility,
    /// Its type parameters, as declared (REFERENCE §4.8).
    generics: &'a [GenericParam],
    derives: &'a [Ident],
    /// The variants the declaration keeps, in order: a record's one, named like it, or the
    /// first of each name in an enum.
    variants: Vec<(Ident, &'a [FieldDecl])>,
    /// A record's record-level `where`.
    refinement: Option<ExprId>,
    /// What an opaque record declares it `uses`, none if it declares nothing (REFERENCE §9.2).
    /// `None` for any other type.
    uses: Option<&'a [TypeId]>,
}

struct Local {
    ty: Ty,
    mutable: bool,
    /// A parameter, or a part of one bound by a pattern, which the function borrows, so
    /// copying it needs `Copy` (REFERENCE §4.8).
    borrowed: bool,
    /// Bound by a `for` pattern, so nothing can make it mutable.
    in_loop: bool,
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
    self_mode: ParamMode,
    params: Vec<ParamInfo>,
    ret: Ty,
    fails: Option<Ty>,
    rejected: bool,
}

/// Code with no function around it (see [`FnState::returns`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Place {
    Where,
    Example,
    Test,
}

impl Place {
    fn describe(self) -> &'static str {
        match self {
            Place::Where => "a `where` clause",
            Place::Example => "an example",
            Place::Test => "a test",
        }
    }
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
    /// How many of the locals are `self` and the parameters, which come first.
    params: usize,
    /// Whether this is a refinement, whose locals are the fields it looks at.
    refinement: bool,
    /// Whether it is a distinct type's, which names its value `self`.
    distinct: bool,
    loops: Vec<LoopState>,
    /// False in a refinement, an example or a test, which have no function to return from or
    /// fail.
    returns: bool,
    /// What is being checked when it isn't a function, so diagnostics name it.
    place: Place,
    /// The interfaces each of the function's type parameters implements.
    bounds: Vec<Vec<IfaceId>>,
    /// Whether each of the function's type parameters has a rejected declaration or
    /// constraint, so a field of its type is unknown (§15.1).
    rejected: Vec<bool>,
    /// For each type parameter that a parameter of interface type stands for, that
    /// parameter's name and the interface, which diagnostics suggest a declaration with.
    anonymous: Vec<Option<(Box<str>, Box<str>)>>,
    /// The closures of the body, in the order they were checked.
    closures: Vec<ExprId>,
    /// The function values `debug` is given, which it writes as their types.
    debugged: Vec<ExprId>,
    /// The captures whose type wasn't known when their closure's type was given, each with
    /// the closure, where it is used, and the written function type the closure was checked
    /// as, if any. Once the capture's type is known, that type's `uses`, or else the
    /// closure's own, must cover its reach (REFERENCE §9.4).
    late_captures: Vec<(ExprId, LocalId, Span, Option<Ty>)>,
    /// How many of the function's locals, counted from the first, a closure, or a local that
    /// holds one, needs to stay alive: one more than the last local it captures, at any
    /// depth. A block can't yield a function value that needs one it declares.
    needs: HashMap<ExprId, u32>,
    local_needs: HashMap<LocalId, u32>,
    /// For an operation of a `cap record` that needs no `effects` permission, its interface
    /// and name. Its body sees `self` through the observes-only view (OPEN_QUESTIONS Q39).
    view: Option<(IfaceId, Box<str>)>,
    /// In such an operation, the expressions that are `self` or a path from it.
    view_paths: HashSet<ExprId>,
    /// The ones that may leave the view, until a parent uses them in a way it allows.
    escapes: HashMap<ExprId, Escape>,
    /// The capabilities the view narrowed, and locals bound to one, with their types outside
    /// the view, so a permission only the view took away is E0601 rather than E0603.
    unnarrowed: HashMap<ExprId, Ty>,
    unnarrowed_locals: HashMap<LocalId, Ty>,
}

/// A value in an operation with the observes-only view that could change what `self` reaches
/// if it left the view (OPEN_QUESTIONS Q39).
#[derive(Clone, Copy)]
enum Escape {
    /// `self`.
    SelfValue,
    /// A `cap record` at the end of a path from `self`.
    Record,
    /// Another value at the end of such a path, with `effects` reach.
    Reaches,
}

impl FnState {
    fn new(ret: Ty, fails: Option<Ty>) -> FnState {
        FnState {
            ret,
            fails,
            scopes: Vec::new(),
            locals: Vec::new(),
            params: 0,
            refinement: false,
            distinct: false,
            loops: Vec::new(),
            returns: true,
            place: Place::Where,
            bounds: Vec::new(),
            anonymous: Vec::new(),
            rejected: Vec::new(),
            closures: Vec::new(),
            debugged: Vec::new(),
            late_captures: Vec::new(),
            needs: HashMap::new(),
            local_needs: HashMap::new(),
            view: None,
            view_paths: HashSet::new(),
            escapes: HashMap::new(),
            unnarrowed: HashMap::new(),
            unnarrowed_locals: HashMap::new(),
        }
    }
}

/// A closure being checked: the first local it declares, and the locals declared before it
/// that its body uses, which it captures.
struct ClosureScope {
    base: u32,
    captures: Vec<(LocalId, Box<str>)>,
    /// Where each capture is first used, by the capture's index.
    spans: Vec<Span>,
    /// Whether its body has a call without the marker it needs, whose failure its error type
    /// would have taken.
    unmarked: bool,
    /// The labels of the loops around it, which its body can't leave.
    labels: Vec<Symbol>,
}

/// An enclosing `try`, `attempt`, `else` form or example, and the error types of the
/// fallible calls it marks.
struct Marker {
    /// What handles their failure (see [`Program::handler_of`]), or `None` for a `try`.
    handler: Option<ExprId>,
    errors: Vec<Ty>,
    /// The error type the handler gives its calls before its chain is checked: the function's
    /// `fails` under `try`, or the error type of the `Result` an `attempt` is expected to be.
    target: Option<Ty>,
}

/// How a call takes its arguments: each borrowed, each taken, as a construction's are, or
/// each by its parameter's mode.
#[derive(Clone, Copy)]
enum Modes<'a> {
    Borrow,
    Take,
    Each(&'a [ParamMode]),
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

/// The fields of `System` that come with `std.fs` in slice 3.5 (REFERENCE §9.1).
const LATER_SYSTEM_FIELDS: &[&str] = &["fs"];

struct Checker<'a> {
    m: &'a Module,
    opts: Options,
    diags: &'a mut Diagnostics,
    p: Program,
    fn_names: HashMap<Symbol, FnId>,
    imports: HashMap<Symbol, Import>,
    /// The module's records and enums.
    adt_names: HashMap<Symbol, AdtId>,
    /// The module's aliases, as far as they are resolved (REFERENCE §4.6).
    aliases: HashMap<Symbol, Alias>,
    /// Names whose declarations were rejected, so their uses aren't reported again: those the
    /// parser rejected, and records and enums whose names the checker rejects.
    poisoned: HashSet<Symbol>,
    /// Whether a function named `main` was rejected, so it isn't reported as missing.
    main_lost: bool,
    /// Every record and enum declaration, including those whose name is rejected.
    adts: Vec<AdtSrc<'a>>,
    /// The visibility of each of [`Checker::adts`].
    adt_vis: HashMap<AdtId, Visibility>,
    /// The visibility of each of the module's capability interfaces, which are types.
    cap_vis: HashMap<IfaceId, Visibility>,
    /// The capability interfaces that declare an operation named `only`, which is rejected.
    only_declared: HashSet<IfaceId>,
    /// The function being checked, or the record whose refinements are.
    f: FnState,
    /// Set while checking the postfix chain a `try` or `attempt` covers (REFERENCE §6.1).
    in_chain: bool,
    /// Set while checking a closure whose expected type is another branch's, which it joins
    /// rather than meets.
    sibling_closure: bool,
    /// The values whose expected type is what another branch, arm or element gave, rather
    /// than one written or required (see [`Checker::joined`]). A branch that is an `if` or
    /// `match` passes this on to its own branches.
    siblings: HashSet<ExprId>,
    /// The enclosing `try` and `attempt` markers, innermost last.
    markers: Vec<Marker>,
    /// Which types have values (see [`Decls::inhabited`]), once every declaration is known.
    inhabited: Option<Inhabited>,
    /// The module's interfaces.
    iface_names: HashMap<Symbol, IfaceId>,
    ifaces: Vec<IfaceSrc<'a>>,
    /// The names the module declares capability interfaces with, including those that are
    /// rejected after they parse, such as a wrongly cased one.
    cap_decls: HashSet<Symbol>,
    /// The methods and associated functions of each record and enum, in declaration order.
    inherent: HashMap<AdtId, Vec<Inherent>>,
    /// The methods of a rejected `impl Abandon`, whose `self` isn't reported as left over,
    /// since its `abandon` was never going to be called (REFERENCE §15.1).
    rejected_abandon: HashSet<FnId>,
    /// The targets of those blocks, with how many type parameters each has, so that
    /// `Abandon.abandon(x)` on a type one matches may mean it (issue #53).
    rejected_abandon_for: Vec<(Ty, usize)>,
    /// Types without an [`ImplKey`], such as `Never` and `Out`, that a rejected `impl` block
    /// is for. They may have methods and interfaces that nothing records (REFERENCE §15.1).
    unknown_tys: Vec<Ty>,
    /// The operators distinct types derive, with the name of each, which
    /// [`Checker::operator_derives`] checks once every `impl` block is known.
    operators: Vec<(AdtId, IfaceId, Ident)>,
    /// What `Self` means here: the type of an `impl` block, or `Param(0)` in an interface.
    self_ty: Option<Ty>,
    /// `Self` is the type that implements a `cap interface`, which comes with `cap record`.
    cap_self: bool,
    /// The type parameters in scope, by name, with their indices; `None` for one whose
    /// constraint is rejected, which stands for an unknown type.
    generic_scope: Vec<(Symbol, Option<u32>)>,
    /// How diagnostics write each type parameter in scope.
    param_names: Vec<Box<str>>,
    /// The type parameters of the `impl` block being declared, which its methods' come after.
    impl_generics: Vec<GenericInfo>,
    /// Set while checking an expression whose value is copied: bound to a name, stored in a
    /// value or returned (REFERENCE §4.8).
    copying: bool,
    /// The expressions of the body being checked whose values are copied, or moved when
    /// their type is unique (REFERENCE §5.1), which the move pass reads.
    consumed: HashSet<ExprId>,
    /// The expressions of the body being checked that an error was reported at, not at one
    /// of their parts, which the move pass leaves alone (REFERENCE §15.1).
    rejected: HashSet<ExprId>,
    /// The branches whose type didn't match the others', and the `if`, `match` and `else`
    /// forms they are in, which give no type (REFERENCE §15.1).
    mismatched: HashSet<ExprId>,
    /// The fields rejected as methods named as values, as in `p.close`, which the move pass
    /// treats as rejected calls of them (REFERENCE §15.1).
    method_values: HashSet<ExprId>,
    /// How many errors were reported, and how many of them inside the parts of the
    /// expression being checked.
    errors: usize,
    inner_errors: usize,
    /// [`Checker::copying`], handed from an `if` or `match` to the values of its branches.
    tail_copying: bool,
    /// Set while checking a pattern that matches a borrowed value, so its bindings are too.
    pattern_borrowed: bool,
    /// Set while checking the pattern of a `var`, whose bindings are mutable.
    pattern_mutable: bool,
    /// Set while checking the pattern of a `for` loop, whose bindings are loop variables.
    pattern_in_loop: bool,
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
    /// The key types of the `Map` types written in declarations, with where they are written
    /// and the bounds of the type parameters there. They are checked once every `derives`
    /// and `impl` is known, and `None` after that, when a written type is checked at once.
    written_keys: Option<Vec<WrittenKey>>,
    /// The closures being checked, innermost last.
    closure_scopes: Vec<ClosureScope>,
    /// The expressions of the body being checked that build a value whose type may hold a
    /// function value, which is reported once the body settles it (E0509), and where such a
    /// value was reported, so a value around it isn't reported again.
    builders: Vec<ExprId>,
    escaped: Vec<Span>,
}

/// The key type of a `Map` type a declaration writes, which is checked once every `derives`
/// and `impl` is known: where it is written, and the bounds and names of the type parameters
/// there.
struct WrittenKey {
    key: Ty,
    span: Span,
    bounds: Vec<Vec<IfaceId>>,
    names: Vec<Box<str>>,
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
    /// A call of method `name` of `iface` on a receiver of type `ty`, found while a handler's
    /// error types in it were open, which must implement `iface` once they settle (E0303).
    Method { ty: Ty, iface: IfaceId, name: Box<str>, span: Span },
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
            | Pending::Method { ty, .. }
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
        self.errors += 1;
        self.diags.error(code, span, message);
    }

    /// Reports an error about the value `e`, which rejects `e` but not what holds it, such
    /// as a call it is an argument of (REFERENCE §15.1).
    fn error_of(&mut self, e: ExprId, code: Code, span: Span, message: impl Into<String>) {
        self.error(code, span, message);
        self.rejected.insert(e);
        self.inner_errors += 1;
    }

    fn not_implemented(&mut self, span: Span, what: &str, planned: Planned) {
        self.errors += 1;
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

    /// Whether a rejected declaration may have given `ty` interfaces that nothing records. A
    /// type parameter whose declaration or constraint is rejected is one (issue #53).
    fn unknown_interfaces(&self, ty: &Ty) -> bool {
        let ty = self.vars.resolve(ty);
        self.p.decls.unknown_interfaces(&ty)
            || self.unknown_tys.contains(&ty)
            || matches!(ty, Ty::Param(i) if self.f.rejected.get(i as usize) == Some(&true))
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

    /// Settles the type of a receiver, or of the base of a field or index, in a handler's
    /// chain, as far as finding its member needs (OPEN_QUESTIONS P5, `fails Never`; issue #37).
    ///
    /// Invariant: an open variable in the error type of a call that a `try`, `attempt`, `else`
    /// or example marks, and that stays inside a later receiver's type arguments, is settled
    /// by its handler's join or by the statement around it, never by that receiver. Only
    /// `Never` or a `todo` hole may have reached it yet, and a value after the chain, such as
    /// `== Err("x")` or the `it` of a fallback, may still give it its type. So:
    /// - Each such variable in the receiver first joins what its handler knows now (see
    ///   [`Checker::join_known`]), which the handler would join it with anyway. One that is
    ///   still open stays open. The caller finds the method on [`Vars::as_never`] of the
    ///   type, where it implements every interface, as the `Never` it would have settled as
    ///   does. An interface method found that way is checked again once it settles
    ///   ([`Pending::Method`]).
    /// - The one exception is a variable at the receiver's head, since finding the member
    ///   needs the type itself. After the join it settles, and a value after the chain is too
    ///   late for it. Where what the handler knows disagrees, the handler reports that, and
    ///   the receiver is an error, so its member isn't reported too (§15.1).
    ///
    /// Every other open variable settles as [`Checker::force`] settles it.
    fn force_receiver(&mut self, ty: &Ty) -> Ty {
        if !self.vars.has_var(ty) {
            return ty.clone();
        }
        let head = match self.vars.resolve(ty) {
            Ty::Var(v) => Some(self.vars.root(v)),
            _ => None,
        };
        let mut open = Vec::new();
        self.vars.open_in(ty, &mut open);
        for &v in &open {
            if self.marked(v) && !self.join_known(v, head == Some(v)) && head == Some(v) {
                return Ty::Error;
            }
        }
        let mut open = Vec::new();
        self.vars.open_in(ty, &mut open);
        open.retain(|&v| head == Some(v) || !self.marked(v));
        self.settle_vars(open);
        self.vars.zonk(ty)
    }

    /// Whether open variable `v` is in the error type of a call a handler marks.
    fn marked(&self, v: u32) -> bool {
        self.vars.handled(v)
    }

    /// Leaves the innermost handler and returns its calls' error types, whose variables are no
    /// longer marked as handled unless an enclosing handler marks them too. That happens where
    /// an inner `attempt` is expected to fail with an outer call's error type. Each error type
    /// is walked once to mark it and once to clear it.
    fn pop_marker(&mut self) -> Vec<Ty> {
        let Some(marker) = self.markers.pop() else { return Vec::new() };
        let depth = self.markers.len() as u32;
        for err in &marker.errors {
            self.vars.set_handled(err, depth, false);
        }
        marker.errors
    }

    /// Joins open variable `v`, if it is in the error type of a call a handler marks, with what
    /// that handler knows now (see [`Checker::force_receiver`]), in the order the handler
    /// compares them. A `try` compares each call's error type with its function's `fails`, so
    /// that comes first. The other handlers join the chain's error types and then compare
    /// their join with an `attempt`'s expected `Result`, so those come first. `v` takes the
    /// first that gives it a type.
    ///
    /// Under a handler other than `try`, returns false, and leaves `v` open, where the types
    /// `v` would join disagree, since either may have been the one meant to give it. The
    /// handler reports that mismatch (§15.1). At the receiver's `head`, a `try` whose `fails`
    /// disagrees with another call, or with a rejected one, reports that call alone, so there
    /// `v` is an error, which it doesn't report again. Elsewhere at the head a rejected call's
    /// error type poisons `v`, since it may have given its type. Inside the receiver's type
    /// arguments `v` only joins a type all of them agree on, so a member no type argument
    /// gives is still reported.
    fn join_known(&mut self, v: u32, head: bool) -> bool {
        let v = self.vars.root(v);
        let holds = |vars: &Vars, err: &Ty| vars.mentions(v, err);
        let Some(marker) = self.markers.iter().rev().find(|m| m.errors.iter().any(|err| holds(&self.vars, err))) else {
            return true;
        };
        // The error type that holds `v`, at its top or inside it as in `fails Option[E]`, is
        // what the handler joins, so that is what joins here.
        let Some(own) = marker.errors.iter().find(|err| holds(&self.vars, err)).cloned() else { return true };
        let errors: Vec<Ty> = marker.errors.iter().filter(|err| !holds(&self.vars, err)).cloned().collect();
        let (handler, target) = (marker.handler, marker.target.clone());
        // The error types the calls already have, or a literal's, which the handler joins.
        let closed: Vec<Ty> = errors.iter().filter_map(|err| self.known(err)).filter(|err| *err != Ty::Never).collect();
        let err = Ty::Var(v);
        if let (None, Some(target)) = (handler, &target) {
            let target = self.vars.zonk(target);
            if closed.iter().any(|known| !self.agree(known, &target)) {
                if head {
                    self.vars.poison(&err);
                }
            } else {
                let _ = self.vars.subsume(&target, &own) && self.vars.subsume(&own, &target);
            }
            return true;
        }
        if closed.contains(&Ty::Error) {
            if head {
                self.vars.poison(&err);
            }
            return true;
        }
        if closed.iter().any(|known| !self.agree(known, &closed[0])) {
            return false;
        }
        let known: Vec<Ty> = errors.into_iter().chain(target).collect();
        for known in &known {
            if !matches!(self.vars.resolve(&err), Ty::Var(_)) {
                break;
            }
            let _ = self.vars.subsume(known, &own) && self.vars.subsume(&own, known);
        }
        true
    }

    /// `ty` where nothing more can change what it joins with: a type without open variables,
    /// or an open literal variable, which joins only a number type of its kind.
    fn known(&self, ty: &Ty) -> Option<Ty> {
        let ty = self.vars.zonk(ty);
        match ty {
            Ty::Var(v) if self.vars.open(v).is_some_and(|open| open.kind != Kind::Any) => Some(Ty::Var(v)),
            // A zonked type's variables are open, and `has_var` remembers its answer per part.
            ty if !self.vars.has_var(&ty) => Some(ty),
            _ => None,
        }
    }

    /// Whether types `a` and `b`, which [`Checker::known`] gave, join.
    fn agree(&self, a: &Ty, b: &Ty) -> bool {
        let kind = |ty: &Ty| match ty {
            Ty::Var(v) => self.vars.open(*v).map(|open| open.kind),
            Ty::Int(_) => Some(Kind::Int),
            Ty::Float(_) => Some(Kind::Float),
            _ => None,
        };
        match (a, b) {
            (Ty::Var(_), _) | (_, Ty::Var(_)) => kind(a).is_some() && kind(a) == kind(b),
            _ => a == b,
        }
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
                // A capability whose permissions the values and places it met leave open.
                Kind::Any if let Some(bounds) = &open.bounds => bounds.solution(),
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
                            self.example_of(adt)
                        ),
                    )
                }
                Origin::Call { f, span, .. } => {
                    let info = &self.p.fns[f];
                    let name = self.m.text(info.name);
                    let params: Vec<usize> = (unknown.iter())
                        .filter_map(|o| match o {
                            Origin::Call { param, span: s, .. } if *s == span => Some(*param),
                            _ => None,
                        })
                        .collect();
                    let missing: Vec<String> =
                        params.iter().map(|&param| format!("`{}`", info.generics[param].name)).collect();
                    let noun = if missing.len() == 1 { "type argument" } else { "type arguments" };
                    // `::[…]` gives only the function's own type parameters, not its `impl`'s.
                    let fix = if params.iter().all(|&param| param < info.impl_params) {
                        String::new()
                    } else {
                        format!(", or write `{name}::[…](…)`")
                    };
                    reported.push(span);
                    (
                        span,
                        format!(
                            "the {noun} {} of `{name}` can't be inferred; give the binding a type{fix}",
                            missing.join(", ")
                        ),
                    )
                }
                Origin::Closure { name, span } => (
                    span,
                    format!(
                        "the type of closure parameter `{}` can't be inferred; write it, as in `|{}: Int|`",
                        self.m.text(name),
                        self.m.text(name)
                    ),
                ),
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
                // A map literal's function key is reported where it goes in (E0509).
                if *callee == *"Map" {
                    self.key_bound(&ty, span);
                    return;
                }
                if self.fn_targ(&ty, span) {
                    return;
                }
                if self.resource_targ(&ty, &callee, &param, span) {
                    return;
                }
                if let Some(iface) = self.unmet_bound(&ty, &ifaces) {
                    let message = format!(
                        "`{}` does not implement `{}`, which `{callee}` needs of `{param}`",
                        self.show(&ty),
                        self.iface_name(iface)
                    );
                    self.error(codes::MISSING_IMPLEMENTATION, span, message);
                }
            }
            Pending::Method { ty, iface, name, span } => {
                let ty = self.vars.zonk(&ty);
                if !ty.is_unknown() && !self.implements(&ty, iface) && !self.unknown_interfaces(&ty) {
                    let message = format!("`{}` has no method `{name}`", self.show(&ty));
                    self.error(codes::UNKNOWN_MEMBER, span, message);
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
        // A value that holds a function value could outlive what it captures (E0509). It is
        // reported where a function value goes into it. A part that holds one already was
        // reported where it was made (§15.1).
        for e in std::mem::take(&mut self.builders) {
            let span = self.span(e);
            if !self.wraps_fn(e) || self.escaped.contains(&span) {
                continue;
            }
            let ty = self.vars.zonk(self.p.ty(e));
            if !holds_fn(&ty) {
                continue;
            }
            // A closure passed where a type argument was already reported has its result
            // from it.
            if matches!(self.m.exprs[e].kind, ExprKind::Closure(_))
                && self.escaped.iter().any(|outer| outer.contains(span))
            {
                continue;
            }
            let message = format!(
                "this value is a `{}`, which holds a function value, and a function value can't be stored or returned, since it lives only as long as what it captures",
                self.show(&ty)
            );
            self.error(codes::FUNCTION_VALUE_ESCAPES, span, message);
            self.escaped.push(span);
        }
        self.escaped.clear();
        for e in std::mem::take(&mut self.typed) {
            if let Some(ty) = self.p.expr_ty.get(e) {
                let ty = self.vars.zonk(ty);
                self.p.expr_ty.insert(e, ty);
            }
        }
        for local in &mut self.f.locals {
            local.ty = self.vars.zonk(&local.ty);
        }
        for e in std::mem::take(&mut self.f.debugged) {
            let shown = self.show(self.p.ty(e)).into();
            self.p.debug_fns.insert(e, shown);
        }
        // Each closure around a capture captures it, and the innermost one is reported.
        let mut reported = HashSet::new();
        for (e, id, span, written) in std::mem::take(&mut self.f.late_captures) {
            let ty = &self.f.locals[id.index()].ty;
            let reach = self.reach(ty);
            // A rejected closure's captures aren't checked (§15.1).
            if self.p.ty(e).is_unknown() {
                continue;
            }
            let Some(Ty::Reach(uses)) = written.as_ref().or(Some(self.p.ty(e))).and_then(Ty::fn_uses) else { continue };
            if ty.is_unknown() || reach.covered_by(uses) || !reported.insert((span.lo, span.hi)) {
                continue;
            }
            let message = match &written {
                Some(written) => format!(
                    "this closure captures a value of type `{}`, which reaches more than `{}` admits (§9.4)",
                    self.show(ty),
                    self.show(written)
                ),
                None => format!(
                    "this closure captures a value of type `{}`, which was inferred after the closure's type `{}`, so the closure's `uses` doesn't cover what it reaches; give the value a type where it is declared (§9.4)",
                    self.show(ty),
                    self.show(self.p.ty(e))
                ),
            };
            self.error(codes::REACH_NOT_ADMITTED, span, message);
        }
        self.vars.clear();
        // A closure owns its `take` parameters of a resource type, which a failure abandons.
        for e in std::mem::take(&mut self.f.closures) {
            let ExprKind::Closure(closure) = &self.m.exprs[e].kind else { continue };
            let Some(info) = self.p.closures.get_mut(e) else { continue };
            info.owned = (info.params.iter().zip(&info.modes).zip(&closure.params))
                .filter(|((local, mode), _)| {
                    **mode == ParamMode::Take && self.p.decls.is_resource(&self.f.locals[local.index()].ty)
                })
                .map(|((local, _), param)| (*local, param.name.span))
                .collect();
        }
    }

    /// Checks the key types of the `Map` types the declarations write, now that every
    /// `derives` and `impl` is known (REFERENCE §4.2).
    fn written_keys(&mut self) {
        let outer = (std::mem::take(&mut self.f.bounds), std::mem::take(&mut self.param_names));
        for written in self.written_keys.take().unwrap_or_default() {
            (self.f.bounds, self.param_names) = (written.bounds, written.names);
            self.key_bound(&written.key, written.span);
        }
        (self.f.bounds, self.param_names) = outer;
        // A type written with a rejected key type is an error, as one written in a body is,
        // so nothing that meets it is reported again (§15.1).
        let unknown = self.unknown_tys.clone();
        for f in 0..self.p.fns.len() {
            let bounds: Vec<Vec<IfaceId>> = self.p.fns[f].generics.iter().map(|g| g.bounds.clone()).collect();
            let decls = &self.p.decls;
            let fix = |ty: &Ty| without_bad_keys(decls, ty, &bounds, &unknown);
            let info = &self.p.fns[f];
            let params: Vec<Ty> = info.params.iter().map(|p| fix(&p.ty)).collect();
            let (ret, fails) = (fix(&info.ret), info.fails.as_ref().map(fix));
            let info = &mut self.p.fns[f];
            for (param, ty) in info.params.iter_mut().zip(params) {
                param.ty = ty;
            }
            (info.ret, info.fails) = (ret, fails);
        }
        self.p.decls.rewrite_types(&mut |decls, ty| without_bad_keys(decls, ty, &[], &unknown));
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
            ItemKind::Alias(decl) => vec![decl.name],
            ItemKind::Impl(_) | ItemKind::Example(_) | ItemKind::Test(_) => vec![],
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
            ["std", "io"] => {
                Some(vec![("In", Ty::cap(IfaceId::IN, Perms::all(1))), ("IoError", Ty::IoError), ("Out", Ty::out())])
            }
            // `ParseError` is the only item `std.text` declares (STD.md).
            ["std", "text"] => Some(vec![("ParseError", Ty::adt(AdtId::PARSE_ERROR))]),
            // A generic import names its type without type arguments, which each use gives.
            ["std", "pool"] => Some(vec![("Pool", Ty::adt(AdtId::POOL)), ("Handle", Ty::adt(AdtId::HANDLE))]),
            // `ConversionError` is the only item `std.num` declares (STD.md).
            ["std", "num"] => Some(vec![("ConversionError", Ty::adt(AdtId::CONVERSION_ERROR))]),
            ["std", module] => {
                let planned = match *module {
                    "fs" | "test" => Planned::Phase(3),
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
                    format!("unknown module `{joined}`; phase 1 checks one file at a time, and the standard library provides only `std.io`, `std.num`, `std.pool` and `std.text`"),
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
            if let ItemKind::Alias(decl) = &item.kind {
                self.alias_name(decl);
                continue;
            }
            let (name, generics, derives, refinement, kind) = match &item.kind {
                ItemKind::Record(decl) => {
                    (decl.name, &decl.generics[..], &decl.derives[..], decl.refinement, AdtKind::Record)
                }
                ItemKind::Enum(decl) => (decl.name, &decl.generics[..], &decl.derives[..], None, AdtKind::Enum),
                _ => continue,
            };
            let text = m.text(name.sym);
            let mut def = match kind {
                AdtKind::Record => AdtDef::record(text, Vec::new()),
                AdtKind::Enum => AdtDef::enumeration(text),
                AdtKind::Native => unreachable!("only the toolchain declares native types"),
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
            // A resource moves as a unique value does, and must also be consumed (§5.1, §10).
            def.resource_base = matches!(&item.kind, ItemKind::Record(decl) if decl.resource);
            def.unique = def.resource_base || matches!(&item.kind, ItemKind::Record(decl) if decl.unique);
            def.distinct = matches!(&item.kind, ItemKind::Record(decl) if decl.distinct);
            def.cap = matches!(&item.kind, ItemKind::Record(decl) if decl.cap);
            def.params = generics.len();
            let id = self.p.decls.push(def);
            let uses = match &item.kind {
                ItemKind::Record(decl) if decl.opaque => Some(decl.uses.as_deref().unwrap_or_default()),
                _ => None,
            };
            self.adts.push(AdtSrc { id, name, vis: item.vis, generics, derives, variants, refinement, uses });
            self.adt_vis.insert(id, item.vis);
            // A rejected name is reported once. Its uses, and what it collides with, are not.
            let cased = self.pascal_case(name, "type");
            if !cased || prelude_type(text) {
                if cased {
                    let message = format!("this {what} would shadow the prelude name `{text}` (H4)");
                    self.error(codes::SHADOWING, name.span, message);
                }
                self.poisoned.insert(name.sym);
            } else if self.adt_names.contains_key(&name.sym)
                || self.imports.contains_key(&name.sym)
                || self.aliases.contains_key(&name.sym)
            {
                // Which one a use means is unclear, so its uses aren't checked (issue #19).
                self.error(codes::DUPLICATE_ITEM, name.span, format!("`{text}` is defined twice in this module"));
                self.poisoned.insert(name.sym);
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

    /// Declares an alias, whose type is resolved once every type has a name. A rejected name
    /// is reported once, and its uses are not (REFERENCE §15.1). An alias that clashes with
    /// another item may have been meant by any use of the name, so none is checked.
    fn alias_name(&mut self, decl: &AliasDecl) {
        let name = decl.name;
        let text = self.m.text(name.sym);
        let cased = self.pascal_case(name, "type");
        if !cased || prelude_type(text) {
            if cased {
                let message = format!("this alias would shadow the prelude name `{text}` (H4)");
                self.error(codes::SHADOWING, name.span, message);
            }
            self.poisoned.insert(name.sym);
        } else if self.adt_names.contains_key(&name.sym)
            || self.imports.contains_key(&name.sym)
            || self.aliases.contains_key(&name.sym)
        {
            self.error(codes::DUPLICATE_ITEM, name.span, format!("`{text}` is defined twice in this module"));
            self.poisoned.insert(name.sym);
        } else {
            self.aliases.insert(name.sym, Alias::Pending(decl.target, name));
        }
    }

    /// Resolves every alias, in declaration order, once every type has a name, so an alias
    /// may name a type or alias declared later. Visibility is checked on the type an alias
    /// names, so a `pub` alias may not name a private type (REFERENCE §3).
    fn resolve_aliases(&mut self) {
        let m = self.m;
        for item in &m.items {
            let ItemKind::Alias(decl) = &item.kind else { continue };
            if self.poisoned.contains(&decl.name.sym) {
                continue;
            }
            let ty = self.alias_type(decl.name.sym);
            self.exposes(decl.name, item.vis, &ty, decl.target);
            // A rejected `impl` block for the alias was for the type it names.
            if m.impls.contains(&decl.name.sym)
                && let Some(key) = ImplKey::of(&ty)
            {
                self.p.decls.mark_unknown(key);
            }
        }
    }

    /// The type alias `sym` names, resolved on first use.
    fn alias_type(&mut self, sym: Symbol) -> Ty {
        if let Some(Alias::Pending(..)) = self.aliases.get(&sym) {
            self.resolve_alias(sym);
        }
        match self.aliases.get(&sym) {
            Some(Alias::Done(ty)) => ty.clone(),
            // The aliases an alias names are resolved before it, so only one of a cycle,
            // which is reported already, is still being resolved.
            Some(Alias::Resolving(..)) => Ty::Error,
            _ => unreachable!("only a declared alias is resolved"),
        }
    }

    /// Resolves alias `sym` after the aliases it names, depth first on a stack of its own, so
    /// a long chain of aliases doesn't recurse once per alias. A cycle is reported once, at
    /// its first alias in the file, and its aliases are unknown types. A type deeper than a
    /// type may be is reported once, at the alias that makes it so (REFERENCE §15.1).
    fn resolve_alias(&mut self, sym: Symbol) {
        let Some(&Alias::Pending(target, name)) = self.aliases.get(&sym) else { return };
        self.aliases.insert(sym, Alias::Resolving(target, name));
        let mut stack = vec![(sym, self.aliases_in(target), 0)];
        while let Some((top, names, next)) = stack.last_mut() {
            // An alias of a cycle already reported is done, and what else it names is
            // resolved when an alias of its own needs it.
            if let Some(Alias::Done(_)) = self.aliases.get(top) {
                stack.pop();
                continue;
            }
            if let Some(&named) = names.get(*next) {
                *next += 1;
                match self.aliases.get(&named) {
                    Some(&Alias::Pending(target, name)) => {
                        self.aliases.insert(named, Alias::Resolving(target, name));
                        let names = self.aliases_in(target);
                        stack.push((named, names, 0));
                    }
                    Some(Alias::Resolving(..)) => {
                        let at = stack.iter().position(|(s, ..)| *s == named).expect("a resolving alias is stacked");
                        let cycle: Vec<Symbol> = stack[at..].iter().map(|(s, ..)| *s).collect();
                        self.alias_cycle(&cycle);
                    }
                    _ => {}
                }
                continue;
            }
            let top = *top;
            stack.pop();
            let Some(&Alias::Resolving(target, name)) = self.aliases.get(&top) else { continue };
            // An alias has no type parameters, and is not in an `impl` block.
            let scope = std::mem::take(&mut self.generic_scope);
            let names = std::mem::take(&mut self.param_names);
            let bounds = std::mem::take(&mut self.f.bounds);
            let self_ty = self.self_ty.take();
            let before = self.errors;
            let mut ty = self.resolve_type(target);
            (self.generic_scope, self.param_names, self.f.bounds, self.self_ty) = (scope, names, bounds, self_ty);
            if self.vars.depth(&ty, MAX_TYPE_DEPTH).is_none() {
                if before == self.errors {
                    let message = format!(
                        "`{}` names a type that nests more than {MAX_TYPE_DEPTH} levels deep, which is more than a type may",
                        self.m.text(name.sym)
                    );
                    self.error(codes::TYPE_TOO_DEEP, name.span, message);
                }
                ty = Ty::Error;
            }
            if ty == Ty::Error {
                self.poisoned.insert(top);
            }
            self.aliases.insert(top, Alias::Done(ty));
        }
    }

    /// Reports the aliases of `cycle`, which name each other in this order, and makes each an
    /// unknown type.
    fn alias_cycle(&mut self, cycle: &[Symbol]) {
        let names: Vec<Ident> = cycle
            .iter()
            .map(|s| match self.aliases[s] {
                Alias::Resolving(_, name) => name,
                _ => unreachable!("the aliases of a cycle are being resolved"),
            })
            .collect();
        let first = names.iter().min_by_key(|name| name.span.lo).expect("a cycle has an alias");
        // A long cycle is named by its first few aliases.
        let mut shown: Vec<String> = names.iter().take(3).map(|name| format!("`{}`", self.m.text(name.sym))).collect();
        if names.len() > 3 {
            shown.push(format!("{} more", names.len() - 3));
        }
        let message = match shown.as_slice() {
            [one] => {
                format!("alias {one} names itself, so it names no type; a recursive type is a record or enum (§4.6)")
            }
            _ => format!(
                "aliases {} name each other in a cycle, so they name no type; a recursive type is a record or enum (§4.6)",
                shown.join(" and ")
            ),
        };
        self.error(codes::ALIAS_CYCLE, first.span, message);
        for &sym in cycle {
            self.aliases.insert(sym, Alias::Done(Ty::Error));
            self.poisoned.insert(sym);
        }
    }

    /// The aliases that type expression `t` names, in the order it names them.
    fn aliases_in(&self, t: TypeId) -> Vec<Symbol> {
        let mut found = Vec::new();
        let mut work = vec![t];
        while let Some(t) = work.pop() {
            match &self.m.types[t].kind {
                TypeExprKind::Named(name) if self.aliases.contains_key(&name.sym) => found.push(name.sym),
                TypeExprKind::Named(_) | TypeExprKind::SelfType | TypeExprKind::Rejected => {}
                TypeExprKind::Applied { name, args } => {
                    if self.aliases.contains_key(&name.sym) {
                        found.push(name.sym);
                    }
                    work.extend(args.iter().flatten().rev());
                }
                TypeExprKind::Tuple(parts) => work.extend(parts.iter().rev()),
                TypeExprKind::Fn { params, ret, fails, uses } => {
                    let parts = fails.iter().chain(ret.iter()).chain(params.iter().map(|(_, t)| t)).chain(uses);
                    work.extend(parts.rev());
                }
                TypeExprKind::Uses { base, uses } => work.extend(std::iter::once(base).chain(uses).rev()),
            }
        }
        found
    }

    /// How to tell a use of alias `name` as a value or pattern what to write instead: aliases
    /// name types only (REFERENCE §4.6).
    fn alias_value(&mut self, name: Ident) {
        let text = self.m.text(name.sym);
        let Some(Alias::Done(ty)) = self.aliases.get(&name.sym) else { return };
        let ty = ty.clone();
        let shown = self.show(&ty);
        // An expression writes a generic type by its name alone, and a tuple or function type
        // by none (REFERENCE §4.8).
        let write = match &ty {
            _ if self.p.decls.is_tuple(&ty) => None,
            Ty::Adt(id, args) if !args.is_empty() => Some(self.p.decls.adt(*id).name.to_string()),
            // A number has its own functions and conversions, as `Int.parse(…)` and `Int64(x)`.
            Ty::Adt(..) | Ty::Int(_) | Ty::Float(_) => Some(shown.clone()),
            _ => None,
        };
        let mut message = format!("`{text}` is an alias of the type `{shown}`, and an alias names a type only");
        if let Some(write) = write {
            message += &format!("; write `{write}` here");
        }
        self.error(codes::UNKNOWN_NAME, name.span, message);
    }

    /// Checks the type parameters of each generic record and enum, once every type has a
    /// name: PascalCase, distinct, and unlike any type's name (REFERENCE §2, §3, H4). A type
    /// whose parameters are rejected may have meant any of them, so its uses aren't checked
    /// (§15.1).
    fn adt_generics(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let (name, generics) = (self.adts[k].name, self.adts[k].generics);
            let mut seen: Vec<Symbol> = Vec::new();
            let mut rejected = false;
            for param in generics {
                let text = m.text(param.name.sym);
                let cased = self.pascal_case(param.name, "type parameter");
                if seen.contains(&param.name.sym) {
                    if cased {
                        self.error(
                            codes::DUPLICATE_NAME,
                            param.name.span,
                            format!("type parameter `{text}` is declared twice"),
                        );
                    }
                    rejected = true;
                } else if cased && self.names_type(param.name.sym) {
                    let message = format!("type parameter `{text}` would shadow the type `{text}` (H4)");
                    self.error(codes::SHADOWING, param.name.span, message);
                    rejected = true;
                }
                seen.push(param.name.sym);
            }
            if rejected {
                self.poisoned.insert(name.sym);
            }
        }
    }

    /// Resolves the fields of every variant once every record and enum has a name, so a
    /// field's type may be declared later in the file (OPEN_QUESTIONS P5). A generic type's
    /// fields name its type parameters, which they write as `Ty::Param(i)`.
    fn adt_fields(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let (id, name, vis) = (self.adts[k].id, self.adts[k].name, self.adts[k].vis);
            let generics = self.adts[k].generics;
            self.generic_scope = generics.iter().enumerate().map(|(i, g)| (g.name.sym, Some(i as u32))).collect();
            self.param_names = generics.iter().map(|g| m.text(g.name.sym).into()).collect();
            for v in 0..self.adts[k].variants.len() {
                let decls = self.adts[k].variants[v].1;
                let mut fields: Vec<FieldDef> = Vec::new();
                let mut index: HashMap<Symbol, usize> = HashMap::new();
                for field in decls {
                    let text = m.text(field.name.sym);
                    let cased = self.snake_case(field.name, "field");
                    let ty = self.part_type(field.ty, "a field");
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
                    fields.push(FieldDef { name: text.into(), ty, state: field.state });
                }
                let variant = &mut self.p.decls.adt_mut(id).variants[v];
                variant.locals = fields.len();
                variant.fields = fields;
            }
            // A declared reach that has a mistake in it is unknown, so the record reaches what
            // its fields do, and nothing more is reported (§15.1).
            if let Some(uses) = self.adts[k].uses {
                let declared = self.exposed_uses(uses, Some((name, vis)));
                if declared.is_none() {
                    self.adts[k].uses = None;
                }
                self.p.decls.adt_mut(id).uses = declared;
            }
        }
        self.generic_scope.clear();
        self.param_names.clear();
    }

    /// Gives each `cap record` the reach of every capability interface its `impl` blocks name,
    /// with every permission, since a direct call on it may run any of their operations
    /// (OPEN_QUESTIONS P5). It is read from the blocks as written, before they are checked, so
    /// that a type holding the record reaches them too once kinds settle.
    fn cap_record_reach(&mut self) {
        let m = self.m;
        for item in &m.items {
            let ItemKind::Impl(decl) = &item.kind else { continue };
            let (Some(iface), TypeExprKind::Named(target)) = (decl.iface, &m.types[decl.target].kind) else {
                continue;
            };
            let (Some(&id), Some(iface)) = (self.adt_names.get(&target.sym), self.cap_named(iface.sym)) else {
                continue;
            };
            if self.p.decls.adt(id).cap {
                let perms = self.p.decls.iface(iface).all_perms();
                self.p.decls.adt_mut(id).reach.add_cap(iface, perms);
            }
        }
    }

    /// Reports each field of a `cap record` whose type is unique or a resource. Copies of the
    /// record share one object, so they would share the value (REFERENCE §5.1, §9.6), which
    /// isn't scheduled (OPEN_QUESTIONS P5).
    fn cap_record_fields(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let id = self.adts[k].id;
            if !self.p.decls.adt(id).cap {
                continue;
            }
            let Some((_, decls)) = self.adts[k].variants.first().copied() else { continue };
            for decl in decls {
                let text = m.text(decl.name.sym);
                let Some((_, field)) = self.p.decls.adt(id).field(text) else { continue };
                if self.p.decls.moves(&field.ty, &[]) {
                    let what = "unique or resource fields of `cap record`s";
                    self.not_implemented(m.types[decl.ty].span, what, Planned::Unscheduled);
                }
            }
            // The record is copyable whatever its fields are, since its values are handles.
            let def = self.p.decls.adt_mut(id);
            (def.unique, def.resource) = (false, false);
        }
    }

    /// Reports each field of an opaque record whose reach the record's `uses` doesn't cover
    /// (REFERENCE §9.2). A type parameter's reach is its type argument's, which the record's
    /// type adds wherever it is used, so only capabilities are compared.
    fn opaque_reach(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let (id, name) = (self.adts[k].id, self.adts[k].name);
            let Some(declared) = self.p.decls.adt(id).uses.clone() else { continue };
            let Some((_, decls)) = self.adts[k].variants.first().copied() else { continue };
            let fields: Vec<(Box<str>, Ty)> =
                self.p.decls.adt(id).variant().fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
            // The variant keeps the first of fields declared twice, so a field is found by name.
            let mut seen = HashSet::new();
            for decl in decls {
                if !seen.insert(decl.name.sym) {
                    continue;
                }
                let text = m.text(decl.name.sym);
                let Some((field, ty)) = fields.iter().find(|(field, _)| **field == *text) else { continue };
                let reach = self.p.decls.reach(ty, &[]).without_params();
                if *ty == Ty::Error || reach.covered_by(&declared) {
                    continue;
                }
                let message = format!(
                    "`{}` declares that it uses {}, but its field `{}` has type `{}`, which reaches more; an opaque record's `uses` covers what its fields reach (§9.2)",
                    m.text(name.sym),
                    self.show_reach(&declared),
                    field,
                    self.show(ty)
                );
                self.error(codes::REACH_NOT_ADMITTED, m.types[decl.ty].span, message);
            }
        }
    }

    /// How a diagnostic writes what a `uses` clause lists: `nothing`, or the list as written.
    fn show_reach(&self, reach: &Reach) -> String {
        if reach.is_empty() {
            return "nothing".into();
        }
        format!("`{}`", self.p.decls.display_in(&Ty::reach(reach.clone()), &self.param_names))
    }

    /// Reports each generic type that holds itself, directly or through other generic types,
    /// with a type argument that grows, such as `Nested[List[T]]` in `enum Nested[T]`
    /// (E0904). Each of its instances would need a bigger one, so they would never end
    /// (REFERENCE §4.8). This is the expanding-cycle rule of ECMA-335 II.9.2. A node is a
    /// type parameter of one of the module's generic types. A field's type argument gives an
    /// edge from each type parameter in it to the parameter it fills, which grows unless the
    /// argument is that type parameter itself. A cycle with a growing edge is the error,
    /// reported once at the first field whose type argument grows. Its types are taken to
    /// have every variant's values, so nothing that depends on them is reported (§15.1).
    fn expanding_types(&mut self) {
        let m = self.m;
        let mut first = vec![usize::MAX; self.adts.len()];
        let mut index: HashMap<AdtId, usize> = HashMap::new();
        let mut count = 0;
        for (k, adt) in self.adts.iter().enumerate() {
            let params = self.p.decls.adt(adt.id).params;
            if params > 0 {
                first[k] = count;
                index.insert(adt.id, k);
                count += params;
            }
        }
        if count == 0 {
            return;
        }
        // Each edge's target, whether it grows, and where the field's type is written.
        let mut edges: Vec<Vec<(usize, bool, Span)>> = vec![Vec::new(); count];
        for (k, adt) in self.adts.iter().enumerate() {
            if first[k] == usize::MAX {
                continue;
            }
            let def = self.p.decls.adt(adt.id);
            for (variant, (_, decls)) in def.variants.iter().zip(&adt.variants) {
                for (field, decl) in variant.fields.iter().zip(kept_fields(decls)) {
                    let span = m.types[decl.ty].span;
                    let mut stack = vec![&field.ty];
                    while let Some(ty) = stack.pop() {
                        let Ty::Adt(id, args) = ty else { continue };
                        if let Some(&j) = index.get(id) {
                            for (p, arg) in args.iter().enumerate() {
                                let mut params = Vec::new();
                                params_in(arg, &mut params);
                                for i in params {
                                    let grows = *arg != Ty::Param(i);
                                    edges[first[k] + i as usize].push((first[j] + p, grows, span));
                                }
                            }
                        }
                        stack.extend(args.iter());
                    }
                }
            }
        }
        let components = strongly_connected(&edges);
        let owner = |node: usize| {
            (0..self.adts.len()).rfind(|&k| first[k] != usize::MAX && first[k] <= node).expect("every node has a type")
        };
        let mut reports: Vec<(Span, Vec<usize>)> = Vec::new();
        for component in components {
            let growing = (component.iter())
                .flat_map(|&node| edges[node].iter())
                .filter(|(to, grows, _)| *grows && component.contains(to))
                .map(|&(_, _, span)| span)
                .min_by_key(|span| span.lo);
            if let Some(span) = growing {
                let mut types: Vec<usize> = component.iter().map(|&node| owner(node)).collect();
                types.sort_unstable();
                types.dedup();
                reports.push((span, types));
            }
        }
        reports.sort_by_key(|(span, _)| span.lo);
        for (span, types) in reports {
            let names: Vec<String> = types.iter().map(|&k| format!("`{}`", m.text(self.adts[k].name.sym))).collect();
            let holds = match names.as_slice() {
                [one] => format!("each time {one} holds itself"),
                _ => format!("on each turn of the cycle of {}", names.join(" and ")),
            };
            let message = format!(
                "this type argument grows {holds}, so its instances would never end; a generic type may hold itself only with its own type parameters (§4.8)"
            );
            self.error(codes::EXPANDING_TYPE, span, message);
            for k in types {
                self.p.decls.adt_mut(self.adts[k].id).unknown_variants = true;
            }
        }
    }

    /// Reports a type that `item`, declared with `vis`, may not mention because it is less
    /// visible (REFERENCE §3).
    fn exposes(&mut self, item: Ident, vis: Visibility, ty: &Ty, at: TypeId) {
        // Nothing is less visible than a private item.
        if reach(vis) == 0 {
            return;
        }
        let Some((named, named_vis)) = self.least_visible(ty) else { return };
        if reach(named_vis) < reach(vis) {
            let name = match named {
                Ok(record) => self.p.decls.adt(record).name.clone(),
                Err(iface) => self.p.decls.iface(iface).name.clone(),
            };
            let span = self.m.types[at].span;
            self.too_visible(item, vis, &name, named_vis, span);
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

    /// The least visible module record, enum or capability interface that `ty` mentions, the
    /// first one written of those equally visible, which is the first private one if there
    /// is one. A shared part is looked at once, so a type that repeats a part costs what its
    /// source does (issue #18).
    fn least_visible(&self, ty: &Ty) -> Option<(Result<AdtId, IfaceId>, Visibility)> {
        let mut least: Option<(Result<AdtId, IfaceId>, Visibility)> = None;
        let mut seen = HashSet::new();
        let mut work = vec![ty];
        while let Some(ty) = work.pop() {
            let named = match ty {
                Ty::Adt(id, _) => self.adt_vis.get(id).map(|&vis| (Ok(*id), vis)),
                _ => None,
            };
            // A capability type names its interface and those it uses, and a function type
            // those it uses.
            let ifaces = match ty {
                Ty::Cap(cap) => {
                    std::iter::once(cap.iface).chain(cap.uses.caps().iter().map(|&(iface, _)| iface)).collect()
                }
                Ty::Reach(uses) => uses.caps().iter().map(|&(iface, _)| iface).collect(),
                _ => Vec::new(),
            };
            let caps = ifaces.into_iter().filter_map(|iface| self.cap_vis.get(&iface).map(|&vis| (Err(iface), vis)));
            for (named, vis) in named.into_iter().chain(caps) {
                if least.is_none_or(|(_, least)| reach(vis) < reach(least)) {
                    least = Some((named, vis));
                }
            }
            if least.is_some_and(|(_, vis)| reach(vis) == 0) {
                break;
            }
            if let Some(parts) = ty.parts()
                && seen.insert(Arc::as_ptr(parts) as *const Ty as usize)
            {
                work.extend(parts.iter().rev());
            }
        }
        least
    }

    /// Declares the module's interfaces, whose methods are resolved once every type has a
    /// name.
    fn iface_names(&mut self) {
        let m = self.m;
        for item in &m.items {
            let ItemKind::Interface(decl) = &item.kind else { continue };
            let text = m.text(decl.name.sym);
            let cap = decl.cap.as_ref().map(|perms| self.cap_def(decl.name, perms));
            let def = IfaceDef { name: text.into(), cap, methods: Vec::new(), incomplete: decl.recovered };
            let id = self.p.decls.push_iface(def);
            self.ifaces.push(IfaceSrc { id, decl, vis: item.vis });
            if decl.cap.is_some() {
                self.cap_decls.insert(decl.name.sym);
                self.cap_vis.insert(id, item.vis);
            }
            let cased = self.pascal_case(decl.name, "interface");
            if !cased || prelude_type(text) {
                if cased {
                    let message = format!("this interface would shadow the prelude name `{text}` (H4)");
                    self.error(codes::SHADOWING, decl.name.span, message);
                }
                self.poisoned.insert(decl.name.sym);
            } else if self.adt_names.contains_key(&decl.name.sym)
                || self.aliases.contains_key(&decl.name.sym)
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

    /// The permissions a `cap interface` named `name` declares, each once (REFERENCE §9.2). A
    /// wrongly cased one stands for the one it misspells, so it is kept as written.
    fn cap_def(&mut self, name: Ident, perms: &CapPerms) -> CapDef {
        let mut def = CapDef { perms: Vec::new(), observes: Perms::NONE, lost: false };
        let declared = perms.observes.iter().map(|p| (p, true)).chain(perms.effects.iter().map(|p| (p, false)));
        for (perm, observes) in declared {
            let text = self.m.text(perm.sym);
            self.snake_case(*perm, "permission");
            if def.perm(text).is_some() {
                self.error(codes::DUPLICATE_NAME, perm.span, format!("permission `{text}` is declared twice"));
                continue;
            }
            if def.perms.len() == Perms::MAX {
                let what = format!(
                    "capability interfaces with more than {} permissions, such as `{}`,",
                    Perms::MAX,
                    self.m.text(name.sym)
                );
                self.not_implemented(perm.span, &what, Planned::Unscheduled);
                def.lost = true;
                break;
            }
            if observes {
                def.observes = def.observes.union(Perms::one(def.perms.len()));
            }
            def.perms.push(text.into());
        }
        def
    }

    /// The permissions of capability interface `iface` that `names` lists, each once, as an
    /// operation's `needs`, a capability type's brackets or `only::[…]` write them. One that
    /// isn't declared is reported, and left out, as is one written twice. `None` when one was.
    fn perms_named(&mut self, iface: IfaceId, names: &[Ident], what: &str) -> (Perms, bool) {
        let mut perms = Perms::NONE;
        let mut ok = true;
        for name in names {
            let text = self.m.text(name.sym);
            let def = self.p.decls.iface(iface);
            match def.cap.as_ref().and_then(|cap| cap.perm(text)) {
                Some(i) if perms.contains(i) => {
                    self.error(codes::DUPLICATE_NAME, name.span, format!("{what} names `{text}` twice"));
                    ok = false;
                }
                Some(i) => perms = perms.union(Perms::one(i)),
                // It may be one of those past the limit, which was reported (§15.1).
                None if def.cap.as_ref().is_some_and(|cap| cap.lost) => ok = false,
                None => {
                    let message = format!("`{}` declares no permission `{text}`", def.name);
                    self.error(codes::UNKNOWN_MEMBER, name.span, message);
                    ok = false;
                }
            }
        }
        (perms, ok)
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
        for &sym in &m.everywhere {
            let iface = self.iface_names.get(&sym).copied().or_else(|| IfaceId::prelude(m.text(sym)));
            if let Some(iface) = iface {
                self.p.decls.mark_everywhere(iface);
            }
        }
    }

    /// Notes that a rejected `impl` block is for the type `sym` names, if any.
    fn unknown_target(&mut self, sym: Symbol) {
        let text = self.m.text(sym);
        let prelude = prelude_adt(text).or_else(|| collection_adt(text));
        let ty = match (self.adt_names.get(&sym), builtin_type(text), prelude, self.imports.get(&sym)) {
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
            self.cap_self = decl.cap.is_some();
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
                // Every capability has `only`, which narrows its permissions (REFERENCE §9.2).
                // The operation's calls may mean either, so they aren't checked (§15.1). An
                // interface the parser rejected may not have been meant as a capability.
                let only = cased && decl.cap.is_some() && text == "only";
                if only {
                    if !m.poisoned.contains(&decl.name.sym) {
                        let message = "every capability has a method `only`, which narrows its permissions, so an operation can't be named `only`";
                        self.error(codes::DUPLICATE_NAME, method.name.span, message);
                    }
                    self.only_declared.insert(id);
                }
                let receiver = method.receiver.expect("the parser keeps only interface methods with `self`");
                let later = match receiver.mode {
                    ParamMode::Borrow | ParamMode::Take => None,
                    // Retention comes with the capabilities (OPEN_QUESTIONS P3).
                    ParamMode::Keep => Some(("`keep self` methods", Planned::Phase(3))),
                    ParamMode::Inout => Some(("interface methods that take `inout self`", Planned::Unscheduled)),
                    ParamMode::InoutPartial => {
                        Some(("interface methods that take `inout(partial) self`", Planned::Unscheduled))
                    }
                };
                if let Some((what, planned)) = later {
                    self.not_implemented(receiver.span, what, planned);
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
                    // Through a handle, an argument of type `Self` may be another implementation,
                    // which the operation's own can't read (OPEN_QUESTIONS P5).
                    if decl.cap.is_some() && mentions_param(&ty, 0) {
                        let span = m.types[param.ty].span;
                        self.not_implemented(
                            span,
                            "parameters of type `Self` in a `cap interface`'s operations",
                            Planned::Unscheduled,
                        );
                        incomplete = true;
                        continue 'methods;
                    }
                    self.exposes(decl.name, vis, &ty, param.ty);
                    params.push((name.into(), ty));
                    modes.push(param.mode);
                }
                let ret = method.ret.map_or(Ty::Unit, |t| self.part_type(t, "a result"));
                let fails = method.fails.map(|t| self.part_type(t, "an error type")).filter(|t| *t != Ty::Never);
                let fails = self.error_type(fails, method.fails);
                if let Some(at) = method.ret {
                    self.exposes(decl.name, vis, &ret, at);
                }
                if let Some(at) = method.fails {
                    self.exposes(decl.name, vis, &fails.clone().unwrap_or(Ty::Never), at);
                }
                let (needs, _) = self.perms_named(id, &method.needs, "`needs`");
                if cased && !duplicate && !only {
                    methods.push(IfaceMethod {
                        name: text.into(),
                        self_mode: receiver.mode,
                        params,
                        modes,
                        ret,
                        fails,
                        needs,
                    });
                }
            }
            let def = self.p.decls.iface_mut(id);
            def.methods = methods;
            def.incomplete = incomplete;
        }
        self.self_ty = None;
        self.cap_self = false;
        self.param_names.clear();
    }

    /// Resolves every `derives` list. Whether each field implements what its record or enum
    /// derives is checked once the `impl` blocks are known.
    fn adt_derives(&mut self) {
        let m = self.m;
        // A distinct type's operator derives, checked once every type's derives are known, so
        // the wrapped type may be declared later.
        let mut operators = Vec::new();
        for k in 0..self.adts.len() {
            let (id, derives_of) = (self.adts[k].id, self.adts[k].derives);
            // A `cap record`'s `derives` is reported by the parser. It may have named any
            // interface, so the record is taken to have each, and any method (§15.1).
            if self.p.decls.adt(id).cap && !derives_of.is_empty() {
                self.p.decls.mark_unknown(ImplKey::Adt(id));
                continue;
            }
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
                let distinct = self.p.decls.adt(id).distinct;
                match IfaceId::prelude(text) {
                    Some(iface) if iface.derivable() => derives.push(iface),
                    // A distinct type derives an operator of the type it wraps (REFERENCE §4.6).
                    Some(iface) if distinct && op_iface(iface).is_some() => {
                        derives.push(iface);
                        operators.push((id, iface, *name));
                    }
                    Some(_) => {
                        unknown = true;
                        self.error(
                            codes::NOT_DERIVABLE,
                            name.span,
                            format!("`{text}` can't be derived; the derivable interfaces are {}", derivable(distinct)),
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
                            format!("unknown interface `{text}`; the derivable interfaces are {}", derivable(distinct)),
                        );
                    }
                }
            }
            let def = self.p.decls.adt_mut(id);
            def.derives = derives;
            def.unknown_interfaces |= unknown;
        }
        self.operators = operators;
    }

    /// Checks each operator a distinct type derives against the type it wraps, once every
    /// `impl` block is known, so one rejected for the wrapped type may have given it.
    fn operator_derives(&mut self) {
        let m = self.m;
        // Each is checked against the derives as written, so one that wraps a distinct type
        // whose own derive is rejected isn't reported again (REFERENCE §15.1).
        let missing: Vec<_> = std::mem::take(&mut self.operators)
            .into_iter()
            .filter(|&(id, iface, _)| {
                let wrapped = &self.p.decls.adt(id).variant().fields[0].ty;
                // A distinct type whose own derives are rejected may have meant this one, and so
                // may a rejected `impl` block for any record or enum (issue #55). A record or
                // enum can't derive an operator, so its rejected derives can't have meant it.
                if let Ty::Adt(of, _) = wrapped
                    && (self.p.decls.adt(*of).distinct && self.p.decls.adt(*of).unknown_interfaces
                        || self.p.decls.adt(*of).unknown_methods)
                {
                    return false;
                }
                let has = match op_iface(iface) {
                    Some(Some(op)) => self.has_arithmetic(op, wrapped),
                    _ => match wrapped {
                        Ty::Int(it) => it.is_signed(),
                        Ty::Float(_) => true,
                        Ty::Adt(of, _) => self.p.decls.adt(*of).derives.contains(&IfaceId::NEG),
                        _ => false,
                    },
                };
                !has && !wrapped.is_unknown()
            })
            .collect();
        for (id, iface, name) in missing {
            let wrapped = self.p.decls.adt(id).variant().fields[0].ty.clone();
            let operator = match op_iface(iface) {
                Some(Some(op)) => format!("`{}`", op.symbol()),
                _ => "unary `-`".to_string(),
            };
            let def = self.p.decls.adt(id);
            let message = format!(
                "`{}` wraps `{}`, which has no {operator}, so it can't derive `{}`",
                def.name,
                self.show(&wrapped),
                m.text(name.sym)
            );
            self.error(codes::MISSING_IMPLEMENTATION, name.span, message);
            let def = self.p.decls.adt_mut(id);
            def.derives.retain(|&derived| derived != iface);
            def.unknown_interfaces = true;
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
            self.param_names = adt.generics.iter().map(|g| m.text(g.name.sym).into()).collect();
            for &iface in def.derives.iter().filter(|iface| iface.derivable()) {
                // A generic type derives it for the type arguments that implement it, so each
                // type parameter is taken to (OPEN_QUESTIONS P5).
                let params = vec![vec![iface]; def.params];
                for (variant, (_, decls)) in def.variants.iter().zip(&adt.variants) {
                    for (field, field_decl) in variant.fields.iter().zip(kept_fields(decls)) {
                        if !field.ty.is_unknown() && !self.p.decls.implements(&field.ty, iface, &params) {
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
        self.param_names.clear();
    }

    /// Checks each refinement as a `Bool` in a scope of the fields it sees: its own field for
    /// a field's `where`, every field for a record's (OPEN_QUESTIONS P5).
    fn adt_predicates(&mut self) {
        let m = self.m;
        for k in 0..self.adts.len() {
            let id = self.adts[k].id;
            // A generic type's refinements see its type parameters, which implement nothing.
            let generics = self.adts[k].generics;
            self.generic_scope = generics.iter().enumerate().map(|(i, g)| (g.name.sym, Some(i as u32))).collect();
            self.param_names = generics.iter().map(|g| m.text(g.name.sym).into()).collect();
            for v in 0..self.adts[k].variants.len() {
                let kept = kept_fields(self.adts[k].variants[v].1);
                let fields = &self.p.decls.adt(id).variants[v].fields;
                let mut state = FnState::new(Ty::Unit, None);
                state.bounds = vec![Vec::new(); generics.len()];
                state.returns = false;
                state.refinement = true;
                state.params = fields.len();
                state.locals = fields
                    .iter()
                    // A refinement looks at the value it checks, so the fields are lent to it.
                    .map(|f| Local { ty: f.ty.clone(), mutable: false, borrowed: true, in_loop: false })
                    .collect();
                self.f = state;
                let mut preds = Vec::new();
                let mut read = HashSet::new();
                for (i, field) in kept.iter().enumerate() {
                    if let Some(expr) = field.refinement {
                        self.f.scopes = vec![vec![(field.name.sym, LocalId(i as u32))]];
                        self.check(expr, &Ty::Bool);
                        self.settle();
                        read.extend(self.predicate_moves(expr));
                        preds.push(Pred { expr, field: Some(FieldIdx(i as u32)) });
                    }
                }
                if let Some(expr) = self.adts[k].refinement {
                    // A distinct type's `where` names its value `self` (REFERENCE §4.6).
                    self.f.distinct = self.p.decls.adt(id).distinct;
                    self.f.scopes = if self.f.distinct {
                        vec![m.interner.lookup("self").map(|sym| (sym, LocalId(0))).into_iter().collect()]
                    } else {
                        vec![kept.iter().enumerate().map(|(i, f)| (f.name.sym, LocalId(i as u32))).collect()]
                    };
                    self.check(expr, &Ty::Bool);
                    self.settle();
                    read.extend(self.predicate_moves(expr));
                    preds.push(Pred { expr, field: None });
                }
                let variant = &mut self.p.decls.adt_mut(id).variants[v];
                variant.preds = preds;
                variant.locals = self.f.locals.len();
                variant.read_fields = (0..variant.fields.len()).map(|i| read.contains(&LocalId(i as u32))).collect();
            }
        }
        self.generic_scope.clear();
        self.param_names.clear();
    }

    /// What the move pass needs to know of the body just checked, whose diagnostics begin at
    /// `start`.
    fn found(&mut self, start: usize) -> moves::Found {
        let errors = self.diags.iter().skip(start).filter(|d| d.severity == Severity::Error).map(|d| d.span).collect();
        moves::Found {
            consumed: std::mem::take(&mut self.consumed),
            rejected: std::mem::take(&mut self.rejected),
            method_values: std::mem::take(&mut self.method_values),
            errors,
        }
    }

    /// Checks what the refinement `expr` moves, which can't be the fields lent to it, and
    /// returns the locals it reads.
    fn predicate_moves(&mut self, expr: ExprId) -> HashSet<LocalId> {
        let m = self.m;
        let found = self.found(0);
        let body = moves::Body::Predicate(expr);
        moves::check(m, &mut self.p, &self.f.locals, &self.f.bounds, &found, body, self.diags)
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
                // A call may mean either function, so none is checked against one (§15.1).
                self.poisoned.insert(decl.name.sym);
                self.main_lost |= name == "main";
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
                impl_params: 0,
                receiver: None,
                self_mode: ParamMode::Borrow,
                owner: None,
                params: sig.params,
                ret: sig.ret,
                fails: sig.fails,
                locals: 0,
                owned: Vec::new(),
                rejected: sig.rejected,
            });
        }
    }

    /// Declares type parameters `params`, after those in `generics`, and puts them in scope.
    /// Their constraints are those of `item`, declared with `vis`, or of an `impl` block when
    /// `item` is `None` (REFERENCE §4.8).
    fn declare_generics(
        &mut self,
        params: &[GenericParam],
        item: Option<Ident>,
        vis: Visibility,
        generics: &mut Vec<GenericInfo>,
    ) {
        let m = self.m;
        for param in params {
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
                match self.bound(bound, item.unwrap_or(param.name), vis) {
                    Some(iface) if !bounds.contains(&iface) => bounds.push(iface),
                    Some(_) => {}
                    None => rejected = true,
                }
            }
            let index = generics.len() as u32;
            self.generic_scope.push((param.name.sym, (!rejected).then_some(index)));
            generics.push(GenericInfo { name: text.into(), sym: Some(param.name.sym), param: None, bounds, rejected });
        }
    }

    /// Puts the type parameters of the `impl` block being declared in scope, and only them.
    fn impl_scope(&mut self) {
        self.generic_scope = (self.impl_generics.iter().enumerate())
            .filter_map(|(i, g)| Some((g.sym?, (!g.rejected).then_some(i as u32))))
            .collect();
        self.param_names = self.impl_generics.iter().map(|g| g.name.clone()).collect();
    }

    /// Resolves the signature of a function, or of a method of an `impl` block for `owner`,
    /// and reports a type that a declaration with `vis` may not mention.
    fn signature(&mut self, decl: &FnDecl, vis: Visibility, owner: Option<Ty>) -> Signature {
        let m = self.m;
        // A method of a generic `impl` has the block's type parameters first.
        let mut generics: Vec<GenericInfo> = self.impl_generics.clone();
        self.impl_scope();
        self.declare_generics(&decl.generics, Some(decl.name), vis, &mut generics);
        self.param_names = generics.iter().map(|g| g.name.clone()).collect();
        // A type such as `Map[K, V]` asks what its type arguments implement.
        let outer_bounds = std::mem::replace(&mut self.f.bounds, generics.iter().map(|g| g.bounds.clone()).collect());
        self.self_ty = owner.clone();
        let mut rejected = false;
        let self_mode = decl.receiver.map_or(ParamMode::Borrow, |r| r.mode);
        // Retention comes with the capabilities (OPEN_QUESTIONS P3).
        if let Some(receiver) = decl.receiver
            && receiver.mode == ParamMode::Keep
        {
            self.not_implemented(receiver.span, "`keep self` methods", Planned::Phase(3));
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
                        self.f.bounds.push(vec![iface]);
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
            params.push(ParamInfo { name: param.name.sym, ty, mode: param.mode });
        }
        let ret = decl.ret.map_or(Ty::Unit, |t| self.part_type(t, "a result"));
        // `Never` has no values, so a function that fails with it cannot fail.
        let fails = decl.fails.map(|t| self.part_type(t, "an error type")).filter(|t| *t != Ty::Never);
        let fails = self.error_type(fails, decl.fails);
        let typed = decl.params.iter().map(|p| p.ty).chain(decl.ret).chain(decl.fails);
        let types = params.iter().map(|p| p.ty.clone()).chain(decl.ret.map(|_| ret.clone()));
        let types: Vec<(Ty, TypeId)> =
            types.chain(decl.fails.map(|_| fails.clone().unwrap_or(Ty::Never))).zip(typed).collect();
        for (ty, at) in types {
            self.exposes(decl.name, vis, &ty, at);
        }
        self.impl_scope();
        self.f.bounds = outer_bounds;
        self.self_ty = None;
        Signature { generics, receiver, self_mode, params, ret, fails, rejected }
    }

    /// The error type `fails` names, written at `at`. A resource can't be one (REFERENCE §10
    /// rule 5), and is reported and read as an unknown type.
    fn error_type(&mut self, fails: Option<Ty>, at: Option<TypeId>) -> Option<Ty> {
        match (fails, at) {
            (Some(ty), Some(at)) if self.p.decls.is_resource(&ty) => {
                let message = format!(
                    "`{}` is a resource, which can't be an error type, since a failure would lose it (§10)",
                    self.show(&ty)
                );
                self.error(codes::RESOURCE_ERROR_TYPE, self.m.types[at].span, message);
                Some(Ty::Error)
            }
            (fails, _) => fails,
        }
    }

    /// Whether `sym` names a type here, which a type parameter may not reuse (H4).
    fn names_type(&self, sym: Symbol) -> bool {
        prelude_type(self.m.text(sym))
            || self.adt_names.contains_key(&sym)
            || self.aliases.contains_key(&sym)
            || matches!(self.imports.get(&sym), Some(Import::Type(_)))
            || self.iface_names.contains_key(&sym)
    }

    /// Whether `sym` names a capability interface such as `Out`, which is a type of its own
    /// rather than a constraint (REFERENCE §9.2).
    fn names_cap(&self, sym: Symbol) -> bool {
        self.cap_named(sym).is_some()
    }

    /// The capability interface `sym` names: the module's, or one imported from the standard
    /// library, such as `Out`.
    fn cap_named(&self, sym: Symbol) -> Option<IfaceId> {
        if self.poisoned.contains(&sym) {
            return None;
        }
        match (self.iface_names.get(&sym), self.imports.get(&sym)) {
            (Some(&id), _) if self.p.decls.iface(id).cap.is_some() => Some(id),
            (_, Some(Import::Type(Ty::Cap(cap)))) => Some(cap.iface),
            _ => None,
        }
    }

    /// The interface a parameter's type names, when it is one, which makes the parameter
    /// generic (REFERENCE §4.9). A capability interface is a type of its own.
    fn param_iface(&self, t: TypeId) -> Option<Ident> {
        let TypeExprKind::Named(name) = self.m.types[t].kind else { return None };
        if self.poisoned.contains(&name.sym)
            || self.generic_scope.iter().any(|(sym, _)| *sym == name.sym)
            || self.names_cap(name.sym)
        {
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
        // A capability interface always dispatches, so `x: T` with `T: Out` would say no more
        // than `x: Out` (OPEN_QUESTIONS Q31).
        if self.names_cap(name.sym) {
            let message = format!(
                "`{text}` is a capability interface, which is a type of its own, so it can't be a constraint; write the parameter's type as `{text}`"
            );
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return None;
        }
        if let Some(&id) = self.iface_names.get(&name.sym) {
            let own = self.ifaces.iter().find(|src| src.id == id).map_or(Visibility::Pub, |src| src.vis);
            if reach(own) < reach(vis) {
                self.too_visible(item, vis, text, own, name.span);
            }
            return Some(id);
        }
        match IfaceId::prelude(text) {
            Some(iface @ (IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::HASH | IfaceId::COPY)) => Some(iface),
            // A type argument that is a resource waits for the reference (OPEN_QUESTIONS §G),
            // and only a resource implements `Abandon`.
            Some(IfaceId::ABANDON) => {
                self.not_implemented(name.span, "`Abandon` constraints", Planned::Unscheduled);
                None
            }
            Some(_) => {
                self.not_implemented(name.span, &format!("`{text}` constraints"), Planned::Unscheduled);
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

    /// Reports each `resource record` without an `impl Abandon`, since every resource type
    /// implements it (REFERENCE §10).
    fn abandon_impls(&mut self) {
        for k in 0..self.adts.len() {
            let (id, name) = (self.adts[k].id, self.adts[k].name);
            let def = self.p.decls.adt(id);
            if !def.resource_base || def.unknown_interfaces || self.poisoned.contains(&name.sym) {
                continue;
            }
            // A second declaration of the name is reported as such, and the `impl` names the
            // first (REFERENCE §15.1).
            let duplicate = self.adts[..k].iter().any(|earlier| earlier.name.sym == name.sym);
            if !duplicate && self.p.decls.impl_of(IfaceId::ABANDON, ImplKey::Adt(id)).is_none() {
                let text = self.m.text(name.sym);
                let message = format!(
                    "`{text}` is a resource, so it must implement `Abandon`, whose `abandon` ends it on a failure exit (§10)"
                );
                self.error(codes::MISSING_IMPLEMENTATION, name.span, message);
            }
        }
    }

    /// Declares an `impl` block, whose type parameters its target and its methods name.
    fn impl_block(&mut self, item: usize, span: Span, decl: &ImplDecl) {
        let mut generics = Vec::new();
        self.declare_generics(&decl.generics, None, Visibility::Private, &mut generics);
        self.impl_generics = generics;
        self.impl_scope();
        let outer =
            std::mem::replace(&mut self.f.bounds, self.impl_generics.iter().map(|g| g.bounds.clone()).collect());
        self.impl_members(item, span, decl);
        self.impl_generics.clear();
        self.impl_scope();
        self.f.bounds = outer;
    }

    fn impl_members(&mut self, item: usize, span: Span, decl: &ImplDecl) {
        let m = self.m;
        let target_span = m.types[decl.target].span;
        let header = span.to(target_span);
        // A parameter with a rejected constraint still has its place in the target, so the
        // block is for `Box[T]`, any box, and not for an unknown type (§15.1). Matching takes
        // it to meet any constraint, and a field of its type is unknown in the block's bodies.
        // One that names a type may have meant the type, so it leaves the target unknown.
        let unscoped: Vec<(Symbol, u32)> = (self.impl_generics.iter().enumerate())
            .filter(|(_, g)| g.rejected)
            .filter_map(|(i, g)| Some((g.sym?, i as u32)))
            .filter(|&(sym, _)| !self.names_type(sym))
            .collect();
        for (sym, index) in self.generic_scope.iter_mut() {
            if let Some(&(_, i)) = unscoped.iter().find(|(s, _)| s == sym) {
                index.get_or_insert(i);
            }
        }
        let target = self.resolve_type(decl.target);
        self.impl_scope();
        // Only the target gives the block's type parameters, so one it doesn't name could
        // be any type at each call (OPEN_QUESTIONS P5). It stands for an unknown type. A
        // target without an error names no parameter whose constraint was rejected, which
        // is reported too (issue #53).
        if !mentions_error(&target) {
            let mut used = Vec::new();
            params_in(&target, &mut used);
            for (i, param) in decl.generics.iter().enumerate() {
                if self.impl_generics[i].sym.is_none() || used.contains(&(i as u32)) {
                    continue;
                }
                let message = format!(
                    "type parameter `{}` doesn't appear in the target `{}`, so nothing gives it; a block's type parameters are those its target names",
                    m.text(param.name.sym),
                    self.show(&target)
                );
                self.error(codes::CANNOT_INFER, param.name.span, message);
                self.impl_generics[i].rejected = true;
            }
            self.impl_scope();
        }
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
        // A capability type gets its operations from its interface. Whether it may have methods
        // or implement interfaces of its own isn't decided (OPEN_QUESTIONS P5).
        if let Ty::Cap(_) = target {
            let what = format!("implementations for capability types such as `{}`", self.show(&target));
            self.not_implemented(target_span, &what, Planned::Unscheduled);
            self.declare_rejected(item, decl, &target);
            self.unknown_ty(&target);
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
        // A capability interface is implemented in Proviso by a `cap record`, whose values are
        // handles that copies share (REFERENCE §9.6).
        if self.p.decls.iface(iface).cap.is_some() && !matches!(&target, Ty::Adt(id, _) if self.p.decls.adt(*id).cap) {
            let message = format!(
                "only a `cap record` implements a capability interface such as `{iface_text}`, and `{target_text}` isn't one (§9.6)"
            );
            self.error(codes::NOT_IMPLEMENTABLE, iface_name.span, message);
            self.reject_impl(item, decl, &target, Rejected { unknown: true, bodies: true });
            return;
        }
        // Dispatch reads the type of the receiver's value, which `Never` has none of.
        let Some(key) = key else {
            self.not_implemented(target_span, "implementations for `Never`", Planned::Unscheduled);
            self.unknown_ty(&target);
            return;
        };
        // A `resource record` is a base resource, which its own `abandon` ends, and any other
        // resource abandons what it holds (REFERENCE §10 rule 4).
        if iface == IfaceId::ABANDON && !matches!(&target, Ty::Adt(id, _) if self.p.decls.adt(*id).resource_base) {
            // A name declared twice, once as a resource, may mean that declaration, which is
            // reported as a duplicate.
            let twice = match &target {
                Ty::Adt(id, _) => self.adts.iter().find(|a| a.id == *id).is_some_and(|found| {
                    let mut named = self.adts.iter().filter(|a| a.name.sym == found.name.sym);
                    named.clone().count() > 1 && named.any(|a| self.p.decls.adt(a.id).resource_base)
                }),
                _ => false,
            };
            if twice {
                // Reported at the second declaration.
            } else if self.p.decls.is_resource(&target) {
                let message = format!(
                    "`{target_text}` is a resource because it holds one, so it implements `Abandon` by itself, abandoning what it holds (§10)"
                );
                self.error(codes::NOT_IMPLEMENTABLE, iface_name.span, message);
            } else {
                let message = format!("`{target_text}` isn't a resource, so it has nothing to abandon (§10)");
                self.error(codes::ABANDON_NOT_RESOURCE, iface_name.span, message);
            }
            let first = self.p.fns.len();
            self.declare_rejected(item, decl, &target);
            self.rejected_abandon.extend(first..self.p.fns.len());
            // A resource implements `Abandon` by itself, so calls of `abandon` on it resolve. On
            // another type, a call of a method the block declares may mean it, so it isn't
            // reported.
            if let Ty::Adt(adt, _) = target
                && !self.p.decls.is_resource(&target)
            {
                self.rejected_abandon_for.push((target.clone(), self.impl_generics.len()));
                let entries = self.inherent.entry(adt).or_default();
                for (i, method) in decl.methods.iter().enumerate() {
                    entries.push(Inherent { name: method.decl.name.sym, f: first + i, rejected: true });
                }
            }
            return;
        }
        if let Ty::Adt(id, _) = &target
            && self.p.decls.adt(*id).derives.contains(&iface)
        {
            let message = format!("`{target_text}` derives `{iface_text}`, so it implements it already");
            self.error(codes::DUPLICATE_IMPLEMENTATION, header, message);
            // The block was meant to give its target the interface, which the derive alone
            // may not for these type arguments (§15.1).
            self.p.decls.mark_taken(iface, key, target.clone(), self.impl_generics.len());
            self.declare_rejected(item, decl, &target);
            return;
        }
        if let Some(earlier) = self.p.decls.impl_of(iface, key) {
            // A generic type has one `impl` of each interface, whatever the targets' type
            // arguments are (OPEN_QUESTIONS P5, §G).
            let (code, message) = if same_target(&earlier.target, &target) {
                self.p.decls.mark_taken(iface, key, target.clone(), self.impl_generics.len());
                (codes::DUPLICATE_IMPLEMENTATION, format!("`{target_text}` already implements `{iface_text}`"))
            } else {
                let earlier = self.p.decls.display_in(&earlier.target, &earlier.names).to_string();
                let head = match &target {
                    Ty::Adt(id, _) if self.p.decls.adt(*id).tuple => "a tuple type".to_string(),
                    Ty::Adt(id, _) => format!("`{}`", self.p.decls.name(*id)),
                    _ => format!("`{target_text}`"),
                };
                let message = format!(
                    "`{earlier}` already implements `{iface_text}`, and {head} has one `impl` of each interface, whatever its type arguments"
                );
                self.p.decls.mark_taken(iface, key, target.clone(), self.impl_generics.len());
                (codes::IMPLEMENTATION_HEAD_TAKEN, message)
            };
            self.error(code, header, message);
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
        let bounds =
            (self.impl_generics.iter()).map(|g| if g.rejected { Vec::new() } else { g.bounds.clone() }).collect();
        let names = self.impl_generics.iter().map(|g| g.name.clone()).collect();
        self.p.decls.add_impl(iface, key, ImplDef { methods: fns, target: target.clone(), bounds, names });
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
        // A capability interface of the standard library, such as `Out`, is imported.
        if let Some(iface) = self.cap_named(name.sym) {
            return Ok(iface);
        }
        if let Some(&id) = self.iface_names.get(&name.sym) {
            return Ok(id);
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
        if self.ifaces.iter().any(|src| src.id == iface) || self.p.decls.iface(iface).cap.is_some() {
            return Ok(());
        }
        let later = Rejected { unknown: true, bodies: false };
        match iface {
            // A hand-written `Ord` defines `<` and the rest by its `cmp` (OPEN_QUESTIONS P5).
            IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::ABANDON => Ok(()),
            IfaceId::COPY => {
                let message =
                    "`Copy` holds by itself for copyable types with no reach, so it can't be implemented (§5.1)";
                self.error(codes::NOT_IMPLEMENTABLE, name.span, message);
                Err(Rejected { unknown: false, bodies: true })
            }
            IfaceId::HASH => {
                self.not_implemented(name.span, "hand-written `Hash` implementations", Planned::Unscheduled);
                Err(later)
            }
            _ => {
                let text = self.m.text(name.sym);
                self.not_implemented(name.span, &format!("`{text}` implementations"), Planned::Unscheduled);
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
            impl_params: self.impl_generics.len(),
            receiver: sig.receiver,
            self_mode: sig.self_mode,
            owner: Some(owner.clone()),
            params: sig.params,
            ret: sig.ret,
            fails: sig.fails,
            locals: 0,
            owned: Vec::new(),
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
        if info.generics.len() == info.impl_params
            && info.receiver.is_some()
            && info.self_mode == want.self_mode
            && params_agree
            && same(&want.ret, &info.ret)
            && fails_agree
        {
            return true;
        }
        let (decls, names) = (&self.p.decls, &self.param_names);
        let receiver = if want.self_mode == ParamMode::Take { "take self" } else { "self" };
        let mut declared = format!("fn {}({receiver}", want.name);
        for ((param, ty), mode) in want.params.iter().zip(&want.modes) {
            let mode = match mode {
                ParamMode::Borrow => "",
                ParamMode::Keep => "keep ",
                ParamMode::Take => "take ",
                ParamMode::Inout | ParamMode::InoutPartial => "inout ",
            };
            declared.push_str(&format!(", {param}: {mode}{}", decls.display_in(&ty.subst(&args), names)));
        }
        declared.push(')');
        if want.ret != Ty::Unit {
            declared.push_str(&format!(" -> {}", decls.display_in(&want.ret.subst(&args), names)));
        }
        if let Some(err) = &want.fails {
            declared.push_str(&format!(" fails {}", decls.display_in(&err.subst(&args), names)));
        }
        let message = format!(
            "`{}` must be declared as `{}` declares it, with `Self` as `{}`: `{declared}`",
            m.text(name.sym),
            decls.iface(iface).name,
            decls.display_in(target, names)
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
            // A `main` that failed to parse or clashed has been reported (§15.1).
            if self.opts.needs_main && !self.main_lost {
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
            TypeExprKind::Fn { ref params, ret, fails, ref uses } => self.fn_type(params, ret, fails, uses),
            // Whether the `cap record` that implements it may use more isn't scheduled
            // (OPEN_QUESTIONS P5; issue #64).
            TypeExprKind::Uses { base, .. }
                if self.cap_self && matches!(m.types[base].kind, TypeExprKind::SelfType) =>
            {
                self.self_uses(te.span);
                Ty::Error
            }
            TypeExprKind::Uses { base, ref uses } => {
                let base_ty = self.resolve_type(base);
                let uses = self.uses_list(uses);
                match (base_ty, uses) {
                    (Ty::Cap(cap), Some(uses)) => Ty::cap_uses(cap.iface, cap.perms, cap.uses.union(&uses)),
                    (Ty::Error, _) | (_, None) => Ty::Error,
                    (ty, Some(_)) => {
                        let message = format!(
                            "`{}` isn't a capability type, so it has no `uses`; a capability type or a function type has one (§9.2, §9.4)",
                            self.show(&ty)
                        );
                        self.error(codes::UNKNOWN_TYPE, m.types[base].span, message);
                        Ty::Error
                    }
                }
            }
            TypeExprKind::Rejected => Ty::Error,
            TypeExprKind::Tuple(ref elements) => {
                let tys = elements.iter().map(|&t| self.part_type(t, "a tuple's element")).collect();
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
                // A rejected declaration's type arguments mean the same whichever one it was.
                // A later phase's item, such as a capability record, or a rejected capability
                // interface takes permissions, which aren't types, as in `Logger[write]`.
                if self.poisoned.contains(&name.sym) {
                    if !m.planned_names.contains(&name.sym) && !self.cap_decls.contains(&name.sym) {
                        for &arg in args.as_deref().unwrap_or_default() {
                            self.resolve_type(arg);
                        }
                    }
                    return Ty::Error;
                }
                if self.generic_scope.iter().any(|(sym, _)| *sym == name.sym) {
                    self.error(codes::UNKNOWN_TYPE, te.span, format!("`{text}` takes no type arguments"));
                    return Ty::Error;
                }
                if let Some(iface) = self.cap_named(name.sym) {
                    return self.cap_type(iface, args.as_deref().unwrap_or_default());
                }
                // `x: Show[Int]` means `[T: Show[Int]]` (REFERENCE §4.9), and generic
                // interfaces are not yet scheduled (OPEN_QUESTIONS P5; issue #53).
                if self.iface_names.contains_key(&name.sym) || IfaceId::prelude(text).is_some() {
                    self.not_implemented(te.span, "generic interfaces", Planned::Unscheduled);
                    return Ty::Error;
                }
                if let Some(id) = self.generic_adt(name.sym) {
                    let args = args.as_deref().unwrap_or_default();
                    let tys: Vec<Ty> = args.iter().map(|&arg| self.part_type(arg, "a type argument")).collect();
                    let n = self.p.decls.adt(id).params;
                    if tys.len() != n {
                        let verb = if tys.len() == 1 { "was" } else { "were" };
                        let message = format!("`{text}` takes {}, but {} {verb} given", type_args(n), tys.len());
                        self.error(codes::UNKNOWN_TYPE, te.span, message);
                        return Ty::Error;
                    }
                    // A map's keys implement `Eq` and `Hash` (REFERENCE §4.2), so its methods
                    // need not ask again.
                    if id == AdtId::MAP {
                        let (bounds, names) = (self.f.bounds.clone(), self.param_names.clone());
                        if let Some(keys) = self.written_keys.as_mut() {
                            keys.push(WrittenKey { key: tys[0].clone(), span: te.span, bounds, names });
                        } else if !self.key_bound(&tys[0], te.span) {
                            return Ty::Error;
                        }
                    }
                    return Ty::applied(id, tys);
                }
                if self.adt_names.contains_key(&name.sym)
                    || self.aliases.contains_key(&name.sym)
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
                    None if prelude_enum(text).is_some() => {
                        self.error(codes::UNKNOWN_TYPE, te.span, format!("`{text}` takes no type arguments"))
                    }
                    None => match later_type(text).or_else(|| unexported_type(text)) {
                        Some(planned) => self.not_implemented(name.span, &format!("`{text}` types"), planned),
                        None => self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown type `{text}`")),
                    },
                }
                Ty::Error
            }
        }
    }

    /// `Log[read, append]`: capability interface `iface` with the permissions `args` name, each
    /// once (REFERENCE §9.2). A mistake in them makes the type unknown, so its uses aren't
    /// reported (§15.1).
    fn cap_type(&mut self, iface: IfaceId, args: &[TypeId]) -> Ty {
        let m = self.m;
        let mut names = Vec::new();
        for &arg in args {
            match m.types[arg].kind {
                TypeExprKind::Named(name) => names.push(name),
                _ => {
                    let def = self.p.decls.iface(iface);
                    let message = format!(
                        "a capability type names permissions of `{}`, as in `{}[{}]`",
                        def.name,
                        def.name,
                        self.p.decls.perm_names(iface, def.all_perms())
                    );
                    self.error(codes::UNKNOWN_TYPE, m.types[arg].span, message);
                    return Ty::Error;
                }
            }
        }
        match self.perms_named(iface, &names, "a capability type") {
            (perms, true) => Ty::cap(iface, perms),
            _ => Ty::Error,
        }
    }

    /// The type written at `t` where a function type can't be: a field, a result, an error, a
    /// type argument or a tuple's element. A function value there could outlive what it
    /// captures (REFERENCE §6.7, OPEN_QUESTIONS P5).
    fn part_type(&mut self, t: TypeId, what: &str) -> Ty {
        let ty = self.resolve_type(t);
        if !matches!(ty, Ty::Fn(..)) {
            return ty;
        }
        let message =
            format!("a function type can't be {what}, since a function value lives only as long as what it captures");
        self.error(codes::FUNCTION_VALUE_ESCAPES, self.m.types[t].span, message);
        Ty::Error
    }

    /// `fn(A, inout B) -> R fails E uses C` (REFERENCE §9.4). A parameter may be a function
    /// too.
    fn fn_type(
        &mut self,
        params: &[(ParamMode, TypeId)],
        ret: Option<TypeId>,
        fails: Option<TypeId>,
        uses: &[TypeId],
    ) -> Ty {
        let modes = params.iter().map(|&(mode, _)| mode).collect();
        let tys = params.iter().map(|&(_, t)| self.resolve_type(t)).collect();
        let ret = ret.map_or(Ty::Unit, |t| self.part_type(t, "a result"));
        let at = fails;
        let fails = fails.map(|t| self.part_type(t, "an error type")).filter(|t| *t != Ty::Never);
        let fails = self.error_type(fails, at).unwrap_or(Ty::Never);
        match self.uses_list(uses) {
            Some(uses) => Ty::func_uses(modes, tys, ret, fails, Ty::reach(uses)),
            None => Ty::Error,
        }
    }

    /// What the capability types `uses` lists reach together: each of them and what it uses
    /// (REFERENCE §9.2). `None` when one isn't a capability type, which is reported, or has an
    /// error.
    fn uses_list(&mut self, uses: &[TypeId]) -> Option<Reach> {
        self.exposed_uses(uses, None)
    }

    /// [`Self::uses_list`] of the declaration `item`, declared with a visibility, which may not
    /// name a capability less visible than itself (§3).
    fn exposed_uses(&mut self, uses: &[TypeId], item: Option<(Ident, Visibility)>) -> Option<Reach> {
        let mut reach = Reach::default();
        let mut known = true;
        for &t in uses {
            // A capability that uses its own implementation isn't scheduled (OPEN_QUESTIONS P5).
            if self.cap_self && matches!(self.m.types[t].kind, TypeExprKind::SelfType) {
                self.self_uses(self.m.types[t].span);
                known = false;
                continue;
            }
            match self.resolve_type(t) {
                Ty::Cap(cap) => {
                    reach.extend(&Reach::of_cap(&cap));
                    if let Some((name, vis)) = item {
                        self.exposes(name, vis, &Ty::Cap(cap), t);
                    }
                }
                Ty::Error => known = false,
                ty => {
                    let message = format!(
                        "`uses` lists capability types, such as `Out` or `Dir[read]`, and `{}` isn't one (§9.4)",
                        self.show(&ty)
                    );
                    self.error(codes::UNKNOWN_TYPE, self.m.types[t].span, message);
                    known = false;
                }
            }
        }
        known.then_some(reach)
    }

    /// Reports `Self` before `uses` or in a `uses` list of a `cap interface`.
    fn self_uses(&mut self, span: Span) {
        self.not_implemented(span, "`uses` clauses with a `cap interface`'s `Self`", Planned::Unscheduled);
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
        if let Some(id) = prelude_enum(text) {
            return Ty::adt(id);
        }
        if self.aliases.contains_key(&name.sym) {
            return self.alias_type(name.sym);
        }
        if let Some(id) = self.generic_adt(name.sym) {
            let message =
                format!("`{text}` takes {}, as in `{}`", type_args(self.p.decls.adt(id).params), self.example_of(id));
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return Ty::Error;
        }
        if let Some(&id) = self.adt_names.get(&name.sym) {
            return Ty::adt(id);
        }
        match self.imports.get(&name.sym) {
            Some(Import::Type(ty)) => return ty.clone(),
            Some(Import::Module) => {
                self.error(codes::UNKNOWN_TYPE, name.span, format!("`{text}` is a module, not a type"));
                return Ty::Error;
            }
            None => {}
        }
        // A bare capability interface has every permission it declares (OPEN_QUESTIONS Q6).
        if let Some(iface) = self.cap_named(name.sym) {
            return Ty::cap(iface, self.p.decls.iface(iface).all_perms());
        }
        if self.iface_names.contains_key(&name.sym) || IfaceId::prelude(text).is_some() {
            let message = format!(
                "`{text}` is an interface, not a type; only a parameter may have an interface type, which makes it generic (§4.9)"
            );
            self.error(codes::UNKNOWN_TYPE, name.span, message);
            return Ty::Error;
        }
        match later_type(text).or_else(|| unexported_type(text)) {
            Some(planned) => self.not_implemented(name.span, &format!("`{text}` types"), planned),
            None => self.error(codes::UNKNOWN_TYPE, name.span, format!("unknown type `{text}`")),
        }
        Ty::Error
    }

    /// How a message writes generic type `id` with its type parameters, as in `Pair[A, B]`.
    fn example_of(&self, id: AdtId) -> String {
        match self.adts.iter().find(|adt| adt.id == id) {
            Some(adt) => {
                let params: Vec<&str> = adt.generics.iter().map(|g| self.m.text(g.name.sym)).collect();
                format!("{}[{}]", self.m.text(adt.name.sym), params.join(", "))
            }
            None => example_type(&self.p.decls.adt(id).name).to_string(),
        }
    }

    /// The generic type `sym` names, which a use gives type arguments: the module's, the
    /// prelude's, or one imported from the standard library, such as `Pool`.
    fn generic_adt(&self, sym: Symbol) -> Option<AdtId> {
        let text = self.m.text(sym);
        if let Some(&id) = self.adt_names.get(&sym) {
            return (self.p.decls.adt(id).params > 0).then_some(id);
        }
        match self.imports.get(&sym) {
            Some(Import::Type(Ty::Adt(id, args))) if args.is_empty() && self.p.decls.adt(*id).params > 0 => Some(*id),
            Some(_) => None,
            None => prelude_adt(text).or_else(|| collection_adt(text)),
        }
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
        // A type parameter with a rejected declaration or constraint may have had any
        // constraint, so it meets every interface, and what needs one of it, such as a copy
        // or another block's constraint, isn't reported (§15.1; issue #53).
        let every: Vec<IfaceId> = self.p.decls.ifaces().map(|(iface, _)| iface).collect();
        state.bounds =
            (info.generics.iter()).map(|g| if g.rejected { every.clone() } else { g.bounds.clone() }).collect();
        state.rejected = info.generics.iter().map(|g| g.rejected).collect();
        state.anonymous = (info.generics.iter())
            .map(|g| Some((m.text(g.param?).into(), self.iface_name(*g.bounds.first()?).into())))
            .collect();
        self.generic_scope = (info.generics.iter().enumerate())
            .filter_map(|(i, g)| Some((g.sym?, (!g.rejected).then_some(i as u32))))
            .collect();
        self.param_names = info.generics.iter().map(|g| g.name.clone()).collect();
        self.self_ty = info.owner.clone();
        // The function borrows `self` and its parameters (REFERENCE §5.2). An `inout` one is
        // lent to it too, but it may change it. A `take` one is owned, and immutable as a `let`
        // is (OPEN_QUESTIONS P5).
        let local = |mode: ParamMode, ty: &Ty| {
            let mutable = matches!(mode, ParamMode::Inout | ParamMode::InoutPartial);
            Local { ty: ty.clone(), mutable, borrowed: mode != ParamMode::Take, in_loop: false }
        };
        let mut scope = Vec::new();
        if let Some(ty) = &info.receiver {
            state.locals.push(local(info.self_mode, ty));
            if let Some(sym) = m.interner.lookup("self") {
                scope.push((sym, LocalId(0)));
            }
        }
        for param in &info.params {
            scope.push((param.name, LocalId(state.locals.len() as u32)));
            state.locals.push(local(param.mode, &param.ty));
        }
        state.params = state.locals.len();
        state.scopes.push(scope);
        state.view = self.view_op(id);
        self.f = state;
        for param in &decl.params {
            self.shadows_item(param.name);
        }
        let start = self.diags.iter().count();
        self.fn_body(decl, body);
        self.settle();
        if self.f.view.is_some() {
            self.view_escapes();
        }
        let found = self.found(start);
        // The resources it owns from the start: its `take` parameters and a `take self`.
        let info = &self.p.fns[id];
        let decls = &self.p.decls;
        let mut params: Vec<(LocalId, Span, String)> = Vec::new();
        if let (Some(ty), Some(receiver)) = (&info.receiver, decl.receiver)
            && info.self_mode == ParamMode::Take
            && decls.is_resource(ty)
            && !self.rejected_abandon.contains(&id)
        {
            params.push((LocalId(0), receiver.span, "self".to_string()));
        }
        let first = usize::from(info.receiver.is_some());
        for (i, (param, at)) in info.params.iter().zip(&decl.params).enumerate() {
            if param.mode == ParamMode::Take && decls.is_resource(&param.ty) {
                params.push((LocalId((first + i) as u32), at.span, m.text(param.name).to_string()));
            }
        }
        // A `take self` method of a base resource consumes `self` when it returns, once it has
        // consumed what `self` holds (OPEN_QUESTIONS Q35).
        let consumes_self = info.self_mode == ParamMode::Take
            && matches!(&info.receiver, Some(Ty::Adt(adt, _)) if decls.adt(*adt).resource_base);
        // An `abandon` that hits a defect leaks `self`, rather than abandoning it again.
        let abandon = consumes_self
            && decls.impl_method(
                IfaceId::ABANDON,
                ImplKey::of(info.receiver.as_ref().expect("a method has a receiver")).expect("a record has a key"),
                0,
            ) == Some(id);
        let owned = params
            .iter()
            .filter(|(local, ..)| !(abandon && *local == LocalId(0)))
            .map(|(l, span, _)| (*l, *span))
            .collect();
        self.p.fns[id].owned = owned;
        let body = moves::Body::Fn(moves::FnBody { block: body, params, consumes_self });
        moves::check(m, &mut self.p, &self.f.locals, &self.f.bounds, &found, body, self.diags);
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
        let mut names: HashSet<&str> = HashSet::new();
        for (index, item) in m.items.iter().enumerate() {
            if let ItemKind::Test(decl) = &item.kind {
                // A second test of a name is checked, but its output would be ambiguous.
                if !names.insert(&decl.name) {
                    let message = format!("a test named \"{}\" is declared twice in this module", decl.name);
                    self.error(codes::DUPLICATE_ITEM, decl.name_span, message);
                }
                self.test(index, decl);
                continue;
            }
            let ItemKind::Example(decl) = &item.kind else { continue };
            let mut state = FnState::new(Ty::Unit, None);
            (state.returns, state.place) = (false, Place::Example);
            state.scopes.push(Vec::new());
            self.f = state;
            if self.names_construction(decl.call) {
                let span = self.span(decl.call);
                let message = "an example tests a function or method call, not a construction";
                self.error(codes::UNEXPECTED_TOKEN, span, message);
                continue;
            }
            let start = self.diags.iter().count();
            self.example(decl);
            self.settle();
            // An example drops what its call and its expected value give (REFERENCE §10).
            let found = self.found(start);
            let expected = match decl.expect {
                Expectation::Equals(x) => Some(x),
                Expectation::Fails(_) => None,
            };
            let body = moves::Body::Example { call: decl.call, expected };
            moves::check(m, &mut self.p, &self.f.locals, &[], &found, body, self.diags);
            self.p.examples.push(ExampleInfo { item: index, locals: self.f.locals.len() });
        }
    }

    /// Checks a `test "name" { … }` (REFERENCE §14). Its body is statements, with no function
    /// to return from or fail, and `expect` may be used in it.
    fn test(&mut self, index: usize, decl: &TestDecl) {
        let m = self.m;
        let mut state = FnState::new(Ty::Unit, None);
        (state.returns, state.place) = (false, Place::Test);
        state.scopes.push(Vec::new());
        self.f = state;
        let start = self.diags.iter().count();
        self.stmts(&decl.body.stmts);
        self.settle();
        let found = self.found(start);
        moves::check(m, &mut self.p, &self.f.locals, &[], &found, moves::Body::Test(&decl.body), self.diags);
        self.p.examples.push(ExampleInfo { item: index, locals: self.f.locals.len() });
    }

    /// Checks one example.
    fn example(&mut self, decl: &ExampleDecl) {
        self.expectation(decl.call, &decl.expect, "an example");
    }

    /// Checks what an example or an `expect` asserts about `call`, whose fallible calls it
    /// marks. `call == v` reads its operands as `==` does, so either may give the other its
    /// type (OPEN_QUESTIONS P5; issue #10).
    fn expectation(&mut self, call: ExprId, expect: &Expectation, what: &str) {
        self.markers.push(Marker { handler: Some(call), errors: Vec::new(), target: None });
        self.in_chain = true;
        let ty = self.expr(call, None);
        let errors = self.pop_marker();
        let span = self.span(call);
        let hole = self.met_hole(&errors);
        // "the calls this example marks", but "an example expects".
        let noun = what.strip_prefix("an ").unwrap_or(what);
        let err = self.one_error(errors, span, noun, &format!("{what} expects one error type"));
        match expect {
            Expectation::Equals(value) => {
                // A call that was rejected gives the value no type, and what the value leaves
                // open isn't reported, as with an operand of `==` (§15.1; issue #39).
                if ty == Ty::Error {
                    let value_ty = self.expr(*value, None);
                    self.vars.quiet(&value_ty);
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
                if !defined && !ty.is_unknown() && !holds_fn(&ty) {
                    let message = format!("`==` is not defined for `{}`, so {what} can't compare it", self.show(&ty));
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
        self.f.locals.push(Local { ty, mutable, borrowed, in_loop: what == "loop variable" });
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
                let typed = declared.is_some();
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
                self.let_pattern(*pat, &ty, *mutable, false);
                self.pattern_borrowed = false;
                // A local bound to a capability the view narrowed is narrowed too.
                if let Some(orig) = self.f.unnarrowed.get(init).cloned()
                    && !typed
                    && let Some(&id) = self.p.pat_local.get(*pat)
                {
                    self.f.unnarrowed_locals.insert(id, orig);
                }
                // The local holds what its function value captures alive (see `FnState::needs`).
                let needs = self.value_needs(*init);
                if needs > 0
                    && let PatKind::Bind(_) = self.m.pats[*pat].kind
                    && let Some(&id) = self.p.pat_local.get(*pat)
                {
                    self.f.local_needs.insert(id, needs);
                }
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
                    match self.f.place {
                        Place::Example => "`return` outside a function body; an example is an expression",
                        Place::Test => "`return` outside a function body; a test has no function to return from",
                        Place::Where => "`return` outside a function body; a `where` clause is an expression",
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
            StmtKind::Expect { value, expect } => {
                // A closure in a test runs when it is called, which may be after the test.
                if self.f.place != Place::Test || !self.closure_scopes.is_empty() {
                    let message = if self.f.place == Place::Test {
                        "`expect` in a closure; it belongs to the test's own body, which reports it (§14)"
                    } else {
                        "`expect` exists only in the body of a `test`; a function asserts with `assert` (§14)"
                    };
                    self.error(codes::MISPLACED_EXPECT, stmt.span, message);
                    self.rejected_value(*value);
                    if let Some(Expectation::Equals(other)) = expect {
                        self.rejected_value(*other);
                    }
                    return Flow::Finishes;
                }
                match expect {
                    None => {
                        let ty = self.check(*value, &Ty::Bool);
                        self.flow(&ty)
                    }
                    Some(expect) => {
                        self.expectation(*value, expect, "an `expect`");
                        Flow::Finishes
                    }
                }
            }
        }
    }

    /// Binds the names of a `let` or `var` pattern for a value of type `ty`, or of a `for`
    /// pattern for each element when `in_loop`. The pattern must match every value
    /// (REFERENCE §6.4; OPEN_QUESTIONS P5).
    fn let_pattern(&mut self, pat: PatId, ty: &Ty, mutable: bool, in_loop: bool) {
        let m = self.m;
        if let PatKind::Bind(name) = m.pats[pat].kind {
            let what = if in_loop {
                "loop variable"
            } else if mutable {
                "variable"
            } else {
                "binding"
            };
            let id = self.declare(name, ty.clone(), mutable, what, self.pattern_borrowed);
            self.p.pat_local.insert(pat, id);
            return;
        }
        (self.pattern_mutable, self.let_pattern, self.pattern_in_loop) = (mutable, true, in_loop);
        let space = self.pattern(pat, ty);
        (self.pattern_mutable, self.let_pattern, self.pattern_in_loop) = (false, false, false);
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
        let message = if in_loop {
            format!("{missing}, and a `for` pattern must match every element; use `match` or `is` in the body")
        } else {
            format!("{missing}, and a `let` pattern must match every value; use `match`, `is` or an `else` form")
        };
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
        let Some((root, id, ty, state)) = self.place(target) else { return self.infer(value) };
        if state {
            self.changes_state(id, span);
        } else if !self.f.locals[id.index()].mutable {
            let message = self.immutable(root, id, "assign to it");
            self.error(codes::IMMUTABLE_ASSIGNMENT, span, message);
        } else if self.changes_capture(id, span) {
            return self.rejected_value(value);
        }
        // A `var` given a function value could outlive what it captures (OPEN_QUESTIONS P5).
        // A `let` can't be given anything, which is reported already.
        if let Ty::Fn(..) = self.vars.resolve(&ty)
            && self.f.locals[id.index()].mutable
        {
            let message = "a `var` or an `inout` parameter can't be given a new function value, which could outlive what it captures";
            self.error(codes::FUNCTION_VALUE_ESCAPES, span, message);
            return self.rejected_value(value);
        }
        self.copying = true;
        let value_ty = self.check(value, &ty);
        if let Some(bin) = op.bin_op()
            && !self.has_arithmetic(bin, &ty)
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

    /// Resolves an assignment target, which is a variable or a chain of fields and elements
    /// rooted at one.
    /// Returns the variable, the type of the place and whether the chain goes through a `state`
    /// field, or `None` once it is reported.
    fn place(&mut self, target: ExprId) -> Option<(Ident, LocalId, Ty, bool)> {
        let m = self.m;
        let (root, id, ty, state) = match m.exprs[target].kind {
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
                self.capture(id, m.text(name.sym), name.span);
                (name, id, self.f.locals[id.index()].ty.clone(), false)
            }
            ExprKind::Field { base, name } => {
                let (root, id, base_ty, state) = self.place(base)?;
                let ty = self.field(target, &base_ty, name);
                // A field that isn't there, or that this code can't name, is reported, and so
                // is not what it would change (§15.1).
                if ty == Ty::Error && !self.p.res(target).is_some_and(|res| matches!(res, Res::Field(_))) {
                    return None;
                }
                (root, id, ty, state || self.is_state(&base_ty, target))
            }
            ExprKind::Index { base, index } => {
                let (root, id, base_ty, state) = self.place(base)?;
                let span = self.span(target);
                if let Ty::Adt(AdtId::POOL, _) = base_ty {
                    self.rejected_value(index);
                    self.pool_element(span);
                    return None;
                }
                (root, id, self.indexed(&base_ty, index, span)?, state)
            }
            _ => {
                let span = self.span(target);
                let message = "only variables and their fields and elements can be assigned";
                self.error(codes::INVALID_ASSIGNMENT_TARGET, span, message);
                return None;
            }
        };
        self.record(target, ty.clone());
        Some((root, id, ty, state))
    }

    /// Whether field `e` of a value of `base_ty`, which resolved, is a `state` field of a `cap
    /// record`, which every copy of the record shares (REFERENCE §9.6).
    fn is_state(&self, base_ty: &Ty, e: ExprId) -> bool {
        match (base_ty, self.p.res(e)) {
            (Ty::Adt(id, _), Some(Res::Field(i))) => {
                let def = self.p.decls.adt(*id);
                def.cap && def.variant().fields[i.index()].state
            }
            _ => false,
        }
    }

    /// Notes a change to a `state` field of a value of a `cap record`, whose root is local `id`.
    /// Any value of the record may change one, even a `let` or a borrowed parameter, since
    /// the change is to the state that the copies share (OPEN_QUESTIONS P5). An operation
    /// with the observes-only view can't change its own (Q39).
    fn changes_state(&mut self, id: LocalId, span: Span) {
        if id == LocalId(0) && self.f.view.is_some() {
            let message = self.view_message("its `state` is read-only");
            self.error(codes::EFFECTS_CALL_IN_OBSERVES, span, message);
        }
    }

    /// A message about operation `f.view`, which sees `self` through the observes-only view,
    /// where `what` is the problem (OPEN_QUESTIONS Q39).
    fn view_message(&self, what: &str) -> String {
        let (iface, op) = self.f.view.as_ref().expect("an operation with the view");
        format!(
            "`{op}` needs no `effects` permission of `{}`, so it sees `self` through the observes-only view, where {what} (§9.6)",
            self.iface_name(*iface)
        )
    }

    /// In an operation with the observes-only view, notes how `e`, of type `ty`, uses `self`
    /// (OPEN_QUESTIONS Q39). A path from `self` is read through, and a capability at its end
    /// is narrowed to its `observes` permissions, as is what it uses. `self`, a `cap record`
    /// at a path's end, and any other end with `effects` reach may be the base of a longer
    /// path, or the receiver of an operation that needs no `effects` permission, which their
    /// parents note. The rest leave the view, and are reported once the body is checked.
    fn view_expr(&mut self, e: ExprId, ty: Ty) -> Ty {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) => match self.p.res(e) {
                Some(Res::Local(LocalId(0))) if ty != Ty::Error => {
                    self.f.view_paths.insert(e);
                    self.f.escapes.insert(e, Escape::SelfValue);
                }
                Some(Res::Local(id)) => {
                    if let Some(orig) = self.f.unnarrowed_locals.get(&id).cloned() {
                        self.f.unnarrowed.insert(e, orig);
                    }
                }
                _ => {}
            },
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } if self.f.view_paths.contains(&base) => {
                self.f.escapes.remove(&base);
                if ty == Ty::Error {
                    return ty;
                }
                self.f.view_paths.insert(e);
                match &ty {
                    Ty::Cap(cap) => {
                        let narrowed = Ty::Cap(std::sync::Arc::new(self.observes_only(cap)));
                        if narrowed != ty {
                            self.f.unnarrowed.insert(e, ty);
                            return narrowed;
                        }
                    }
                    Ty::Adt(id, _) if self.p.decls.adt(*id).cap => {
                        self.f.escapes.insert(e, Escape::Record);
                    }
                    _ if self.effects_reach(&ty) => {
                        self.f.escapes.insert(e, Escape::Reaches);
                    }
                    _ => {}
                }
            }
            // The receiver of `I.f(x)` is its first argument.
            ExprKind::MethodCall { receiver, ref args, .. } => match self.p.res(e) {
                res @ Some(Res::Dispatch { qualified: true, .. }) => {
                    if let Some(first) = args.first() {
                        self.view_receiver(e, first.value, res);
                    }
                }
                res => self.view_receiver(e, receiver, res),
            },
            _ => {}
        }
        ty
    }

    /// Call `call` on `receiver`, which resolved to `res`, in an operation with the
    /// observes-only view. `self`, or a value at the end of a path from it that may leave
    /// the view, may be the receiver of an operation that needs no `effects` permission
    /// only (OPEN_QUESTIONS Q39).
    fn view_receiver(&mut self, call: ExprId, receiver: ExprId, res: Option<Res>) {
        let Some(escape) = self.f.escapes.remove(&receiver) else { return };
        let decls = &self.p.decls;
        match res {
            // A call that resolved to nothing is reported already (§15.1).
            None => return,
            Some(Res::Dispatch { iface, method, .. })
                if matches!(escape, Escape::SelfValue | Escape::Record)
                    && decls
                        .iface(iface)
                        .cap
                        .as_ref()
                        .is_some_and(|cap| decls.iface(iface).methods[method].needs.is_subset(cap.observes)) =>
            {
                return;
            }
            _ => {}
        }
        let what = match escape {
            Escape::SelfValue => "`self`".to_string(),
            Escape::Record | Escape::Reaches => format!("this `{}`", self.show(self.p.ty(receiver))),
        };
        let message = self.view_message(&format!(
            "a call on {what} may change what `self` reaches; only operations of a `cap interface` that need no `effects` permission are called on it"
        ));
        let span = self.span(call);
        self.error(codes::EFFECTS_CALL_IN_OBSERVES, span, message);
    }

    /// Reports each value that leaves the observes-only view, once the body is checked.
    fn view_escapes(&mut self) {
        let mut escapes: Vec<(ExprId, Escape)> = self.f.escapes.drain().collect();
        escapes.sort_by_key(|(e, _)| self.span(*e).lo);
        for (e, escape) in escapes {
            let what = match escape {
                Escape::SelfValue => {
                    "`self` may only be read through, or be the receiver of an operation that needs no `effects` permission".to_string()
                }
                Escape::Record => format!(
                    "this `{}` may only be read through, or be the receiver of an operation that needs no `effects` permission",
                    self.show(self.p.ty(e))
                ),
                Escape::Reaches => format!(
                    "this `{}` reaches `effects` permissions, so it may only be read through",
                    self.show(self.p.ty(e))
                ),
            };
            let message = self.view_message(&what);
            let span = self.span(e);
            self.error(codes::EFFECTS_CALL_IN_OBSERVES, span, message);
        }
    }

    /// `cap` narrowed to its interface's `observes` permissions, and using only theirs.
    fn observes_only(&self, cap: &CapTy) -> CapTy {
        let observes = |iface: IfaceId| self.p.decls.iface(iface).cap.as_ref().map_or(Perms::NONE, |c| c.observes);
        let mut uses = Reach::default();
        for &(iface, perms) in cap.uses.caps() {
            let kept = perms.intersect(observes(iface));
            if kept != Perms::NONE {
                uses.add_cap(iface, kept);
            }
        }
        for &i in cap.uses.params() {
            uses.extend(&Reach::param(i));
        }
        CapTy { iface: cap.iface, perms: cap.perms.intersect(observes(cap.iface)), uses }
    }

    /// Whether a value of type `ty` reaches an `effects` permission, or a type parameter.
    fn effects_reach(&self, ty: &Ty) -> bool {
        let reach = self.reach(ty);
        !reach.params().is_empty()
            || reach.caps().iter().any(|&(iface, perms)| {
                let observes = self.p.decls.iface(iface).cap.as_ref().map_or(Perms::NONE, |c| c.observes);
                perms.minus(observes) != Perms::NONE
            })
    }

    /// Reports a call of operation `j` on `receiver`, a capability of `iface` with `perms`
    /// that the observes-only view narrowed, which it would permit outside the view.
    fn view_permits(&mut self, receiver: ExprId, iface: IfaceId, perms: Perms, j: usize, span: Span) -> bool {
        let Some(Ty::Cap(orig)) = self.f.unnarrowed.get(&receiver) else { return false };
        let method = &self.p.decls.iface(iface).methods[j];
        if method.needs.is_subset(perms) || !method.needs.is_subset(orig.perms) {
            return false;
        }
        let missing = self.p.decls.perm_names(iface, method.needs.minus(perms));
        let name = method.name.clone();
        let message = self.view_message(&format!(
            "this capability has its `observes` permissions only, so it can't call `{name}`, which needs `{missing}`"
        ));
        self.error(codes::EFFECTS_CALL_IN_OBSERVES, span, message);
        true
    }

    /// For function `f`, an operation of a capability interface that a `cap record` implements
    /// and that needs no `effects` permission, the interface and the operation's name
    /// (OPEN_QUESTIONS Q39).
    fn view_op(&self, f: usize) -> Option<(IfaceId, Box<str>)> {
        let decls = &self.p.decls;
        let key = ImplKey::of(self.p.fns[f].owner.as_ref()?)?;
        decls.impls_for(key).find_map(|iface| {
            let def = decls.iface(iface);
            let cap = def.cap.as_ref()?;
            let j = (0..def.methods.len()).find(|&j| decls.impl_method(iface, key, j) == Some(f))?;
            let method = &def.methods[j];
            method.needs.minus(cap.observes).is_subset(Perms::NONE).then(|| (iface, method.name.clone()))
        })
    }

    /// Reports a change to a pool's element through `pool[h]` (OPEN_QUESTIONS P5).
    fn pool_element(&mut self, span: Span) {
        let message = "a pool's element can't be changed through `pool[h]`; `remove` it and `insert` the new value";
        self.error(codes::UNSUPPORTED_OPERATOR, span, message);
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
                | ExprKind::List(_)
                | ExprKind::Map(_)
                | ExprKind::Index { .. }
                | ExprKind::It
                | ExprKind::Closure(_)
                | ExprKind::Applied { .. }
        ) || matches!(self.m.exprs[e].kind, ExprKind::Else { value, .. } if self.is_bare_value(value))
    }

    fn jump(&mut self, s: StmtId, label: Option<Ident>, is_break: bool) {
        let span = self.m.stmts[s].span;
        let keyword = if is_break { "break" } else { "continue" };
        let index = match label {
            None if self.f.loops.is_empty() && !self.closure_scopes.is_empty() => {
                let message = format!(
                    "`{keyword}` can't leave a closure; its body ends with its value or a `return` (OPEN_QUESTIONS Q33)"
                );
                self.error(codes::MISPLACED_JUMP, span, message);
                return;
            }
            None if self.f.loops.is_empty() => {
                self.error(codes::MISPLACED_JUMP, span, format!("`{keyword}` outside a loop"));
                return;
            }
            None => self.f.loops.len() - 1,
            Some(label) => match self.f.loops.iter().rposition(|l| l.label == Some(label.sym)) {
                Some(index) => index,
                None => {
                    let text = self.m.text(label.sym);
                    let message = if self.closure_scopes.iter().any(|scope| scope.labels.contains(&label.sym)) {
                        format!(
                            "`{keyword} {text}` can't leave a closure; its body ends with its value or a `return` (OPEN_QUESTIONS Q33)"
                        )
                    } else {
                        format!("no enclosing loop is labelled `{text}`")
                    };
                    self.error(codes::MISPLACED_JUMP, label.span, message);
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
        let base = self.f.locals.len() as u32;
        self.f.scopes.push(Vec::new());
        let mut flow = Flow::Finishes;
        let mut value = None;
        let mut tail = None;
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
                tail = Some(e);
                continue;
            }
            let next = self.stmt(s);
            flow = self.then(flow, next);
        }
        self.f.scopes.pop();
        if let Some(e) = tail {
            self.local_capture(e, base);
        }
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

    /// `[a, b]`. Its elements meet, so their types are joined, and the expected type gives
    /// what it knows first, as a variant's does (OPEN_QUESTIONS P5; issue #10). An empty one
    /// has only what it meets to give it a type. A list stores its elements, so it copies
    /// them (REFERENCE §4.8).
    fn list(&mut self, e: ExprId, elements: &[ExprId], expected: Option<&Ty>) -> Ty {
        let span = self.span(e);
        let mut element = match expected {
            Some(Ty::Adt(AdtId::LIST, args)) => args[0].clone(),
            // An unused value, or one whose context has an error, needs no type (§15.1).
            Some(Ty::Error) => self.vars.rejected(),
            _ => self.vars.fresh(Kind::Any, Origin::Variant { adt: AdtId::LIST, span }),
        };
        for &x in elements {
            element = self.element(x, element);
        }
        Ty::list(element)
    }

    /// `["k": v]`, whose keys meet each other, and whose values do, as a list's elements do.
    /// Its keys implement `Eq` and `Hash` (REFERENCE §4.2).
    fn map(&mut self, e: ExprId, entries: &[(ExprId, ExprId)], expected: Option<&Ty>) -> Ty {
        let span = self.span(e);
        let origin = Origin::Variant { adt: AdtId::MAP, span };
        // An expected map type has had its key type checked where it was written or built, so
        // literals whose keys meet, which give each other their types, report it once.
        let (mut key, mut value, mut checked) = match expected {
            Some(Ty::Adt(AdtId::MAP, args)) => (args[0].clone(), args[1].clone(), true),
            Some(Ty::Error) => (self.vars.rejected(), self.vars.rejected(), true),
            _ => (self.vars.fresh(Kind::Any, origin), self.vars.fresh(Kind::Any, origin), false),
        };
        // A key type still open in the expected type was left by a literal without entries,
        // as in `[:] == [x: 1]`, so this literal, whose entries give the key type, takes over
        // its check (issue #39).
        if checked
            && !entries.is_empty()
            && let open @ Ty::Var(_) = self.vars.resolve(&key)
            && let Some(i) = self.pending.iter().position(|check| {
                matches!(check, Pending::Bound { ty, callee, .. } if **callee == *"Map" && self.vars.resolve(ty) == open)
            })
        {
            self.pending.remove(i);
            checked = false;
        }
        for &(k, v) in entries {
            key = self.element(k, key);
            value = self.element(v, value);
        }
        if !checked {
            let key = self.vars.resolve(&key);
            // A float literal settles as a float type, and none has `Eq` (REFERENCE §12.2).
            let float = matches!(key, Ty::Var(v) if self.vars.open(v).is_some_and(|open| open.kind == Kind::Float));
            if self.vars.has_var(&key) && !float {
                let (ifaces, callee, param) = (vec![IfaceId::EQ, IfaceId::HASH], "Map".into(), "K".into());
                self.pending.push(Pending::Bound { ty: key, ifaces, callee, param, span });
            } else if !self.key_bound(if float { &Ty::Float(FloatTy::F64) } else { &key }, span)
                && !matches!(key, Ty::Fn(..))
                && !holds_fn(&key)
            {
                // The literal is rejected, as a written map type with this key is, so what uses
                // it isn't reported again (§15.1). A function key is reported where the map
                // goes (E0509), which needs its type.
                self.vars.quiet(&value);
                return Ty::Error;
            }
        }
        Ty::map(key, value)
    }

    /// Checks `x`, an element, key or value of a literal, which it stores, where the others
    /// give `known`, and returns the type of all of them. A `Never` gives way, so it gives
    /// `known` only if nothing else does (OPEN_QUESTIONS P5).
    fn element(&mut self, x: ExprId, known: Ty) -> Ty {
        self.copying = true;
        self.siblings.insert(x);
        match self.joined(x, &known) {
            Ty::Never => self.vars.join(&known, &Ty::Never).unwrap_or(known),
            ty => ty,
        }
    }

    /// Reports a map's key type that doesn't implement `Eq` and `Hash` (REFERENCE §4.2), or
    /// is a resource, and returns whether it is fine.
    fn key_bound(&mut self, key: &Ty, span: Span) -> bool {
        let key = self.vars.zonk(key);
        if key.is_unknown() || self.vars.has_open(&key) || self.unknown_interfaces(&key) {
            return true;
        }
        // A function value can't be a key, which is reported where it goes in (E0509).
        if matches!(key, Ty::Fn(..)) || holds_fn(&key) {
            return false;
        }
        // `set` keeps the key it has and drops the equal one it is given, which can't drop a
        // resource (§10 rule 5).
        if self.p.decls.is_resource(&key) {
            let what = format!("resources, such as `{}`, as map keys", self.show(&key));
            self.not_implemented(span, &what, Planned::Unscheduled);
            return false;
        }
        let Some(iface) = [IfaceId::EQ, IfaceId::HASH].into_iter().find(|&iface| !self.implements(&key, iface)) else {
            return true;
        };
        let message =
            format!("`{}` does not implement `{}`, which `Map` needs of `K`", self.show(&key), self.iface_name(iface));
        self.error(codes::MISSING_IMPLEMENTATION, span, message);
        false
    }

    /// Reports `ty`, a type argument of a collection, if it doesn't implement `iface`, which
    /// `what` needs of `param` (STD.md), or waits for the statement to settle it.
    fn needs(&mut self, ty: Ty, iface: IfaceId, what: &str, param: &str, span: Span) {
        if self.vars.has_open(&ty) {
            let (ifaces, callee, param) = (vec![iface], what.into(), param.into());
            self.pending.push(Pending::Bound { ty, ifaces, callee, param, span });
            return;
        }
        // One that holds a function value was reported where it was made (E0509).
        if !ty.is_unknown() && !self.implements(&ty, iface) && !self.unknown_interfaces(&ty) && !holds_fn(&ty) {
            let message = format!(
                "`{}` does not implement `{}`, which `{what}` needs of `{param}`",
                self.show(&ty),
                self.iface_name(iface)
            );
            self.error(codes::MISSING_IMPLEMENTATION, span, message);
        }
    }

    /// Whether `e` is an element of a list or a pool, or a field of one at any depth.
    fn in_element(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Index { .. } => true,
            ExprKind::Field { base, .. } => self.in_element(base),
            _ => false,
        }
    }

    /// Reports a copy of a field of an element, which stays in its list or pool, so copying
    /// it needs `Copy` as copying the element does (STD.md, OPEN_QUESTIONS P5).
    fn element_part_copied(&mut self, e: ExprId, ty: &Ty) {
        let span = self.span(e);
        let ty = self.vars.resolve(ty);
        if self.vars.has_open(&ty) {
            return self.needs(ty, IfaceId::COPY, "xs[i]", "T", span);
        }
        if ty.is_unknown() || self.implements(&ty, IfaceId::COPY) || self.unknown_interfaces(&ty) {
            return;
        }
        let message = format!(
            "this copies a part of an element, which stays in its list or pool, and `{}` doesn't implement `Copy`; move the element out first, as with `remove` or `pop` (STD.md)",
            self.show(&ty)
        );
        self.error(codes::MISSING_IMPLEMENTATION, span, message);
    }

    /// Reports a receiver that a method takes, when it is an element of a list or pool or a
    /// part of one, which stays where it is, so taking it copies it (STD.md, §10 rule 1).
    fn element_taken(&mut self, receiver: ExprId, ty: &Ty) {
        match self.m.exprs[receiver].kind {
            ExprKind::Index { base, .. } => {
                let pool = matches!(self.vars.resolve(self.p.ty(base)), Ty::Adt(AdtId::POOL, _));
                let span = self.span(receiver);
                self.needs(ty.clone(), IfaceId::COPY, if pool { "pool[h]" } else { "xs[i]" }, "T", span);
            }
            ExprKind::Field { base, .. } if self.in_element(base) => self.element_part_copied(receiver, ty),
            _ => {}
        }
    }

    /// `xs[i]`, which reads element `i` of a list (STD.md). The element stays in the list, so
    /// it is borrowed, and only `copying` it needs `T: Copy`, as for a borrowed parameter
    /// (REFERENCE §4.8, OPEN_QUESTIONS P5). The element's type need not be known yet, so what
    /// the element meets may still give it (issue #10).
    fn index(&mut self, e: ExprId, base: ExprId, index: ExprId, chain: bool, copying: bool) -> Ty {
        self.in_chain = chain;
        let base_ty = self.infer(base);
        let base_ty = match self.vars.resolve(&base_ty) {
            ty @ Ty::Adt(AdtId::LIST | AdtId::POOL, _) => ty,
            _ => self.force_receiver(&base_ty),
        };
        let span = self.span(e);
        let Some(element) = self.indexed(&base_ty, index, span) else { return Ty::Error };
        if copying {
            let what = if matches!(base_ty, Ty::Adt(AdtId::POOL, _)) { "pool[h]" } else { "xs[i]" };
            self.needs(element.clone(), IfaceId::COPY, what, "T", span);
        }
        element
    }

    /// The type of element `index` of a value of type `base_ty`: a list, whose index is an
    /// `Int`, or a pool, whose index is a handle into it (STD.md). Nothing else has an index
    /// (E0306). `None` once reported.
    fn indexed(&mut self, base_ty: &Ty, index: ExprId, span: Span) -> Option<Ty> {
        if let Ty::Adt(AdtId::LIST, args) = base_ty {
            self.check(index, &Ty::INT);
            return Some(args[0].clone());
        }
        if let Ty::Adt(AdtId::POOL, args) = base_ty {
            self.check(index, &Ty::applied(AdtId::HANDLE, vec![args[0].clone()]));
            return Some(args[0].clone());
        }
        self.rejected_value(index);
        if !base_ty.is_unknown() {
            let ty = self.show(base_ty);
            let message = match base_ty {
                Ty::Adt(AdtId::MAP, _) => format!("`{ty}` has no index; read a map with `get`, as in `m.get(k)`"),
                Ty::Text => "`Text` has no index; text is never indexed by integers (§12.3)".to_string(),
                _ => format!("`{ty}` has no index; only a list and a pool have one, as in `xs[i]` and `pool[h]`"),
            };
            self.error(codes::UNSUPPORTED_OPERATOR, span, message);
        }
        None
    }

    /// Why local `id`, called `name`, can't be changed by what `does` (E0305).
    fn immutable(&self, name: Ident, id: LocalId, does: &str) -> String {
        let text = self.m.text(name.sym);
        let local = &self.f.locals[id.index()];
        if self.f.refinement && id.index() < self.f.params {
            format!(
                "`{text}` is a field this refinement only looks at, so the refinement can't {does} (OPEN_QUESTIONS P5)"
            )
        } else if local.in_loop {
            format!("`{text}` is a loop variable, which can't be changed; copy it into a `var` to {does}")
        } else if id.index() >= self.f.params {
            format!("`{text}` is bound by `let` or a pattern; declare it with `var` to {does}")
        } else if !local.borrowed {
            format!("`{text}` is a `take` parameter, which can't be changed; copy it into a `var` to {does}")
        } else if text == "self" {
            format!("`self` is borrowed by this method; declare it `inout self` to {does}")
        } else {
            format!("`{text}` is a borrowed parameter; declare it `inout` to {does}")
        }
    }

    /// Reports the receiver of a method that changes it, such as `push`, unless it is a `var`
    /// or a field or element of one, as an assignment's target is (STD.md, REFERENCE §5.2).
    fn changes(&mut self, receiver: ExprId, method: &str) {
        let m = self.m;
        let mut e = receiver;
        let mut state = false;
        loop {
            match m.exprs[e].kind {
                ExprKind::Field { base, .. } if matches!(self.p.res(e), Some(Res::Field(_))) => {
                    state |= self.is_state(self.p.ty(base), e);
                    e = base;
                }
                ExprKind::Index { base, .. } if matches!(self.p.ty(base), Ty::Adt(AdtId::POOL, _)) => {
                    self.pool_element(self.span(e));
                    return;
                }
                ExprKind::Index { base, .. } => e = base,
                ExprKind::Name(name) if let Some(Res::Local(id)) = self.p.res(e) => {
                    if state {
                        self.changes_state(id, self.span(receiver));
                    } else if !self.f.locals[id.index()].mutable {
                        let message = self.immutable(name, id, &format!("call `{method}`, which changes it"));
                        self.error(codes::IMMUTABLE_ASSIGNMENT, self.span(receiver), message);
                    } else {
                        self.changes_capture(id, self.span(receiver));
                    }
                    return;
                }
                _ => break,
            }
        }
        let message = format!("`{method}` changes its receiver, so the receiver must be a variable or a part of one");
        self.error(codes::INVALID_ASSIGNMENT_TARGET, self.span(receiver), message);
    }

    /// Infers the type of `e`, a part of an expression that was rejected, which was the one
    /// to give the type arguments `e` leaves open, so they are not reported again (§15.1).
    fn rejected_value(&mut self, e: ExprId) -> Ty {
        // A closure has no function type to take its parameters' types from.
        let ty = match self.m.exprs[e].kind {
            ExprKind::Closure(_) => self.expr(e, Some(&Ty::Error)),
            _ => self.infer(e),
        };
        self.vars.quiet(&ty);
        ty
    }

    /// [`Checker::rejected_value`] for each argument of a rejected call.
    fn rejected_args(&mut self, args: &[Arg]) {
        for arg in args {
            self.rejected_value(arg.value);
        }
    }

    /// Reports that `e`'s type doesn't fit where it is, as `code`. A mismatched place moves nothing. Any
    /// other value, such as a call, still takes what it is given, and the mismatch is about
    /// the value it gives.
    fn mismatch(&mut self, e: ExprId, code: Code, span: Span, message: String) {
        if matches!(
            self.m.exprs[e].kind,
            ExprKind::Name(_) | ExprKind::It | ExprKind::Field { .. } | ExprKind::Index { .. }
        ) {
            self.error_of(e, code, span, message);
        } else {
            self.error(code, span, message);
            self.inner_errors += 1;
        }
    }

    /// The code of a value of type `actual` where `expected` is required: E0603 or E0602 when
    /// the two differ only in the permissions or the `uses` of capabilities and function types
    /// (see [`reach_mismatch`]), and E0301 otherwise.
    fn mismatch_code(&self, expected: &Ty, actual: &Ty) -> Code {
        reach_mismatch(&self.vars.defaulted(expected), &self.vars.defaulted(actual), false)
            .unwrap_or(codes::TYPE_MISMATCH)
    }

    /// Checks `e` against `expected`, reports a mismatch, and returns the actual type.
    fn check(&mut self, e: ExprId, expected: &Ty) -> Ty {
        let actual = self.expr(e, Some(expected));
        if !self.vars.subsume(expected, &actual) {
            let span = self.span(e);
            let mut message = format!("expected `{}`, found `{}`", self.show(expected), self.show(&actual));
            let mut code = self.mismatch_code(expected, &actual);
            // A capability the observes-only view narrowed fits where it would have outside it.
            if let Some(orig) = self.f.unnarrowed.get(&e)
                && [codes::PERMISSION_NOT_GRANTED, codes::REACH_NOT_ADMITTED].contains(&code)
                && reach_mismatch(&self.vars.defaulted(expected), &self.vars.defaulted(orig), false).is_none()
            {
                code = codes::EFFECTS_CALL_IN_OBSERVES;
                message = self.view_message(&format!(
                    "this capability is `{}`, and `{}` is expected",
                    self.show(&actual),
                    self.show(expected)
                ));
            }
            self.mismatch(e, code, span, message);
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
        let (before, outer) = (self.errors, std::mem::replace(&mut self.inner_errors, 0));
        let ty = self.expr_kind(e, expected.as_ref(), chain, copying);
        let ty = self.vars.resolve(&ty);
        let ty = self.shallow(e, ty, before);
        let ty = if self.f.view.is_some() { self.view_expr(e, ty) } else { ty };
        if copying {
            self.copied(e, &ty);
            self.consumed.insert(e);
        }
        // A call that resolves to nothing, as on a receiver of an unknown type, is rejected
        // too, though its error was reported before it (REFERENCE §15.1).
        let unresolved = ty == Ty::Error
            && match self.m.exprs[e].kind {
                ExprKind::Call { callee, .. } => self.p.res.get(callee).is_none(),
                ExprKind::MethodCall { .. } => self.p.res.get(e).is_none(),
                _ => false,
            };
        if self.errors - before > self.inner_errors || unresolved {
            self.rejected.insert(e);
        }
        self.inner_errors = outer + (self.errors - before);
        self.record(e, ty.clone());
        if matches!(
            self.m.exprs[e].kind,
            ExprKind::List(_)
                | ExprKind::Map(_)
                | ExprKind::Tuple(_)
                | ExprKind::Call { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::Closure(_)
        ) {
            self.builders.push(e);
        }
        ty
    }

    /// `ty`, the type of `e`, or an error once it is reported for nesting more than
    /// [`MAX_TYPE_DEPTH`] levels deep. Each walk of a type and each message about it then
    /// stays bounded however a generic function nests its type parameter (OPEN_QUESTIONS
    /// P5; issues #17, #18). Once a part of `e` has an error, from `before` on, the type may
    /// be deep because of it, so it isn't reported (§15.1).
    fn shallow(&mut self, e: ExprId, ty: Ty, before: usize) -> Ty {
        if ty.parts().is_none() {
            return ty;
        }
        // One with an error in it was rejected where the error was, and the walk stops at
        // the limit, so a type too deep for one is reported however much deeper it is.
        let error = match self.vars.depth(&ty, MAX_TYPE_DEPTH) {
            Some(_) => return ty,
            None => before < self.errors,
        };
        if !error {
            let message = format!(
                "the type of this nests more than {MAX_TYPE_DEPTH} levels deep, as `{}`, which is more than a type may",
                self.show(&ty)
            );
            self.error(codes::TYPE_TOO_DEEP, self.span(e), message);
        }
        Ty::Error
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
        // `xs[i]` reports its own copy, as STD.md has it need `T: Copy`.
        if self.f.bounds.is_empty() || !self.borrowed_place(e) || matches!(self.m.exprs[e].kind, ExprKind::Index { .. })
        {
            return;
        }
        let ty = &self.vars.zonk(ty);
        // A type that moves whatever its parameters are, such as `Pool[T]`, is a move of a
        // lent value, which the move pass reports (E0504).
        if !self.p.decls.copy_needs_param(ty, &self.f.bounds) {
            return;
        }
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

    /// A type parameter in `ty` that isn't `Copy`, outside a handle, which neither holds nor
    /// reaches its element (STD.md).
    fn uncopyable(&self, ty: &Ty) -> Option<u32> {
        match ty {
            Ty::Param(i) if !self.f.bounds.get(*i as usize).is_some_and(|b| b.contains(&IfaceId::COPY)) => Some(*i),
            Ty::Adt(AdtId::HANDLE, _) => None,
            Ty::Adt(_, args) => args.iter().find_map(|arg| self.uncopyable(arg)),
            _ => None,
        }
    }

    /// Whether `e` is a parameter, a part of one bound by a pattern, an element of a list, or
    /// a field of one of those.
    fn borrowed_place(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) => matches!(self.p.res(e), Some(Res::Local(id)) if self.f.locals[id.index()].borrowed),
            ExprKind::Field { base, .. } => matches!(self.p.res(e), Some(Res::Field(_))) && self.borrowed_place(base),
            // An element stays in its list, so reading it borrows it (OPEN_QUESTIONS P5).
            ExprKind::Index { .. } => true,
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
                        // One that holds a function value was reported where it was made (E0509).
                        if !self.implements(&ty, IfaceId::SHOW) && !ty.is_unknown() && !holds_fn(&ty) {
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
                let enum_id = self.enum_named(*base);
                if let Some(id) = enum_id
                    && self.p.decls.adt(id).variant_named(self.m.text(name.sym)).is_some()
                {
                    return self.unit_variant(e, id, *name, expected);
                }
                if let Some((id, method)) = self.associated_named(*base, name.sym) {
                    let (ty, text) = (&self.p.decls.adt(id).name, self.m.text(name.sym));
                    let message = if method {
                        format!(
                            "`{text}` is a method of `{ty}`, which is called on a value with its arguments; it isn't a function value, but a closure can wrap a call of it, as in `|x: {ty}| x.{text}()`"
                        )
                    } else {
                        format!(
                            "`{ty}.{text}` is an associated function, which is called with its arguments; it isn't a function value, but a closure can wrap a call of it, as in `|| {ty}.{text}()`"
                        )
                    };
                    self.error(codes::METHOD_VALUE, name.span, message);
                    return Ty::Error;
                }
                if let Some(id) = enum_id {
                    return self.unit_variant(e, id, *name, expected);
                }
                self.in_chain = chain;
                let base_ty = self.infer(*base);
                let base_ty = self.force_receiver(&base_ty);
                let ty = self.field(e, &base_ty, *name);
                if copying && self.in_element(*base) {
                    self.element_part_copied(e, &ty);
                }
                ty
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
                self.not_implemented(span, "ranges outside `for` loops", Planned::Phase(4));
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
                        let message = if !self.closure_scopes.is_empty() {
                            "`fail` in a closure whose function type has no `fails`; the type it is passed as must have one, as in `fn(Int) -> Int fails E`"
                        } else if self.f.returns {
                            "`fail` needs a `fails` clause, and this function declares none"
                        } else {
                            &format!("`fail` in {}, which has no function to fail", self.f.place.describe())
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
            ExprKind::For { label, pat, iter, consume, body } => self.for_loop(e, *label, *pat, *iter, *consume, body),
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
                    if let Ty::Fn(..) = self.infer(*value) {
                        self.f.debugged.push(*value);
                    }
                }
                Ty::Unit
            }
            ExprKind::Tuple(elements) => self.tuple(elements, expected),
            ExprKind::List(elements) => self.list(e, elements, expected),
            ExprKind::Map(entries) => self.map(e, entries, expected),
            ExprKind::Index { base, index } => self.index(e, *base, *index, chain, copying),
            ExprKind::Else { value, fallback } => self.else_expr(e, *value, fallback, expected, copying),
            ExprKind::It => match self.its.last() {
                Some(&id) => {
                    self.p.res.insert(e, Res::Local(id));
                    self.capture(id, "it", span);
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
            ExprKind::Applied { callee, targs } => self.applied(e, *callee, targs),
            ExprKind::Closure(closure) => self.closure(e, closure, expected),
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
                // An unused value, or one whose context has an error, needs no type (§15.1).
                None if expected == Some(&Ty::Error) => self.expr(element, Some(&Ty::Error)),
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
        self.markers.push(Marker { handler: Some(e), errors: Vec::new(), target: None });
        self.in_chain = true;
        self.copying = copying;
        let value_ty = self.expr(value, None);
        let errors = self.pop_marker();
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
        let base = self.f.locals.len() as u32;
        match &it {
            Some(err) => {
                let id = LocalId(self.f.locals.len() as u32);
                self.f.locals.push(Local { ty: err.clone(), mutable: false, borrowed: false, in_loop: false });
                self.p.it_local.insert(e, id);
                self.its.push(id);
            }
            None => self.option_fallbacks += 1,
        }
        // The form's own expected type gives the fallback its type when the value doesn't.
        let inherited = self.siblings.remove(&e);
        let (expected, sibling) = match &unwrapped {
            Ty::Never => (expected.cloned().filter(|ty| !ty.is_unknown()), inherited),
            ty => (Some(ty.clone()), true),
        };
        let expected = expected.as_ref();
        if sibling {
            self.mark_sibling(match fallback {
                Fallback::Value(x) => Some(*x),
                Fallback::Block(block) => self.tail(block),
            });
        }
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
        // A closure the fallback gives can't capture `it` (Q34).
        if let Some(tail) = tail {
            self.local_capture(tail, base);
        }
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
            // A fallback whose type doesn't match the value's gives the form no type (issue #55).
            _ if self.mismatched_tail(tail) => {
                self.mismatched.insert(e);
                Ty::Error
            }
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
            Ty::Adt(id, _) if self.p.decls.adt(*id).derives.contains(&IfaceId::NEG) => true,
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
            ty => self.has_arithmetic(op, ty),
        };
        // A rejected `impl` block may have been the type's `impl Add` (§15.1).
        if !defined && !self.unknown_interfaces(ty) {
            let message = format!("`{}` is not defined for `{}`", op.symbol(), self.show(ty));
            self.error(codes::UNSUPPORTED_OPERATOR, span, message);
        }
        defined
    }

    /// Whether operands of type `ty` have arithmetic operator `op`: built in, or derived by a
    /// distinct type (REFERENCE §4.6).
    fn has_arithmetic(&self, op: BinOp, ty: &Ty) -> bool {
        match ty {
            Ty::Adt(id, _) => {
                let iface = match op {
                    BinOp::Add => IfaceId::ADD,
                    BinOp::Sub => IfaceId::SUB,
                    BinOp::Mul => IfaceId::MUL,
                    BinOp::Div => IfaceId::DIV,
                    _ => return false,
                };
                self.p.decls.adt(*id).derives.contains(&iface)
            }
            ty => arithmetic_defined(op, ty),
        }
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
                // One that holds a function value was reported where it was made (E0509).
                if !defined && !ty.is_unknown() && !holds_fn(&ty) {
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
            self.capture(id, self.m.text(name.sym), name.span);
            return self.f.locals[id.index()].ty.clone();
        }
        // A module item that reuses a variant's name has been reported, and so are its uses.
        if let Some(id) = bare_variant(text) {
            if self.poisoned.contains(&name.sym) {
                return Ty::Error;
            }
            return self.unit_variant(e, id, name, expected);
        }
        if let Some(&f) = self.fn_names.get(&name.sym).filter(|_| !self.poisoned.contains(&name.sym)) {
            return self.fn_value(e, f, None, name.span);
        } else if self.unqualified_variant(name) || self.poisoned.contains(&name.sym) {
        } else if self.aliases.contains_key(&name.sym) {
            self.alias_value(name);
        } else if self.imports.contains_key(&name.sym)
            || self.adt_named(name.sym).is_some()
            || self.iface_names.contains_key(&name.sym)
            || prelude_type(text)
        {
            self.error(codes::UNKNOWN_NAME, name.span, format!("`{text}` is a type or module, not a value"));
        } else if text == "self" {
            self.error(codes::UNKNOWN_NAME, name.span, "`self` exists only in a method, which takes it first");
        } else if self.f.distinct && text == "value" {
            let message = "a distinct type's `where` names its value `self`, as in `where self > 0` (§4.6)";
            self.error(codes::UNKNOWN_NAME, name.span, message);
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
            return self.fn_call(e, id, None, targs, args, span, chain, expected);
        }
        // A variant or record takes no type arguments. A name that resolves to nothing or to
        // a rejected declaration may have, and a call of a local is a later phase's (§15.1).
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && !self.poisoned.contains(&name.sym)
            && self.lookup_local(name.sym).is_none()
            && let Some(id) = bare_variant(m.text(name.sym)).or_else(|| self.adt_named(name.sym))
        {
            self.ctor_targs(targs, id, m.text(name.sym), span);
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
            // Only the toolchain builds a pool or a handle (STD.md).
            if self.p.decls.adt(id).is_native() {
                let text = m.text(name.sym);
                let message = match id {
                    AdtId::POOL => format!("`{text}` has no constructor; `{text}.new()` builds an empty pool"),
                    _ => format!("`{text}` has no constructor; a pool's `insert` makes handles"),
                };
                self.error(codes::UNKNOWN_NAME, name.span, message);
                self.rejected_args(args);
                return Ty::Error;
            }
            return self.construct(callee, id, args, span, expected);
        }
        let callee_span = self.span(callee);
        match m.exprs[callee].kind {
            ExprKind::Name(name) if self.lookup_local(name.sym).is_some() => {
                return self.value_call(e, callee, targs, args, span, chain);
            }
            ExprKind::Name(name) if self.unqualified_variant(name) => {}
            ExprKind::Name(name) if self.poisoned.contains(&name.sym) => {}
            ExprKind::Name(name) if self.aliases.contains_key(&name.sym) => self.alias_value(name),
            ExprKind::Name(name) if m.text(name.sym) == "System" && !self.poisoned.contains(&name.sym) => {
                self.system_constructed(callee_span, "built");
            }
            ExprKind::Name(name) if let Some(target) = builtin_type(m.text(name.sym)) => {
                return self.conversion(callee, name, target, targs, args, span);
            }
            ExprKind::Name(name) => {
                let text = m.text(name.sym);
                self.error(codes::UNKNOWN_NAME, name.span, format!("unknown function `{text}`"));
            }
            _ => return self.value_call(e, callee, targs, args, span, chain),
        }
        self.rejected_args(args);
        Ty::Error
    }

    /// Module function `f` used as a value, generic with type arguments from `targs` or else
    /// from the type it meets (REFERENCE §4.8). A method or associated function isn't one.
    fn fn_value(&mut self, e: ExprId, f: FnId, targs: Option<&[TypeId]>, span: Span) -> Ty {
        let info = &self.p.fns[f];
        if info.rejected {
            return Ty::Error;
        }
        let later = info.params.iter().find_map(|p| match p.mode {
            ParamMode::Keep => Some(("functions with `keep` parameters used as values", Planned::Phase(3))),
            ParamMode::InoutPartial => {
                Some(("functions with `inout(partial)` parameters used as values", Planned::Unscheduled))
            }
            _ => None,
        });
        if let Some((what, planned)) = later {
            self.not_implemented(span, what, planned);
            return Ty::Error;
        }
        self.p.res.insert(e, Res::Fn(f));
        let Some(tvars) = self.call_targs(f, targs, None, span) else { return Ty::Error };
        self.targ_bounds(f, &tvars, span);
        let info = &self.p.fns[f];
        let modes = info.params.iter().map(|p| p.mode).collect();
        let params = info.params.iter().map(|p| p.ty.subst(&tvars)).collect();
        let fails = info.fails.as_ref().map_or(Ty::Never, |err| err.subst(&tvars));
        Ty::func(modes, params, info.ret.subst(&tvars), fails)
    }

    /// `|x| expr`, `|a: Int| -> Int { … }` or `|| expr` (REFERENCE §6.7). Its parameters take
    /// their types from their annotations or from the function type it is `expected` to be,
    /// and their modes from that type. Its result and error types come from that type or its
    /// body, where `return` returns from the closure and `break` and `continue` can't leave it
    /// (OPEN_QUESTIONS Q33). It captures the locals declared before it that its body uses,
    /// by reference, so it can't change them or capture a capability yet (phase 3).
    fn closure(&mut self, e: ExprId, closure: &Closure, expected: Option<&Ty>) -> Ty {
        let m = self.m;
        let sibling = std::mem::take(&mut self.sibling_closure);
        let span = self.span(e);
        // A written function type, rather than one a variable or another branch gave, is where
        // the closure goes, so it may admit a capture whose type is settled later (§9.4).
        let written = expected.filter(|ty| !sibling && matches!(ty.fn_uses(), Some(Ty::Reach(_)))).cloned();
        let expected = expected.map(|ty| self.vars.resolve(ty));
        let mut rejected = false;
        // Where the call it is passed to was rejected, or a value of another type is expected,
        // its parameters' types are unknown and not reported (§15.1).
        let quiet = match &expected {
            Some(Ty::Error) => true,
            Some(ty) if ty.fn_parts().is_none() && !matches!(ty, Ty::Var(_)) => {
                let message = format!("expected `{}`, found a closure", self.show(ty));
                self.error(codes::TYPE_MISMATCH, span, message);
                rejected = true;
                true
            }
            _ => false,
        };
        let mut expected = expected
            .as_ref()
            .and_then(Ty::fn_parts)
            .map(|(modes, ret, fails, params)| (modes.to_vec(), ret.clone(), fails.clone(), params.to_vec()));
        if let Some((_, _, _, params)) = &expected
            && params.len() != closure.params.len()
        {
            let (n, given) = (params.len(), closure.params.len());
            let noun = if given == 1 { "parameter" } else { "parameters" };
            let message = format!("this closure takes {given} {noun}, but the function type it is passed as takes {n}");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.inner_errors += 1;
            expected = None;
            rejected = true;
        }
        let mut modes = Vec::new();
        let mut params = Vec::new();
        for (i, param) in closure.params.iter().enumerate() {
            let given = expected.as_ref().map(|(modes, _, _, params)| (modes[i], params[i].clone()));
            modes.push(given.as_ref().map_or(ParamMode::Borrow, |(mode, _)| *mode));
            let ty = match (param.ty, given) {
                (Some(t), given) => {
                    let ty = self.resolve_type(t);
                    // The closure takes what the function type passes it (§9.4).
                    if let Some((_, given)) = given
                        && !sibling
                        && !self.vars.subsume(&ty, &given)
                    {
                        let message = format!(
                            "this parameter is `{}`, but the function type the closure is passed as gives it `{}`",
                            self.show(&ty),
                            self.show(&given)
                        );
                        let code = self.mismatch_code(&ty, &given);
                        self.error(code, m.types[t].span, message);
                        self.inner_errors += 1;
                        rejected = true;
                    }
                    ty
                }
                (None, Some((_, given))) => given,
                (None, None) if rejected || quiet => self.vars.rejected(),
                (None, None) => {
                    self.vars.fresh(Kind::Any, Origin::Closure { name: param.name.sym, span: param.name.span })
                }
            };
            params.push(ty);
        }
        // Another branch's result only guides the body, whose own value gives the result, so
        // the join decides the type (OPEN_QUESTIONS P5).
        let (ret, guide) = match (closure.ret, &expected) {
            (Some(t), _) => (self.part_type(t, "a result"), None),
            (None, Some((_, ret, _, _))) if sibling => {
                (self.vars.fresh(Kind::Any, Origin::Defaulted), Some(ret.clone()))
            }
            (None, Some((_, ret, _, _))) => (ret.clone(), None),
            (None, None) => (self.vars.fresh(Kind::Any, Origin::Defaulted), None),
        };
        // An error type that only `Never` gives is `Never`, so a closure without one can't fail.
        // Another branch's error is only a guide too, which the join widens (issue #61).
        let fails = match &expected {
            Some((_, _, fails, _)) if !sibling => fails.clone(),
            _ => self.vars.open_nevers(&Ty::Never),
        };
        // The closure's own state: its result and error, and no loops to leave.
        let base = self.f.locals.len() as u32;
        let own_fails = (self.vars.resolve(&fails) != Ty::Never).then(|| fails.clone());
        let outer = (
            std::mem::replace(&mut self.f.ret, ret.clone()),
            std::mem::replace(&mut self.f.fails, own_fails),
            std::mem::take(&mut self.f.loops),
            std::mem::replace(&mut self.f.returns, true),
            std::mem::take(&mut self.markers),
        );
        let labels = outer.2.iter().filter_map(|l| l.label).collect();
        self.closure_scopes.push(ClosureScope {
            base,
            captures: Vec::new(),
            spans: Vec::new(),
            unmarked: false,
            labels,
        });
        self.f.scopes.push(Vec::new());
        let mut locals = Vec::new();
        for ((param, ty), mode) in closure.params.iter().zip(&params).zip(&modes) {
            // Without a function type, what the body may change is unknown (§15.1).
            let mutable = quiet || matches!(mode, ParamMode::Inout | ParamMode::InoutPartial);
            locals.push(self.declare(param.name, ty.clone(), mutable, "parameter", *mode != ParamMode::Take));
        }
        // A body without a value gives `()`, whatever another branch's result is (issue #61).
        let expected_body = match &guide {
            Some(_) if self.tail(&closure.body).is_none() => None,
            Some(guide) => Some(guide),
            None => Some(&ret),
        };
        let body = self.block_value(&closure.body, expected_body, true);
        // A body that always leaves gives `Never`, however it leaves (OPEN_QUESTIONS Q33).
        if diverges_ty(&body) {
            let _ = self.vars.subsume(&ret, &Ty::Never);
        } else if body != Ty::Error && !self.vars.subsume(&ret, &body) {
            // The tail joins the result as a branch would, so a value that only fits the
            // join, such as an `Int` where `Never` is required, is reported here.
            if let Some(tail) = self.tail(&closure.body) {
                let message = format!("expected `{}`, found `{}`", self.show(&ret), self.show(&body));
                let code = self.mismatch_code(&ret, &body);
                self.mismatch(tail, code, self.span(tail), message);
                self.vars.poison(&body);
                self.vars.quiet(&ret);
            }
        }
        // A body that never fails gives the error type `Never`, as a call of a function
        // without `fails` does, so a type argument nothing else gives settles as `Never`.
        let _ = self.vars.subsume(&fails, &Ty::Never);
        self.f.scopes.pop();
        let scope = self.closure_scopes.pop().expect("pushed above");
        // Its error type would have come from the call, so it is unknown (§15.1).
        if scope.unmarked && expected.is_none() {
            rejected = true;
        }
        (self.f.ret, self.f.fails, self.f.loops, self.f.returns, self.markers) = outer;
        let needs = scope.captures.iter().map(|(id, _)| self.local_needs(*id)).max().unwrap_or(0);
        // Its reach is what its captures reach (REFERENCE §9.4). One whose type is still open
        // is checked against it once the type settles.
        let mut uses = Reach::default();
        for (&(id, _), &span) in scope.captures.iter().zip(&scope.spans) {
            let ty = self.vars.zonk(&self.f.locals[id.index()].ty);
            if self.vars.has_open(&ty) {
                self.f.late_captures.push((e, id, span, written.clone()));
            } else {
                uses.extend(&self.reach(&ty));
            }
        }
        self.f.needs.insert(e, needs);
        self.f.closures.push(e);
        self.p.closures.insert(
            e,
            ClosureInfo { params: locals, modes: modes.clone(), captures: scope.captures, owned: Vec::new() },
        );
        if rejected {
            self.rejected.insert(e);
            return Ty::Error;
        }
        Ty::func_uses(modes, params, ret, fails, Ty::reach(uses))
    }

    /// How many locals a value held in local `id` needs alive (see [`FnState::needs`]): `id`
    /// itself, and those its function value captures.
    fn local_needs(&self, id: LocalId) -> u32 {
        (id.0 + 1).max(self.f.local_needs.get(&id).copied().unwrap_or(0))
    }

    /// Reports `e`, the value a block, branch or fallback gives, when it is a function value
    /// that captures a local declared there, from `base` on, which ends with it (E0509).
    fn local_capture(&mut self, e: ExprId, base: u32) {
        let span = self.span(e);
        if self.value_needs(e) <= base || self.escaped.iter().any(|inner| span.contains(*inner)) {
            return;
        }
        let message = "this gives a function value that captures a local declared here, such as a binding of the block or of a pattern, which ends here";
        self.error(codes::FUNCTION_VALUE_ESCAPES, span, message);
        self.escaped.push(span);
    }

    /// How many locals the value of `e` needs alive, if it is a function value (see
    /// [`FnState::needs`]).
    fn value_needs(&self, e: ExprId) -> u32 {
        let m = self.m;
        let tail = |block: &Block| self.tail(block).map_or(0, |e| self.value_needs(e));
        match &m.exprs[e].kind {
            ExprKind::Closure(_) => self.f.needs.get(&e).copied().unwrap_or(0),
            ExprKind::Name(_) => match self.p.res(e) {
                Some(Res::Local(id)) => self.f.local_needs.get(&id).copied().unwrap_or(0),
                _ => 0,
            },
            ExprKind::If { then_block, else_branch, .. } => {
                let other = match else_branch {
                    Some(ElseBranch::Block(block)) => tail(block),
                    Some(ElseBranch::If(nested)) => self.value_needs(*nested),
                    None => 0,
                };
                tail(then_block).max(other)
            }
            ExprKind::Match { arms, .. } => arms.iter().map(|arm| tail(&arm.body)).max().unwrap_or(0),
            ExprKind::Else { value, fallback } => {
                let fallback = match fallback {
                    Fallback::Value(value) => self.value_needs(*value),
                    Fallback::Block(block) => tail(block),
                };
                self.value_needs(*value).max(fallback)
            }
            _ => 0,
        }
    }

    /// Notes that the closures being checked capture local `id`, used at `span`, when it is
    /// declared before them. What it reaches, a closure reaches too (REFERENCE §9.4).
    fn capture(&mut self, id: LocalId, name: &str, span: Span) {
        for scope in &mut self.closure_scopes {
            if id.0 < scope.base && !scope.captures.iter().any(|(captured, _)| *captured == id) {
                scope.captures.push((id, name.into()));
                scope.spans.push(span);
            }
        }
    }

    /// What a value of type `ty` may reach in the function being checked, where a type
    /// parameter without `Copy` may reach what its type argument does (REFERENCE §5.1, Q31).
    fn reach(&self, ty: &Ty) -> Reach {
        self.p.decls.reach(ty, &self.f.bounds)
    }

    /// Whether local `id` is one the innermost closure being checked captures, which it may
    /// not change before phase 3 (REFERENCE §5.3).
    fn changes_capture(&mut self, id: LocalId, span: Span) -> bool {
        if !self.closure_scopes.last().is_some_and(|scope| id.0 < scope.base) {
            return false;
        }
        self.not_implemented(span, "closures that change a variable they capture", Planned::Phase(3));
        true
    }

    /// `f::[T]` without a call, which names a generic function as a value. A method is
    /// called, never a value (E0320), and nothing else takes type arguments.
    fn applied(&mut self, e: ExprId, callee: ExprId, targs: &[TypeId]) -> Ty {
        let m = self.m;
        let span = self.span(e);
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && self.lookup_local(name.sym).is_none()
            && !self.poisoned.contains(&name.sym)
            && let Some(&f) = self.fn_names.get(&name.sym)
        {
            let ty = self.fn_value(callee, f, Some(targs), span);
            self.record(callee, ty.clone());
            return ty;
        }
        // What the type arguments were meant for is checked as written, and its type is
        // unknown after them (§15.1).
        let ty = self.rejected_value(callee);
        if !ty.is_unknown() {
            let what = match &m.exprs[callee].kind {
                ExprKind::Name(name) | ExprKind::Field { name, .. }
                    if matches!(self.p.res(callee), Some(Res::Ctor(..))) =>
                {
                    format!("`{}` is a variant, which", m.text(name.sym))
                }
                ExprKind::Name(name) if matches!(ty, Ty::Fn(..)) => {
                    format!("`{}` is a function value, which", m.text(name.sym))
                }
                ExprKind::Name(name) => format!("`{}`", m.text(name.sym)),
                ExprKind::Field { name, .. } => format!("`{}` is a field, which", m.text(name.sym)),
                _ => "this value".to_string(),
            };
            let span = match (targs.first(), targs.last()) {
                (Some(&first), Some(&last)) => m.types[first].span.to(m.types[last].span),
                _ => span,
            };
            self.error(codes::TYPE_ARGUMENT_COUNT, span, format!("{what} takes no type arguments"));
        }
        Ty::Error
    }

    /// The record or enum that `base` names, when `name` is one of its associated functions
    /// or methods, so `base.name` without a call names it as a value (E0320), and whether it
    /// is a method.
    fn associated_named(&self, base: ExprId, name: Symbol) -> Option<(AdtId, bool)> {
        let ExprKind::Name(type_name) = self.m.exprs[base].kind else { return None };
        if self.lookup_local(type_name.sym).is_some() {
            return None;
        }
        let id = self.adt_named(type_name.sym)?;
        if let Some(entry) = self.inherent.get(&id).and_then(|entries| entries.iter().find(|entry| entry.name == name))
        {
            return Some((id, self.p.fns[entry.f].receiver.is_some()));
        }
        // An interface's method, which takes `self`, of a type that derives the interface or
        // has an `impl` of it, for any of its instances (issue #50).
        let text = self.m.text(name);
        let def = self.p.decls.adt(id);
        let own = Ty::Adt(id, (0..def.params as u32).map(Ty::Param).collect());
        let named = self.p.decls.ifaces().any(|(iface, idef)| {
            idef.method(text).is_some() && (def.derives.contains(&iface) || self.p.decls.has_impl_head(iface, &own))
        });
        named.then_some((id, true))
    }

    /// Whether a value of type `ty` has a method `name`, its own, built in or from an
    /// interface it implements. Nothing is reported.
    fn has_method(&self, ty: &Ty, name: Symbol) -> bool {
        let text = self.m.text(name);
        if let Ty::Adt(id, _) = ty
            && self.inherent.get(id).is_some_and(|entries| entries.iter().any(|entry| entry.name == name))
        {
            return true;
        }
        builtin_method(ty, text).is_some()
            || self.p.decls.ifaces().any(|(iface, def)| def.method(text).is_some() && self.implements(ty, iface))
    }

    /// A call of a function value, which takes no labels and no type arguments, and takes
    /// `&` for each `inout` parameter (REFERENCE §3, §9.4). A call through `fails E` is
    /// marked like any call that can fail (§7.2).
    fn value_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
    ) -> Ty {
        let m = self.m;
        let ty = self.infer(callee);
        // Only the callee's own type must be known now. Its parts may still be settled by
        // the arguments or later code.
        let ty = match self.vars.resolve(&ty) {
            ty @ Ty::Var(_) => self.force(&ty),
            ty => ty,
        };
        let name = match m.exprs[callee].kind {
            ExprKind::Name(name) => m.text(name.sym).to_string(),
            _ => "this function value".to_string(),
        };
        let Some((modes, ret, fails, params)) = ty.fn_parts() else {
            if !ty.is_unknown() {
                let message = format!("`{name}` is a `{}`, not a function, so it can't be called", self.show(&ty));
                self.error(codes::TYPE_MISMATCH, self.span(callee), message);
            }
            self.rejected_args(args);
            return Ty::Error;
        };
        self.no_targs(targs, &name, span);
        let (modes, ret, fails) = (modes.to_vec(), ret.clone(), fails.clone());
        let params: Vec<(&str, Ty)> = params.iter().map(|ty| ("", ty.clone())).collect();
        self.generic_args(&name, &params, &[], args, span, Modes::Each(&modes));
        self.fallible_call(e, &name, &fails, span, chain);
        ret
    }

    /// The module function that `callee` names. A variant of the prelude is never one, even
    /// when a wrongly cased function has its name.
    fn fn_named(&self, callee: ExprId) -> Option<FnId> {
        let ExprKind::Name(name) = self.m.exprs[callee].kind else { return None };
        if bare_variant(self.m.text(name.sym)).is_some() || self.poisoned.contains(&name.sym) {
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

    /// Reports type arguments given to a constructor of `id`. A generic one takes them from
    /// its fields and the expected type (OPEN_QUESTIONS P5).
    fn ctor_targs(&mut self, targs: Option<&[TypeId]>, id: AdtId, what: &str, span: Span) {
        if self.p.decls.adt(id).params == 0 {
            return self.no_targs(targs, what, span);
        }
        let Some(targs) = targs else { return };
        let m = self.m;
        let span = match (targs.first(), targs.last()) {
            (Some(&first), Some(&last)) => m.types[first].span.to(m.types[last].span),
            _ => span,
        };
        let message = format!(
            "`{what}` takes its type arguments from its fields and the type it is expected to have, not from `::[…]`; give the binding a type instead"
        );
        self.error(codes::TYPE_ARGUMENT_COUNT, span, message);
    }

    /// A call of function `f`, a module's or a method. Its type arguments come from
    /// `targs`, or else from the type the call is expected to have and then from the
    /// arguments, and each must implement its parameter's constraints (REFERENCE §4.8;
    /// OPEN_QUESTIONS P5).
    /// Reports a resource as the type argument for `param` of the generic function `callee`.
    /// Its body may drop a value of a type parameter without `Copy`, which a resource can't
    /// allow, and the reference doesn't say how a type parameter admits one (OPEN_QUESTIONS
    /// §G). Returns whether it reported one.
    fn resource_targ(&mut self, ty: &Ty, callee: &str, param: &str, span: Span) -> bool {
        if !self.p.decls.is_resource(ty) {
            return false;
        }
        let what = format!("resources, such as `{}`, as the type argument `{param}` of `{callee}`", self.show(ty));
        self.not_implemented(span, &what, Planned::Unscheduled);
        true
    }

    #[allow(clippy::too_many_arguments)]
    fn fn_call(
        &mut self,
        e: ExprId,
        f: FnId,
        receiver: Option<&Ty>,
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
        let modes: Vec<ParamMode> = info.params.iter().map(|p| p.mode).collect();
        let (ret, fails) = (info.ret.clone(), info.fails.clone());
        let Some(tvars) = self.call_targs(f, targs, receiver, span) else {
            self.rejected_args(args);
            return Ty::Error;
        };
        // The type the call is expected to have gives what it can first, so a mismatch is
        // reported at the argument (OPEN_QUESTIONS P5). A `Never` in it is known only in part,
        // and the arguments may widen it.
        if targs.is_none()
            && let Some(expected) = expected.filter(|t| !t.is_unknown())
        {
            self.vars.subsume(expected, &ret.subst(&tvars));
        }
        let counted = self.generic_args(name, &params, &tvars, args, span, Modes::Each(&modes));
        // An expected type with an error may have given them, and arguments that don't
        // match their parameters leave them to nothing (§15.1).
        if expected == Some(&Ty::Error) || !counted {
            for ty in &tvars {
                self.vars.poison(ty);
            }
        }
        self.targ_bounds(f, &tvars, span);
        if let Some(err) = fails {
            self.fallible_call(e, name, &err.subst(&tvars), span, chain);
        }
        ret.subst(&tvars)
    }

    /// The type arguments of a call or a use as a value of function `f`: from `targs`, or else
    /// fresh variables that the expected type and the arguments give. A parameter whose
    /// declaration or constraint is rejected stands for an unknown type. `None` when `targs`
    /// gives the wrong number, which is reported. A method's `impl` parameters come from
    /// matching the type of its `receiver` with the block's target (OPEN_QUESTIONS P5).
    fn call_targs(&mut self, f: FnId, targs: Option<&[TypeId]>, receiver: Option<&Ty>, span: Span) -> Option<Vec<Ty>> {
        let m = self.m;
        let info = &self.p.fns[f];
        let name = m.text(info.name);
        let (own, owner) = (info.impl_params, info.owner.clone());
        // A parameter whose declaration or constraint is rejected stands for an unknown type,
        // and any other is a variable until `::[…]`, the expected type or an argument gives it.
        let rejected: Vec<bool> = info.generics.iter().map(|g| g.rejected).collect();
        let mut tvars: Vec<Option<Ty>> = rejected.iter().map(|&rejected| rejected.then_some(Ty::Error)).collect();
        // `::[…]` gives the declared parameters, which come before those of interface types,
        // and after the `impl` block's.
        let declared = info.generics[own..].iter().filter(|g| g.param.is_none()).count();
        // A parameter declared twice may have been meant as one, so a count without it is
        // also right.
        let duplicates = info.generics[own..].iter().filter(|g| g.sym.is_none() && g.param.is_none()).count();
        if let Some(targs) = targs {
            let tys: Vec<Ty> = targs.iter().map(|&t| self.part_type(t, "a type argument")).collect();
            let fewest = declared - duplicates;
            if tys.len() != declared && (fewest..declared).contains(&tys.len()) {
                tvars.fill(Some(Ty::Error));
            } else if tys.len() != declared {
                let at = match (targs.first(), targs.last()) {
                    (Some(&first), Some(&last)) => m.types[first].span.to(m.types[last].span),
                    _ => span,
                };
                let message = match (declared, tys.len() < fewest) {
                    (0, _) if own > 0 => format!(
                        "`{name}` takes no type arguments of its own, and its `impl`'s come from its receiver, its arguments or the type it is expected to have"
                    ),
                    (0, _) => format!("`{name}` takes no type arguments"),
                    (n, short) => {
                        let verb = if tys.len() == 1 { "was" } else { "were" };
                        let n = if short { fewest } else { n };
                        format!("`{name}` takes {}, but {} {verb} given", type_args(n), tys.len())
                    }
                };
                self.error(codes::TYPE_ARGUMENT_COUNT, at, message);
                return None;
            } else {
                for (slot, ty) in tvars[own..].iter_mut().zip(tys) {
                    slot.get_or_insert(ty);
                }
            }
        }
        let mut tvars: Vec<Ty> = (tvars.into_iter().enumerate())
            .map(|(param, ty)| ty.unwrap_or_else(|| self.vars.fresh(Kind::Any, Origin::Call { f, param, span })))
            .collect();
        // The receiver is an argument of the block's target type, so its type gives the
        // block's parameters as an argument's does, with a `Never` part giving way to the
        // others. An open part of it that settles on another type doesn't match the target.
        if let (Some(receiver), Some(owner)) = (receiver, &owner)
            && !self.vars.subsume(&owner.subst(&tvars), receiver)
        {
            let names: Vec<Box<str>> = self.p.fns[f].generics.iter().map(|g| g.name.clone()).collect();
            let message = format!(
                "`{}` has no method `{name}`; the `impl` that declares it is for `{}`",
                self.show(receiver),
                self.p.decls.display_in(owner, &names)
            );
            self.error(codes::UNKNOWN_MEMBER, span, message);
            tvars[..own].fill(Ty::Error);
        }
        Some(tvars)
    }

    /// Checks each type argument of a call or use of function `f` against its parameter's
    /// constraints, once the statement settles it if it has a variable in it. A function
    /// value can't be one, since it could outlive what it captures (OPEN_QUESTIONS P5).
    fn targ_bounds(&mut self, f: FnId, tvars: &[Ty], span: Span) {
        let info = &self.p.fns[f];
        let name: Box<str> = self.m.text(info.name).into();
        let generics: Vec<(Box<str>, Vec<IfaceId>)> =
            info.generics.iter().map(|g| (g.name.clone(), g.bounds.clone())).collect();
        let name = &*name;
        for (ty, (param, bounds)) in tvars.iter().zip(&generics) {
            let ty = self.vars.resolve(ty);
            if ty.is_unknown() {
                continue;
            }
            // One with a variable in it is checked once the statement settles it, which
            // also walks a deep argument once rather than at each call around it.
            if self.vars.has_var(&ty) {
                let (ifaces, callee, param) = (bounds.clone(), name.into(), param.clone());
                self.pending.push(Pending::Bound { ty: ty.clone(), ifaces, callee, param, span });
                continue;
            }
            if self.fn_targ(&ty, span) || self.resource_targ(&ty, name, param, span) {
                continue;
            }
            if let Some(iface) = self.unmet_bound(&ty, bounds) {
                let message = format!(
                    "`{}` does not implement `{}`, which `{name}` needs of `{param}`",
                    self.show(&ty),
                    self.iface_name(iface)
                );
                self.error(codes::MISSING_IMPLEMENTATION, span, message);
            }
        }
    }

    /// Whether the value `e` builds takes a function value itself, rather than in a part
    /// that holds one already: as an element or argument, or a closure as its result or
    /// error.
    fn wraps_fn(&self, e: ExprId) -> bool {
        let bare = |e: &ExprId| self.p.expr_ty.get(*e).is_some_and(|ty| matches!(self.vars.resolve(ty), Ty::Fn(..)));
        match &self.m.exprs[e].kind {
            ExprKind::Closure(_) => self
                .vars
                .zonk(self.p.ty(e))
                .fn_parts()
                .is_some_and(|(_, ret, fails, _)| matches!(ret, Ty::Fn(..)) || matches!(fails, Ty::Fn(..))),
            // Only a variant takes a function value into what it gives. A function value
            // given to a function's type parameter is a type argument, reported by
            // [`Checker::fn_targ`], and a closure's result was reported in the closure.
            ExprKind::Call { callee, args, .. } if matches!(self.p.res(*callee), Some(Res::Ctor(..))) => {
                args.iter().any(|arg| bare(&arg.value))
            }
            // A qualified variant, as in `Option.Some(f)`.
            ExprKind::MethodCall { args, .. } if matches!(self.p.res(e), Some(Res::Ctor(..))) => {
                args.iter().any(|arg| bare(&arg.value))
            }
            ExprKind::List(elements) | ExprKind::Tuple(elements) => elements.iter().any(bare),
            ExprKind::Map(entries) => entries.iter().any(|(key, value)| bare(key) || bare(value)),
            _ => false,
        }
    }

    /// The first of `bounds` that type argument `ty` doesn't implement. One that holds a
    /// function value was reported where it was made (E0509), so its bounds are not.
    fn unmet_bound(&self, ty: &Ty, bounds: &[IfaceId]) -> Option<IfaceId> {
        let iface = bounds.iter().copied().find(|&iface| !self.implements(ty, iface))?;
        (!holds_fn(&self.vars.zonk(ty))).then_some(iface)
    }

    /// Reports a function value as a type argument and returns whether it did (E0509). One
    /// call is reported once. A type that holds one was reported where it was made, and its
    /// constraints aren't (see [`Checker::unmet_bound`]).
    fn fn_targ(&mut self, ty: &Ty, span: Span) -> bool {
        if !matches!(ty, Ty::Fn(..)) {
            return false;
        }
        if self.escaped.contains(&span) {
            return true;
        }
        self.escaped.push(span);
        let message = format!(
            "`{}` is a function type, which can't be a type argument, since a function value lives only as long as what it captures",
            self.show(ty)
        );
        self.error(codes::FUNCTION_VALUE_ESCAPES, span, message);
        true
    }

    /// A record's constructor takes its fields as parameters, so a construction follows the
    /// rules of a call (REFERENCE §4.4). It stores its arguments, so it copies them.
    /// A generic record takes its type arguments from its fields and the expected type
    /// together, as a variant does (OPEN_QUESTIONS P5).
    fn construct(&mut self, callee: ExprId, id: AdtId, args: &[Arg], span: Span, expected: Option<&Ty>) -> Ty {
        self.p.res.insert(callee, Res::Ctor(id, VariantIdx::RECORD));
        let def = self.p.decls.adt(id);
        let name = def.name.clone();
        let params: Vec<(Box<str>, Ty)> = def.variant().fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        let targs = self.variant_args(id, expected, span);
        let counted = self.generic_args(&name, &params, &targs, args, span, Modes::Take);
        self.variant_type(id, targs, expected, span, !counted)
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
            if let Some((v, _)) = self.p.decls.adt(id).variant_named(name) {
                let ctor = self.p.decls.ctor_name(id, v);
                self.ctor_targs(targs, id, &ctor, span);
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
            // `Set` and `Array` come later, also as the receivers of their functions (Q37).
            let generic = self.generic_scope.iter().any(|(sym, _)| *sym == receiver_name.sym);
            if let Some(planned) = later_type(m.text(receiver_name.sym))
                .or_else(|| unexported_type(m.text(receiver_name.sym)).filter(|_| !generic))
                && !self.poisoned.contains(&receiver_name.sym)
            {
                let what = format!("`{}` types", m.text(receiver_name.sym));
                self.not_implemented(receiver_name.span, &what, planned);
                self.rejected_args(args);
                return Ty::Error;
            }
            // `[]` and `[:]` build collections, which have no associated functions (STD.md).
            if let Some(id) = collection_adt(m.text(receiver_name.sym))
                && !self.poisoned.contains(&receiver_name.sym)
            {
                let ty = self.p.decls.adt(id).name.clone();
                let empty = if id == AdtId::MAP { "[:]" } else { "[]" };
                let message = format!("`{ty}` has no associated function `{name}`; `{empty}` builds an empty one");
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
                self.rejected_args(args);
                return Ty::Error;
            }
            if let Some(ty) = builtin_type(m.text(receiver_name.sym)).filter(|ty| ty.is_numeric() || is_scalar(ty)) {
                return self.scalar_call(e, &ty, receiver_name, method, targs, args, span, chain);
            }
            // A rejected declaration may have had the name.
            if self.poisoned.contains(&receiver_name.sym) {
                self.rejected_args(args);
                return Ty::Error;
            }
        }
        self.in_chain = chain;
        // Which method this is depends on the receiver's type, so it must be known here. A
        // list's or map's own methods don't depend on its type arguments, so what the call
        // meets may still give them (OPEN_QUESTIONS P5; issue #10). Nor do the others depend
        // on a handler's error types in them, which its join settles (issue #37).
        let receiver_ty = self.infer(receiver);
        let open = self.vars.resolve(&receiver_ty);
        let receiver_ty = match open {
            Ty::Adt(AdtId::LIST | AdtId::MAP | AdtId::POOL, _) if builtin_method(&open, name).is_some() => open,
            _ => self.force_receiver(&receiver_ty),
        };
        if let Ty::Cap(cap) = &receiver_ty {
            return self.cap_call(e, cap.iface, cap.perms, (receiver, &receiver_ty), method, targs, args, span, chain);
        }
        if let (Ty::Adt(AdtId::SYSTEM, _), "with") = (&receiver_ty, name) {
            self.system_constructed(method.span, "copied with `with`");
            self.rejected_args(args);
            return Ty::Error;
        }
        if let (Ty::Adt(id, _), "with") = (&receiver_ty, name)
            && self.p.decls.adt(*id).kind == AdtKind::Record
            && !self.p.decls.adt(*id).tuple
            && !self.p.decls.adt(*id).distinct
        {
            self.no_targs(targs, name, span);
            self.p.res.insert(e, Res::With);
            // The new record takes the fields it doesn't replace, so a unique one is consumed
            // (REFERENCE §4.4).
            if self.p.decls.adt(*id).unique {
                self.consumed.insert(receiver);
                self.element_taken(receiver, &receiver_ty);
            }
            self.with_args(e, &receiver_ty, args, span);
            return receiver_ty;
        }
        // The `Text` methods of §12.3 that STD.md doesn't declare yet.
        let planned = matches!(name, "split" | "chars" | "find" | "find_last" | "slice" | "normalize_nfc");
        if receiver_ty == Ty::Text && planned {
            let what = format!("`Text` methods of §12.3, such as `{name}`,");
            self.not_implemented(method.span, &what, Planned::Unscheduled);
            self.rejected_args(args);
            return Ty::Error;
        }
        if let Ty::Adt(AdtId::LIST | AdtId::MAP, _) = receiver_ty
            && let Some((what, planned)) = later_collection_method(name)
        {
            self.not_implemented(method.span, &format!("{what}, such as `{name}`,"), planned);
            self.rejected_args(args);
            return Ty::Error;
        }
        if let Some(sig) = builtin_method(&receiver_ty, name) {
            self.no_targs(targs, name, span);
            self.p.res.insert(e, Res::Method(sig.builtin));
            if sig.builtin.changes_receiver() {
                self.changes(receiver, name);
            }
            if let Some((ty, iface, param)) = sig.needs {
                self.needs(ty, iface, name, param, span);
            }
            let modes = if sig.takes { Modes::Take } else { Modes::Borrow };
            self.generic_args(name, &sig.params, &[], args, span, modes);
            if let Some(err) = sig.fails {
                self.fallible_call(e, name, &err, span, chain);
            }
            return sig.ret;
        }
        let found = self.vars.as_never(&receiver_ty);
        let callee = self.resolve_method(&found, &receiver_ty, method);
        if let Some(Callee::Iface(iface, _)) = callee
            && found != receiver_ty
        {
            self.pending.push(Pending::Method { ty: receiver_ty.clone(), iface, name: name.into(), span: method.span });
        }
        match callee {
            Some(Callee::Fn(f)) => {
                self.p.res.insert(e, Res::Fn(f));
                // An `inout self` method changes its receiver, and a `take self` one owns it
                // (REFERENCE §5.2).
                match self.p.fns[f].self_mode {
                    mode @ (ParamMode::Inout | ParamMode::InoutPartial) => {
                        self.changes(receiver, name);
                        // The receiver of a resource is partial, as an `&` of one is (§5.4).
                        let partial = mode == ParamMode::InoutPartial;
                        if (partial || self.p.decls.is_resource(&receiver_ty)) && self.refined_part(receiver) {
                            let method = if partial {
                                "an `inout(partial) self` method"
                            } else {
                                "an `inout self` method of a resource"
                            };
                            let message = format!(
                                "this is a part of a refined value, which a failure could leave breaking its refinement, so it can't be the receiver of {method}, which keeps partial changes (§5.4)"
                            );
                            self.error(codes::PARTIAL_INOUT_OF_REFINED_PART, self.span(receiver), message);
                        }
                    }
                    ParamMode::Take => {
                        self.consumed.insert(receiver);
                        self.element_taken(receiver, &receiver_ty);
                    }
                    _ => {}
                }
                self.fn_call(e, f, Some(&receiver_ty), targs, args, span, chain, expected)
            }
            Some(Callee::Iface(iface, j)) => {
                self.dispatch_call(e, iface, j, (receiver, &receiver_ty), method, targs, args, span, chain, false)
            }
            None => {
                self.rejected_args(args);
                Ty::Error
            }
        }
    }

    /// `x.f(…)` on a capability of `iface` with `perms`: an operation of its interface, which
    /// the static type must permit, or `x.only::[…]()` (REFERENCE §9.2). A call the type
    /// doesn't permit is still checked as the operation's, so nothing else is reported (§15.1).
    #[allow(clippy::too_many_arguments)]
    fn cap_call(
        &mut self,
        e: ExprId,
        iface: IfaceId,
        perms: Perms,
        (receiver, receiver_ty): (ExprId, &Ty),
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
    ) -> Ty {
        let name = self.m.text(method.sym);
        if name == "only" {
            if self.only_declared.contains(&iface) {
                self.rejected_args(args);
                return Ty::Error;
            }
            return self.only_call(e, iface, perms, receiver_ty, method, targs, args, span);
        }
        let def = self.p.decls.iface(iface);
        let Some(j) = def.method(name) else {
            if matches!(iface, IfaceId::NET | IfaceId::PROCESS | IfaceId::CLOCK | IfaceId::RANDOM | IfaceId::ENV) {
                let what = format!("the operations of `{}`", def.name);
                self.not_implemented(method.span, &what, Planned::Unscheduled);
            } else if !def.incomplete
                // A rejected `impl` for the capability type may have declared the method (§15.1).
                && !self.unknown_tys.iter().any(|ty| matches!(ty, Ty::Cap(cap) if cap.iface == iface))
            {
                let message = format!("`{}` has no operation `{name}`", self.show(receiver_ty));
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
            self.rejected_args(args);
            return Ty::Error;
        };
        if !self.view_permits(receiver, iface, perms, j, method.span) {
            self.permits(iface, perms, j, receiver_ty, method.span);
        }
        self.dispatch_call(e, iface, j, (receiver, receiver_ty), method, targs, args, span, chain, false)
    }

    /// Reports a call of operation `j` of `iface` on a capability of type `ty`, whose
    /// permissions `perms` lack some that it needs (REFERENCE §9.2).
    fn permits(&mut self, iface: IfaceId, perms: Perms, j: usize, ty: &Ty, span: Span) {
        let method = &self.p.decls.iface(iface).methods[j];
        let missing = method.needs.minus(perms);
        if missing == Perms::NONE {
            return;
        }
        let (name, missing) = (method.name.clone(), self.p.decls.perm_names(iface, missing));
        let message = format!(
            "`{}` doesn't permit `{name}`, which needs `{missing}`; pass a capability that has it",
            self.show(ty)
        );
        self.error(codes::PERMISSION_NOT_GRANTED, span, message);
    }

    /// `x.only::[read]()`: the capability `x` of `iface`, narrowed to the permissions it
    /// names, which `x` must have, and using what `x` uses (REFERENCE §9.2).
    #[allow(clippy::too_many_arguments)]
    fn only_call(
        &mut self,
        e: ExprId,
        iface: IfaceId,
        perms: Perms,
        receiver_ty: &Ty,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
    ) -> Ty {
        let m = self.m;
        let Some(targs) = targs else {
            let message = "`only` names the permissions it keeps, as in `x.only::[read]()`";
            self.error(codes::TYPE_ARGUMENT_COUNT, method.span, message);
            self.rejected_args(args);
            return Ty::Error;
        };
        if !args.is_empty() {
            let message = "`only` takes no arguments; it names the permissions it keeps in `::[…]`";
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.rejected_args(args);
        }
        let mut names = Vec::new();
        for &t in targs {
            let TypeExprKind::Named(name) = m.types[t].kind else {
                let message = "`only` names permissions, as in `x.only::[read]()`";
                self.error(codes::UNKNOWN_TYPE, m.types[t].span, message);
                return Ty::Error;
            };
            names.push(name);
        }
        let (kept, ok) = self.perms_named(iface, &names, "`only`");
        if !ok {
            return Ty::Error;
        }
        let missing = kept.minus(perms);
        if missing != Perms::NONE {
            let message = format!(
                "`{}` lacks `{}`, so `only` can't keep it; `only` narrows a capability and never widens one",
                self.show(receiver_ty),
                self.p.decls.perm_names(iface, missing)
            );
            self.error(codes::PERMISSION_NOT_GRANTED, method.span, message);
        }
        self.p.res.insert(e, Res::Method(Builtin::Only));
        // The implementation is the same, so it uses what it did.
        let uses = match receiver_ty {
            Ty::Cap(cap) => cap.uses.clone(),
            _ => Reach::default(),
        };
        Ty::cap_uses(iface, kept, uses)
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
            (Ty::Int(it), "try_from" | "wrapping_from") => {
                let callee = format!("{type_text}.{name}");
                self.no_targs(targs, &callee, span);
                let builtin = if name == "try_from" { Builtin::TryFrom(*it) } else { Builtin::WrappingFrom(*it) };
                self.p.res.insert(e, Res::Method(builtin));
                self.int_arg(&callee, args, span);
                if name == "try_from" {
                    self.fallible_call(e, &callee, &Ty::adt(AdtId::CONVERSION_ERROR), span, chain);
                }
                return ty.clone();
            }
            (Ty::Float(ft), "from") => {
                let callee = format!("{type_text}.from");
                self.no_targs(targs, &callee, span);
                self.p.res.insert(e, Res::Method(Builtin::Convert(Num::Float(*ft))));
                self.int_arg(&callee, args, span);
                return ty.clone();
            }
            // `Int.from` would be the lossless `Int(x)`, and the rest have no agreed meaning
            // yet (OPEN_QUESTIONS §G).
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

    /// `T(x)`, where `T` is the built-in type `target`: a conversion that keeps every value,
    /// from an integer type to one that holds all of its values, or from `Float32` to `Float`.
    /// A conversion that may lose a value is spelled as what it does, by `T.try_from`,
    /// `T.wrapping_from`, `T.from` or `to_int` (STD.md). A literal argument has type `T`.
    fn conversion(
        &mut self,
        callee: ExprId,
        name: Ident,
        target: Ty,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
    ) -> Ty {
        let text = self.m.text(name.sym);
        let num = match target {
            Ty::Int(it) => Num::Int(it),
            Ty::Float(ft) => Num::Float(ft),
            _ => {
                let message = format!("`{text}` has no constructor, and only a numeric type converts with `T(x)`");
                self.error(codes::UNKNOWN_NAME, name.span, message);
                self.rejected_args(args);
                return Ty::Error;
            }
        };
        self.no_targs(targs, text, span);
        let [arg] = args else {
            let message = format!("`{text}(…)` converts 1 value, but {} were given", args.len());
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.rejected_args(args);
            return Ty::Error;
        };
        if let Some(label) = arg.label {
            let message = format!("the value `{text}(…)` converts takes no label");
            self.error(codes::WRONG_LABEL, label.span, message);
            self.rejected_value(arg.value);
            return Ty::Error;
        }
        if arg.inout {
            let message = format!("`{text}(…)` reads its value, so its argument takes no `&`");
            self.error(codes::INOUT_MARKER_MISMATCH, self.span(arg.value), message);
        }
        let ty = self.expr(arg.value, Some(&target));
        let ty = self.force(&ty);
        let lossless = match (&ty, &target) {
            _ if ty.is_unknown() || ty == target => true,
            (Ty::Int(from), Ty::Int(to)) => to.min() <= from.min() && from.max() <= to.max(),
            // A float holds every integer up to 2^24 or 2^53 exactly, by the bits of its
            // significand.
            (Ty::Int(from), Ty::Float(to)) => {
                let exact: i128 = if *to == FloatTy::F32 { 1 << 24 } else { 1 << 53 };
                -exact <= from.min() && from.max() <= exact
            }
            (Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F64)) => true,
            _ => false,
        };
        if !lossless {
            let shown = self.show(&ty);
            let instead = match (&ty, &target) {
                (Ty::Int(_), Ty::Int(_)) => format!(
                    "`{text}.try_from(x)` fails when it doesn't fit, and `{text}.wrapping_from(x)` keeps its low bits"
                ),
                (Ty::Int(_), Ty::Float(_)) => format!("`{text}.from(x)` rounds it to the nearest `{text}`"),
                (Ty::Float(_), Ty::Int(_)) => {
                    "`x.to_int(rounding: Rounding.TowardZero)` rounds it as it says and gives an `Int`".to_string()
                }
                (Ty::Float(_), Ty::Float(_)) => "no conversion narrows a float yet".to_string(),
                _ => String::new(),
            };
            let message = match &ty {
                Ty::Int(_) | Ty::Float(_) => {
                    format!("`{text}(…)` can't convert `{shown}` without losing values; {instead}")
                }
                Ty::Adt(id, _) if self.p.decls.adt(*id).distinct => format!(
                    "`{text}(…)` converts a number, not `{shown}`; a distinct type's number is `x.value` (§4.6)"
                ),
                _ => format!("`{text}(…)` converts a number, not `{shown}`"),
            };
            self.error(codes::TYPE_MISMATCH, self.span(arg.value), message);
            return target;
        }
        self.p.res.insert(callee, Res::Method(Builtin::Convert(num)));
        target
    }

    /// Checks the one argument of `callee`, which converts a value of any integer type.
    fn int_arg(&mut self, callee: &str, args: &[Arg], span: Span) {
        let [arg] = args else {
            let message = format!("`{callee}` takes 1 argument, but {} were given", args.len());
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.rejected_args(args);
            return;
        };
        // STD.md names the one parameter `value`, so its label is optional (H3).
        if let Some(label) = arg.label
            && self.m.text(label.sym) != "value"
        {
            let message = format!("`{callee}`'s one parameter is `value`, so its label is `value:` or none");
            self.error(codes::WRONG_LABEL, label.span, message);
            self.rejected_value(arg.value);
            return;
        }
        if arg.inout {
            let message = format!("`{callee}` reads its value, so its argument takes no `&`");
            self.error(codes::INOUT_MARKER_MISMATCH, self.span(arg.value), message);
        }
        let ty = self.infer(arg.value);
        let ty = self.force(&ty);
        if !matches!(ty, Ty::Int(_)) && !ty.is_unknown() {
            let message = format!("`{callee}` converts an integer, not `{}`", self.show(&ty));
            self.error(codes::TYPE_MISMATCH, self.span(arg.value), message);
        }
    }

    /// The method `x.name(…)` calls on a value of type `ty`: one of the type's own, or one of
    /// an interface it implements, which must be the only one (REFERENCE §3). Reports a
    /// call that resolves to none or to several.
    /// A message writes the type as `shown`, the receiver's own type, where `ty` reads its
    /// open error types as `Never` (see [`Checker::force_receiver`]).
    fn resolve_method(&mut self, ty: &Ty, shown: &Ty, method: Ident) -> Option<Callee> {
        let m = self.m;
        let name = m.text(method.sym);
        if *ty == Ty::Error {
            return None;
        }
        let mut found: Vec<Callee> = Vec::new();
        // A method of the type's whose `impl` target the type doesn't match.
        let mut elsewhere: Option<FnId> = None;
        if let Ty::Adt(id, _) = ty
            && let Some(entries) = self.inherent.get(id)
        {
            let mut named = entries.iter().filter(|e| e.name == method.sym);
            // A rejected declaration of the name, a duplicate or one named like an interface's
            // method, may be the one the call means, and it has been reported (§15.1).
            if named.clone().any(|e| e.rejected) {
                return None;
            }
            // A method of a generic `impl` is one of the types its target matches (OPEN_QUESTIONS
            // P5).
            if let Some(entry) = named.next() {
                let info = &self.p.fns[entry.f];
                let mut binds = vec![None; info.impl_params];
                if info.owner.as_ref().is_none_or(|owner| matches_target(owner, ty, &mut binds)) {
                    found.push(Callee::Fn(entry.f));
                } else {
                    elsewhere = Some(entry.f);
                }
            }
        }
        // A rejected `impl` block or method declaration may have declared the method.
        let mut unknown = self.p.decls.unknown_methods(ty) || self.unknown_tys.contains(ty);
        // A rejected `derives` entry or `impl` block makes the type implement every interface,
        // so only its own method is known to exist.
        let interfaces_known = !self.unknown_interfaces(ty);
        unknown |= !interfaces_known;
        // An interface whose `impl` matches the type but whose constraints it doesn't meet.
        let mut unmet: Option<IfaceId> = None;
        for (iface, def) in self.p.decls.ifaces() {
            if !self.implements(ty, iface) {
                if unmet.is_none() && def.method(name).is_some() && self.p.decls.impl_for(iface, ty).is_some() {
                    unmet = Some(iface);
                }
                continue;
            }
            if !interfaces_known && !found.is_empty() {
                continue;
            }
            unknown |= def.incomplete;
            if let Some(j) = def.method(name) {
                found.push(Callee::Iface(iface, j));
            }
        }
        match found.as_slice() {
            [] if !unknown && let Some(iface) = unmet => {
                self.unmet_impl(ty, shown, iface, method.span);
                None
            }
            [] if !unknown && let Some(f) = elsewhere => {
                let info = &self.p.fns[f];
                let names: Vec<Box<str>> = info.generics.iter().map(|g| g.name.clone()).collect();
                let owner = info.owner.as_ref().expect("a method has an owner");
                let message = format!(
                    "`{}` has no method `{name}`; the `impl` that declares it is for `{}`",
                    self.show(shown),
                    self.p.decls.display_in(owner, &names)
                );
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
                None
            }
            [] => {
                if !unknown {
                    let message = format!("`{}` has no method `{name}`", self.show(shown));
                    self.error(codes::UNKNOWN_MEMBER, method.span, message);
                }
                None
            }
            [Callee::Fn(f)] if self.p.fns[*f].receiver.is_none() => {
                let message = format!(
                    "`{name}` is an associated function, so it is called on the type, as in `{}.{name}(…)`",
                    self.show(shown)
                );
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
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
                    self.show(shown),
                    owners.join(" and "),
                    owners[0].trim_matches('`')
                );
                self.error(codes::AMBIGUOUS_METHOD, method.span, message);
                None
            }
        }
    }

    /// Reports that `ty`, written as `shown`, doesn't implement `iface`, whose generic `impl`
    /// matches it, because a type argument doesn't meet the block's constraints (E0309).
    fn unmet_impl(&mut self, ty: &Ty, shown: &Ty, iface: IfaceId, span: Span) {
        let Some((def, binds)) = self.p.decls.impl_for(iface, ty) else { return };
        let unmet = binds.iter().zip(&def.bounds).find_map(|(bind, bounds)| {
            let arg = bind.as_ref()?;
            Some((arg.clone(), self.unmet_bound(arg, bounds)?))
        });
        let iface_text = self.iface_name(iface).to_string();
        let message = match unmet {
            Some((arg, need)) => format!(
                "`{}` does not implement `{iface_text}`, since its `impl` needs `{}` to implement `{}`",
                self.show(shown),
                self.show(&arg),
                self.iface_name(need)
            ),
            None => format!("`{}` does not implement `{iface_text}`", self.show(shown)),
        };
        self.error(codes::MISSING_IMPLEMENTATION, span, message);
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
        if self.p.decls.adt(adt).is_native() {
            return self.native_call(e, adt, method, targs, args, span, expected);
        }
        let def = self.p.decls.adt(adt);
        let entries = self.inherent.get(&adt).map_or(&[][..], Vec::as_slice);
        // A rejected declaration of the name may be the one the call means, and it has been
        // reported (§15.1).
        let rejected = entries.iter().any(|entry| entry.name == method.sym && entry.rejected);
        match entries.iter().find(|entry| entry.name == method.sym).map(|entry| entry.f) {
            Some(_) if rejected => {}
            Some(f) if self.p.fns[f].receiver.is_none() => {
                self.p.res.insert(e, Res::Fn(f));
                return self.fn_call(e, f, None, targs, args, span, chain, expected);
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
                self.not_implemented(span, &what, Planned::Phase(5));
            }
            None => {
                let message = format!("`{}` has no associated function `{name}`", def.name);
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
        }
        self.rejected_args(args);
        Ty::Error
    }

    /// `Pool.new()`, the one associated function of `std.pool`'s types, whose element type
    /// comes from the type it is expected to have, or else from what it meets, as `[]`'s
    /// does (STD.md).
    #[allow(clippy::too_many_arguments)]
    fn native_call(
        &mut self,
        e: ExprId,
        adt: AdtId,
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        expected: Option<&Ty>,
    ) -> Ty {
        let name = self.m.text(method.sym);
        let ty = self.p.decls.adt(adt).name.clone();
        if (adt, name) != (AdtId::POOL, "new") {
            let message = match adt {
                AdtId::POOL => format!("`{ty}` has no associated function `{name}`; `{ty}.new()` builds an empty pool"),
                _ => format!("`{ty}` has no associated function `{name}`; a pool's `insert` makes handles"),
            };
            self.error(codes::UNKNOWN_MEMBER, method.span, message);
            self.rejected_args(args);
            return Ty::Error;
        }
        self.no_targs(targs, "Pool.new", span);
        self.p.res.insert(e, Res::Method(Builtin::PoolNew));
        self.args("Pool.new", &[] as &[(&str, Ty)], args, span);
        let element = match expected {
            Some(Ty::Adt(AdtId::POOL, args)) => args[0].clone(),
            Some(Ty::Error) => self.vars.rejected(),
            _ => self.vars.fresh(Kind::Any, Origin::Variant { adt: AdtId::POOL, span }),
        };
        Ty::applied(AdtId::POOL, vec![element])
    }

    /// The interface that `sym` names: the module's, the prelude's, or a capability interface
    /// imported from the standard library.
    fn iface_named(&self, sym: Symbol) -> Option<IfaceId> {
        if self.poisoned.contains(&sym) {
            return None;
        }
        (self.iface_names.get(&sym).copied())
            .or_else(|| IfaceId::prelude(self.m.text(sym)))
            .or_else(|| self.cap_named(sym))
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
        let (found, cap) = (def.method(name), def.cap.is_some());
        let rejected = match found {
            None if iface.methods_later() => {
                self.not_implemented(method.span, &format!("calls of `{iface_text}`'s methods"), Planned::Unscheduled);
                true
            }
            None if def.incomplete => true,
            // `Dir.of(x)` makes a capability of a `cap record` (REFERENCE §9.6).
            None if cap && name == "of" => return self.of_call(e, iface, targs, args, span),
            None if cap && name == "only" && self.only_declared.contains(&iface) => true,
            None if cap && name == "only" => {
                let message = "`only` has no qualified form; call it on the capability, as in `x.only::[…]()`";
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
                true
            }
            None => {
                let message = format!("`{iface_text}` has no method `{name}`");
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
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
        if iface == IfaceId::ABANDON
            && (self.rejected_abandon_for.iter())
                .any(|(target, params)| matches_target(target, &receiver_ty, &mut vec![None; *params]))
        {
            self.rejected_args(rest);
            return Ty::Error;
        }
        if !receiver_ty.is_unknown() && !self.implements(&receiver_ty, iface) {
            let at = self.span(first.value);
            // A capability interface is a type, so its receiver is a value of that type (Q31).
            if cap {
                let message = format!("expected `{iface_text}`, found `{}`", self.show(&receiver_ty));
                self.error(codes::TYPE_MISMATCH, at, message);
            } else {
                let message = format!("`{}` does not implement `{iface_text}`", self.show(&receiver_ty));
                self.error(codes::MISSING_IMPLEMENTATION, at, message);
            }
            self.rejected_args(rest);
            return Ty::Error;
        }
        if let Ty::Cap(cap) = &receiver_ty {
            self.permits(iface, cap.perms, j, &receiver_ty, method.span);
        }
        self.dispatch_call(e, iface, j, (first.value, &receiver_ty), method, targs, rest, span, chain, true)
    }

    /// `X.of(r)`: a capability of `iface` with every permission it declares, which runs the
    /// operations of `r`, a `cap record` that implements it, and uses what `r` reaches besides
    /// `iface` (REFERENCE §9.6; OPEN_QUESTIONS P5).
    fn of_call(&mut self, e: ExprId, iface: IfaceId, targs: Option<&[TypeId]>, args: &[Arg], span: Span) -> Ty {
        let iface_text = self.iface_name(iface).to_string();
        self.no_targs(targs, "of", span);
        let [arg] = args else {
            let message = format!("`{iface_text}.of` takes one `cap record` that implements `{iface_text}`");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            self.rejected_args(args);
            return Ty::Error;
        };
        if let Some(label) = arg.label {
            let message = format!("the argument of `{iface_text}.of` takes no label (H3)");
            self.error(codes::WRONG_LABEL, label.span, message);
        }
        let ty = self.infer(arg.value);
        let ty = self.force(&ty);
        let at = self.span(arg.value);
        match &ty {
            ty if ty.is_unknown() => return Ty::Error,
            Ty::Adt(id, _) if self.p.decls.adt(*id).cap => {
                if !self.implements(&ty, iface) {
                    let message = format!("`{}` does not implement `{iface_text}`", self.show(&ty));
                    self.error(codes::MISSING_IMPLEMENTATION, at, message);
                    return Ty::Error;
                }
            }
            ty => {
                let message = format!(
                    "`{iface_text}.of` makes a capability of a `cap record` that implements `{iface_text}`, and `{}` isn't one (§9.6)",
                    self.show(ty)
                );
                self.error(codes::TYPE_MISMATCH, at, message);
                return Ty::Error;
            }
        }
        self.p.res.insert(e, Res::Method(Builtin::Of));
        let uses = self.p.decls.reach(&ty, &[]).without(iface).without_params();
        Ty::cap_uses(iface, self.p.decls.iface(iface).all_perms(), uses)
    }

    /// A call of method `j` of `iface` on a receiver of type `receiver_ty`, with `Self` read
    /// as that type. The implementation for the receiver's value runs it (REFERENCE §4.9). A
    /// `take self` method owns the receiver.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_call(
        &mut self,
        e: ExprId,
        iface: IfaceId,
        j: usize,
        (receiver, receiver_ty): (ExprId, &Ty),
        method: Ident,
        targs: Option<&[TypeId]>,
        args: &[Arg],
        span: Span,
        chain: bool,
        qualified: bool,
    ) -> Ty {
        let name = self.m.text(method.sym);
        self.no_targs(targs, name, span);
        if self.p.decls.iface(iface).methods[j].self_mode == ParamMode::Take {
            self.consumed.insert(receiver);
            self.element_taken(receiver, receiver_ty);
        }
        let def = &self.p.decls.iface(iface).methods[j];
        let receiver = [receiver_ty.clone()];
        let params: Vec<(Box<str>, Ty)> = def.params.iter().map(|(n, t)| (n.clone(), t.subst(&receiver))).collect();
        let modes = def.modes.clone();
        let ret = def.ret.subst(&receiver);
        let fails = def.fails.as_ref().map(|t| t.subst(&receiver));
        self.p.res.insert(e, Res::Dispatch { iface, method: j, qualified });
        // A generic `impl`'s method may drop a value of its type parameter, as a generic
        // function may (OPEN_QUESTIONS P5, Resources in generic code).
        let found = self.vars.zonk(&receiver[0]);
        if let Some((def, binds)) = self.p.decls.impl_for(iface, &found)
            && let Some(i) = binds.iter().position(|bind| bind.as_ref().is_some_and(|ty| self.p.decls.is_resource(ty)))
        {
            let param = match def.methods[j] {
                Some(f) => self.p.fns[f].generics[i].name.clone(),
                None => "_".into(),
            };
            let ty = binds[i].clone().expect("a resource was bound");
            self.resource_targ(&ty, name, &param, span);
            self.rejected_args(args);
            return ret;
        }
        self.generic_args(name, &params, &[], args, span, Modes::Each(&modes));
        if let Some(err) = fails {
            self.fallible_call(e, name, &err, span, chain);
        }
        ret
    }

    /// The type arguments `args` of a value's type, with each type parameter of the function
    /// whose declaration or constraint is rejected unknown, as in the bodies of `impl[T: Nope]
    /// Box[T]`, so the parts of that type aren't reported (§15.1).
    fn known_args(&self, args: &[Ty]) -> Vec<Ty> {
        if !self.f.rejected.contains(&true) {
            return args.to_vec();
        }
        let unknown: Vec<Ty> = (self.f.rejected.iter().enumerate())
            .map(|(i, &rejected)| if rejected { Ty::Error } else { Ty::Param(i as u32) })
            .collect();
        args.iter().map(|arg| arg.subst(&unknown)).collect()
    }

    fn field(&mut self, e: ExprId, base_ty: &Ty, name: Ident) -> Ty {
        let text = self.m.text(name.sym);
        if let Ty::Adt(id, args) = base_ty
            && let Some((i, field)) = self.p.decls.adt(*id).field(text)
        {
            // Only the record's own `impl` blocks see its state (OPEN_QUESTIONS Q40).
            if field.state && !matches!(&self.self_ty, Some(Ty::Adt(owner, _)) if owner == id) {
                let record = self.p.decls.name(*id);
                let message = format!(
                    "`{text}` is a `state` field of `{record}`, which only `{record}`'s own `impl` blocks see (§9.6)"
                );
                self.error(codes::UNKNOWN_MEMBER, name.span, message);
                return Ty::Error;
            }
            let ty = field.ty.subst(&self.known_args(args));
            self.p.res.insert(e, Res::Field(i));
            return ty;
        }
        match (base_ty, text) {
            (Ty::Adt(AdtId::SYSTEM, _), text) if LATER_SYSTEM_FIELDS.contains(&text) => {
                self.not_implemented(name.span, &format!("`sys.{text}` and the rest of `std.fs`"), Planned::Phase(3));
                Ty::Error
            }
            (Ty::Error, _) => Ty::Error,
            (ty, _) if self.has_method(ty, name.sym) => {
                let message = format!(
                    "`{text}` is a method, which is called with its arguments; it isn't a function value, but a closure can wrap a call of it, as in `|| x.{text}()`"
                );
                self.error(codes::METHOD_VALUE, name.span, message);
                self.method_values.insert(e);
                Ty::Error
            }
            (ty, _) => {
                let message = format!("`{}` has no field `{text}`", self.show(ty));
                self.error(codes::UNKNOWN_MEMBER, name.span, message);
                Ty::Error
            }
        }
    }

    /// Reports a `System` that is `how`: built, copied with `with` or matched by a pattern.
    /// The runtime gives `main` the only one (REFERENCE §9.1).
    fn system_constructed(&mut self, span: Span, how: &str) {
        let message = format!(
            "a `System` can't be {how}; the runtime gives `main` the only one, and its fields are read by name, as in `sys.stdout` (§9.1)"
        );
        self.error(codes::SYSTEM_CONSTRUCTED, span, message);
    }

    /// Checks the arguments of `with`. They label the fields they replace, at least one, once
    /// each and in declaration order, even on a one-field record (OPEN_QUESTIONS P5). One
    /// label problem is reported per call.
    /// A generic record keeps its type arguments, so a field it replaces keeps its type.
    fn with_args(&mut self, e: ExprId, record_ty: &Ty, args: &[Arg], span: Span) {
        let m = self.m;
        let Ty::Adt(id, targs) = record_ty else { return };
        let id = *id;
        let targs = self.known_args(targs);
        let def = self.p.decls.adt(id);
        let record = def.name.clone();
        let fields: Vec<(Box<str>, Ty)> =
            def.variant().fields.iter().map(|f| (f.name.clone(), f.ty.subst(&targs))).collect();
        let state: Vec<bool> = def.variant().fields.iter().map(|f| f.state).collect();
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
                let message = "`with` replaces fields, which aren't `inout` parameters, so its arguments take no `&`";
                self.error(codes::INOUT_MARKER_MISMATCH, span, message);
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
                (Some((label, text)), None) => {
                    Some((codes::UNKNOWN_MEMBER, label.span, format!("`{record}` has no field `{text}`")))
                }
                // A copy made by `with` shares the state, so it has nothing of it to replace
                // (OPEN_QUESTIONS Q40).
                (Some((label, text)), Some(i)) if state[i] => Some((
                    codes::UNKNOWN_MEMBER,
                    label.span,
                    format!(
                        "`with` replaces plain fields, and `{text}` is a `state` field of `{record}`, which the copy shares (§9.6)"
                    ),
                )),
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
        self.generic_args(callee, params, &[], args, span, Modes::Borrow);
    }

    /// Checks arguments against parameters whose types may mention the type parameters
    /// `targs` gives, which may be variables, so an argument in any position may give them
    /// (OPEN_QUESTIONS P5; issue #10). An argument for a `take` parameter is copied, or moved,
    /// as a construction's are, and one for an `inout` parameter is written `&x` (REFERENCE
    /// §5.2). Returns whether the number of arguments was right.
    fn generic_args<S: AsRef<str>>(
        &mut self,
        callee: &str,
        params: &[(S, Ty)],
        targs: &[Ty],
        args: &[Arg],
        span: Span,
        modes: Modes,
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
        // One label problem is reported per call, with the labels the call needs. A function
        // value's parameters have no names, so its arguments take no labels (REFERENCE §3).
        let labelled = params.iter().map(|(param, _)| format!("{}: …", param.as_ref())).collect::<Vec<_>>().join(", ");
        let unnamed = params.iter().any(|(param, _)| param.as_ref().is_empty());
        let mut labels_reported = false;
        for (i, (arg, (param, _))) in args.iter().zip(params).enumerate() {
            let param = param.as_ref();
            match arg.label {
                _ if labels_reported => {}
                Some(label) if unnamed => {
                    let message = format!(
                        "`{callee}` is a function value, whose parameters have no names, so its arguments take no labels"
                    );
                    self.error(codes::WRONG_LABEL, label.span, message);
                    labels_reported = true;
                }
                None if unnamed => {}
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
        // A closure's parameters take their types from the others, so the others go first,
        // then each closure whose parameter types are written or settled, so the order of the
        // arguments doesn't change the types (OPEN_QUESTIONS Q33). A closure that an `if`,
        // `match` or `else` gives waits as one does.
        // Where a label is wrong, each argument is checked against the parameter its label
        // names, so the label isn't reported again as a mismatched type (§15.1; issue #51).
        // An argument whose label names a parameter another argument has is checked as written.
        let to = if labels_reported && !unnamed {
            label_order(m, args, params)
        } else {
            (0..args.len()).map(Some).collect()
        };
        let (mut closures, others): (Vec<usize>, Vec<usize>) =
            (0..args.len()).partition(|&i| self.gives_closure(args[i].value));
        for i in others {
            match to[i] {
                Some(j) => self.generic_arg(callee, j, &args[i], (params[j].0.as_ref(), &params[j].1), targs, modes),
                None => self.rejected_args(std::slice::from_ref(&args[i])),
            }
        }
        while !closures.is_empty() {
            let ready = closures
                .iter()
                .position(|&i| to[i].is_none_or(|j| self.closure_ready(args[i].value, &params[j].1, targs)))
                .unwrap_or(0);
            let i = closures.remove(ready);
            match to[i] {
                Some(j) => self.generic_arg(callee, j, &args[i], (params[j].0.as_ref(), &params[j].1), targs, modes),
                None => self.rejected_args(std::slice::from_ref(&args[i])),
            }
        }
        true
    }

    /// Checks the argument for parameter `i` of a call against parameter `param` of type `ty`.
    fn generic_arg(&mut self, callee: &str, i: usize, arg: &Arg, (param, ty): (&str, &Ty), targs: &[Ty], modes: Modes) {
        let mode = match modes {
            Modes::Borrow => ParamMode::Borrow,
            Modes::Take => ParamMode::Take,
            Modes::Each(modes) => modes.get(i).copied().unwrap_or(ParamMode::Borrow),
        };
        // A type parameter that `targs` doesn't cover is the caller's own, such as the `T`
        // that `Self` stands for in `x.bigger(y)` where `x: T`, so it is a type like any.
        let ty = if mentions_targ(ty, targs) { ty.subst(targs) } else { ty.clone() };
        let inout = matches!(mode, ParamMode::Inout | ParamMode::InoutPartial);
        if inout && arg.inout {
            // An `inout` of a resource is never rolled back, so it is partial (§5.4).
            let partial = mode == ParamMode::InoutPartial || self.p.decls.is_resource(&ty);
            self.inout_arg(arg.value, &ty, partial);
            return;
        }
        if inout || arg.inout {
            let value = self.span(arg.value);
            let n = i + 1;
            let message = if param.is_empty() && inout {
                format!(
                    "argument {n} of `{callee}` is an `inout` parameter, so it is marked with `&`, as in `{callee}(&x)`"
                )
            } else if param.is_empty() {
                format!("argument {n} of `{callee}` isn't an `inout` parameter, so it takes no `&`")
            } else if inout {
                format!("`{param}` is an `inout` parameter, so its argument is marked with `&`, as in `{param}: &x`")
            } else {
                format!("`{param}` isn't an `inout` parameter, so its argument takes no `&`")
            };
            self.error_of(arg.value, codes::INOUT_MARKER_MISMATCH, value, message);
        }
        self.copying = mode == ParamMode::Take;
        self.check(arg.value, &ty);
    }

    /// Whether the closure `arg`, passed as a parameter of type `ty`, would find its
    /// parameters' types known, from its annotations or from `ty`.
    fn closure_ready(&mut self, arg: ExprId, ty: &Ty, targs: &[Ty]) -> bool {
        let ty = if mentions_targ(ty, targs) { ty.subst(targs) } else { ty.clone() };
        let ty = self.vars.resolve(&ty);
        let written = |j: usize| match &self.m.exprs[arg].kind {
            ExprKind::Closure(closure) => closure.params.get(j).is_some_and(|param| param.ty.is_some()),
            _ => false,
        };
        ty.fn_parts().is_some_and(|(_, _, _, params)| {
            params.iter().enumerate().all(|(j, param)| written(j) || !self.vars.has_open(param))
        })
    }

    /// Whether `e` is a closure, or an `if`, `match` or `else` that may give one.
    fn gives_closure(&self, e: ExprId) -> bool {
        let tail = |block: &Block| self.tail(block).is_some_and(|e| self.gives_closure(e));
        match &self.m.exprs[e].kind {
            ExprKind::Closure(_) => true,
            ExprKind::If { then_block, else_branch, .. } => {
                tail(then_block)
                    || match else_branch {
                        Some(ElseBranch::Block(block)) => tail(block),
                        Some(ElseBranch::If(nested)) => self.gives_closure(*nested),
                        None => false,
                    }
            }
            ExprKind::Match { arms, .. } => arms.iter().any(|arm| tail(&arm.body)),
            ExprKind::Else { value, fallback } => {
                self.gives_closure(*value)
                    || match fallback {
                        Fallback::Value(value) => self.gives_closure(*value),
                        Fallback::Block(block) => tail(block),
                    }
            }
            _ => false,
        }
    }

    /// Checks an `&` argument, which a failure may leave half changed when it is `partial`.
    /// An error about it rejects the argument, not the call.
    fn inout_arg(&mut self, value: ExprId, ty: &Ty, partial: bool) {
        let (errors, inner) = (self.errors, self.inner_errors);
        self.inout_place(value, ty);
        if partial && self.errors == errors && self.refined_part(value) {
            let message = "this is a part of a refined value, which a failure could leave breaking its refinement, so it can't be passed to an `inout` parameter that keeps partial changes, as `inout(partial)` and an `inout` of a resource do (§5.4)";
            self.error(codes::PARTIAL_INOUT_OF_REFINED_PART, self.span(value), message);
        }
        let own = (self.errors - errors) - (self.inner_errors - inner);
        if self.errors > errors {
            self.rejected.insert(value);
        }
        self.inner_errors += own;
    }

    /// Whether the place `e` is a field of a record with a refinement, at any depth.
    fn refined_part(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Field { base, .. } => {
                let refined = match self.p.ty(base) {
                    Ty::Adt(id, _) => {
                        let def = self.p.decls.adt(*id);
                        !def.is_enum() && def.variants.iter().any(|v| !v.preds.is_empty())
                    }
                    _ => false,
                };
                refined || self.refined_part(base)
            }
            ExprKind::Index { base, .. } => self.refined_part(base),
            _ => false,
        }
    }

    /// `&x`, the argument of an `inout` parameter of type `ty`. It is a variable the caller
    /// may change, or a field or element of one, as an assignment's target is, and its type is
    /// the parameter's exactly, since the callee's value flows back into it (REFERENCE §5.2,
    /// §8.3).
    fn inout_place(&mut self, value: ExprId, ty: &Ty) {
        let span = self.span(value);
        if !matches!(self.m.exprs[value].kind, ExprKind::Name(_) | ExprKind::Field { .. } | ExprKind::Index { .. }) {
            let message = "an `&` argument is a variable, or a field or element of one, which the call may change";
            self.error(codes::INVALID_ASSIGNMENT_TARGET, span, message);
            self.rejected_value(value);
            return;
        }
        let Some((root, id, actual, state)) = self.place(value) else { return };
        if state {
            self.changes_state(id, span);
        } else if !self.f.locals[id.index()].mutable {
            let message = self.immutable(root, id, "pass it with `&`");
            self.error(codes::IMMUTABLE_ASSIGNMENT, span, message);
        } else if self.changes_capture(id, span) {
            return;
        }
        if actual.is_unknown() || ty.is_unknown() {
            return;
        }
        if !(self.vars.subsume(ty, &actual) && self.vars.subsume(&actual, ty)) {
            let message = format!(
                "an `&` argument has its parameter's type exactly, `{}`, but this is `{}`",
                self.show(ty),
                self.show(&actual)
            );
            // The callee may store a capability with fewer permissions in it (OPEN_QUESTIONS P3).
            let (ty_d, actual_d) = (self.vars.defaulted(ty), self.vars.defaulted(&actual));
            let code = reach_mismatch(&ty_d, &actual_d, true).unwrap_or(codes::TYPE_MISMATCH);
            self.error(code, span, message);
            self.vars.poison(&actual);
            self.vars.quiet(ty);
        }
    }

    fn fallible_call(&mut self, call: ExprId, callee: &str, err: &Ty, span: Span, chain: bool) {
        // A call whose error type is `Never`, as `::[Never]` gives it, can't fail, as one that
        // declares `fails Never` can't (OPEN_QUESTIONS P5).
        if self.vars.resolve(err) == Ty::Never {
            return;
        }
        let depth = self.markers.len().saturating_sub(1) as u32;
        match self.markers.last_mut() {
            Some(marker) if chain => {
                // Its handler joins the error type. A later receiver leaves it open inside its
                // type arguments (see `force_receiver`).
                marker.errors.push(err.clone());
                self.vars.set_handled(err, depth, true);
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
                    if let Some(scope) = self.closure_scopes.last_mut() {
                        scope.unmarked = true;
                    }
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
        // A missing marker doesn't change what the call takes, so it rejects nothing.
        self.error(codes::UNMARKED_FALLIBLE_CALL, span, message);
        self.inner_errors += 1;
    }

    fn try_expr(&mut self, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        let target = self.f.fails.clone().filter(|own| *own != Ty::Error);
        self.markers.push(Marker { handler: None, errors: Vec::new(), target });
        self.in_chain = true;
        let ty = self.expr(inner, expected);
        let errors = self.pop_marker();
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
            let message = if !self.closure_scopes.is_empty() {
                let err = self.show(err);
                format!("`try` propagates `{err}`, but the function type of this closure has no `fails {err}`")
            } else if self.f.returns {
                let err = self.show(err);
                format!("`try` propagates `{err}`, but this function does not declare `fails {err}`")
            } else {
                let place = self.f.place.describe();
                format!("`try` in {place}, which has no function to propagate `{}` to", self.show(err))
            };
            self.error(codes::TRY_ERROR_MISMATCH, span, message);
        }
    }

    /// `attempt f(…)`: a `Result` of the chain's value and the error of the calls it marks
    /// (REFERENCE §7.2).
    fn attempt_expr(&mut self, e: ExprId, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        let (value_expected, target) = match expected {
            Some(Ty::Adt(AdtId::RESULT, args)) => (Some(args[0].clone()), Some(args[1].clone())),
            _ => (None, None),
        };
        self.markers.push(Marker { handler: Some(e), errors: Vec::new(), target });
        self.in_chain = true;
        let ty = self.expr(inner, value_expected.as_ref());
        let errors = self.pop_marker();
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

    /// Whether a `todo` hole met one of `errors`, the error types of the calls a handler
    /// marks, which a chain may have settled before [`Checker::one_error`] joins them, as a
    /// receiver's type is (Q25).
    fn met_hole(&self, errors: &[Ty]) -> bool {
        errors.iter().any(|err| self.vars.from_hole(err))
    }

    /// Reports the `attempt` or `else` form at `span` if its calls fail with `Never`, which
    /// can't happen, once the statement settles `err` (OPEN_QUESTIONS P5, `fails Never`).
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
        let inherited = self.siblings.remove(&e);
        // The bindings of an `is` in the condition scope over the then-block (REFERENCE §6.4).
        let base = self.f.locals.len() as u32;
        self.f.scopes.push(Vec::new());
        self.condition(*cond);
        if inherited {
            self.mark_sibling(self.tail(then_block));
        }
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
        // So does a closure the then-block gives, which can't capture them (Q34).
        if let (Mode::Value(_), Some(tail)) = (mode, self.tail(then_block)) {
            self.local_capture(tail, base);
        }
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
                // A written function type is what each branch's closure must be (issue #61), and
                // the `if`'s type is still the join of both.
                let required = !inherited && self.requires_fn(expected);
                let from_then = !then_ty.is_unknown() && !required;
                let known = if from_then { Some(then_ty.clone()) } else { expected.cloned() };
                let expected = known.as_ref();
                if inherited || from_then {
                    self.mark_sibling(match branch {
                        ElseBranch::Block(block) => self.tail(block),
                        ElseBranch::If(nested) => Some(*nested),
                    });
                }
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
                    // Branches whose types don't match give the `if` no type (issue #55).
                    _ if self.mismatched_tail(self.tail(then_block)) || self.mismatched_tail(else_tail) => {
                        self.mismatched.insert(e);
                        Ty::Error
                    }
                    _ if required => self.join_branches(then_ty, else_ty, else_tail),
                    // The else-branch's type is the join, unless it has none of its own.
                    Some(known) if else_ty.is_unknown() => known.clone(),
                    _ => else_ty,
                }
            }
        };
        self.record(e, ty.clone());
        ty
    }

    /// The join of `known`, what earlier branches gave, and `ty`, what the branch `tail`
    /// gives, where both were checked against a written function type. A mismatch is reported
    /// at `tail`.
    fn join_branches(&mut self, known: Ty, ty: Ty, tail: Option<ExprId>) -> Ty {
        if ty.is_unknown() || diverges_ty(&ty) {
            return known;
        }
        if known.is_unknown() || diverges_ty(&known) {
            return ty;
        }
        self.vars.join(&known, &ty).unwrap_or_else(|| {
            let message = format!("expected `{}`, found `{}`", self.show(&known), self.show(&ty));
            let code = self.mismatch_code(&known, &ty);
            match tail {
                Some(tail) => {
                    self.mismatch(tail, code, self.span(tail), message);
                    self.mismatched.insert(tail);
                }
                None => self.vars.quiet(&known),
            }
            self.vars.poison(&ty);
            Ty::Error
        })
    }

    /// Checks `e`, a branch's value or a tuple's element, where the others give `known`,
    /// and returns the type of either: their join, where a `Never` part of `known` gives way
    /// (OPEN_QUESTIONS P5). A mismatch is reported at `e`.
    fn joined(&mut self, e: ExprId, known: &Ty) -> Ty {
        // Another branch's closure only guides this one's parameters, whose written types the
        // join meets (OPEN_QUESTIONS P3, decided for phase 3). A written type is required.
        self.sibling_closure = matches!(self.m.exprs[e].kind, ExprKind::Closure(_)) && self.siblings.remove(&e);
        let ty = self.expr(e, Some(known));
        if ty == Ty::Error {
            self.vars.quiet(known);
        }
        if diverges_ty(&ty) {
            return ty;
        }
        self.vars.join(known, &ty).unwrap_or_else(|| {
            let message = format!("expected `{}`, found `{}`", self.show(known), self.show(&ty));
            let code = self.mismatch_code(known, &ty);
            self.mismatch(e, code, self.span(e), message);
            self.vars.poison(&ty);
            self.vars.quiet(known);
            self.mismatched.insert(e);
            Ty::Error
        })
    }

    /// Whether `expected`, a branching expression's, is a function type that each branch must
    /// have, rather than one the branches' join decides.
    fn requires_fn(&self, expected: Option<&Ty>) -> bool {
        expected.is_some_and(|ty| matches!(self.vars.resolve(ty), Ty::Fn(..)))
    }

    /// Notes that `e`, if there is one, is expected to have the type another branch gave.
    fn mark_sibling(&mut self, e: Option<ExprId>) {
        self.siblings.extend(e);
    }

    /// Whether `tail`, the value a branch gives, has a type that didn't match the others'.
    fn mismatched_tail(&self, tail: Option<ExprId>) -> bool {
        tail.is_some_and(|tail| self.mismatched.contains(&tail))
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
        let text = self.m.text(sym);
        self.adt_names.get(&sym).copied().or_else(|| prelude_adt(text)).or_else(|| prelude_enum(text)).or_else(imported)
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
        // A variant with fields isn't a function value, so it takes its arguments, and a
        // closure can wrap it (OPEN_QUESTIONS P5).
        if !variant.fields.is_empty() && !variant.rejected {
            let ctor = def.ctor_name(v);
            let message = format!(
                "`{ctor}` has fields, so it is written with its arguments, as in `{ctor}(…)`; it isn't a function value"
            );
            self.error(codes::WRONG_ARGUMENT_COUNT, name.span, message);
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
        let counted = self.generic_args(&ctor, &params, &targs, args, span, Modes::Take);
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
        let mut mismatched = false;
        let mut leaves = Ty::Never;
        let mut tys = Vec::new();
        let mut sibling = self.siblings.remove(&e);
        // A written function type is what each arm's closure must be, and the arms still join.
        let required = !sibling && self.requires_fn(expected.as_ref());
        let mut joined = Ty::Never;
        for arm in arms {
            // An arm's bindings scope over its guard and body.
            let base = self.f.locals.len() as u32;
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
                    if sibling {
                        self.mark_sibling(self.tail(&arm.body));
                    }
                    let ty = self.block_value(&arm.body, expected.as_ref(), copying);
                    if required {
                        joined = self.join_branches(joined, ty.clone(), self.tail(&arm.body));
                    } else if !ty.is_unknown() {
                        expected = Some(ty.clone());
                        sibling = true;
                    }
                    mismatched |= self.mismatched_tail(self.tail(&arm.body));
                    // A closure the arm gives can't capture its bindings (Q34).
                    if let Some(tail) = self.tail(&arm.body) {
                        self.local_capture(tail, base);
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
            // Arms whose types don't match give the `match` no type (issue #55).
            Mode::Value(_) if mismatched => {
                self.mismatched.insert(e);
                Ty::Error
            }
            Mode::Value(_) if required && joined != Ty::Never => joined,
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
                let (mutable, what) = match (self.pattern_mutable, self.pattern_in_loop) {
                    (true, _) => (true, "variable"),
                    (false, true) => (false, "loop variable"),
                    (false, false) => (false, "binding"),
                };
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
        if let Ty::Adt(AdtId::SYSTEM, _) = ty {
            self.system_constructed(span, "matched by a pattern");
            return self.unknown_parts(fields);
        }
        // A pattern would read the `state` of an object that may change while the match runs.
        if let Ty::Adt(id, _) = ty
            && self.p.decls.adt(*id).cap
        {
            self.not_implemented(span, "patterns that match a `cap record`", Planned::Unscheduled);
            return self.unknown_parts(fields);
        }
        // A collection has no constructor to match, as a scalar has none (REFERENCE §6.4).
        let adt = match ty {
            Ty::Adt(id, targs) if !self.p.decls.adt(*id).is_native() => Some((id, targs)),
            _ => None,
        };
        let Some((id, targs)) = adt else {
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
            if self.aliases.contains_key(&q.sym) && !self.poisoned.contains(&q.sym) {
                self.alias_value(q);
                return self.unknown_parts(fields);
            }
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
                None if self.imports.contains_key(&q.sym)
                    || builtin_type(q_text).is_some()
                    || collection_adt(q_text).is_some()
                    || later_type(q_text).is_some() =>
                {
                    Some((
                        codes::TYPE_MISMATCH,
                        q.span,
                        format!("expected a pattern for `{}`, found one for `{q_text}`", self.p.decls.name(id)),
                    ))
                }
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
            AdtKind::Native => unreachable!("native types were rejected above"),
        };
        let Some(v) = found else {
            if self.poisoned.contains(&name.sym) {
            } else if qualifier.is_none() && self.aliases.contains_key(&name.sym) {
                self.alias_value(name);
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
        let targs = self.known_args(targs);
        let declared: Vec<(Box<str>, Ty)> =
            variant.fields.iter().map(|f| (f.name.clone(), f.ty.subst(&targs))).collect();
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
            // A pattern whose fields are only out of order still takes each one apart, so
            // what it binds and moves is known (§15.1; issue #46).
            let distinct = targets.iter().collect::<HashSet<_>>().len();
            if code == codes::WRONG_LABEL && targets.len() == fields.len() && distinct == targets.len() {
                self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: v, fields: targets.into() });
            }
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

    /// `for pat in iter`, over a range, a list's elements or a map's entries as `(k, v)`
    /// (REFERENCE §6.5). The pattern matches every element, as a `let` pattern does. A loop
    /// over a collection borrows the elements it binds (OPEN_QUESTIONS P5), and one that
    /// `consume`s it, `for pat in take xs`, owns them.
    fn for_loop(
        &mut self,
        e: ExprId,
        label: Option<Ident>,
        pat: PatId,
        iter: ExprId,
        consume: bool,
        body: &Block,
    ) -> Ty {
        let m = self.m;
        let span = self.span(iter);
        let (element, borrowed) = match m.exprs[iter].kind {
            ExprKind::Range { lo, hi, .. } if consume => {
                self.operands(lo, hi, None, span);
                let message =
                    "a consuming loop goes over a list or a map; a range has nothing to consume, so drop `take`";
                self.error(codes::TYPE_MISMATCH, span, message);
                self.record(iter, Ty::Error);
                (Ty::Error, false)
            }
            ExprKind::Range { lo, hi, .. } => {
                let ty = self.operands(lo, hi, None, span);
                let element = match self.force(&ty) {
                    Ty::Int(it) => Ty::Int(it),
                    ty if ty.is_unknown() => Ty::Error,
                    ty => {
                        let message = format!("a `for` range needs integer bounds, not `{}`", self.show(&ty));
                        self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                        Ty::Error
                    }
                };
                self.record(iter, element.clone());
                (element, false)
            }
            _ => {
                self.copying = consume;
                let ty = self.infer(iter);
                let element = match self.force(&ty) {
                    Ty::Adt(AdtId::LIST, args) => args[0].clone(),
                    Ty::Adt(AdtId::MAP, args) => self.p.decls.tuple_ty(args.to_vec()),
                    ty if ty.is_unknown() => Ty::Error,
                    ty => {
                        let message =
                            format!("expected a range, a list or a map to go over, found `{}`", self.show(&ty));
                        self.error(codes::TYPE_MISMATCH, span, message);
                        Ty::Error
                    }
                };
                (element, !consume)
            }
        };
        self.f.scopes.push(Vec::new());
        self.pattern_borrowed = borrowed;
        self.let_pattern(pat, &element, false, true);
        self.pattern_borrowed = false;
        self.loop_body(e, label, body);
        self.f.scopes.pop();
        Ty::Unit
    }
}

/// `ty` with each map whose key type doesn't implement `Eq` and `Hash` an error, where type
/// parameter `i` implements `bounds[i]`, and `unknown` may implement anything.
fn without_bad_keys(decls: &Decls, ty: &Ty, bounds: &[Vec<IfaceId>], unknown: &[Ty]) -> Ty {
    without_bad_keys_in(decls, ty, bounds, unknown, &mut HashMap::new()).unwrap_or_else(|| ty.clone())
}

/// [`without_bad_keys`], or `None` where nothing changes, so the type keeps its shared parts.
/// A type argument list in `seen`, by address, was looked at already, so a type that shares
/// its parts, as a doubling alias does, costs each part once (issue #55).
fn without_bad_keys_in(
    decls: &Decls,
    ty: &Ty,
    bounds: &[Vec<IfaceId>],
    unknown: &[Ty],
    seen: &mut HashMap<(AdtId, usize), Option<Ty>>,
) -> Option<Ty> {
    let Ty::Adt(id, args) = ty else { return None };
    if args.is_empty() {
        return None;
    }
    let key = (*id, Arc::as_ptr(args) as *const Ty as usize);
    if let Some(done) = seen.get(&key) {
        return done.clone();
    }
    let parts: Vec<Option<Ty>> =
        args.iter().map(|arg| without_bad_keys_in(decls, arg, bounds, unknown, seen)).collect();
    let changed = parts.iter().any(Option::is_some) || args.contains(&Ty::Error);
    let args: Vec<Ty> =
        parts.into_iter().zip(args.iter()).map(|(part, arg)| part.unwrap_or_else(|| arg.clone())).collect();
    let keyed = || {
        let key = &args[0];
        key.is_unknown()
            || unknown.contains(key)
            || decls.unknown_interfaces(key)
            || (!decls.is_resource(key)
                && [IfaceId::EQ, IfaceId::HASH].iter().all(|&iface| decls.implements(key, iface, bounds)))
    };
    let done = if *id == AdtId::MAP && !keyed() {
        Some(Ty::Error)
    } else if changed {
        Some(Ty::applied(*id, args))
    } else {
        None
    };
    seen.insert(key, done.clone());
    done
}

/// The parameter each argument of a call whose labels are wrong is checked against: the one
/// its label names, or its own or the first that no argument names when its label names
/// none. An argument whose label names a parameter an earlier one has gets none.
fn label_order<S: AsRef<str>>(m: &Module, args: &[Arg], params: &[(S, Ty)]) -> Vec<Option<usize>> {
    let named: Vec<Option<usize>> = args
        .iter()
        .map(|arg| arg.label.and_then(|label| params.iter().position(|(param, _)| param.as_ref() == m.text(label.sym))))
        .collect();
    let mut taken = vec![false; params.len()];
    let mut to: Vec<Option<usize>> = vec![None; args.len()];
    for (i, &j) in named.iter().enumerate() {
        if let Some(j) = j.filter(|&j| !taken[j]) {
            (to[i], taken[j]) = (Some(j), true);
        }
    }
    for i in 0..args.len() {
        if named[i].is_none() {
            let free = if taken[i] { taken.iter().position(|t| !t) } else { Some(i) };
            if let Some(j) = free {
                (to[i], taken[j]) = (Some(j), true);
            }
        }
    }
    to
}

/// Whether `ty` mentions one of the type parameters `targs` stands for. Each shared part is
/// walked once (issue #55).
/// Whether `ty` mentions type parameter `i`.
fn mentions_param(ty: &Ty, i: u32) -> bool {
    let mut found = Vec::new();
    params_in(ty, &mut found);
    found.contains(&i)
}

fn mentions_targ(ty: &Ty, targs: &[Ty]) -> bool {
    fn walk(ty: &Ty, targs: &[Ty], seen: &mut HashSet<usize>) -> bool {
        match ty {
            Ty::Param(i) => (*i as usize) < targs.len(),
            ty => ty.parts().is_some_and(|parts| {
                seen.insert(Arc::as_ptr(parts) as *const Ty as usize)
                    && parts.iter().any(|part| walk(part, targs, seen))
            }),
        }
    }
    walk(ty, targs, &mut HashSet::new())
}

/// Whether `ty` holds a function value where one can't be: in a record, enum, tuple or
/// collection, or in a function type's result or error (OPEN_QUESTIONS P5). A function
/// type's parameter may be a function. Each shared part is walked once.
fn holds_fn(ty: &Ty) -> bool {
    fn walk(ty: &Ty, inside: bool, seen: &mut HashSet<(usize, bool)>) -> bool {
        match ty {
            Ty::Fn(_, parts) => {
                inside
                    || (seen.insert((Arc::as_ptr(parts) as *const Ty as usize, false))
                        && (parts[..2].iter().any(|part| walk(part, true, seen))
                            || parts[FN_PARAMS..].iter().any(|part| walk(part, false, seen))))
            }
            Ty::Adt(_, args) => {
                seen.insert((Arc::as_ptr(args) as *const Ty as usize, true))
                    && args.iter().any(|arg| walk(arg, true, seen))
            }
            _ => false,
        }
    }
    walk(ty, false, &mut HashSet::new())
}

/// The code of a value of type `actual` where `expected` is required, when the two are built
/// alike and name the same capability interfaces, so they differ at most in permissions and
/// `uses`: E0603 when the value lacks a permission, which is reported first, and E0602 when
/// it reaches more than the expected type admits (REFERENCE §9.2, §9.4). A function type's
/// parameters compare the other way, and an `inout` one both ways, as do the whole types when
/// `exact`. `None` for any other mismatch. Each pair of shared parts is walked once in each direction, so types that double
/// at each level cost their depth (issue #55).
fn reach_mismatch(expected: &Ty, actual: &Ty, exact: bool) -> Option<Code> {
    #[derive(Default)]
    struct Walk {
        perms: bool,
        uses: bool,
        seen: HashSet<(usize, usize, bool)>,
    }
    impl Walk {
        fn parts(&mut self, xs: &Arc<[Ty]>, ys: &Arc<[Ty]>, flipped: bool, modes: &[ParamMode]) -> bool {
            let key = (Arc::as_ptr(xs) as *const Ty as usize, Arc::as_ptr(ys) as *const Ty as usize, flipped);
            if xs.len() != ys.len() || !self.seen.insert(key) {
                return xs.len() == ys.len();
            }
            xs.iter().zip(ys.iter()).enumerate().all(|(i, (x, y))| match i.checked_sub(FN_PARAMS) {
                Some(p) if !modes.is_empty() && modes[p].is_inout() => {
                    self.walk(x, y, flipped) && self.walk(x, y, !flipped)
                }
                Some(_) if !modes.is_empty() => self.walk(x, y, !flipped),
                _ => self.walk(x, y, flipped),
            })
        }

        fn walk(&mut self, expected: &Ty, actual: &Ty, flipped: bool) -> bool {
            let (want, have) = if flipped { (actual, expected) } else { (expected, actual) };
            match (expected, actual) {
                (Ty::Var(_), _) | (_, Ty::Var(_)) => true,
                (Ty::Cap(_), Ty::Cap(_)) => {
                    let (Ty::Cap(want), Ty::Cap(have)) = (want, have) else { unreachable!("both capabilities") };
                    self.perms |= !want.perms.is_subset(have.perms);
                    self.uses |= !have.uses.covered_by(&want.uses);
                    want.iface == have.iface
                }
                (Ty::Reach(_), Ty::Reach(_)) => {
                    let (Ty::Reach(want), Ty::Reach(have)) = (want, have) else { unreachable!("both reach sets") };
                    self.uses |= !have.covered_by(want);
                    true
                }
                (Ty::Adt(x, xs), Ty::Adt(y, ys)) => x == y && self.parts(xs, ys, flipped, &[]),
                (Ty::Fn(xm, xs), Ty::Fn(ym, ys)) => xm == ym && self.parts(xs, ys, flipped, xm),
                (a, b) => a == b,
            }
        }
    }
    let mut walk = Walk::default();
    if !walk.walk(expected, actual, false) || exact && !walk.walk(expected, actual, true) {
        return None;
    }
    if walk.perms {
        Some(codes::PERMISSION_NOT_GRANTED)
    } else if walk.uses {
        Some(codes::REACH_NOT_ADMITTED)
    } else {
        None
    }
}

/// Whether a value of this type may never be produced. An error counts, because the code it
/// stands for might diverge.
fn diverges_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Never | Ty::Error)
}

/// The operator a prelude operator interface stands for, which a distinct type may derive:
/// a binary one, or `None` for unary `-`. `None` for any other interface.
fn op_iface(iface: IfaceId) -> Option<Option<BinOp>> {
    Some(match iface {
        IfaceId::ADD => Some(BinOp::Add),
        IfaceId::SUB => Some(BinOp::Sub),
        IfaceId::MUL => Some(BinOp::Mul),
        IfaceId::DIV => Some(BinOp::Div),
        IfaceId::NEG => None,
        _ => return None,
    })
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

/// A built-in method's signature (STD.md).
struct BuiltinSig {
    builtin: Builtin,
    params: Vec<(&'static str, Ty)>,
    ret: Ty,
    fails: Option<Ty>,
    /// It takes its arguments (`take`), so passing a borrowed one copies it (REFERENCE §4.8).
    takes: bool,
    /// A type argument of the receiver's type that its `impl` block constrains, the
    /// interface it must implement, and the type parameter's name in STD.md.
    needs: Option<(Ty, IfaceId, &'static str)>,
}

/// The method `name` that values of `ty` have built in (STD.md).
fn builtin_method(ty: &Ty, name: &str) -> Option<BuiltinSig> {
    let sig = |builtin, params, ret| BuiltinSig { builtin, params, ret, fails: None, takes: false, needs: None };
    Some(match (ty, name) {
        (Ty::Text, "byte_len") => sig(Builtin::ByteLen, vec![], Ty::INT),
        (Ty::Text, "is_empty") => sig(Builtin::IsEmpty, vec![], Ty::Bool),
        (Ty::Text, "trim") => sig(Builtin::Trim, vec![], Ty::Text),
        (Ty::Text, "split_once") => {
            let pair = Ty::applied(AdtId::PAIR, vec![Ty::Text, Ty::Text]);
            sig(Builtin::SplitOnce, vec![("sep", Ty::Text)], Ty::option(pair))
        }
        (Ty::Text, "starts_with") => sig(Builtin::StartsWith, vec![("prefix", Ty::Text)], Ty::Bool),
        (Ty::Text, "strip_prefix") => sig(Builtin::StripPrefix, vec![("prefix", Ty::Text)], Ty::option(Ty::Text)),
        (Ty::Text, "lines") => sig(Builtin::Lines, vec![], Ty::list(Ty::Text)),
        (Ty::Float(_), "to_int") => BuiltinSig {
            fails: Some(Ty::adt(AdtId::CONVERSION_ERROR)),
            ..sig(Builtin::ToInt, vec![("rounding", Ty::adt(AdtId::ROUNDING))], Ty::INT)
        },
        (Ty::Adt(AdtId::LIST, args), _) => {
            let t = args[0].clone();
            match name {
                "len" => sig(Builtin::Len, vec![], Ty::INT),
                "is_empty" => sig(Builtin::IsEmpty, vec![], Ty::Bool),
                "push" => BuiltinSig { takes: true, ..sig(Builtin::Push, vec![("value", t)], Ty::Unit) },
                "pop" => sig(Builtin::Pop, vec![], Ty::option(t)),
                "get" => BuiltinSig {
                    needs: Some((t.clone(), IfaceId::COPY, "T")),
                    ..sig(Builtin::Get, vec![("index", Ty::INT)], Ty::option(t))
                },
                "enumerate" => {
                    let pair = Ty::applied(AdtId::PAIR, vec![Ty::INT, t.clone()]);
                    BuiltinSig {
                        needs: Some((t, IfaceId::COPY, "T")),
                        ..sig(Builtin::Enumerate, vec![], Ty::list(pair))
                    }
                }
                "contains" => BuiltinSig {
                    needs: Some((t.clone(), IfaceId::EQ, "T")),
                    ..sig(Builtin::Contains, vec![("value", t)], Ty::Bool)
                },
                _ => return None,
            }
        }
        (Ty::Adt(AdtId::MAP, args), _) => {
            let (k, v) = (args[0].clone(), args[1].clone());
            match name {
                "len" => sig(Builtin::Len, vec![], Ty::INT),
                "is_empty" => sig(Builtin::IsEmpty, vec![], Ty::Bool),
                "contains_key" => sig(Builtin::ContainsKey, vec![("key", k)], Ty::Bool),
                "set" => BuiltinSig {
                    takes: true,
                    ..sig(Builtin::Set, vec![("key", k), ("value", v.clone())], Ty::option(v))
                },
                "remove" => sig(Builtin::Remove, vec![("key", k)], Ty::option(v)),
                "get" => BuiltinSig {
                    needs: Some((v.clone(), IfaceId::COPY, "V")),
                    ..sig(Builtin::Get, vec![("key", k)], Ty::option(v))
                },
                _ => return None,
            }
        }
        (Ty::Adt(AdtId::POOL, args), _) => {
            let t = args[0].clone();
            let handle = Ty::applied(AdtId::HANDLE, vec![t.clone()]);
            match name {
                "len" => sig(Builtin::Len, vec![], Ty::INT),
                "insert" => BuiltinSig { takes: true, ..sig(Builtin::Insert, vec![("value", t)], handle) },
                "remove" => sig(Builtin::Remove, vec![("handle", handle)], Ty::option(t)),
                "get" => BuiltinSig {
                    needs: Some((t.clone(), IfaceId::COPY, "T")),
                    ..sig(Builtin::Get, vec![("handle", handle)], Ty::option(t))
                },
                "duplicate" => BuiltinSig {
                    needs: Some((t.clone(), IfaceId::COPY, "T")),
                    ..sig(Builtin::Duplicate, vec![], Ty::applied(AdtId::POOL, vec![t]))
                },
                "update" => {
                    let change = Ty::func(vec![ParamMode::Take], vec![t.clone()], t, Ty::Never);
                    sig(Builtin::Update, vec![("handle", handle), ("change", change)], Ty::Bool)
                }
                _ => return None,
            }
        }
        _ => return None,
    })
}

/// The methods of a list or map that later phases bring, with what to call them and when.
fn later_collection_method(name: &str) -> Option<(&'static str, Planned)> {
    Some(match name {
        "map" | "filter" => ("operations that take a closure", Planned::Phase(3)),
        // STD.md declares none of them.
        "is_sorted" | "is_permutation_of" | "is_unique" => ("the predicates of §8.1", Planned::Unscheduled),
        // `replace` returns a resource it would otherwise discard (REFERENCE §10 rule 5), but
        // STD.md doesn't declare it yet.
        "replace" => ("list operations that STD.md doesn't declare, such as `replace`,", Planned::Unscheduled),
        "swap" | "sort" => ("collection operations that STD.md doesn't declare", Planned::Unscheduled),
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
/// The interfaces a record or enum derives, or with `distinct`, a distinct type (REFERENCE
/// §4.4, §4.6).
fn derivable(distinct: bool) -> &'static str {
    if distinct {
        "`Eq`, `Ord`, `Hash` and `Show`, and on a distinct type `Add`, `Sub`, `Mul`, `Div` and `Neg`"
    } else {
        "`Eq`, `Ord`, `Hash` and `Show`"
    }
}

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

/// `Ordering` and `Rounding`, the prelude's enums without type parameters (STD.md).
fn prelude_enum(name: &str) -> Option<AdtId> {
    match name {
        "Ordering" => Some(AdtId::ORDERING),
        "Rounding" => Some(AdtId::ROUNDING),
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
    match name {
        "Result" => "Result[T, E]",
        "List" => "List[T]",
        "Map" => "Map[K, V]",
        "Pool" => "Pool[T]",
        "Handle" => "Handle[T]",
        _ => "Option[T]",
    }
}

/// `List` and `Map`, the prelude's collections (STD.md).
fn collection_adt(name: &str) -> Option<AdtId> {
    match name {
        "List" => Some(AdtId::LIST),
        "Map" => Some(AdtId::MAP),
        _ => None,
    }
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
        || prelude_enum(name).is_some()
        || collection_adt(name).is_some()
        || bare_variant(name).is_some()
        || later_type(name).is_some()
        || IfaceId::prelude(name).is_some()
}

/// The types of `System`'s fields that no module exports yet, so a program can't name them,
/// though a module may declare its own (REFERENCE §9.1; OPEN_QUESTIONS P5).
fn unexported_type(name: &str) -> Option<Planned> {
    matches!(name, "Net" | "Clock" | "Random" | "Env" | "Process").then_some(Planned::Unscheduled)
}

/// Prelude types that later phases implement.
fn later_type(name: &str) -> Option<Planned> {
    match name {
        // Nothing builds an `Array` or `Bytes` yet, and the validators that report `Invalid`
        // come with the verifier (OPEN_QUESTIONS P3).
        "Array" | "Bytes" => Some(Planned::Unscheduled),
        "Invalid" => Some(Planned::Phase(5)),
        // Nothing builds a `Set` yet (OPEN_QUESTIONS Q37).
        "Set" => Some(Planned::Unscheduled),
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

/// How deeply the type of an expression may nest, counting each type argument as a level
/// (OPEN_QUESTIONS P5, Nesting limit). `let`s that each wrap the one before nest a type
/// deeper than any expression, as `collections/deep` does 3,000 levels. A debug build drops
/// a type 10,000 deep on the main thread's 8 MiB stack, so this keeps half of that.
pub const MAX_TYPE_DEPTH: u32 = 5_000;

/// Whether `ty` has an error in it.
fn mentions_error(ty: &Ty) -> bool {
    *ty == Ty::Error || ty.parts().is_some_and(|parts| parts.iter().any(mentions_error))
}

/// Pushes the index of each type parameter `ty` mentions to `found`, once each.
fn params_in(ty: &Ty, found: &mut Vec<u32>) {
    match ty {
        Ty::Param(i) if !found.contains(i) => found.push(*i),
        ty => {
            for part in ty.parts().into_iter().flat_map(|parts| parts.iter()) {
                params_in(part, found);
            }
        }
    }
}

/// The strongly connected components of the graph whose node `i` has an edge to each
/// target in `edges[i]`, by Tarjan's algorithm with an explicit stack, so a long chain of
/// types can't overflow the native one.
fn strongly_connected<E>(edges: &[Vec<(usize, bool, E)>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let (mut index, mut low, mut on_stack) = (vec![usize::MAX; n], vec![0; n], vec![false; n]);
    let (mut next, mut stack, mut components) = (0, Vec::new(), Vec::new());
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // Each frame is a node and how many of its edges it has followed.
        let mut frames = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (node, ref mut edge)) = frames.last_mut() {
            if let Some(&(to, ..)) = edges[node].get(*edge) {
                *edge += 1;
                if index[to] == usize::MAX {
                    index[to] = next;
                    low[to] = next;
                    next += 1;
                    stack.push(to);
                    on_stack[to] = true;
                    frames.push((to, 0));
                } else if on_stack[to] {
                    low[node] = low[node].min(index[to]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                low[parent] = low[parent].min(low[node]);
            }
            if low[node] == index[node] {
                let mut component = Vec::new();
                while let Some(top) = stack.pop() {
                    on_stack[top] = false;
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                components.push(component);
            }
        }
    }
    components
}

/// Whether two `impl` targets are the same up to the names of their blocks' type parameters,
/// as `Pair[A, B]` in `impl[A, B]` and in `impl[B, A]` are.
fn same_target(a: &Ty, b: &Ty) -> bool {
    fn walk(a: &Ty, b: &Ty, pairs: &mut Vec<(u32, u32)>) -> bool {
        match (a, b) {
            (Ty::Param(x), Ty::Param(y)) => match pairs.iter().find(|(p, q)| p == x || q == y) {
                Some(pair) => *pair == (*x, *y),
                None => {
                    pairs.push((*x, *y));
                    true
                }
            },
            (Ty::Adt(x, xs), Ty::Adt(y, ys)) => {
                x == y && xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(a, b)| walk(a, b, pairs))
            }
            (a, b) => a == b,
        }
    }
    walk(a, b, &mut Vec::new())
}
