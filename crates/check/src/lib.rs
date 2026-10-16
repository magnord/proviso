//! Name resolution and type checking for the phase-1 subset (scalar types, functions,
//! control flow, `fails` and `try`, and the prelude's `System` with only `stdout`), for
//! records, for enums, `match` and patterns, for `Option`, `Result`, `fail` and `attempt`,
//! and for methods, interfaces and generic functions.
//!
//! The checker never rewrites the tree. It records what it learns in side tables of
//! [`Program`], which the interpreter reads.

pub mod decls;
pub mod exhaust;
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
    pub let_local: SideTable<Stmt, LocalId>,
    /// The local each binding pattern binds.
    pub pat_local: SideTable<Pat, LocalId>,
    /// What each constructor pattern matches.
    pub pat_ctor: SideTable<Pat, CtorPat>,
    pub for_local: SideTable<Expr, LocalId>,
    /// The loop each `break` or `continue` leaves.
    pub jump_target: SideTable<Stmt, ExprId>,
    /// The `attempt` that marks each fallible call it covers, which reifies the call's
    /// failure as an `Err` (REFERENCE §7.2).
    pub attempt_of: SideTable<Expr, ExprId>,
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
    checker.p
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
    /// False in a refinement, which is an expression with no function to return from.
    returns: bool,
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
            bounds: Vec::new(),
            anonymous: Vec::new(),
        }
    }
}

/// An enclosing `try` or `attempt`, and the error types of the fallible calls it marks.
struct Marker {
    /// The `attempt`, or `None` for a `try`.
    attempt: Option<ExprId>,
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

    /// How diagnostics write `ty`.
    fn show<'s>(&'s self, ty: &'s Ty) -> impl std::fmt::Display + 's {
        self.p.decls.display_in(ty, &self.param_names)
    }

    /// Whether `ty` implements `iface`, where a type parameter implements its constraints.
    fn implements(&self, ty: &Ty, iface: IfaceId) -> bool {
        self.p.decls.implements(ty, iface, &self.f.bounds) || self.unknown_tys.contains(ty)
    }

    /// Whether a rejected declaration may have given `ty` interfaces that nothing records.
    fn unknown_interfaces(&self, ty: &Ty) -> bool {
        self.p.decls.unknown_interfaces(ty) || self.unknown_tys.contains(ty)
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
            ItemKind::Impl(_) => vec![],
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
                        preds.push(Pred { expr, field: Some(FieldIdx(i as u32)) });
                    }
                }
                if let Some(expr) = self.adts[k].refinement {
                    let all = kept.iter().enumerate().map(|(i, f)| (f.name.sym, LocalId(i as u32)));
                    self.f.scopes = vec![all.collect()];
                    self.check(expr, &Ty::Bool);
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
        self.p.fns[id].locals = self.f.locals.len();
        self.generic_scope.clear();
        self.param_names.clear();
        self.self_ty = None;
    }

    fn fn_body(&mut self, decl: &FnDecl, body: &Block) {
        let m = self.m;
        let ret = self.f.ret.clone();
        self.f.scopes.push(Vec::new());
        let diverges = if ret == Ty::Unit {
            body.stmts.iter().fold(false, |diverges, &s| self.stmt(s) | diverges)
        } else {
            self.tail_stmts(body, &ret)
        };
        self.f.scopes.pop();
        // A body that needed parse recovery has unknown control flow.
        if ret != Ty::Unit && ret != Ty::Error && !diverges && !decl.recovered {
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
    /// statements always diverge, counting such a value as a return.
    fn tail_stmts(&mut self, block: &Block, ret: &Ty) -> bool {
        let m = self.m;
        let mut diverges = false;
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
                    return true;
                }
                match m.exprs[e].kind {
                    ExprKind::If { .. } => return diverges | diverges_ty(&self.if_expr(e, Mode::Tail(ret))),
                    ExprKind::Match { .. } => return diverges | diverges_ty(&self.match_expr(e, Mode::Tail(ret))),
                    _ => {}
                }
            }
            diverges |= self.stmt(s);
        }
        diverges
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

    /// Checks a statement and returns whether it always diverges.
    fn stmt(&mut self, s: StmtId) -> bool {
        let m = self.m;
        let stmt = &m.stmts[s];
        match &stmt.kind {
            StmtKind::Let { mutable, name, ty, init } => {
                let declared = ty.map(|t| self.resolve_type(t));
                // Binding a value to a new name copies it (REFERENCE §4.8).
                self.copying = true;
                let (ty, init_ty) = match declared {
                    Some(declared) => {
                        let init_ty = self.check(*init, &declared);
                        (declared, init_ty)
                    }
                    None => {
                        let ty = self.infer(*init);
                        (ty.clone(), ty)
                    }
                };
                let what = if *mutable { "variable" } else { "binding" };
                let id = self.declare(*name, ty, *mutable, what, false);
                self.p.let_local.insert(s, id);
                diverges_ty(&init_ty)
            }
            StmtKind::Assign { target, op, value } => diverges_ty(&self.assign(*target, *op, *value)),
            StmtKind::Expr(e) => diverges_ty(&self.expr_stmt(*e)),
            StmtKind::Return(value) if !self.f.returns => {
                if let Some(value) = value {
                    self.infer(*value);
                }
                self.error(
                    codes::MISPLACED_RETURN,
                    stmt.span,
                    "`return` outside a function body; a `where` clause is an expression",
                );
                true
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
            StmtKind::Assert(cond) => diverges_ty(&self.check(*cond, &Ty::Bool)),
        }
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
        self.p.expr_ty.insert(target, ty.clone());
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
        )
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
    fn block_stmt(&mut self, block: &Block, tail: Option<&Ty>) -> Ty {
        self.f.scopes.push(Vec::new());
        let diverges = match tail {
            Some(ret) => self.tail_stmts(block, ret),
            None => block.stmts.iter().fold(false, |diverges, &s| self.stmt(s) | diverges),
        };
        self.f.scopes.pop();
        if diverges { Ty::Never } else { Ty::Unit }
    }

    /// Checks a block used for its value: the final expression, if there is one, which is
    /// copied when `copying` says so.
    fn block_value(&mut self, block: &Block, expected: Option<&Ty>, copying: bool) -> Ty {
        let m = self.m;
        self.f.scopes.push(Vec::new());
        let mut diverges = false;
        let mut value = None;
        let count = block.stmts.len();
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == count
                && let StmtKind::Expr(e) = m.stmts[s].kind
            {
                self.copying = copying;
                let ty = match expected {
                    Some(expected) => self.check(e, expected),
                    None => self.infer(e),
                };
                diverges |= diverges_ty(&ty);
                value = Some(ty);
                continue;
            }
            diverges |= self.stmt(s);
        }
        self.f.scopes.pop();
        if diverges {
            return Ty::Never;
        }
        // Its value may have come from the code that is missing.
        if block.unclosed {
            return Ty::Error;
        }
        match (value, expected) {
            (Some(ty), _) => ty,
            (None, Some(expected)) if *expected != Ty::Unit && *expected != Ty::Error => {
                self.error(
                    codes::TYPE_MISMATCH,
                    block.span.end(),
                    format!("expected a value of type `{}`, but this block ends without one", self.show(expected)),
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
    fn check(&mut self, e: ExprId, expected: &Ty) -> Ty {
        let actual = self.expr(e, Some(expected));
        if !expected.accepts(&actual) {
            let span = self.span(e);
            let message = format!("expected `{}`, found `{}`", self.show(expected), self.show(&actual));
            self.error(codes::TYPE_MISMATCH, span, message);
        }
        actual
    }

    /// Infers the type of `e`. `expected` guides literals and `if` branches, but mismatches
    /// against it are reported by [`Checker::check`].
    fn expr(&mut self, e: ExprId, expected: Option<&Ty>) -> Ty {
        let chain = std::mem::replace(&mut self.in_chain, false);
        let copying = std::mem::replace(&mut self.copying, false);
        let ty = self.expr_kind(e, expected, chain, copying);
        if copying {
            self.copied(e, &ty);
        }
        self.p.expr_ty.insert(e, ty.clone());
        ty
    }

    /// Reports a copy of a borrowed value whose type has a type parameter that isn't `Copy`,
    /// such as `x` or `o` in `return x` or `let y = o` (REFERENCE §4.8).
    fn copied(&mut self, e: ExprId, ty: &Ty) {
        // Only a generic function's types mention type parameters, and the borrowed place is
        // the cheap test, so a deep type is walked only where it can matter.
        if self.f.bounds.is_empty() || !self.borrowed_place(e) {
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

    fn expr_kind(&mut self, e: ExprId, expected: Option<&Ty>, chain: bool, copying: bool) -> Ty {
        let m = self.m;
        let span = self.span(e);
        match &m.exprs[e].kind {
            ExprKind::Int(value) => self.int_literal(*value, false, expected, span),
            ExprKind::Float(text) => {
                let ft = match expected {
                    Some(Ty::Float(ft)) => *ft,
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
                        self.infer(*value);
                        let message = if self.f.returns {
                            "`fail` needs a `fails` clause, and this function declares none"
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

    fn int_literal(&mut self, magnitude: u128, negative: bool, expected: Option<&Ty>, span: Span) -> Ty {
        let it = match expected {
            Some(Ty::Int(it)) => *it,
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

    fn negate(&mut self, operand: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        // A negative integer literal is one value, so `-128` fits in `Int8`.
        if let ExprKind::Int(value) = self.m.exprs[operand].kind {
            let ty = self.int_literal(value, true, expected, span);
            self.p.expr_ty.insert(operand, ty.clone());
            return ty;
        }
        let ty = self.expr(operand, expected.filter(|t| t.is_numeric()));
        match ty {
            Ty::Int(it) if it.is_signed() => ty,
            Ty::Float(_) | Ty::Error | Ty::Never => ty,
            // A rejected `impl` block may have been the type's `impl Neg` (§15.1).
            _ if self.unknown_interfaces(&ty) => Ty::Error,
            _ => {
                let message = format!("unary `-` is not defined for `{}`", self.show(&ty));
                self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                Ty::Error
            }
        }
    }

    /// Checks the operands of a binary operator. An untyped literal takes its type from the
    /// other operand (REFERENCE §2), so the non-literal side is checked first.
    fn operands(&mut self, lhs: ExprId, rhs: ExprId, hint: Option<&Ty>) -> (Ty, Ty) {
        // An operand that already has an error gives the other no type, so a literal there
        // isn't reported again against the hint.
        // `Some(1)` and `None` also take their type arguments from the other operand.
        let numeric_or = |ty: &Ty| match ty {
            Ty::Error => None,
            ty if ty.is_numeric() || matches!(ty, Ty::Adt(..)) => Some(ty.clone()),
            _ => hint.cloned(),
        };
        // The operand that says more about its own type goes first, so `None == Some(1)` and
        // `Some(1) == Some(small)` check as their swapped forms do.
        if self.context_rank(lhs) > self.context_rank(rhs) {
            let rt = self.expr(rhs, hint);
            let lt = self.expr(lhs, numeric_or(&rt).as_ref());
            (lt, rt)
        } else {
            let lt = self.expr(lhs, hint);
            let rt = self.expr(rhs, numeric_or(&lt).as_ref());
            (lt, rt)
        }
    }

    /// How little an argument or operand says about its own type, so that one that says more
    /// is checked first and gives the others theirs, in any position (OPEN_QUESTIONS P5). 0
    /// needs no context. 1 is a variant or call with such a part, as `Some(x)` is. 2 has only
    /// a literal's type, as `1` and `Some(1)` do. 3 says nothing, as `None`, `nothing()` and
    /// `id(None)` do.
    fn context_rank(&self, e: ExprId) -> u8 {
        if !self.needs_context(e) {
            return 0;
        }
        if self.is_untyped_literal(e) {
            return 2;
        }
        match &self.m.exprs[e].kind {
            ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. } => {
                args.iter().map(|arg| self.context_rank(arg.value)).min().map_or(3, |rank| rank.max(1))
            }
            _ => 3,
        }
    }

    /// A literal, a variant of `Option` or `Result`, or a call of a generic function whose
    /// result type only its context can give, as in `id(1)` or `nothing()`, whose type comes
    /// from its context when it has one (OPEN_QUESTIONS P5).
    fn needs_context(&self, e: ExprId) -> bool {
        let m = self.m;
        let prelude_variant =
            |name: Ident| bare_variant(m.text(name.sym)).is_some() && self.lookup_local(name.sym).is_none();
        let prelude_enum = |base: ExprId| match m.exprs[base].kind {
            ExprKind::Name(name) => prelude_adt(m.text(name.sym)).is_some() && !self.poisoned.contains(&name.sym),
            _ => false,
        };
        match &m.exprs[e].kind {
            ExprKind::Name(name) => prelude_variant(*name),
            ExprKind::Call { callee, targs: None, args } if let Some(f) = self.fn_named(*callee) => {
                let info = &self.p.fns[f];
                !info.generics.is_empty()
                    && mentions_param(&info.ret)
                    && args.iter().all(|arg| self.needs_context(arg.value))
            }
            ExprKind::Call { callee, .. } => {
                matches!(m.exprs[*callee].kind, ExprKind::Name(name) if prelude_variant(name))
            }
            ExprKind::Field { base, .. } | ExprKind::MethodCall { receiver: base, .. } => prelude_enum(*base),
            _ => self.is_untyped_literal(e),
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

    /// The type both operands have, where `Never` gives way to the other side, also as a
    /// type argument, so `Some(fail e) == Some(1)` compares `Option[Int]`s.
    fn unify_operands(&mut self, lt: Ty, rt: Ty, span: Span) -> Ty {
        match lt.join(&rt) {
            Some(ty) => ty,
            None => {
                let message = format!(
                    "mismatched operand types `{}` and `{}`; Proviso has no implicit conversions",
                    self.show(&lt),
                    self.show(&rt)
                );
                self.error(codes::TYPE_MISMATCH, span, message);
                Ty::Error
            }
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
                let (lt, rt) = self.operands(lhs, rhs, expected.filter(|t| t.is_numeric()));
                let ty = self.unify_operands(lt, rt, span);
                // A rejected `impl` block may have been the type's `impl Add` (§15.1).
                if !arithmetic_defined(op, &ty) && !self.unknown_interfaces(&ty) {
                    let message = format!("`{symbol}` is not defined for `{}`", self.show(&ty));
                    self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                    return Ty::Error;
                }
                ty
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (lt, rt) = self.operands(lhs, rhs, None);
                let ty = self.unify_operands(lt, rt, span);
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
                for arg in args {
                    self.infer(arg.value);
                }
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
                for arg in args {
                    self.infer(arg.value);
                }
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
        for arg in args {
            self.infer(arg.value);
        }
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
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        }
        let name = m.text(info.name);
        let params: Vec<(&str, Ty)> = info.params.iter().map(|p| (m.text(p.name), p.ty.clone())).collect();
        let (ret, fails) = (info.ret.clone(), info.fails.clone());
        let generics: Vec<(Box<str>, Vec<IfaceId>)> =
            info.generics.iter().map(|g| (g.name.clone(), g.bounds.clone())).collect();
        // A parameter whose declaration or constraint is rejected stands for an unknown type.
        let mut tvars: Vec<Option<Ty>> = info.generics.iter().map(|g| g.rejected.then_some(Ty::Error)).collect();
        // `::[…]` gives the declared parameters, which come before those of interface types.
        let declared = info.generics.iter().filter(|g| g.param.is_none()).count();
        // A parameter declared twice may have been meant as one, so a count without it is
        // also right.
        let duplicates = info.generics.iter().filter(|g| g.sym.is_none() && g.param.is_none()).count();
        let mut fixed = vec![false; tvars.len()];
        match targs {
            Some(targs) => {
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
                    for arg in args {
                        self.infer(arg.value);
                    }
                    return Ty::Error;
                } else {
                    for ((slot, fixed), ty) in tvars.iter_mut().zip(&mut fixed).zip(tys) {
                        *fixed = true;
                        slot.get_or_insert(ty);
                    }
                }
            }
            None => {
                if let Some(expected) = expected.filter(|t| !t.is_unknown() && !t.has_never_arg()) {
                    unify(&ret, expected, &mut tvars);
                }
            }
        }
        let counted = self.generic_args(name, &params, &mut tvars, &fixed, args, span, false);
        // An expected type with an error may have given them (§15.1).
        if expected == Some(&Ty::Error) {
            for slot in tvars.iter_mut().filter(|slot| slot.is_none()) {
                *slot = Some(Ty::Error);
            }
        }
        let Some(tvars) = tvars.iter().cloned().collect::<Option<Vec<Ty>>>() else {
            if counted {
                let missing: Vec<String> = (tvars.iter().zip(&generics))
                    .filter(|(t, _)| t.is_none())
                    .map(|(_, (param, _))| format!("`{param}`"))
                    .collect();
                let noun = if missing.len() == 1 { "type argument" } else { "type arguments" };
                let message = format!(
                    "the {noun} {} of `{name}` can't be inferred; give the binding a type, or write `{name}::[…](…)`",
                    missing.join(", ")
                );
                self.error(codes::CANNOT_INFER, span, message);
            }
            return Ty::Error;
        };
        for (ty, (param, bounds)) in tvars.iter().zip(&generics) {
            if ty.is_unknown() {
                continue;
            }
            if let Some(&iface) = bounds.iter().find(|&&iface| !self.implements(ty, iface)) {
                let message = format!(
                    "`{}` does not implement `{}`, which `{name}` needs of `{param}`",
                    self.show(ty),
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
        self.generic_args(&name, &params, &mut [], &[], args, span, true);
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
            let cap = self.names_cap(receiver_name.sym);
            if cap {
                let what = "calls of capability interface methods such as `Out.write_line(…)`";
                self.not_implemented(receiver_name.span, what, Planned::Phase(3));
            }
            // A rejected declaration may have had the name.
            if cap || self.poisoned.contains(&receiver_name.sym) {
                for arg in args {
                    self.infer(arg.value);
                }
                return Ty::Error;
            }
        }
        self.in_chain = chain;
        let receiver_ty = self.infer(receiver);
        if let (Ty::Adt(id, _), "with") = (&receiver_ty, name)
            && !self.p.decls.adt(*id).is_enum()
        {
            self.no_targs(targs, name, span);
            self.p.res.insert(e, Res::With);
            self.with_args(e, *id, args, span);
            return receiver_ty;
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
                for arg in args {
                    self.infer(arg.value);
                }
                Ty::Error
            }
        }
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
        for arg in args {
            self.infer(arg.value);
        }
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
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        };
        if let Some(label) = first.label {
            let message = format!("the receiver of `{iface_text}.{name}` takes no label (H3)");
            self.error(codes::WRONG_LABEL, label.span, message);
        }
        let receiver_ty = self.infer(first.value);
        if !receiver_ty.is_unknown() && !self.implements(&receiver_ty, iface) {
            let message = format!("`{}` does not implement `{iface_text}`", self.show(&receiver_ty));
            let at = self.span(first.value);
            self.error(codes::MISSING_IMPLEMENTATION, at, message);
            for arg in rest {
                self.infer(arg.value);
            }
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
                    self.infer(arg.value);
                }
            }
        }
        if !labels_reported {
            self.p.with_fields.insert(e, replaced.into());
        }
    }

    /// Checks arguments against parameters, including the label rules (REFERENCE §3, H3).
    fn args<S: AsRef<str>>(&mut self, callee: &str, params: &[(S, Ty)], args: &[Arg], span: Span) {
        self.generic_args(callee, params, &mut [], &[], args, span, false);
    }

    /// Checks arguments against parameters whose types may mention the type parameters
    /// `targs` stands for, of which `::[…]` gave those `fixed` marks. An argument whose
    /// parameter mentions a type parameter not yet known gives it the part of its own type
    /// in that place. A construction, which stores its arguments, `copy`s them. Returns
    /// whether the number of arguments was right.
    #[allow(clippy::too_many_arguments)]
    fn generic_args<S: AsRef<str>>(
        &mut self,
        callee: &str,
        params: &[(S, Ty)],
        targs: &mut [Option<Ty>],
        fixed: &[bool],
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
            for arg in args {
                self.infer(arg.value);
            }
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
        // Arguments that say more about their type go first, so that a literal or a `None`
        // takes the type the others give, in any position (OPEN_QUESTIONS P5).
        let mut order: Vec<usize> = (0..args.len()).collect();
        if targs.iter().any(Option::is_none) && args.len() > 1 {
            order.sort_by_key(|&i| self.context_rank(args[i].value));
        }
        for i in order {
            let (arg, ty) = (&args[i], &params[i].1);
            self.copying = copy;
            // A type parameter that `targs` doesn't cover is the caller's own, such as the `T`
            // that `Self` stands for in `x.bigger(y)` where `x: T`, so it is a type like any.
            if !mentions_targ(ty, targs) {
                self.check(arg.value, ty);
                continue;
            }
            // A type argument not known yet is `Never` in the expected type, which the argument
            // widens, as a field widens a `Never` the expected type gives, so `Ok(1)` meets a
            // `Result[T, Text]` and `Some(1)` widens an `Option[Never]` (OPEN_QUESTIONS P5). An
            // expected type that says nothing more is left out, so `None` alone gives no `T`.
            let open: Vec<Ty> = targs.iter().map(|t| t.clone().unwrap_or(Ty::Never)).collect();
            let expected = ty.subst(&open);
            let informative = expected != Ty::Never && says_more(ty, targs);
            let actual = self.expr(arg.value, informative.then_some(&expected));
            infer_targs(ty, &actual, targs, fixed);
            let known: Vec<Ty> = targs.iter().map(|t| t.clone().unwrap_or(Ty::Error)).collect();
            let expected = ty.subst(&known);
            if !expected.accepts(&actual) {
                let span = self.span(arg.value);
                let message = format!("expected `{}`, found `{}`", self.show(&expected), self.show(&actual));
                self.error(codes::TYPE_MISMATCH, span, message);
            }
        }
        true
    }

    fn fallible_call(&mut self, call: ExprId, callee: &str, err: &Ty, span: Span, chain: bool) {
        match self.markers.last_mut() {
            Some(marker) if chain => {
                marker.errors.push(err.clone());
                if let Some(attempt) = marker.attempt {
                    self.p.attempt_of.insert(call, attempt);
                }
            }
            _ => {
                let message = format!(
                    "`{callee}` can fail with `{}`, so the call must be marked, for example with `try` (§7.2)",
                    self.show(err)
                );
                self.error(codes::UNMARKED_FALLIBLE_CALL, span, message);
            }
        }
    }

    fn try_expr(&mut self, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        self.markers.push(Marker { attempt: None, errors: Vec::new() });
        self.in_chain = true;
        let ty = self.expr(inner, expected);
        let mut errors = self.markers.pop().map(|m| m.errors).unwrap_or_default();
        errors.dedup();
        // A chain with an error may hold the fallible call that didn't resolve.
        if errors.is_empty() && ty != Ty::Error {
            self.error(codes::TRY_WITHOUT_FAILURE, span, "`try` marks no call that can fail");
        }
        for err in errors {
            let message = match &self.f.fails {
                None => {
                    let err = self.show(&err);
                    format!("`try` propagates `{err}`, but this function does not declare `fails {err}`")
                }
                Some(own) if *own != err && *own != Ty::Error && err != Ty::Error => format!(
                    "`try` needs equal error types, but the call fails with `{}` and this function fails with `{}`",
                    self.show(&err),
                    self.show(own)
                ),
                Some(_) => continue,
            };
            self.error(codes::TRY_ERROR_MISMATCH, span, message);
        }
        ty
    }

    /// `attempt f(…)`: a `Result` of the chain's value and the error of the calls it marks
    /// (REFERENCE §7.2).
    fn attempt_expr(&mut self, e: ExprId, inner: ExprId, expected: Option<&Ty>, span: Span) -> Ty {
        let value_expected = match expected {
            Some(Ty::Adt(AdtId::RESULT, args)) => Some(args[0].clone()),
            _ => None,
        };
        self.markers.push(Marker { attempt: Some(e), errors: Vec::new() });
        self.in_chain = true;
        let ty = self.expr(inner, value_expected.as_ref());
        let mut errors: Vec<Ty> = Vec::new();
        for err in self.markers.pop().map(|m| m.errors).unwrap_or_default() {
            if !errors.contains(&err) {
                errors.push(err);
            }
        }
        match errors.as_slice() {
            // A chain with an error may hold the fallible call that didn't resolve.
            [] => {
                if ty != Ty::Error {
                    self.error(codes::ATTEMPT_WITHOUT_FAILURE, span, "`attempt` marks no call that can fail");
                }
                Ty::Error
            }
            [err] => Ty::result(ty, err.clone()),
            _ if errors.contains(&Ty::Error) => Ty::Error,
            // Calls with errors of their own need methods, which come in a later slice.
            [first, second, ..] => {
                let message = format!(
                    "the calls this `attempt` marks fail with `{}` and `{}`, but its `Result` has one error type",
                    self.show(first),
                    self.show(second)
                );
                self.error(codes::TYPE_MISMATCH, span, message);
                Ty::Error
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
                if then_ty == Ty::Never && else_ty == Ty::Never { Ty::Never } else { Ty::Unit }
            }
            (Mode::Value(_), None) => {
                // A block that was never closed may have been followed by an `else`.
                if !then_ty.is_unknown() {
                    let span = self.span(e);
                    self.error(codes::TYPE_MISMATCH, span, "an `if` without `else` has no value; add an `else` branch");
                }
                Ty::Error
            }
            (Mode::Value(expected), Some(branch)) => {
                // The then-branch gives the else-branch its type, unless its type has a
                // `Never` argument, as `Some(fail e)` does.
                let partial = then_ty.has_never_arg();
                let expected = expected.or(Some(&then_ty).filter(|t| !t.is_unknown() && !partial));
                let else_ty = match branch {
                    ElseBranch::Block(block) => self.block_value(block, expected, copying),
                    ElseBranch::If(nested) => {
                        self.tail_copying = copying;
                        self.if_expr(*nested, Mode::Value(expected))
                    }
                };
                match expected {
                    _ if then_ty == Ty::Never && else_ty == Ty::Never => Ty::Never,
                    Some(expected) => expected.clone(),
                    None if partial => {
                        let span = match branch {
                            ElseBranch::Block(block) => block.span,
                            ElseBranch::If(nested) => self.span(*nested),
                        };
                        self.join_branch(&then_ty, &else_ty, span)
                    }
                    None => else_ty,
                }
            }
        };
        self.p.expr_ty.insert(e, ty.clone());
        ty
    }

    /// The type of a branch's value when one branch is `known` and another, at `span`, is
    /// `other`. Used where a `Never` argument kept a branch from giving the other its type.
    fn join_branch(&mut self, known: &Ty, other: &Ty, span: Span) -> Ty {
        known.join(other).unwrap_or_else(|| {
            let message = format!("expected `{}`, found `{}`", self.show(known), self.show(other));
            self.error(codes::TYPE_MISMATCH, span, message);
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
        self.p.expr_ty.insert(e, Ty::Bool);
    }

    /// `value is pat`, whose bindings go in the innermost scope.
    fn is_test(&mut self, value: ExprId, pat: PatId) {
        let ty = self.infer(value);
        self.pattern_borrowed = self.borrowed_place(value);
        self.pattern(pat, &ty);
        self.pattern_borrowed = false;
    }

    /// The record or enum named `sym`: the module's, or `Option` or `Result` from the prelude.
    fn adt_named(&self, sym: Symbol) -> Option<AdtId> {
        if self.poisoned.contains(&sym) {
            return None;
        }
        self.adt_names.get(&sym).copied().or_else(|| prelude_adt(self.m.text(sym)))
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

    /// The type arguments of a variant of `id` that `expected` gives, one per parameter.
    fn expected_args(&self, id: AdtId, expected: Option<&Ty>) -> Vec<Option<Ty>> {
        match expected {
            Some(Ty::Adt(other, args)) if *other == id => args.iter().cloned().map(Some).collect(),
            _ => vec![None; self.p.decls.adt(id).params],
        }
    }

    /// The type of a variant of `id` built with type arguments `targs`. One that neither the
    /// expected type nor the fields gave is reported, unless `reported` says the construction
    /// already has an error (OPEN_QUESTIONS P5).
    fn variant_type(
        &mut self,
        id: AdtId,
        targs: Vec<Option<Ty>>,
        expected: Option<&Ty>,
        span: Span,
        reported: bool,
    ) -> Ty {
        if let Some(args) = targs.iter().cloned().collect::<Option<Vec<Ty>>>() {
            return Ty::applied(id, args);
        }
        let name = self.p.decls.adt(id).name.clone();
        match expected {
            _ if reported => {}
            Some(Ty::Error) => {}
            Some(expected) if !matches!(expected, Ty::Adt(other, _) if *other == id) => {
                let article = if &*name == "Option" { "an" } else { "a" };
                let message = format!("expected `{}`, found {article} `{name}`", self.show(expected));
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            _ => {
                let missing = targs.iter().filter(|t| t.is_none()).count();
                let message = format!(
                    "the {} of this `{name}` can't be inferred; give the binding a type, such as `{}`",
                    if missing == 1 { "type argument" } else { "type arguments" },
                    example_type(&name)
                );
                self.error(codes::CANNOT_INFER, span, message);
            }
        }
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
        let targs = self.expected_args(id, expected);
        let span = self.span(e);
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
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        };
        let ctor = def.ctor_name(v);
        let mut targs = self.expected_args(id, expected);
        if variant.rejected {
            for arg in args {
                self.infer(arg.value);
            }
            return self.variant_type(id, targs, expected, span, true);
        }
        if variant.fields.is_empty() {
            let message = format!("`{ctor}` has no fields, so it is written without parentheses");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            for arg in args {
                self.infer(arg.value);
            }
            return self.variant_type(id, targs, expected, span, true);
        }
        let params: Vec<(Box<str>, Ty)> = variant.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        self.p.res.insert(e, Res::Ctor(id, v));
        let counted = self.generic_args(&ctor, &params, &mut targs, &[], args, span, true);
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
        // The parts of a borrowed value are borrowed too.
        let borrowed = self.borrowed_place(*scrutinee);
        let mut rows = Vec::new();
        let mut expected = match mode {
            Mode::Value(expected) => expected.cloned(),
            _ => None,
        };
        // Arms whose type has a `Never` argument, which give the others no type.
        let mut partial: Vec<(Ty, Span)> = Vec::new();
        let mut diverges = true;
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
                    let ty = self.block_value(&arm.body, expected.as_ref(), copying);
                    if expected.is_none() && ty.has_never_arg() {
                        partial.push((ty.clone(), arm.body.span));
                    } else if expected.is_none() && !ty.is_unknown() {
                        expected = Some(ty.clone());
                    }
                    ty
                }
            };
            diverges &= ty == Ty::Never;
            self.f.scopes.pop();
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
        let mut partial = partial.into_iter();
        if expected.is_none() {
            expected = partial.next().map(|(ty, _)| ty);
        }
        for (ty, span) in partial {
            expected = expected.map(|known| self.join_branch(&known, &ty, span));
        }
        let ty = match mode {
            _ if diverges => Ty::Never,
            Mode::Stmt | Mode::Tail(_) => Ty::Unit,
            Mode::Value(_) if !complete => Ty::Error,
            Mode::Value(_) => expected.unwrap_or(Ty::Error),
        };
        self.p.expr_ty.insert(e, ty.clone());
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
                let id = self.declare(*name, ty.clone(), false, "binding", self.pattern_borrowed);
                self.p.pat_local.insert(pat, id);
                Space::Wild
            }
            PatKind::Lit(lit) => self.literal_pattern(*lit, ty),
            PatKind::Range { lo, hi, .. } => match ty {
                Ty::Int(_) | Ty::Char => {
                    let lo_ty = self.check(*lo, ty);
                    let hi_ty = self.check(*hi, ty);
                    match ty {
                        _ if lo_ty != *ty || hi_ty != *ty => Space::Error,
                        Ty::Char => Space::Some,
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
            // Integers are covered by facts, which the v1 profile checks at run time.
            _ => Space::Wild,
        }
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
        if let Some(q) = qualifier {
            let q_text = m.text(q.sym);
            let def = self.p.decls.adt(id);
            let problem = match self.adt_named(q.sym) {
                _ if self.poisoned.contains(&q.sym) => None,
                Some(other) if other == id && def.is_enum() => None,
                Some(other) => Some((
                    codes::TYPE_MISMATCH,
                    q.span,
                    format!("expected a pattern for `{}`, found one for `{}`", def.name, self.p.decls.adt(other).name),
                )),
                None if self.imports.contains_key(&q.sym) || builtin_type(q_text).is_some() => Some((
                    codes::TYPE_MISMATCH,
                    q.span,
                    format!("expected a pattern for `{}`, found one for `{q_text}`", def.name),
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
            } else if let Some(&other) = self.adt_names.get(&name.sym).filter(|_| !def.is_enum()) {
                let message =
                    format!("expected a pattern for `{}`, found one for `{}`", def.name, self.p.decls.adt(other).name);
                self.error(codes::TYPE_MISMATCH, span, message);
            } else if def.is_enum() {
                self.error(codes::UNKNOWN_MEMBER, name.span, format!("`{}` has no variant `{text}`", def.name));
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
                let (lt, rt) = self.operands(lo, hi, None);
                let span = self.span(iter);
                match self.unify_operands(lt, rt, span) {
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
                self.infer(iter);
                let span = self.span(iter);
                self.not_implemented(span, "`for` loops over collections", Planned::Phase(2));
                Ty::Error
            }
        };
        self.p.expr_ty.insert(iter, element.clone());
        self.f.scopes.push(Vec::new());
        let id = self.declare(binding, element, false, "loop variable", false);
        self.p.for_local.insert(e, id);
        self.loop_body(e, label, body);
        self.f.scopes.pop();
        Ty::Unit
    }
}

/// Whether `ty` mentions one of the type parameters `targs` stands for.
fn mentions_targ(ty: &Ty, targs: &[Option<Ty>]) -> bool {
    match ty {
        Ty::Param(i) => (*i as usize) < targs.len(),
        Ty::Adt(_, args) => args.iter().any(|arg| mentions_targ(arg, targs)),
        _ => false,
    }
}

/// Whether `ty` mentions a type parameter.
fn mentions_param(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) => true,
        Ty::Adt(_, args) => args.iter().any(mentions_param),
        _ => false,
    }
}

/// Whether `ty`, with the type parameters `targs` knows, says more about an argument than
/// that it is any type, as `Result[T, Text]` does and `Option[T]` doesn't while `T` is open.
fn says_more(ty: &Ty, targs: &[Option<Ty>]) -> bool {
    match ty {
        Ty::Param(i) => targs.get(*i as usize).is_none_or(Option::is_some),
        Ty::Adt(_, args) => args.is_empty() || args.iter().any(|arg| says_more(arg, targs)),
        _ => true,
    }
}

/// Learns the type parameters in `declared` from an argument of type `actual`. One not known
/// yet takes the part of `actual` in its place, and one known as `Never`, or with a `Never`
/// inside, widens to it, unless `::[…]` gave it (`fixed`). An error gives every one it
/// covers, so nothing more is reported about them (§15.1). Parts that differ are left for
/// the caller to report.
fn infer_targs(declared: &Ty, actual: &Ty, targs: &mut [Option<Ty>], fixed: &[bool]) {
    match (declared, actual) {
        (Ty::Param(i), actual) => {
            let i = *i as usize;
            match targs.get(i) {
                Some(None) => targs[i] = Some(actual.clone()),
                // Only a `Never` in what is known yet can widen, and joining a type without one
                // would rebuild it at every level of `Some(Some(…))` for nothing.
                Some(Some(known))
                    if !fixed.get(i).copied().unwrap_or(false) && (*known == Ty::Never || known.has_never_arg()) =>
                {
                    if let Some(joined) = known.join(actual) {
                        targs[i] = Some(joined);
                    }
                }
                _ => {}
            }
        }
        (Ty::Adt(id, args), Ty::Adt(other, actual_args)) if id == other && args.len() == actual_args.len() => {
            for (arg, actual) in args.iter().zip(actual_args.iter()) {
                infer_targs(arg, actual, targs, fixed);
            }
        }
        (Ty::Adt(_, args), Ty::Error | Ty::Never) => {
            for arg in args.iter() {
                infer_targs(arg, actual, targs, fixed);
            }
        }
        _ => {}
    }
}

/// Gives each type parameter in `declared` that `targs` doesn't know yet the part of
/// `actual` in its place, so `Option[T]` and `Option[Int]` make `T` an `Int`. Parts that
/// differ are left for the caller to report.
fn unify(declared: &Ty, actual: &Ty, targs: &mut [Option<Ty>]) {
    match (declared, actual) {
        (Ty::Param(i), actual) => {
            if let Some(slot @ None) = targs.get_mut(*i as usize) {
                *slot = Some(actual.clone());
            }
        }
        (Ty::Adt(id, args), Ty::Adt(other, actual_args)) if id == other && args.len() == actual_args.len() => {
            for (arg, actual) in args.iter().zip(actual_args.iter()) {
                unify(arg, actual, targs);
            }
        }
        _ => {}
    }
}

/// Whether a statement or block of this type may never finish. An error counts, because the
/// code it stands for might diverge, and reporting a missing `return` would depend on it.
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
        _ => return None,
    })
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
