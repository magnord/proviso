//! Name resolution and type checking for the phase-1 subset (scalar types, functions,
//! control flow, `fails` and `try`, and the prelude's `System` with only `stdout`), for
//! records, and for enums, `match` and patterns.
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

use crate::decls::{AdtDef, AdtId, AdtKind, Decls, FieldDef, FieldIdx, IfaceId, Pred, VariantDef, VariantIdx};
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
    /// `show()` on any type with `Show`
    Show,
    /// `Text.byte_len() -> Int`
    ByteLen,
    /// `Text.is_empty() -> Bool`
    IsEmpty,
    /// `eq(other: Self) -> Bool` on any type with `Eq` (STD.md)
    Eq,
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
}

static ERROR: Ty = Ty::Error;

impl Program {
    pub fn ty(&self, e: ExprId) -> &Ty {
        self.expr_ty.get(e).unwrap_or(&ERROR)
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
        adt_names: HashMap::new(),
        poisoned: m.poisoned.clone(),
        adts: Vec::new(),
        f: FnState::new(Ty::Unit, None),
        in_chain: false,
        tries: Vec::new(),
    };
    checker.imports();
    checker.adt_names();
    checker.adt_fields();
    checker.signatures();
    checker.adt_derives();
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
}

impl FnState {
    fn new(ret: Ty, fails: Option<Ty>) -> FnState {
        FnState { ret, fails, scopes: Vec::new(), locals: Vec::new(), loops: Vec::new(), returns: true }
    }
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

    /// How diagnostics write `ty`.
    fn show<'s>(&'s self, ty: &'s Ty) -> impl std::fmt::Display + 's {
        self.p.decls.display(ty)
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
        let describe = |vis| match vis {
            Visibility::Private => "private",
            Visibility::PubPkg => "`pub(pkg)`",
            Visibility::Pub => "`pub`",
        };
        let Some((record, record_vis)) = self.least_visible(ty) else { return };
        if reach(record_vis) < reach(vis) {
            let message = format!(
                "`{}` is {}, so it may not mention `{}`, which is {} (§3)",
                self.m.text(item.sym),
                describe(vis),
                self.p.decls.adt(record).name,
                describe(record_vis),
            );
            let span = self.m.types[at].span;
            self.error(codes::PRIVATE_IN_PUBLIC, span, message);
        }
    }

    /// The least visible module record or enum that `ty` mentions.
    fn least_visible(&self, ty: &Ty) -> Option<(AdtId, Visibility)> {
        let Ty::Adt(id, args) = ty else { return None };
        let own = self.adts.iter().find(|adt| adt.id == *id).map(|adt| (*id, adt.vis));
        let inner = args.iter().filter_map(|arg| self.least_visible(arg));
        own.into_iter().chain(inner).min_by_key(|&(_, vis)| reach(vis))
    }

    /// Resolves every `derives` list, then checks that each field implements what its
    /// record or enum derives, so a field's type answers wherever it is declared.
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
                match text {
                    "Eq" => derives.push(IfaceId::EQ),
                    "Show" => derives.push(IfaceId::SHOW),
                    // It still counts, unchecked, so `<` on the type isn't reported again.
                    "Ord" => {
                        self.not_implemented(name.span, "the `Ord` and `Hash` derives", Planned::Phase(2));
                        derives.push(IfaceId::ORD);
                    }
                    "Hash" => self.not_implemented(name.span, "the `Ord` and `Hash` derives", Planned::Phase(2)),
                    _ if prelude_interface(text) => {
                        unknown = true;
                        self.error(
                            codes::NOT_DERIVABLE,
                            name.span,
                            format!(
                                "`{text}` can't be derived; the derivable interfaces are `Eq`, `Ord`, `Hash` and `Show`"
                            ),
                        );
                    }
                    _ => {
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
        for k in 0..self.adts.len() {
            let adt = &self.adts[k];
            let def = self.p.decls.adt(adt.id);
            let mut missing = Vec::new();
            for &iface in def.derives.iter().filter(|&&iface| iface != IfaceId::ORD) {
                for (variant, (_, decls)) in def.variants.iter().zip(&adt.variants) {
                    for (field, field_decl) in variant.fields.iter().zip(kept_fields(decls)) {
                        if !field.ty.is_unknown() && !self.p.decls.implements(&field.ty, iface) {
                            let message = format!(
                                "field `{}` has type `{}`, which does not implement `{}`, so `{}` cannot derive it",
                                field.name,
                                self.show(&field.ty),
                                iface.name(),
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
                state.locals = fields.iter().map(|f| Local { ty: f.ty.clone(), mutable: false }).collect();
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
                    ParamMode::Keep if matches!(ty, Ty::Adt(AdtId::SYSTEM, _) | Ty::Error) => {}
                    ParamMode::Keep => {
                        self.not_implemented(param.span, "`keep` parameters other than `System`", Planned::Phase(2))
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
            let fails = decl.fails.map(|t| self.resolve_type(t)).filter(|t| *t != Ty::Never);
            // `main` is `pub` so the runtime can call it, not to export it (OPEN_QUESTIONS P5).
            if name != "main" {
                let typed = decl.params.iter().map(|p| p.ty).chain(decl.ret).chain(decl.fails);
                let types = params.iter().map(|p| p.ty.clone()).chain(decl.ret.map(|_| ret.clone()));
                let types: Vec<(Ty, TypeId)> =
                    types.chain(decl.fails.map(|_| fails.clone().unwrap_or(Ty::Never))).zip(typed).collect();
                for (ty, at) in types {
                    self.exposes(decl.name, item.vis, &ty, at);
                }
            }
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
            && !self.p.decls.implements(&err, IfaceId::SHOW)
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
            TypeExprKind::Applied(name) => {
                let text = m.text(name.sym);
                if self.poisoned.contains(&name.sym) {
                    return Ty::Error;
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
        if let Some(ty) = builtin_type(text) {
            return ty;
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
        let Some(decl) = m.fn_decl(info.item) else { return };
        let mut state = FnState::new(info.ret.clone(), info.fails.clone());
        let mut scope = Vec::new();
        for (i, param) in info.params.iter().enumerate() {
            state.locals.push(Local { ty: param.ty.clone(), mutable: false });
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
        let ret = self.f.ret.clone();
        self.f.scopes.push(Vec::new());
        let diverges = if ret == Ty::Unit {
            decl.body.stmts.iter().fold(false, |diverges, &s| self.stmt(s) | diverges)
        } else {
            self.tail_stmts(&decl.body, &ret)
        };
        self.f.scopes.pop();
        // A body that needed parse recovery has unknown control flow.
        if ret != Ty::Unit && ret != Ty::Error && !diverges && !decl.recovered {
            let name = m.text(decl.name.sym);
            self.error(
                codes::MISSING_RETURN,
                decl.body.span.end(),
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
                let id = self.declare(*name, ty, *mutable, what);
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
        let ty = self.infer(e);
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

    /// Checks a block used for its value: the final expression, if there is one.
    fn block_value(&mut self, block: &Block, expected: Option<&Ty>) -> Ty {
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
        let ty = self.expr_kind(e, expected, chain);
        self.p.expr_ty.insert(e, ty.clone());
        ty
    }

    fn expr_kind(&mut self, e: ExprId, expected: Option<&Ty>, chain: bool) -> Ty {
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
                        if !self.p.decls.implements(&ty, IfaceId::SHOW) && !ty.is_unknown() {
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
            ExprKind::Name(name) => self.name(e, *name),
            ExprKind::Call { callee, args } => self.call(*callee, args, span, chain),
            ExprKind::MethodCall { receiver, method, args } => {
                self.method_call(e, *receiver, *method, args, span, chain)
            }
            ExprKind::Field { base, name } => {
                if let Some(id) = self.enum_named(*base) {
                    return self.unit_variant(e, id, *name);
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
            ExprKind::If { .. } => self.if_expr(e, Mode::Value(expected)),
            ExprKind::Match { .. } => self.match_expr(e, Mode::Value(expected)),
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
        let numeric_or = |ty: &Ty| match ty {
            Ty::Error => None,
            ty if ty.is_numeric() => Some(ty.clone()),
            _ => hint.cloned(),
        };
        if self.is_untyped_literal(lhs) && !self.is_untyped_literal(rhs) {
            let rt = self.expr(rhs, hint);
            let lt = self.expr(lhs, numeric_or(&rt).as_ref());
            (lt, rt)
        } else {
            let lt = self.expr(lhs, hint);
            let rt = self.expr(rhs, numeric_or(&lt).as_ref());
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
            (lt, rt) if lt == rt => lt,
            (Ty::Never, other) | (other, Ty::Never) => other,
            (lt, rt) => {
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
                if !arithmetic_defined(op, &ty) {
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
                    BinOp::Eq | BinOp::Ne => matches!(ty, Ty::Float(_)) || self.p.decls.implements(&ty, IfaceId::EQ),
                    _ => matches!(ty, Ty::Float(_)) || self.p.decls.implements(&ty, IfaceId::ORD),
                };
                if !defined && !ty.is_unknown() {
                    let message = format!("`{symbol}` is not defined for `{}`", self.show(&ty));
                    self.error(codes::UNSUPPORTED_OPERATOR, span, message);
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
            return self.f.locals[id.index()].ty.clone();
        }
        if self.fn_names.contains_key(&name.sym) {
            self.not_implemented(name.span, "functions used as values", Planned::Phase(2));
        } else if self.unqualified_variant(name) || self.poisoned.contains(&name.sym) {
        } else if self.imports.contains_key(&name.sym)
            || self.adt_names.contains_key(&name.sym)
            || builtin_type(text).is_some()
        {
            self.error(codes::UNKNOWN_NAME, name.span, format!("`{text}` is a type or module, not a value"));
        } else {
            self.error(codes::UNKNOWN_NAME, name.span, format!("unknown name `{text}`"));
        }
        Ty::Error
    }

    fn call(&mut self, callee: ExprId, args: &[Arg], span: Span, chain: bool) -> Ty {
        let m = self.m;
        if let ExprKind::Name(name) = m.exprs[callee].kind
            && let Some(&id) = self.adt_names.get(&name.sym)
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
                        self.not_implemented(callee_span, "calls of function values", Planned::Phase(2))
                    }
                    Some(name) if self.unqualified_variant(name) => {}
                    Some(name) if self.poisoned.contains(&name.sym) => {}
                    // Phase 3 gives `System` the rest of its fields (REFERENCE §9.1).
                    Some(name) if m.text(name.sym) == "System" => {
                        self.not_implemented(callee_span, "constructions of `System`", Planned::Phase(3))
                    }
                    Some(name) if builtin_type(m.text(name.sym)).is_some() => {
                        self.not_implemented(callee_span, "conversions such as `Int64(x)`", Planned::Phase(2))
                    }
                    Some(name) => {
                        let text = m.text(name.sym);
                        self.error(codes::UNKNOWN_NAME, name.span, format!("unknown function `{text}`"));
                    }
                    None => self.not_implemented(callee_span, "calls of function values", Planned::Phase(2)),
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
        let params: Vec<(&str, Ty)> = info.params.iter().map(|p| (m.text(p.name), p.ty.clone())).collect();
        let (ret, fails) = (info.ret.clone(), info.fails.clone());
        self.args(name, &params, args, span);
        if let Some(err) = fails {
            self.fallible_call(name, &err, span, chain);
        }
        ret
    }

    /// A record's constructor takes its fields as parameters, so a construction follows the
    /// rules of a call (REFERENCE §4.4).
    fn construct(&mut self, callee: ExprId, id: AdtId, args: &[Arg], span: Span) -> Ty {
        self.p.res.insert(callee, Res::Ctor(id, VariantIdx::RECORD));
        let def = self.p.decls.adt(id);
        let name = def.name.clone();
        let params: Vec<(Box<str>, Ty)> = def.variant().fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        self.args(&name, &params, args, span);
        Ty::adt(id)
    }

    fn method_call(&mut self, e: ExprId, receiver: ExprId, method: Ident, args: &[Arg], span: Span, chain: bool) -> Ty {
        let m = self.m;
        let name = m.text(method.sym);
        if let Some(id) = self.enum_named(receiver)
            && (self.p.decls.adt(id).variant_named(name).is_some() || is_pascal(name))
        {
            return self.construct_variant(e, id, method, args, span);
        }
        if let ExprKind::Name(receiver_name) = m.exprs[receiver].kind
            && self.lookup_local(receiver_name.sym).is_none()
            && self.adt_names.contains_key(&receiver_name.sym)
        {
            let record = m.text(receiver_name.sym);
            let what = format!("associated functions such as `{record}.{name}`");
            self.not_implemented(span, &what, Planned::Phase(2));
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        }
        if let ExprKind::Name(receiver_name) = m.exprs[receiver].kind
            && self.lookup_local(receiver_name.sym).is_none()
            && prelude_interface(m.text(receiver_name.sym))
        {
            let iface = m.text(receiver_name.sym);
            let what = format!("calls through an interface, such as `{iface}.{name}(x)`,");
            self.not_implemented(span, &what, Planned::Phase(2));
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        }
        self.in_chain = chain;
        let receiver_ty = self.infer(receiver);
        if let (Ty::Adt(id, _), "with") = (&receiver_ty, name)
            && !self.p.decls.adt(*id).is_enum()
        {
            self.p.res.insert(e, Res::With);
            self.with_args(e, *id, args, span);
            return receiver_ty;
        }
        let decls = &self.p.decls;
        let signature = match (&receiver_ty, name) {
            (Ty::Cap(cap), "write_line") if cap.iface == IfaceId::OUT => {
                Some((Builtin::WriteLine, vec![("text", Ty::Text)], Ty::Unit, Some(Ty::IoError)))
            }
            (ty, "show") if decls.implements(ty, IfaceId::SHOW) => Some((Builtin::Show, vec![], Ty::Text, None)),
            (ty, "eq") if decls.implements(ty, IfaceId::EQ) => {
                Some((Builtin::Eq, vec![("other", ty.clone())], Ty::Bool, None))
            }
            (Ty::Text, "byte_len") => Some((Builtin::ByteLen, vec![], Ty::INT, None)),
            (Ty::Text, "is_empty") => Some((Builtin::IsEmpty, vec![], Ty::Bool, None)),
            _ => None,
        };
        let Some((builtin, params, ret, fails)) = signature else {
            // A rejected `impl` block may have declared the method.
            let unknown_methods = matches!(&receiver_ty, Ty::Adt(id, _) if self.p.decls.adt(*id).unknown_methods);
            if receiver_ty != Ty::Error && !unknown_methods {
                let message = format!("`{}` has no method `{name}`", self.show(&receiver_ty));
                self.error(codes::UNKNOWN_MEMBER, method.span, message);
            }
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::Error;
        };
        self.p.res.insert(e, Res::Method(builtin));
        self.args(name, &params, args, span);
        if let Some(err) = fails {
            self.fallible_call(name, &err, span, chain);
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
        let labelled = params.iter().map(|(param, _)| format!("{}: …", param.as_ref())).collect::<Vec<_>>().join(", ");
        let mut labels_reported = false;
        for (i, (arg, (param, ty))) in args.iter().zip(params).enumerate() {
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
            self.check(arg.value, ty);
        }
    }

    fn fallible_call(&mut self, callee: &str, err: &Ty, span: Span, chain: bool) {
        match self.tries.last_mut() {
            Some(errors) if chain => errors.push(err.clone()),
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

    fn if_expr(&mut self, e: ExprId, mode: Mode) -> Ty {
        let m = self.m;
        let ExprKind::If { cond, then_block, else_branch } = &m.exprs[e].kind else {
            unreachable!("if_expr is called on `if` expressions")
        };
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
            (Mode::Value(_), None) => self.block_value(then_block, None),
            (Mode::Value(expected), Some(_)) => self.block_value(then_block, expected),
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
                let expected = expected.or(Some(&then_ty).filter(|t| !t.is_unknown()));
                let else_ty = match branch {
                    ElseBranch::Block(block) => self.block_value(block, expected),
                    ElseBranch::If(nested) => self.if_expr(*nested, Mode::Value(expected)),
                };
                match expected {
                    _ if then_ty == Ty::Never && else_ty == Ty::Never => Ty::Never,
                    Some(expected) => expected.clone(),
                    None => else_ty,
                }
            }
        };
        self.p.expr_ty.insert(e, ty.clone());
        ty
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
        self.pattern(pat, &ty);
    }

    /// The enum that `e` names, when it is a name that is not a local.
    fn enum_named(&self, e: ExprId) -> Option<AdtId> {
        let ExprKind::Name(name) = self.m.exprs[e].kind else { return None };
        if self.lookup_local(name.sym).is_some() {
            return None;
        }
        let id = *self.adt_names.get(&name.sym)?;
        self.p.decls.adt(id).is_enum().then_some(id)
    }

    /// `Shape.Empty`, a variant without fields (REFERENCE §4.5).
    fn unit_variant(&mut self, e: ExprId, id: AdtId, name: Ident) -> Ty {
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
        Ty::adt(id)
    }

    /// `Shape.Circle(radius: 2)`: a variant's fields are passed as the arguments of a call
    /// (REFERENCE §4.5, §3).
    fn construct_variant(&mut self, e: ExprId, id: AdtId, name: Ident, args: &[Arg], span: Span) -> Ty {
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
        if variant.rejected {
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::adt(id);
        }
        if variant.fields.is_empty() {
            let message = format!("`{ctor}` has no fields, so it is written without parentheses");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            for arg in args {
                self.infer(arg.value);
            }
            return Ty::adt(id);
        }
        let params: Vec<(Box<str>, Ty)> = variant.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        self.p.res.insert(e, Res::Ctor(id, v));
        self.args(&ctor, &params, args, span);
        Ty::adt(id)
    }

    /// Reports a variant used without its enum, and returns whether `name` is one. Only
    /// `Some`, `None`, `Ok` and `Err` may be (REFERENCE §3, §4.5), and those come with
    /// `Option` and `Result`.
    fn unqualified_variant(&mut self, name: Ident) -> bool {
        let m = self.m;
        let text = m.text(name.sym);
        if matches!(text, "Some" | "None" | "Ok" | "Err") {
            self.not_implemented(name.span, "`Option` and `Result` values", Planned::Phase(2));
            return true;
        }
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
        let scrutinee_ty = self.infer(*scrutinee);
        let mut rows = Vec::new();
        let mut expected = match mode {
            Mode::Value(expected) => expected.cloned(),
            _ => None,
        };
        let mut diverges = true;
        for arm in arms {
            // An arm's bindings scope over its guard and body.
            self.f.scopes.push(Vec::new());
            let space = self.pattern(arm.pat, &scrutinee_ty);
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
                    let ty = self.block_value(&arm.body, expected.as_ref());
                    if expected.is_none() && !ty.is_unknown() {
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
            match exhaust::uncovered(&self.p.decls, &scrutinee_ty, &rows) {
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
                let id = self.declare(*name, ty.clone(), false, "binding");
                self.p.pat_local.insert(pat, id);
                Space::Wild
            }
            PatKind::Lit(lit) => self.literal_pattern(*lit, ty),
            PatKind::Range { lo, hi, .. } => {
                match ty {
                    Ty::Int(_) | Ty::Char => {
                        let lo_ty = self.check(*lo, ty);
                        let hi_ty = self.check(*hi, ty);
                        if *ty == Ty::Char && lo_ty == *ty && hi_ty == *ty {
                            return Space::Some;
                        }
                    }
                    _ if ty.is_unknown() => {
                        self.infer(*lo);
                        self.infer(*hi);
                    }
                    _ => {
                        self.infer(*lo);
                        self.infer(*hi);
                        let message = format!("a range pattern needs integer or char bounds, not `{}`", self.show(ty));
                        self.error(codes::UNSUPPORTED_OPERATOR, span, message);
                    }
                }
                // Integers are covered by facts, which the v1 profile checks at run time.
                Space::Wild
            }
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
            return Space::Wild;
        }
        let actual = self.check(lit, ty);
        if actual != *ty {
            return Space::Wild;
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
        Space::Wild
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
        let Ty::Adt(id, _) = ty else {
            if matches!(text, "Some" | "None" | "Ok" | "Err") && qualifier.is_none() {
                self.not_implemented(name.span, "`Option` and `Result` patterns", Planned::Phase(2));
            } else if !ty.is_unknown() && !qualifier.is_some_and(|q| self.poisoned.contains(&q.sym)) {
                let message = format!("expected a pattern for `{}`, found the variant pattern `{text}`", self.show(ty));
                self.error(codes::TYPE_MISMATCH, span, message);
            }
            return self.unknown_parts(fields);
        };
        let id = *id;
        if let Some(q) = qualifier {
            let q_text = m.text(q.sym);
            let def = self.p.decls.adt(id);
            let problem = match self.adt_names.get(&q.sym) {
                _ if self.poisoned.contains(&q.sym) => None,
                Some(&other) if other == id && def.is_enum() => None,
                Some(&other) => Some((
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
            if matches!(text, "Some" | "None" | "Ok" | "Err") && qualifier.is_none() {
                self.not_implemented(name.span, "`Option` and `Result` patterns", Planned::Phase(2));
            } else if self.poisoned.contains(&name.sym) {
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
        let declared: Vec<(Box<str>, Ty)> = variant.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        let Some(fields) = fields else {
            if declared.is_empty() {
                self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: v, fields: Box::new([]) });
                return Space::Ctor(Ctor::Variant(v), Vec::new());
            }
            let n = declared.len();
            let noun = if n == 1 { "field" } else { "fields" };
            let message = format!("`{ctor}` has {n} {noun}; match them, or write `{ctor}(..)` to skip them");
            self.error(codes::WRONG_ARGUMENT_COUNT, span, message);
            return Space::Wild;
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
            return Space::Wild;
        }
        self.p.pat_ctor.insert(pat, CtorPat { adt: id, variant: v, fields: targets.into() });
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
        let id = self.declare(binding, element, false, "loop variable");
        self.p.for_local.insert(e, id);
        self.loop_body(e, label, body);
        self.f.scopes.pop();
        Ty::Unit
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

/// The interfaces of the prelude (REFERENCE §3).
fn prelude_interface(name: &str) -> bool {
    matches!(
        name,
        "Eq" | "Ord" | "Hash" | "Show" | "Copy" | "Index" | "Abandon" | "Add" | "Sub" | "Mul" | "Div" | "Neg"
    )
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
