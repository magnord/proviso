//! Nominal declarations: the records, enums and interfaces of the prelude, and those of the
//! module, with the module's implementations. Questions about a type that depend on what it
//! declares, such as its name or the interfaces it implements, are answered here.

use std::collections::{HashMap, HashSet};
use std::fmt;

use proviso_syntax::ast::{ExprId, ParamMode};

use crate::types::{FloatTy, IntTy, Ty};

/// A record or enum declared in Proviso. The prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AdtId(u32);

impl AdtId {
    pub const SYSTEM: AdtId = AdtId(0);
    pub const OPTION: AdtId = AdtId(1);
    pub const RESULT: AdtId = AdtId(2);
    /// `std.text`'s `ParseError` (STD.md).
    pub const PARSE_ERROR: AdtId = AdtId(3);
    /// The 2-tuple `(A, B)`. Tuples of other lengths are declared when first used.
    pub const PAIR: AdtId = AdtId(4);
    /// `List[T]` (STD.md).
    pub const LIST: AdtId = AdtId(5);
    /// `Map[K, V]` (STD.md).
    pub const MAP: AdtId = AdtId(6);

    /// How many records and enums are declared before the module's own.
    const BUILT_IN: usize = 7;

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// An interface: one of the prelude's, `std.io`'s `Out`, or one the module declares. The
/// prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct IfaceId(u32);

impl IfaceId {
    pub const EQ: IfaceId = IfaceId(0);
    pub const ORD: IfaceId = IfaceId(1);
    pub const SHOW: IfaceId = IfaceId(2);
    /// The capability interface of `std.io`.
    pub const OUT: IfaceId = IfaceId(3);
    pub const HASH: IfaceId = IfaceId(4);
    pub const COPY: IfaceId = IfaceId(5);

    /// The interfaces declared before the module's, in id order: the prelude's (REFERENCE §3),
    /// and `std.io`'s `Out`.
    const BUILT_IN: [&str; 13] =
        ["Eq", "Ord", "Show", "Out", "Hash", "Copy", "Abandon", "Index", "Add", "Sub", "Mul", "Div", "Neg"];

    /// The prelude interface named `name`. `Out` comes from `std.io`, so it isn't one.
    pub fn prelude(name: &str) -> Option<IfaceId> {
        let i = Self::BUILT_IN.iter().position(|n| *n == name && name != "Out")?;
        Some(IfaceId(i as u32))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Whether a record can derive it (REFERENCE §4.4).
    pub fn derivable(self) -> bool {
        matches!(self, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::HASH)
    }

    /// Whether it is a prelude interface whose methods come later: `Abandon`, whose `abandon`
    /// takes `take self` (STD.md), and `Index` and the operator interfaces, whose methods
    /// STD.md doesn't declare yet.
    pub fn methods_later(self) -> bool {
        (6..13).contains(&self.0)
    }
}

/// An interface's declaration.
pub struct IfaceDef {
    pub name: Box<str>,
    pub methods: Vec<IfaceMethod>,
    /// A rejected method declaration may be the one an implementation or a call names, so
    /// neither is checked against the methods it lists (REFERENCE §15.1).
    pub incomplete: bool,
}

impl IfaceDef {
    pub fn method(&self, name: &str) -> Option<usize> {
        self.methods.iter().position(|m| &*m.name == name)
    }
}

/// A method an interface declares. Every method takes `self`, and its types write the
/// implementing type, `Self`, as `Ty::Param(0)`.
pub struct IfaceMethod {
    pub name: Box<str>,
    /// The parameters after `self`.
    pub params: Vec<(Box<str>, Ty)>,
    /// The mode of each parameter in `params`, which an implementation must repeat.
    pub modes: Vec<ParamMode>,
    pub ret: Ty,
    pub fails: Option<Ty>,
}

/// The type an `impl` is for, told apart as its values tell it at run time. Phase 2
/// implements interfaces only for types without type arguments, so this names one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ImplKey {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Text,
    Unit,
    IoError,
    Adt(AdtId),
}

impl ImplKey {
    pub fn of(ty: &Ty) -> Option<ImplKey> {
        Some(match ty {
            Ty::Int(it) => ImplKey::Int(*it),
            Ty::Float(ft) => ImplKey::Float(*ft),
            Ty::Bool => ImplKey::Bool,
            Ty::Char => ImplKey::Char,
            Ty::Text => ImplKey::Text,
            Ty::Unit => ImplKey::Unit,
            Ty::IoError => ImplKey::IoError,
            Ty::Adt(id, args) if args.is_empty() => ImplKey::Adt(*id),
            _ => return None,
        })
    }
}

/// An `impl I for T`: the function of each of `I`'s methods, in `I`'s order, or `None` for
/// one the block lacks or declares differently.
pub struct ImplDef {
    pub methods: Vec<Option<usize>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FieldIdx(pub(crate) u32);

impl FieldIdx {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VariantIdx(u32);

impl VariantIdx {
    /// The one variant of a record, named like the record.
    pub const RECORD: VariantIdx = VariantIdx(0);
    pub const SOME: VariantIdx = VariantIdx(0);
    pub const NONE: VariantIdx = VariantIdx(1);
    pub const OK: VariantIdx = VariantIdx(0);
    pub const ERR: VariantIdx = VariantIdx(1);

    pub const fn new(index: usize) -> VariantIdx {
        VariantIdx(index as u32)
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AdtKind {
    Record,
    Enum,
    /// A prelude collection, `List` or `Map`, whose values the toolchain builds. It has no
    /// variants, and every one has values, as an empty collection does.
    Collection,
}

pub struct AdtDef {
    pub name: Box<str>,
    pub kind: AdtKind,
    /// The number of type parameters. Fields refer to them as [`Ty::Param`].
    pub params: usize,
    /// Its variants are written without the enum's name, and their one field without a label:
    /// `Some(3)` and `Err(e)` (REFERENCE §3, STD.md).
    pub bare_variants: bool,
    /// A record has one, named like it. An enum has one per variant it keeps, in
    /// declaration order.
    pub variants: Vec<VariantDef>,
    /// What `derives` names, including a derive whose fields don't all implement it, so that
    /// its uses aren't reported again.
    pub derives: Vec<IfaceId>,
    /// A rejected `derives` entry or `impl` block may have given it more interfaces, so it is
    /// taken to implement each one a record can derive, and their uses aren't reported again.
    pub unknown_interfaces: bool,
    /// A rejected `impl` block may have given it methods, so a call of a method it doesn't
    /// have isn't reported.
    pub unknown_methods: bool,
    /// A rejected variant may be the one a pattern meant, so a `match` on the enum isn't
    /// checked for exhaustiveness.
    pub unknown_variants: bool,
    /// A tuple, whose one variant has a field per element, named by its position. It is
    /// written `(A, B)`, and so are its values and patterns (OPEN_QUESTIONS P5).
    pub tuple: bool,
}

impl AdtDef {
    pub fn record(name: &str, fields: Vec<FieldDef>) -> AdtDef {
        let mut def = AdtDef::new(name, AdtKind::Record);
        def.variants.push(VariantDef::new(name, fields));
        def
    }

    /// An enum, whose variants are added once their names are checked.
    pub fn enumeration(name: &str) -> AdtDef {
        AdtDef::new(name, AdtKind::Enum)
    }

    fn new(name: &str, kind: AdtKind) -> AdtDef {
        AdtDef {
            name: name.into(),
            kind,
            params: 0,
            bare_variants: false,
            variants: Vec::new(),
            derives: Vec::new(),
            unknown_interfaces: false,
            unknown_methods: false,
            unknown_variants: false,
            tuple: false,
        }
    }

    /// The tuple of `n` elements, a record whose type parameters are its elements' types.
    fn tuple(n: usize) -> AdtDef {
        let name = format!("({})", vec!["_"; n].join(", "));
        let fields = (0..n).map(|i| FieldDef { name: i.to_string().into(), ty: Ty::Param(i as u32) }).collect();
        let mut def = AdtDef::record(&name, fields);
        def.params = n;
        def.tuple = true;
        def.derives = vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH];
        def
    }

    /// A prelude collection, which implements what its type arguments do (STD.md).
    fn collection(name: &str, params: usize) -> AdtDef {
        let mut def = AdtDef::new(name, AdtKind::Collection);
        def.params = params;
        def.derives = vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH];
        def
    }

    pub fn is_enum(&self) -> bool {
        self.kind == AdtKind::Enum
    }

    pub fn is_collection(&self) -> bool {
        self.kind == AdtKind::Collection
    }

    /// The one variant of a record.
    pub fn variant(&self) -> &VariantDef {
        debug_assert_eq!(self.kind, AdtKind::Record, "only a record has exactly one variant");
        &self.variants[VariantIdx::RECORD.index()]
    }

    /// A field of a record. An enum has none: its variants do. Nor has a collection.
    pub fn field(&self, name: &str) -> Option<(FieldIdx, &FieldDef)> {
        if self.kind != AdtKind::Record {
            return None;
        }
        let i = self.variant().fields.iter().position(|f| &*f.name == name)?;
        Some((FieldIdx(i as u32), &self.variant().fields[i]))
    }

    /// An enum's variant called `name`.
    pub fn variant_named(&self, name: &str) -> Option<(VariantIdx, &VariantDef)> {
        if !self.is_enum() {
            return None;
        }
        let i = self.variants.iter().position(|v| &*v.name == name)?;
        Some((VariantIdx::new(i), &self.variants[i]))
    }

    /// How code names a variant: `Point` for a record, `Shape.Circle` for an enum's variant,
    /// and `Some` for one of the prelude's. A tuple has no name.
    pub fn ctor_name(&self, variant: VariantIdx) -> String {
        match self.kind {
            AdtKind::Record | AdtKind::Collection => self.name.to_string(),
            AdtKind::Enum if self.bare_variants => self.variants[variant.index()].name.to_string(),
            AdtKind::Enum => format!("{}.{}", self.name, self.variants[variant.index()].name),
        }
    }

    /// The types of a variant's fields in a value of this type applied to `args`.
    pub fn field_types(&self, variant: VariantIdx, args: &[Ty]) -> Vec<Ty> {
        self.variants[variant.index()].fields.iter().map(|f| f.ty.subst(args)).collect()
    }
}

pub struct VariantDef {
    pub name: Box<str>,
    pub fields: Vec<FieldDef>,
    /// The fields' `where` clauses in field order, then the record-level one. Each is checked
    /// in a scope where field `i` is `LocalId(i)`.
    pub preds: Vec<Pred>,
    /// The local slots its predicates need, fields first.
    pub locals: usize,
    /// Declared twice, so uses of it are not checked (REFERENCE §15.1).
    pub rejected: bool,
}

impl VariantDef {
    pub fn new(name: &str, fields: Vec<FieldDef>) -> VariantDef {
        VariantDef { name: name.into(), locals: fields.len(), fields, preds: Vec::new(), rejected: false }
    }
}

pub struct FieldDef {
    pub name: Box<str>,
    pub ty: Ty,
}

/// A refinement, which the v1 profile checks at run time (OPEN_QUESTIONS P3).
pub struct Pred {
    pub expr: ExprId,
    /// The field whose `where` this is, which sees only that field; `None` for the
    /// record-level one, which sees them all (OPEN_QUESTIONS P5).
    pub field: Option<FieldIdx>,
}

pub struct Decls {
    adts: Vec<AdtDef>,
    ifaces: Vec<IfaceDef>,
    impls: HashMap<(IfaceId, ImplKey), ImplDef>,
    /// The tuple of each length, by its length.
    tuples: HashMap<usize, AdtId>,
    /// Whether a rejected `impl` block was for a tuple type.
    unknown_tuples: bool,
    /// Types other than records and enums that a rejected `impl` block names, such as
    /// `Int`. It may have given them methods and interfaces, so uses of those aren't
    /// reported. A record or enum keeps this in its [`AdtDef`].
    unknown: HashSet<ImplKey>,
}

impl Default for Decls {
    /// The prelude, with each declaration at the id its constant names.
    fn default() -> Decls {
        let system = AdtDef::record("System", vec![FieldDef { name: "stdout".into(), ty: Ty::out() }]);
        // As STD.md declares them, so `Some` comes before `None`.
        let generic = |name: &str, params: usize, variants: [(&str, Option<(&str, u32)>); 2]| {
            let mut def = AdtDef::enumeration(name);
            def.params = params;
            def.bare_variants = true;
            def.derives = vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH];
            for (variant, field) in variants {
                let fields = field.map(|(name, param)| FieldDef { name: name.into(), ty: Ty::Param(param) });
                def.variants.push(VariantDef::new(variant, fields.into_iter().collect()));
            }
            def
        };
        let option = generic("Option", 1, [("Some", Some(("value", 0))), ("None", None)]);
        let result = generic("Result", 2, [("Ok", Some(("value", 0))), ("Err", Some(("error", 1)))]);
        let mut parse_error = AdtDef::enumeration("ParseError");
        parse_error.derives = vec![IfaceId::EQ, IfaceId::SHOW];
        for variant in ["Empty", "Invalid", "OutOfRange"] {
            parse_error.variants.push(VariantDef::new(variant, Vec::new()));
        }
        // `Ord`'s `cmp` returns an `Ordering`, which comes later, so its calls are rejected.
        let method = |name: &str, params: Vec<(&str, Ty)>, ret: Ty| IfaceMethod {
            name: name.into(),
            modes: vec![ParamMode::Borrow; params.len()],
            params: params.into_iter().map(|(n, t)| (n.into(), t)).collect(),
            ret,
            fails: None,
        };
        let ifaces = IfaceId::BUILT_IN
            .iter()
            .map(|&name| {
                let methods = match name {
                    "Eq" => vec![method("eq", vec![("other", Ty::Param(0))], Ty::Bool)],
                    "Ord" => vec![method("cmp", vec![("other", Ty::Param(0))], Ty::Error)],
                    "Show" => vec![method("show", vec![], Ty::Text)],
                    _ => Vec::new(),
                };
                IfaceDef { name: name.into(), methods, incomplete: false }
            })
            .collect();
        let (list, map) = (AdtDef::collection("List", 1), AdtDef::collection("Map", 2));
        let adts = vec![system, option, result, parse_error, AdtDef::tuple(2), list, map];
        debug_assert_eq!(adts.len(), AdtId::BUILT_IN);
        let tuples = HashMap::from([(2, AdtId::PAIR)]);
        Decls { adts, ifaces, impls: HashMap::new(), tuples, unknown_tuples: false, unknown: HashSet::new() }
    }
}

impl Decls {
    pub fn push(&mut self, def: AdtDef) -> AdtId {
        self.adts.push(def);
        AdtId(self.adts.len() as u32 - 1)
    }

    pub fn adt(&self, id: AdtId) -> &AdtDef {
        &self.adts[id.0 as usize]
    }

    pub fn adt_mut(&mut self, id: AdtId) -> &mut AdtDef {
        &mut self.adts[id.0 as usize]
    }

    /// The tuple of `n` elements, declared on first use.
    pub fn tuple(&mut self, n: usize) -> AdtId {
        if let Some(&id) = self.tuples.get(&n) {
            return id;
        }
        let mut def = AdtDef::tuple(n);
        (def.unknown_interfaces, def.unknown_methods) = (self.unknown_tuples, self.unknown_tuples);
        let id = self.push(def);
        self.tuples.insert(n, id);
        id
    }

    /// The `n`-tuple applied to `elements`.
    pub fn tuple_ty(&mut self, elements: Vec<Ty>) -> Ty {
        let id = self.tuple(elements.len());
        Ty::applied(id, elements)
    }

    /// Notes that a rejected `impl` block was for a tuple type, so every tuple type, now and
    /// later, may have methods and interfaces we don't know (§15.1).
    pub fn poison_tuples(&mut self) {
        self.unknown_tuples = true;
        for &id in self.tuples.values() {
            let def = &mut self.adts[id.index()];
            (def.unknown_interfaces, def.unknown_methods) = (true, true);
        }
    }

    pub fn is_tuple(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Adt(id, _) if self.adt(*id).tuple)
    }

    pub fn push_iface(&mut self, def: IfaceDef) -> IfaceId {
        self.ifaces.push(def);
        IfaceId(self.ifaces.len() as u32 - 1)
    }

    pub fn iface(&self, id: IfaceId) -> &IfaceDef {
        &self.ifaces[id.index()]
    }

    pub fn iface_mut(&mut self, id: IfaceId) -> &mut IfaceDef {
        &mut self.ifaces[id.index()]
    }

    /// Every interface, with its id.
    pub fn ifaces(&self) -> impl Iterator<Item = (IfaceId, &IfaceDef)> {
        self.ifaces.iter().enumerate().map(|(i, def)| (IfaceId(i as u32), def))
    }

    /// Records the `impl` of `iface` for `key`, unless there is one; returns whether it was new.
    pub fn add_impl(&mut self, iface: IfaceId, key: ImplKey, def: ImplDef) -> bool {
        match self.impls.entry((iface, key)) {
            std::collections::hash_map::Entry::Occupied(_) => false,
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(def);
                true
            }
        }
    }

    pub fn impl_of(&self, iface: IfaceId, key: ImplKey) -> Option<&ImplDef> {
        self.impls.get(&(iface, key))
    }

    /// The function that runs method `method` of `iface` for values of `key`, when an `impl`
    /// declares one rather than `derives` or the prelude.
    pub fn impl_method(&self, iface: IfaceId, key: ImplKey, method: usize) -> Option<usize> {
        self.impls.get(&(iface, key))?.methods.get(method).copied().flatten()
    }

    /// The interfaces implemented for `key` by an `impl`.
    pub fn impls_for(&self, key: ImplKey) -> impl Iterator<Item = IfaceId> + '_ {
        self.impls.keys().filter(move |(_, k)| *k == key).map(|(iface, _)| *iface)
    }

    /// Notes that a rejected `impl` block names `key`, so it may have methods and interfaces
    /// that nothing records.
    pub fn mark_unknown(&mut self, key: ImplKey) {
        match key {
            ImplKey::Adt(id) => {
                let def = self.adt_mut(id);
                def.unknown_interfaces = true;
                def.unknown_methods = true;
            }
            key => {
                self.unknown.insert(key);
            }
        }
    }

    /// Whether a rejected `impl` block may have given `ty` methods that nothing records.
    pub fn unknown_methods(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Adt(id, _) => self.adt(*id).unknown_methods,
            ty => ImplKey::of(ty).is_some_and(|key| self.unknown.contains(&key)),
        }
    }

    /// Whether a rejected `impl` block or `derives` entry may have given `ty` interfaces that
    /// nothing records, so that [`Decls::implements`] answers yes for every interface.
    pub fn unknown_interfaces(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Adt(id, _) => self.adt(*id).unknown_interfaces,
            ty => ImplKey::of(ty).is_some_and(|key| self.unknown.contains(&key)),
        }
    }

    /// Which records and enums have values: those with a variant whose fields all have types
    /// with values. An enum without variants has none, and so does a type that can only be
    /// built from itself. A type with a rejected variant is taken to have some, so that
    /// nothing about it is reported (REFERENCE §15.1).
    pub fn inhabited(&self) -> Inhabited {
        let mut graph = Graph::default();
        // Node `i` is record or enum `i`, which has values if one of its variants does.
        for _ in &self.adts {
            graph.node(false);
        }
        for (a, def) in self.adts.iter().enumerate() {
            // A generic type's values depend on its arguments, so `has_values` asks per use.
            if def.params > 0 {
                continue;
            }
            for variant in &def.variants {
                let fields = variant.fields.iter().map(|f| graph.requirement(self, &f.ty)).collect();
                let variant = graph.all(fields);
                graph.implies(variant, a);
            }
            if def.unknown_variants {
                graph.fire(a);
            }
        }
        graph.run();
        Inhabited { adts: graph.nodes[..self.adts.len()].iter().map(|n| n.fired).collect() }
    }

    /// Whether `ty` implements `iface`: built in, derived (STD.md) or by an `impl`. Type
    /// parameter `i` implements the interfaces `params[i]` lists. An unknown type implements
    /// nothing, so callers decide whether it is worth reporting.
    pub fn implements(&self, ty: &Ty, iface: IfaceId, params: &[Vec<IfaceId>]) -> bool {
        if iface == IfaceId::COPY {
            return self.copyable(ty, params, &mut Vec::new());
        }
        let by_impl =
            || ImplKey::of(ty).is_some_and(|key| self.impls.contains_key(&(iface, key)) || self.unknown.contains(&key));
        match ty {
            Ty::Param(i) => params.get(*i as usize).is_some_and(|bounds| bounds.contains(&iface)),
            // A rejected `impl` block may have given it this interface for any type arguments.
            Ty::Adt(id, _) if self.adt(*id).unknown_interfaces => true,
            // A map's keys implement `Eq` and `Hash` wherever its type is checked (REFERENCE
            // §4.2), so only its values decide, and a rejected key type isn't reported again.
            Ty::Adt(AdtId::MAP, args) if matches!(iface, IfaceId::EQ | IfaceId::HASH) => {
                args[1] == Ty::Never || self.implements(&args[1], iface, params)
            }
            // `Option` and `Result` implement what their type arguments do (STD.md). `Never` has
            // no values, so it implements everything as an argument.
            Ty::Adt(id, args) if self.adt(*id).derives.contains(&iface) => {
                args.iter().all(|arg| *arg == Ty::Never || self.implements(arg, iface, params))
            }
            Ty::Adt(id, _) => self.adt(*id).unknown_interfaces || by_impl(),
            // Text is ordered by code point (REFERENCE §12.3).
            Ty::Int(_) | Ty::Char | Ty::Text => {
                matches!(iface, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::HASH) || by_impl()
            }
            // `Float` has IEEE `==` built in, but no `Eq` (REFERENCE §12.2, Q22).
            Ty::Float(_) => iface == IfaceId::SHOW || by_impl(),
            Ty::Bool => matches!(iface, IfaceId::EQ | IfaceId::SHOW | IfaceId::HASH) || by_impl(),
            Ty::Unit => matches!(iface, IfaceId::EQ | IfaceId::HASH) || by_impl(),
            Ty::IoError => iface == IfaceId::SHOW || by_impl(),
            Ty::Cap(_) | Ty::Never | Ty::Error | Ty::Var(_) => false,
        }
    }

    /// Whether `ty` is `Copy`: copyable with no reach, which a capability has (REFERENCE
    /// §5.1). A record or enum is when its fields are; one already being asked about in
    /// `seen` is taken to be, since only its other fields can decide.
    fn copyable(&self, ty: &Ty, params: &[Vec<IfaceId>], seen: &mut Vec<AdtId>) -> bool {
        match ty {
            Ty::Cap(_) => false,
            Ty::Param(i) => params.get(*i as usize).is_some_and(|bounds| bounds.contains(&IfaceId::COPY)),
            // A collection holds values of its type arguments (REFERENCE §5.1).
            Ty::Adt(id, args) if self.adt(*id).is_collection() => {
                args.iter().all(|arg| self.copyable(arg, params, seen))
            }
            Ty::Adt(id, args) => {
                if args.is_empty() && seen.contains(id) {
                    return true;
                }
                seen.push(*id);
                let def = self.adt(*id);
                let copyable = (0..def.variants.len())
                    .all(|v| def.field_types(VariantIdx::new(v), args).iter().all(|f| self.copyable(f, params, seen)));
                seen.pop();
                copyable
            }
            _ => true,
        }
    }

    /// How diagnostics write `ty`, with its type arguments: `Option[Int]`. A standard
    /// library type is qualified when a record of the module has its name, so the two can be
    /// told apart.
    pub fn display<'a>(&'a self, ty: &'a Ty) -> impl fmt::Display + 'a {
        self.display_in(ty, &[])
    }

    /// How diagnostics name the record or enum `id`, qualified as [`Decls::display`] does.
    pub fn name(&self, id: AdtId) -> String {
        self.display(&Ty::adt(id)).to_string()
    }

    /// How diagnostics write variant `v` of `id`, as [`AdtDef::ctor_name`] does, with the
    /// enum's name qualified as [`Decls::display`] does it.
    pub fn ctor_name(&self, id: AdtId, v: VariantIdx) -> String {
        let def = self.adt(id);
        match def.kind {
            AdtKind::Enum if !def.bare_variants => format!("{}.{}", self.name(id), def.variants[v.index()].name),
            _ => def.ctor_name(v),
        }
    }

    /// Like [`Decls::display`], where type parameter `i` is called `names[i]`.
    pub fn display_in<'a>(&'a self, ty: &'a Ty, names: &'a [Box<str>]) -> impl fmt::Display + 'a {
        let std = move |name: &'static str, qualified: &'static str| {
            if self.adts[AdtId::BUILT_IN..].iter().any(|adt| &*adt.name == name) { qualified } else { name }
        };
        fmt::from_fn(move |f| {
            if let Ty::Adt(id, args) = ty
                && self.adt(*id).tuple
            {
                f.write_str("(")?;
                for (i, arg) in args.iter().enumerate() {
                    let sep = if i == 0 { "" } else { ", " };
                    write!(f, "{sep}{}", self.display_in(arg, names))?;
                }
                return f.write_str(")");
            }
            if let Ty::Adt(id, args) = ty
                && !args.is_empty()
            {
                write!(f, "{}[", self.adt(*id).name)?;
                for (i, arg) in args.iter().enumerate() {
                    let sep = if i == 0 { "" } else { ", " };
                    write!(f, "{sep}{}", self.display_in(arg, names))?;
                }
                return f.write_str("]");
            }
            if let Ty::Param(i) = ty
                && let Some(name) = names.get(*i as usize)
            {
                return f.write_str(name);
            }
            f.write_str(match ty {
                Ty::Int(it) => it.name(),
                Ty::Float(ft) => ft.name(),
                Ty::Bool => "Bool",
                Ty::Char => "Char",
                Ty::Text => "Text",
                Ty::Unit => "Unit",
                Ty::Never => "Never",
                Ty::Adt(AdtId::PARSE_ERROR, _) => std("ParseError", "std.text.ParseError"),
                Ty::Adt(id, _) => &self.adt(*id).name,
                Ty::IoError => std("IoError", "std.io.IoError"),
                Ty::Cap(cap) if cap.iface == IfaceId::OUT => std("Out", "std.io.Out"),
                Ty::Cap(cap) => &self.iface(cap.iface).name,
                Ty::Param(_) | Ty::Var(_) => "_",
                Ty::Error => "{unknown}",
            })
        })
    }
}

/// Which types have values (see [`Decls::inhabited`]).
pub struct Inhabited {
    adts: Vec<bool>,
}

impl Inhabited {
    pub fn has_values(&self, decls: &Decls, ty: &Ty) -> bool {
        match ty {
            Ty::Never => false,
            // An empty collection is a value whatever its type arguments.
            Ty::Adt(id, _) if decls.adt(*id).is_collection() => true,
            Ty::Adt(id, args) if !args.is_empty() => {
                let def = decls.adt(*id);
                (0..def.variants.len()).any(|v| {
                    def.field_types(VariantIdx::new(v), args).iter().all(|field| self.has_values(decls, field))
                })
            }
            Ty::Adt(id, _) => self.adts[id.index()],
            _ => true,
        }
    }
}

/// Whether a type has values, as a condition on records and enums whose answer isn't known
/// yet.
#[derive(Clone, Copy, PartialEq)]
enum Requirement {
    Met,
    Unmet,
    /// Met once this node of the [`Graph`] fires.
    Node(usize),
}

/// Conditions that become true one by one, from which follow the conditions that depend
/// on them: each node fires when all of its parts have (an `all` node) or when one has.
#[derive(Default)]
struct Graph {
    nodes: Vec<GraphNode>,
    fired: Vec<usize>,
}

struct GraphNode {
    /// For an `all` node, the parts that haven't fired; `None` for a node that fires with
    /// its first part.
    missing: Option<usize>,
    fired: bool,
    /// The nodes this one is a part of.
    parents: Vec<usize>,
}

impl Graph {
    fn node(&mut self, all: bool) -> usize {
        self.nodes.push(GraphNode { missing: all.then_some(0), fired: false, parents: Vec::new() });
        self.nodes.len() - 1
    }

    fn fire(&mut self, node: usize) {
        if !self.nodes[node].fired {
            self.nodes[node].fired = true;
            self.fired.push(node);
        }
    }

    /// Makes `parent` fire when `part` is met.
    fn implies(&mut self, part: Requirement, parent: usize) {
        match part {
            Requirement::Met => self.fire(parent),
            Requirement::Unmet => {}
            Requirement::Node(node) => {
                self.nodes[node].parents.push(parent);
                if let Some(missing) = &mut self.nodes[parent].missing {
                    *missing += 1;
                }
            }
        }
    }

    fn combine(&mut self, all: bool, parts: Vec<Requirement>) -> Requirement {
        let (decisive, neutral) =
            if all { (Requirement::Unmet, Requirement::Met) } else { (Requirement::Met, Requirement::Unmet) };
        let mut nodes = Vec::new();
        for part in parts {
            match part {
                Requirement::Node(node) => nodes.push(node),
                part if part == decisive => return decisive,
                _ => {}
            }
        }
        match nodes.as_slice() {
            [] => neutral,
            [node] => Requirement::Node(*node),
            _ => {
                let parent = self.node(all);
                for node in nodes {
                    self.implies(Requirement::Node(node), parent);
                }
                Requirement::Node(parent)
            }
        }
    }

    /// Met when every part is.
    fn all(&mut self, parts: Vec<Requirement>) -> Requirement {
        self.combine(true, parts)
    }

    /// When `ty` has values. A generic type has values when one of its variants does, for
    /// its arguments, so `Option[Never]` has `None` and `Result[Never, Never]` has none.
    fn requirement(&mut self, decls: &Decls, ty: &Ty) -> Requirement {
        match ty {
            Ty::Never => Requirement::Unmet,
            Ty::Adt(id, _) if decls.adt(*id).is_collection() => Requirement::Met,
            Ty::Adt(id, args) if !args.is_empty() => {
                let def = decls.adt(*id);
                let variants = (0..def.variants.len())
                    .map(|v| {
                        let fields = def.field_types(VariantIdx::new(v), args);
                        let parts = fields.iter().map(|field| self.requirement(decls, field)).collect();
                        self.all(parts)
                    })
                    .collect();
                self.combine(false, variants)
            }
            Ty::Adt(id, _) => Requirement::Node(id.index()),
            _ => Requirement::Met,
        }
    }

    /// Fires every node whose condition follows from those already fired.
    fn run(&mut self) {
        while let Some(node) = self.fired.pop() {
            for i in 0..self.nodes[node].parents.len() {
                let parent = self.nodes[node].parents[i];
                let ready = match &mut self.nodes[parent].missing {
                    Some(missing) => {
                        *missing -= 1;
                        *missing == 0
                    }
                    None => true,
                };
                if ready {
                    self.fire(parent);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn std_types_are_qualified_when_a_record_shares_their_name() {
        let mut decls = Decls::default();
        assert_eq!(decls.display(&Ty::IoError).to_string(), "IoError");
        assert_eq!(decls.display(&Ty::out()).to_string(), "Out");
        let own = decls.push(AdtDef::record("IoError", Vec::new()));
        assert_eq!(decls.display(&Ty::IoError).to_string(), "std.io.IoError");
        assert_eq!(decls.display(&Ty::adt(own)).to_string(), "IoError");
        assert_eq!(decls.display(&Ty::out()).to_string(), "Out");
        let parse_error = Ty::adt(AdtId::PARSE_ERROR);
        assert_eq!(decls.display(&parse_error).to_string(), "ParseError");
        decls.push(AdtDef::record("ParseError", Vec::new()));
        assert_eq!(decls.display(&parse_error).to_string(), "std.text.ParseError");
    }

    #[test]
    fn tuples_are_written_as_their_literals() {
        let mut decls = Decls::default();
        let triple = decls.tuple_ty(vec![Ty::INT, Ty::Text, Ty::option(Ty::Bool)]);
        assert_eq!(decls.display(&triple).to_string(), "(Int, Text, Option[Bool])");
        assert_eq!(decls.tuple(2), AdtId::PAIR);
        assert_eq!(decls.tuple(3), decls.tuple(3));
    }
}
