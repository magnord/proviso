//! Nominal declarations: the records, enums and interfaces of the prelude, and those of the
//! module, with the module's implementations. Questions about a type that depend on what it
//! declares, such as its name or the interfaces it implements, are answered here.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex};

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
    /// `std.pool`'s `Pool[T]` (STD.md).
    pub const POOL: AdtId = AdtId(7);
    /// `std.pool`'s `Handle[T]` (STD.md).
    pub const HANDLE: AdtId = AdtId(8);
    /// The prelude's `Ordering`, which `cmp` returns (STD.md).
    pub const ORDERING: AdtId = AdtId(9);
    /// The prelude's `Rounding`, which `to_int` takes (STD.md).
    pub const ROUNDING: AdtId = AdtId(10);
    /// `std.num`'s `ConversionError` (STD.md).
    pub const CONVERSION_ERROR: AdtId = AdtId(11);

    /// How many records and enums are declared before the module's own.
    const BUILT_IN: usize = 12;

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
    /// Ends a resource on a failure exit (REFERENCE §10, STD.md).
    pub const ABANDON: IfaceId = IfaceId(6);
    /// The operator interfaces, which only a distinct type derives (REFERENCE §4.6).
    pub const ADD: IfaceId = IfaceId(8);
    pub const SUB: IfaceId = IfaceId(9);
    pub const MUL: IfaceId = IfaceId(10);
    pub const DIV: IfaceId = IfaceId(11);
    pub const NEG: IfaceId = IfaceId(12);

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

    /// Whether it is a prelude interface whose methods come later: `Index` and the operator
    /// interfaces, whose methods STD.md doesn't declare yet.
    pub fn methods_later(self) -> bool {
        (7..13).contains(&self.0)
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
    /// How it takes `self`: borrowed, or `take self` (REFERENCE §5.2).
    pub self_mode: ParamMode,
    /// The parameters after `self`.
    pub params: Vec<(Box<str>, Ty)>,
    /// The mode of each parameter in `params`, which an implementation must repeat.
    pub modes: Vec<ParamMode>,
    pub ret: Ty,
    pub fails: Option<Ty>,
}

/// The type an `impl` is for, told apart as its values tell it at run time: by its name,
/// whatever its type arguments are. A type has at most one `impl` of an interface, so the
/// name is enough (OPEN_QUESTIONS §G, P5).
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
            Ty::Adt(id, _) => ImplKey::Adt(*id),
            _ => return None,
        })
    }
}

/// An `impl I for T`: the function of each of `I`'s methods, in `I`'s order, or `None` for
/// one the block lacks or declares differently.
pub struct ImplDef {
    pub methods: Vec<Option<usize>>,
    /// The types it applies to: its target, where the block's type parameter `i` is
    /// `Ty::Param(i)`, as in `Box[Param(0)]` for `impl[T: Show] Show for Box[T]`.
    pub target: Ty,
    /// The constraints of each of the block's type parameters, which the type arguments
    /// that match them must meet.
    pub bounds: Vec<Vec<IfaceId>>,
    /// The names of the block's type parameters, for messages.
    pub names: Vec<Box<str>>,
}

impl ImplDef {
    /// The `impl` of a type without type parameters of its own.
    pub fn plain(methods: Vec<Option<usize>>, target: Ty) -> ImplDef {
        ImplDef { methods, target, bounds: Vec::new(), names: Vec::new() }
    }
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
    /// A standard library type whose values the toolchain builds: the prelude's `List` and
    /// `Map`, and `std.pool`'s `Pool` and `Handle`. It has no variants or fields, and every
    /// one has values, as an empty collection does.
    Native,
}

pub struct AdtDef {
    pub name: Box<str>,
    pub kind: AdtKind,
    /// The number of type parameters. Fields refer to them as [`Ty::Param`].
    pub params: usize,
    /// Whether a value holds values of each type parameter, at any depth of its fields. A
    /// handle doesn't hold its element, so `Handle[T]` holds no `T`, and nor does a record
    /// whose only `T` is in a handle. Only held type arguments decide a type's kind and the
    /// interfaces it derives (REFERENCE §5.1; OPEN_QUESTIONS P5).
    pub held: Vec<bool>,
    /// A value has reach whatever the type arguments are, as `System` does (REFERENCE §9.4).
    pub reach: bool,
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
    /// Its values move instead of being copied (REFERENCE §5.1): it is declared `unique`, is
    /// `Pool`, or holds a unique value. A generic type's depends on its type arguments, so
    /// [`Decls::moves`] asks about those.
    pub unique: bool,
    /// Declared `resource record`: a base resource, which its own `abandon` ends (REFERENCE
    /// §10).
    pub resource_base: bool,
    /// It is a resource (REFERENCE §5.1): a base resource, or one that holds a resource. A
    /// resource is also [`AdtDef::unique`]. A generic type's depends on its type arguments,
    /// so [`Decls::is_resource`] asks about those.
    pub resource: bool,
    /// Declared `type Name = distinct T`: a record whose one field, `value`, holds a `T`,
    /// written `Name(v)` (REFERENCE §4.6). It may derive the operators of `T`.
    pub distinct: bool,
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
            held: Vec::new(),
            reach: false,
            bare_variants: false,
            variants: Vec::new(),
            derives: Vec::new(),
            unknown_interfaces: false,
            unknown_methods: false,
            unknown_variants: false,
            tuple: false,
            unique: false,
            resource_base: false,
            resource: false,
            distinct: false,
        }
    }

    /// The tuple of `n` elements, a record whose type parameters are its elements' types.
    fn tuple(n: usize) -> AdtDef {
        let name = format!("({})", vec!["_"; n].join(", "));
        let fields = (0..n).map(|i| FieldDef { name: i.to_string().into(), ty: Ty::Param(i as u32) }).collect();
        let mut def = AdtDef::record(&name, fields);
        def.params = n;
        def.held = vec![true; n];
        def.tuple = true;
        def.derives = vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH];
        def
    }

    /// A type the toolchain builds with `params` type parameters, which derives `derives`.
    fn native(name: &str, params: usize, derives: Vec<IfaceId>) -> AdtDef {
        let mut def = AdtDef::new(name, AdtKind::Native);
        def.params = params;
        def.held = vec![true; params];
        def.derives = derives;
        def
    }

    pub fn is_enum(&self) -> bool {
        self.kind == AdtKind::Enum
    }

    pub fn is_native(&self) -> bool {
        self.kind == AdtKind::Native
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
            AdtKind::Record | AdtKind::Native => self.name.to_string(),
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
    /// Whether its predicates read each field, by the field's index.
    pub read_fields: Vec<bool>,
    /// Declared twice, so uses of it are not checked (REFERENCE §15.1).
    pub rejected: bool,
}

impl VariantDef {
    pub fn new(name: &str, fields: Vec<FieldDef>) -> VariantDef {
        VariantDef {
            name: name.into(),
            locals: fields.len(),
            read_fields: vec![false; fields.len()],
            fields,
            preds: Vec::new(),
            rejected: false,
        }
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

/// An argument list [`Decls::is_resource`] has answered for, kept alive with the answer.
type Known = (Arc<[Ty]>, bool);

/// The answers of a walk for the type argument lists it has seen: by the type's id, the
/// interface asked about and the list's address.
type Memo = HashMap<(u32, u32, usize), bool>;

/// What a value of a type is (REFERENCE §5.1, §9.4).
#[derive(Clone, Copy, Default)]
struct Kinds {
    unique: bool,
    resource: bool,
    reach: bool,
}

impl Kinds {
    fn or(self, other: Kinds) -> Kinds {
        Kinds {
            unique: self.unique || other.unique,
            resource: self.resource || other.resource,
            reach: self.reach || other.reach,
        }
    }
}

/// Whether `ty` is a type that `pattern` describes, where `Ty::Param(i)` stands for any type,
/// the same one at each place, which `binds[i]` records (REFERENCE §4.8). `Never`, which is a
/// subtype of every type, matches anything, and so do an open variable and an unknown type,
/// which could be anything.
pub fn matches_target(pattern: &Ty, ty: &Ty, binds: &mut [Option<Ty>]) -> bool {
    matches_in(pattern, ty, binds, &mut HashMap::new())
}

/// [`matches_target`], where `joins` holds the joins of the argument lists already joined.
fn matches_in(pattern: &Ty, ty: &Ty, binds: &mut [Option<Ty>], joins: &mut Joins) -> bool {
    match (pattern, ty) {
        (Ty::Param(i), ty) => match &binds[*i as usize] {
            Some(bound) => {
                let agree = compatible(bound, ty, &mut HashSet::new());
                if agree {
                    binds[*i as usize] = Some(join(bound, ty, joins));
                }
                agree
            }
            None => {
                binds[*i as usize] = Some(ty.clone());
                true
            }
        },
        (_, Ty::Never | Ty::Var(_) | Ty::Error) | (Ty::Error, _) => true,
        (Ty::Adt(a, pargs), Ty::Adt(b, targs)) => {
            a == b
                && pargs.len() == targs.len()
                && pargs.iter().zip(targs.iter()).all(|(p, t)| matches_in(p, t, binds, joins))
        }
        (pattern, ty) => pattern == ty,
    }
}

/// The type that two [`compatible`] types both describe, which takes each part where one of
/// them has `Never` from the other, so `Pair[Option[Never], Int]` and `Pair[Option[Int], Int]`
/// join as the second. An open variable or an unknown part stays as it is. `joins` holds
/// the joins of the argument lists already joined, by address, so equal types that share no
/// part cost each pair of parts once.
fn join(a: &Ty, b: &Ty, joins: &mut Joins) -> Ty {
    match (a, b) {
        (Ty::Never, other) => other.clone(),
        (Ty::Adt(x, xs), Ty::Adt(_, ys)) if !Arc::ptr_eq(xs, ys) => {
            let key = (Arc::as_ptr(xs) as *const Ty as usize, Arc::as_ptr(ys) as *const Ty as usize);
            if let Some(joined) = joins.get(&key) {
                return joined.0.clone();
            }
            let joined = Ty::Adt(*x, xs.iter().zip(ys.iter()).map(|(x, y)| join(x, y, joins)).collect());
            joins.insert(key, (joined.clone(), xs.clone(), ys.clone()));
            joined
        }
        (a, _) => a.clone(),
    }
}

/// The joins of pairs of argument lists, by their addresses, with the lists, which keeps the
/// addresses from being reused.
type Joins = HashMap<(usize, usize), (Ty, Arc<[Ty]>, Arc<[Ty]>)>;

/// Whether `a` and `b` are the same type, where `Never`, an open variable or an unknown type
/// on either side agrees with anything. `seen` holds the pairs of argument lists already
/// found to agree, by address, so types that share parts cost each pair once.
fn compatible(a: &Ty, b: &Ty, seen: &mut HashSet<(usize, usize)>) -> bool {
    match (a, b) {
        (Ty::Never | Ty::Var(_) | Ty::Error, _) | (_, Ty::Never | Ty::Var(_) | Ty::Error) => true,
        (Ty::Adt(x, xs), Ty::Adt(y, ys)) => {
            let key = (Arc::as_ptr(xs) as *const Ty as usize, Arc::as_ptr(ys) as *const Ty as usize);
            x == y
                && xs.len() == ys.len()
                && (key.0 == key.1
                    || seen.contains(&key)
                    || (xs.iter().zip(ys.iter()).all(|(x, y)| compatible(x, y, seen)) && seen.insert(key)))
        }
        (Ty::Fn(xm, xs), Ty::Fn(ym, ys)) => {
            xm == ym && xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| compatible(x, y, seen))
        }
        (a, b) => a == b,
    }
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
    /// The targets of `impl` blocks rejected because their type head had an `impl` of the
    /// interface already, with the number of type parameters each block declares. Each may
    /// have been meant for the types it matches, with other constraints than the accepted
    /// one, so their uses aren't reported (§15.1).
    taken: HashMap<(IfaceId, ImplKey), Vec<(Ty, usize)>>,
    /// Interfaces that a rejected `impl` block for every type, as `impl[T] I for T`, may have
    /// given every type, so their uses aren't reported (§15.1).
    everywhere: HashSet<IfaceId>,
    /// Whether the module declares a resource, without which no type is one.
    any_resource: bool,
    /// The argument lists [`Decls::is_resource`] has answered for, by address, so a deep type
    /// such as a list of lists costs each level once over the whole program. Each entry keeps
    /// its list alive, so the address isn't reused.
    resource_args: Mutex<HashMap<(u32, usize), Known>>,
}

impl Default for Decls {
    /// The prelude, with each declaration at the id its constant names.
    fn default() -> Decls {
        let mut system = AdtDef::record("System", vec![FieldDef { name: "stdout".into(), ty: Ty::out() }]);
        system.reach = true;
        // As STD.md declares them, so `Some` comes before `None`.
        let generic = |name: &str, params: usize, variants: [(&str, Option<(&str, u32)>); 2]| {
            let mut def = AdtDef::enumeration(name);
            def.params = params;
            def.held = vec![true; params];
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
        // An enum whose variants have no fields, which derives `derives`.
        let plain = |name: &str, variants: &[&str], derives: Vec<IfaceId>| {
            let mut def = AdtDef::enumeration(name);
            def.derives = derives;
            def.variants.extend(variants.iter().map(|variant| VariantDef::new(variant, Vec::new())));
            def
        };
        let parse_error = plain("ParseError", &["Empty", "Invalid", "OutOfRange"], vec![IfaceId::EQ, IfaceId::SHOW]);
        // Ordered as declared, so `Less < Equal < Greater` (STD.md).
        let ordering = plain(
            "Ordering",
            &["Less", "Equal", "Greater"],
            vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH],
        );
        let rounding = plain(
            "Rounding",
            &["TowardZero", "TowardNegative", "TowardPositive", "NearestEven", "NearestAway"],
            vec![IfaceId::EQ, IfaceId::SHOW, IfaceId::HASH],
        );
        let conversion_error =
            plain("ConversionError", &["OutOfRange", "NotANumber"], vec![IfaceId::EQ, IfaceId::SHOW]);
        let method = |name: &str, params: Vec<(&str, Ty)>, ret: Ty| IfaceMethod {
            name: name.into(),
            self_mode: ParamMode::Borrow,
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
                    "Ord" => vec![method("cmp", vec![("other", Ty::Param(0))], Ty::adt(AdtId::ORDERING))],
                    "Show" => vec![method("show", vec![], Ty::Text)],
                    // `abandon` takes `take self` and can't fail (STD.md).
                    "Abandon" => {
                        vec![IfaceMethod { self_mode: ParamMode::Take, ..method("abandon", vec![], Ty::Unit) }]
                    }
                    _ => Vec::new(),
                };
                IfaceDef { name: name.into(), methods, incomplete: false }
            })
            .collect();
        // A list and a map implement what their type arguments do (STD.md).
        let all = || vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW, IfaceId::HASH];
        let (list, map) = (AdtDef::native("List", 1, all()), AdtDef::native("Map", 2, all()));
        // A pool implements nothing and is unique, and a handle implements `Eq` and `Hash`
        // whatever its element type (STD.md, REFERENCE §5.5).
        let mut pool = AdtDef::native("Pool", 1, Vec::new());
        pool.unique = true;
        let mut handle = AdtDef::native("Handle", 1, vec![IfaceId::EQ, IfaceId::HASH]);
        handle.held = vec![false];
        let adts = vec![
            system,
            option,
            result,
            parse_error,
            AdtDef::tuple(2),
            list,
            map,
            pool,
            handle,
            ordering,
            rounding,
            conversion_error,
        ];
        debug_assert_eq!(adts.len(), AdtId::BUILT_IN);
        let tuples = HashMap::from([(2, AdtId::PAIR)]);
        Decls {
            adts,
            ifaces,
            impls: HashMap::new(),
            tuples,
            unknown_tuples: false,
            unknown: HashSet::new(),
            taken: HashMap::new(),
            everywhere: HashSet::new(),
            any_resource: false,
            resource_args: Mutex::default(),
        }
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

    /// Replaces the type of every field of a record or enum, and of every parameter, result
    /// and error of an interface's method, by what `f` makes of it.
    pub fn rewrite_types(&mut self, f: &mut dyn FnMut(&Decls, &Ty) -> Ty) {
        for a in 0..self.adts.len() {
            for v in 0..self.adts[a].variants.len() {
                for i in 0..self.adts[a].variants[v].fields.len() {
                    let ty = f(self, &self.adts[a].variants[v].fields[i].ty);
                    self.adts[a].variants[v].fields[i].ty = ty;
                }
            }
        }
        for k in 0..self.ifaces.len() {
            for j in 0..self.ifaces[k].methods.len() {
                for i in 0..self.ifaces[k].methods[j].params.len() {
                    let ty = f(self, &self.ifaces[k].methods[j].params[i].1);
                    self.ifaces[k].methods[j].params[i].1 = ty;
                }
                let ret = f(self, &self.ifaces[k].methods[j].ret);
                self.ifaces[k].methods[j].ret = ret;
                if let Some(fails) = self.ifaces[k].methods[j].fails.clone() {
                    self.ifaces[k].methods[j].fails = Some(f(self, &fails));
                }
            }
        }
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

    /// Notes that an `impl` block of `iface` for `target`, with `params` type parameters, was
    /// rejected because `key`, its type head, has one already, for that target or another.
    pub fn mark_taken(&mut self, iface: IfaceId, key: ImplKey, target: Ty, params: usize) {
        self.taken.entry((iface, key)).or_default().push((target, params));
    }

    /// Notes that a rejected `impl` block for every type implements `iface`.
    pub fn mark_everywhere(&mut self, iface: IfaceId) {
        self.everywhere.insert(iface);
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
    /// nothing about it is reported (REFERENCE §15.1). Whether a generic type has values
    /// depends only on whether its type arguments do, so each generic type is asked once per
    /// combination of those answers that a use needs (OPEN_QUESTIONS P5).
    pub fn inhabited(&self) -> Inhabited {
        let mut graph = Graph::default();
        let mut instances = Instances::default();
        // Node `i` is record or enum `i`, which has values if one of its variants does.
        for _ in &self.adts {
            graph.node(false);
        }
        for (a, def) in self.adts.iter().enumerate() {
            // A generic type's node is one per combination of its type arguments' answers.
            if def.params > 0 {
                continue;
            }
            for variant in &def.variants {
                let fields =
                    variant.fields.iter().map(|f| graph.requirement(self, &f.ty, &[], &mut instances)).collect();
                let variant = graph.all(fields);
                graph.implies(variant, a);
            }
            if def.unknown_variants {
                graph.fire(a);
            }
        }
        graph.expand(self, &mut instances);
        graph.run();
        Inhabited { graph: RefCell::new((graph, instances)), applied: RefCell::default() }
    }

    /// The type arguments of a value of `id` that it holds (see [`AdtDef::held`]).
    fn held_args<'t>(&'t self, id: AdtId, args: &'t [Ty]) -> impl Iterator<Item = &'t Ty> + 't {
        let held = &self.adt(id).held;
        args.iter().enumerate().filter(move |(i, _)| held.get(*i).copied().unwrap_or(true)).map(|(_, arg)| arg)
    }

    /// Whether `ty` implements `iface`: built in, derived (STD.md) or by an `impl`. Type
    /// parameter `i` implements the interfaces `params[i]` lists. An unknown type implements
    /// nothing, so callers decide whether it is worth reporting.
    pub fn implements(&self, ty: &Ty, iface: IfaceId, params: &[Vec<IfaceId>]) -> bool {
        self.implements_in(ty, iface, params, &mut HashMap::new())
    }

    /// [`Decls::implements`], where `memo` holds the answers for the type argument lists
    /// already asked about, by address, so a type that shares its parts, as `(t, t)` does,
    /// costs each part once.
    fn implements_in(&self, ty: &Ty, iface: IfaceId, params: &[Vec<IfaceId>], memo: &mut Memo) -> bool {
        if iface == IfaceId::COPY {
            return self.copyable(ty, params, memo);
        }
        // Every resource type implements `Abandon`: a base resource by its `impl`, which
        // E0309 asks for, and an aggregate by abandoning what it holds (REFERENCE §10).
        if iface == IfaceId::ABANDON && self.is_resource(ty) || self.everywhere.contains(&iface) {
            return true;
        }
        match ty {
            Ty::Param(i) => params.get(*i as usize).is_some_and(|bounds| bounds.contains(&iface)),
            // A rejected `impl` block may have given it this interface for any type arguments.
            Ty::Adt(id, _) if self.adt(*id).unknown_interfaces => true,
            // A handle holds no element, so its element type doesn't decide (STD.md).
            Ty::Adt(AdtId::HANDLE, _) => {
                matches!(iface, IfaceId::EQ | IfaceId::HASH) || self.by_impl(ty, iface, params, memo)
            }
            // A map's keys implement `Eq` and `Hash` wherever its type is checked (REFERENCE
            // §4.2), so only its values decide, and a rejected key type isn't reported again.
            Ty::Adt(AdtId::MAP, args) if matches!(iface, IfaceId::EQ | IfaceId::HASH) => {
                args[1] == Ty::Never || self.implements_in(&args[1], iface, params, memo)
            }
            Ty::Adt(id, args) => {
                let key = (id.0, iface.0, Arc::as_ptr(args) as *const Ty as usize);
                if let Some(&known) = memo.get(&key) {
                    return known;
                }
                // A derived interface holds when the type arguments the type holds implement
                // it (STD.md; OPEN_QUESTIONS P5). `Never` has no values, so it implements
                // everything as an argument.
                // A rejected `impl` block may give it for the arguments the derive doesn't.
                let known = if self.adt(*id).derives.contains(&iface) {
                    self.held_args(*id, args)
                        .all(|arg| *arg == Ty::Never || self.implements_in(arg, iface, params, memo))
                        || self.by_impl(ty, iface, params, memo)
                } else {
                    self.by_impl(ty, iface, params, memo)
                };
                memo.insert(key, known);
                known
            }
            // Text is ordered by code point (REFERENCE §12.3).
            Ty::Int(_) | Ty::Char | Ty::Text => {
                matches!(iface, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW | IfaceId::HASH)
                    || self.by_impl(ty, iface, params, memo)
            }
            // `Float` has IEEE `==` built in, but no `Eq` (REFERENCE §12.2, Q22).
            Ty::Float(_) => iface == IfaceId::SHOW || self.by_impl(ty, iface, params, memo),
            Ty::Bool => {
                matches!(iface, IfaceId::EQ | IfaceId::SHOW | IfaceId::HASH) || self.by_impl(ty, iface, params, memo)
            }
            Ty::Unit => matches!(iface, IfaceId::EQ | IfaceId::HASH) || self.by_impl(ty, iface, params, memo),
            Ty::IoError => iface == IfaceId::SHOW || self.by_impl(ty, iface, params, memo),
            // A function value implements nothing, so it isn't compared or shown (OPEN_QUESTIONS P5).
            Ty::Cap(_) | Ty::Fn(..) | Ty::Never | Ty::Error | Ty::Var(_) => false,
        }
    }

    /// Whether an `impl` of `iface` applies to `ty`: one for its name whose target matches
    /// it, with type arguments that meet the block's constraints (REFERENCE §4.9). A
    /// rejected `impl` block for it may have been one.
    fn by_impl(&self, ty: &Ty, iface: IfaceId, params: &[Vec<IfaceId>], memo: &mut Memo) -> bool {
        let Some(key) = ImplKey::of(ty) else { return false };
        let taken = self.taken.get(&(iface, key)).map_or(&[][..], |targets| targets.as_slice());
        if self.unknown.contains(&key)
            || taken.iter().any(|(target, params)| matches_target(target, ty, &mut vec![None; *params]))
        {
            return true;
        }
        let Some(def) = self.impls.get(&(iface, key)) else { return false };
        let mut binds = vec![None; def.bounds.len()];
        matches_target(&def.target, ty, &mut binds)
            && binds.iter().zip(&def.bounds).all(|(bind, bounds)| match bind {
                Some(Ty::Never | Ty::Var(_) | Ty::Error) | None => true,
                Some(arg) => bounds.iter().all(|&b| self.implements_in(arg, b, params, memo)),
            })
    }

    /// The `impl` of `iface` for `ty`'s name, whose target `ty` matches, with the type
    /// arguments it gives the block's parameters, whatever they implement.
    /// Whether `iface` has an `impl` for some instance of `ty`'s type head, as
    /// `impl Show for Box[Int]` is for `Box`.
    pub fn has_impl_head(&self, iface: IfaceId, ty: &Ty) -> bool {
        ImplKey::of(ty).is_some_and(|key| self.impls.contains_key(&(iface, key)))
    }

    pub fn impl_for(&self, iface: IfaceId, ty: &Ty) -> Option<(&ImplDef, Vec<Option<Ty>>)> {
        let def = self.impls.get(&(iface, ImplKey::of(ty)?))?;
        let mut binds = vec![None; def.bounds.len()];
        matches_target(&def.target, ty, &mut binds).then_some((def, binds))
    }

    /// Whether copying a value of `ty` needs a type parameter in it to be `Copy` (REFERENCE
    /// §4.8): it moves, or isn't `Copy`, only because one may lack `Copy`. So `Box[T]`, which
    /// may hold a unique value, and `Phantom[T]`, which may have reach through `T`, both need
    /// `T: Copy`.
    pub fn copy_needs_param(&self, ty: &Ty, params: &[Vec<IfaceId>]) -> bool {
        let copy: Vec<Vec<IfaceId>> =
            params.iter().map(|bounds| bounds.iter().copied().chain([IfaceId::COPY]).collect()).collect();
        (self.moves(ty, params) && !self.moves(ty, &copy))
            || (!self.implements(ty, IfaceId::COPY, params) && self.implements(ty, IfaceId::COPY, &copy))
    }

    /// [`Decls::moves`], where `memo` holds what each type argument list already walked gave,
    /// by its type's id and its address, so a walk over many types that share parts costs
    /// each part once. The types must outlive `memo`.
    pub fn moves_memo(&self, ty: &Ty, params: &[Vec<IfaceId>], memo: &mut HashMap<(u32, usize), bool>) -> bool {
        match ty {
            Ty::Param(i) => !params.get(*i as usize).is_some_and(|bounds| bounds.contains(&IfaceId::COPY)),
            Ty::Adt(id, _) if self.adt(*id).unique => true,
            Ty::Adt(id, args) if !args.is_empty() => {
                let key = (id.0, Arc::as_ptr(args) as *const Ty as usize);
                if let Some(&moves) = memo.get(&key) {
                    return moves;
                }
                let moves = self.held_args(*id, args).any(|arg| self.moves_memo(arg, params, memo));
                memo.insert(key, moves);
                moves
            }
            _ => false,
        }
    }

    /// Whether values of `ty` move instead of being copied (REFERENCE §5.1): it is unique, or
    /// holds a unique value, or is a type parameter that `params` doesn't give `Copy`, which
    /// may stand for a unique type (§4.8). A generic type moves when it is declared unique,
    /// holds a unique value whatever its type arguments are, or when a type argument it holds
    /// moves.
    pub fn moves(&self, ty: &Ty, params: &[Vec<IfaceId>]) -> bool {
        self.moves_memo(ty, params, &mut HashMap::new())
    }

    /// Whether `ty` is a resource (REFERENCE §5.1): a base resource, or an aggregate that holds
    /// one, such as `Option[File]`, `List[File]` or a generic record of one. A type parameter
    /// isn't, since a resource can't be a type argument of a generic function yet
    /// (OPEN_QUESTIONS P5).
    pub fn is_resource(&self, ty: &Ty) -> bool {
        match ty {
            _ if !self.any_resource => false,
            Ty::Adt(id, _) if self.adt(*id).resource => true,
            Ty::Adt(id, args) if !args.is_empty() => {
                let key = (id.0, Arc::as_ptr(args) as *const Ty as usize);
                let cache = || self.resource_args.lock().unwrap_or_else(|e| e.into_inner());
                if let Some((_, known)) = cache().get(&key) {
                    return *known;
                }
                let known = self.held_args(*id, args).any(|arg| self.is_resource(arg));
                cache().insert(key, (args.clone(), known));
                known
            }
            _ => false,
        }
    }

    /// Whether a value of `ty` has reach (REFERENCE §9.4): it is a capability, or holds one,
    /// as `System` and a record with an `Out` field do. A handle refers to its pool's element
    /// without holding it.
    pub fn has_reach(&self, ty: &Ty) -> bool {
        self.reach_in(ty, &mut HashMap::new())
    }

    /// Whether a value of `ty` may have reach, where type parameter `i` has none when
    /// `params[i]` makes it `Copy`.
    fn may_reach(&self, ty: &Ty, params: &[Vec<IfaceId>], memo: &mut HashMap<(u32, usize), bool>) -> bool {
        match ty {
            Ty::Param(i) => !params.get(*i as usize).is_some_and(|bounds| bounds.contains(&IfaceId::COPY)),
            Ty::Adt(AdtId::HANDLE, _) => false,
            Ty::Adt(id, args) if !args.is_empty() && !self.adt(*id).reach => {
                let key = (id.0, Arc::as_ptr(args) as *const Ty as usize);
                if let Some(&reach) = memo.get(&key) {
                    return reach;
                }
                let reach = args.iter().any(|arg| self.may_reach(arg, params, memo));
                memo.insert(key, reach);
                reach
            }
            ty => self.reach_in(ty, memo),
        }
    }

    fn reach_in(&self, ty: &Ty, memo: &mut HashMap<(u32, usize), bool>) -> bool {
        match ty {
            Ty::Cap(_) => true,
            Ty::Adt(id, _) if self.adt(*id).reach => true,
            // A handle is `Copy` whatever its element is (STD.md).
            Ty::Adt(AdtId::HANDLE, _) => false,
            Ty::Adt(id, args) if !args.is_empty() => {
                let key = (id.0, Arc::as_ptr(args) as *const Ty as usize);
                if let Some(&reach) = memo.get(&key) {
                    return reach;
                }
                // Reach comes through every type argument, held or not (REFERENCE §5.1).
                let reach = args.iter().any(|arg| self.reach_in(arg, memo));
                memo.insert(key, reach);
                reach
            }
            _ => false,
        }
    }

    /// Settles which type parameters each record and enum holds, and which are unique,
    /// resources or have reach whatever their type arguments are (REFERENCE §5.1), once every
    /// field's type is known. A field's type may hold a type declared later, so each type is
    /// settled again whenever one it mentions changes, until nothing does.
    pub fn settle_kinds(&mut self) {
        let module = AdtId::BUILT_IN..self.adts.len();
        // Which records and enums mention each one in a field.
        let mut held_by: HashMap<usize, Vec<usize>> = HashMap::new();
        for a in module.clone() {
            let mut parts = Vec::new();
            for field in self.adts[a].variants.iter().flat_map(|v| &v.fields) {
                mentioned(&field.ty, &mut parts);
            }
            parts.sort_unstable();
            parts.dedup();
            for part in parts {
                held_by.entry(part).or_default().push(a);
            }
            let def = &mut self.adts[a];
            if def.held.len() != def.params {
                def.held = vec![false; def.params];
            }
            def.resource |= def.resource_base;
        }
        self.any_resource = module.clone().any(|a| self.adts[a].resource_base);
        let mut queue: Vec<usize> = module.clone().rev().collect();
        let mut queued = vec![false; self.adts.len()];
        for &a in &queue {
            queued[a] = true;
        }
        while let Some(a) = queue.pop() {
            queued[a] = false;
            let def = &self.adts[a];
            let mut held = def.held.clone();
            let mut kind = Kinds { unique: def.unique, resource: def.resource, reach: def.reach };
            for field in def.variants.iter().flat_map(|v| &v.fields) {
                kind = kind.or(self.base_kind(&field.ty, &mut held));
            }
            let def = &mut self.adts[a];
            if held == def.held && kind.unique == def.unique && kind.resource == def.resource && kind.reach == def.reach
            {
                continue;
            }
            def.held = held;
            (def.unique, def.resource, def.reach) = (kind.unique || kind.resource, kind.resource, kind.reach);
            for &holder in held_by.get(&a).map_or(&[][..], Vec::as_slice) {
                if !queued[holder] {
                    queued[holder] = true;
                    queue.push(holder);
                }
            }
        }
        self.resource_args.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }

    /// What a value of `ty`, written in a field, is whatever the type parameters are, from
    /// what is settled so far. Marks each type parameter it holds in `held`.
    fn base_kind(&self, ty: &Ty, held: &mut [bool]) -> Kinds {
        match ty {
            Ty::Param(i) => {
                if let Some(slot) = held.get_mut(*i as usize) {
                    *slot = true;
                }
                Kinds::default()
            }
            Ty::Cap(_) => Kinds { reach: true, ..Kinds::default() },
            Ty::Adt(id, args) => {
                let def = self.adt(*id);
                let mut kind = Kinds { unique: def.unique, resource: def.resource, reach: def.reach };
                for (i, arg) in args.iter().enumerate() {
                    if def.held.get(i).copied().unwrap_or(false) {
                        kind = kind.or(self.base_kind(arg, held));
                    } else if *id != AdtId::HANDLE {
                        // A type argument it doesn't hold still gives it reach (REFERENCE §5.1),
                        // but a handle's never does (STD.md).
                        kind.reach |= self.base_kind(arg, &mut []).reach;
                    }
                }
                kind
            }
            _ => Kinds::default(),
        }
    }

    /// Whether `ty` is `Copy`: copyable with no reach, which a capability has (REFERENCE
    /// §5.1). A unique type isn't copyable, and a generic one is when the type arguments it
    /// holds are.
    fn copyable(&self, ty: &Ty, params: &[Vec<IfaceId>], memo: &mut Memo) -> bool {
        match ty {
            Ty::Cap(_) => false,
            Ty::Param(i) => params.get(*i as usize).is_some_and(|bounds| bounds.contains(&IfaceId::COPY)),
            Ty::Adt(id, _) if self.adt(*id).unique || self.adt(*id).reach => false,
            Ty::Adt(id, args) if !args.is_empty() => {
                let key = (id.0, IfaceId::COPY.0, Arc::as_ptr(args) as *const Ty as usize);
                if let Some(&known) = memo.get(&key) {
                    return known;
                }
                // A type argument it doesn't hold still gives it reach (REFERENCE §5.1), but a
                // handle's never does (STD.md).
                let held = &self.adt(*id).held;
                let known = args.iter().enumerate().all(|(i, arg)| match held.get(i).copied().unwrap_or(true) {
                    true => self.copyable(arg, params, memo),
                    false => *id == AdtId::HANDLE || !self.may_reach(arg, params, &mut HashMap::new()),
                });
                memo.insert(key, known);
                known
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

    /// Like [`Decls::display`], where type parameter `i` is called `names[i]`. A type with
    /// more than [`DISPLAY_BUDGET`] parts is written in part, with `…` for the rest, so a
    /// type that doubles at each level gives a short message (issue #18).
    pub fn display_in<'a>(&'a self, ty: &'a Ty, names: &'a [Box<str>]) -> impl fmt::Display + 'a {
        fmt::from_fn(move |f| self.write_ty(f, ty, names, &Cell::new(DISPLAY_BUDGET)))
    }

    /// Writes `ty` as [`Decls::display_in`] does, spending one of `budget` on each part.
    fn write_ty(&self, f: &mut fmt::Formatter, ty: &Ty, names: &[Box<str>], budget: &Cell<usize>) -> fmt::Result {
        if budget.get() == 0 {
            return f.write_str("…");
        }
        budget.set(budget.get() - 1);
        let std = |name: &'static str, qualified: &'static str| {
            if self.adts[AdtId::BUILT_IN..].iter().any(|adt| &*adt.name == name) { qualified } else { name }
        };
        let list = |f: &mut fmt::Formatter, args: &[Ty]| -> fmt::Result {
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                if budget.get() == 0 {
                    return f.write_str("…");
                }
                self.write_ty(f, arg, names, budget)?;
            }
            Ok(())
        };
        if let Ty::Adt(id, args) = ty
            && self.adt(*id).tuple
        {
            f.write_str("(")?;
            list(f, args)?;
            return f.write_str(")");
        }
        if let Ty::Adt(id, args) = ty
            && !args.is_empty()
        {
            let name = match *id {
                AdtId::POOL => std("Pool", "std.pool.Pool"),
                AdtId::HANDLE => std("Handle", "std.pool.Handle"),
                _ => &self.adt(*id).name,
            };
            write!(f, "{name}[")?;
            list(f, args)?;
            return f.write_str("]");
        }
        if let Some((modes, ret, fails, params)) = ty.fn_parts() {
            f.write_str("fn(")?;
            for (i, (mode, param)) in modes.iter().zip(params).enumerate() {
                let sep = if i == 0 { "" } else { ", " };
                let mode = match mode {
                    ParamMode::Inout => "inout ",
                    ParamMode::InoutPartial => "inout(partial) ",
                    ParamMode::Take => "take ",
                    ParamMode::Keep => "keep ",
                    ParamMode::Borrow => "",
                };
                write!(f, "{sep}{mode}")?;
                self.write_ty(f, param, names, budget)?;
            }
            f.write_str(")")?;
            if *ret != Ty::Unit {
                f.write_str(" -> ")?;
                self.write_ty(f, ret, names, budget)?;
            }
            if *fails != Ty::Never {
                f.write_str(" fails ")?;
                self.write_ty(f, fails, names, budget)?;
            }
            return Ok(());
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
            Ty::Adt(AdtId::CONVERSION_ERROR, _) => std("ConversionError", "std.num.ConversionError"),
            Ty::Adt(id, _) => &self.adt(*id).name,
            Ty::IoError => std("IoError", "std.io.IoError"),
            Ty::Cap(cap) if cap.iface == IfaceId::OUT => std("Out", "std.io.Out"),
            Ty::Cap(cap) => &self.iface(cap.iface).name,
            Ty::Param(_) | Ty::Var(_) => "_",
            Ty::Error => "{unknown}",
            Ty::Fn(..) => unreachable!("written above"),
        })
    }
}

/// How many parts of a type a diagnostic writes before it writes `…` for the rest.
pub const DISPLAY_BUDGET: usize = 64;

/// Pushes the index of each record and enum that a value of `ty` holds, at any depth, to
/// `found`. A handle holds no element (STD.md).
fn mentioned(ty: &Ty, found: &mut Vec<usize>) {
    if let Ty::Adt(id, args) = ty
        && *id != AdtId::HANDLE
    {
        found.push(id.index());
        for arg in args.iter() {
            mentioned(arg, found);
        }
    }
}

/// Which types have values (see [`Decls::inhabited`]).
pub struct Inhabited {
    /// The conditions, settled so far, with the generic types asked about. A use may ask
    /// about a generic type with type arguments nothing asked about before, which extends
    /// them. Those it adds depend on nothing settled before, so the answers settled stay.
    graph: RefCell<(Graph, Instances)>,
    /// Whether each record or enum with type arguments asked about so far has values, by its
    /// id and the address of its argument list. A type never changes, so the answer stays,
    /// and the entry holds the list so its address isn't reused. A type that shares a part,
    /// as `(t, t)` does, is then asked about once per part, not once per leaf of its tree.
    applied: RefCell<Applied>,
}

type Applied = HashMap<(AdtId, usize), (Arc<[Ty]>, bool)>;

impl Inhabited {
    pub fn has_values(&self, decls: &Decls, ty: &Ty) -> bool {
        match ty {
            Ty::Never => false,
            // An empty collection is a value whatever its type arguments, and so is a handle.
            Ty::Adt(id, _) if decls.adt(*id).is_native() => true,
            Ty::Adt(id, args) if !args.is_empty() => {
                let key = (*id, Arc::as_ptr(args) as *const Ty as usize);
                if let Some((_, answer)) = self.applied.borrow().get(&key) {
                    return *answer;
                }
                let bits: Box<[bool]> = args.iter().map(|arg| self.has_values(decls, arg)).collect();
                let mut graph = self.graph.borrow_mut();
                let (graph, instances) = &mut *graph;
                let node = graph.instance(*id, bits, instances);
                graph.expand(decls, instances);
                graph.run();
                let answer = graph.nodes[node].fired;
                self.applied.borrow_mut().insert(key, (args.clone(), answer));
                answer
            }
            Ty::Adt(id, _) => self.graph.borrow().0.nodes[id.index()].fired,
            _ => true,
        }
    }
}

/// The generic types the [`Graph`] has a node for: each by its id and whether each of its
/// type arguments has values, with those whose variants aren't in the graph yet.
#[derive(Default)]
struct Instances {
    nodes: HashMap<(AdtId, Box<[bool]>), usize>,
    pending: Vec<(AdtId, Box<[bool]>, usize)>,
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

    /// `part` as it is now: a node that has fired is met.
    fn settled(&self, part: Requirement) -> Requirement {
        match part {
            Requirement::Node(node) if self.nodes[node].fired => Requirement::Met,
            part => part,
        }
    }

    /// Makes `parent` fire when `part` is met.
    fn implies(&mut self, part: Requirement, parent: usize) {
        match self.settled(part) {
            Requirement::Met => match &mut self.nodes[parent].missing {
                Some(_) => {}
                None => self.fire(parent),
            },
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
            match self.settled(part) {
                Requirement::Node(node) => nodes.push(node),
                part if part == decisive => return decisive,
                _ => {}
            }
        }
        nodes.sort_unstable();
        nodes.dedup();
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

    /// When `ty`, written where type parameter `i` has values when `params[i]` says so, has
    /// values. A generic type has values when one of its variants does for its arguments, so
    /// `Option[Never]` has `None` and `Result[Never, Never]` has none. That depends only on
    /// which of its type arguments have values, so a type argument whose answer isn't known
    /// yet, such as a record of the module, splits the condition by its answer.
    fn requirement(&mut self, decls: &Decls, ty: &Ty, params: &[bool], instances: &mut Instances) -> Requirement {
        match ty {
            Ty::Never => Requirement::Unmet,
            Ty::Param(i) => match params.get(*i as usize) {
                Some(false) => Requirement::Unmet,
                _ => Requirement::Met,
            },
            Ty::Adt(id, _) if decls.adt(*id).is_native() || decls.adt(*id).unknown_variants => Requirement::Met,
            Ty::Adt(id, args) if !args.is_empty() => {
                let parts: Vec<Requirement> =
                    args.iter().map(|arg| self.requirement(decls, arg, params, instances)).collect();
                let mut open: Vec<usize> = (parts.iter())
                    .filter_map(|part| match part {
                        Requirement::Node(node) => Some(*node),
                        _ => None,
                    })
                    .collect();
                open.sort_unstable();
                open.dedup();
                // Each answer of the open arguments is a case. Many open arguments would be
                // too many cases, so the type is taken to have values, which asks for an arm
                // rather than leaving one out.
                if open.len() > 8 {
                    return Requirement::Met;
                }
                let cases = (0..1usize << open.len())
                    .map(|case| {
                        let holds = |node: usize| case & (1 << open.iter().position(|&n| n == node).unwrap_or(0)) != 0;
                        let bits = (parts.iter())
                            .map(|part| match part {
                                Requirement::Met => true,
                                Requirement::Unmet => false,
                                Requirement::Node(node) => holds(*node),
                            })
                            .collect();
                        let mut conditions: Vec<Requirement> =
                            open.iter().filter(|&&node| holds(node)).map(|&node| Requirement::Node(node)).collect();
                        conditions.push(Requirement::Node(self.instance(*id, bits, instances)));
                        self.all(conditions)
                    })
                    .collect();
                self.combine(false, cases)
            }
            Ty::Adt(id, _) => Requirement::Node(id.index()),
            _ => Requirement::Met,
        }
    }

    /// The node of generic type `id` whose type arguments have values as `bits` says.
    fn instance(&mut self, id: AdtId, bits: Box<[bool]>, instances: &mut Instances) -> usize {
        if let Some(&node) = instances.nodes.get(&(id, bits.clone())) {
            return node;
        }
        let node = self.node(false);
        instances.nodes.insert((id, bits.clone()), node);
        instances.pending.push((id, bits, node));
        node
    }

    /// Adds the variants of each generic type's node that lacks them, and of those they
    /// need in turn.
    fn expand(&mut self, decls: &Decls, instances: &mut Instances) {
        while let Some((id, bits, node)) = instances.pending.pop() {
            let def = decls.adt(id);
            for variant in &def.variants {
                let fields = variant.fields.iter().map(|f| self.requirement(decls, &f.ty, &bits, instances)).collect();
                let variant = self.all(fields);
                self.implies(variant, node);
            }
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
