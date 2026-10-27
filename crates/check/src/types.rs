//! The types the checker assigns.

use std::collections::HashMap;
use std::sync::Arc;

use proviso_syntax::ast::ParamMode;

use crate::decls::{AdtId, IfaceId};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntTy {
    pub fn min(self) -> i128 {
        match self {
            IntTy::I8 => i8::MIN.into(),
            IntTy::I16 => i16::MIN.into(),
            IntTy::I32 => i32::MIN.into(),
            IntTy::I64 => i64::MIN.into(),
            IntTy::U8 | IntTy::U16 | IntTy::U32 | IntTy::U64 => 0,
        }
    }

    pub fn max(self) -> i128 {
        match self {
            IntTy::I8 => i8::MAX.into(),
            IntTy::I16 => i16::MAX.into(),
            IntTy::I32 => i32::MAX.into(),
            IntTy::I64 => i64::MAX.into(),
            IntTy::U8 => u8::MAX.into(),
            IntTy::U16 => u16::MAX.into(),
            IntTy::U32 => u32::MAX.into(),
            IntTy::U64 => u64::MAX.into(),
        }
    }

    pub fn contains(self, value: i128) -> bool {
        self.min() <= value && value <= self.max()
    }

    pub fn is_signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
    }

    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "Int8",
            IntTy::I16 => "Int16",
            IntTy::I32 => "Int32",
            IntTy::I64 => "Int",
            IntTy::U8 => "UInt8",
            IntTy::U16 => "UInt16",
            IntTy::U32 => "UInt32",
            IntTy::U64 => "UInt64",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    pub fn name(self) -> &'static str {
        match self {
            FloatTy::F32 => "Float32",
            FloatTy::F64 => "Float",
        }
    }

    /// Whether `text` denotes a finite value of this type.
    pub fn holds(self, text: &str) -> bool {
        match self {
            FloatTy::F32 => text.parse::<f32>().is_ok_and(f32::is_finite),
            FloatTy::F64 => text.parse::<f64>().is_ok_and(f64::is_finite),
        }
    }
}

/// A type. Compound types own their parts, so a `Ty` means the same thing wherever it is
/// held, and equality needs no context. A nominal type is named by id, and what it declares
/// is in [`Decls`](crate::decls::Decls).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Text,
    Unit,
    Never,
    /// A record declared in Proviso: the module's, or the prelude's `System`.
    Adt(AdtId, Arc<[Ty]>),
    /// The error of `std.io` operations.
    IoError,
    /// A capability interface type such as `Out`. Copies of its values share state (REFERENCE §9.6).
    Cap(Arc<CapTy>),
    /// A function type: the modes of its parameters, and its parts, `[result, error, uses,
    /// parameters…]`, where the error of one that can't fail is `Never` and `uses` is a
    /// [`Ty::Reach`] (REFERENCE §9.4).
    Fn(Arc<[ParamMode]>, Arc<[Ty]>),
    /// The `uses` of a function type, which is one of its parts so that inference can leave it
    /// open as it does a type argument. No value has this type.
    Reach(Arc<Reach>),
    /// The type parameter at this index of the generic declaration whose fields mention it,
    /// such as `T` in the prelude's `Option[T]`.
    Param(u32),
    /// An inference variable of the body being checked (see [`crate::infer`]). None is
    /// left in [`crate::Program`] once the body is checked.
    Var(u32),
    /// The type of an expression that already has an error; it is compatible with
    /// everything, so one mistake is reported once.
    Error,
}

/// Where a function type's parameters start in its parts: after its result, error and `uses`.
pub const FN_PARAMS: usize = 3;

/// A capability type: its interface, the permissions it has, and the capabilities its
/// implementation `uses` (REFERENCE §9.2).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CapTy {
    pub iface: IfaceId,
    pub perms: Perms,
    pub uses: Reach,
}

/// What a value may reach (REFERENCE §9.2, §9.4): each capability interface it may reach a
/// capability of, with the permissions it may use, and each type parameter whose type
/// argument may reach more (OPEN_QUESTIONS Q31). Capabilities of one interface are one
/// entry with the permissions of all of them, so a set has one spelling, and the `uses` of
/// a capability it reaches are in it too. Effect parameters join it in slice 3.6.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Reach {
    /// Sorted by interface, each once.
    caps: Vec<(IfaceId, Perms)>,
    /// Sorted, each once.
    params: Vec<u32>,
}

impl Reach {
    pub fn is_empty(&self) -> bool {
        self.caps.is_empty() && self.params.is_empty()
    }

    pub fn caps(&self) -> &[(IfaceId, Perms)] {
        &self.caps
    }

    pub fn params(&self) -> &[u32] {
        &self.params
    }

    /// What a value of type parameter `i` without `Copy` may reach.
    pub fn param(i: u32) -> Reach {
        Reach { caps: Vec::new(), params: vec![i] }
    }

    /// What it reaches apart from capabilities of `iface`.
    pub fn without(mut self, iface: IfaceId) -> Reach {
        self.caps.retain(|&(i, _)| i != iface);
        self
    }

    /// What it reaches apart from type parameters.
    pub fn without_params(mut self) -> Reach {
        self.params.clear();
        self
    }

    /// What a capability of `cap`'s type reaches: itself and what it uses.
    pub fn of_cap(cap: &CapTy) -> Reach {
        let mut reach = cap.uses.clone();
        reach.add_cap(cap.iface, cap.perms);
        reach
    }

    pub fn add_cap(&mut self, iface: IfaceId, perms: Perms) {
        match self.caps.binary_search_by_key(&iface, |&(i, _)| i) {
            Ok(at) => self.caps[at].1 = self.caps[at].1.union(perms),
            Err(at) => self.caps.insert(at, (iface, perms)),
        }
    }

    pub fn union(&self, other: &Reach) -> Reach {
        let mut union = self.clone();
        union.extend(other);
        union
    }

    pub fn extend(&mut self, other: &Reach) {
        for &(iface, perms) in &other.caps {
            self.add_cap(iface, perms);
        }
        for &i in &other.params {
            if let Err(at) = self.params.binary_search(&i) {
                self.params.insert(at, i);
            }
        }
    }

    /// What both reach: each interface both reach, with the permissions both have.
    pub fn intersect(&self, other: &Reach) -> Reach {
        let caps = (self.caps.iter())
            .filter_map(|&(iface, perms)| other.perms(iface).map(|theirs| (iface, perms.intersect(theirs))))
            .collect();
        let params = self.params.iter().copied().filter(|i| other.params.contains(i)).collect();
        Reach { caps, params }
    }

    fn perms(&self, iface: IfaceId) -> Option<Perms> {
        self.caps.binary_search_by_key(&iface, |&(i, _)| i).ok().map(|at| self.caps[at].1)
    }

    /// Whether `other` covers this: it reaches each interface this does, with at least its
    /// permissions, and each type parameter (OPEN_QUESTIONS P3, decided for phase 3).
    pub fn covered_by(&self, other: &Reach) -> bool {
        self.caps.iter().all(|&(iface, perms)| other.perms(iface).is_some_and(|theirs| perms.is_subset(theirs)))
            && self.params.iter().all(|i| other.params.contains(i))
    }
}

/// A set of the permissions one capability interface declares, as bits in the order it
/// declares them, so a set has one spelling. An interface declares at most 64.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Perms(pub u64);

impl Perms {
    pub const NONE: Perms = Perms(0);
    pub const MAX: usize = 64;

    /// The first `n` permissions: every one an interface that declares `n` has.
    pub fn all(n: usize) -> Perms {
        Perms(if n >= Self::MAX { u64::MAX } else { (1 << n) - 1 })
    }

    pub fn one(i: usize) -> Perms {
        Perms(1 << i)
    }

    pub fn contains(self, i: usize) -> bool {
        self.0 & (1 << i) != 0
    }

    pub fn is_subset(self, other: Perms) -> bool {
        self.0 & !other.0 == 0
    }

    pub fn union(self, other: Perms) -> Perms {
        Perms(self.0 | other.0)
    }

    pub fn intersect(self, other: Perms) -> Perms {
        Perms(self.0 & other.0)
    }

    pub fn minus(self, other: Perms) -> Perms {
        Perms(self.0 & !other.0)
    }

    /// The indices of the permissions in it, in declaration order.
    pub fn iter(self) -> impl Iterator<Item = usize> {
        (0..Self::MAX).filter(move |&i| self.contains(i))
    }
}

impl Ty {
    pub const INT: Ty = Ty::Int(IntTy::I64);

    pub fn adt(id: AdtId) -> Ty {
        Ty::Adt(id, Arc::from([]))
    }

    /// `id` applied to `args`. A type argument that has an error makes the whole type one, so
    /// a mistake inside it is reported once (REFERENCE §15.1).
    pub fn applied(id: AdtId, args: Vec<Ty>) -> Ty {
        if args.contains(&Ty::Error) { Ty::Error } else { Ty::Adt(id, args.into()) }
    }

    /// The function type with these parameters, result and error, which uses nothing. A part
    /// that has an error makes the whole type one, as [`Ty::applied`] does.
    pub fn func(modes: Vec<ParamMode>, params: Vec<Ty>, ret: Ty, fails: Ty) -> Ty {
        Ty::func_uses(modes, params, ret, fails, Ty::reach(Reach::default()))
    }

    /// [`Ty::func`] with `uses`, a [`Ty::Reach`] or a variable for one.
    pub fn func_uses(modes: Vec<ParamMode>, params: Vec<Ty>, ret: Ty, fails: Ty, uses: Ty) -> Ty {
        let mut parts = vec![ret, fails, uses];
        parts.extend(params);
        Ty::func_parts(modes.into(), parts)
    }

    pub fn reach(reach: Reach) -> Ty {
        Ty::Reach(Arc::new(reach))
    }

    fn func_parts(modes: Arc<[ParamMode]>, parts: Vec<Ty>) -> Ty {
        if parts.contains(&Ty::Error) { Ty::Error } else { Ty::Fn(modes, parts.into()) }
    }

    /// The types a compound type is built from: a record's or enum's type arguments, or a
    /// function type's parts. `None` for a type without any.
    pub fn parts(&self) -> Option<&Arc<[Ty]>> {
        match self {
            Ty::Adt(_, args) if !args.is_empty() => Some(args),
            Ty::Fn(_, parts) => Some(parts),
            _ => None,
        }
    }

    /// The type built as this one is, from `parts` in place of its own [`Ty::parts`].
    pub fn with_parts(&self, parts: Vec<Ty>) -> Ty {
        match self {
            Ty::Adt(id, _) => Ty::applied(*id, parts),
            Ty::Fn(modes, _) => Ty::func_parts(modes.clone(), parts),
            ty => ty.clone(),
        }
    }

    pub fn option(value: Ty) -> Ty {
        Ty::applied(AdtId::OPTION, vec![value])
    }

    pub fn result(value: Ty, error: Ty) -> Ty {
        Ty::applied(AdtId::RESULT, vec![value, error])
    }

    /// The type with each parameter replaced by its argument in `args`.
    pub fn subst(&self, args: &[Ty]) -> Ty {
        self.subst_in(args, &mut HashMap::new()).unwrap_or_else(|| self.clone())
    }

    /// [`Ty::subst`], or `None` where nothing changes, so the type keeps its shared parts. A
    /// list of parts in `seen`, by address, was replaced already, so a type that shares its
    /// parts, as a doubling alias does, costs each part once (issue #55). A list of parts
    /// belongs to one type, so its address names that type.
    fn subst_in(&self, args: &[Ty], seen: &mut HashMap<usize, Option<Ty>>) -> Option<Ty> {
        match self {
            Ty::Param(i) => Some(args[*i as usize].clone()),
            ty if let Some(parts) = ty.parts() => {
                let key = Arc::as_ptr(parts) as *const Ty as usize;
                if let Some(done) = seen.get(&key) {
                    return done.clone();
                }
                let new: Vec<Option<Ty>> = parts.iter().map(|part| part.subst_in(args, seen)).collect();
                // A part with an error makes the whole type one, as `with_parts` does.
                let done = (new.iter().any(Option::is_some) || parts.contains(&Ty::Error)).then(|| {
                    ty.with_parts(
                        new.into_iter()
                            .zip(parts.iter())
                            .map(|(new, part)| new.unwrap_or_else(|| part.clone()))
                            .collect(),
                    )
                });
                seen.insert(key, done.clone());
                done
            }
            _ => None,
        }
    }

    pub fn list(element: Ty) -> Ty {
        Ty::applied(AdtId::LIST, vec![element])
    }

    pub fn map(key: Ty, value: Ty) -> Ty {
        Ty::applied(AdtId::MAP, vec![key, value])
    }

    pub fn system() -> Ty {
        Ty::adt(AdtId::SYSTEM)
    }

    /// `iface` with the permissions `perms`, which uses nothing.
    pub fn cap(iface: IfaceId, perms: Perms) -> Ty {
        Ty::cap_uses(iface, perms, Reach::default())
    }

    /// `iface` with the permissions `perms`, which uses `uses`.
    pub fn cap_uses(iface: IfaceId, perms: Perms, uses: Reach) -> Ty {
        Ty::Cap(Arc::new(CapTy { iface, perms, uses }))
    }

    /// `std.io`'s `Out`, with its one permission, `write` (OPEN_QUESTIONS Q6).
    pub fn out() -> Ty {
        Ty::cap(IfaceId::OUT, Perms::all(1))
    }

    /// A function type's result, error and parameters.
    pub fn fn_parts(&self) -> Option<(&[ParamMode], &Ty, &Ty, &[Ty])> {
        match self {
            Ty::Fn(modes, parts) => Some((modes, &parts[0], &parts[1], &parts[FN_PARAMS..])),
            _ => None,
        }
    }

    /// A function type's `uses`: a [`Ty::Reach`], or a variable for one while inference
    /// leaves it open.
    pub fn fn_uses(&self) -> Option<&Ty> {
        match self {
            Ty::Fn(_, parts) => Some(&parts[2]),
            _ => None,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }

    /// Whether the type has no value yet to report against: an error or a diverging expression.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Ty::Error | Ty::Never)
    }
}
