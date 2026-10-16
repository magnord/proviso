//! The types the checker assigns.

use std::sync::Arc;

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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CapTy {
    pub iface: IfaceId,
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

    pub fn option(value: Ty) -> Ty {
        Ty::applied(AdtId::OPTION, vec![value])
    }

    pub fn result(value: Ty, error: Ty) -> Ty {
        Ty::applied(AdtId::RESULT, vec![value, error])
    }

    /// The type with each parameter replaced by its argument in `args`.
    pub fn subst(&self, args: &[Ty]) -> Ty {
        match self {
            Ty::Param(i) => args[*i as usize].clone(),
            Ty::Adt(id, inner) if !inner.is_empty() => Ty::applied(*id, inner.iter().map(|t| t.subst(args)).collect()),
            ty => ty.clone(),
        }
    }

    pub fn system() -> Ty {
        Ty::adt(AdtId::SYSTEM)
    }

    pub fn out() -> Ty {
        Ty::Cap(Arc::new(CapTy { iface: IfaceId::OUT }))
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }

    /// Whether the type has no value yet to report against: an error or a diverging expression.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Ty::Error | Ty::Never)
    }
}
