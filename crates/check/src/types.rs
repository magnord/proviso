//! The types of the phase-1 subset.

use std::fmt;

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Text,
    Unit,
    Never,
    /// The stub `System` record. Phase 1 provides only its `stdout` field.
    System,
    /// The `Out` capability of `std.io`.
    Out,
    /// The error of `Out` operations.
    IoError,
    /// The type of an expression that already has an error; it is compatible with
    /// everything, so one mistake is reported once.
    Error,
}

impl Ty {
    pub const INT: Ty = Ty::Int(IntTy::I64);

    pub fn is_numeric(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }

    /// Whether the type has no value yet to report against: an error or a diverging expression.
    pub fn is_unknown(self) -> bool {
        matches!(self, Ty::Error | Ty::Never)
    }

    pub fn is_show(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Text | Ty::IoError)
    }

    /// `==` and `!=`; built into scalars, including IEEE equality on floats (REFERENCE §4.9).
    pub fn has_equality(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Text | Ty::Unit)
    }

    /// `<`, `<=`, `>` and `>=`. Text compares by code point (REFERENCE §12.3).
    pub fn has_ordering(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_) | Ty::Char | Ty::Text)
    }

    /// Whether `actual` may be used where `self` is expected. `Never` is a subtype of every
    /// type (REFERENCE §9.2).
    pub fn accepts(self, actual: Ty) -> bool {
        self == actual || actual.is_unknown() || self == Ty::Error
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Ty::Int(it) => it.name(),
            Ty::Float(ft) => ft.name(),
            Ty::Bool => "Bool",
            Ty::Char => "Char",
            Ty::Text => "Text",
            Ty::Unit => "Unit",
            Ty::Never => "Never",
            Ty::System => "System",
            Ty::Out => "Out",
            Ty::IoError => "IoError",
            Ty::Error => "{unknown}",
        };
        f.write_str(name)
    }
}
