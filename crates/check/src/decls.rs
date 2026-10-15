//! Nominal declarations: the records of the prelude and of the module. Questions about a type
//! that depend on what it declares, such as its name or the interfaces it implements, are
//! answered here.

use std::fmt;

use crate::types::Ty;

/// A record declared in Proviso. The prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AdtId(u32);

impl AdtId {
    pub const SYSTEM: AdtId = AdtId(0);
}

/// An interface of the prelude.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct IfaceId(u32);

impl IfaceId {
    pub const EQ: IfaceId = IfaceId(0);
    pub const SHOW: IfaceId = IfaceId(1);
    /// The capability interface of `std.io`.
    pub const OUT: IfaceId = IfaceId(2);

    pub fn name(self) -> &'static str {
        ["Eq", "Show", "Out"][self.0 as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FieldIdx(u32);

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

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

pub struct AdtDef {
    pub name: Box<str>,
    /// The declaring item in `Module::items`; `None` for the prelude.
    pub item: Option<usize>,
    /// A record has one.
    pub variants: Vec<VariantDef>,
    pub derives: Vec<IfaceId>,
}

impl AdtDef {
    /// The fields of a record, which are those of its one variant.
    pub fn record(&self) -> &VariantDef {
        &self.variants[VariantIdx::RECORD.index()]
    }

    pub fn field(&self, name: &str) -> Option<(FieldIdx, &FieldDef)> {
        let i = self.record().fields.iter().position(|f| &*f.name == name)?;
        Some((FieldIdx(i as u32), &self.record().fields[i]))
    }
}

pub struct VariantDef {
    pub name: Box<str>,
    pub fields: Vec<FieldDef>,
}

pub struct FieldDef {
    pub name: Box<str>,
    pub ty: Ty,
}

pub struct Decls {
    adts: Vec<AdtDef>,
}

impl Default for Decls {
    /// The prelude, with each declaration at the id its constant names.
    fn default() -> Decls {
        let system = AdtDef {
            name: "System".into(),
            item: None,
            variants: vec![VariantDef {
                name: "System".into(),
                fields: vec![FieldDef { name: "stdout".into(), ty: Ty::out() }],
            }],
            derives: Vec::new(),
        };
        Decls { adts: vec![system] }
    }
}

impl Decls {
    pub fn adt(&self, id: AdtId) -> &AdtDef {
        &self.adts[id.0 as usize]
    }

    /// Whether `ty` implements `iface`, built in or derived (STD.md). An unknown type
    /// implements nothing, so callers decide whether it is worth reporting.
    pub fn implements(&self, ty: &Ty, iface: IfaceId) -> bool {
        match ty {
            Ty::Adt(id, _) => self.adt(*id).derives.contains(&iface),
            // `==` on floats follows IEEE (REFERENCE §4.9).
            Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Text => matches!(iface, IfaceId::EQ | IfaceId::SHOW),
            Ty::Unit => iface == IfaceId::EQ,
            Ty::IoError => iface == IfaceId::SHOW,
            Ty::Cap(_) | Ty::Never | Ty::Error => false,
        }
    }

    /// How diagnostics write `ty`.
    pub fn display<'a>(&'a self, ty: &'a Ty) -> impl fmt::Display + 'a {
        fmt::from_fn(move |f| {
            f.write_str(match ty {
                Ty::Int(it) => it.name(),
                Ty::Float(ft) => ft.name(),
                Ty::Bool => "Bool",
                Ty::Char => "Char",
                Ty::Text => "Text",
                Ty::Unit => "Unit",
                Ty::Never => "Never",
                Ty::Adt(id, _) => &self.adt(*id).name,
                Ty::IoError => "IoError",
                Ty::Cap(cap) => cap.iface.name(),
                Ty::Error => "{unknown}",
            })
        })
    }
}
