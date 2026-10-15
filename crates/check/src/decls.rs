//! Nominal declarations: the records of the prelude and of the module. Questions about a type
//! that depend on what it declares, such as its name or the interfaces it implements, are
//! answered here.

use std::fmt;

use proviso_syntax::ast::ExprId;

use crate::types::Ty;

/// A record declared in Proviso. The prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AdtId(u32);

impl AdtId {
    pub const SYSTEM: AdtId = AdtId(0);
}

/// An interface of the prelude, or of the standard library such as `std.io`'s `Out`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct IfaceId(u32);

impl IfaceId {
    pub const EQ: IfaceId = IfaceId(0);
    pub const ORD: IfaceId = IfaceId(1);
    pub const SHOW: IfaceId = IfaceId(2);
    /// The capability interface of `std.io`.
    pub const OUT: IfaceId = IfaceId(3);

    pub fn name(self) -> &'static str {
        ["Eq", "Ord", "Show", "Out"][self.0 as usize]
    }

    /// Whether a record can derive it (REFERENCE §4.4).
    pub fn derivable(self) -> bool {
        matches!(self, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW)
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

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

pub struct AdtDef {
    pub name: Box<str>,
    /// A record has one.
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
}

impl AdtDef {
    pub fn record(name: &str, fields: Vec<FieldDef>) -> AdtDef {
        let variant = VariantDef { name: name.into(), locals: fields.len(), fields, preds: Vec::new() };
        AdtDef {
            name: name.into(),
            variants: vec![variant],
            derives: Vec::new(),
            unknown_interfaces: false,
            unknown_methods: false,
        }
    }

    /// The one variant of a record.
    pub fn variant(&self) -> &VariantDef {
        &self.variants[VariantIdx::RECORD.index()]
    }

    pub fn variant_mut(&mut self) -> &mut VariantDef {
        &mut self.variants[VariantIdx::RECORD.index()]
    }

    pub fn field(&self, name: &str) -> Option<(FieldIdx, &FieldDef)> {
        let i = self.variant().fields.iter().position(|f| &*f.name == name)?;
        Some((FieldIdx(i as u32), &self.variant().fields[i]))
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
}

impl Default for Decls {
    /// The prelude, with each declaration at the id its constant names.
    fn default() -> Decls {
        let system = AdtDef::record("System", vec![FieldDef { name: "stdout".into(), ty: Ty::out() }]);
        Decls { adts: vec![system] }
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

    /// Whether `ty` implements `iface`, built in or derived (STD.md). An unknown type
    /// implements nothing, so callers decide whether it is worth reporting.
    pub fn implements(&self, ty: &Ty, iface: IfaceId) -> bool {
        match ty {
            Ty::Adt(id, _) => {
                let def = self.adt(*id);
                def.derives.contains(&iface) || (def.unknown_interfaces && iface.derivable())
            }
            // Text is ordered by code point (REFERENCE §12.3).
            Ty::Int(_) | Ty::Char | Ty::Text => matches!(iface, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW),
            // `Float` has IEEE `==` built in, but no `Eq` (REFERENCE §12.2, Q22).
            Ty::Float(_) => iface == IfaceId::SHOW,
            Ty::Bool => matches!(iface, IfaceId::EQ | IfaceId::SHOW),
            Ty::Unit => iface == IfaceId::EQ,
            Ty::IoError => iface == IfaceId::SHOW,
            Ty::Cap(_) | Ty::Never | Ty::Error => false,
        }
    }

    /// How diagnostics write `ty`. A standard library type is qualified when a record of the
    /// module has its name, so the two can be told apart.
    pub fn display<'a>(&'a self, ty: &'a Ty) -> impl fmt::Display + 'a {
        let std = move |name: &'static str, qualified: &'static str| {
            if self.adts.iter().any(|adt| &*adt.name == name) { qualified } else { name }
        };
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
                Ty::IoError => std("IoError", "std.io.IoError"),
                Ty::Cap(cap) if cap.iface == IfaceId::OUT => std("Out", "std.io.Out"),
                Ty::Cap(cap) => cap.iface.name(),
                Ty::Error => "{unknown}",
            })
        })
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
    }
}
