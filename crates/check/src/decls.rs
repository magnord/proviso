//! Nominal declarations: the records of the prelude, and the records and enums of the module. Questions about a type
//! that depend on what it declares, such as its name or the interfaces it implements, are
//! answered here.

use std::fmt;

use proviso_syntax::ast::ExprId;

use crate::types::Ty;

/// A record or enum declared in Proviso. The prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AdtId(u32);

impl AdtId {
    pub const SYSTEM: AdtId = AdtId(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
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

    pub fn new(index: usize) -> VariantIdx {
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
}

pub struct AdtDef {
    pub name: Box<str>,
    pub kind: AdtKind,
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
            variants: Vec::new(),
            derives: Vec::new(),
            unknown_interfaces: false,
            unknown_methods: false,
            unknown_variants: false,
        }
    }

    pub fn is_enum(&self) -> bool {
        self.kind == AdtKind::Enum
    }

    /// The one variant of a record.
    pub fn variant(&self) -> &VariantDef {
        debug_assert_eq!(self.kind, AdtKind::Record, "only a record has exactly one variant");
        &self.variants[VariantIdx::RECORD.index()]
    }

    /// A field of a record. An enum has none: its variants do.
    pub fn field(&self, name: &str) -> Option<(FieldIdx, &FieldDef)> {
        if self.is_enum() {
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

    /// How code names a variant: `Point` for a record, `Shape.Circle` for an enum's variant.
    pub fn ctor_name(&self, variant: VariantIdx) -> String {
        match self.kind {
            AdtKind::Record => self.name.to_string(),
            AdtKind::Enum => format!("{}.{}", self.name, self.variants[variant.index()].name),
        }
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

    /// For each record and enum, whether it has values: whether a variant's fields all have
    /// types with values. An enum without variants has none, and so does a type that can only
    /// be built from itself. A type with a rejected variant is taken to have some, so that
    /// nothing about it is reported (REFERENCE §15.1).
    pub fn inhabited(&self) -> Vec<bool> {
        let mut inhabited = vec![false; self.adts.len()];
        // For each variant, the fields whose types aren't known to have values yet, and for
        // each type, the variants that wait on it.
        let mut missing: Vec<Vec<usize>> = Vec::new();
        let mut waiting: Vec<Vec<(usize, usize)>> = vec![Vec::new(); self.adts.len()];
        let mut found = Vec::new();
        for (a, def) in self.adts.iter().enumerate() {
            let mut counts = Vec::new();
            for (v, variant) in def.variants.iter().enumerate() {
                let mut count = 0;
                for field in &variant.fields {
                    match field.ty {
                        Ty::Adt(id, _) => {
                            count += 1;
                            waiting[id.0 as usize].push((a, v));
                        }
                        Ty::Never => count = usize::MAX,
                        _ => {}
                    }
                    if count == usize::MAX {
                        break;
                    }
                }
                if count == 0 && !inhabited[a] {
                    inhabited[a] = true;
                    found.push(a);
                }
                counts.push(count);
            }
            if def.unknown_variants && !inhabited[a] {
                inhabited[a] = true;
                found.push(a);
            }
            missing.push(counts);
        }
        while let Some(id) = found.pop() {
            for &(a, v) in &waiting[id] {
                let count = &mut missing[a][v];
                if *count == usize::MAX {
                    continue;
                }
                *count -= 1;
                if *count == 0 && !inhabited[a] {
                    inhabited[a] = true;
                    found.push(a);
                }
            }
        }
        inhabited
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
