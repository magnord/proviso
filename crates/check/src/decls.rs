//! Nominal declarations: the records and enums of the prelude, and those of the module.
//! Questions about a type that depend on what it declares, such as its name or the
//! interfaces it implements, are answered here.

use std::fmt;

use proviso_syntax::ast::ExprId;

use crate::types::Ty;

/// A record or enum declared in Proviso. The prelude's come first, at fixed ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AdtId(u32);

impl AdtId {
    pub const SYSTEM: AdtId = AdtId(0);
    pub const OPTION: AdtId = AdtId(1);
    pub const RESULT: AdtId = AdtId(2);

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
    pub const SOME: VariantIdx = VariantIdx(0);
    pub const NONE: VariantIdx = VariantIdx(1);
    pub const OK: VariantIdx = VariantIdx(0);
    pub const ERR: VariantIdx = VariantIdx(1);

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

    /// How code names a variant: `Point` for a record, `Shape.Circle` for an enum's variant,
    /// and `Some` for one of the prelude's.
    pub fn ctor_name(&self, variant: VariantIdx) -> String {
        match self.kind {
            AdtKind::Record => self.name.to_string(),
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
            def.derives = vec![IfaceId::EQ, IfaceId::ORD, IfaceId::SHOW];
            for (variant, field) in variants {
                let fields = field.map(|(name, param)| FieldDef { name: name.into(), ty: Ty::Param(param) });
                def.variants.push(VariantDef::new(variant, fields.into_iter().collect()));
            }
            def
        };
        let option = generic("Option", 1, [("Some", Some(("value", 0))), ("None", None)]);
        let result = generic("Result", 2, [("Ok", Some(("value", 0))), ("Err", Some(("error", 1)))]);
        Decls { adts: vec![system, option, result] }
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

    /// Whether `ty` implements `iface`, built in or derived (STD.md). An unknown type
    /// implements nothing, so callers decide whether it is worth reporting.
    pub fn implements(&self, ty: &Ty, iface: IfaceId) -> bool {
        match ty {
            // `Option` and `Result` implement what their type arguments do (STD.md). `Never` has
            // no values, so it implements everything as an argument.
            Ty::Adt(id, args) => {
                let def = self.adt(*id);
                (def.derives.contains(&iface) || (def.unknown_interfaces && iface.derivable()))
                    && args.iter().all(|arg| *arg == Ty::Never || self.implements(arg, iface))
            }
            // Text is ordered by code point (REFERENCE §12.3).
            Ty::Int(_) | Ty::Char | Ty::Text => matches!(iface, IfaceId::EQ | IfaceId::ORD | IfaceId::SHOW),
            // `Float` has IEEE `==` built in, but no `Eq` (REFERENCE §12.2, Q22).
            Ty::Float(_) => iface == IfaceId::SHOW,
            Ty::Bool => matches!(iface, IfaceId::EQ | IfaceId::SHOW),
            Ty::Unit => iface == IfaceId::EQ,
            Ty::IoError => iface == IfaceId::SHOW,
            Ty::Cap(_) | Ty::Param(_) | Ty::Never | Ty::Error => false,
        }
    }

    /// How diagnostics write `ty`, with its type arguments: `Option[Int]`. A standard
    /// library type is qualified when a record of the module has its name, so the two can be
    /// told apart.
    pub fn display<'a>(&'a self, ty: &'a Ty) -> impl fmt::Display + 'a {
        let std = move |name: &'static str, qualified: &'static str| {
            if self.adts.iter().any(|adt| &*adt.name == name) { qualified } else { name }
        };
        fmt::from_fn(move |f| {
            if let Ty::Adt(id, args) = ty
                && !args.is_empty()
            {
                write!(f, "{}[", self.adt(*id).name)?;
                for (i, arg) in args.iter().enumerate() {
                    let sep = if i == 0 { "" } else { ", " };
                    write!(f, "{sep}{}", self.display(arg))?;
                }
                return f.write_str("]");
            }
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
                Ty::Param(_) => "_",
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
    }
}
