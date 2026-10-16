//! Exhaustiveness of `match` (REFERENCE §6.3), by the usefulness algorithm of Maranget's
//! "Warnings for pattern matching" (2007).
//!
//! Each arm without a guard contributes the [`Space`] its pattern covers. Integer patterns
//! cover as much as `_` here: their exhaustiveness is `[verified]`, so before the verifier
//! exists the v1 profile checks it at run time instead (OPEN_QUESTIONS P5). Text and chars
//! have too many values to list, so only `_` or a binding covers them. A constructor with a
//! field of a type that has no values, such as an enum without variants or `Never`, builds
//! nothing, so it needs no arm: `Err` of a `Result[Int, Never]` is one.
//!
//! The algorithm keeps its own stack and holds rows as lists that share their tails, so no
//! pattern is too wide or deep for the native stack, and taking a column off a row costs the
//! same however wide the row is. Some sets of arms still take exponential work, so the check
//! gives up after [`MAX_STEPS`] steps.

use crate::decls::{Decls, Inhabited, VariantIdx};
use crate::types::Ty;

/// The most work one `match` may take to check, counted in rows visited and columns added.
/// It allows a record of a million fields, but not the doubling some sets of arms cause.
pub const MAX_STEPS: usize = 10_000_000;

/// What a pattern covers.
#[derive(Clone, Debug)]
pub enum Space {
    /// Every value: `_`, a binding or an integer pattern.
    Wild,
    /// A pattern with an error, anywhere inside it. It counts as `_`, so that what it may
    /// have meant to cover is not reported missing (REFERENCE §15.1).
    Error,
    /// The values built by one constructor, whose fields are covered by the parts, one per
    /// field in declaration order.
    Ctor(Ctor, Vec<Space>),
    /// Some values of a type too large to list, such as one text or a range of chars.
    Some,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ctor {
    Variant(VariantIdx),
    Bool(bool),
    Unit,
}

/// The check took more than [`MAX_STEPS`] steps.
#[derive(Debug)]
pub struct TooComplex;

/// A value no row covers, as constructors with `_` for any value.
enum Witness {
    Any,
    Ctor(Ctor, Vec<Witness>),
}

/// A pattern for a value of type `ty` that none of `rows` covers, or `None` if they cover
/// every value.
/// `inhabited` says which types have values (see [`Decls::inhabited`]).
pub fn uncovered(decls: &Decls, inhabited: &Inhabited, ty: &Ty, rows: &[Space]) -> Result<Option<String>, TooComplex> {
    let mut m = Matrices { decls, inhabited, cells: Vec::new(), tys: Vec::new(), steps: 0 };
    let tys = Some(m.push_ty(ty.clone(), None));
    let rows = rows.iter().map(|row| Some(m.push_cell(row, None))).collect();
    let witness = m.useful(rows, tys)?;
    Ok(witness.map(|mut witness| render(decls, ty, &witness.remove(0))))
}

/// The constructors of `ty` that build values, with their field types, or `None` when its
/// values are too many to list. An unknown type, or an enum with a rejected variant, is taken
/// to have none, so that nothing about it is reported (REFERENCE §15.1).
fn constructors(decls: &Decls, inhabited: &Inhabited, ty: &Ty) -> Option<Vec<(Ctor, Vec<Ty>)>> {
    match ty {
        Ty::Adt(id, args) => {
            let def = decls.adt(*id);
            if def.unknown_variants {
                return Some(Vec::new());
            }
            let ctors = (0..def.variants.len())
                .map(|v| (Ctor::Variant(VariantIdx::new(v)), def.field_types(VariantIdx::new(v), args)))
                .filter(|(_, fields)| fields.iter().all(|field| inhabited.has_values(decls, field)));
            Some(ctors.collect())
        }
        Ty::Bool => Some(vec![(Ctor::Bool(false), Vec::new()), (Ctor::Bool(true), Vec::new())]),
        Ty::Unit => Some(vec![(Ctor::Unit, Vec::new())]),
        Ty::Never | Ty::Error => Some(Vec::new()),
        // A type parameter stands for any type, so its values can't be listed.
        Ty::Int(_) | Ty::Float(_) | Ty::Char | Ty::Text | Ty::IoError | Ty::Cap(_) | Ty::Param(_) => None,
    }
}

/// A value built by the first of `ctors`, with any fields, or any value if they are too many
/// to list. `None` if the type has no constructors, and so no values.
fn any(ctors: Option<Vec<(Ctor, Vec<Ty>)>>) -> Option<Witness> {
    match ctors {
        Some(ctors) => {
            let (ctor, fields) = ctors.into_iter().next()?;
            Some(Witness::Ctor(ctor, fields.iter().map(|_| Witness::Any).collect()))
        }
        None => Some(Witness::Any),
    }
}

static WILD: Space = Space::Wild;

/// A list of columns, first column first, as the index of its first cell, or `None` when
/// empty. Rows that differ only in their first columns share the rest.
type List = Option<usize>;

/// The pattern matrices of one check: their cells, their column types, and the work so far.
struct Matrices<'a, 's> {
    decls: &'a Decls,
    inhabited: &'a Inhabited,
    /// A pattern and the rest of its row.
    cells: Vec<(&'s Space, List)>,
    /// A column's type and the types of the columns after it.
    tys: Vec<(Ty, List)>,
    steps: usize,
}

/// A matrix whose first column has every constructor of its type, waiting while the rows
/// that match each constructor are checked in turn.
struct Split {
    /// The witnesses for the columns before this one.
    heads: Vec<Witness>,
    rows: Vec<List>,
    /// The types of the columns after this one.
    rest: List,
    ctors: Vec<(Ctor, Vec<Ty>)>,
    /// The constructor to check next. The one being checked is the one before it.
    next: usize,
}

enum Walk {
    Decided(Option<Vec<Witness>>),
    Split(Split),
}

impl<'s> Matrices<'_, 's> {
    fn push_cell(&mut self, space: &'s Space, rest: List) -> usize {
        self.cells.push((space, rest));
        self.cells.len() - 1
    }

    fn push_ty(&mut self, ty: Ty, rest: List) -> usize {
        self.tys.push((ty, rest));
        self.tys.len() - 1
    }

    fn step(&mut self, n: usize) -> Result<(), TooComplex> {
        self.steps += n;
        if self.steps > MAX_STEPS { Err(TooComplex) } else { Ok(()) }
    }

    /// Values of the columns typed `tys` that no row covers, one witness per column, or
    /// `None` if the rows cover them all.
    fn useful(&mut self, mut rows: Vec<List>, mut tys: List) -> Result<Option<Vec<Witness>>, TooComplex> {
        let mut splits: Vec<Split> = Vec::new();
        loop {
            let mut result = match self.walk(rows, tys)? {
                Walk::Decided(result) => result,
                Walk::Split(split) => {
                    splits.push(split);
                    None
                }
            };
            // Hands the result to the split waiting for it, until one has a constructor left
            // to check. A witness for one constructor is a witness for its split, and a split
            // whose constructors are all covered is covered.
            (rows, tys) = loop {
                let Some(split) = splits.last_mut() else { return Ok(result) };
                if let Some(mut witness) = result.take() {
                    let split = splits.pop().expect("a split is waiting");
                    let (ctor, fields) = &split.ctors[split.next - 1];
                    let after = witness.split_off(fields.len());
                    let mut heads = split.heads;
                    heads.push(Witness::Ctor(*ctor, witness));
                    heads.extend(after);
                    result = Some(heads);
                } else if split.next < split.ctors.len() {
                    let matrix = self.specialize(split)?;
                    split.next += 1;
                    break matrix;
                } else {
                    splits.pop();
                }
            };
        }
    }

    /// Takes columns off the matrix while that needs no split, until it is decided or its
    /// first column has every constructor of its type.
    fn walk(&mut self, mut rows: Vec<List>, mut tys: List) -> Result<Walk, TooComplex> {
        let mut heads = Vec::new();
        loop {
            self.step(1 + rows.len())?;
            let Some(column) = tys else {
                return Ok(Walk::Decided(rows.is_empty().then_some(heads)));
            };
            let (ty, rest) = &self.tys[column];
            let (ctors, rest) = (constructors(self.decls, self.inhabited, ty), *rest);
            // No row covers the rest, so any value of the remaining columns is a witness, if
            // they all have values. A column of a type without any, such as an enum without
            // variants, is covered.
            if rows.is_empty() {
                let witness = || -> Option<Vec<Witness>> {
                    heads.push(any(ctors)?);
                    let mut tys = rest;
                    while let Some(column) = tys {
                        heads.push(any(constructors(self.decls, self.inhabited, &self.tys[column].0))?);
                        tys = self.tys[column].1;
                    }
                    Some(heads)
                };
                return Ok(Walk::Decided(witness()));
            }
            let cells = &self.cells;
            let used =
                |ctor: Ctor| rows.iter().any(|row| matches!(cells[cell(*row)].0, Space::Ctor(c, _) if *c == ctor));
            let head = match ctors {
                Some(ctors) if ctors.iter().all(|(ctor, _)| used(*ctor)) => {
                    return Ok(Walk::Split(Split { heads, rows, rest, ctors, next: 0 }));
                }
                // Some values of this column match no constructor pattern, so only the rows
                // with `_` there can cover them.
                Some(ctors) => {
                    let unused = ctors.into_iter().filter(|(ctor, _)| !used(*ctor)).collect();
                    any(Some(unused)).expect("a constructor is unused")
                }
                None => Witness::Any,
            };
            heads.push(head);
            rows.retain_mut(|row| {
                let (space, rest) = self.cells[cell(*row)];
                *row = rest;
                matches!(space, Space::Wild | Space::Error)
            });
            tys = rest;
        }
    }

    /// The rows of `split` that match its next constructor, with that constructor's fields
    /// in place of its column.
    fn specialize(&mut self, split: &Split) -> Result<(Vec<List>, List), TooComplex> {
        let (ctor, fields) = &split.ctors[split.next];
        let mut rows = Vec::new();
        for row in &split.rows {
            self.step(1 + fields.len())?;
            let (space, mut list) = self.cells[cell(*row)];
            match space {
                Space::Ctor(c, parts) if c == ctor => {
                    for part in parts.iter().rev() {
                        list = Some(self.push_cell(part, list));
                    }
                }
                Space::Wild | Space::Error => {
                    for _ in fields {
                        list = Some(self.push_cell(&WILD, list));
                    }
                }
                _ => continue,
            }
            rows.push(list);
        }
        let mut tys = split.rest;
        for ty in fields.iter().rev() {
            tys = Some(self.push_ty(ty.clone(), tys));
        }
        Ok((rows, tys))
    }
}

/// The first cell of a row, which has one for each column left.
fn cell(row: List) -> usize {
    row.expect("rows have a cell for each column")
}

/// Writes a witness as a pattern: `Shape.Empty`, `IntList.Cons(head: _, tail: IntList.Nil)`,
/// with `..` for a constructor whose fields may be anything. A variant of `Option` or
/// `Result` is written as code writes it: `Some(None)`, `Err(_)`.
fn render(decls: &Decls, ty: &Ty, witness: &Witness) -> String {
    let Witness::Ctor(ctor, parts) = witness else { return "_".to_string() };
    match (ctor, ty) {
        (Ctor::Bool(b), _) => b.to_string(),
        (Ctor::Unit, _) => "()".to_string(),
        (Ctor::Variant(v), Ty::Adt(id, args)) => {
            let def = decls.adt(*id);
            let name = decls.ctor_name(*id, *v);
            let fields = &def.variants[v.index()].fields;
            let tys = def.field_types(*v, args);
            if def.tuple {
                let parts: Vec<String> = tys.iter().zip(parts).map(|(ty, part)| render(decls, ty, part)).collect();
                return format!("({})", parts.join(", "));
            }
            if fields.is_empty() {
                return if def.is_enum() { name } else { format!("{name}()") };
            }
            if def.bare_variants {
                return format!("{name}({})", render(decls, &tys[0], &parts[0]));
            }
            if parts.iter().all(|p| matches!(p, Witness::Any)) {
                return format!("{name}(..)");
            }
            let parts: Vec<String> = fields
                .iter()
                .zip(&tys)
                .zip(parts)
                .map(|((field, ty), part)| format!("{}: {}", field.name, render(decls, ty, part)))
                .collect();
            format!("{name}({})", parts.join(", "))
        }
        (Ctor::Variant(_), _) => "_".to_string(),
    }
}
