//! Inference variables: the type arguments and literal types that nothing has given yet.
//!
//! A `None` without an expected type is an `Option[?a]`, a literal without one an `?i`, and
//! a generic call's type parameter a fresh variable. Where values meet (the operands of a
//! comparison, the branches of an `if`, a call's arguments), their types are joined, which
//! binds the variables, so no operand, branch or argument has to go first (OPEN_QUESTIONS
//! P5; issue #10). Each statement then solves what it leaves open.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::Arc;

use proviso_syntax::source::Span;

use crate::FnId;
use crate::decls::AdtId;
use crate::types::{FloatTy, Ty};

/// What a variable may become.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Any,
    /// An integer literal's: an integer type, `Int` by default (REFERENCE §2).
    Int,
    /// A float literal's: a float type, `Float` by default.
    Float,
}

/// Where a variable came from, which an error about it names.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Origin {
    /// A type argument of a variant of `adt` built at `span`.
    Variant { adt: AdtId, span: Span },
    /// Type parameter `param` of function `f`, called at `span`.
    Call { f: FnId, param: usize, span: Span },
    /// A literal, or a `Never` the expected type gave, which have defaults.
    Defaulted,
}

#[derive(Clone, Debug)]
pub struct Open {
    pub kind: Kind,
    /// Only `Never` has reached it so far, so it is `Never` if nothing else does.
    pub never: bool,
    /// A rejected value was the one to give it, so it is an error, not reported, if nothing
    /// else does (REFERENCE §15.1).
    pub quiet: bool,
    pub origin: Origin,
}

#[derive(Clone, Debug)]
enum State {
    Open(Open),
    Bound(Ty),
}

/// What a type holds anywhere in it, which tells a walk whether it has anything to do.
#[derive(Clone, Copy, Default)]
pub struct Shape {
    pub var: bool,
    pub never: bool,
}

#[derive(Default)]
pub struct Vars {
    states: Vec<State>,
    /// The shape of each type argument list seen since the last [`Vars::clear`], by address.
    /// A type never changes, so a list keeps its shape, and the entry holds the list so its
    /// address isn't reused. A statement then walks only the parts of its types that are new,
    /// not the whole of a deep type it got from a local.
    shapes: RefCell<HashMap<usize, (Arc<[Ty]>, Shape), BuildHasherDefault<AddressHasher>>>,
    /// What each bound variable stands for once nothing in it is open, by variable. A bound
    /// variable never changes, so a walk need not go through it again, and a chain of calls
    /// whose types hold the one before costs each call its own part only.
    ground: RefCell<Vec<Option<Ty>>>,
    /// Each variable in the order it was bound, so a statement can find the variables of the
    /// expressions around it that it gave a type.
    trail: Vec<u32>,
}

/// Hashes an address with one multiply, which is all a key that is already unique needs.
#[derive(Default)]
struct AddressHasher(u64);

impl Hasher for AddressHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(byte)).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
    }

    fn write_usize(&mut self, n: usize) {
        self.0 = (n as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(29);
    }
}

impl Vars {
    pub fn count(&self) -> u32 {
        self.states.len() as u32
    }

    pub fn clear(&mut self) {
        self.states.clear();
        self.shapes.get_mut().clear();
        self.ground.get_mut().clear();
        self.trail.clear();
    }

    /// How many variables have been bound so far.
    pub fn bound(&self) -> usize {
        self.trail.len()
    }

    /// The open variables, made at `since` or later, in what the variables made before
    /// `since` were bound to after `mark`. A statement must not settle these, since the
    /// expression around it may still give them a type.
    pub fn outer(&self, since: u32, mark: usize) -> Vec<u32> {
        let mut found = Vec::new();
        for &v in &self.trail[mark..] {
            if v < since {
                self.open_in(&Ty::Var(v), &mut found);
            }
        }
        found.retain(|&v| v >= since);
        found
    }

    fn ground_of(&self, v: u32) -> Option<Ty> {
        self.ground.borrow().get(v as usize).cloned().flatten()
    }

    fn keep_ground(&self, v: u32, ty: Ty) {
        let mut ground = self.ground.borrow_mut();
        if ground.len() <= v as usize {
            ground.resize(v as usize + 1, None);
        }
        ground[v as usize] = Some(ty);
    }

    pub fn shape(&self, ty: &Ty) -> Shape {
        match ty {
            Ty::Var(_) => Shape { var: true, never: false },
            Ty::Never => Shape { var: false, never: true },
            Ty::Adt(_, args) if !args.is_empty() => {
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some((_, shape)) = self.shapes.borrow().get(&key) {
                    return *shape;
                }
                let shape = args.iter().fold(Shape::default(), |acc, arg| {
                    let part = self.shape(arg);
                    Shape { var: acc.var || part.var, never: acc.never || part.never }
                });
                self.shapes.borrow_mut().insert(key, (args.clone(), shape));
                shape
            }
            _ => Shape::default(),
        }
    }

    /// Whether `ty` has a variable in it, bound or open.
    pub fn has_var(&self, ty: &Ty) -> bool {
        self.shape(ty).var
    }

    pub fn fresh(&mut self, kind: Kind, origin: Origin) -> Ty {
        self.states.push(State::Open(Open { kind, never: false, quiet: false, origin }));
        Ty::Var(self.count() - 1)
    }

    /// A variable that only `Never` has reached, as a `Never` in an expected type is.
    fn never(&mut self) -> Ty {
        self.states.push(State::Open(Open { kind: Kind::Any, never: true, quiet: false, origin: Origin::Defaulted }));
        Ty::Var(self.count() - 1)
    }

    /// The variable `v` stands for: itself, or the one it was joined with.
    pub fn root(&self, mut v: u32) -> u32 {
        while let State::Bound(Ty::Var(next)) = &self.states[v as usize] {
            v = *next;
        }
        v
    }

    /// What is known of open variable `v`'s class, or `None` once it is bound.
    pub fn open(&self, v: u32) -> Option<&Open> {
        match &self.states[self.root(v) as usize] {
            State::Open(open) => Some(open),
            State::Bound(_) => None,
        }
    }

    /// `ty` with the variables at its top replaced by what they are bound to.
    pub fn resolve(&self, ty: &Ty) -> Ty {
        let mut ty = ty;
        while let Ty::Var(v) = ty {
            match &self.states[*v as usize] {
                State::Bound(next) => ty = next,
                State::Open(_) => return ty.clone(),
            }
        }
        ty.clone()
    }

    /// `ty` with every bound variable replaced, at any depth. Parts without one are shared.
    pub fn zonk(&self, ty: &Ty) -> Ty {
        self.zonk_part(ty).unwrap_or_else(|| ty.clone())
    }

    fn zonk_part(&self, ty: &Ty) -> Option<Ty> {
        match ty {
            Ty::Var(v) => match &self.states[*v as usize] {
                State::Open(_) => None,
                State::Bound(next) => {
                    if let Some(ty) = self.ground_of(*v) {
                        return Some(ty);
                    }
                    let ty = self.zonk(next);
                    if !self.has_var(&ty) {
                        self.keep_ground(*v, ty.clone());
                    }
                    Some(ty)
                }
            },
            Ty::Adt(id, args) if self.has_var(ty) => {
                let parts: Vec<Option<Ty>> = args.iter().map(|arg| self.zonk_part(arg)).collect();
                if parts.iter().all(Option::is_none) {
                    return None;
                }
                let args = parts.into_iter().zip(args.iter()).map(|(part, arg)| part.unwrap_or_else(|| arg.clone()));
                Some(Ty::applied(*id, args.collect()))
            }
            _ => None,
        }
    }

    /// `ty` zonked, with an open literal variable as its default, as diagnostics and interface
    /// checks see it. Any other open variable stays.
    pub fn defaulted(&self, ty: &Ty) -> Ty {
        match self.resolve(ty) {
            Ty::Var(v) => match self.open(v).map(|open| open.kind) {
                Some(Kind::Int) => Ty::INT,
                Some(Kind::Float) => Ty::Float(FloatTy::F64),
                _ => Ty::Var(self.root(v)),
            },
            Ty::Adt(id, args) if self.has_var(ty) => {
                Ty::applied(id, args.iter().map(|arg| self.defaulted(arg)).collect())
            }
            ty => ty,
        }
    }

    /// The open variables in `ty`, by their roots, each once and in order.
    pub fn open_in(&self, ty: &Ty, found: &mut Vec<u32>) {
        self.open_part(ty, found);
    }

    /// [`Vars::open_in`], which also says whether it found any, so a bound variable with none
    /// in it is kept as ground.
    fn open_part(&self, ty: &Ty, found: &mut Vec<u32>) -> bool {
        if !self.has_var(ty) {
            return false;
        }
        match ty {
            Ty::Var(v) => match &self.states[*v as usize] {
                State::Open(_) => {
                    if !found.contains(v) {
                        found.push(*v);
                    }
                    true
                }
                State::Bound(next) => {
                    if self.ground_of(*v).is_some() {
                        return false;
                    }
                    let open = self.open_part(next, found);
                    if !open {
                        self.keep_ground(*v, self.zonk(next));
                    }
                    open
                }
            },
            Ty::Adt(_, args) => args.iter().fold(false, |open, arg| self.open_part(arg, found) || open),
            _ => false,
        }
    }

    pub fn has_open(&self, ty: &Ty) -> bool {
        let mut found = Vec::new();
        self.open_in(ty, &mut found);
        !found.is_empty()
    }

    /// Settles open variable `v`'s class as `ty`.
    pub fn settle(&mut self, v: u32, ty: Ty) {
        let root = self.root(v);
        self.states[root as usize] = State::Bound(ty);
        self.trail.push(root);
    }

    /// Settles every open variable in `ty` as an error, so nothing more is reported about
    /// a type that already has one (REFERENCE §15.1).
    pub fn poison(&mut self, ty: &Ty) {
        let mut found = Vec::new();
        self.open_in(ty, &mut found);
        for v in found {
            self.settle(v, Ty::Error);
        }
    }

    /// Marks every open variable in `ty` as one a rejected value was to give. Unlike
    /// [`Vars::poison`], a later value may still give it a type.
    pub fn quiet(&mut self, ty: &Ty) {
        let mut found = Vec::new();
        self.open_in(ty, &mut found);
        for v in found {
            if let State::Open(open) = &mut self.states[v as usize] {
                open.quiet = true;
            }
        }
    }

    /// `ty` with each `Never` in it a variable that only `Never` has reached, which a value
    /// may widen, as a field widens a `Never` the expected type gives (OPEN_QUESTIONS P5).
    /// Parts without one are shared.
    pub fn open_nevers(&mut self, ty: &Ty) -> Ty {
        self.open_nevers_part(ty).unwrap_or_else(|| ty.clone())
    }

    fn open_nevers_part(&mut self, ty: &Ty) -> Option<Ty> {
        match ty {
            Ty::Never => Some(self.never()),
            Ty::Adt(id, args) if self.shape(ty).never => {
                let parts: Vec<Option<Ty>> = args.iter().map(|arg| self.open_nevers_part(arg)).collect();
                if parts.iter().all(Option::is_none) {
                    return None;
                }
                let args = parts.into_iter().zip(args.iter()).map(|(part, arg)| part.unwrap_or_else(|| arg.clone()));
                Some(Ty::Adt(*id, args.collect::<Vec<_>>().into()))
            }
            _ => None,
        }
    }

    /// Whether variable `v` occurs in `ty`, which would make it part of itself.
    fn occurs(&self, v: u32, ty: &Ty) -> bool {
        if !self.has_var(ty) {
            return false;
        }
        match ty {
            Ty::Var(w) => match &self.states[*w as usize] {
                State::Open(_) => *w == v,
                State::Bound(next) => self.ground_of(*w).is_none() && self.occurs(v, next),
            },
            Ty::Adt(_, args) => args.iter().any(|arg| self.occurs(v, arg)),
            _ => false,
        }
    }

    /// Whether open variable `v` of kind `kind` may stand for `ty`, which isn't a variable.
    fn fits(kind: Kind, ty: &Ty) -> bool {
        match kind {
            Kind::Any => true,
            Kind::Int => matches!(ty, Ty::Int(_) | Ty::Error),
            Kind::Float => matches!(ty, Ty::Float(_) | Ty::Error),
        }
    }

    /// Makes the classes of `a` and `b` one. The older root stays, so a statement's solve,
    /// which settles only the roots made since it began, can't settle a class that also
    /// holds a variable of the expression around it.
    fn union(&mut self, a: u32, b: u32) -> bool {
        let (a, b) = (self.root(a), self.root(b));
        if a == b {
            return true;
        }
        let (keep, gone) = if a < b { (a, b) } else { (b, a) };
        let (State::Open(kept), State::Open(other)) = (&self.states[keep as usize], &self.states[gone as usize]) else {
            unreachable!("roots are open")
        };
        let kind = match (kept.kind, other.kind) {
            (Kind::Any, kind) | (kind, Kind::Any) => kind,
            (x, y) if x == y => x,
            _ => return false,
        };
        let never = kept.never || other.never;
        let quiet = kept.quiet || other.quiet;
        // An error about the class names the value that first left it open.
        let origin = if matches!(kept.origin, Origin::Defaulted) { other.origin } else { kept.origin };
        self.states[keep as usize] = State::Open(Open { kind, never, quiet, origin });
        self.states[gone as usize] = State::Bound(Ty::Var(keep));
        self.trail.push(gone);
        true
    }

    /// Variable `v` is at least `ty`: a value of type `ty` flows into it. A `Never` gives it
    /// nothing, and one inside `ty` stays open for later values to widen.
    fn lower(&mut self, v: u32, ty: &Ty) -> bool {
        let v = self.root(v);
        let State::Open(open) = &mut self.states[v as usize] else { unreachable!("roots are open") };
        if *ty == Ty::Never {
            open.never = true;
            return true;
        }
        let kind = open.kind;
        if !Self::fits(kind, ty) || self.occurs(v, ty) {
            return false;
        }
        let ty = self.open_nevers(ty);
        self.settle(v, ty);
        true
    }

    /// Variable `v` is exactly `ty`: its value must fit where a `ty` is required.
    fn exact(&mut self, v: u32, ty: &Ty) -> bool {
        let v = self.root(v);
        let State::Open(open) = &self.states[v as usize] else { unreachable!("roots are open") };
        if !Self::fits(open.kind, ty) || self.occurs(v, ty) {
            return false;
        }
        self.settle(v, ty.clone());
        true
    }

    /// Whether a value of type `actual` may be used where `expected` is required, binding
    /// variables so that it may. `Never` is a subtype of every type, also as a type argument
    /// (REFERENCE §9.2), and an error fits everything, so it is reported once.
    pub fn subsume(&mut self, expected: &Ty, actual: &Ty) -> bool {
        let (expected, actual) = (self.resolve(expected), self.resolve(actual));
        match (&expected, &actual) {
            (_, Ty::Error) => {
                self.poison(&expected);
                true
            }
            (Ty::Error, _) => {
                self.poison(&actual);
                true
            }
            (Ty::Var(x), Ty::Var(y)) => self.union(*x, *y),
            (Ty::Var(x), ty) => self.lower(*x, ty),
            (_, Ty::Never) => true,
            (ty, Ty::Var(y)) => self.exact(*y, ty),
            (Ty::Adt(id, args), Ty::Adt(other, actual_args)) if id == other && args.len() == actual_args.len() => {
                // Shared parts are the same type, so an expected type built from the
                // argument's own isn't walked again, and `Some(Some(…))` stays linear.
                Arc::ptr_eq(args, actual_args)
                    || args.iter().zip(actual_args.iter()).all(|(arg, actual)| self.subsume(arg, actual))
            }
            (expected, actual) => expected == actual,
        }
    }

    /// The type of a value that is either an `a` or a `b`, binding variables so that there
    /// is one. `Never` gives way to the other side, also as a type argument, so
    /// `Option[Never]` and `Option[Int]` join to `Option[Int]`. `None` when there is none.
    pub fn join(&mut self, a: &Ty, b: &Ty) -> Option<Ty> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Error, other) | (other, Ty::Error) => {
                self.poison(other);
                Some(Ty::Error)
            }
            (Ty::Var(x), Ty::Var(y)) => self.union(*x, *y).then(|| self.resolve(&a)),
            (Ty::Var(x), ty) | (ty, Ty::Var(x)) => {
                let x = *x;
                self.lower(x, ty).then(|| self.resolve(&Ty::Var(x)))
            }
            (Ty::Never, ty) | (ty, Ty::Never) => Some(ty.clone()),
            (Ty::Adt(id, args), Ty::Adt(other, other_args)) if id == other && args.len() == other_args.len() => {
                if Arc::ptr_eq(args, other_args) {
                    return Some(a.clone());
                }
                let joined =
                    args.iter().zip(other_args.iter()).map(|(x, y)| self.join(x, y)).collect::<Option<Vec<_>>>()?;
                Some(Ty::applied(*id, joined))
            }
            (x, y) => (x == y).then(|| a.clone()),
        }
    }
}
