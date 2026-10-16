//! Inference variables: the type arguments and literal types that nothing has given yet.
//!
//! A `None` without an expected type is an `Option[?a]`, a literal without one an `?i`, and
//! a generic call's type parameter a fresh variable. Where values meet (the operands of a
//! comparison, the branches of an `if`, a call's arguments), their types are joined, which
//! binds the variables, so no operand, branch or argument has to go first (OPEN_QUESTIONS
//! P5; issue #10). Each statement then solves what it leaves open.

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
    pub origin: Origin,
}

#[derive(Clone, Debug)]
enum State {
    Open(Open),
    Bound(Ty),
}

#[derive(Default)]
pub struct Vars {
    states: Vec<State>,
}

impl Vars {
    pub fn count(&self) -> u32 {
        self.states.len() as u32
    }

    pub fn clear(&mut self) {
        self.states.clear();
    }

    pub fn fresh(&mut self, kind: Kind, origin: Origin) -> Ty {
        self.states.push(State::Open(Open { kind, never: false, origin }));
        Ty::Var(self.count() - 1)
    }

    /// A variable that only `Never` has reached, as a `Never` in an expected type is.
    fn never(&mut self) -> Ty {
        self.states.push(State::Open(Open { kind: Kind::Any, never: true, origin: Origin::Defaulted }));
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
            Ty::Var(_) => match self.resolve(ty) {
                Ty::Var(v) => Some(Ty::Var(self.root(v))),
                resolved => Some(self.zonk_part(&resolved).unwrap_or(resolved)),
            },
            Ty::Adt(id, args) => {
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
            Ty::Adt(id, args) if !args.is_empty() => {
                Ty::applied(id, args.iter().map(|arg| self.defaulted(arg)).collect())
            }
            ty => ty,
        }
    }

    /// The open variables in `ty`, by their roots, each once and in order.
    pub fn open_in(&self, ty: &Ty, found: &mut Vec<u32>) {
        match self.resolve(ty) {
            Ty::Var(v) => {
                let root = self.root(v);
                if !found.contains(&root) {
                    found.push(root);
                }
            }
            Ty::Adt(_, args) => args.iter().for_each(|arg| self.open_in(arg, found)),
            _ => {}
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

    /// `ty` with each `Never` in it a variable that only `Never` has reached, which a value
    /// may widen, as a field widens a `Never` the expected type gives (OPEN_QUESTIONS P5).
    /// Parts without one are shared.
    pub fn open_nevers(&mut self, ty: &Ty) -> Ty {
        self.open_nevers_part(ty).unwrap_or_else(|| ty.clone())
    }

    fn open_nevers_part(&mut self, ty: &Ty) -> Option<Ty> {
        match ty {
            Ty::Never => Some(self.never()),
            Ty::Adt(id, args) if !args.is_empty() => {
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
        match self.resolve(ty) {
            Ty::Var(w) => self.root(w) == v,
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

    /// Makes the classes of `a` and `b` one. The older root stays, so a statement's own
    /// variables never stand for those of the expression around it.
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
        // An error about the class names the value that first left it open.
        let origin = if matches!(kept.origin, Origin::Defaulted) { other.origin } else { kept.origin };
        self.states[keep as usize] = State::Open(Open { kind, never, origin });
        self.states[gone as usize] = State::Bound(Ty::Var(keep));
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
