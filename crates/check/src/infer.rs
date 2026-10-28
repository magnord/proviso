//! Inference variables: the type arguments and literal types that nothing has given yet.
//!
//! A `None` without an expected type is an `Option[?a]`, a literal without one an `?i`, and
//! a generic call's type parameter a fresh variable. Where values meet (the operands of a
//! comparison, the branches of an `if`, a call's arguments), their types are joined, which
//! binds the variables, so no operand, branch or argument has to go first (OPEN_QUESTIONS
//! P5; issue #10). Each statement then solves what it leaves open.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::Arc;

use proviso_syntax::ast::ParamMode;
use proviso_syntax::intern::Symbol;
use proviso_syntax::source::Span;

use crate::FnId;
use crate::decls::{AdtId, IfaceId};
use crate::types::{FN_PARAMS, FloatTy, Perms, Reach, Ty};

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
    /// Parameter `name` of a closure, declared at `span` without a type.
    Closure { name: Symbol, span: Span },
    /// A literal, or a `Never` the expected type gave, which have defaults.
    Defaulted,
}

/// What a variable that capabilities of one interface, or the `uses` of function types, met
/// may be. Values that flow into it bound it from one side, and the places it flows into from
/// the other, so it settles as the same type whichever came first (OPEN_QUESTIONS P3, decided
/// for phase 3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Bounds {
    /// A capability of `iface`.
    Cap {
        iface: IfaceId,
        /// The permissions every capability that flowed in has, or `None` before one did.
        at_most: Option<Perms>,
        /// The permissions some place it flowed into needs.
        at_least: Perms,
        uses: ReachBounds,
    },
    /// A function type's `uses`.
    Reach(ReachBounds),
}

/// What a variable for a reach set, a capability's or a function type's `uses`, may be.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct ReachBounds {
    /// What the values that flowed in reach together, or `None` before one did.
    pub given: Option<Reach>,
    /// What every place it flowed into admits, or `None` before it flowed into one.
    pub admitted: Option<Reach>,
}

impl ReachBounds {
    fn new(reach: &Reach, flow: Flow) -> ReachBounds {
        match flow {
            Flow::In => ReachBounds { given: Some(reach.clone()), admitted: None },
            Flow::Out => ReachBounds { given: None, admitted: Some(reach.clone()) },
        }
    }

    /// What it settles as: what the values reach, or else what its places admit.
    pub fn solution(&self) -> Reach {
        self.given.clone().or_else(|| self.admitted.clone()).unwrap_or_default()
    }

    fn meet(&self, other: &ReachBounds) -> Option<ReachBounds> {
        let given = match (&self.given, &other.given) {
            (Some(a), Some(b)) => Some(a.union(b)),
            (a, b) => a.clone().or_else(|| b.clone()),
        };
        let admitted = match (&self.admitted, &other.admitted) {
            (Some(a), Some(b)) => Some(a.intersect(b)),
            (a, b) => a.clone().or_else(|| b.clone()),
        };
        let holds = match (&given, &admitted) {
            (Some(given), Some(admitted)) => given.covered_by(admitted),
            _ => true,
        };
        holds.then_some(ReachBounds { given, admitted })
    }
}

impl Bounds {
    /// The bounds a value of type `ty` gives where it flows `flow`, if it is a capability or a
    /// reach set. A value that flows in gives a capability at most its permissions and at least
    /// its `uses`, and a place it flows into gives the reverse.
    fn of(ty: &Ty, flow: Flow) -> Option<Bounds> {
        match ty {
            Ty::Cap(cap) => {
                let (at_most, at_least) = match flow {
                    Flow::In => (Some(cap.perms), Perms::NONE),
                    Flow::Out => (None, cap.perms),
                };
                Some(Bounds::Cap { iface: cap.iface, at_most, at_least, uses: ReachBounds::new(&cap.uses, flow) })
            }
            Ty::Reach(reach) => Some(Bounds::Reach(ReachBounds::new(reach, flow))),
            _ => None,
        }
    }

    /// The type it settles as. A capability has all the permissions the values give it, or
    /// else what its places need.
    pub fn solution(&self) -> Ty {
        match self {
            Bounds::Cap { iface, at_most, at_least, uses } => {
                Ty::cap_uses(*iface, at_most.unwrap_or(*at_least), uses.solution())
            }
            Bounds::Reach(reach) => Ty::reach(reach.solution()),
        }
    }

    fn meet(&self, other: &Bounds) -> Option<Bounds> {
        match (self, other) {
            (
                Bounds::Cap { iface, at_most, at_least, uses },
                Bounds::Cap { iface: other_iface, at_most: other_most, at_least: other_least, uses: other_uses },
            ) if iface == other_iface => {
                let at_most = match (at_most, other_most) {
                    (Some(a), Some(b)) => Some(a.intersect(*b)),
                    (a, b) => a.or(*b),
                };
                let at_least = at_least.union(*other_least);
                let uses = uses.meet(other_uses)?;
                at_most.is_none_or(|most| at_least.is_subset(most)).then_some(Bounds::Cap {
                    iface: *iface,
                    at_most,
                    at_least,
                    uses,
                })
            }
            (Bounds::Reach(a), Bounds::Reach(b)) => a.meet(b).map(Bounds::Reach),
            _ => None,
        }
    }
}

/// Which way a value's type meets a variable: it flows in, so the variable is at least as
/// general, or the variable flows out to where the type is required.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Flow {
    In,
    Out,
}

impl Flow {
    fn flip(self) -> Flow {
        match self {
            Flow::In => Flow::Out,
            Flow::Out => Flow::In,
        }
    }
}

/// Which way [`Vars::bound_in`] bounds two types: from above, as the join of two values, or
/// from below, as the meet of two places they go, such as a function's parameters.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Variance {
    Co,
    Contra,
}

impl Variance {
    fn flip(self) -> Variance {
        match self {
            Variance::Co => Variance::Contra,
            Variance::Contra => Variance::Co,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Open {
    pub kind: Kind,
    /// Only `Never` has reached it so far, so it is `Never` if nothing else does.
    pub never: bool,
    /// Why it is not reported if nothing gives it; [`crate::Checker`]'s `settle_vars` holds
    /// the rule. A rejected value was the one to give it.
    pub quiet: bool,
    /// It is the error type of a call without a marker.
    pub unmarked: bool,
    /// A `try` with no `fails` to take it needs it.
    pub owed: bool,
    /// A `todo` hole met it, which stands for a value of a type no one wrote. So it is
    /// `Never`, as the hole is, unless something gives it a type, and a `Never` it settles as
    /// may stand for another type (Q25; issue #30).
    pub hole: bool,
    /// It is in the error type of a call that an enclosing `try`, `attempt`, `else` form or
    /// example marks, which the handler joins, so a later receiver leaves it open inside its
    /// type arguments. It holds how many handlers enclose the outermost one that marks it, so
    /// an inner handler that ends doesn't clear what an outer one still joins.
    pub handled: Option<u32>,
    /// It is a capability, or a function type's `uses`, that is still open.
    pub bounds: Option<Bounds>,
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
    /// A capability or a function type's `uses`, which inference opens where it flows (see
    /// [`Vars::open_caps`]).
    pub cap: bool,
}

#[derive(Default)]
pub struct Vars {
    states: Vec<State>,
    /// The shape of each type argument list seen since the last [`Vars::clear`], by address.
    /// A type never changes, so a list keeps its shape, and the entry holds the list so its
    /// address isn't reused. A statement then walks only the parts of its types that are new,
    /// not the whole of a deep type it got from a local.
    shapes: RefCell<Shapes>,
    /// How deeply each type argument list without a variable nests, and whether it has an
    /// error, by address, kept as `shapes` is, so a chain of `let`s that each wrap the one
    /// before costs each its own level.
    depths: RefCell<Depths>,
    /// What each bound variable stands for once nothing in it is open, by variable. A bound
    /// variable never changes, so a walk need not go through it again, and a chain of calls
    /// whose types hold the one before costs each call its own part only.
    ground: RefCell<Vec<Option<Ty>>>,
    /// Each variable in the order it was bound, so a statement can find the variables of the
    /// expressions around it that it gave a type.
    trail: Vec<u32>,
    /// The variables that settled as `Never` after a `todo` hole met them.
    holes: Vec<u32>,
    /// The type each list of parts that [`Vars::open_caps`] built was opened from, by address.
    /// Once its variables settle as they were, [`Vars::zonk`] gives back that type, so the
    /// copies opened from one shared part share it again, and a type that doubles at each
    /// level with a capability in it stays linear.
    origins: Origins,
}

type Origins = HashMap<usize, (Arc<[Ty]>, Ty), BuildHasherDefault<AddressHasher>>;
type Shapes = HashMap<usize, (Arc<[Ty]>, Shape), BuildHasherDefault<AddressHasher>>;
type Depths = HashMap<usize, (Arc<[Ty]>, u32, bool), BuildHasherDefault<AddressHasher>>;

/// The pairs of type argument lists that one [`Vars::subsume`] or [`Vars::join`] has walked,
/// by address, with the join of each. It holds the lists, so no address is reused while it
/// lives. Two types that share their parts within each but not with each other, as two
/// doubling chains built apart do, then cost each pair of parts once (issue #53).
#[derive(Default)]
struct Pairs {
    done: HashMap<(usize, usize, Option<Variance>), Option<Ty>>,
    held: Vec<Arc<[Ty]>>,
}

impl Pairs {
    fn key(a: &Arc<[Ty]>, b: &Arc<[Ty]>, v: Option<Variance>) -> (usize, usize, Option<Variance>) {
        (Arc::as_ptr(a) as *const Ty as usize, Arc::as_ptr(b) as *const Ty as usize, v)
    }

    /// Whether `actual` was found to fit `expected`, which is recorded only once it holds.
    fn get(&self, expected: &Arc<[Ty]>, actual: &Arc<[Ty]>) -> Option<&Option<Ty>> {
        self.done.get(&Self::key(expected, actual, None))
    }

    fn insert(&mut self, expected: &Arc<[Ty]>, actual: &Arc<[Ty]>) {
        self.done.insert(Self::key(expected, actual, None), None);
        self.held.extend([expected.clone(), actual.clone()]);
    }

    /// What `a` and `b` gave when they were bounded in direction `v`, if they were.
    fn get_in(&self, a: &Arc<[Ty]>, b: &Arc<[Ty]>, v: Variance) -> Option<&Option<Ty>> {
        self.done.get(&Self::key(a, b, Some(v)))
    }

    fn insert_in(&mut self, a: &Arc<[Ty]>, b: &Arc<[Ty]>, v: Variance, bounded: Ty) {
        self.done.insert(Self::key(a, b, Some(v)), Some(bounded));
        self.held.extend([a.clone(), b.clone()]);
    }
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
        self.depths.get_mut().clear();
        self.trail.clear();
        self.holes.clear();
        self.origins.clear();
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
            Ty::Var(_) => Shape { var: true, ..Shape::default() },
            Ty::Never => Shape { never: true, ..Shape::default() },
            Ty::Cap(_) | Ty::Reach(_) => Shape { cap: true, ..Shape::default() },
            _ if let Some(args) = ty.parts() => {
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some((_, shape)) = self.shapes.borrow().get(&key) {
                    return *shape;
                }
                let shape = args.iter().fold(Shape::default(), |acc, arg| {
                    let part = self.shape(arg);
                    Shape { var: acc.var || part.var, never: acc.never || part.never, cap: acc.cap || part.cap }
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
        self.states.push(State::Open(Open {
            kind,
            never: false,
            quiet: false,
            unmarked: false,
            owed: false,
            hole: false,
            handled: None,
            bounds: None,
            origin,
        }));
        Ty::Var(self.count() - 1)
    }

    /// A variable for a capability or a reach set that stays open, with `bounds`.
    fn bounds_var(&mut self, bounds: Bounds) -> Ty {
        let ty = self.fresh(Kind::Any, Origin::Defaulted);
        let Ty::Var(v) = ty else { unreachable!("fresh makes a variable") };
        let State::Open(open) = &mut self.states[v as usize] else { unreachable!("fresh is open") };
        open.bounds = Some(bounds);
        ty
    }

    /// A variable that only `Never` has reached, as a `Never` in an expected type is.
    fn never(&mut self) -> Ty {
        self.states.push(State::Open(Open {
            kind: Kind::Any,
            never: true,
            quiet: false,
            unmarked: false,
            owed: false,
            hole: false,
            handled: None,
            bounds: None,
            origin: Origin::Defaulted,
        }));
        Ty::Var(self.count() - 1)
    }

    /// A variable that a rejected value stands for in a type built from parts, such as a
    /// tuple's element, so the others keep their own type arguments (§15.1).
    pub fn rejected(&mut self) -> Ty {
        let ty = self.fresh(Kind::Any, Origin::Defaulted);
        self.quiet(&ty);
        ty
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

    /// How deeply `ty` nests with its variables' types in place, counting each type argument
    /// as a level, and whether it has an error in it; `None` when it nests more than `limit`
    /// levels. A part shared in many places is walked once, so a type that doubles at each
    /// level costs its depth, and the walk stops at `limit`, however deep the type is.
    pub fn depth(&self, ty: &Ty, limit: u32) -> Option<(u32, bool)> {
        self.depth_part(ty, limit, &mut HashMap::new())
    }

    fn depth_part(&self, ty: &Ty, room: u32, memo: &mut HashMap<usize, (u32, bool)>) -> Option<(u32, bool)> {
        let ty = self.resolve(ty);
        let Some(parts) = ty.parts() else { return (room > 0).then_some((1, ty == Ty::Error)) };
        let key = Arc::as_ptr(parts) as *const Ty as usize;
        let known = memo.get(&key).copied().or_else(|| self.depths.borrow().get(&key).map(|&(_, d, e)| (d, e)));
        if let Some((depth, error)) = known {
            return (depth <= room).then_some((depth, error));
        }
        let (mut depth, mut error) = (0, false);
        for part in parts.iter() {
            let (d, e) = self.depth_part(part, room.checked_sub(1)?, memo)?;
            (depth, error) = (depth.max(d), error || e);
        }
        // A variable in it may be bound later, which changes its depth.
        if self.has_var(&ty) {
            memo.insert(key, (depth + 1, error));
        } else {
            self.depths.borrow_mut().insert(key, (parts.clone(), depth + 1, error));
        }
        Some((depth + 1, error))
    }

    /// `ty` with every bound variable replaced, at any depth. Parts without one are shared.
    pub fn zonk(&self, ty: &Ty) -> Ty {
        self.zonk_part(ty, &mut HashMap::new()).unwrap_or_else(|| ty.clone())
    }

    /// [`Vars::zonk`], or `None` where nothing changes. A type argument list in `seen`, by
    /// address, was zonked already, so a type that repeats a part with an open variable in
    /// it, which no variable keeps as ground, costs its distinct parts.
    fn zonk_part(&self, ty: &Ty, seen: &mut HashMap<usize, Option<Ty>>) -> Option<Ty> {
        match ty {
            Ty::Var(v) => match &self.states[*v as usize] {
                State::Open(_) => None,
                State::Bound(next) => {
                    if let Some(ty) = self.ground_of(*v) {
                        return Some(ty);
                    }
                    let ty = self.zonk_part(next, seen).unwrap_or_else(|| next.clone());
                    if !self.has_var(&ty) {
                        self.keep_ground(*v, ty.clone());
                    }
                    Some(ty)
                }
            },
            _ if self.has_var(ty)
                && let Some(args) = ty.parts() =>
            {
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some(done) = seen.get(&key) {
                    return done.clone();
                }
                let parts: Vec<Option<Ty>> = args.iter().map(|arg| self.zonk_part(arg, seen)).collect();
                let done = if parts.iter().all(Option::is_none) {
                    None
                } else {
                    let args: Vec<Ty> = parts
                        .into_iter()
                        .zip(args.iter())
                        .map(|(part, arg)| part.unwrap_or_else(|| arg.clone()))
                        .collect();
                    Some(self.origin_of(key, &args).unwrap_or_else(|| ty.with_parts(args)))
                };
                seen.insert(key, done.clone());
                done
            }
            _ => None,
        }
    }

    /// `ty` zonked, with an open literal variable as its default and any other open variable
    /// read as `Never`, which implements every interface as a type argument. A method found on
    /// it may need checking again once they settle.
    pub fn as_never(&self, ty: &Ty) -> Ty {
        self.as_never_part(ty, &mut HashMap::new())
    }

    /// [`Vars::as_never`], which reads each shared type argument list once, by address.
    fn as_never_part(&self, ty: &Ty, seen: &mut HashMap<usize, Ty>) -> Ty {
        match self.resolve(ty) {
            Ty::Var(v) => match self.open(v).map(|open| (open.kind, &open.bounds)) {
                Some((Kind::Int, _)) => Ty::INT,
                Some((Kind::Float, _)) => Ty::Float(FloatTy::F64),
                Some((_, Some(bounds))) => bounds.solution(),
                _ => Ty::Never,
            },
            ty if !self.has_var(&ty) => ty,
            ty if ty.parts().is_some() => {
                let args = ty.parts().expect("checked above");
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some(ty) = seen.get(&key) {
                    return ty.clone();
                }
                let done = ty.with_parts(args.iter().map(|arg| self.as_never_part(arg, seen)).collect());
                seen.insert(key, done.clone());
                done
            }
            ty => ty,
        }
    }

    /// `ty` zonked, with an open literal variable as its default, as diagnostics and interface
    /// checks see it. Any other open variable stays.
    pub fn defaulted(&self, ty: &Ty) -> Ty {
        self.defaulted_part(ty, &mut HashMap::new())
    }

    /// [`Vars::defaulted`], where `memo` holds what each shared part gave.
    fn defaulted_part(&self, ty: &Ty, memo: &mut HashMap<usize, Ty>) -> Ty {
        match self.resolve(ty) {
            Ty::Var(v) => match self.open(v).map(|open| (open.kind, open.never, &open.bounds)) {
                Some((Kind::Int, ..)) => Ty::INT,
                Some((Kind::Float, ..)) => Ty::Float(FloatTy::F64),
                Some((_, _, Some(bounds))) => bounds.solution(),
                // Only `Never` has reached it, as a closure's error type when nothing fails.
                Some((_, true, _)) => Ty::Never,
                _ => Ty::Var(self.root(v)),
            },
            ty if self.has_var(&ty) && ty.parts().is_some() => {
                let args = ty.parts().expect("checked above");
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some(known) = memo.get(&key) {
                    return known.clone();
                }
                let done = ty.with_parts(args.iter().map(|arg| self.defaulted_part(arg, memo)).collect());
                memo.insert(key, done.clone());
                done
            }
            ty => ty,
        }
    }

    /// The open variables in `ty`, by their roots, each once and in order.
    pub fn open_in(&self, ty: &Ty, found: &mut Vec<u32>) {
        self.open_part(ty, found, &mut HashMap::new());
    }

    /// [`Vars::open_in`], which also says whether it found any, so a bound variable with none
    /// in it is kept as ground. A type argument list in `seen`, by address, was walked already.
    fn open_part(&self, ty: &Ty, found: &mut Vec<u32>, seen: &mut HashMap<usize, bool>) -> bool {
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
                    let open = self.open_part(next, found, seen);
                    if !open {
                        self.keep_ground(*v, self.zonk(next));
                    }
                    open
                }
            },
            _ if let Some(args) = ty.parts() => {
                let key = Arc::as_ptr(args) as *const Ty as usize;
                if let Some(&open) = seen.get(&key) {
                    return open;
                }
                // Every part is walked, also after one has an open variable, to find them all.
                let mut open = false;
                for arg in args.iter() {
                    open |= self.open_part(arg, found, seen);
                }
                seen.insert(key, open);
                open
            }
            _ => false,
        }
    }

    pub fn has_open(&self, ty: &Ty) -> bool {
        let mut found = Vec::new();
        self.open_in(ty, &mut found);
        !found.is_empty()
    }

    /// Settles `ty` as `Never` where it is a variable that only `Never` has reached, so no
    /// later place widens it. An effect parameter's error part comes from the arguments
    /// alone (REFERENCE §9.5). A literal's variable keeps its default, as a literal does.
    pub fn close_never(&mut self, ty: &Ty) {
        if let Ty::Var(v) = self.resolve(ty)
            && self.open(v).is_some_and(|open| open.never && open.kind == Kind::Any)
        {
            self.settle(v, Ty::Never);
        }
    }

    /// Whether `ty` is a variable that only `Never` has reached.
    pub fn only_never(&self, ty: &Ty) -> bool {
        matches!(self.resolve(ty), Ty::Var(v) if self.open(v).is_some_and(|open| open.never))
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
        self.mark(ty, |open| open.quiet = true);
    }

    /// Marks every open variable in `ty` as the error type of a call without a marker.
    pub fn unmarked(&mut self, ty: &Ty) {
        self.mark(ty, |open| open.unmarked = true);
    }

    /// Marks every open variable in `ty` as one a `todo` hole met.
    pub fn hole(&mut self, ty: &Ty) {
        self.mark(ty, |open| open.hole = true);
    }

    /// Notes that open variable `v`, which a `todo` hole met, settles as `Never`.
    pub fn settled_hole(&mut self, v: u32) {
        self.holes.push(self.root(v));
    }

    /// Whether `ty` is a variable that settled as `Never` after a `todo` hole met it.
    pub fn from_hole(&self, ty: &Ty) -> bool {
        let mut ty = ty;
        while let Ty::Var(v) = ty {
            if self.holes.contains(v) {
                return true;
            }
            match &self.states[*v as usize] {
                State::Bound(next) => ty = next,
                State::Open(_) => return false,
            }
        }
        false
    }

    /// Whether open variable `v` is in the error type of a call a handler marks.
    pub fn handled(&self, v: u32) -> bool {
        self.open(v).is_some_and(|open| open.handled.is_some())
    }

    /// Marks every open variable in `ty` as one that the handler at `depth` joins, or, with
    /// `on` false, no longer one that it or a handler inside it joins. It walks each shared
    /// part once, so a wide or deeply shared type costs its distinct parts.
    pub fn set_handled(&mut self, ty: &Ty, depth: u32, on: bool) {
        let mut found = Vec::new();
        self.each_open(ty, &mut found, &mut (HashSet::new(), HashSet::new()));
        for v in found {
            if let State::Open(open) = &mut self.states[v as usize] {
                open.handled = match open.handled {
                    _ if !on => open.handled.filter(|&d| d < depth),
                    Some(d) => Some(d.min(depth)),
                    None => Some(depth),
                };
            }
        }
    }

    /// Whether open variable `v`'s class occurs in `ty`, walking each shared part once.
    pub fn mentions(&self, v: u32, ty: &Ty) -> bool {
        let mut found = Vec::new();
        self.each_open(ty, &mut found, &mut (HashSet::new(), HashSet::new()));
        let v = self.root(v);
        found.contains(&v)
    }

    /// The open variables in `ty`, by their roots, maybe more than once. A bound variable or
    /// a type argument list in `seen`, by number or by address, was walked already.
    fn each_open(&self, ty: &Ty, found: &mut Vec<u32>, seen: &mut (HashSet<u32>, HashSet<usize>)) {
        if !self.has_var(ty) {
            return;
        }
        match ty {
            Ty::Var(v) => match &self.states[*v as usize] {
                State::Open(_) => found.push(*v),
                State::Bound(next) => {
                    if self.ground_of(*v).is_none() && seen.0.insert(*v) {
                        self.each_open(next, found, seen);
                    }
                }
            },
            _ if let Some(args) = ty.parts()
                && seen.1.insert(Arc::as_ptr(args) as *const Ty as usize) =>
            {
                args.iter().for_each(|arg| self.each_open(arg, found, seen));
            }
            _ => {}
        }
    }

    /// Marks every open variable in `ty` as one a `try` with no `fails` to take it needs.
    pub fn owe(&mut self, ty: &Ty) {
        self.mark(ty, |open| open.owed = true);
    }

    fn mark(&mut self, ty: &Ty, set: impl Fn(&mut Open)) {
        let mut found = Vec::new();
        self.open_in(ty, &mut found);
        for v in found {
            if let State::Open(open) = &mut self.states[v as usize] {
                set(open);
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

    /// `ty` with each capability in it a variable whose permissions stay open, where a value of
    /// type `ty` flows `flow` (OPEN_QUESTIONS P3, decided for phase 3), and each `Never` that
    /// flows in a variable that a later value may widen. A function type's parameters flow
    /// the other way, and an `inout` one keeps its permissions, since what is passed must have
    /// exactly those. Parts without either are shared.
    fn open_caps(&mut self, ty: &Ty, flow: Flow) -> Ty {
        self.open_caps_part(ty, flow, &mut HashMap::new()).unwrap_or_else(|| ty.clone())
    }

    /// [`Vars::open_caps`], or `None` where nothing changes. A list of parts in `seen`, by
    /// address and flow, was opened already, so a type that shares its parts costs each part
    /// once (issue #55), and a shared part's capabilities share their variables.
    fn open_caps_part(&mut self, ty: &Ty, flow: Flow, seen: &mut HashMap<(usize, Flow), Option<Ty>>) -> Option<Ty> {
        match ty {
            Ty::Cap(_) | Ty::Reach(_) => {
                return Some(self.bounds_var(Bounds::of(ty, flow).expect("a capability or a reach set")));
            }
            // A `Never` that flows in, as a function's result does, may widen, as one in a type
            // argument does (see [`Vars::open_nevers`]).
            Ty::Never if flow == Flow::In => return Some(self.never()),
            _ => {}
        }
        // A part without either is shared, and its shape is known once.
        let shape = self.shape(ty);
        if !shape.cap && !(shape.never && flow == Flow::In) {
            return None;
        }
        let parts = ty.parts()?;
        let key = (Arc::as_ptr(parts) as *const Ty as usize, flow);
        if let Some(done) = seen.get(&key) {
            return done.clone();
        }
        let new: Vec<Option<Ty>> = match ty {
            Ty::Fn(modes, _) => (parts.iter().enumerate())
                .map(|(i, part)| match i.checked_sub(FN_PARAMS).map(|p| modes[p]) {
                    None => self.open_caps_part(part, flow, seen),
                    Some(ParamMode::Inout | ParamMode::InoutPartial) => None,
                    Some(_) => self.open_caps_part(part, flow.flip(), seen),
                })
                .collect(),
            _ => parts.iter().map(|arg| self.open_caps_part(arg, flow, seen)).collect(),
        };
        let done = self.rebuilt(ty, parts, new);
        seen.insert(key, done.clone());
        done
    }

    /// `ty` built from its `parts` with those in `new` replaced, or `None` when none is. The
    /// new type's parts remember `ty` as their origin.
    fn rebuilt(&mut self, ty: &Ty, parts: &Arc<[Ty]>, new: Vec<Option<Ty>>) -> Option<Ty> {
        if new.iter().all(Option::is_none) {
            return None;
        }
        let built = ty
            .with_parts(new.into_iter().zip(parts.iter()).map(|(n, part)| n.unwrap_or_else(|| part.clone())).collect());
        if let Some(list) = built.parts() {
            self.origins.insert(Arc::as_ptr(list) as *const Ty as usize, (list.clone(), ty.clone()));
        }
        Some(built)
    }

    /// The type that the list of parts at `key` was opened from, when `parts`, what that list
    /// zonks to, are that type's own parts again. A part is compared by the address of its
    /// own parts, so this costs the length of the list.
    fn origin_of(&self, key: usize, parts: &[Ty]) -> Option<Ty> {
        let (_, origin) = self.origins.get(&key)?;
        let own = origin.parts()?;
        let same = |a: &Ty, b: &Ty| match (a.parts(), b.parts()) {
            (Some(x), Some(y)) => Arc::ptr_eq(x, y),
            (None, None) => a == b,
            _ => false,
        };
        (own.len() == parts.len() && own.iter().zip(parts).all(|(a, b)| same(a, b))).then(|| origin.clone())
    }

    /// Whether a value of type `ty` may flow `flow` through open variable `v`, a capability or
    /// reach set with `bounds`, which narrows them.
    fn bounds_meet(&mut self, v: u32, bounds: &Bounds, ty: &Ty, flow: Flow) -> bool {
        let Some(met) = Bounds::of(ty, flow).and_then(|other| bounds.meet(&other)) else { return false };
        let State::Open(open) = &mut self.states[v as usize] else { unreachable!("roots are open") };
        open.bounds = Some(met);
        true
    }

    /// Whether variable `v` occurs in `ty`, which would make it part of itself.
    fn occurs(&self, v: u32, ty: &Ty) -> bool {
        self.occurs_in(v, ty, &mut HashSet::new())
    }

    /// [`Vars::occurs`], where `seen` holds the argument lists and bound variables walked
    /// already, so a type that shares its parts costs each part once.
    fn occurs_in(&self, v: u32, ty: &Ty, seen: &mut HashSet<usize>) -> bool {
        if !self.has_var(ty) {
            return false;
        }
        match ty {
            Ty::Var(w) => match &self.states[*w as usize] {
                State::Open(_) => *w == v,
                // A variable's key is odd, which no list's address is.
                State::Bound(next) => {
                    self.ground_of(*w).is_none() && seen.insert(2 * *w as usize + 1) && self.occurs_in(v, next, seen)
                }
            },
            _ if let Some(args) = ty.parts() => {
                seen.insert(Arc::as_ptr(args) as *const Ty as usize)
                    && args.iter().any(|arg| self.occurs_in(v, arg, seen))
            }
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
        let bounds = match (&kept.bounds, &other.bounds) {
            (Some(a), Some(b)) => match a.meet(b) {
                Some(met) => Some(met),
                None => return false,
            },
            (Some(bounds), None) | (None, Some(bounds)) if kind == Kind::Any => Some(bounds.clone()),
            (Some(_), None) | (None, Some(_)) => return false,
            (None, None) => None,
        };
        let never = kept.never || other.never;
        let quiet = kept.quiet || other.quiet;
        let unmarked = kept.unmarked || other.unmarked;
        let owed = kept.owed || other.owed;
        let hole = kept.hole || other.hole;
        let handled = kept.handled.into_iter().chain(other.handled).min();
        // An error about the class names the value that first left it open.
        let origin = if matches!(kept.origin, Origin::Defaulted) { other.origin } else { kept.origin };
        self.states[keep as usize] =
            State::Open(Open { kind, never, quiet, unmarked, owed, hole, handled, bounds, origin });
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
        if let Some(bounds) = open.bounds.clone() {
            return self.bounds_meet(v, &bounds, ty, Flow::In);
        }
        let (kind, marks) = (open.kind, (open.quiet, open.hole, open.handled));
        if !Self::fits(kind, ty) || self.occurs(v, ty) {
            return false;
        }
        let ty = self.open_nevers(ty);
        let ty = self.open_caps(&ty, Flow::In);
        self.bind_marks(marks, &ty);
        self.settle(v, ty);
        true
    }

    /// A variable that a rejected value was to give, that a `todo` hole met, or that a
    /// handler joins, bound to `ty`, passes that on to what `ty` leaves open.
    fn bind_marks(&mut self, (quiet, hole, handled): (bool, bool, Option<u32>), ty: &Ty) {
        if quiet {
            self.quiet(ty);
        }
        if hole {
            self.hole(ty);
        }
        if let Some(depth) = handled {
            self.set_handled(ty, depth, true);
        }
    }

    /// Variable `v` is exactly `ty`: its value must fit where a `ty` is required.
    fn exact(&mut self, v: u32, ty: &Ty) -> bool {
        let v = self.root(v);
        let State::Open(open) = &self.states[v as usize] else { unreachable!("roots are open") };
        if let Some(bounds) = open.bounds.clone() {
            return self.bounds_meet(v, &bounds, ty, Flow::Out);
        }
        let marks = (open.quiet, open.hole, open.handled);
        if !Self::fits(open.kind, ty) || self.occurs(v, ty) {
            return false;
        }
        let ty = self.open_caps(ty, Flow::Out);
        self.bind_marks(marks, &ty);
        self.settle(v, ty);
        true
    }

    /// Whether a value of type `actual` may be used where `expected` is required, binding
    /// variables so that it may. `Never` is a subtype of every type, also as a type argument
    /// (REFERENCE §9.2), and an error fits everything, so it is reported once.
    pub fn subsume(&mut self, expected: &Ty, actual: &Ty) -> bool {
        self.subsume_in(expected, actual, &mut Pairs::default())
    }

    /// [`Vars::subsume`], where `pairs` holds the pairs of parts that already fit.
    fn subsume_in(&mut self, expected: &Ty, actual: &Ty, pairs: &mut Pairs) -> bool {
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
                if Arc::ptr_eq(args, actual_args) || pairs.get(args, actual_args).is_some() {
                    return true;
                }
                let fits = args.iter().zip(actual_args.iter()).all(|(arg, actual)| self.subsume_in(arg, actual, pairs));
                if fits {
                    pairs.insert(args, actual_args);
                }
                fits
            }
            // A function value fits a function type whose parameters it accepts, with the
            // same modes, whose result it gives, and whose error it fails with, if any
            // (OPEN_QUESTIONS P5).
            (Ty::Fn(modes, parts), Ty::Fn(actual_modes, actual_parts)) if modes == actual_modes => {
                if Arc::ptr_eq(parts, actual_parts) || pairs.get(parts, actual_parts).is_some() {
                    return true;
                }
                // An `inout` parameter's value goes in and comes back, so its type must be the
                // same both ways. Its `uses` must cover the value's (REFERENCE §9.4).
                let fits = (0..FN_PARAMS).all(|i| self.subsume_in(&parts[i], &actual_parts[i], pairs))
                    && (parts[FN_PARAMS..].iter().zip(&actual_parts[FN_PARAMS..]).zip(modes.iter())).all(
                        |((param, actual), mode)| {
                            self.subsume_in(actual, param, pairs)
                                && (!mode.is_inout() || self.subsume_in(param, actual, pairs))
                        },
                    );
                if fits {
                    pairs.insert(parts, actual_parts);
                }
                fits
            }
            // A capability fits where fewer permissions are expected and its `uses` are covered
            // (REFERENCE §9.2).
            (Ty::Cap(expected), Ty::Cap(actual)) => {
                expected.iface == actual.iface
                    && expected.perms.is_subset(actual.perms)
                    && actual.uses.covered_by(&expected.uses)
            }
            (Ty::Reach(expected), Ty::Reach(actual)) => actual.covered_by(expected),
            (expected, actual) => expected == actual,
        }
    }

    /// The type of a value that is either an `a` or a `b`, binding variables so that there
    /// is one. `Never` gives way to the other side, also as a type argument, so
    /// `Option[Never]` and `Option[Int]` join to `Option[Int]`. `None` when there is none.
    pub fn join(&mut self, a: &Ty, b: &Ty) -> Option<Ty> {
        self.bound_in(a, b, Variance::Co, &mut Pairs::default())
    }

    /// The type that bounds `a` and `b` from above, as [`Vars::join`] does, or, `Contra`, from
    /// below: the type of a parameter that takes either, so a function that takes it serves
    /// as either. Each case holds both directions, and a function's parameters flip it, so the
    /// two can't drift apart (OPEN_QUESTIONS P3, decided for phase 3). Nothing in it depends
    /// on which of `a` and `b` comes first. `pairs` holds the bounds of the pairs of parts
    /// already bounded, by direction.
    fn bound_in(&mut self, a: &Ty, b: &Ty, v: Variance, pairs: &mut Pairs) -> Option<Ty> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Error, other) | (other, Ty::Error) => {
                self.poison(other);
                Some(Ty::Error)
            }
            (Ty::Var(x), Ty::Var(y)) => self.union(*x, *y).then(|| self.resolve(&a)),
            // Above, a value flows into the variable. Below, what either needs flows out to it,
            // and `Never` still meets a variable whose kind or permissions it can't settle, such
            // as an integer literal's, which then defaults as it would.
            (Ty::Var(x), ty) | (ty, Ty::Var(x)) => {
                let x = *x;
                match v {
                    Variance::Co => self.lower(x, ty).then(|| self.resolve(&Ty::Var(x))),
                    Variance::Contra if self.exact(x, ty) => Some(self.resolve(&Ty::Var(x))),
                    Variance::Contra => (*ty == Ty::Never).then_some(Ty::Never),
                }
            }
            // `Never` is a subtype of every type (REFERENCE §9.2), so it gives way above and
            // serves as either below.
            (Ty::Never, ty) | (ty, Ty::Never) => Some(if v == Variance::Co { ty.clone() } else { Ty::Never }),
            (Ty::Adt(id, args), Ty::Adt(other, other_args)) if id == other && args.len() == other_args.len() => {
                if Arc::ptr_eq(args, other_args) {
                    return Some(a.clone());
                }
                if let Some(Some(known)) = pairs.get_in(args, other_args, v) {
                    return Some(known.clone());
                }
                let parts = (args.iter().zip(other_args.iter()))
                    .map(|(x, y)| self.bound_in(x, y, v, pairs))
                    .collect::<Option<Vec<_>>>()?;
                let bounded = Ty::applied(*id, parts);
                pairs.insert_in(args, other_args, v, bounded.clone());
                Some(bounded)
            }
            // A function's result and error vary as it does, and its parameters against it, so
            // above it takes what either function needs and gives what either gives. An `inout`
            // parameter goes in and comes back, so it must be the same.
            (Ty::Fn(modes, parts), Ty::Fn(other_modes, other_parts)) if modes == other_modes => {
                if Arc::ptr_eq(parts, other_parts) {
                    return Some(a.clone());
                }
                if let Some(Some(known)) = pairs.get_in(parts, other_parts, v) {
                    return Some(known.clone());
                }
                let mut bounded = Vec::with_capacity(parts.len());
                for (i, (x, y)) in parts.iter().zip(other_parts.iter()).enumerate() {
                    bounded.push(match i.checked_sub(FN_PARAMS).map(|p| modes[p]) {
                        None => self.bound_in(x, y, v, pairs)?,
                        Some(mode) if mode.is_inout() => self.same(x, y)?,
                        Some(_) => self.bound_in(x, y, v.flip(), pairs)?,
                    });
                }
                let bounded = a.with_parts(bounded);
                pairs.insert_in(parts, other_parts, v, bounded.clone());
                Some(bounded)
            }
            // A value that is either capability has the permissions both have and uses what
            // either uses, and a parameter that takes either needs every permission either needs
            // and admits only what both admit.
            (Ty::Cap(x), Ty::Cap(y)) if x.iface == y.iface => Some(match v {
                Variance::Co => Ty::cap_uses(x.iface, x.perms.intersect(y.perms), x.uses.union(&y.uses)),
                Variance::Contra => Ty::cap_uses(x.iface, x.perms.union(y.perms), x.uses.intersect(&y.uses)),
            }),
            (Ty::Reach(x), Ty::Reach(y)) => Some(Ty::reach(match v {
                Variance::Co => x.union(y),
                Variance::Contra => x.intersect(y),
            })),
            (x, y) => (x == y).then(|| a.clone()),
        }
    }

    /// `a`, binding variables so that `b` is the same type, or `None` when it can't be.
    fn same(&mut self, a: &Ty, b: &Ty) -> Option<Ty> {
        (self.subsume(a, b) && self.subsume(b, a)).then(|| a.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Types to bound in pairs: scalars, `Never` and capabilities with several permission
    /// sets, and each of them as a type argument, a result and a parameter of each mode.
    fn universe() -> Vec<Ty> {
        let net = |bits| Ty::cap(IfaceId::NET, Perms(bits));
        let leaves = vec![
            Ty::INT,
            Ty::Text,
            Ty::Never,
            Ty::out(),
            Ty::cap(IfaceId::OUT, Perms::NONE),
            net(0),
            net(1),
            net(2),
            net(3),
        ];
        let takes = |mode, x: Ty| Ty::func(vec![mode], vec![x], Ty::Unit, Ty::Never);
        let gives = |x: Ty| Ty::func(Vec::new(), Vec::new(), x, Ty::Never);
        let mut all = leaves.clone();
        for x in &leaves {
            all.push(Ty::option(x.clone()));
            all.push(Ty::result(x.clone(), Ty::Text));
            all.push(gives(x.clone()));
            all.push(Ty::func(Vec::new(), Vec::new(), Ty::Unit, x.clone()));
            all.push(takes(ParamMode::Borrow, x.clone()));
            all.push(takes(ParamMode::Inout, x.clone()));
            all.push(takes(ParamMode::Borrow, takes(ParamMode::Borrow, x.clone())));
            all.push(Ty::option(takes(ParamMode::Take, Ty::option(x.clone()))));
        }
        all
    }

    fn show(ty: &Ty) -> String {
        crate::tests::std_decls().display(ty).to_string()
    }

    fn bound(a: &Ty, b: &Ty, v: Variance) -> Option<Ty> {
        let mut vars = Vars::default();
        let bounded = vars.bound_in(a, b, v, &mut Pairs::default())?;
        Some(vars.defaulted(&bounded))
    }

    /// Bounding two types gives the same type in either order, a type bounded with itself
    /// is that type, and each input fits the bound: a value of either type where the join is
    /// expected, and a value of the meet where either is (OPEN_QUESTIONS P3).
    #[test]
    fn bounds_are_symmetric_idempotent_and_bound_their_inputs() {
        let all = universe();
        for v in [Variance::Co, Variance::Contra] {
            for a in &all {
                assert_eq!(bound(a, a, v).as_ref(), Some(a), "{v:?} of {} with itself", show(a));
                for b in &all {
                    let (ab, ba) = (bound(a, b, v), bound(b, a, v));
                    let pair = format!("{v:?} of {} and {}", show(a), show(b));
                    assert_eq!(ab, ba, "{pair} depends on their order");
                    let Some(ab) = ab else { continue };
                    for input in [a, b] {
                        let fits = match v {
                            Variance::Co => Vars::default().subsume(&ab, input),
                            Variance::Contra => Vars::default().subsume(input, &ab),
                        };
                        assert!(fits, "{pair} is {}, which doesn't bound {}", show(&ab), show(input));
                    }
                }
            }
        }
    }

    /// Whether `ty` has a `Never` where a function takes it: a parameter, or the result of a
    /// function-typed parameter. Such a part can't narrow once a variable holds it, which is
    /// a limit of inference (OPEN_QUESTIONS P5).
    fn takes_never(ty: &Ty, flipped: bool) -> bool {
        match ty {
            Ty::Never => flipped,
            Ty::Fn(..) => {
                let (_, ret, fails, params) = ty.fn_parts().expect("a function type");
                takes_never(ret, flipped)
                    || takes_never(fails, flipped)
                    || params.iter().any(|param| takes_never(param, !flipped))
            }
            _ => ty.parts().is_some_and(|parts| parts.iter().any(|part| takes_never(part, flipped))),
        }
    }

    /// Two values that flow into one variable, as two arguments for one type parameter do,
    /// give it their join, whichever flows in first.
    #[test]
    fn values_flowing_into_a_variable_give_their_join_in_either_order() {
        let all: Vec<Ty> = universe().into_iter().filter(|ty| !takes_never(ty, false)).collect();
        let flow = |first: &Ty, second: &Ty| {
            let mut vars = Vars::default();
            let var = vars.fresh(Kind::Any, Origin::Defaulted);
            (vars.subsume(&var, first) && vars.subsume(&var, second)).then(|| vars.defaulted(&var))
        };
        for a in &all {
            for b in &all {
                let pair = format!("{} and {}", show(a), show(b));
                let (ab, ba) = (flow(a, b), flow(b, a));
                assert_eq!(ab, ba, "{pair} flowing into a variable depends on their order");
                assert_eq!(ab, bound(a, b, Variance::Co), "{pair} flowing into a variable isn't their join");
            }
        }
    }
}
