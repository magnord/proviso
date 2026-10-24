//! Moves and exclusive access (REFERENCE §5.1–§5.3), checked over a function body once its
//! types are settled.
//!
//! A value of a unique type, or an owned value of a type parameter without `Copy`, moves
//! wherever the checker found it copied (its `consumed` expressions), and
//! wherever a pattern binds its parts. The walk tracks which places may have moved: a local,
//! or a field of one at any depth. A use of a place that may have moved, or of a record one
//! of whose fields may have, is a use after move (E0501). Branches join what they moved, and
//! a loop's body is walked until what may have moved at its head stops growing, so a move
//! in one turn reaches the uses of the next. A lent place, a borrowed or `inout` parameter
//! or a part of one, never moves (E0504), and neither does what an arm's pattern binds while
//! its guard runs. A guard that fails hands the later arms what it moved, but not what the
//! pattern did, since the scrutinee leaves only once an arm is chosen.
//!
//! Within one call, an `&` argument and an `inout self` receiver begin their access once the
//! other arguments are evaluated, as in Swift (SE-0176), and keep it for the call. Two of
//! them may not overlap, and a unique value lent to the call by one argument may not move in
//! a later one (E0505; OPEN_QUESTIONS P5).
//!
//! Resources (REFERENCE §10) are tracked twice: a resource may have moved (E0501), and it
//! is released where it has moved, or holds none, on every path. Each owned resource must be
//! released at every normal exit of its scope (E0507), and nothing may overwrite or drop one
//! (E0508). The pass records what the interpreter needs to abandon them on a failure exit:
//! the bindings that own one, the parts a pattern moves out of a place, and the values a call
//! or a literal holds while its later arguments run.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, Planned, codes};
use proviso_syntax::source::Span;

use crate::decls::{AdtId, FieldIdx, IfaceId, VariantIdx};
use crate::types::Ty;
use crate::{Local, LocalId, Program, Res};

/// What the checker found about the expressions of a body.
pub(crate) struct Found {
    /// The expressions whose values are copied, or moved when their type is unique.
    pub consumed: HashSet<ExprId>,
    /// The expressions an error was reported at, not at one of their parts.
    pub rejected: HashSet<ExprId>,
    /// Where the checker reported errors in the body, which the resources reported here must
    /// not depend on (REFERENCE §15.1).
    pub errors: Vec<Span>,
}

/// What the move pass walks.
pub(crate) enum Body<'a> {
    /// A function's body.
    Fn(FnBody<'a>),
    /// A refinement, whose fields are lent to it.
    Predicate(ExprId),
    /// An example's call and the value it is compared with, which it drops.
    Example { call: ExprId, expected: Option<ExprId> },
}

/// A function's body, with what it owns from the start.
pub(crate) struct FnBody<'a> {
    pub block: &'a Block,
    /// Its owned resource parameters, `take` ones and a `take self`, with their spans and
    /// names.
    pub params: Vec<(LocalId, Span, String)>,
    /// It is a `take self` method of a base resource, which consumes `self` when it returns
    /// once the resources `self` holds are consumed (OPEN_QUESTIONS Q35).
    pub consumes_self: bool,
}

/// Checks the moves and accesses of `body`, whose locals are `locals` and whose type
/// parameters implement `bounds`, given the expressions the checker found `consumed`.
/// Records each expression that moves a whole local in [`Program::moves_out`], each `match`
/// arm whose pattern does in [`Program::arms_out`], and what the interpreter needs to
/// abandon resources. Returns the locals the body uses.
pub(crate) fn check(
    m: &Module,
    p: &mut Program,
    locals: &[Local],
    bounds: &[Vec<IfaceId>],
    found: &Found,
    body: Body,
    diags: &mut Diagnostics,
) -> HashSet<LocalId> {
    let mut walk = Walk {
        m,
        p,
        locals,
        bounds,
        consumed: &found.consumed,
        rejected: &found.rejected,
        checked: &found.errors,
        state: Some(State::default()),
        loops: Vec::new(),
        reported: HashSet::new(),
        errors: Vec::new(),
        later: Vec::new(),
        lent: Vec::new(),
        handled: HashMap::new(),
        loop_cache: HashMap::new(),
        memo: RefCell::new(HashMap::new()),
        touched: Vec::new(),
        reach: usize::MAX,
        moves_out: HashSet::new(),
        arms_out: HashSet::new(),
        guarded: Vec::new(),
        scopes: Vec::new(),
        pending: Vec::new(),
        consumes_self: false,
        used: HashSet::new(),
        held: HashSet::new(),
        owned_binds: HashSet::new(),
        parts_out: HashMap::new(),
        unscheduled: Vec::new(),
        refused: HashSet::new(),
        excused: HashSet::new(),
    };
    match body {
        Body::Fn(body) => {
            walk.consumes_self = body.consumes_self;
            walk.scopes.push(body.params);
            walk.block(body.block);
            walk.close_scope("the end of the function");
        }
        Body::Predicate(e) => walk.expr(e),
        Body::Example { call, expected } => {
            for e in std::iter::once(call).chain(expected) {
                walk.expr(e);
                // An example with an error may not compare at all (REFERENCE §15.1).
                if found.errors.is_empty() {
                    walk.discarded(e, "the example drops once it has compared it");
                }
            }
        }
    }
    let Walk { errors, later, moves_out, arms_out, unscheduled, held, owned_binds, parts_out, used, .. } = walk;
    for (code, span, message) in errors {
        diags.error(code, span, message);
    }
    for span in later {
        diags.not_implemented(
            span,
            "`&` accesses to two elements whose indices only a fact can tell apart (§5.3)",
            Planned::Phase(5),
        );
    }
    for (span, what) in unscheduled {
        diags.not_implemented(span, &what, Planned::Unscheduled);
    }
    for e in moves_out {
        p.moves_out.insert(e, ());
    }
    for pat in arms_out {
        p.arms_out.insert(pat, ());
    }
    for e in held {
        p.held.insert(e, ());
    }
    for pat in owned_binds {
        p.owned_binds.insert(pat, ());
    }
    for (pat, paths) in parts_out {
        p.parts_out.insert(pat, paths.into_iter().map(Vec::into_boxed_slice).collect());
    }
    used
}

/// A local, or a field of one, by the index of each field on the way.
type Path = Vec<u32>;

/// What may have moved at a point of the body that is reached: each place, by its local's
/// index and its path, with how diagnostics write it. The map is shared until it changes,
/// so a branch that moves nothing costs nothing to copy or join.
#[derive(Clone, Default)]
struct State {
    moved: Arc<BTreeMap<(u32, Path), String>>,
    /// The places that hold no resource on every path here: those that moved, and those
    /// found to hold none, such as a value an arm's variant shows to be `None` (§10 rule 2).
    released: Arc<BTreeSet<(u32, Path)>>,
}

impl State {
    /// The places of `local` that may have moved, with how diagnostics write each.
    fn of(&self, local: LocalId) -> impl Iterator<Item = (&Path, &String)> {
        self.moved.range((local.0, Vec::new())..).take_while(move |((l, _), _)| *l == local.0).map(|((_, p), d)| (p, d))
    }

    /// Forgets the places of `local` whose paths `keep` rejects.
    fn forget(&mut self, local: LocalId, keep: impl Fn(&Path) -> bool) {
        let gone: Vec<Path> = self.of(local).filter(|(p, _)| !keep(p)).map(|(p, _)| p.clone()).collect();
        if gone.is_empty() {
            return;
        }
        let moved = Arc::make_mut(&mut self.moved);
        for path in gone {
            moved.remove(&(local.0, path));
        }
    }

    /// Whether every place `other` holds is in this one too.
    fn covers(&self, other: &State) -> bool {
        Arc::ptr_eq(&self.moved, &other.moved) || other.moved.keys().all(|key| self.moved.contains_key(key))
    }

    /// Whether every place this one has released, `other` has too.
    fn released_in(&self, other: &State) -> bool {
        Arc::ptr_eq(&self.released, &other.released) || self.released.is_subset(&other.released)
    }

    /// Whether `other` adds nothing to what may have moved here, and releases all this does.
    fn holds(&self, other: &State) -> bool {
        self.covers(other) && self.released_in(other)
    }

    fn release(&mut self, local: LocalId, path: Path) {
        if !self.released.contains(&(local.0, path.clone())) {
            Arc::make_mut(&mut self.released).insert((local.0, path));
        }
    }

    /// Forgets that the places of `local` that `gone` accepts are released.
    fn unrelease(&mut self, local: LocalId, gone: impl Fn(&Path) -> bool) {
        let range = (local.0, Vec::new())..;
        let found: Vec<Path> = self
            .released
            .range(range)
            .take_while(|(l, _)| *l == local.0)
            .filter(|(_, p)| gone(p))
            .map(|(_, p)| p.clone())
            .collect();
        if found.is_empty() {
            return;
        }
        let released = Arc::make_mut(&mut self.released);
        for path in found {
            released.remove(&(local.0, path));
        }
    }

    /// Whether `local`'s `path`, or a place holding it, is released.
    fn is_released(&self, local: LocalId, path: &[u32]) -> bool {
        (0..=path.len()).any(|n| self.released.contains(&(local.0, path[..n].to_vec())))
    }
}

/// What may have moved after either of two paths, where `None` is a path that leaves.
fn join(a: Option<State>, b: Option<State>) -> Option<State> {
    match (a, b) {
        (Some(mut a), Some(b)) => {
            if a.holds(&b) {
                return Some(a);
            }
            if b.holds(&a) {
                return Some(b);
            }
            if !a.covers(&b) {
                let moved = Arc::make_mut(&mut a.moved);
                for (key, desc) in b.moved.iter() {
                    moved.entry(key.clone()).or_insert_with(|| desc.clone());
                }
            }
            // Released on both paths, so it is released after either.
            if !a.released_in(&b) {
                a.released = if b.released_in(&a) {
                    b.released
                } else {
                    Arc::new(a.released.intersection(&b.released).cloned().collect())
                };
            }
            Some(a)
        }
        (a, None) => a,
        (None, b) => b,
    }
}

fn is_prefix(short: &[u32], long: &[u32]) -> bool {
    short.len() <= long.len() && long[..short.len()] == *short
}

/// A step of an access path: a field, or an element by its index.
#[derive(Clone, Copy, PartialEq)]
enum Step {
    Field(u32),
    Element(Index),
}

/// An element's index, as far as two can be told apart without facts.
#[derive(Clone, Copy, PartialEq)]
enum Index {
    Literal(u128),
    Local(LocalId),
    Other,
}

/// Whether two access paths of one local reach the same memory.
#[derive(PartialEq)]
enum Overlap {
    No,
    Yes,
    /// Only a fact about two indices, such as `i != j`, can tell (§5.3).
    Unknown,
}

/// Whether two access paths of one local reach the same memory: one is a prefix of the
/// other. Two elements are the same when their indices are the same literal or variable,
/// and differ when they are different literals.
fn overlap(a: &[Step], b: &[Step]) -> Overlap {
    let mut unknown = false;
    for pair in a.iter().zip(b) {
        match pair {
            (Step::Element(Index::Literal(x)), Step::Element(Index::Literal(y))) if x != y => return Overlap::No,
            (Step::Element(Index::Literal(_)), Step::Element(Index::Literal(_))) => {}
            (Step::Element(Index::Local(x)), Step::Element(Index::Local(y))) if x == y => {}
            (Step::Element(_), Step::Element(_)) => unknown = true,
            (x, y) if x != y => return Overlap::No,
            _ => {}
        }
    }
    if unknown { Overlap::Unknown } else { Overlap::Yes }
}

/// How an argument or receiver of a call reaches a place for the length of the call.
#[derive(Clone, Copy, PartialEq)]
enum Access {
    /// `&x`, or an `inout self` receiver.
    Inout,
    /// A borrowed argument or receiver of a unique type, which nothing in the call's later
    /// arguments may move, at any depth.
    Lent,
}

#[derive(Clone)]
struct CallAccess {
    access: Access,
    local: LocalId,
    steps: Vec<Step>,
    expr: ExprId,
    /// What the place is lent to.
    by: Lender,
}

/// What a lent place is lent to, for as long as it runs.
#[derive(Clone, Copy, PartialEq)]
enum Lender {
    /// A call, while its later arguments are evaluated.
    Call,
    /// A `match` arm's guard.
    Guard,
    /// Its own index, as the base of an indexing expression.
    Index,
}

/// What a loop reached when it was last walked: what may have moved at its head and where it
/// ends, and the locals it touched.
struct LoopWalk {
    head: State,
    exit: Option<State>,
    touched: HashSet<LocalId>,
}

struct LoopFrame {
    expr: ExprId,
    breaks: Option<State>,
    continues: Option<State>,
    /// How many scopes and held values were open when the loop began, which a jump out of
    /// its turn leaves.
    scopes: usize,
    pending: usize,
}

/// A resource a call, a literal or a consuming loop holds while the rest of it runs, which a
/// jump out of it would drop, with the consuming loop that holds it, if one does.
struct Held {
    by_loop: Option<ExprId>,
}

struct Walk<'a> {
    m: &'a Module,
    p: &'a Program,
    locals: &'a [Local],
    bounds: &'a [Vec<IfaceId>],
    consumed: &'a HashSet<ExprId>,
    /// The expressions the checker rejected, which move nothing and lend nothing, so that
    /// nothing is reported that depends on them (REFERENCE §15.1).
    rejected: &'a HashSet<ExprId>,
    /// See [`Found::errors`].
    checked: &'a [Span],
    /// What may have moved here, or `None` where the code is unreachable.
    state: Option<State>,
    loops: Vec<LoopFrame>,
    /// A loop's body is walked more than once, so each mistake is reported once.
    reported: HashSet<(&'static str, Span)>,
    errors: Vec<(Code, Span, String)>,
    /// Accesses whose disjointness needs the verifier.
    later: Vec<Span>,
    /// What the calls whose arguments are being walked lend, innermost call last.
    lent: Vec<CallAccess>,
    /// What may have moved where a call that never returns fails to the `else` form or
    /// `attempt` that handles it, by that handler.
    handled: HashMap<ExprId, Option<State>>,
    /// What [`Walk::moves`] found for each argument list, by its address.
    memo: RefCell<HashMap<usize, bool>>,
    /// What each loop reached when it was last walked.
    loop_cache: HashMap<ExprId, LoopWalk>,
    /// The locals each loop being walked has touched, innermost last.
    touched: Vec<HashSet<LocalId>>,
    /// The outermost loop frame a jump has targeted, or a failure handler has been handed
    /// a state, since the innermost loop being walked began. `0` stands for the handler.
    reach: usize,
    moves_out: HashSet<ExprId>,
    arms_out: HashSet<PatId>,
    /// The locals an arm's pattern binds, while its guard is walked.
    guarded: Vec<LocalId>,
    /// The owned resources of each scope, innermost last, with the span and name of each
    /// one's binding, which every normal exit must have released (§10 rule 2).
    scopes: Vec<Vec<(LocalId, Span, String)>>,
    /// The resources held while the rest of their call, literal or loop runs.
    pending: Vec<Held>,
    /// See [`FnBody::consumes_self`]; `self` is local 0.
    consumes_self: bool,
    /// The locals the body uses.
    used: HashSet<LocalId>,
    /// See [`Program::held`].
    held: HashSet<ExprId>,
    /// See [`Program::owned_binds`].
    owned_binds: HashSet<PatId>,
    /// See [`Program::parts_out`].
    parts_out: HashMap<PatId, Vec<Vec<FieldIdx>>>,
    /// Constructs that are not yet scheduled, with how to name them.
    unscheduled: Vec<(Span, String)>,
    /// The values reported for moving out of a lent place, which hand nothing on, so what
    /// binds them owns nothing (REFERENCE §15.1).
    refused: HashSet<ExprId>,
    /// The locals a rejected move would have consumed, which aren't reported as left over.
    excused: HashSet<LocalId>,
}

impl Walk<'_> {
    fn report(&mut self, code: Code, span: Span, message: String) {
        if self.reported.insert((code.id, span)) {
            self.errors.push((code, span, message));
        }
    }

    /// Notes that the loops being walked touch `local`.
    fn touch(&mut self, local: LocalId) {
        self.used.insert(local);
        if let Some(top) = self.touched.last_mut() {
            top.insert(local);
        }
    }

    fn span(&self, e: ExprId) -> Span {
        self.m.exprs[e].span
    }

    /// Whether the checker rejected `e` or reported an error inside it, so that what it holds
    /// or gives is unknown (REFERENCE §15.1).
    fn tainted(&self, e: ExprId) -> bool {
        let span = self.span(e);
        self.rejected.contains(&e) || self.checked.iter().any(|at| span.lo <= at.lo && at.hi <= span.hi)
    }

    fn moves(&self, ty: &Ty) -> bool {
        self.p.decls.moves_memo(ty, self.bounds, &mut self.memo.borrow_mut())
    }

    fn is_resource(&self, ty: &Ty) -> bool {
        self.p.decls.is_resource(ty)
    }

    /// The type of `local`'s part at `path`, a field of a field and so on.
    fn ty_at(&self, local: LocalId, path: &[u32]) -> Ty {
        let mut ty = self.locals[local.index()].ty.clone();
        for &i in path {
            let Ty::Adt(id, args) = &ty else { return Ty::Error };
            let Some(field) = self.p.decls.adt(*id).variants.first().and_then(|v| v.fields.get(i as usize)) else {
                return Ty::Error;
            };
            ty = field.ty.subst(args);
        }
        ty
    }

    /// Whether `e` makes a new value, rather than naming a place or a part of one.
    fn is_temp(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) | ExprKind::It => !matches!(self.p.res(e), Some(Res::Local(_))),
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => {
                matches!(self.p.res(e), Some(Res::Ctor(..))) || self.is_temp(base)
            }
            _ => true,
        }
    }

    /// Whether the value of `e` may hold a resource: its type is a resource, unless it is a
    /// construction none of whose arguments is one, such as `None` or `Slot.Empty`.
    fn holds_resource(&self, e: ExprId) -> bool {
        if !self.is_resource(self.p.ty(e)) {
            return false;
        }
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (ExprKind::Name(_) | ExprKind::Field { .. }, Some(Res::Ctor(..))) => false,
            (ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. }, Some(Res::Ctor(..))) => {
                args.iter().any(|arg| self.holds_resource(arg.value))
            }
            _ => true,
        }
    }

    /// Whether `local`'s `path`, of type `ty`, holds no resource on every path here: it is
    /// released, or it is a record or tuple whose parts all are. A base resource holds itself,
    /// apart from the `self` of its own `take self` method (OPEN_QUESTIONS Q35).
    fn released_fully(&self, local: LocalId, path: &mut Path, ty: &Ty) -> bool {
        self.released_within(local, path, ty, &mut Vec::new())
    }

    /// [`Walk::released_fully`] inside the records in `within`. A record that holds itself
    /// has no values, so it holds no resource.
    fn released_within(&self, local: LocalId, path: &mut Path, ty: &Ty, within: &mut Vec<AdtId>) -> bool {
        let Some(state) = &self.state else { return true };
        if state.is_released(local, path) || !self.is_resource(ty) {
            return true;
        }
        let Ty::Adt(id, args) = ty else { return false };
        let def = self.p.decls.adt(*id);
        let own_self = self.consumes_self && local == LocalId(0) && path.is_empty();
        if def.is_enum() || def.is_native() || (def.resource_base && !own_self) {
            return false;
        }
        if within.contains(id) {
            return true;
        }
        within.push(*id);
        let released = def.field_types(VariantIdx::RECORD, args).iter().enumerate().all(|(i, field)| {
            path.push(i as u32);
            let released = self.released_within(local, path, field, within);
            path.pop();
            released
        });
        within.pop();
        released
    }

    // ---- resources ----

    /// Reports each owned resource in `self.scopes[from..]` that some path reaches `exit`
    /// without releasing (§10 rule 2).
    fn unreleased(&mut self, from: usize, exit: &str) {
        if self.state.is_none() {
            return;
        }
        let owned: Vec<(LocalId, Span, String)> = self.scopes[from..].iter().flatten().cloned().collect();
        for (local, span, name) in owned {
            if self.excused.contains(&local) {
                continue;
            }
            let ty = self.locals[local.index()].ty.clone();
            if !self.released_fully(local, &mut Vec::new(), &ty) {
                let message = format!(
                    "`{name}` is a resource that may still be owned at {exit}; consume it, as a `take self` method does, or transfer it, as to a `take` parameter, first (§10)"
                );
                self.report(codes::RESOURCE_NOT_CONSUMED, span, message);
            }
        }
    }

    fn open_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Ends the innermost scope, whose resources must be released here.
    fn close_scope(&mut self, exit: &str) {
        let from = self.scopes.len() - 1;
        self.unreleased(from, exit);
        self.scopes.pop();
    }

    /// Reports the resources held by the calls, literals and loops being walked from
    /// `self.pending[from..]`, which a jump to `exit` would drop. `except` is the consuming loop
    /// a `continue` goes on with.
    fn drops_held(&mut self, from: usize, exit: &str, span: Span, except: Option<ExprId>) {
        if self.state.is_none() {
            return;
        }
        if let Some(held) = self.pending[from..].iter().find(|h| h.by_loop.is_none() || h.by_loop != except) {
            let what = if held.by_loop.is_some() {
                "the elements a consuming loop hasn't reached yet"
            } else {
                "a resource that a call or literal around it already holds"
            };
            let message = format!("{exit} would drop {what}, which can't be discarded (§10)");
            self.report(codes::RESOURCE_DISCARDED, span, message);
        }
    }

    /// Reports a resource that `e` makes and nothing consumes (§10 rule 5).
    fn discarded(&mut self, e: ExprId, how: &str) {
        if self.is_temp(e) && self.holds_resource(e) && !self.tainted(e) && *self.p.ty(e) != Ty::Never {
            let message = format!(
                "this makes a resource, `{}`, that {how}, so it would be lost; consume it or transfer it (§10)",
                self.p.decls.display(self.p.ty(e))
            );
            self.report(codes::RESOURCE_DISCARDED, self.span(e), message);
        }
    }

    /// A resource `e` makes that its context only borrows, which drops it afterwards.
    fn borrowed_temp(&mut self, e: ExprId) {
        if !self.consumed.contains(&e) {
            self.discarded(e, "is only borrowed here");
        }
    }

    /// Notes that the call, literal or loop being walked holds what `e` gives it while the
    /// rest of it runs.
    fn hold(&mut self, e: ExprId) {
        if self.is_resource(self.p.ty(e)) && !self.rejected.contains(&e) {
            self.held.insert(e);
            self.pending.push(Held { by_loop: None });
        }
    }

    /// Notes the owned resources `pat` binds in the innermost scope.
    fn own(&mut self, pat: PatId) {
        let m = self.m;
        match &m.pats[pat].kind {
            PatKind::Bind(name) => {
                if let Some(&local) = self.p.pat_local.get(pat)
                    && !self.locals[local.index()].borrowed
                    && self.is_resource(&self.locals[local.index()].ty)
                {
                    self.owned_binds.insert(pat);
                    let entry = (local, m.pats[pat].span, m.text(name.sym).to_string());
                    if let Some(top) = self.scopes.last_mut()
                        && !top.iter().any(|(l, ..)| *l == local)
                    {
                        top.push(entry);
                    }
                }
            }
            PatKind::Tuple(parts) => {
                for &part in parts {
                    self.own(part);
                }
            }
            PatKind::Ctor { fields: Some(fields), .. } => {
                for field in fields {
                    self.own(field.pat);
                }
            }
            _ => {}
        }
    }

    /// The type arguments of `ty`, and its record or enum.
    fn adt_of<'t>(&self, ty: &'t Ty) -> Option<(AdtId, &'t [Ty])> {
        match ty {
            Ty::Adt(id, args) => Some((*id, args)),
            _ => None,
        }
    }

    /// Whether variant `v` of `ty`'s enum holds a resource.
    fn variant_holds(&self, ty: &Ty, v: usize) -> bool {
        let Some((id, args)) = self.adt_of(ty) else { return false };
        self.p.decls.adt(id).field_types(VariantIdx::new(v), args).iter().any(|f| self.is_resource(f))
    }

    /// Whether `pat` matches every value of its type.
    fn irrefutable(&self, pat: PatId) -> bool {
        match &self.m.pats[pat].kind {
            PatKind::Wild | PatKind::Bind(_) => true,
            PatKind::Lit(_) | PatKind::Range { .. } => false,
            PatKind::Tuple(parts) => parts.iter().all(|&part| self.irrefutable(part)),
            PatKind::Ctor { fields, .. } => {
                let Some(ctor) = self.p.pat_ctor.get(pat) else { return true };
                let def = self.p.decls.adt(ctor.adt);
                (!def.is_enum() || def.variants.len() == 1)
                    && fields.iter().flatten().all(|field| self.irrefutable(field.pat))
            }
        }
    }

    /// Whether a value of type `ty` that `pat` matches may hold a resource.
    fn may_hold(&self, pat: PatId, ty: &Ty) -> bool {
        match &self.m.pats[pat].kind {
            PatKind::Wild | PatKind::Bind(_) => self.is_resource(ty),
            PatKind::Lit(_) | PatKind::Range { .. } => false,
            PatKind::Tuple(parts) => {
                let Some((_, args)) = self.adt_of(ty) else { return false };
                parts.iter().zip(args).any(|(&part, arg)| self.may_hold(part, arg))
            }
            PatKind::Ctor { fields, .. } => {
                let (Some(ctor), Some((_, args))) = (self.p.pat_ctor.get(pat), self.adt_of(ty)) else {
                    return self.is_resource(ty);
                };
                // A base resource holds itself, whatever its fields are.
                if self.p.decls.adt(ctor.adt).resource_base {
                    return true;
                }
                let types = self.p.decls.adt(ctor.adt).field_types(ctor.variant, args);
                let written = fields.iter().flatten().zip(ctor.fields.iter());
                let left_out = (0..types.len())
                    .filter(|i| !ctor.fields.iter().any(|f| f.index() == *i))
                    .any(|i| self.is_resource(&types[i]));
                left_out || written.into_iter().any(|(field, idx)| self.may_hold(field.pat, &types[idx.index()]))
            }
        }
    }

    /// Whether `pat` matches every value of the variant it names, or of its type.
    fn irrefutable_in_variant(&self, pat: PatId) -> bool {
        match &self.m.pats[pat].kind {
            PatKind::Ctor { fields, .. } => fields.iter().flatten().all(|field| self.irrefutable(field.pat)),
            _ => self.irrefutable(pat),
        }
    }

    /// An `is` test of `value` against `pat`, which moves what it binds whether or not it
    /// matches (OPEN_QUESTIONS P5), so a failed test loses a resource the value may hold.
    fn tested(&mut self, value: ExprId, pat: PatId) {
        let ty = self.p.ty(value).clone();
        if !self.is_resource(&ty) || self.tainted(value) {
            return;
        }
        let temp = self.is_temp(value);
        let mut moved = Vec::new();
        self.bound_paths(pat, &mut Vec::new(), &mut moved);
        let lost_when_matched = self.lost(pat, &ty, temp);
        // The value is gone after a failed test when the test moves it or it is a temporary.
        let lost_when_failed = (temp || !moved.is_empty()) && {
            let variants = match self.adt_of(&ty) {
                Some((id, _)) if self.p.decls.adt(id).is_enum() => self.p.decls.adt(id).variants.len(),
                _ => 0,
            };
            match self.pattern_variant(pat) {
                _ if self.irrefutable(pat) => false,
                Some(v) if self.irrefutable_in_variant(pat) => {
                    (0..variants).any(|other| other != v && self.variant_holds(&ty, other))
                }
                _ => true,
            }
        };
        if lost_when_matched || lost_when_failed {
            let message = if lost_when_matched {
                "this pattern leaves out a resource of the value it moves, which would drop it (§10)"
            } else {
                "this test moves the value whether or not it matches, so a value it doesn't match, which may hold a resource, would be lost; use `match` (§10)"
            };
            self.report(codes::RESOURCE_DISCARDED, self.m.pats[pat].span, message.to_string());
        }
    }

    /// The variant of an enum that `pat` names, or `None` when it names none.
    fn pattern_variant(&self, pat: PatId) -> Option<usize> {
        match &self.m.pats[pat].kind {
            PatKind::Ctor { .. } => {
                let ctor = self.p.pat_ctor.get(pat)?;
                self.p.decls.adt(ctor.adt).is_enum().then_some(ctor.variant.index())
            }
            _ => None,
        }
    }

    /// Whether matching `pat` against a value of type `ty` drops a resource part of it: one
    /// the pattern leaves out of a value that doesn't stay in its place (`gone`), or a base
    /// resource it takes apart there. A binding
    /// inside an enum's variant moves the whole value, so what the rest leaves out goes
    /// with it (OPEN_QUESTIONS P5).
    fn lost(&self, pat: PatId, ty: &Ty, gone: bool) -> bool {
        match &self.m.pats[pat].kind {
            PatKind::Wild => gone && self.is_resource(ty),
            PatKind::Bind(_) | PatKind::Lit(_) | PatKind::Range { .. } => false,
            PatKind::Tuple(parts) => {
                let Some((_, args)) = self.adt_of(ty) else { return false };
                parts.iter().zip(args).any(|(&part, arg)| self.lost(part, arg, gone))
            }
            PatKind::Ctor { fields, .. } => {
                let (Some(ctor), Some((_, args))) = (self.p.pat_ctor.get(pat), self.adt_of(ty)) else { return false };
                let def = self.p.decls.adt(ctor.adt);
                let gone = gone || {
                    let mut moved = Vec::new();
                    def.is_enum() && {
                        self.bound_paths(pat, &mut Vec::new(), &mut moved);
                        !moved.is_empty()
                    }
                };
                let types = def.field_types(ctor.variant, args);
                let written = fields.iter().flatten().zip(ctor.fields.iter());
                let mut lost = false;
                for (field, idx) in written {
                    lost |= self.lost(field.pat, &types[idx.index()], gone);
                }
                let left_out = (0..types.len())
                    .filter(|i| !ctor.fields.iter().any(|f| f.index() == *i))
                    .any(|i| self.is_resource(&types[i]));
                // A pattern can't take a base resource apart, so one that goes is dropped.
                lost || (gone && (left_out || def.resource_base))
            }
        }
    }

    /// The local and fields that `e` names, when it is a place a move can leave.
    fn place(&self, e: ExprId) -> Option<(LocalId, Path)> {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) | ExprKind::It => match self.p.res(e) {
                Some(Res::Local(id)) => Some((id, Vec::new())),
                _ => None,
            },
            ExprKind::Field { base, .. } => match self.p.res(e) {
                Some(Res::Field(i)) => {
                    let (id, mut path) = self.place(base)?;
                    path.push(i.0);
                    Some((id, path))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The local and steps that `e` reaches, when it is a variable or a field or element of
    /// one.
    fn access_path(&self, e: ExprId) -> Option<(LocalId, Vec<Step>)> {
        match self.m.exprs[e].kind {
            ExprKind::Name(_) => match self.p.res(e) {
                Some(Res::Local(id)) => Some((id, Vec::new())),
                _ => None,
            },
            ExprKind::Field { base, .. } => match self.p.res(e) {
                Some(Res::Field(i)) => {
                    let (id, mut steps) = self.access_path(base)?;
                    steps.push(Step::Field(i.0));
                    Some((id, steps))
                }
                _ => None,
            },
            ExprKind::Index { base, index } => {
                let (id, mut steps) = self.access_path(base)?;
                let index = match self.m.exprs[index].kind {
                    ExprKind::Int(value) => Index::Literal(value),
                    ExprKind::Name(_) => match self.p.res(index) {
                        Some(Res::Local(id)) => Index::Local(id),
                        _ => Index::Other,
                    },
                    _ => Index::Other,
                };
                steps.push(Step::Element(index));
                Some((id, steps))
            }
            _ => None,
        }
    }

    /// How diagnostics write the place `e` names.
    fn describe(&self, e: ExprId) -> String {
        match &self.m.exprs[e].kind {
            ExprKind::Name(name) => self.m.text(name.sym).to_string(),
            ExprKind::Field { base, name } => format!("{}.{}", self.describe(*base), self.m.text(name.sym)),
            ExprKind::Index { base, .. } => format!("{}[…]", self.describe(*base)),
            ExprKind::It => "it".to_string(),
            _ => "this value".to_string(),
        }
    }

    /// How diagnostics write the part at `path` of a value of type `ty` written `desc`.
    fn describe_path(&self, desc: &str, ty: &Ty, path: &[u32]) -> String {
        let mut desc = desc.to_string();
        let mut ty = ty.clone();
        for &i in path {
            let Ty::Adt(id, args) = &ty else { break };
            let def = self.p.decls.adt(*id);
            let Some(field) = def.variants.first().and_then(|v| v.fields.get(i as usize)) else { break };
            desc = format!("{desc}.{}", field.name);
            ty = field.ty.subst(args);
        }
        desc
    }

    /// Whether no record that holds `local`'s `path` has a predicate. A predicate reads the
    /// whole record when another of its fields is assigned (REFERENCE §9), so a field that
    /// moves out of one is copied instead of taken out.
    fn unrefined(&self, local: LocalId, path: &[u32]) -> bool {
        let mut ty = self.locals[local.index()].ty.clone();
        for &i in path {
            let Ty::Adt(id, args) = &ty else { return false };
            let Some(variant) = self.p.decls.adt(*id).variants.first() else { return false };
            let Some(field) = variant.fields.get(i as usize) else { return false };
            if !variant.preds.is_empty() {
                return false;
            }
            ty = field.ty.subst(args);
        }
        true
    }

    // ---- places ----

    /// Reports a use of `local`'s `path` that may have moved, or a part of which may have.
    fn use_place(&mut self, e: ExprId, local: LocalId, path: &[u32]) {
        self.touch(local);
        let Some(state) = &self.state else { return };
        let Some((moved, desc)) = state.of(local).find(|(m, _)| is_prefix(m, path) || is_prefix(path, m)) else {
            return;
        };
        let here = self.describe(e);
        let message = if moved.len() > path.len() {
            format!("`{desc}` may have moved already, so `{here}` can't be used whole here (§5.1)")
        } else if moved.len() < path.len() {
            format!("`{desc}` may have moved already, so `{here}` can't be used here (§5.1)")
        } else {
            format!("`{here}` may have moved already, so it can't be used here; assign it a new value first (§5.1)")
        };
        self.report(codes::USE_AFTER_MOVE, self.span(e), message);
    }

    /// Moves `local`'s `path`, which `e` writes as `desc`.
    fn move_place(&mut self, e: ExprId, local: LocalId, path: Path, desc: String) {
        self.use_place(e, local, &path);
        self.leave(e, local, path, desc);
    }

    /// Moves `local`'s `path` once its use is checked.
    fn leave(&mut self, e: ExprId, local: LocalId, path: Path, desc: String) {
        let resource = self.is_resource(&self.ty_at(local, &path));
        // A lent resource can't be consumed (§10 rule 6).
        let lent = if resource { codes::LENT_RESOURCE_CONSUMED } else { codes::LENT_VALUE_MOVED };
        if self.locals[local.index()].borrowed {
            let message = if resource {
                format!(
                    "`{desc}` is a resource lent here, not owned, so it can't be consumed; only its owner can consume it, such as through a `take` parameter (§10)"
                )
            } else {
                format!(
                    "`{desc}` is lent here, not owned, so it can't move; only an owned value, such as a `take` parameter, can (§5.2)"
                )
            };
            self.report(lent, self.span(e), message);
            self.refused.insert(e);
            return;
        }
        if self.guarded.contains(&local) {
            let message = format!(
                "`{desc}` is bound by this arm's pattern and lent to its guard, which can only look at it, since the arm may still not be chosen; move it in the arm's body (OPEN_QUESTIONS P5)"
            );
            self.report(lent, self.span(e), message);
            self.refused.insert(e);
            // It was meant to move, so it isn't reported as left over (REFERENCE §15.1).
            self.excused.insert(local);
            return;
        }
        let steps: Vec<Step> = path.iter().map(|&i| Step::Field(i)).collect();
        if let Some(lender) = self.lent.iter().find(|l| l.local == local && overlap(&l.steps, &steps) != Overlap::No) {
            match lender.by {
                Lender::Guard => {
                    let message = format!(
                        "`{desc}` is lent to this arm's guard, which can only look at it, since the arm may still not be chosen; move it in the arm's body (OPEN_QUESTIONS P5)"
                    );
                    self.report(codes::LENT_VALUE_MOVED, self.span(e), message);
                }
                Lender::Call => {
                    let message = format!(
                        "`{desc}` is lent to this call by an earlier argument, so it can't also move into it (§5.3)"
                    );
                    self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
                }
                Lender::Index => {
                    let message =
                        format!("`{desc}` is indexed here, so it can't move while its index is evaluated (§5.3)");
                    self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
                }
            }
            return;
        }
        if resource && !self.unrefined(local, &path) && self.read_by_refinement(local, &path) {
            let what = "moving a resource out of a field that its record's refinement reads, which may run again,";
            if self.reported.insert((codes::NOT_IMPLEMENTED.id, self.span(e))) {
                self.unscheduled.push((self.span(e), what.to_string()));
            }
        }
        let Some(state) = &mut self.state else { return };
        if resource {
            state.release(local, path.clone());
        }
        if state.of(local).any(|(m, _)| is_prefix(m, &path)) {
            return;
        }
        state.forget(local, |m| !is_prefix(&path, m));
        Arc::make_mut(&mut state.moved).insert((local.0, path.clone()), desc);
        // A resource always leaves its place, so the interpreter never abandons it twice.
        if self.place(e).is_some_and(|named| named == (local, path.clone()))
            && (resource || self.unrefined(local, &path))
        {
            self.moves_out.insert(e);
        }
    }

    /// Whether a refinement of a record that holds `local`'s `path` reads the field on the
    /// way to it.
    fn read_by_refinement(&self, local: LocalId, path: &[u32]) -> bool {
        let mut ty = self.locals[local.index()].ty.clone();
        for &i in path {
            let Ty::Adt(id, args) = &ty else { return false };
            let Some(variant) = self.p.decls.adt(*id).variants.first() else { return false };
            let Some(field) = variant.fields.get(i as usize) else { return false };
            if variant.read_fields.get(i as usize).copied().unwrap_or(false) {
                return true;
            }
            ty = field.ty.subst(args);
        }
        false
    }

    /// Gives `local`'s `path` a new value, which makes it and its parts usable again. A part
    /// of a value that may have moved can't be assigned.
    fn assign_place(&mut self, e: ExprId, local: LocalId, path: &[u32]) {
        self.touch(local);
        let Some(state) = &self.state else { return };
        if state.of(local).any(|(m, _)| m.len() < path.len() && is_prefix(m, path)) {
            self.use_place(e, local, path);
            return;
        }
        if let Some(state) = &mut self.state {
            state.forget(local, |m| !is_prefix(path, m));
            state.unrelease(local, |m| is_prefix(path, m));
        }
    }

    /// A new value for `local`, as a pattern binds it on each turn of a loop.
    fn bind(&mut self, local: LocalId) {
        self.touch(local);
        if let Some(state) = &mut self.state {
            state.forget(local, |_| false);
            state.unrelease(local, |_| true);
        }
    }

    // ---- statements ----

    /// A block whose value, if any, is dropped.
    fn block(&mut self, block: &Block) {
        self.value_block(block, false);
    }

    /// A block whose final expression gives its value, which is `used` when the expression
    /// around the block takes it.
    fn value_block(&mut self, block: &Block, used: bool) {
        for (i, &s) in block.stmts.iter().enumerate() {
            match self.m.stmts[s].kind {
                StmtKind::Expr(e) if used && i + 1 == block.stmts.len() => self.expr(e),
                _ => self.stmt(s),
            }
        }
    }

    /// A block with a scope of its own, whose owned resources its end releases.
    fn scoped_block(&mut self, block: &Block, used: bool) {
        self.open_scope();
        self.value_block(block, used);
        self.close_scope("the end of its block");
    }

    fn stmt(&mut self, s: StmtId) {
        let m = self.m;
        match &m.stmts[s].kind {
            StmtKind::Let { pat, init, .. } => {
                self.expr(*init);
                let ty = self.p.ty(*init).clone();
                let gone = self.is_temp(*init) || self.consumed.contains(init);
                if self.is_resource(&ty) && !self.tainted(*init) && self.lost(*pat, &ty, gone) {
                    let message = "this pattern leaves out a resource of the value it takes, which would drop it (§10)";
                    self.report(codes::RESOURCE_DISCARDED, m.pats[*pat].span, message.to_string());
                }
                self.matched(*init, *pat);
                // A value that holds no resource, such as `None`, has nothing to consume.
                if !self.holds_resource(*init) || self.refused.contains(init) || self.tainted(*init) {
                    let mut locals = Vec::new();
                    self.pattern_locals(*pat, &mut locals);
                    if let Some(state) = &mut self.state {
                        for local in locals {
                            state.release(local, Vec::new());
                        }
                    }
                }
            }
            StmtKind::Assign { target, op, value } => {
                self.expr(*value);
                if self.place(*target).is_some() {
                    self.change_lent(*target, self.lent.len());
                }
                // A place that may still hold a resource can't be assigned over (§10 rule 5).
                if self.is_resource(self.p.ty(*target)) && !self.tainted(*target) && !self.tainted(*value) {
                    let released = match self.place(*target) {
                        Some((local, _)) if self.excused.contains(&local) => true,
                        Some((local, mut path)) => {
                            let ty = self.ty_at(local, &path);
                            self.released_fully(local, &mut path, &ty)
                        }
                        None => false,
                    };
                    if !released {
                        let message = "this place may still hold a resource, which assigning would discard; consume or transfer it first (§10)";
                        self.report(codes::RESOURCE_DISCARDED, self.span(*target), message.to_string());
                    }
                }
                match self.place(*target) {
                    Some((local, path)) if *op == AssignOp::Set => {
                        self.assign_place(*target, local, &path);
                        if !self.holds_resource(*value)
                            && let Some(state) = &mut self.state
                        {
                            state.release(local, path);
                        }
                    }
                    Some((local, path)) => self.use_place(*target, local, &path),
                    None => self.target(*target),
                }
            }
            StmtKind::Expr(e) => {
                self.expr(*e);
                self.discarded(*e, "this statement drops");
            }
            StmtKind::Assert(e) => self.expr(*e),
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(*value);
                }
                self.drops_held(0, "this `return`", m.stmts[s].span, None);
                self.unreleased(0, "this `return`");
                self.state = None;
            }
            StmtKind::Break(_) | StmtKind::Continue(_) => {
                let is_break = matches!(m.stmts[s].kind, StmtKind::Break(_));
                let target = self.p.jump_target.get(s).copied();
                if let Some(i) = self.loops.iter().rposition(|f| Some(f.expr) == target) {
                    let (scopes, pending, expr) = (self.loops[i].scopes, self.loops[i].pending, self.loops[i].expr);
                    let exit = if is_break { "this `break`" } else { "this `continue`" };
                    let except = (!is_break).then_some(expr);
                    self.drops_held(pending, exit, m.stmts[s].span, except);
                    self.unreleased(scopes, exit);
                }
                let state = self.state.take();
                if let Some(i) = self.loops.iter().rposition(|f| Some(f.expr) == target) {
                    let frame = &mut self.loops[i];
                    let slot = if is_break { &mut frame.breaks } else { &mut frame.continues };
                    *slot = join(slot.take(), state);
                    self.reach = self.reach.min(i + 1);
                }
            }
            StmtKind::Check { cond, fallback } => {
                // What the condition binds is in scope after the `check`, where the fallback,
                // which leaves, doesn't reach (OPEN_QUESTIONS P5).
                self.open_scope();
                self.condition(*cond);
                let bound = self.scopes.pop().expect("the condition's scope was opened");
                // The fallback leaves, so only the code after it runs on.
                let after = self.state.clone();
                self.fallback(fallback, false);
                self.state = after;
                if let Some(top) = self.scopes.last_mut() {
                    top.extend(bound);
                }
            }
        }
    }

    /// Reports a change to the place `e`, by assignment or an `&` access, while a call, an
    /// index or a guard that `self.lent[..upto]` lists still has it lent (§5.3).
    fn change_lent(&mut self, e: ExprId, upto: usize) {
        let Some((local, steps)) = self.access_path(e) else { return };
        let found = self.lent[..upto].iter().rev().find_map(|l| {
            let overlap = if l.local == local { overlap(&l.steps, &steps) } else { Overlap::No };
            (overlap != Overlap::No).then_some((l.by, l.expr, overlap))
        });
        let Some((by, there, overlap)) = found else { return };
        let span = self.span(e);
        if overlap == Overlap::Unknown {
            if self.reported.insert((codes::NOT_IMPLEMENTED.id, span)) {
                self.later.push(span);
            }
            return;
        }
        let (here, there) = (self.describe(e), self.describe(there));
        let lent = match by {
            Lender::Call => {
                format!("`{there}` is lent to a call by one of its earlier arguments until the call returns")
            }
            Lender::Guard => format!("`{there}` is lent to this arm's guard, which can only look at it"),
            Lender::Index => format!("`{there}` is indexed while its index is evaluated"),
        };
        let message = if here == there {
            format!("{lent}, so it can't change here (§5.3)")
        } else {
            format!("{lent}, so `{here}` can't change here (§5.3)")
        };
        self.report(codes::OVERLAPPING_ACCESS, span, message);
    }

    /// An assignment's target that isn't a place, such as `xs[i].n`, which uses the
    /// variable it changes once the target's indices are evaluated.
    fn target(&mut self, target: ExprId) {
        self.indices(target);
        self.change_lent(target, self.lent.len());
        self.root(target);
    }

    /// The indices of the place `e`, innermost first, which are evaluated before the place
    /// is reached (OPEN_QUESTIONS P5).
    fn indices(&mut self, e: ExprId) {
        match self.m.exprs[e].kind {
            ExprKind::Field { base, .. } => self.indices(base),
            ExprKind::Index { base, index } => {
                self.indices(base);
                self.expr(index);
            }
            _ => {}
        }
    }

    /// Reaching the place `e`, whose indices [`Walk::indices`] walked, uses its variable.
    fn root(&mut self, e: ExprId) {
        if self.place(e).is_some() {
            return self.expr(e);
        }
        match self.m.exprs[e].kind {
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => self.root(base),
            _ => self.expr(e),
        }
    }

    /// The fallback of an `else` form, whose value is `used` when it is a resource, or of a
    /// `check`.
    fn fallback(&mut self, fallback: &Fallback, used: bool) {
        match fallback {
            Fallback::Value(x) => self.expr(*x),
            Fallback::Block(block) => self.scoped_block(block, used),
        }
    }

    // ---- expressions ----

    fn expr(&mut self, e: ExprId) {
        self.expr_kind(e);
        if *self.p.ty(e) == Ty::Never {
            // A call that never returns may still fail to the handler that goes on after it.
            if let Some(&handler) = self.p.handler_of.get(e) {
                let pending = self.handled.remove(&handler).flatten();
                let state = join(pending, self.state.take());
                self.handled.insert(handler, state);
                self.reach = 0;
            }
            self.state = None;
        }
    }

    fn expr_kind(&mut self, e: ExprId) {
        let m = self.m;
        if let Some((local, path)) = self.place(e) {
            if self.consumed.contains(&e) && !self.rejected.contains(&e) && self.moves(self.p.ty(e)) {
                let desc = self.describe(e);
                self.move_place(e, local, path, desc);
            } else {
                self.use_place(e, local, &path);
                // A rejected place moves nothing, but it was meant to, so what it names isn't
                // reported as left over (REFERENCE §15.1).
                if self.consumed.contains(&e)
                    && self.rejected.contains(&e)
                    && let Some(state) = &mut self.state
                {
                    state.release(local, path);
                }
            }
            return;
        }
        match &m.exprs[e].kind {
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Text(_)
            | ExprKind::Unit
            | ExprKind::Name(_)
            | ExprKind::It
            | ExprKind::Todo(_)
            | ExprKind::Unreachable => {}
            // Code that failed to parse may have consumed what the scopes own, so none of it
            // is reported as left over or assigned over (§15.1).
            ExprKind::Error => {
                let owned: Vec<LocalId> = self.scopes.iter().flatten().map(|(local, ..)| *local).collect();
                self.excused.extend(owned);
            }
            ExprKind::FText(parts) => {
                for part in parts {
                    if let FTextPart::Expr(x) = part {
                        self.expr(*x);
                        self.borrowed_temp(*x);
                    }
                }
            }
            ExprKind::Call { args, .. } => self.call(e, None, args),
            ExprKind::MethodCall { receiver, args, .. } => {
                let mode = match self.p.res(e) {
                    Some(Res::Fn(f)) if self.p.fns[f].receiver.is_some() => self.p.fns[f].self_mode,
                    Some(Res::Method(builtin)) if builtin.changes_receiver() => ParamMode::Inout,
                    Some(Res::Dispatch { iface, method, qualified: false }) => {
                        self.p.decls.iface(iface).methods[method].self_mode
                    }
                    _ => ParamMode::Borrow,
                };
                self.call(e, Some((*receiver, mode)), args);
            }
            ExprKind::Field { base, .. } => {
                self.expr(*base);
                if !matches!(self.p.res(e), Some(Res::Ctor(..))) {
                    self.borrowed_temp(*base);
                }
            }
            ExprKind::Index { base, index } => {
                self.expr(*base);
                self.borrowed_temp(*base);
                // The base is reached before its index, which may not move or change it.
                let outer = self.lent.len();
                if let Some((local, steps)) = self.access_path(*base)
                    && self.moves(self.p.ty(*base))
                    && !self.moved_here(*base)
                {
                    self.lent.push(CallAccess { access: Access::Lent, local, steps, expr: *base, by: Lender::Index });
                }
                self.expr(*index);
                self.lent.truncate(outer);
            }
            ExprKind::Unary { operand, .. } => self.expr(*operand),
            ExprKind::Binary { op: BinOp::And, .. } => self.condition(e),
            ExprKind::Binary { op: BinOp::Or, lhs, rhs } => {
                self.expr(*lhs);
                let before = self.state.clone();
                self.expr(*rhs);
                self.state = join(before, self.state.take());
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Range { lo: lhs, hi: rhs, .. } => {
                self.expr(*lhs);
                self.expr(*rhs);
                self.borrowed_temp(*lhs);
                self.borrowed_temp(*rhs);
            }
            ExprKind::Try(inner) | ExprKind::Fail(inner) => self.expr(*inner),
            ExprKind::Attempt(inner) => {
                self.expr(*inner);
                let failed = self.handled.remove(&e).flatten();
                self.state = join(self.state.take(), failed);
            }
            ExprKind::If { cond, then_block, else_branch } => {
                // What the condition binds is in scope in the then-block only.
                let used = self.is_resource(self.p.ty(e));
                self.open_scope();
                self.condition(*cond);
                let after = self.state.clone();
                self.value_block(then_block, used);
                self.close_scope("the end of its block");
                let then_state = std::mem::replace(&mut self.state, after);
                match else_branch {
                    Some(ElseBranch::Block(block)) => self.scoped_block(block, used),
                    Some(ElseBranch::If(nested)) => self.expr(*nested),
                    None => {}
                }
                self.state = join(then_state, self.state.take());
            }
            ExprKind::While { cond, body, .. } => {
                self.looped(e, |w| {
                    w.open_scope();
                    w.condition(*cond);
                    let exit = w.state.clone();
                    w.block(body);
                    w.close_scope("the end of the loop's body");
                    exit
                });
            }
            ExprKind::Loop { body, .. } => {
                self.looped(e, |w| {
                    w.scoped_block(body, false);
                    None
                });
            }
            ExprKind::For { pat, iter, body, consume, .. } => {
                self.expr(*iter);
                if !consume {
                    self.borrowed_temp(*iter);
                }
                // A consuming loop owns what is left of its collection until it ends (§6.5).
                let elements = match self.p.ty(*iter) {
                    Ty::Adt(AdtId::LIST, args) if *consume => args[0].clone(),
                    Ty::Adt(AdtId::MAP, args) if *consume => Ty::applied(AdtId::PAIR, args.to_vec()),
                    _ => Ty::Error,
                };
                let holds = self.is_resource(&elements);
                if holds && self.lost(*pat, &elements, true) {
                    let message = "this pattern leaves out a resource of each element, which the loop would drop (§10)";
                    self.report(codes::RESOURCE_DISCARDED, self.m.pats[*pat].span, message.to_string());
                }
                self.looped(e, |w| {
                    let exit = w.state.clone();
                    w.open_scope();
                    if holds {
                        w.pending.push(Held { by_loop: Some(e) });
                    }
                    w.bind_all(*pat);
                    w.block(body);
                    if holds {
                        w.pending.pop();
                    }
                    w.close_scope("the end of the loop's body");
                    exit
                });
            }
            ExprKind::Debug(values) => {
                for &value in values {
                    self.expr(value);
                    self.borrowed_temp(value);
                }
            }
            ExprKind::Tuple(values) | ExprKind::List(values) => {
                let outer = self.pending.len();
                for &value in values {
                    self.expr(value);
                    self.hold(value);
                }
                self.pending.truncate(outer);
            }
            ExprKind::Map(entries) => {
                let outer = self.pending.len();
                for &(k, v) in entries {
                    self.expr(k);
                    self.hold(k);
                    self.expr(v);
                    self.hold(v);
                }
                self.pending.truncate(outer);
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.expr(*scrutinee);
                let ty = self.p.ty(*scrutinee).clone();
                let resource = self.is_resource(&ty) && !self.tainted(*scrutinee);
                let temp = self.is_temp(*scrutinee);
                // A temporary that guards may still fail past is held until an arm takes it.
                if resource && temp {
                    self.held.insert(*scrutinee);
                }
                // The variants an arm may still meet: an earlier arm without a guard that
                // matches all of a variant takes it (OPEN_QUESTIONS P5).
                let variants = match self.adt_of(&ty) {
                    Some((id, _)) if self.p.decls.adt(id).is_enum() => self.p.decls.adt(id).variants.len(),
                    _ => 0,
                };
                let mut remaining = vec![true; variants];
                // What may have moved when an arm is tried: what moved before the `match`,
                // and what the guards of the arms before it moved.
                let mut tried = self.state.clone();
                let mut after = None;
                for arm in arms {
                    self.state = tried.clone();
                    self.open_scope();
                    let arm_variant = self.pattern_variant(arm.pat);
                    let meets: Vec<usize> =
                        (0..variants).filter(|&v| remaining[v] && arm_variant.is_none_or(|a| a == v)).collect();
                    // An arm whose values hold no resource leaves nothing to consume.
                    let empty = match &self.m.pats[arm.pat].kind {
                        PatKind::Wild | PatKind::Bind(_) => {
                            variants > 0 && meets.iter().all(|&v| !self.variant_holds(&ty, v))
                        }
                        _ => !self.may_hold(arm.pat, &ty),
                    };
                    if arm.guard.is_none() && self.irrefutable_in_variant(arm.pat) {
                        for &v in &meets {
                            remaining[v] = false;
                        }
                    }
                    if let Some(guard) = arm.guard {
                        // The guard runs before the pattern moves anything, with the
                        // scrutinee and what the pattern binds lent to it. A guard that fails
                        // hands the next arm what it moved.
                        self.bind_all(arm.pat);
                        let (outer, lent) = (self.guarded.len(), self.lent.len());
                        let mut locals = Vec::new();
                        self.pattern_locals(arm.pat, &mut locals);
                        self.guarded.extend(locals);
                        if let Some((local, steps)) = self.access_path(*scrutinee)
                            && self.moves(self.p.ty(*scrutinee))
                            && !self.moved_here(*scrutinee)
                        {
                            self.lent.push(CallAccess {
                                access: Access::Lent,
                                local,
                                steps,
                                expr: *scrutinee,
                                by: Lender::Guard,
                            });
                        }
                        self.condition(guard);
                        self.guarded.truncate(outer);
                        self.lent.truncate(lent);
                        tried = join(tried, self.state.clone());
                    }
                    if resource && !empty && self.lost(arm.pat, &ty, temp) {
                        let message =
                            "this pattern leaves out a resource of a value it moves, which would drop it (§10)";
                        self.report(codes::RESOURCE_DISCARDED, self.m.pats[arm.pat].span, message.to_string());
                    }
                    self.matched(*scrutinee, arm.pat);
                    if empty
                        && let Some((local, path)) = self.place(*scrutinee)
                        && let Some(state) = &mut self.state
                    {
                        state.release(local, path);
                    }
                    // The scrutinee leaves its local only once this arm is chosen.
                    if self.moves_out.remove(scrutinee) {
                        self.arms_out.insert(arm.pat);
                    }
                    self.value_block(&arm.body, self.is_resource(self.p.ty(e)));
                    self.close_scope("the end of its arm");
                    after = join(after, self.state.take());
                }
                self.state = after;
            }
            ExprKind::Is { value, pat } => {
                self.expr(*value);
                self.tested(*value, *pat);
                self.matched(*value, *pat);
            }
            ExprKind::Else { value, fallback } => {
                self.expr(*value);
                let after = self.state.clone();
                let failed = self.handled.remove(&e).flatten();
                self.state = join(self.state.take(), failed);
                self.fallback(fallback, self.is_resource(self.p.ty(e)));
                self.state = join(after, self.state.take());
            }
        }
    }

    /// A condition, whose `and` runs its right side only when its left is true.
    fn condition(&mut self, e: ExprId) {
        match self.m.exprs[e].kind {
            ExprKind::Binary { op: BinOp::And, lhs, rhs } => {
                self.condition(lhs);
                let before = self.state.clone();
                self.condition(rhs);
                self.state = join(before, self.state.take());
            }
            _ => self.expr(e),
        }
    }

    /// A loop whose turn `turn` walks, returning what may have moved where the loop ends
    /// without a `break`. The turn is walked until what may have moved at the loop's head
    /// stops growing.
    ///
    /// A loop inside another is walked on each of the outer loop's turns, with an entry that
    /// only grows. So it starts from the head it reached last time, and when the entry gained
    /// only places of locals the loop never touches, the walk would change nothing but carry
    /// them through, so it is skipped. That keeps nested loops from costing time exponential
    /// in their depth.
    fn looped(&mut self, e: ExprId, turn: impl Fn(&mut Self) -> Option<State>) {
        let entry = self.state.clone();
        // What is released at the head must be what it was too, which a program without
        // resources always has.
        if let (Some(entry), Some(last)) = (&entry, self.loop_cache.get(&e))
            && entry.released_in(&last.head)
            && last.head.released_in(entry)
        {
            let gained: Vec<_> = entry.moved.iter().filter(|(key, _)| !last.head.moved.contains_key(key)).collect();
            if gained.iter().all(|((local, _), _)| !last.touched.contains(&LocalId(*local))) {
                let mut exit = last.exit.clone();
                if let Some(exit) = &mut exit {
                    for (key, desc) in gained {
                        Arc::make_mut(&mut exit.moved).entry(key.clone()).or_insert_with(|| desc.clone());
                    }
                }
                let touched = last.touched.clone();
                if let Some(top) = self.touched.last_mut() {
                    top.extend(touched);
                }
                self.state = exit;
                return;
            }
        }
        let mut head = match (&entry, self.loop_cache.get(&e)) {
            (Some(_), Some(last)) => join(entry.clone(), Some(last.head.clone())),
            _ => entry.clone(),
        };
        let depth = self.loops.len();
        let outer_reach = std::mem::replace(&mut self.reach, usize::MAX);
        self.touched.push(HashSet::new());
        loop {
            self.state = head.clone();
            let (scopes, pending) = (self.scopes.len(), self.pending.len());
            self.loops.push(LoopFrame { expr: e, breaks: None, continues: None, scopes, pending });
            let exit = turn(self);
            let frame = self.loops.pop().expect("the loop's frame was pushed");
            let back = join(self.state.take(), frame.continues);
            let next = join(entry.clone(), back);
            let grew = match (&head, &next) {
                (Some(head), Some(next)) => !head.holds(next),
                (None, Some(_)) => true,
                (_, None) => false,
            };
            if !grew {
                let exit = join(exit, frame.breaks);
                let touched = self.touched.pop().expect("the loop's set was pushed");
                // A walk that handed a state to something outside the loop can't be skipped.
                if let Some(head) = head
                    && self.reach > depth
                {
                    self.loop_cache.insert(e, LoopWalk { head, exit: exit.clone(), touched: touched.clone() });
                } else {
                    self.loop_cache.remove(&e);
                }
                if let Some(top) = self.touched.last_mut() {
                    top.extend(touched);
                }
                self.reach = self.reach.min(outer_reach);
                self.state = exit;
                return;
            }
            head = next;
        }
    }

    /// The bindings of `pat`, matched against the value of `value`. A binding of a unique
    /// part moves that part out of an owned place: a field of a record or an element of a
    /// tuple, or the whole value for a binding inside an enum's variant (OPEN_QUESTIONS P5).
    fn matched(&mut self, value: ExprId, pat: PatId) {
        if let Some((local, base)) = self.place(value)
            && !self.locals[local.index()].borrowed
            && !self.consumed.contains(&value)
        {
            let mut paths = Vec::new();
            self.bound_paths(pat, &mut base.clone(), &mut paths);
            let desc = self.describe(value);
            let ty = self.p.ty(value).clone();
            for path in paths {
                let part = self.describe_path(&desc, &ty, &path[base.len()..]);
                // A resource part leaves the value it is in, so the interpreter doesn't abandon
                // it twice.
                if path.len() > base.len() && self.is_resource(&self.ty_at(local, &path)) {
                    let rel = path[base.len()..].iter().map(|&i| FieldIdx(i)).collect();
                    let parts = self.parts_out.entry(pat).or_default();
                    if !parts.contains(&rel) {
                        parts.push(rel);
                    }
                }
                self.move_place(value, local, path, part);
            }
        }
        self.bind_all(pat);
    }

    /// The paths of the parts of a value at `path` that `pat` binds and moves.
    fn bound_paths(&self, pat: PatId, path: &mut Path, out: &mut Vec<Path>) {
        let m = self.m;
        match &m.pats[pat].kind {
            PatKind::Wild | PatKind::Lit(_) | PatKind::Range { .. } => {}
            PatKind::Bind(_) => {
                if let Some(&local) = self.p.pat_local.get(pat)
                    && self.moves(&self.locals[local.index()].ty)
                {
                    out.push(path.clone());
                }
            }
            PatKind::Tuple(parts) => {
                for (i, &part) in parts.iter().enumerate() {
                    path.push(i as u32);
                    self.bound_paths(part, path, out);
                    path.pop();
                }
            }
            PatKind::Ctor { fields, .. } => {
                let (Some(ctor), Some(fields)) = (self.p.pat_ctor.get(pat), fields) else { return };
                let def = self.p.decls.adt(ctor.adt);
                if def.is_enum() || ctor.adt == AdtId::OPTION || ctor.adt == AdtId::RESULT {
                    let mut inner = Vec::new();
                    for field in fields.iter() {
                        self.bound_paths(field.pat, &mut Vec::new(), &mut inner);
                    }
                    if !inner.is_empty() {
                        out.push(path.clone());
                    }
                    return;
                }
                for (field, idx) in fields.iter().zip(ctor.fields.iter()) {
                    path.push(idx.0);
                    self.bound_paths(field.pat, path, out);
                    path.pop();
                }
            }
        }
    }

    /// Gives each local `pat` binds a new value, and the innermost scope owns the resources
    /// among them.
    fn bind_all(&mut self, pat: PatId) {
        let mut locals = Vec::new();
        self.pattern_locals(pat, &mut locals);
        for local in locals {
            self.bind(local);
        }
        self.own(pat);
    }

    /// The locals `pat` binds.
    fn pattern_locals(&self, pat: PatId, out: &mut Vec<LocalId>) {
        let m = self.m;
        match &m.pats[pat].kind {
            PatKind::Bind(_) => out.extend(self.p.pat_local.get(pat).copied()),
            PatKind::Tuple(parts) => {
                for &part in parts {
                    self.pattern_locals(part, out);
                }
            }
            PatKind::Ctor { fields: Some(fields), .. } => {
                for field in fields {
                    self.pattern_locals(field.pat, out);
                }
            }
            _ => {}
        }
    }

    // ---- calls ----

    /// The arguments of a call, and its receiver with the mode it takes `self` in. The
    /// indices of an `&` argument and an `inout self` receiver are evaluated in order with
    /// the other arguments, but the place is reached once they all are (§5.3), and no two
    /// accesses of the call may conflict.
    fn call(&mut self, e: ExprId, receiver: Option<(ExprId, ParamMode)>, args: &[Arg]) {
        if self.rejected.contains(&e) {
            // A rejected call only reads what it is given, and may have meant to consume it,
            // so no resource it reads is reported as left over (REFERENCE §15.1).
            for value in receiver.map(|(r, _)| r).into_iter().chain(args.iter().map(|arg| arg.value)) {
                self.read(value);
                if let Some((local, path)) = self.place(value)
                    && let Some(state) = &mut self.state
                {
                    state.release(local, path);
                }
            }
            return;
        }
        // `with` takes the fields it keeps from a receiver that moves once its arguments are
        // evaluated, so they may read the receiver and the fields it replaces may have moved
        // (OPEN_QUESTIONS P5).
        if let Some((receiver, _)) = receiver
            && self.p.res(e) == Some(Res::With)
            && self.consumed.contains(&receiver)
            && self.moves(self.p.ty(receiver))
            && let Some((local, path)) = self.place(receiver)
        {
            let outer = self.pending.len();
            for arg in args {
                self.expr(arg.value);
                self.hold(arg.value);
            }
            self.pending.truncate(outer);
            let replaced = self.p.with_fields.get(e).expect("`with` is resolved");
            self.replaced(receiver, Some((local, &path)), replaced);
            let kept = |m: &[u32]| m.len() <= path.len() || !replaced.iter().any(|i| i.0 == m[path.len()]);
            self.touch(local);
            let desc = self.describe(receiver);
            let moved = self.state.as_ref().and_then(|state| {
                state
                    .of(local)
                    .find(|(m, _)| (is_prefix(m, &path) || is_prefix(&path, m)) && kept(m))
                    .map(|(_, d)| d.clone())
            });
            if let Some(moved) = moved {
                let message = if moved == desc {
                    format!(
                        "`{desc}` may have moved already, so it can't be used here; assign it a new value first (§5.1)"
                    )
                } else {
                    format!(
                        "`{moved}` may have moved already, and `with` keeps it, so `{desc}` can't be used here (§5.1)"
                    )
                };
                self.report(codes::USE_AFTER_MOVE, self.span(receiver), message);
            }
            return self.leave(receiver, local, path, desc);
        }
        let mut accesses: Vec<CallAccess> = Vec::new();
        let outer = self.lent.len();
        let held = self.pending.len();
        let late = matches!(receiver, Some((_, ParamMode::Inout)));
        match receiver {
            Some((receiver, _)) if late => self.indices(receiver),
            Some((receiver, _)) => {
                self.expr(receiver);
                // A `take self` receiver, and that of `with` on a unique record, move.
                if !self.consumed.contains(&receiver) {
                    self.note(&mut accesses, outer, receiver, Access::Lent);
                    if self.is_value(receiver) {
                        self.borrowed_temp(receiver);
                    }
                } else {
                    self.hold(receiver);
                }
                if self.p.res(e) == Some(Res::With) {
                    let replaced = self.p.with_fields.get(e).expect("`with` is resolved");
                    self.replaced(receiver, None, replaced);
                }
            }
            None => {}
        }
        for arg in args {
            if arg.inout {
                self.indices(arg.value);
                continue;
            }
            self.expr(arg.value);
            // An argument that moves was checked against what the call lends as it moved.
            if !self.consumed.contains(&arg.value) && !self.rejected.contains(&arg.value) {
                self.note(&mut accesses, outer, arg.value, Access::Lent);
                self.borrowed_temp(arg.value);
            } else if self.consumed.contains(&arg.value) {
                self.hold(arg.value);
            }
        }
        self.pending.truncate(held);
        for arg in args.iter().filter(|arg| arg.inout) {
            self.root(arg.value);
            if !self.rejected.contains(&arg.value) {
                self.note(&mut accesses, outer, arg.value, Access::Inout);
            }
        }
        if let Some((receiver, _)) = receiver
            && late
        {
            self.root(receiver);
            self.note(&mut accesses, outer, receiver, Access::Inout);
        }
        self.lent.truncate(outer);
    }

    /// Reports a field that `with` replaces while it may still hold a resource, which the new
    /// record would discard (§10 rule 5). `place` is the receiver's place, when it is one.
    fn replaced(&mut self, receiver: ExprId, place: Option<(LocalId, &Path)>, replaced: &[FieldIdx]) {
        let Some((id, args)) = self.adt_of(self.p.ty(receiver)) else { return };
        let types = self.p.decls.adt(id).field_types(VariantIdx::RECORD, args);
        for field in replaced {
            let ty = &types[field.index()];
            if !self.is_resource(ty) {
                continue;
            }
            let released = match place {
                Some((local, path)) => {
                    let mut path = path.clone();
                    path.push(field.0);
                    self.released_fully(local, &mut path, ty)
                }
                None => false,
            };
            if !released {
                let message = "`with` replaces a field that may still hold a resource, which the new record would discard; move it out first (§10)";
                self.report(codes::RESOURCE_DISCARDED, self.span(receiver), message.to_string());
            }
        }
    }

    /// Whether the receiver `e` is a value, not the name of a type or interface.
    fn is_value(&self, e: ExprId) -> bool {
        self.p.expr_ty.get(e).is_some()
    }

    /// Whether `e` was reported as used after it moved, which leaves nothing for it to lend
    /// or access.
    fn moved_here(&self, e: ExprId) -> bool {
        self.reported.contains(&(codes::USE_AFTER_MOVE.id, self.span(e)))
    }

    /// Reads `e` without moving it, as a rejected call does with what it is given.
    fn read(&mut self, e: ExprId) {
        match self.place(e) {
            Some((local, path)) => self.use_place(e, local, &path),
            None => {
                self.indices(e);
                self.root(e);
            }
        }
    }

    /// Records the access `e` makes for its call, and reports one it conflicts with. A lent
    /// or moved value matters only when its type is unique.
    fn note(&mut self, accesses: &mut Vec<CallAccess>, outer: usize, e: ExprId, access: Access) {
        if self.moved_here(e) {
            return;
        }
        if access == Access::Inout {
            self.change_lent(e, outer);
        }
        let Some((local, steps)) = self.access_path(e) else { return };
        if access == Access::Lent && !self.moves(self.p.ty(e)) {
            return;
        }
        let conflict = accesses.iter().find_map(|other| {
            let overlap = if other.local == local { overlap(&other.steps, &steps) } else { Overlap::No };
            let conflicts = overlap != Overlap::No
                && matches!(
                    (other.access, access),
                    (Access::Inout, Access::Inout) | (Access::Inout, Access::Lent) | (Access::Lent, Access::Inout)
                );
            conflicts.then_some((other, overlap))
        });
        if let Some((_, Overlap::Unknown)) = conflict {
            let span = self.span(e);
            if self.reported.insert((codes::NOT_IMPLEMENTED.id, span)) {
                self.later.push(span);
            }
        } else if let Some((other, _)) = conflict {
            let (here, there) = (self.describe(e), self.describe(other.expr));
            let message = if here == there {
                format!("this call reaches `{here}` twice while one of the accesses is `inout` (§5.3)")
            } else {
                format!(
                    "`{here}` overlaps `{there}`, which this call also reaches while one of them is `inout`, so the call would have two accesses to one variable (§5.3)"
                )
            };
            self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
        }
        let access = CallAccess { access, local, steps, expr: e, by: Lender::Call };
        if access.access == Access::Lent {
            self.lent.push(access.clone());
        }
        accesses.push(access);
    }
}
