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

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, Planned, codes};
use proviso_syntax::source::Span;

use crate::decls::{AdtId, IfaceId};
use crate::types::Ty;
use crate::{Local, LocalId, Program, Res};

/// What the checker found about the expressions of a body.
pub(crate) struct Found {
    /// The expressions whose values are copied, or moved when their type is unique.
    pub consumed: HashSet<ExprId>,
    /// The expressions an error was reported at, not at one of their parts.
    pub rejected: HashSet<ExprId>,
}

/// What the move pass walks.
pub(crate) enum Body<'a> {
    /// A function's body.
    Fn(&'a Block),
    /// A refinement, whose fields are lent to it.
    Predicate(ExprId),
}

/// Checks the moves and accesses of `body`, whose locals are `locals` and whose type
/// parameters implement `bounds`, given the expressions the checker found `consumed`.
/// Records each expression that moves a whole local in [`Program::moves_out`], and each
/// `match` arm whose pattern does in [`Program::arms_out`].
pub(crate) fn check(
    m: &Module,
    p: &mut Program,
    locals: &[Local],
    bounds: &[Vec<IfaceId>],
    found: &Found,
    body: Body,
    diags: &mut Diagnostics,
) {
    let mut walk = Walk {
        m,
        p,
        locals,
        bounds,
        consumed: &found.consumed,
        rejected: &found.rejected,
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
    };
    match body {
        Body::Fn(block) => walk.block(block),
        Body::Predicate(e) => walk.expr(e),
    }
    let (errors, later, moves_out, arms_out) = (walk.errors, walk.later, walk.moves_out, walk.arms_out);
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
    for e in moves_out {
        p.moves_out.insert(e, ());
    }
    for pat in arms_out {
        p.arms_out.insert(pat, ());
    }
}

/// A local, or a field of one, by the index of each field on the way.
type Path = Vec<u32>;

/// What may have moved at a point of the body that is reached: each place, by its local's
/// index and its path, with how diagnostics write it. The map is shared until it changes,
/// so a branch that moves nothing costs nothing to copy or join.
#[derive(Clone, Default)]
struct State {
    moved: Arc<BTreeMap<(u32, Path), String>>,
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
}

/// What may have moved after either of two paths, where `None` is a path that leaves.
fn join(a: Option<State>, b: Option<State>) -> Option<State> {
    match (a, b) {
        (Some(mut a), Some(b)) => {
            if a.covers(&b) {
                return Some(a);
            }
            if b.covers(&a) {
                return Some(b);
            }
            let moved = Arc::make_mut(&mut a.moved);
            for (key, desc) in b.moved.iter() {
                moved.entry(key.clone()).or_insert_with(|| desc.clone());
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
}

impl Walk<'_> {
    fn report(&mut self, code: Code, span: Span, message: String) {
        if self.reported.insert((code.id, span)) {
            self.errors.push((code, span, message));
        }
    }

    /// Notes that the loops being walked touch `local`.
    fn touch(&mut self, local: LocalId) {
        if let Some(top) = self.touched.last_mut() {
            top.insert(local);
        }
    }

    fn span(&self, e: ExprId) -> Span {
        self.m.exprs[e].span
    }

    fn moves(&self, ty: &Ty) -> bool {
        self.p.decls.moves_memo(ty, self.bounds, &mut self.memo.borrow_mut())
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
        if self.locals[local.index()].borrowed {
            let message = format!(
                "`{desc}` is lent here, not owned, so it can't move; only an owned value, such as a `take` parameter, can (§5.2)"
            );
            self.report(codes::LENT_VALUE_MOVED, self.span(e), message);
            return;
        }
        if self.guarded.contains(&local) {
            let message = format!(
                "`{desc}` is bound by this arm's pattern and lent to its guard, which can only look at it, since the arm may still not be chosen; move it in the arm's body (OPEN_QUESTIONS P5)"
            );
            self.report(codes::LENT_VALUE_MOVED, self.span(e), message);
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
        let Some(state) = &mut self.state else { return };
        if state.of(local).any(|(m, _)| is_prefix(m, &path)) {
            return;
        }
        state.forget(local, |m| !is_prefix(&path, m));
        Arc::make_mut(&mut state.moved).insert((local.0, path.clone()), desc);
        if self.place(e).is_some_and(|named| named == (local, path.clone())) && self.unrefined(local, &path) {
            self.moves_out.insert(e);
        }
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
        }
    }

    /// A new value for `local`, as a pattern binds it on each turn of a loop.
    fn bind(&mut self, local: LocalId) {
        self.touch(local);
        if let Some(state) = &mut self.state {
            state.forget(local, |_| false);
        }
    }

    // ---- statements ----

    fn block(&mut self, block: &Block) {
        for &s in &block.stmts {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: StmtId) {
        let m = self.m;
        match &m.stmts[s].kind {
            StmtKind::Let { pat, init, .. } => {
                self.expr(*init);
                self.matched(*init, *pat);
            }
            StmtKind::Assign { target, op, value } => {
                self.expr(*value);
                if self.place(*target).is_some() {
                    self.change_lent(*target, self.lent.len());
                }
                match self.place(*target) {
                    Some((local, path)) if *op == AssignOp::Set => self.assign_place(*target, local, &path),
                    Some((local, path)) => self.use_place(*target, local, &path),
                    None => self.target(*target),
                }
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) => self.expr(*e),
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(*value);
                }
                self.state = None;
            }
            StmtKind::Break(_) | StmtKind::Continue(_) => {
                let is_break = matches!(m.stmts[s].kind, StmtKind::Break(_));
                let state = self.state.take();
                let target = self.p.jump_target.get(s).copied();
                if let Some(i) = self.loops.iter().rposition(|f| Some(f.expr) == target) {
                    let frame = &mut self.loops[i];
                    let slot = if is_break { &mut frame.breaks } else { &mut frame.continues };
                    *slot = join(slot.take(), state);
                    self.reach = self.reach.min(i + 1);
                }
            }
            StmtKind::Check { cond, fallback } => {
                self.condition(*cond);
                // The fallback leaves, so only the code after it runs on.
                let after = self.state.clone();
                self.fallback(fallback);
                self.state = after;
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

    fn fallback(&mut self, fallback: &Fallback) {
        match fallback {
            Fallback::Value(x) => self.expr(*x),
            Fallback::Block(block) => self.block(block),
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
            | ExprKind::Unreachable
            | ExprKind::Error => {}
            ExprKind::FText(parts) => {
                for part in parts {
                    if let FTextPart::Expr(x) = part {
                        self.expr(*x);
                    }
                }
            }
            ExprKind::Call { args, .. } => self.call(e, None, args),
            ExprKind::MethodCall { receiver, args, .. } => {
                let mode = match self.p.res(e) {
                    Some(Res::Fn(f)) if self.p.fns[f].receiver.is_some() => self.p.fns[f].self_mode,
                    Some(Res::Method(builtin)) if builtin.changes_receiver() => ParamMode::Inout,
                    _ => ParamMode::Borrow,
                };
                self.call(e, Some((*receiver, mode)), args);
            }
            ExprKind::Field { base, .. } => self.expr(*base),
            ExprKind::Index { base, index } => {
                self.expr(*base);
                // The base is reached before its index, which may not move or change it.
                let outer = self.lent.len();
                if let Some((local, steps)) = self.access_path(*base)
                    && self.moves(self.p.ty(*base))
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
            }
            ExprKind::Try(inner) | ExprKind::Fail(inner) => self.expr(*inner),
            ExprKind::Attempt(inner) => {
                self.expr(*inner);
                let failed = self.handled.remove(&e).flatten();
                self.state = join(self.state.take(), failed);
            }
            ExprKind::If { cond, then_block, else_branch } => {
                self.condition(*cond);
                let after = self.state.clone();
                self.block(then_block);
                let then_state = std::mem::replace(&mut self.state, after);
                match else_branch {
                    Some(ElseBranch::Block(block)) => self.block(block),
                    Some(ElseBranch::If(nested)) => self.expr(*nested),
                    None => {}
                }
                self.state = join(then_state, self.state.take());
            }
            ExprKind::While { cond, body, .. } => {
                self.looped(e, |w| {
                    w.condition(*cond);
                    let exit = w.state.clone();
                    w.block(body);
                    exit
                });
            }
            ExprKind::Loop { body, .. } => {
                self.looped(e, |w| {
                    w.block(body);
                    None
                });
            }
            ExprKind::For { pat, iter, body, .. } => {
                self.expr(*iter);
                self.looped(e, |w| {
                    let exit = w.state.clone();
                    w.bind_all(*pat);
                    w.block(body);
                    exit
                });
            }
            ExprKind::Debug(values) | ExprKind::Tuple(values) | ExprKind::List(values) => {
                for &value in values {
                    self.expr(value);
                }
            }
            ExprKind::Map(entries) => {
                for &(k, v) in entries {
                    self.expr(k);
                    self.expr(v);
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.expr(*scrutinee);
                // What may have moved when an arm is tried: what moved before the `match`,
                // and what the guards of the arms before it moved.
                let mut tried = self.state.clone();
                let mut after = None;
                for arm in arms {
                    self.state = tried.clone();
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
                    self.matched(*scrutinee, arm.pat);
                    // The scrutinee leaves its local only once this arm is chosen.
                    if self.moves_out.remove(scrutinee) {
                        self.arms_out.insert(arm.pat);
                    }
                    self.block(&arm.body);
                    after = join(after, self.state.take());
                }
                self.state = after;
            }
            ExprKind::Is { value, pat } => {
                self.expr(*value);
                self.matched(*value, *pat);
            }
            ExprKind::Else { value, fallback } => {
                self.expr(*value);
                let after = self.state.clone();
                let failed = self.handled.remove(&e).flatten();
                self.state = join(self.state.take(), failed);
                self.fallback(fallback);
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
        if let (Some(entry), Some(last)) = (&entry, self.loop_cache.get(&e)) {
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
            self.loops.push(LoopFrame { expr: e, breaks: None, continues: None });
            let exit = turn(self);
            let frame = self.loops.pop().expect("the loop's frame was pushed");
            let back = join(self.state.take(), frame.continues);
            let next = join(entry.clone(), back);
            let grew = match (&head, &next) {
                (Some(head), Some(next)) => !head.covers(next),
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

    /// Gives each local `pat` binds a new value.
    fn bind_all(&mut self, pat: PatId) {
        let mut locals = Vec::new();
        self.pattern_locals(pat, &mut locals);
        for local in locals {
            self.bind(local);
        }
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
            // A rejected call only reads what it is given.
            for value in receiver.map(|(r, _)| r).into_iter().chain(args.iter().map(|arg| arg.value)) {
                self.read(value);
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
            for arg in args {
                self.expr(arg.value);
            }
            let replaced = self.p.with_fields.get(e).expect("`with` is resolved");
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
        let late = matches!(receiver, Some((_, ParamMode::Inout)));
        match receiver {
            Some((receiver, _)) if late => self.indices(receiver),
            Some((receiver, _)) => {
                self.expr(receiver);
                // A `take self` receiver, and that of `with` on a unique record, move.
                if !self.consumed.contains(&receiver) {
                    self.note(&mut accesses, outer, receiver, Access::Lent);
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
            if !self.consumed.contains(&arg.value) {
                self.note(&mut accesses, outer, arg.value, Access::Lent);
            }
        }
        for arg in args.iter().filter(|arg| arg.inout) {
            self.root(arg.value);
            self.note(&mut accesses, outer, arg.value, Access::Inout);
        }
        if let Some((receiver, _)) = receiver
            && late
        {
            self.root(receiver);
            self.note(&mut accesses, outer, receiver, Access::Inout);
        }
        self.lent.truncate(outer);
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
        // A value used after it moved was already reported, and has nothing left to access.
        if self.reported.contains(&(codes::USE_AFTER_MOVE.id, self.span(e))) {
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
