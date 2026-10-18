//! Moves and exclusive access (REFERENCE §5.1–§5.3), checked over a function body once its
//! types are settled.
//!
//! A value of a unique type, or an owned value of a type parameter without `Copy`, moves
//! wherever the checker found it copied ([`Checker::consumed`](super::Checker)), and
//! wherever a pattern binds its parts. The walk tracks which places may have moved: a local,
//! or a field of one at any depth. A use of a place that may have moved, or of a record one
//! of whose fields may have, is a use after move (E0501). Branches join what they moved, and
//! a loop's body is walked until what may have moved at its head stops growing, so a move
//! in one turn reaches the uses of the next. A lent place, a borrowed or `inout` parameter
//! or a part of one, never moves (E0504).
//!
//! Within one call, an `&` argument and an `inout self` receiver begin their access once the
//! other arguments are evaluated, as in Swift (SE-0176), and keep it for the call. Two of
//! them may not overlap, and a unique value lent to the call by one argument may not move in
//! a later one (E0505; OPEN_QUESTIONS P5).

use std::collections::HashSet;

use proviso_syntax::ast::*;
use proviso_syntax::diag::{Code, Diagnostics, codes};
use proviso_syntax::source::Span;

use crate::decls::{AdtId, IfaceId};
use crate::types::Ty;
use crate::{Local, LocalId, Program, Res};

/// Checks the moves and accesses of `body`, whose locals are `locals` and whose type
/// parameters implement `bounds`, given the expressions the checker found `consumed`.
/// Records each expression that moves a whole local in [`Program::moves_out`].
pub(crate) fn check(
    m: &Module,
    p: &mut Program,
    locals: &[Local],
    bounds: &[Vec<IfaceId>],
    consumed: &HashSet<ExprId>,
    body: &Block,
    diags: &mut Diagnostics,
) {
    let mut walk = Walk {
        m,
        p,
        locals,
        bounds,
        consumed,
        state: Some(State::default()),
        loops: Vec::new(),
        reported: HashSet::new(),
        errors: Vec::new(),
        moves_out: HashSet::new(),
    };
    walk.block(body);
    let (errors, moves_out) = (walk.errors, walk.moves_out);
    for (code, span, message) in errors {
        diags.error(code, span, message);
    }
    for e in moves_out {
        p.moves_out.insert(e, ());
    }
}

/// A local, or a field of one, by the index of each field on the way.
type Path = Vec<u32>;

/// A place that may have moved, where it moved, and how diagnostics write it.
#[derive(Clone)]
struct Moved {
    local: LocalId,
    path: Path,
    desc: String,
}

/// What may have moved at a point of the body that is reached.
#[derive(Clone, Default)]
struct State {
    moved: Vec<Moved>,
}

impl State {
    fn has(&self, local: LocalId, path: &[u32]) -> bool {
        self.moved.iter().any(|m| m.local == local && m.path == path)
    }

    /// Whether every place `other` holds is in this one too.
    fn covers(&self, other: &State) -> bool {
        other.moved.iter().all(|m| self.has(m.local, &m.path))
    }
}

/// What may have moved after either of two paths, where `None` is a path that leaves.
fn join(a: Option<State>, b: Option<State>) -> Option<State> {
    match (a, b) {
        (Some(mut a), Some(b)) => {
            for m in b.moved {
                if !a.has(m.local, &m.path) {
                    a.moved.push(m);
                }
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

/// A step of an access path: a field, or an element, whose index is known when it is a
/// literal.
#[derive(Clone, Copy, PartialEq)]
enum Step {
    Field(u32),
    Element(Option<u128>),
}

/// Whether two access paths of one local may reach the same memory: one is a prefix of the
/// other, where elements differ only when both indices are literals that differ.
fn overlap(a: &[Step], b: &[Step]) -> bool {
    a.iter().zip(b).all(|pair| match pair {
        (Step::Element(Some(x)), Step::Element(Some(y))) => x == y,
        (Step::Element(_), Step::Element(_)) => true,
        (x, y) => x == y,
    })
}

/// How an argument or receiver of a call reaches a place for the length of the call.
#[derive(Clone, Copy, PartialEq)]
enum Access {
    /// `&x`, or an `inout self` receiver.
    Inout,
    /// A borrowed argument or receiver of a unique type.
    Lent,
    /// An argument of a unique type that moves into the call.
    Move,
    /// A `take self` receiver of a unique type.
    ReceiverMove,
}

struct CallAccess {
    access: Access,
    local: LocalId,
    steps: Vec<Step>,
    expr: ExprId,
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
    /// What may have moved here, or `None` where the code is unreachable.
    state: Option<State>,
    loops: Vec<LoopFrame>,
    /// A loop's body is walked more than once, so each mistake is reported once.
    reported: HashSet<(&'static str, Span)>,
    errors: Vec<(Code, Span, String)>,
    moves_out: HashSet<ExprId>,
}

impl Walk<'_> {
    fn report(&mut self, code: Code, span: Span, message: String) {
        if self.reported.insert((code.id, span)) {
            self.errors.push((code, span, message));
        }
    }

    fn span(&self, e: ExprId) -> Span {
        self.m.exprs[e].span
    }

    fn moves(&self, ty: &Ty) -> bool {
        self.p.decls.moves(ty, self.bounds)
    }

    /// Whether `ty` mentions a type parameter without `Copy`, whose copy of a borrowed value
    /// the checker reports instead (E0503).
    fn generic(&self, ty: &Ty) -> bool {
        // A type that doesn't move mentions no such parameter.
        self.moves(ty) && self.generic_in(ty, &mut HashSet::new())
    }

    /// [`Walk::generic`], where `seen` holds the argument lists already walked, so a type that
    /// shares a part costs each part once.
    fn generic_in(&self, ty: &Ty, seen: &mut HashSet<usize>) -> bool {
        match ty {
            Ty::Param(i) => !self.bounds.get(*i as usize).is_some_and(|b| b.contains(&IfaceId::COPY)),
            Ty::Adt(_, args) => {
                seen.insert(std::sync::Arc::as_ptr(args) as *const Ty as usize)
                    && args.iter().any(|arg| self.generic_in(arg, seen))
            }
            _ => false,
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
                let literal = match self.m.exprs[index].kind {
                    ExprKind::Int(value) => Some(value),
                    _ => None,
                };
                steps.push(Step::Element(literal));
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

    // ---- places ----

    /// Reports a use of `local`'s `path` that may have moved, or a part of which may have.
    fn use_place(&mut self, e: ExprId, local: LocalId, path: &[u32]) {
        let Some(state) = &self.state else { return };
        let Some(moved) =
            state.moved.iter().find(|m| m.local == local && (is_prefix(&m.path, path) || is_prefix(path, &m.path)))
        else {
            return;
        };
        let here = self.describe(e);
        let message = if moved.path.len() > path.len() {
            format!("`{}` may have moved already, so `{here}` can't be used whole here (§5.1)", moved.desc)
        } else if moved.path.len() < path.len() {
            format!("`{}` may have moved already, so `{here}` can't be used here (§5.1)", moved.desc)
        } else {
            format!("`{here}` may have moved already, so it can't be used here; assign it a new value first (§5.1)")
        };
        self.report(codes::USE_AFTER_MOVE, self.span(e), message);
    }

    /// Moves `local`'s `path`, which `e` writes as `desc`.
    fn move_place(&mut self, e: ExprId, local: LocalId, path: Path, desc: String) {
        self.use_place(e, local, &path);
        if self.locals[local.index()].borrowed {
            let message = format!(
                "`{desc}` is lent here, not owned, so it can't move; only an owned value, such as a `take` parameter, can (§5.2)"
            );
            self.report(codes::LENT_VALUE_MOVED, self.span(e), message);
            return;
        }
        let Some(state) = &mut self.state else { return };
        if state.moved.iter().any(|m| m.local == local && is_prefix(&m.path, &path)) {
            return;
        }
        state.moved.retain(|m| !(m.local == local && is_prefix(&path, &m.path)));
        if path.is_empty() {
            self.moves_out.insert(e);
        }
        state.moved.push(Moved { local, path, desc });
    }

    /// Gives `local`'s `path` a new value, which makes it and its parts usable again. A part
    /// of a value that may have moved can't be assigned.
    fn assign_place(&mut self, e: ExprId, local: LocalId, path: &[u32]) {
        let Some(state) = &self.state else { return };
        if state.moved.iter().any(|m| m.local == local && m.path.len() < path.len() && is_prefix(&m.path, path)) {
            self.use_place(e, local, path);
            return;
        }
        if let Some(state) = &mut self.state {
            state.moved.retain(|m| !(m.local == local && is_prefix(path, &m.path)));
        }
    }

    /// A new value for `local`, as a pattern binds it on each turn of a loop.
    fn bind(&mut self, local: LocalId) {
        if let Some(state) = &mut self.state {
            state.moved.retain(|m| m.local != local);
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
                if let Some(frame) = self.loops.iter_mut().rev().find(|f| Some(f.expr) == target) {
                    let slot = if is_break { &mut frame.breaks } else { &mut frame.continues };
                    *slot = join(slot.take(), state);
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

    /// An assignment's target that isn't a place, such as `xs[i].n`, which uses the
    /// variable it changes.
    fn target(&mut self, target: ExprId) {
        match self.m.exprs[target].kind {
            ExprKind::Field { base, .. } => self.target(base),
            _ => self.expr(target),
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
            self.state = None;
        }
    }

    fn expr_kind(&mut self, e: ExprId) {
        let m = self.m;
        if let Some((local, path)) = self.place(e) {
            if self.consumed.contains(&e) && self.moves(self.p.ty(e)) {
                let desc = self.describe(e);
                // A lent value whose type parameter lacks `Copy` is reported by the checker.
                if self.locals[local.index()].borrowed && self.generic(self.p.ty(e)) {
                    return;
                }
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
            ExprKind::Call { args, .. } => self.call(None, args),
            ExprKind::MethodCall { receiver, args, .. } => {
                let mode = match self.p.res(e) {
                    Some(Res::Fn(f)) if self.p.fns[f].receiver.is_some() => self.p.fns[f].self_mode,
                    Some(Res::Method(builtin)) if builtin.changes_receiver() => ParamMode::Inout,
                    _ => ParamMode::Borrow,
                };
                self.call(Some((*receiver, mode)), args);
            }
            ExprKind::Field { base, .. } => self.expr(*base),
            ExprKind::Index { base, index } => {
                self.expr(*base);
                self.expr(*index);
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
            ExprKind::Try(inner) | ExprKind::Attempt(inner) | ExprKind::Fail(inner) => self.expr(*inner),
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
                let before = self.state.clone();
                let mut after = None;
                for arm in arms {
                    self.state = before.clone();
                    self.matched(*scrutinee, arm.pat);
                    if let Some(guard) = arm.guard {
                        self.expr(guard);
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
    fn looped(&mut self, e: ExprId, turn: impl Fn(&mut Self) -> Option<State>) {
        let entry = self.state.clone();
        let mut head = entry.clone();
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
                self.state = join(exit, frame.breaks);
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
        let m = self.m;
        match &m.pats[pat].kind {
            PatKind::Bind(_) => {
                if let Some(&local) = self.p.pat_local.get(pat) {
                    self.bind(local);
                }
            }
            PatKind::Tuple(parts) => {
                for &part in parts {
                    self.bind_all(part);
                }
            }
            PatKind::Ctor { fields: Some(fields), .. } => {
                for field in fields {
                    self.bind_all(field.pat);
                }
            }
            _ => {}
        }
    }

    // ---- calls ----

    /// The arguments of a call, and its receiver with the mode it takes `self` in. An `&`
    /// argument and an `inout self` receiver are reached once the other arguments are
    /// evaluated (§5.3), and no two accesses of the call may conflict.
    fn call(&mut self, receiver: Option<(ExprId, ParamMode)>, args: &[Arg]) {
        let mut accesses: Vec<CallAccess> = Vec::new();
        let late = matches!(receiver, Some((_, ParamMode::Inout)));
        if let Some((receiver, _)) = receiver
            && !late
        {
            self.expr(receiver);
            // A `take self` receiver, and that of `with` on a unique record, move.
            let access = if self.consumed.contains(&receiver) { Access::ReceiverMove } else { Access::Lent };
            self.note(&mut accesses, receiver, access);
        }
        for arg in args.iter().filter(|arg| !arg.inout) {
            self.expr(arg.value);
            let access = if self.consumed.contains(&arg.value) { Access::Move } else { Access::Lent };
            self.note(&mut accesses, arg.value, access);
        }
        for arg in args.iter().filter(|arg| arg.inout) {
            self.expr(arg.value);
            self.note(&mut accesses, arg.value, Access::Inout);
        }
        if let Some((receiver, _)) = receiver
            && late
        {
            self.expr(receiver);
            self.note(&mut accesses, receiver, Access::Inout);
        }
    }

    /// Records the access `e` makes for its call, and reports one it conflicts with. A lent
    /// or moved value matters only when its type is unique.
    fn note(&mut self, accesses: &mut Vec<CallAccess>, e: ExprId, access: Access) {
        let Some((local, steps)) = self.access_path(e) else { return };
        if matches!(access, Access::Lent | Access::Move | Access::ReceiverMove) && !self.moves(self.p.ty(e)) {
            return;
        }
        let conflict = accesses.iter().find(|other| {
            other.local == local
                && overlap(&other.steps, &steps)
                && matches!(
                    (other.access, access),
                    (Access::Inout, Access::Inout)
                        | (Access::Inout, Access::Lent)
                        | (Access::Lent, Access::Inout)
                        | (Access::Lent, Access::Move)
                        | (Access::ReceiverMove, Access::Inout)
                )
        });
        if let Some(other) = conflict {
            let (here, there) = (self.describe(e), self.describe(other.expr));
            let message = match (other.access, access) {
                (Access::Lent, Access::Move) => {
                    format!(
                        "`{here}` is lent to this call by an earlier argument, so it can't also move into it (§5.3)"
                    )
                }
                (Access::ReceiverMove, _) => {
                    format!(
                        "`{there}` moves into this call as its receiver, so `{here}` can't also be passed with `&` (§5.3)"
                    )
                }
                _ if other.steps.iter().chain(&steps).any(|s| *s == Step::Element(None)) => format!(
                    "`{here}` may overlap `{there}`, which this call also reaches while one of them is `inout`; two elements are known to differ only when their indices are different literals (§5.3; OPEN_QUESTIONS P5)"
                ),
                _ => format!(
                    "`{here}` overlaps `{there}`, which this call also reaches while one of them is `inout`, so the call would have two accesses to one variable (§5.3)"
                ),
            };
            self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
        }
        accesses.push(CallAccess { access, local, steps, expr: e });
    }
}
