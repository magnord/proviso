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
//! A closure borrows what it captures (REFERENCE §6.7), so its body can't move a captured
//! unique value or consume a captured resource (E0504, E0502). It reads its captures where
//! it is made, and a use of a local that holds it reads them again, so they can't have moved
//! by then (E0501). A closure argument reads its captures for the length of the call, so an
//! `&` argument or `inout self` receiver may not reach them, and a captured unique value may
//! not move in a later argument (E0505; OPEN_QUESTIONS P5).
//!
//! A value with reach, or that can hold a function value, has an origin: how long it may
//! live (OPEN_QUESTIONS P5). A `keep` parameter and an owned value built from free parts are
//! free. A borrowed parameter is bounded by the call, and a closure that captures locals by
//! reference by the last of them to end. A value derived from others, by a field, an element,
//! a call or a construction, takes the shortest of their origins. A value can't escape where
//! it would outlive its origin: a `return`, a `fail`, a store into a place that outlives it,
//! a `keep` argument, a capture by a closure passed to a `keep fn` parameter, or the value of
//! a block that declares what it depends on. One that can hold a function value is E0509,
//! and any other E0607.
//!
//! A closure that changes a `var` it captures holds the `var` exclusively from where a local
//! gets it to the local's last use, which a use in a loop that doesn't declare the local
//! extends to the loop's end. Any other use of the `var` in between, by name or through a
//! closure that captures it, is E0505 (OPEN_QUESTIONS Q34). Passed to a call directly, the
//! closure changes the `var` as an `&` argument does, once the other arguments are
//! evaluated, and the call rolls the `var` back if it fails.
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
    /// The fields rejected as methods named as values.
    pub method_values: HashSet<ExprId>,
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
    /// A test's body.
    Test(&'a Block),
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
    /// The mode of each parameter, `self` first, by local.
    pub modes: Vec<ParamMode>,
    /// The error type it fails with, if any.
    pub fails: Option<Ty>,
}

/// Checks the moves and accesses of `body`, whose locals are `locals` and whose type
/// parameters implement `bounds`, given the expressions the checker found `consumed`.
/// Records each expression that moves a whole local in [`Program::moves_out`], each `match`
/// arm whose pattern does in [`Program::arms_out`], and what the interpreter needs to
/// abandon resources. Returns the locals the body uses.
pub(crate) fn check(
    m: &Ast,
    p: &mut Program,
    locals: &[Local],
    bounds: &[Vec<IfaceId>],
    found: &Found,
    body: Body,
    diags: &mut Diagnostics,
) -> HashSet<LocalId> {
    // A closure's body is walked with the origins its captures end the walk with, since a
    // later assignment may give a captured `var` a shorter lived value before the closure
    // runs. When a walk ends with more than its closures saw, it is walked again.
    let mut view: Vec<Origin> = vec![None; locals.len()];
    let walk = loop {
        let mut walk = Walk {
            m,
            p,
            locals,
            bounds,
            consumed: &found.consumed,
            rejected: &found.rejected,
            method_values: &found.method_values,
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
            reading: RefCell::new(None),
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
            captured: Vec::new(),
            fn_reads: HashMap::new(),
            fn_read_sets: HashMap::new(),
            listed: Vec::new(),
            expands: 0,
            origins: vec![None; locals.len()],
            inout_limits: HashMap::new(),
            frame: None,
            fails: None,
            escaped: HashSet::new(),
            grown: 0,
            holders: HashMap::new(),
            last_use: vec![0; locals.len()],
            declared: vec![0; locals.len()],
            holds_fn: locals.iter().map(|local| p.decls.holds_fn(&local.ty)).collect(),
            loop_spans: Vec::new(),
            var_uses: HashMap::new(),
            rollbacks: HashMap::new(),
            var_names: HashMap::new(),
            view: std::mem::take(&mut view),
            seen: Vec::new(),
            closure_exprs: Vec::new(),
            stores: Vec::new(),
            clashed: HashSet::new(),
        };
        match &body {
            Body::Fn(body) => {
                walk.consumes_self = body.consumes_self;
                walk.frame = INOUT;
                walk.fails = body.fails.clone();
                for (i, mode) in body.modes.iter().enumerate() {
                    walk.param(LocalId(i as u32), *mode, CALL, INOUT);
                }
                walk.scopes.push(body.params.clone());
                walk.block(body.block);
                walk.close_scope("the end of the function");
            }
            Body::Predicate(e) => {
                walk.origins.fill(CALL);
                walk.expr(*e)
            }
            Body::Test(block) => {
                walk.scopes.push(Vec::new());
                walk.block(block);
                walk.close_scope("the end of the test");
            }
            Body::Example { call, expected } => {
                for e in std::iter::once(*call).chain(*expected) {
                    walk.expr(e);
                    // An example with an error may not compare at all (REFERENCE §15.1).
                    if found.errors.is_empty() {
                        walk.discarded(e, "the example drops once it has compared it");
                    }
                }
            }
        }
        walk.held_vars();
        let stale = walk.seen.iter().any(|&(local, saw)| walk.origins[local.index()] > saw);
        if !stale {
            break walk;
        }
        let mut next = std::mem::take(&mut walk.view);
        for &(local, _) in &walk.seen {
            walk.origins[local.index()] = walk.origins[local.index()].max(next[local.index()]);
        }
        walk.closure_origins();
        for &(local, _) in &walk.seen {
            next[local.index()] = walk.origins[local.index()];
        }
        view = next;
    };
    let Walk { errors, later, moves_out, arms_out, unscheduled, held, owned_binds, parts_out, used, rollbacks, .. } =
        walk;
    for (e, vars) in rollbacks {
        p.rollback.insert(e, vars.into_boxed_slice());
    }
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

/// The uses of a `var`, by where each is and the local holding a closure it is used through,
/// each once however often a loop is walked, with the use's span and the `var`'s name.
type VarUses = HashMap<(u32, Option<LocalId>), (Span, Arc<str>)>;

/// A local, or a field of one, by the index of each field on the way.
type Path = Vec<u32>;

/// How long a value may live (see the module's documentation). `None` is free, so it may be
/// kept. A position bounds it, and a larger position ends sooner: [`INOUT`] is what an
/// `inout` parameter of the function holds, [`CALL`] the function's call, [`closure_call`]
/// the call of a closure, and [`alive`] the life of a local. Where values meet, the larger
/// position wins, which doesn't depend on their order.
type Origin = Option<u32>;

const INOUT: Origin = Some(0);
const CALL: Origin = Some(1);

/// Bounded by local `i`: a closure that captures it by reference.
fn alive(i: LocalId) -> Origin {
    Some(2 * i.0 + 3)
}

/// Bounded by the call of a closure whose first local is `base`: its parameters.
fn closure_call(base: u32) -> Origin {
    Some(2 * base + 2)
}

/// Whether `origin` is that of a function's or closure's parameter without `keep`. A call of
/// such a function value gives what its caller's own values gave it, and the caller bounds
/// the call that passed it by the argument (`Walk::given_back`), so it doesn't bound the
/// call's result here.
fn of_param(origin: Origin) -> bool {
    matches!(origin, Some(n) if n == 1 || (n >= 2 && n % 2 == 0))
}

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
            // Released on both paths, so it is released after either. A place released on
            // one path is, on the other, when it or a place holding it is.
            if !a.released_in(&b) {
                a.released = if b.released_in(&a) {
                    b.released
                } else {
                    let both = |x: &State, y: &State| {
                        x.released
                            .iter()
                            .filter(|(l, path)| y.is_released(LocalId(*l), path))
                            .cloned()
                            .collect::<Vec<_>>()
                    };
                    let mut met: BTreeSet<(u32, Path)> = both(&a, &b).into_iter().collect();
                    met.extend(both(&b, &a));
                    Arc::new(met)
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
    /// A local of a copy type that a closure argument captures, which the call may read
    /// while it runs.
    Read,
}

#[derive(Clone)]
struct CallAccess {
    access: Access,
    local: LocalId,
    steps: Vec<Step>,
    expr: ExprId,
    /// What the place is lent to.
    by: Lender,
    /// The name of the local, when a closure argument captures it.
    captured: Option<Arc<str>>,
}

/// A local a call of a function value reads, with its name.
type Read = (LocalId, Arc<str>);

/// The locals a call of a function value reads.
type Reads = Vec<Read>;

/// What a lent place is lent to, for as long as it runs.
#[derive(Clone, Copy, PartialEq)]
enum Lender {
    /// A call, while its later arguments are evaluated.
    Call,
    /// A `match` arm's guard.
    Guard,
    /// Its own index, as the base of an indexing expression.
    Index,
    /// A call, by a closure argument that captures it.
    Capture,
    /// A call, by the function value it calls, which captures it.
    Callee,
}

/// What a loop reached when it was last walked: what may have moved at its head and where it
/// ends, and the locals it touched.
struct LoopWalk {
    head: State,
    exit: Option<State>,
    touched: HashSet<LocalId>,
    /// [`Walk::grown`] when it was walked, since a grown origin changes what its turn checks.
    grown: u32,
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
    m: &'a Ast,
    p: &'a Program,
    locals: &'a [Local],
    bounds: &'a [Vec<IfaceId>],
    consumed: &'a HashSet<ExprId>,
    /// The expressions the checker rejected, which move nothing and lend nothing, so that
    /// nothing is reported that depends on them (REFERENCE §15.1).
    rejected: &'a HashSet<ExprId>,
    /// See [`Found::method_values`].
    method_values: &'a HashSet<ExprId>,
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
    memo: RefCell<HashMap<(u32, usize), bool>>,
    /// The locals [`Walk::origin`] reads, while [`Walk::loop_origins`] collects them.
    reading: RefCell<Option<Vec<LocalId>>>,
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
    /// The locals the closures being walked capture, which they borrow.
    captured: Vec<LocalId>,
    /// What a call of the function values each local holds reads: the locals their closures
    /// capture, and what those read in turn, with their names, however the closures got
    /// there. A `let` local listed here is left out of the lists, since nothing can move it
    /// or give it a new value, but a `var` can still be passed with `&` (§5.3).
    fn_reads: HashMap<LocalId, Arc<Vec<Read>>>,
    /// The locals in each list of [`Walk::fn_reads`] that a store added to, so a store
    /// adds to one in the time what it adds takes.
    fn_read_sets: HashMap<LocalId, HashSet<LocalId>>,
    /// For each local, the last [`Walk::expand`] that listed it, so each lists it once.
    listed: Vec<u32>,
    expands: u32,
    /// The origin of what each local may hold, which only grows as the walk goes on.
    origins: Vec<Origin>,
    /// The longest origin a store into each `inout` parameter may take.
    inout_limits: HashMap<LocalId, Origin>,
    /// The longest origin the value the frame being walked returns or fails with may take.
    frame: Origin,
    /// The error type the frame being walked fails with, if any.
    fails: Option<Ty>,
    /// The origin each local ended the last walk with, which a closure that captures it
    /// sees in its body.
    view: Vec<Origin>,
    /// The origins each closure's body saw its captures with.
    seen: Vec<(LocalId, Origin)>,
    /// The default closures walked.
    closure_exprs: Vec<ExprId>,
    /// Each `var`, with where a call reaches it beside a closure that changes it, which that
    /// call's report covers, so holding it doesn't report the use again (REFERENCE §15.1).
    clashed: HashSet<(LocalId, u32)>,
    /// What each store in the closures being walked gave a local, which may be no more than
    /// the closure saw it with.
    stores: Vec<(LocalId, Origin)>,
    /// The values reported as escaping, which give no origin to what holds them, so each
    /// mistake is reported once (REFERENCE §15.1).
    escaped: HashSet<ExprId>,
    /// How many times a local's origin has grown, so a loop whose turn grew one is walked
    /// again.
    grown: u32,
    /// The locals that may hold a closure that changes a `var` it captures: those `var`s,
    /// where the local first may, and how diagnostics write the local.
    holders: HashMap<LocalId, (Vec<LocalId>, u32, String)>,
    /// Where each local is used last, so far, where a use in a loop that doesn't declare it
    /// lasts to the loop's end.
    last_use: Vec<u32>,
    /// Where each local is declared.
    declared: Vec<u32>,
    /// Whether each local's type can hold a function value.
    holds_fn: Vec<bool>,
    /// The loops around the code being walked, outermost first, also outside a closure.
    loop_spans: Vec<Span>,
    /// Each use of a `var`: where, how diagnostics write the `var`, and the local holding a
    /// closure it is used through, if any.
    var_uses: HashMap<LocalId, VarUses>,
    /// See [`Program::rollback`].
    rollbacks: HashMap<ExprId, Vec<LocalId>>,
    /// The names of the locals the closures walked so far capture.
    var_names: HashMap<LocalId, Arc<str>>,
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

    /// Whether what `e` gives is unknown, since the checker rejected it or reported an error
    /// inside it. A call of a function gives a value of its result type whatever its
    /// arguments are, so only an error at the call makes that unknown (issue #46), such as
    /// its value not fitting where it is given.
    fn gives_unknown(&self, e: ExprId) -> bool {
        match self.m.exprs[e].kind {
            ExprKind::Call { callee, .. } if matches!(self.p.res(callee), Some(Res::Fn(_))) => {
                let span = self.span(e);
                self.rejected.contains(&e) || self.checked.contains(&span)
            }
            _ => self.tainted(e),
        }
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
    /// construction or literal none of whose parts is one, such as `None`, `Slot.Empty`,
    /// `(1, None)` or `[]`. A base resource's construction holds itself.
    fn holds_resource(&self, e: ExprId) -> bool {
        if !self.is_resource(self.p.ty(e)) {
            return false;
        }
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (ExprKind::Name(_) | ExprKind::Field { .. }, Some(Res::Ctor(..))) => false,
            (ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. }, Some(Res::Ctor(adt, _))) => {
                self.p.decls.adt(adt).resource_base || args.iter().any(|arg| self.holds_resource(arg.value))
            }
            (ExprKind::Call { callee, args, .. }, _) if let Some(Res::Ctor(adt, _)) = self.p.res(*callee) => {
                self.p.decls.adt(adt).resource_base || args.iter().any(|arg| self.holds_resource(arg.value))
            }
            (ExprKind::Tuple(parts) | ExprKind::List(parts), _) => parts.iter().any(|&part| self.holds_resource(part)),
            (ExprKind::Map(entries), _) => {
                entries.iter().any(|&(k, v)| self.holds_resource(k) || self.holds_resource(v))
            }
            _ => true,
        }
    }

    /// [`Walk::holds_resource`] for a value bound to a `var` or assigned to one, which may get
    /// a resource in place later, through a field, an element or an `&` argument. Only an
    /// enum's variant can't, so only a variant that holds no resource holds none here.
    fn may_hold_later(&self, e: ExprId) -> bool {
        if !self.is_resource(self.p.ty(e)) {
            return false;
        }
        let variant = |adt: AdtId| self.p.decls.adt(adt).is_enum();
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (ExprKind::Name(_) | ExprKind::Field { .. }, Some(Res::Ctor(adt, _))) if variant(adt) => false,
            (ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. }, Some(Res::Ctor(adt, _)))
                if variant(adt) =>
            {
                args.iter().any(|arg| self.holds_resource(arg.value))
            }
            (ExprKind::Call { callee, args, .. }, _)
                if let Some(Res::Ctor(adt, _)) = self.p.res(*callee)
                    && variant(adt) =>
            {
                args.iter().any(|arg| self.holds_resource(arg.value))
            }
            _ => true,
        }
    }

    /// The locals of `pat` whose part of `init`, when the pattern follows its construction,
    /// holds no resource and can't get one in place: for a `var`, a variant without one, and
    /// for a `let`, any value without one.
    fn empty_bindings(&self, pat: PatId, init: Option<ExprId>, out: &mut Vec<LocalId>) {
        let Some(init) = init else { return };
        match &self.m.pats[pat].kind {
            PatKind::Bind(_) => {
                let Some(&local) = self.p.pat_local.get(pat) else { return };
                let empty = if self.locals[local.index()].mutable {
                    !self.may_hold_later(init)
                } else {
                    !self.holds_resource(init)
                };
                if empty && !out.contains(&local) {
                    out.push(local);
                }
            }
            PatKind::Tuple(parts) => {
                if let ExprKind::Tuple(values) = &self.m.exprs[init].kind {
                    for (&part, &value) in parts.iter().zip(values) {
                        self.empty_bindings(part, Some(value), out);
                    }
                }
            }
            PatKind::Ctor { fields, .. } => {
                let (Some(ctor), ExprKind::Call { callee, args, .. }) =
                    (self.p.pat_ctor.get(pat), &self.m.exprs[init].kind)
                else {
                    return;
                };
                if !matches!(self.p.res(*callee), Some(Res::Ctor(adt, v)) if adt == ctor.adt && v == ctor.variant) {
                    return;
                }
                // Labels follow the declaration order, so argument `i` is field `i`.
                for (field, idx) in fields.iter().flatten().zip(ctor.fields.iter()) {
                    self.empty_bindings(field.pat, args.get(idx.index()).map(|arg| arg.value), out);
                }
            }
            _ => {}
        }
    }

    /// Whether `local`'s `path`, of type `ty`, holds no resource on every path here: it is
    /// released, or it is a record or tuple whose parts all are. A base resource holds itself,
    /// apart from the `self` of its own `take self` method (OPEN_QUESTIONS Q35).
    fn released_fully(&self, local: LocalId, path: &mut Path, ty: &Ty) -> bool {
        self.released_within(local, path, ty, &mut Vec::new())
    }

    /// [`Walk::released_fully`] inside the record types in `within`. A record type that holds
    /// itself has no values, so it holds no resource. A generic record may hold itself with
    /// other type arguments, as `Outer[Outer[Probe]]` does, which is another type.
    fn released_within(&self, local: LocalId, path: &mut Path, ty: &Ty, within: &mut Vec<Ty>) -> bool {
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
        // A record whose type argument grows has no finite parts, and it has been reported
        // (E0904; §15.1).
        if def.unknown_variants || within.contains(ty) {
            return true;
        }
        within.push(ty.clone());
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
        if self.is_temp(e) && self.holds_resource(e) && !self.gives_unknown(e) && *self.p.ty(e) != Ty::Never {
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

    /// Whether a value of type `ty` that `pat` matches, any when `None`, and that no pattern
    /// of `taken` matches, may hold a resource. It looks through enums, records and tuples
    /// at any depth, so `_` after `Some(Some(p))` meets only values without one (OPEN_QUESTIONS
    /// P5). A pattern of `taken` with two refutable parts takes no part on its own.
    fn rest_holds(&self, ty: &Ty, pat: Option<PatId>, taken: &[PatId]) -> bool {
        if !self.is_resource(ty) || taken.iter().any(|&x| self.irrefutable(x)) {
            return false;
        }
        let pat = pat.filter(|&p| !self.irrefutable(p));
        let Some((id, args)) = self.adt_of(ty) else { return true };
        let def = self.p.decls.adt(id);
        if def.resource_base || def.is_native() {
            return true;
        }
        let variants: Vec<usize> = match pat.map(|p| self.shape_of(p)) {
            Some(None) => return true,
            Some(Some((v, _))) => vec![v],
            None => (0..def.variants.len()).collect(),
        };
        variants.into_iter().any(|v| {
            let types = def.field_types(VariantIdx::new(v), args);
            let parts: Vec<Vec<Option<PatId>>> = taken
                .iter()
                .filter_map(|&x| self.shape_of(x).filter(|(w, _)| *w == v).map(|(_, parts)| parts))
                .collect();
            let refutable = |part: &Option<PatId>| part.is_some_and(|p| !self.irrefutable(p));
            if parts.iter().any(|parts| !parts.iter().any(refutable)) {
                return false;
            }
            let own = pat.and_then(|p| self.shape_of(p)).map(|(_, parts)| parts);
            (0..types.len()).any(|i| {
                let taken_here: Vec<PatId> = parts
                    .iter()
                    .filter(|parts| parts.iter().enumerate().all(|(j, part)| j == i || !refutable(part)))
                    .filter_map(|parts| parts[i])
                    .collect();
                let mine = own.as_ref().and_then(|parts| parts[i]);
                self.rest_holds(&types[i], mine, &taken_here)
            })
        })
    }

    /// The variant a constructor or tuple pattern matches, 0 for a record or tuple, and the
    /// pattern each field must match, `None` for any. `None` for a pattern it can't read.
    fn shape_of(&self, pat: PatId) -> Option<(usize, Vec<Option<PatId>>)> {
        match &self.m.pats[pat].kind {
            PatKind::Tuple(parts) => Some((0, parts.iter().map(|&p| Some(p)).collect())),
            PatKind::Ctor { fields, .. } => {
                let ctor = self.p.pat_ctor.get(pat)?;
                let count = self.p.decls.adt(ctor.adt).variants[ctor.variant.index()].fields.len();
                let mut parts = vec![None; count];
                for (field, idx) in fields.iter().flatten().zip(ctor.fields.iter()) {
                    parts[idx.index()] = Some(field.pat);
                }
                Some((ctor.variant.index(), parts))
            }
            _ => None,
        }
    }

    /// An `is` test of `value` against `pat`, which moves what it binds whether or not it
    /// matches (OPEN_QUESTIONS P5), so a failed test loses a resource the value may hold.
    fn tested(&mut self, value: ExprId, pat: PatId) {
        let ty = self.p.ty(value).clone();
        if !self.is_resource(&ty) || self.gives_unknown(value) {
            return;
        }
        let temp = self.is_temp(value);
        let mut moved = Vec::new();
        self.bound_paths(pat, &mut Vec::new(), &mut moved);
        let lost_when_matched = self.lost(pat, &ty, temp);
        // The value is gone after a failed test when the test moves it or it is a temporary.
        let lost_when_failed = (temp || !moved.is_empty()) && self.rest_holds(&ty, None, &[pat]);
        if lost_when_matched || lost_when_failed {
            let message = if lost_when_matched {
                "this pattern leaves out a resource of the value it moves, which would drop it (§10)"
            } else {
                "this test moves the value whether or not it matches, so a value it doesn't match, which may hold a resource, would be lost; use `match` (§10)"
            };
            self.report(codes::RESOURCE_DISCARDED, self.m.pats[pat].span, message.to_string());
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

    /// Whether `e` names a place that holds no resource.
    fn released_place(&self, e: ExprId) -> bool {
        self.place(e).is_some_and(|(local, mut path)| {
            let ty = self.ty_at(local, &path);
            self.released_fully(local, &mut path, &ty)
        })
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
        self.used_at(e, local);
        // A rejected capture may have been meant to be consumed (REFERENCE §15.1).
        if self.captured.contains(&local) && self.tainted(e) {
            self.excused.insert(local);
        }
        if let Some(reads) = self.fn_reads.get(&local).cloned() {
            let name = self.describe(e);
            self.reads(e, &reads, |captured| {
                format!("`{name}` captures `{captured}`, which may have moved already, so `{name}` can't be used here (§5.1)")
            });
        }
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
        if self.captured.contains(&local) {
            let message = if resource {
                format!(
                    "`{desc}` is a resource a closure captures, which only borrows it, so it can't be consumed here; pass it to the closure through a `take` parameter instead (§6.7, §10)"
                )
            } else {
                format!(
                    "`{desc}` is captured by a closure, which only borrows it, so it can't move here; pass it to the closure through a `take` parameter instead (§5.2, §6.7)"
                )
            };
            self.report(lent, self.span(e), message);
            self.refused.insert(e);
            // It was meant to move, so it isn't reported as left over (REFERENCE §15.1).
            self.excused.insert(local);
            return;
        }
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
                Lender::Capture => {
                    let message = format!(
                        "`{desc}` is captured by a closure an earlier argument passes to this call, which may read it while the call runs, so it can't also move into it (§5.3)"
                    );
                    self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
                }
                Lender::Callee => {
                    let message = format!(
                        "`{desc}` is captured by the function value this call calls, which may read it while the call runs, so it can't also move into it (§5.3)"
                    );
                    self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
                }
            }
            // It was meant to move, so it isn't reported as left over (REFERENCE §15.1).
            self.excused.insert(local);
            return;
        }
        if resource && !self.unrefined(local, &path) && self.read_by_refinement(local, &path) {
            let what = "moves of a resource out of a field that its record's refinement reads, which may run again,";
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
        self.used_at(e, local);
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

    /// Reports the first of `reads`, the locals a closure reads, that may have moved, at
    /// `e`, with the message `moved` gives for its name.
    fn reads(&mut self, e: ExprId, reads: &[Read], moved: impl Fn(&str) -> String) {
        for (local, name) in reads {
            self.touch(*local);
            if self.state.as_ref().is_some_and(|state| state.of(*local).next().is_some()) {
                self.report(codes::USE_AFTER_MOVE, self.span(e), moved(name));
                return;
            }
        }
    }

    /// What a call of the function value `e` gives reads: the locals its closure captures,
    /// and what a function value it captures reads, at any depth.
    fn fn_reads(&mut self, e: ExprId) -> Reads {
        let direct = self.direct_reads(e);
        self.expand(direct)
    }

    /// `reads`, with each local listed in [`Walk::fn_reads`] replaced by what it reads, each
    /// local once. Those lists are expanded already, so a chain of closures doesn't expand
    /// again at each link. Each list still holds what the links before it read, so a chain
    /// of n closures that each capture a local of their own costs time in n squared.
    fn expand(&mut self, reads: Reads) -> Reads {
        if self.listed.len() < self.locals.len() {
            self.listed.resize(self.locals.len(), 0);
        }
        self.expands += 1;
        let mut out = Vec::new();
        for (local, name) in reads {
            let held = self.fn_reads.get(&local).cloned();
            let parts = match &held {
                Some(held) if self.locals[local.index()].mutable => {
                    std::iter::once((local, name)).chain(held.iter().cloned()).collect()
                }
                Some(held) => held.to_vec(),
                None => vec![(local, name)],
            };
            for (local, name) in parts {
                if std::mem::replace(&mut self.listed[local.index()], self.expands) != self.expands {
                    out.push((local, name));
                }
            }
        }
        out
    }

    /// The locals the function value `e`, or the function values a value `e` holds, read
    /// directly: those its closures capture, or the locals that hold them. [`Walk::expand`]
    /// follows them.
    fn direct_reads(&self, e: ExprId) -> Reads {
        let tail = |block: &Block| match block.stmts.last().map(|&s| &self.m.stmts[s].kind) {
            Some(StmtKind::Expr(e)) => self.direct_reads(*e),
            _ => Vec::new(),
        };
        let of = |e: ExprId| if self.holds_fn(e) { self.direct_reads(e) } else { Vec::new() };
        let compound = matches!(
            self.m.exprs[e].kind,
            ExprKind::Field { .. }
                | ExprKind::Index { .. }
                | ExprKind::Call { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::Tuple(_)
                | ExprKind::List(_)
                | ExprKind::Map(_)
        );
        if compound && !self.holds_fn(e) {
            return Vec::new();
        }
        match &self.m.exprs[e].kind {
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => of(*base),
            ExprKind::Call { callee, args, .. } => {
                std::iter::once(*callee).chain(args.iter().map(|arg| arg.value)).flat_map(of).collect()
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                std::iter::once(*receiver).chain(args.iter().map(|arg| arg.value)).flat_map(of).collect()
            }
            ExprKind::Tuple(values) | ExprKind::List(values) => values.iter().flat_map(|&v| of(v)).collect(),
            ExprKind::Map(entries) => entries.iter().flat_map(|&(k, v)| of(k).into_iter().chain(of(v))).collect(),
            ExprKind::Try(inner) | ExprKind::Attempt(inner) => self.direct_reads(*inner),
            ExprKind::Closure(_) => self.p.closures.get(e).map_or_else(Vec::new, |info| {
                info.captures.iter().map(|(local, name)| (*local, Arc::from(&**name))).collect()
            }),
            ExprKind::Name(_) => match self.p.res(e) {
                Some(Res::Local(local)) if self.fn_reads.contains_key(&local) => {
                    vec![(local, self.describe(e).into())]
                }
                _ => Vec::new(),
            },
            ExprKind::If { then_block, else_branch, .. } => {
                let mut out = tail(then_block);
                match else_branch {
                    Some(ElseBranch::Block(block)) => out.extend(tail(block)),
                    Some(ElseBranch::If(nested)) => out.extend(self.direct_reads(*nested)),
                    None => {}
                }
                out
            }
            ExprKind::Match { arms, .. } => arms.iter().flat_map(|arm| tail(&arm.body)).collect(),
            ExprKind::Else { value, fallback } => {
                let mut out = self.direct_reads(*value);
                match fallback {
                    Fallback::Value(value) => out.extend(self.direct_reads(*value)),
                    Fallback::Block(block) => out.extend(tail(block)),
                }
                out
            }
            _ => Vec::new(),
        }
    }

    /// A closure, which reads what it captures where it is made. Its body is walked as a
    /// function's of its own, which borrows what it captures and owns its `take` parameters
    /// of a resource type.
    fn closure(&mut self, e: ExprId, closure: &Closure) {
        let Some(info) = self.p.closures.get(e) else { return };
        let captures: Vec<(LocalId, Box<str>)> = info.captures.clone();
        let kept = info.kept;
        for (local, name) in &captures {
            self.var_names.entry(*local).or_insert_with(|| Arc::from(&**name));
        }
        let reads = self.fn_reads(e);
        self.reads(e, &reads, |captured| {
            format!("`{captured}` may have moved already, so this closure can't capture it (§5.1)")
        });
        let params: Vec<(LocalId, Span, String)> = (info.owned.iter())
            .map(|(local, span)| {
                let i = info.params.iter().position(|p| p == local).expect("an owned parameter is a parameter");
                (*local, *span, self.m.text(closure.params[i].name.sym).to_string())
            })
            .collect();
        // A kept closure copies what it captures, which must be free (REFERENCE §6.7).
        if info.kept {
            for ((local, _), &span) in captures.iter().zip(&info.spans) {
                let ty = &self.locals[local.index()].ty;
                if self.origins[local.index()].is_none() || !self.tracked(ty) {
                    continue;
                }
                let (code, message) = if self.p.decls.holds_fn(ty) {
                    let message = "a closure passed to a `keep fn` parameter lives indefinitely, so it can't capture a function value, or a value that holds one, unless that is kept too (§6.7)";
                    (codes::FUNCTION_VALUE_ESCAPES, message)
                } else {
                    let message = "a closure passed to a `keep fn` parameter lives indefinitely, so it can't capture a borrowed capability or a value that holds or comes from one; take it as `keep` (§6.7, §9.3)";
                    (codes::BORROWED_RETAINED, message)
                };
                self.report(code, span, message.to_string());
            }
        }
        for (&local, &mode) in info.params.iter().zip(&info.modes) {
            self.param(local, mode, closure_call(info.base), None);
            self.declared[local.index()] = self.span(e).lo;
        }
        let frame = self.frame.replace(2 * info.base + 1);
        let fails = self.p.ty(e).fn_parts().map(|(_, _, fails, _)| fails.clone()).filter(|ty| *ty != Ty::Never);
        let fails = std::mem::replace(&mut self.fails, fails);
        let outer = (
            self.state.replace(State::default()),
            std::mem::take(&mut self.loops),
            std::mem::take(&mut self.lent),
            std::mem::replace(&mut self.scopes, vec![params]),
            std::mem::take(&mut self.pending),
            std::mem::take(&mut self.guarded),
            std::mem::take(&mut self.handled),
            std::mem::take(&mut self.touched),
            self.reach,
        );
        let depth = self.captured.len();
        self.captured.extend(captures.iter().map(|(local, _)| *local));
        // A default closure sees what its captures may hold when it runs. A kept one copies
        // them as they are now.
        let mut raised = Vec::new();
        let stored = self.stores.len();
        if !kept {
            self.closure_exprs.push(e);
            for (local, _) in &captures {
                let (before, seen) = (self.origins[local.index()], self.view[local.index()]);
                let saw = before.max(seen);
                self.origins[local.index()] = saw;
                self.seen.push((*local, saw));
                raised.push((*local, before));
            }
        }
        self.value_block(&closure.body, true);
        if let Some(&s) = closure.body.stmts.last()
            && let StmtKind::Expr(tail) = self.m.stmts[s].kind
        {
            self.escapes(tail, self.frame, "be the closure's result");
        }
        // Past the closure, a capture has what it had, and what the body stored into it.
        for (local, before) in raised {
            let stores = self.stores[stored..].iter().filter(|(l, _)| *l == local).map(|(_, origin)| *origin);
            self.origins[local.index()] = stores.fold(before, Ord::max);
        }
        if depth == 0 {
            self.stores.clear();
        }
        self.frame = frame;
        self.fails = fails;
        self.close_scope("the end of the closure");
        self.captured.truncate(depth);
        let touched;
        (
            self.state,
            self.loops,
            self.lent,
            self.scopes,
            self.pending,
            self.guarded,
            self.handled,
            touched,
            self.reach,
        ) = outer;
        self.touched = touched;
    }

    /// Notes that a call reads `reads`, what the function value `e` captures, for as long as
    /// it runs, where `e` is the call's callee or an argument. So a later argument, or a call
    /// inside one, can't change what it reads, and can't move a captured unique value.
    fn note_reads(&mut self, accesses: &mut Vec<CallAccess>, e: ExprId, reads: Reads, by: Lender) {
        for (local, name) in reads {
            let ty = self.locals[local.index()].ty.clone();
            let access = if self.moves(&ty) { Access::Lent } else { Access::Read };
            let access = CallAccess { access, local, steps: Vec::new(), expr: e, by, captured: Some(name) };
            self.lent.push(access.clone());
            accesses.push(access);
        }
    }

    // ---- origins ----

    /// Gives parameter `local`, taken in `mode`, its origin: free for `keep` and `take`,
    /// `inout` for an `inout` one, and `bounded` for a borrowed one. A store into an `inout`
    /// one may take at most `inout`.
    fn param(&mut self, local: LocalId, mode: ParamMode, bounded: Origin, inout: Origin) {
        let origin = match mode {
            ParamMode::Keep | ParamMode::Take => None,
            ParamMode::Inout | ParamMode::InoutPartial => {
                self.inout_limits.insert(local, inout);
                if inout.is_none() { bounded } else { inout }
            }
            ParamMode::Borrow => bounded,
        };
        self.origins[local.index()] = origin;
    }

    /// Notes that `local` may hold a value of `origin`.
    fn grow(&mut self, local: LocalId, origin: Origin) {
        if !self.captured.is_empty() && origin.is_some() {
            self.stores.push((local, origin));
        }
        let slot = &mut self.origins[local.index()];
        if origin > *slot {
            *slot = origin;
            self.grown += 1;
        }
    }

    /// Whether a value of `ty` has an origin: it reaches a capability or a type parameter
    /// without `Copy`, whose type argument may be either, or can hold a function value.
    fn tracked(&self, ty: &Ty) -> bool {
        !self.p.decls.reach(ty, self.bounds).is_empty() || self.p.decls.holds_fn(ty)
    }

    /// The origin of the value `e` gives, when its type is tracked.
    fn tracked_origin(&self, e: ExprId) -> Origin {
        let origin = self.origin(e);
        if origin.is_some() && self.is_value(e) && self.tracked(self.p.ty(e)) { origin } else { None }
    }

    /// The origin of the value `e` gives. A field or element has its base's, and a call or
    /// construction the shortest of what it is given, as does a collection of its elements.
    fn origin(&self, e: ExprId) -> Origin {
        if self.escaped.contains(&e) {
            return None;
        }
        let m = self.m;
        let tail = |block: &Block| match block.stmts.last().map(|&s| &m.stmts[s].kind) {
            Some(StmtKind::Expr(e)) => self.origin(*e),
            _ => None,
        };
        match &m.exprs[e].kind {
            ExprKind::Name(_) | ExprKind::It => match self.p.res(e) {
                Some(Res::Local(local)) => {
                    if let Some(read) = self.reading.borrow_mut().as_mut() {
                        read.push(local);
                    }
                    self.origins[local.index()]
                }
                _ => None,
            },
            ExprKind::Field { base, .. } => match self.p.res(e) {
                Some(Res::Ctor(..)) => None,
                _ => self.origin(*base),
            },
            ExprKind::Index { base, .. } => self.origin(*base),
            ExprKind::Closure(_) => self.closure_origin(e),
            ExprKind::Call { callee, args, .. } => {
                let callee = if self.is_value(*callee) { self.tracked_origin(*callee) } else { None };
                let callee = callee.filter(|_| !of_param(callee));
                self.given_back(e, args).fold(callee, Ord::max)
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                let lent = matches!(self.p.res(e), Some(Res::Fn(_) | Res::Dispatch { qualified: false, .. }))
                    && self.receiver_mode(e) == ParamMode::Borrow
                    && (!self.holds_fn(*receiver) || of_param(self.tracked_origin(*receiver)));
                let receiver = if self.is_value(*receiver) && !lent { self.tracked_origin(*receiver) } else { None };
                self.given_back(e, args).fold(receiver, Ord::max)
            }
            ExprKind::Tuple(values) | ExprKind::List(values) => {
                values.iter().map(|&value| self.tracked_origin(value)).max().flatten()
            }
            ExprKind::Map(entries) => {
                entries.iter().map(|&(k, v)| self.tracked_origin(k).max(self.tracked_origin(v))).max().flatten()
            }
            ExprKind::If { then_block, else_branch, .. } => {
                let other = match else_branch {
                    Some(ElseBranch::Block(block)) => tail(block),
                    Some(ElseBranch::If(nested)) => self.origin(*nested),
                    None => None,
                };
                tail(then_block).max(other)
            }
            ExprKind::Match { arms, .. } => arms.iter().map(|arm| tail(&arm.body)).max().flatten(),
            ExprKind::Else { value, fallback } => {
                let fallback = match fallback {
                    Fallback::Value(value) => self.origin(*value),
                    Fallback::Block(block) => tail(block),
                };
                self.origin(*value).max(fallback)
            }
            ExprKind::Try(inner) => self.origin(*inner),
            ExprKind::Attempt(inner) => self.origin(*inner).max(self.error_origin(*inner)),
            _ => None,
        }
    }

    /// The origin of the error a call in the postfix chain `e` may fail with: the shortest of
    /// what each call in it that can fail gives back, as its result would (REFERENCE §6).
    fn error_origin(&self, e: ExprId) -> Origin {
        let mut origin = None;
        let mut next = Some(e);
        while let Some(e) = next {
            next = match &self.m.exprs[e].kind {
                ExprKind::Call { callee, .. } => {
                    if self.can_fail(e) {
                        origin = origin.max(self.origin(e));
                    }
                    Some(*callee)
                }
                ExprKind::MethodCall { receiver, .. } => {
                    if self.can_fail(e) {
                        origin = origin.max(self.origin(e));
                    }
                    Some(*receiver)
                }
                ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => Some(*base),
                _ => None,
            };
        }
        origin
    }

    /// Whether call `e` may fail. A builtin may.
    fn can_fail(&self, e: ExprId) -> bool {
        let fails = |ty: Option<&Ty>| ty.is_some_and(|ty| *ty != Ty::Never);
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (ExprKind::MethodCall { .. }, Some(Res::Fn(f))) => fails(self.p.fns[f].fails.as_ref()),
            (ExprKind::MethodCall { .. }, Some(Res::Dispatch { iface, method, .. })) => {
                fails(self.p.decls.iface(iface).methods[method].fails.as_ref())
            }
            (ExprKind::Call { callee, .. }, _) => match self.p.res(*callee) {
                Some(Res::Ctor(..)) => false,
                _ => self.p.ty(*callee).fn_parts().is_none_or(|(_, _, fails, _)| *fails != Ty::Never),
            },
            _ => true,
        }
    }

    /// The origins of the arguments of call `e` that its result may hold: all of them for a
    /// builtin, and otherwise those its callee doesn't borrow, since a checked body can't
    /// give back a borrowed parameter. It can give back what a call of one gives, so a
    /// borrowed argument that can hold a function value counts too, unless it is a parameter
    /// of the frame being walked, whose caller bounds it in turn (`of_param`).
    fn given_back<'a>(&'a self, e: ExprId, args: &'a [Arg]) -> impl Iterator<Item = Origin> + 'a {
        let modes = self.arg_modes(e);
        args.iter().enumerate().filter_map(move |(i, arg)| {
            let origin = self.tracked_origin(arg.value);
            let given = modes.get(i).is_none_or(|mode| *mode != ParamMode::Borrow);
            (given || (self.holds_fn(arg.value) && !of_param(origin))).then_some(origin)
        })
    }

    /// The mode in which method call `e` takes its receiver.
    fn receiver_mode(&self, e: ExprId) -> ParamMode {
        match self.p.res(e) {
            Some(Res::Fn(f)) if self.p.fns[f].receiver.is_some() => self.p.fns[f].self_mode,
            Some(Res::Method(builtin)) if builtin.changes_receiver() => ParamMode::Inout,
            Some(Res::Dispatch { iface, method, qualified: false }) => {
                self.p.decls.iface(iface).methods[method].self_mode
            }
            _ => ParamMode::Borrow,
        }
    }

    /// A closure lives as long as the shortest lived local it captures by reference. A kept
    /// one copies what it captures, which must be free, so it is free.
    fn closure_origin(&self, e: ExprId) -> Origin {
        let info = self.p.closures.get(e)?;
        if info.kept {
            return None;
        }
        if let Some(read) = self.reading.borrow_mut().as_mut() {
            read.extend(info.captures.iter().map(|(local, _)| *local));
        }
        info.captures.iter().map(|(local, _)| alive(*local).max(self.origins[local.index()])).max().flatten()
    }

    /// Reports `e` when its origin is longer than `limit` allows, where it would `how`.
    fn escapes(&mut self, e: ExprId, limit: Origin, how: &str) {
        if self.tainted(e) || self.refused.contains(&e) {
            return;
        }
        let origin = self.tracked_origin(e);
        let holds_fn = self.p.decls.holds_fn(self.p.ty(e));
        self.escape(e, origin, holds_fn, limit, how);
    }

    /// Reports `e`, a value of `origin` whose type can hold a function value when `holds_fn`,
    /// when `limit` doesn't allow that origin.
    fn escape(&mut self, e: ExprId, origin: Origin, holds_fn: bool, limit: Origin, how: &str) {
        if origin <= limit || self.escaped.contains(&e) {
            return;
        }
        self.escaped.insert(e);
        let (code, message) = if holds_fn {
            let message = format!(
                "this is a function value, or holds one, that may capture a local or a borrowed value that ends before it would, so it can't {how} (§6.7, Q34)"
            );
            (codes::FUNCTION_VALUE_ESCAPES, message)
        } else {
            let message = format!(
                "this is borrowed, or holds or comes from a borrowed value, so it can't {how}; a `keep` parameter can be retained (§9.3)"
            );
            (codes::BORROWED_RETAINED, message)
        };
        self.report(code, self.span(e), message);
    }

    /// The longest origin a value stored into `local` may take: one that outlives it, or for
    /// an `inout` parameter, one that outlives the call.
    fn store_limit(&self, local: LocalId) -> Origin {
        self.inout_limits.get(&local).copied().unwrap_or(Some(2 * local.0 + 2))
    }

    /// Stores the value `e` gives into a place of `local`, written `name`.
    fn store(&mut self, e: ExprId, local: LocalId, name: &str) {
        self.escapes(e, self.store_limit(local), "be stored in a place that outlives it");
        let origin = self.tracked_origin(e);
        self.grow(local, origin);
        if self.holds_fn(e) {
            let reads = self.fn_reads(e);
            self.add_reads(local, reads);
            let changes = self.changes_of(e);
            self.hold_vars(local, &changes, self.span(e).hi, name.to_string());
        }
    }

    /// The modes of the arguments of call `e`, after its receiver: those its callee takes,
    /// and for a builtin that changes its receiver, `take` for each.
    fn arg_modes(&self, e: ExprId) -> Vec<ParamMode> {
        let iface = |iface: IfaceId, method: usize| self.p.decls.iface(iface).methods[method].modes.clone();
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (_, Some(Res::Dispatch { iface: id, method, qualified: true })) => {
                std::iter::once(self.p.decls.iface(id).methods[method].self_mode).chain(iface(id, method)).collect()
            }
            (ExprKind::MethodCall { .. }, Some(Res::Fn(f))) => self.p.fns[f].params.iter().map(|p| p.mode).collect(),
            (ExprKind::MethodCall { args, .. }, Some(Res::Method(builtin))) if builtin.changes_receiver() => {
                vec![ParamMode::Take; args.len()]
            }
            (ExprKind::MethodCall { .. }, Some(Res::Dispatch { iface: id, method, .. })) => iface(id, method),
            (ExprKind::Call { callee, args, .. }, _) => match self.p.res(*callee) {
                Some(Res::Fn(f)) => self.p.fns[f].params.iter().map(|p| p.mode).collect(),
                Some(Res::Ctor(..)) => vec![ParamMode::Take; args.len()],
                _ => self
                    .p
                    .expr_ty
                    .get(*callee)
                    .and_then(Ty::fn_parts)
                    .map_or_else(Vec::new, |(modes, ..)| modes.to_vec()),
            },
            _ => Vec::new(),
        }
    }

    /// Checks what call `e` may retain: a `keep` argument or `keep self` receiver must be
    /// free, and what it may store into its `inout` arguments and `inout self` receiver,
    /// what it owns or keeps and what they already hold, must outlive them.
    fn retains(&mut self, e: ExprId, receiver: Option<(ExprId, ParamMode)>, args: &[Arg]) {
        let modes = self.arg_modes(e);
        let mut given: Vec<(ExprId, ParamMode)> = receiver.into_iter().collect();
        given.extend(args.iter().enumerate().map(|(i, arg)| {
            let mode = modes.get(i).copied().unwrap_or(ParamMode::Borrow);
            (arg.value, if arg.inout { ParamMode::Inout } else { mode })
        }));
        if given.iter().all(|&(value, _)| {
            (self.tracked_origin(value).is_none() && !self.holds_fn(value)) || self.rejected.contains(&value)
        }) {
            return;
        }
        let first_arg = usize::from(receiver.is_some());
        for (i, &(value, mode)) in given.iter().enumerate() {
            if mode == ParamMode::Keep {
                let how = if i < first_arg {
                    "be the receiver of a `keep self` method"
                } else {
                    "be passed to a `keep` parameter"
                };
                self.escapes(value, None, how);
            }
        }
        let inout = |mode: ParamMode| matches!(mode, ParamMode::Inout | ParamMode::InoutPartial);
        let targets: Vec<(ExprId, LocalId)> = given
            .iter()
            .filter(|&&(value, mode)| inout(mode) && !self.rejected.contains(&value) && self.tracked(self.p.ty(value)))
            .filter_map(|&(value, _)| Some((value, self.root_local(value)?)))
            .collect();
        for &(source, mode) in &given {
            if !(inout(mode) || matches!(mode, ParamMode::Take | ParamMode::Keep)) {
                continue;
            }
            for &(target, local) in &targets {
                if target != source {
                    let name = self.describe(target);
                    self.store(source, local, &name);
                }
            }
        }
    }

    // ---- changed captures ----

    /// Whether the value `e` gives can hold a function value.
    fn holds_fn(&self, e: ExprId) -> bool {
        self.is_value(e) && self.p.decls.holds_fn(self.p.ty(e))
    }

    /// The `var`s that the closures the value `e` gives may change, as it derives them as
    /// [`Walk::origin`] does. A closure changes what it changes itself, and what the closures
    /// it captures do.
    fn changes_of(&self, e: ExprId) -> Vec<LocalId> {
        let m = self.m;
        let mut out = Vec::new();
        let mut add = |vars: &[LocalId]| {
            for var in vars {
                if !out.contains(var) {
                    out.push(*var);
                }
            }
        };
        let of = |e: ExprId| if self.holds_fn(e) { self.changes_of(e) } else { Vec::new() };
        let tail = |block: &Block| match block.stmts.last().map(|&s| &m.stmts[s].kind) {
            Some(StmtKind::Expr(e)) => self.changes_of(*e),
            _ => Vec::new(),
        };
        let held = |local: LocalId| self.holders.get(&local).map_or(&[][..], |(vars, ..)| &vars[..]);
        match &m.exprs[e].kind {
            // A kept closure changes a copy of what it captures (E0305 otherwise).
            ExprKind::Closure(_) => {
                if let Some(info) = self.p.closures.get(e)
                    && !info.kept
                {
                    add(&info.changes);
                    for (local, _) in &info.captures {
                        add(held(*local));
                    }
                }
            }
            ExprKind::Name(_) | ExprKind::It => {
                if let Some(Res::Local(local)) = self.p.res(e) {
                    add(held(local));
                }
            }
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => add(&of(*base)),
            ExprKind::Call { callee, args, .. } => {
                add(&of(*callee));
                for arg in args {
                    add(&of(arg.value));
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                add(&of(*receiver));
                for arg in args {
                    add(&of(arg.value));
                }
            }
            ExprKind::Tuple(values) | ExprKind::List(values) => {
                for &value in values {
                    add(&of(value));
                }
            }
            ExprKind::Map(entries) => {
                for &(k, v) in entries {
                    add(&of(k));
                    add(&of(v));
                }
            }
            ExprKind::If { then_block, else_branch, .. } => {
                add(&tail(then_block));
                match else_branch {
                    Some(ElseBranch::Block(block)) => add(&tail(block)),
                    Some(ElseBranch::If(nested)) => add(&self.changes_of(*nested)),
                    None => {}
                }
            }
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    add(&tail(&arm.body));
                }
            }
            ExprKind::Else { value, fallback } => {
                add(&self.changes_of(*value));
                match fallback {
                    Fallback::Value(value) => add(&self.changes_of(*value)),
                    Fallback::Block(block) => add(&tail(block)),
                }
            }
            ExprKind::Try(inner) | ExprKind::Attempt(inner) => add(&self.changes_of(*inner)),
            _ => {}
        }
        out
    }

    /// Notes that `local`, written `name`, may hold a closure that changes `vars` from `at`
    /// on.
    fn hold_vars(&mut self, local: LocalId, vars: &[LocalId], at: u32, name: String) {
        if vars.is_empty() {
            return;
        }
        // A hold that begins in a loop that doesn't declare its local is there from the
        // loop's start on the next turn.
        let declared = self.declared[local.index()];
        let outside = self.loop_spans.iter().find(|l| !(l.lo <= declared && declared < l.hi));
        let at = outside.map_or(at, |l| l.lo.min(at));
        let (held, from, _) = self.holders.entry(local).or_insert_with(|| (Vec::new(), at, name));
        *from = (*from).min(at);
        for var in vars {
            if !held.contains(var) {
                held.push(*var);
            }
        }
    }

    /// Notes a use of `local` at `e`: where it is used last, and a use of a `var`, directly
    /// or through a closure that reads it.
    fn used_at(&mut self, e: ExprId, local: LocalId) {
        let span = self.span(e);
        if self.holds_fn[local.index()] {
            let declared = self.declared[local.index()];
            let outside = self.loop_spans.iter().find(|l| !(l.lo <= declared && declared < l.hi));
            let end = outside.map_or(span.hi, |l| l.hi.max(span.hi));
            let last = &mut self.last_use[local.index()];
            *last = (*last).max(end);
        }
        if self.locals[local.index()].mutable {
            let name: Arc<str> = self.describe(e).into();
            self.var_uses.entry(local).or_default().insert((span.lo, None), (span, name));
        }
        if let Some(reads) = self.fn_reads.get(&local).cloned() {
            for (var, name) in reads.iter() {
                if self.locals[var.index()].mutable {
                    self.var_uses.entry(*var).or_default().insert((span.lo, Some(local)), (span, name.clone()));
                }
            }
        }
    }

    /// Reports each use of a `var` while a local holds a closure that changes it, other than
    /// through that local (OPEN_QUESTIONS Q34).
    fn held_vars(&mut self) {
        let mut found = Vec::new();
        for (&holder, (vars, from, name)) in &self.holders {
            let until = self.last_use[holder.index()];
            let uses = vars.iter().flat_map(|var| {
                self.var_uses
                    .get(var)
                    .into_iter()
                    .flatten()
                    .map(move |((_, through), (span, name))| (var, span, name, through))
            });
            for (var, span, var_name, through) in uses {
                // A use through a closure that holds the `var` too, as one that calls this
                // holder does, was checked where that closure captured it.
                let held_through = through.is_some_and(|other| {
                    other == holder || self.holders.get(&other).is_some_and(|(vars, ..)| vars.contains(var))
                });
                let clashed = self.clashed.contains(&(*var, span.lo));
                if vars.contains(var) && !held_through && !clashed && *from < span.lo && span.lo <= until {
                    let message = format!(
                        "`{name}` holds a closure that changes `{var_name}` until `{name}` is last used, so nothing else may use `{var_name}` meanwhile (§5.3, Q34)"
                    );
                    found.push((*span, message));
                }
            }
        }
        found.sort_by(|(a, x), (b, y)| (a.lo, x).cmp(&(b.lo, y)));
        for (span, message) in found {
            self.report(codes::OVERLAPPING_ACCESS, span, message);
        }
    }

    /// The local the place `e` is a part of.
    fn root_local(&self, e: ExprId) -> Option<LocalId> {
        match self.m.exprs[e].kind {
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => self.root_local(base),
            ExprKind::Name(_) | ExprKind::It => match self.p.res(e) {
                Some(Res::Local(local)) => Some(local),
                _ => None,
            },
            _ => None,
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
                // A place known to hold no resource, as a `let` bound to `Spare(probe: None)`
                // is, loses none (issue #46).
                let empty = self.released_place(*init);
                self.expr(*init);
                let ty = self.p.ty(*init).clone();
                let gone = self.is_temp(*init) || self.consumed.contains(init);
                if self.holds_resource(*init) && !empty && !self.gives_unknown(*init) && self.lost(*pat, &ty, gone) {
                    let message = "this pattern leaves out a resource of the value it takes, which would drop it (§10)";
                    self.report(codes::RESOURCE_DISCARDED, m.pats[*pat].span, message.to_string());
                }
                self.matched(*init, *pat);
                // A value that holds no resource, such as `None`, has nothing to consume.
                let mut empty = Vec::new();
                if self.refused.contains(init) || self.gives_unknown(*init) || !self.holds_resource(*init) {
                    self.pattern_locals(*pat, &mut empty);
                    // A `var` may get a resource in place later, so it is released only when
                    // the part it binds is a variant (OPEN_QUESTIONS P5).
                    let tainted = self.refused.contains(init) || self.gives_unknown(*init);
                    empty.retain(|l| tainted || !self.locals[l.index()].mutable);
                }
                self.empty_bindings(*pat, Some(*init), &mut empty);
                if let Some(state) = &mut self.state {
                    for local in empty {
                        state.release(local, Vec::new());
                    }
                }
            }
            StmtKind::Assign { target, op, value } => {
                self.expr(*value);
                if self.place(*target).is_some() {
                    self.change_lent(*target, self.lent.len());
                }
                // A place that may still hold a resource can't be assigned over (§10 rule 5).
                if self.is_resource(self.p.ty(*target)) && !self.tainted(*target) && !self.gives_unknown(*value) {
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
                if *op == AssignOp::Set
                    && let Some(local) = self.root_local(*target)
                {
                    let name = self.describe(*target);
                    self.store(*value, local, &name);
                }
                match self.place(*target) {
                    Some((local, path)) if *op == AssignOp::Set => {
                        self.assign_place(*target, local, &path);
                        if !self.may_hold_later(*value)
                            && let Some(state) = &mut self.state
                        {
                            state.release(local, path);
                        } else if let Some(state) = &mut self.state {
                            // A record released while empty holds what its part now does.
                            state.unrelease(local, |p| is_prefix(p, &path));
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
            StmtKind::Expect { value, expect } => {
                self.expr(*value);
                let expected = match expect {
                    Some(Expectation::Equals(other)) => Some(*other),
                    _ => None,
                };
                if let Some(other) = expected {
                    self.expr(other);
                }
                // What it compares, or the call whose error it matches, it drops (REFERENCE §10).
                if expect.is_some() {
                    for e in std::iter::once(*value).chain(expected) {
                        self.discarded(e, "the `expect` drops once it has compared it");
                    }
                }
            }
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(*value);
                    self.escapes(*value, self.frame, "be returned");
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
        self.change_lent_at(e, local, &steps, upto);
    }

    /// [`Walk::change_lent`] for a change of `local`'s `steps` that `e` makes.
    fn change_lent_at(&mut self, e: ExprId, local: LocalId, steps: &[Step], upto: usize) {
        let found = self.lent[..upto].iter().rev().find_map(|l| {
            let overlap = if l.local == local { overlap(&l.steps, steps) } else { Overlap::No };
            (overlap != Overlap::No).then_some((l.by, l.expr, overlap, l.captured.clone()))
        });
        let Some((by, there, overlap, captured)) = found else { return };
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
            Lender::Capture => format!(
                "`{}` is captured by a closure that one of a call's earlier arguments passes, which may read it until the call returns",
                captured.as_deref().unwrap_or(&there)
            ),
            Lender::Callee => format!(
                "`{}` is captured by the function value a call calls, which may read it until the call returns",
                captured.as_deref().unwrap_or(&there)
            ),
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
        // A block, arm or fallback can't give a value that depends on a local it declares.
        if let Some(&base) = self.p.scope_tails.get(e) {
            let how = "leave the block, arm or fallback that declares a local it depends on, which ends there";
            self.escapes(e, Some(2 * base + 2), how);
        }
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
            | ExprKind::Applied { .. }
            | ExprKind::Unreachable => {}
            ExprKind::Closure(closure) => self.closure(e, closure),
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
            ExprKind::Call { callee, args, .. } => {
                // A function value is read before its arguments, and what it captures is read
                // for as long as the call runs.
                if self.is_value(*callee) {
                    self.expr(*callee);
                }
                self.call(e, None, args);
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.call(e, Some((*receiver, self.receiver_mode(e))), args);
            }
            ExprKind::Field { base, .. } => {
                self.expr(*base);
                // A method value, as in `p.close`, was meant to be called, which may have
                // consumed its receiver, as a rejected call may (REFERENCE §15.1).
                if self.method_values.contains(&e) {
                    self.rejected_receiver(*base);
                } else if !matches!(self.p.res(e), Some(Res::Ctor(..))) {
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
                    self.lent.push(CallAccess {
                        access: Access::Lent,
                        local,
                        steps,
                        expr: *base,
                        by: Lender::Index,
                        captured: None,
                    });
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
            // A `try` fails with the error of the call it marks, which the call's origin bounds.
            ExprKind::Try(inner) => {
                self.expr(*inner);
                if let Some(err) = self.fails.clone()
                    && self.tracked(&err)
                    && !self.tainted(*inner)
                {
                    let origin = self.error_origin(*inner);
                    let holds_fn = self.p.decls.holds_fn(&err);
                    self.escape(e, origin, holds_fn, self.frame, "be the error a function fails with");
                }
            }
            ExprKind::Fail(inner) => {
                self.expr(*inner);
                self.escapes(*inner, self.frame, "be the error a function fails with");
            }
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
                    w.bind_origin(*pat, *iter);
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
                let resource = self.is_resource(&ty) && !self.gives_unknown(*scrutinee);
                let temp = self.is_temp(*scrutinee);
                // A temporary that guards may still fail past is held until an arm takes it.
                if resource && temp {
                    self.held.insert(*scrutinee);
                }
                // The values an arm may still meet: those no earlier arm without a guard
                // matches (OPEN_QUESTIONS P5).
                let mut taken: Vec<PatId> = Vec::new();
                // What may have moved when an arm is tried: what moved before the `match`,
                // and what the guards of the arms before it moved.
                let mut tried = self.state.clone();
                let mut after = None;
                for arm in arms {
                    self.state = tried.clone();
                    self.open_scope();
                    // An arm whose values hold no resource leaves nothing to consume.
                    let empty = !self.rest_holds(&ty, Some(arm.pat), &taken) || !self.may_hold(arm.pat, &ty);
                    if arm.guard.is_none() {
                        taken.push(arm.pat);
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
                        self.bind_origin(arm.pat, *scrutinee);
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
                                captured: None,
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
                    // So is a binding of the whole value that meets only values without one.
                    if empty
                        && matches!(self.m.pats[arm.pat].kind, PatKind::Bind(_))
                        && let Some(&local) = self.p.pat_local.get(arm.pat)
                        && let Some(state) = &mut self.state
                    {
                        state.release(local, Vec::new());
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
                if let Some(&it) = self.p.it_local.get(e)
                    && self.tracked(&self.locals[it.index()].ty)
                {
                    let origin = self.error_origin(*value);
                    self.grow(it, origin);
                }
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
            && last.grown == self.grown
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
        self.loop_origins(e);
        let mut head = match (&entry, self.loop_cache.get(&e)) {
            (Some(_), Some(last)) => join(entry.clone(), Some(last.head.clone())),
            _ => entry.clone(),
        };
        let depth = self.loops.len();
        let outer_reach = std::mem::replace(&mut self.reach, usize::MAX);
        self.touched.push(HashSet::new());
        self.loop_spans.push(self.span(e));
        loop {
            self.state = head.clone();
            let (scopes, pending) = (self.scopes.len(), self.pending.len());
            self.loops.push(LoopFrame { expr: e, breaks: None, continues: None, scopes, pending });
            let grown = self.grown;
            let exit = turn(self);
            let frame = self.loops.pop().expect("the loop's frame was pushed");
            let back = join(self.state.take(), frame.continues);
            let next = join(entry.clone(), back);
            let grew = self.grown != grown
                || match (&head, &next) {
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
                    let grown = self.grown;
                    self.loop_cache.insert(e, LoopWalk { head, exit: exit.clone(), touched: touched.clone(), grown });
                } else {
                    self.loop_cache.remove(&e);
                }
                if let Some(top) = self.touched.last_mut() {
                    top.extend(touched);
                }
                self.reach = self.reach.min(outer_reach);
                self.state = exit;
                self.loop_spans.pop();
                return;
            }
            head = next;
        }
    }

    /// Gives each local that a statement of loop `e`'s body assigns, or binds with a `let`,
    /// the origin those statements give it over any number of turns, so a chain of them
    /// doesn't walk the loop again once per link. A worklist reevaluates a statement when a
    /// local it reads grew. Turns of the walk still grow what this leaves out.
    fn loop_origins(&mut self, e: ExprId) {
        let body = match &self.m.exprs[e].kind {
            ExprKind::While { body, .. } | ExprKind::Loop { body, .. } | ExprKind::For { body, .. } => body,
            _ => return,
        };
        self.settle(&body.stmts);
    }

    /// Gives each local that a statement of a default closure's body assigns, or binds with
    /// a `let`, the origin those statements give it, as [`Walk::loop_origins`] does for a
    /// loop, since a closure may run any number of times once it is made. So a chain of
    /// closures that each store into what the next reads doesn't walk the function again once
    /// per link.
    fn closure_origins(&mut self) {
        let m = self.m;
        let stmts: Vec<StmtId> = self
            .closure_exprs
            .iter()
            .filter_map(|&e| match &m.exprs[e].kind {
                ExprKind::Closure(closure) => Some(closure.body.stmts.iter().copied()),
                _ => None,
            })
            .flatten()
            .collect();
        self.settle(&stmts);
    }

    /// Grows the origins of what `stmts` assign or bind with a `let` until they settle.
    fn settle(&mut self, stmts: &[StmtId]) {
        let mut pairs: Vec<(LocalId, ExprId)> = Vec::new();
        let mut assigned = HashSet::new();
        for &s in stmts {
            match &self.m.stmts[s].kind {
                StmtKind::Assign { target, op: AssignOp::Set, value } => {
                    if let (ExprKind::Name(_), Some(Res::Local(local))) =
                        (&self.m.exprs[*target].kind, self.p.res(*target))
                    {
                        assigned.insert(pairs.len());
                        pairs.push((local, *value));
                    }
                }
                StmtKind::Let { pat, init, .. } => {
                    if let Some(&local) = self.p.pat_local.get(*pat) {
                        pairs.push((local, *init));
                    }
                }
                _ => {}
            }
        }
        if pairs.len() < 2 {
            return;
        }
        let mut readers: HashMap<LocalId, Vec<usize>> = HashMap::new();
        for (i, &(_, value)) in pairs.iter().enumerate() {
            *self.reading.borrow_mut() = Some(Vec::new());
            self.tracked_origin(value);
            for local in self.reading.borrow_mut().take().unwrap_or_default() {
                readers.entry(local).or_default().push(i);
            }
        }
        let mut work: Vec<usize> = (0..pairs.len()).rev().collect();
        while let Some(i) = work.pop() {
            let (target, value) = pairs[i];
            let origin = self.tracked_origin(value);
            // A store the walk rejects gives its target nothing (REFERENCE §15.1).
            if assigned.contains(&i) && origin > self.store_limit(target) {
                continue;
            }
            if origin > self.origins[target.index()] {
                self.grow(target, origin);
                work.extend(readers.get(&target).into_iter().flatten().copied());
            }
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
        self.bind_origin(pat, value);
    }

    /// What `pat` binds comes from the value `value` gives, so it has its origin, and holds
    /// the `var`s its closures change.
    fn bind_origin(&mut self, pat: PatId, value: ExprId) {
        let origin = self.tracked_origin(value);
        let holds_fn = self.holds_fn(value);
        if origin.is_none() && !holds_fn {
            return;
        }
        let changes = if holds_fn { self.changes_of(value) } else { Vec::new() };
        let reads = if holds_fn { self.fn_reads(value) } else { Vec::new() };
        let mut locals = Vec::new();
        self.pattern_locals(pat, &mut locals);
        for local in locals {
            self.grow(local, origin);
            if self.holds_fn[local.index()] {
                self.add_reads(local, reads.clone());
                let name = match &self.m.pats[pat].kind {
                    PatKind::Bind(name) => self.m.text(name.sym).to_string(),
                    _ => "a binding of this pattern".to_string(),
                };
                self.hold_vars(local, &changes, self.span(value).hi, name);
            }
        }
    }

    /// Notes that a call of the function values `local` holds may read `reads` too. A loop
    /// is walked again when the list grows, as when an origin does.
    fn add_reads(&mut self, local: LocalId, reads: Reads) {
        let Some(held) = self.fn_reads.get_mut(&local) else {
            self.fn_reads.insert(local, Arc::new(reads));
            return;
        };
        let known = self.fn_read_sets.entry(local).or_insert_with(|| held.iter().map(|(l, _)| *l).collect());
        let new: Vec<Read> = reads.into_iter().filter(|(l, _)| known.insert(*l)).collect();
        if !new.is_empty() {
            Arc::make_mut(held).extend(new);
            self.grown += 1;
        }
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
        let at = self.m.pats[pat].span.lo;
        for local in locals {
            self.bind(local);
            self.declared[local.index()] = at;
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

    /// Releases the place `value` names, which a rejected call or method value is given and
    /// may have meant to consume, so it isn't reported as left over (REFERENCE §15.1).
    fn rejected_receiver(&mut self, value: ExprId) {
        let Some((local, path)) = self.place(value) else { return };
        // A closure's state ends with it, so what it captures is excused instead.
        if self.captured.contains(&local) {
            self.excused.insert(local);
        }
        if let Some(state) = &mut self.state {
            state.release(local, path);
        }
    }

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
                self.rejected_receiver(value);
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
        let late = matches!(receiver, Some((_, ParamMode::Inout | ParamMode::InoutPartial)));
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
        let mut rollback = Vec::new();
        if let ExprKind::Call { callee, .. } = self.m.exprs[e].kind
            && self.is_value(callee)
        {
            let reads = self.fn_reads(callee);
            self.note_reads(&mut accesses, callee, reads, Lender::Callee);
            if self.holds_fn(callee) {
                rollback = self.changes_of(callee);
            }
        }
        // What a closure argument changes, it changes as an `&` argument does. So do the
        // closures the receiver and the `&` arguments hold.
        let mut changed: Vec<(ExprId, Vec<LocalId>)> = Vec::new();
        // A builtin calls none of them.
        let builtin = matches!(self.p.res(e), Some(Res::Method(_)));
        let held_by = std::iter::once(receiver.map(|(r, _)| r))
            .flatten()
            .chain(args.iter().filter(|a| a.inout).map(|a| a.value))
            .filter(|_| !builtin);
        for value in held_by.collect::<Vec<_>>() {
            if self.holds_fn(value) && !self.rejected.contains(&value) {
                let changes = self.changes_of(value);
                if !changes.is_empty() {
                    changed.push((value, changes));
                }
            }
        }
        if let Some((receiver, _)) = receiver
            && !late
            && !builtin
            && self.holds_fn(receiver)
            && !self.rejected.contains(&receiver)
        {
            let changes = changed.first().filter(|(v, _)| *v == receiver).map(|(_, c)| c.clone()).unwrap_or_default();
            let mut reads = self.fn_reads(receiver);
            reads.retain(|(local, _)| !changes.contains(local));
            self.note_reads(&mut accesses, receiver, reads, Lender::Capture);
        }
        for arg in args {
            if arg.inout {
                self.indices(arg.value);
                // A function value passed with `&` reads its captures for the call too, unless
                // it was rejected, so it accesses nothing (REFERENCE §15.1).
                if !self.rejected.contains(&arg.value)
                    && let Some((local, _)) = self.place(arg.value)
                    && let Some(reads) = self.fn_reads.get(&local).cloned()
                {
                    self.note_reads(&mut accesses, arg.value, reads.to_vec(), Lender::Capture);
                }
                continue;
            }
            self.expr(arg.value);
            let changes = if self.holds_fn(arg.value) { self.changes_of(arg.value) } else { Vec::new() };
            let mut reads = self.fn_reads(arg.value);
            reads.retain(|(local, _)| !changes.contains(local));
            self.note_reads(&mut accesses, arg.value, reads, Lender::Capture);
            if !changes.is_empty() && !self.rejected.contains(&arg.value) {
                changed.push((arg.value, changes));
            }
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
        for (value, vars) in changed {
            for var in vars {
                if !rollback.contains(&var) {
                    rollback.push(var);
                }
                self.note_change(&mut accesses, outer, value, var);
            }
        }
        if !rollback.is_empty() {
            self.rollbacks.insert(e, rollback);
        }
        self.lent.truncate(outer);
        self.retains(e, receiver, args);
    }

    /// Records that the closure `e` gives a call changes `var` while the call runs, as an
    /// `&` argument does, and reports what else the call reaches it by (OPEN_QUESTIONS Q34).
    fn note_change(&mut self, accesses: &mut Vec<CallAccess>, outer: usize, e: ExprId, var: LocalId) {
        self.change_lent_at(e, var, &[], outer);
        let name = self.var_names.get(&var).cloned().unwrap_or_else(|| "a variable".into());
        let clashes: Vec<u32> = accesses
            .iter()
            .filter(|other| other.local == var && other.expr != e)
            .map(|other| self.span(other.expr).lo)
            .collect();
        if !clashes.is_empty() {
            self.clashed.extend(clashes.into_iter().map(|lo| (var, lo)));
            let message = format!(
                "a closure this call takes changes `{name}`, so the call can't also reach `{name}` another way (§5.3, Q34)"
            );
            self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
        }
        let access = CallAccess {
            access: Access::Inout,
            local: var,
            steps: Vec::new(),
            expr: e,
            by: Lender::Capture,
            captured: Some(name),
        };
        accesses.push(access);
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

    /// Notes that the place `e` may get a resource in place, as by `push`, an `&` argument or
    /// an assignment to a part of it, so it, and what holds it, is no longer released.
    fn filled(&mut self, e: ExprId) {
        if !self.is_resource(self.p.ty(e)) {
            return;
        }
        let mut at = e;
        while let ExprKind::Index { base, .. } = self.m.exprs[at].kind {
            at = base;
        }
        let Some((local, path)) = self.place(at) else { return };
        if let Some(state) = &mut self.state {
            state.unrelease(local, |p| is_prefix(p, &path) || is_prefix(&path, p));
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
            self.filled(e);
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
                    (Access::Inout, Access::Inout)
                        | (Access::Inout, Access::Lent | Access::Read)
                        | (Access::Lent | Access::Read, Access::Inout)
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
            let message = if let Some(name) = &other.captured
                && other.by == Lender::Callee
            {
                format!(
                    "`{name}` is captured by the function value this call calls, which may read it while the call runs, so the call can't also change `{here}` (§5.3)"
                )
            } else if let Some(name) = &other.captured {
                format!(
                    "`{name}` is captured by a closure this call takes, which may read it while the call runs, so the call can't also change `{here}` (§5.3)"
                )
            } else if here == there {
                format!("this call reaches `{here}` twice while one of the accesses is `inout` (§5.3)")
            } else {
                format!(
                    "`{here}` overlaps `{there}`, which this call also reaches while one of them is `inout`, so the call would have two accesses to one variable (§5.3)"
                )
            };
            self.report(codes::OVERLAPPING_ACCESS, self.span(e), message);
        }
        let access = CallAccess { access, local, steps, expr: e, by: Lender::Call, captured: None };
        if access.access == Access::Lent {
            self.lent.push(access.clone());
        }
        accesses.push(access);
    }
}
