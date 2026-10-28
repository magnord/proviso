//! A tree-walking interpreter over a checked module.
//!
//! It trusts the checker: every name is resolved and every expression has a type, so a
//! missing side-table entry is an interpreter bug, not a user error. Values that the
//! language treats as copies are shared behind `Arc`, so a later phase can hand them to
//! other task threads unchanged.

mod fs;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::convert::Infallible;
use std::hash::{Hash, Hasher};
use std::io::{BufRead, Write};
use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use proviso_check::decls::{AdtId, Decls, FieldIdx, IfaceId, ImplKey, VariantIdx};
use proviso_check::types::{FloatTy, IntTy, Ty};
use proviso_check::{Builtin, ExampleInfo, FnId, LocalId, Num, Program, Res};
use proviso_syntax::ast::*;
use proviso_syntax::source::{SourceMap, Span};

/// Calls nested deeper than this are a stack-exhaustion defect (REFERENCE §7.3).
pub const MAX_CALL_DEPTH: usize = 10_000;

/// The interpreter thread's stack. Each call can still use a lot of it when its expressions
/// nest deeply, so the interpreter also checks how much is left, and stops with the same
/// defect before it runs out.
const STACK_SIZE: usize = 1 << 30;

/// The stack kept free for the deepest work between two checks.
const STACK_RESERVE: usize = 1 << 20;

/// The steps an example may take, each a call or a turn of a loop (REFERENCE §14;
/// OPEN_QUESTIONS P5).
pub const EXAMPLE_FUEL: u64 = 1_000_000;

/// A runtime value. It describes itself: an integer knows its type and a record knows its
/// declaration, so arithmetic, `show` and `==` need no static types.
#[derive(Clone, Debug)]
pub enum Value {
    /// Every integer type, range-checked against its type after each operation.
    Int(i128, IntTy),
    F64(f64),
    F32(f32),
    Bool(bool),
    Char(char),
    Text(Arc<str>),
    Unit,
    Adt(Adt),
    /// A list. Writes go through `Arc::make_mut`, as a record's do, so a list that nothing
    /// else shares changes in place.
    List(Arc<ListValue>),
    Map(Arc<MapValue>),
    /// `std.pool`'s `Pool[T]`. A pool is unique, so only the interpreter shares one, while a
    /// call may still fail and roll it back, and a write copies it then (REFERENCE §5.5).
    Pool(Arc<PoolValue>),
    Handle(HandleValue),
    Cap(Cap),
    /// A value of a `cap record`, which is a handle to its object (REFERENCE §9.6). The `Arc`
    /// keeps a `Value` as small as it is without one.
    Object(Arc<CapObject>),
    Fn(FnValue),
}

/// A function value: a module function, or a closure (REFERENCE §6.7).
#[derive(Clone, Debug)]
pub enum FnValue {
    Named(FnId),
    Closure(Arc<ClosureValue>),
}

/// A closure, with the values of the locals it captures. It borrows them, so the frame that
/// made it reads them again whenever a local of its holds the closure, and a call sees them as
/// they are then (OPEN_QUESTIONS P5).
#[derive(Debug)]
pub struct ClosureValue {
    expr: ExprId,
    /// The call whose frame made it.
    frame: u64,
    /// The size of that frame. The closure's own locals are slots of the function it is
    /// written in.
    locals: usize,
    env: Vec<(LocalId, Value)>,
    /// The `cap record` whose own `impl` blocks it is written in.
    owner: Option<AdtId>,
}

/// A pool's slots, each empty or holding an element with the generation it was inserted
/// with. A removed element's slot is reused by a later insert, last removed first.
#[derive(Clone, Debug)]
pub struct PoolValue {
    /// Which pool this is, so a handle into another pool reads nothing. A copy that a call's
    /// rollback keeps is the same pool, but `duplicate` makes a new one.
    id: u64,
    slots: Vec<Option<(u64, Value)>>,
    free: Vec<u32>,
    len: usize,
}

impl PoolValue {
    fn new(id: u64) -> PoolValue {
        PoolValue { id, slots: Vec::new(), free: Vec::new(), len: 0 }
    }

    /// The element `handle` reads, or why it reads none.
    fn lookup(&self, handle: &HandleValue) -> Result<&Value, &'static str> {
        if handle.pool != self.id {
            return Err("this handle belongs to another pool");
        }
        match self.slots.get(handle.slot as usize) {
            Some(Some((generation, value))) if *generation == handle.generation => Ok(value),
            _ => Err("this handle's element was removed from the pool"),
        }
    }

    fn insert(&mut self, value: Value, generation: u64) -> HandleValue {
        let slot = match self.free.pop() {
            Some(slot) => {
                self.slots[slot as usize] = Some((generation, value));
                slot
            }
            None => {
                self.slots.push(Some((generation, value)));
                (self.slots.len() - 1) as u32
            }
        };
        self.len += 1;
        HandleValue { pool: self.id, slot, generation }
    }

    /// Puts `value` back in the slot of `handle`, whose element was just removed, under the
    /// same generation, so `handle` reads it again.
    fn restore(&mut self, handle: &HandleValue, value: Value) {
        // Nothing changes the pool while its element is out, so the slot is the last freed.
        if self.free.last() == Some(&handle.slot) {
            self.free.pop();
        } else {
            self.free.retain(|&slot| slot != handle.slot);
        }
        self.slots[handle.slot as usize] = Some((handle.generation, value));
        self.len += 1;
    }

    fn remove(&mut self, handle: &HandleValue) -> Option<Value> {
        self.lookup(handle).ok()?;
        let (_, value) = self.slots[handle.slot as usize].take()?;
        self.free.push(handle.slot);
        self.len -= 1;
        Some(value)
    }

    /// The elements, in slot order.
    fn elements(&self) -> impl Iterator<Item = &Value> {
        self.slots.iter().flatten().map(|(_, value)| value)
    }
}

impl Drop for PoolValue {
    /// Drops what the pool alone holds with a list of its own, as [`Adt`]'s drop does.
    fn drop(&mut self) {
        let mut owned: Vec<Value> = std::mem::take(&mut self.slots).into_iter().flatten().map(|(_, v)| v).collect();
        drop_parts(&mut owned);
    }
}

/// A handle: the pool it was issued by, its slot there, and the generation of the element
/// it was issued for (STD.md).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct HandleValue {
    pool: u64,
    slot: u32,
    generation: u64,
}

/// The elements of a list, first to last.
#[derive(Clone, Debug, Default)]
pub struct ListValue {
    pub items: Vec<Value>,
}

impl Drop for ListValue {
    /// Drops what the list alone holds with a list of its own, as [`Adt`]'s drop does.
    fn drop(&mut self) {
        drop_parts(&mut self.items);
    }
}

/// A map's entries in insertion order (REFERENCE §4.2), with the hash of each key. A removed
/// entry leaves a gap until the gaps outnumber the entries, so removing one costs as little
/// as adding one. Keys are found by hash, then by `==`, which may be a hand-written `eq`.
#[derive(Clone, Debug, Default)]
pub struct MapValue {
    entries: Vec<Option<(u64, Value, Value)>>,
    /// The places in `entries` of the keys with each hash.
    buckets: HashMap<u64, Vec<usize>>,
    len: usize,
}

impl MapValue {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The entries in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.entries.iter().flatten().map(|(_, k, v)| (k, v))
    }

    /// The place of `key`, whose hash is `hash`, where `same` says whether two keys are equal.
    fn find<E>(
        &self,
        key: &Value,
        hash: u64,
        same: &mut dyn FnMut(&Value, &Value) -> Result<bool, E>,
    ) -> Result<Option<usize>, E> {
        for &at in self.buckets.get(&hash).map_or(&[][..], Vec::as_slice) {
            if let Some((_, k, _)) = &self.entries[at]
                && same(k, key)?
            {
                return Ok(Some(at));
            }
        }
        Ok(None)
    }

    /// The places of the keys whose hash is `hash`.
    fn candidates(&self, hash: u64) -> &[usize] {
        self.buckets.get(&hash).map_or(&[], Vec::as_slice)
    }

    fn key_at(&self, at: usize) -> &Value {
        &self.entries[at].as_ref().expect("found entries are present").1
    }

    fn value_at(&self, at: usize) -> &Value {
        &self.entries[at].as_ref().expect("found entries are present").2
    }

    fn insert(&mut self, hash: u64, key: Value, value: Value) {
        self.buckets.entry(hash).or_default().push(self.entries.len());
        self.entries.push(Some((hash, key, value)));
        self.len += 1;
    }

    fn replace(&mut self, at: usize, value: Value) -> Value {
        let entry = self.entries[at].as_mut().expect("found entries are present");
        std::mem::replace(&mut entry.2, value)
    }

    fn remove(&mut self, at: usize) -> Value {
        let (hash, _, value) = self.entries[at].take().expect("found entries are present");
        let bucket = self.buckets.get_mut(&hash).expect("present keys have buckets");
        bucket.retain(|&i| i != at);
        if bucket.is_empty() {
            self.buckets.remove(&hash);
        }
        self.len -= 1;
        if self.entries.len() > 8 && self.entries.len() > 2 * self.len {
            self.compact();
        }
        value
    }

    /// Closes the gaps that removed entries left, keeping the order of the rest.
    fn compact(&mut self) {
        let entries = std::mem::take(&mut self.entries);
        self.buckets.clear();
        for entry in entries.into_iter().flatten() {
            self.buckets.entry(entry.0).or_default().push(self.entries.len());
            self.entries.push(Some(entry));
        }
    }
}

impl Drop for MapValue {
    /// Drops what the map alone holds with a list of its own, as [`Adt`]'s drop does.
    fn drop(&mut self) {
        let mut owned = Vec::new();
        for (_, key, value) in std::mem::take(&mut self.entries).into_iter().flatten() {
            owned.push(key);
            owned.push(value);
        }
        drop_parts(&mut owned);
    }
}

// Phase 6 hands values to task threads.
const _: () = {
    const fn send_sync<T: Send + Sync>() {}
    send_sync::<Value>()
};

/// A record or enum value. Writes go through `Arc::make_mut`, so a shared value is copied one
/// level at the first write (value semantics, REFERENCE §5.1).
#[derive(Clone, Debug)]
pub struct Adt {
    pub def: AdtId,
    pub variant: VariantIdx,
    pub fields: Arc<[Value]>,
}

impl Drop for Adt {
    /// Drops the values this one alone holds with a list of its own rather than recursion, so
    /// a recursive enum as long as memory allows, such as a list of a million nodes, does not
    /// overflow the native stack when it goes away.
    fn drop(&mut self) {
        let mut owned = Vec::new();
        if let Some(fields) = Arc::get_mut(&mut self.fields) {
            take_parts(fields, &mut owned);
        }
        drop_parts(&mut owned);
    }
}

/// Drops `owned` one value at a time, first moving out what each alone holds, so dropping a
/// value never recurses into the values inside it.
fn drop_parts(owned: &mut Vec<Value>) {
    while let Some(mut value) = owned.pop() {
        match &mut value {
            Value::Adt(adt) => {
                if let Some(fields) = Arc::get_mut(&mut adt.fields) {
                    take_parts(fields, owned);
                }
            }
            Value::List(list) => {
                if let Some(list) = Arc::get_mut(list) {
                    owned.append(&mut list.items);
                }
            }
            Value::Map(map) => {
                if let Some(map) = Arc::get_mut(map) {
                    for (_, key, value) in std::mem::take(&mut map.entries).into_iter().flatten() {
                        owned.push(key);
                        owned.push(value);
                    }
                }
            }
            Value::Pool(pool) => {
                if let Some(pool) = Arc::get_mut(pool) {
                    owned.extend(std::mem::take(&mut pool.slots).into_iter().flatten().map(|(_, value)| value));
                }
            }
            Value::Object(object) => {
                if let Some(object) = Arc::get_mut(object) {
                    object.take_parts(owned);
                }
            }
            _ => {}
        }
        // `value` now holds no other record, enum or collection, so dropping it doesn't recurse.
    }
}

/// Moves the records, enums and collections out of `fields` into `owned`.
fn take_parts(fields: &mut [Value], owned: &mut Vec<Value>) {
    for field in fields {
        if let Value::Adt(_) | Value::List(_) | Value::Map(_) | Value::Pool(_) | Value::Object(_) = field {
            owned.push(std::mem::replace(field, Value::Unit));
        }
    }
}

/// A capability the runtime provides. Copies share the underlying state, the one exception to
/// value semantics (REFERENCE §9.6), as copies of a [`Value::Object`] do.
#[derive(Clone, Debug)]
pub enum Cap {
    Stdin,
    Stdout,
    Stderr,
    /// A directory tree, such as `System.fs` (REFERENCE §9.2).
    Dir(Arc<fs::Root>),
    /// One of `System`'s capabilities that has no operations yet, such as its `Clock`
    /// (OPEN_QUESTIONS Q6).
    Inert(IfaceId),
}

/// A value of a `cap record`. Its plain fields are its own, as a record's are, and `with`
/// replaces them. Its `state` is the object's, which every copy shares (REFERENCE §9.6).
#[derive(Clone, Debug)]
pub struct CapObject {
    pub def: AdtId,
    /// The plain fields, with `Unit` at each `state` field.
    pub fields: Arc<[Value]>,
    pub state: Arc<CapState>,
}

impl CapObject {
    /// Moves the records, enums, collections and objects that this handle alone holds, in its
    /// plain fields or, as the last handle to its object, in its `state`, into `owned`.
    fn take_parts(&mut self, owned: &mut Vec<Value>) {
        if let Some(fields) = Arc::get_mut(&mut self.fields) {
            take_parts(fields, owned);
        }
        if let Some(state) = Arc::get_mut(&mut self.state) {
            take_parts(&mut state.0.get_mut().unwrap_or_else(PoisonError::into_inner).values, owned);
        }
    }
}

impl Drop for CapObject {
    /// Drops what the handle holds without recursion, as [`Adt`] does, so a chain of objects
    /// as long as memory allows doesn't overflow the native stack.
    fn drop(&mut self) {
        let mut owned = Vec::new();
        self.take_parts(&mut owned);
        drop_parts(&mut owned);
    }
}

/// The `state` of a capability object, and the calls of its methods in progress.
#[derive(Debug)]
pub struct CapState(Mutex<StateInner>);

#[derive(Debug)]
struct StateInner {
    /// The `state` fields, with `Unit` at each plain field.
    values: Vec<Value>,
    /// Which of them are lent out to a change in place, which nothing may read until it is
    /// done.
    lent: Vec<bool>,
    /// How many calls of the record's methods on this object are in progress.
    running: usize,
}

impl CapState {
    fn new(values: Vec<Value>) -> CapState {
        let lent = vec![false; values.len()];
        CapState(Mutex::new(StateInner { values, lent, running: 0 }))
    }

    /// The interpreter runs on one thread and never panics while it holds the lock, so a
    /// poisoned one is still consistent.
    fn lock(&self) -> MutexGuard<'_, StateInner> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefectKind {
    IntegerOverflow,
    DivisionByZero,
    AssertionFailed,
    TodoReached,
    UnreachableReached,
    StackExhausted,
    RefinementFailed,
    NoArmMatched,
    FuelExhausted,
    IndexOutOfBounds,
    StaleHandle,
    ReentrantCall,
}

impl DefectKind {
    pub fn name(self) -> &'static str {
        match self {
            DefectKind::IntegerOverflow => "integer_overflow",
            DefectKind::DivisionByZero => "division_by_zero",
            DefectKind::AssertionFailed => "assertion_failed",
            DefectKind::TodoReached => "todo_reached",
            DefectKind::UnreachableReached => "unreachable_reached",
            DefectKind::StackExhausted => "stack_exhausted",
            DefectKind::RefinementFailed => "refinement_failed",
            DefectKind::NoArmMatched => "no_arm_matched",
            DefectKind::FuelExhausted => "fuel_exhausted",
            DefectKind::IndexOutOfBounds => "index_out_of_bounds",
            DefectKind::StaleHandle => "stale_handle",
            DefectKind::ReentrantCall => "reentrant_call",
        }
    }
}

/// A bug found at run time (REFERENCE §7.3).
#[derive(Debug)]
pub struct Defect {
    pub kind: DefectKind,
    pub message: String,
    pub span: Span,
    /// The call sites that led here, innermost first.
    pub callers: Vec<Span>,
    /// What the cleanup after it reported, in order: defects in `abandon` and the leaks they
    /// caused (REFERENCE §10; OPEN_QUESTIONS T10).
    pub cleanup: Vec<Report>,
}

/// Drops the cleanup reports with a stack of their own, since a cleanup defect may carry its
/// own to any depth.
impl Drop for Defect {
    fn drop(&mut self) {
        let mut reports = std::mem::take(&mut self.cleanup);
        while let Some(report) = reports.pop() {
            if let Report::Defect(mut defect) = report {
                reports.append(&mut defect.cleanup);
            }
        }
    }
}

/// A report from the cleanup that follows a failure exit.
#[derive(Debug)]
pub enum Report {
    Defect(Defect),
    /// A resource of type `ty` whose `abandon` hit a defect, owned by the binding or the
    /// expression at `span`.
    Leak {
        ty: String,
        span: Span,
    },
}

pub enum Outcome {
    Done,
    /// `main` failed with an error; this is its `show()`.
    Failed(String),
    Defect(Defect),
}

/// How an example or a test came out (REFERENCE §14).
pub enum ExampleOutcome {
    Passed,
    /// It ran, but not as it says: `why` tells how, and `at` is the `expect` of a test that
    /// didn't hold.
    Failed {
        why: String,
        at: Option<Span>,
    },
    Defect(Defect),
}

/// The standard streams a run reads and writes: `System`'s `stdin`, `stdout` and `stderr`.
/// `debug` output goes to `stderr` too.
pub struct Streams<'a> {
    pub stdin: &'a mut (dyn BufRead + Send),
    pub stdout: &'a mut (dyn Write + Send),
    pub stderr: &'a mut (dyn Write + Send),
}

/// Runs `main` on a thread of its own, with `streams` as its standard streams and `System.fs`
/// rooted at `root`. An `Err` is a panic in the interpreter, which is a bug.
pub fn run_main<'a>(
    sources: &'a SourceMap,
    m: &'a Ast,
    p: &'a Program,
    streams: Streams<'a>,
    root: &Path,
) -> std::thread::Result<Outcome> {
    on_interp_thread(sources, m, p, streams, |interp| interp.main(root))
}

/// Runs each example, and each test when `tests` is set, in declaration order, each with
/// [`EXAMPLE_FUEL`]. `report` gets how each came out as soon as it has run, with the output
/// streams, so a result is written next to its `debug` output. `debug` output goes to
/// `stderr`.
pub fn run_examples(
    sources: &SourceMap,
    m: &Ast,
    p: &Program,
    tests: bool,
    stdout: &mut (dyn Write + Send),
    stderr: &mut (dyn Write + Send),
    mut report: impl FnMut(&ExampleInfo, ExampleOutcome, &mut dyn Write, &mut dyn Write) + Send,
) -> std::thread::Result<()> {
    // An example or a test gets no `System`, so it reads no input (REFERENCE §14).
    let streams = Streams { stdin: &mut std::io::empty(), stdout, stderr };
    on_interp_thread(sources, m, p, streams, |interp| {
        let run = |info: &&ExampleInfo| tests || matches!(m.items[info.item].kind, ItemKind::Example(_));
        for info in p.examples.iter().filter(run) {
            let outcome = interp.example(info);
            report(info, outcome, &mut *interp.stdout, &mut *interp.stderr);
        }
    })
}

fn on_interp_thread<'a, R: Send>(
    sources: &'a SourceMap,
    m: &'a Ast,
    p: &'a Program,
    Streams { stdin, stdout, stderr }: Streams<'a>,
    run: impl FnOnce(&mut Interp<'a>) -> R + Send,
) -> std::thread::Result<R> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("proviso-main".to_string())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, || {
                // The stack grows down, so this is close to its top.
                let stack_limit = stack_address().saturating_sub(STACK_SIZE - STACK_RESERVE);
                let mut interp = Interp {
                    sources,
                    m,
                    p,
                    stdin,
                    stdout,
                    stderr,
                    depth: 0,
                    stack_limit,
                    fuel: None,
                    fueled: "example",
                    generations: 0,
                    pools: 0,
                    owned: Vec::new(),
                    acquired: 0,
                    base: 0,
                    frame: 0,
                    frames: 0,
                    handle_call: false,
                    owner: None,
                };
                run(&mut interp)
            })
            .expect("failed to start the interpreter thread")
            .join()
    })
}

/// The address of a local variable, which shows how deep the stack is.
fn stack_address() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

/// Why evaluation left the normal path.
enum Unwind {
    Return(Value),
    Break(ExprId),
    Continue(ExprId),
    Fail(Value),
    /// A call that this `attempt`, `else` form or example marks failed with this error. Only
    /// that one catches it, so a failure from anywhere else, such as a `try` in an argument,
    /// passes it by (REFERENCE §7.2).
    Attempted(ExprId, Value),
    /// An `expect` that didn't hold, which ends its test: why, and where it is (REFERENCE §14).
    Expected(String, Span),
    Defect(Defect),
}

type Flow<T> = Result<T, Unwind>;

/// Whether `e` is an `if`, or a chain of `else if`s, that ends without an `else`.
fn lacks_final_else(m: &Ast, mut e: ExprId) -> bool {
    loop {
        match &m.exprs[e].kind {
            ExprKind::If { else_branch: None, .. } => return true,
            ExprKind::If { else_branch: Some(ElseBranch::If(nested)), .. } => e = *nested,
            _ => return false,
        }
    }
}

fn defect(kind: DefectKind, message: impl Into<String>, span: Span) -> Unwind {
    Unwind::Defect(Defect { kind, message: message.into(), span, callers: Vec::new(), cleanup: Vec::new() })
}

struct Interp<'a> {
    sources: &'a SourceMap,
    m: &'a Ast,
    p: &'a Program,
    stdin: &'a mut (dyn BufRead + Send),
    stdout: &'a mut (dyn Write + Send),
    stderr: &'a mut (dyn Write + Send),
    /// The number of calls in progress.
    depth: usize,
    /// The lowest stack address the interpreter may reach.
    stack_limit: usize,
    /// The steps an example or a test has left, or `None` outside one.
    fuel: Option<u64>,
    /// What the fuel is for, "example" or "test", which a defect names.
    fueled: &'static str,
    /// The last generation a pool's insert took. One counter serves every pool for the whole
    /// run, and a failed call never rolls it back, so no two handles ever share one
    /// (REFERENCE §5.5).
    generations: u64,
    /// The last identity a pool took.
    pools: u64,
    /// The resources the calls in progress own, each with when it was acquired, which a
    /// failure exit abandons newest first (REFERENCE §10). Each call's come after its
    /// caller's. An entry never moves, since a call, literal or loop keeps where its own
    /// begin, so a local given a new value is acquired again in place.
    owned: Vec<(u64, Owned)>,
    /// The last acquisition the run made.
    acquired: u64,
    /// Where the running call's resources begin in `owned`.
    base: usize,
    /// The running call, which the closures its frame makes name.
    frame: u64,
    /// The last call the run made.
    frames: u64,
    /// Whether the next call is of an operation through a capability handle, which may not
    /// re-enter an object whose method is running (REFERENCE §9.6; OPEN_QUESTIONS Q30).
    handle_call: bool,
    /// The `cap record` whose own `impl` blocks the running code is written in. Only there is
    /// a call on a value of the record direct, so that it may re-enter the object.
    owner: Option<AdtId>,
}

/// What a call runs: a module function, or a closure.
#[derive(Clone, Copy)]
enum Callee<'c> {
    Fn(FnId),
    Closure(&'c ClosureValue),
}

/// A function's local slots, indexed by `LocalId`.
type Frame = Vec<Value>;

/// A resource a call owns: in a local, with the span of its binding, or held while its call,
/// literal or consuming loop runs, with the span of the expression that holds it.
enum Owned {
    Local(LocalId, Span),
    Value(Value, Span),
    /// The elements a consuming loop hasn't reached, last first.
    Rest(Vec<Value>, Span),
}

impl Interp<'_> {
    fn main(&mut self, root: &Path) -> Outcome {
        let main = self.p.main.expect("the driver checks that `main` exists");
        let site = self.p.decl(self.m, main).name.span;
        // In the order of `System`'s fields, `fs`, `net`, `clock`, `random`, `env`, `stdin`,
        // `stdout`, `stderr` and `process` (REFERENCE §9.1).
        let fields = Arc::from([
            Value::Cap(Cap::Dir(Arc::new(fs::Root::new(root)))),
            Value::Cap(Cap::Inert(IfaceId::NET)),
            Value::Cap(Cap::Inert(IfaceId::CLOCK)),
            Value::Cap(Cap::Inert(IfaceId::RANDOM)),
            Value::Cap(Cap::Inert(IfaceId::ENV)),
            Value::Cap(Cap::Stdin),
            Value::Cap(Cap::Stdout),
            Value::Cap(Cap::Stderr),
            Value::Cap(Cap::Inert(IfaceId::PROCESS)),
        ]);
        let sys = Value::Adt(Adt { def: AdtId::SYSTEM, variant: VariantIdx::RECORD, fields });
        match self.call(main, vec![sys], site) {
            Ok(_) => Outcome::Done,
            // The error's `show` runs on behalf of `main`, so a defect in it is traced to there.
            Err(Unwind::Fail(error)) => match self.show(&error, site) {
                Ok(text) => Outcome::Failed(text),
                Err(Unwind::Defect(defect)) => Outcome::Defect(defect),
                Err(_) => unreachable!("`show` doesn't fail"),
            },
            Err(Unwind::Defect(mut defect)) => {
                // The last caller is the synthetic call of `main` itself.
                defect.callers.pop();
                Outcome::Defect(defect)
            }
            Err(
                Unwind::Return(_)
                | Unwind::Break(_)
                | Unwind::Continue(_)
                | Unwind::Attempted(..)
                | Unwind::Expected(..),
            ) => {
                unreachable!("returns, jumps, attempted failures and `expect`s do not escape a function")
            }
        }
    }

    /// Stops with a defect when the stack is nearly used up, or when a call would begin past
    /// `MAX_CALL_DEPTH` nested calls. The last call allowed still runs its body (OPEN_QUESTIONS
    /// P5; issue #25).
    fn check_stack(&self, span: Span, call: bool) -> Flow<()> {
        if (call && self.depth >= MAX_CALL_DEPTH) || stack_address() < self.stack_limit {
            let depth = self.depth;
            return Err(defect(
                DefectKind::StackExhausted,
                format!("the call stack is exhausted after {depth} nested calls"),
                span,
            ));
        }
        Ok(())
    }

    /// Runs one example or test and tells how it came out. A test's failed `expect` is a
    /// failure exit, which abandons the resources it holds (REFERENCE §10).
    fn example(&mut self, info: &ExampleInfo) -> ExampleOutcome {
        let mut frame: Frame = vec![Value::Unit; info.locals];
        (self.fuel, self.depth, self.base) = (Some(EXAMPLE_FUEL), 0, 0);
        let result = match &self.m.items[info.item].kind {
            ItemKind::Example(decl) => {
                self.fueled = "example";
                self.expect(decl.call, &decl.expect, &mut frame).map(|why| why.map(|why| (why, None)))
            }
            ItemKind::Test(decl) => {
                self.fueled = "test";
                self.block(&decl.body, &mut frame).map(|_| None)
            }
            _ => unreachable!("examples and tests are items"),
        };
        let outcome = match result {
            Err(unwind) => Err(self.abandon_owned(0, &mut frame, unwind)),
            ok => {
                self.owned.clear();
                ok
            }
        };
        self.fuel = None;
        match outcome {
            Ok(None) => ExampleOutcome::Passed,
            Ok(Some((why, at))) => ExampleOutcome::Failed { why, at },
            Err(Unwind::Expected(why, at)) => ExampleOutcome::Failed { why, at: Some(at) },
            Err(Unwind::Defect(defect)) => ExampleOutcome::Defect(defect),
            Err(_) => unreachable!("an example or a test neither returns nor fails"),
        }
    }

    /// Runs the call of an example or an `expect` and compares the outcome with what it
    /// expects: `None` when they agree, or else what differs. Values are written as `debug`
    /// writes them.
    fn expect(&mut self, call: ExprId, expect: &Expectation, frame: &mut Frame) -> Flow<Option<String>> {
        let decls = &self.p.decls;
        let outcome = match self.expr(call, frame) {
            Ok(value) => Ok(value),
            Err(Unwind::Attempted(handler, error)) if handler == call => Err(error),
            Err(other) => return Err(other),
        };
        Ok(match (expect, outcome) {
            (Expectation::Equals(x), outcome) => {
                let expected = self.expr(*x, frame)?;
                match outcome {
                    Ok(value) if self.equal(&value, &expected, self.m.exprs[*x].span)? => None,
                    Ok(value) => Some(format!(
                        "expected `{}`, found `{}`",
                        debug_repr(&expected, decls),
                        debug_repr(&value, decls)
                    )),
                    Err(error) => Some(format!(
                        "expected `{}`, but it failed with `{}`",
                        debug_repr(&expected, decls),
                        debug_repr(&error, decls)
                    )),
                }
            }
            (Expectation::Fails(pat), outcome) => {
                let text = self.sources.slice(self.m.pats[*pat].span);
                match outcome {
                    Err(error) if self.matches(*pat, &error, frame)? => None,
                    Err(error) => Some(format!(
                        "expected a failure matching `{text}`, but it failed with `{}`",
                        debug_repr(&error, decls)
                    )),
                    Ok(value) => Some(format!(
                        "expected a failure matching `{text}`, but it returned `{}`",
                        debug_repr(&value, decls)
                    )),
                }
            }
        })
    }

    /// Takes one step of an example's fuel, if it runs in one.
    fn step(&mut self, span: Span) -> Flow<()> {
        match &mut self.fuel {
            Some(0) => {
                let message = format!("the {} took more than {EXAMPLE_FUEL} steps", self.fueled);
                Err(defect(DefectKind::FuelExhausted, message, span))
            }
            Some(fuel) => {
                *fuel -= 1;
                Ok(())
            }
            None => Ok(()),
        }
    }

    fn call(&mut self, f: FnId, args: Vec<Value>, site: Span) -> Flow<Value> {
        self.run(Callee::Fn(f), args, site, &[]).0
    }

    /// Calls the function value `f` with arguments that have no `&` places.
    fn call_value(&mut self, f: &FnValue, args: Vec<Value>, site: Span) -> Flow<Value> {
        match f {
            FnValue::Named(f) => self.call(*f, args, site),
            FnValue::Closure(c) => self.run(Callee::Closure(c), args, site, &[]).0,
        }
    }

    /// Calls `callee` and returns its value, with the final values of the arguments `keep`
    /// names, which are its `inout` parameters, however the call ends. A failure exit abandons
    /// the resources the call still owns, newest first (REFERENCE §10). A closure's frame
    /// starts with what it captures, and its arguments go to its parameters' slots.
    fn run(&mut self, callee: Callee, args: Vec<Value>, site: Span, keep: &[usize]) -> (Flow<Value>, Vec<Value>) {
        let p = self.p;
        let handle = std::mem::take(&mut self.handle_call);
        // A method of a `cap record` runs on its object, whose `state` it leaves as it was if
        // it fails (REFERENCE §9.6).
        let object = match (callee, args.first()) {
            (Callee::Fn(f), Some(Value::Object(object))) if p.fns[f].receiver.is_some() => Some((object.clone(), f)),
            _ => None,
        };
        let (body, mut frame, owned, params) = match callee {
            Callee::Fn(f) => {
                let body = p.decl(self.m, f).body.as_ref().expect("functions that run have bodies");
                let mut frame = args;
                frame.resize(p.fns[f].locals, Value::Unit);
                (body, frame, &p.fns[f].owned, None)
            }
            Callee::Closure(c) => {
                let ExprKind::Closure(closure) = &self.m.exprs[c.expr].kind else {
                    unreachable!("closures are closures")
                };
                let info = p.closures.get(c.expr).expect("closures are checked");
                let mut frame = vec![Value::Unit; c.locals];
                for (local, value) in &c.env {
                    frame[local.index()] = value.clone();
                }
                for (local, value) in info.params.iter().zip(args) {
                    frame[local.index()] = value;
                }
                (&closure.body, frame, &info.owned, Some(&info.params))
            }
        };
        let mark = self.owned.len();
        for &(local, span) in owned {
            self.acquire(Owned::Local(local, span));
        }
        let outer = std::mem::replace(&mut self.base, mark);
        self.frames += 1;
        let outer_frame = std::mem::replace(&mut self.frame, self.frames);
        let owner = match callee {
            Callee::Fn(f) => match &p.fns[f].owner {
                Some(Ty::Adt(id, _)) => Some(*id),
                _ => None,
            },
            Callee::Closure(c) => c.owner,
        };
        let caller = std::mem::replace(&mut self.owner, owner);
        // A call that can't start owns its arguments already, so it abandons them and hands
        // its `inout` ones back as any other failure does.
        let mut snapshot = None;
        let begun = self.check_stack(site, true).and_then(|()| self.step(site)).and_then(|()| {
            if let Some((object, f)) = &object {
                let handle = handle || caller != Some(object.def);
                snapshot = Some(self.enter(object, *f, handle, site)?);
            }
            Ok(())
        });
        let started = begun.is_ok();
        let result = match begun {
            Ok(()) => {
                self.depth += 1;
                let result = self.block(body, &mut frame);
                self.depth -= 1;
                result
            }
            Err(unwind) => Err(unwind),
        };
        self.base = outer;
        self.frame = outer_frame;
        self.owner = caller;
        // A closure's body gives its value, as a block does; a function's ends with `return`.
        let result = match result {
            Ok(value) if params.is_some() => Ok(value),
            Ok(_) => Ok(Value::Unit),
            Err(Unwind::Return(value)) => Ok(value),
            Err(unwind) => Err(unwind),
        };
        // The object is done before the call's resources are abandoned, so an `abandon` may
        // call it through a handle.
        if let (Some((object, _)), Some(snapshot)) = (&object, snapshot) {
            let mut state = object.state.lock();
            state.running -= 1;
            // A field lent out to a change that began before this call is `Unit` in both, and
            // goes back when that change ends.
            if result.is_err() {
                state.values = snapshot;
            }
        }
        let result = match result {
            Ok(value) => {
                self.owned.truncate(mark);
                Ok(value)
            }
            Err(unwind) => match self.abandon_owned(mark, &mut frame, unwind) {
                // A defect at `site` itself, before the call began, isn't called from there.
                Unwind::Defect(mut defect) if started => {
                    defect.callers.push(site);
                    Err(Unwind::Defect(defect))
                }
                other => Err(other),
            },
        };
        let slot = |i: usize| params.map_or(i, |params| params[i].index());
        let finals = keep.iter().map(|&i| std::mem::replace(&mut frame[slot(i)], Value::Unit)).collect();
        (result, finals)
    }

    /// Abandons what the call whose resources begin at `mark` still owns, newest first, as
    /// `unwind` leaves it. A defect in an `abandon` is reported and leaks its resource, and the
    /// first one replaces an error that began the exit (REFERENCE §10; OPEN_QUESTIONS T10).
    fn abandon_owned(&mut self, mark: usize, frame: &mut Frame, mut unwind: Unwind) -> Unwind {
        let mut owned = self.owned.split_off(mark);
        owned.sort_by_key(|(acquired, _)| *acquired);
        while let Some((_, entry)) = owned.pop() {
            let (value, span) = match entry {
                Owned::Local(local, span) => (std::mem::replace(&mut frame[local.index()], Value::Unit), span),
                Owned::Value(value, span) => (value, span),
                Owned::Rest(mut rest, span) => {
                    rest.reverse();
                    (Value::List(Arc::new(ListValue { items: rest })), span)
                }
            };
            unwind = self.abandon(value, span, unwind);
        }
        unwind
    }

    /// Abandons the resources in `value`, which the binding or expression at `span` owned:
    /// the base resources it holds, at any depth, last first (REFERENCE §10 rule 4). A base
    /// resource that a field, or a part of one, moved out of abandons the rest of its
    /// resource fields instead, since its `abandon` would read the one that is gone
    /// (OPEN_QUESTIONS P5).
    fn abandon(&mut self, value: Value, span: Span, mut unwind: Unwind) -> Unwind {
        let p = self.p;
        let decls = &p.decls;
        let mut stack = vec![value];
        while let Some(value) = stack.pop() {
            match value {
                Value::Adt(adt) => {
                    let def = decls.adt(adt.def);
                    let partial = def.resource_base && has_hole(decls, &adt, &[]);
                    if def.resource_base && !partial {
                        let f = decls.impl_method(IfaceId::ABANDON, ImplKey::Adt(adt.def), 0);
                        let f = f.expect("the checker found every resource's `abandon`");
                        let ty = adt.def;
                        if let Err(Unwind::Defect(defect)) = self.call(f, vec![Value::Adt(adt)], span) {
                            let leak = Report::Leak { ty: decls.name(ty), span };
                            unwind = match unwind {
                                Unwind::Defect(mut first) => {
                                    first.cleanup.push(Report::Defect(defect));
                                    first.cleanup.push(leak);
                                    Unwind::Defect(first)
                                }
                                _ => {
                                    let mut defect = defect;
                                    defect.cleanup.push(leak);
                                    Unwind::Defect(defect)
                                }
                            };
                        }
                        continue;
                    }
                    // A module's record or enum knows which of its fields hold resources; a
                    // tuple, `Option` or `Result` is walked whole.
                    let fields = &def.variants[adt.variant.index()].fields;
                    for (field, value) in fields.iter().zip(adt.fields.iter()) {
                        if def.params > 0 || decls.is_resource(&field.ty) {
                            stack.push(value.clone());
                        }
                    }
                }
                Value::List(list) => stack.extend(list.items.iter().cloned()),
                Value::Map(map) => {
                    for (key, value) in map.iter() {
                        stack.push(key.clone());
                        stack.push(value.clone());
                    }
                }
                Value::Pool(pool) => stack.extend(pool.elements().cloned()),
                _ => {}
            }
        }
        unwind
    }

    /// Evaluates the receiver, when there is one, and then the arguments of a call, in
    /// order. An `inout self` receiver and an `&` argument are places, whose indices are
    /// evaluated in order, but whose values are read once every other argument is, since
    /// their access begins then (REFERENCE §5.3). Each is copied in, or taken out when the
    /// callee can't fail and so never rolls it back, or keeps partial changes (§5.4). Returns
    /// the values, and the places with the index of the value each gives. The call holds the
    /// resources it is given until it takes them, so the caller drops what this pushes to
    /// [`Interp::owned`] once it has.
    fn args(
        &mut self,
        shape: Shape,
        receiver: Option<ExprId>,
        args: &[Arg],
        frame: &mut Frame,
    ) -> Flow<(Vec<Value>, Vec<Inout>)> {
        let mut values = Vec::with_capacity(args.len() + 1);
        let mut places = Vec::new();
        let Shape { inout_self, can_fail, f, method, value } = shape;
        // An `inout` that keeps partial changes is written back however the call ends.
        let partial = |p: &Program, i: Option<usize>| {
            if let Some((iface, j, self_value, first)) = method {
                // An interface's methods borrow or take `self`, and its parameters may name
                // `Self`, the type of the value that gives it.
                let Some(k) = i.and_then(|i| if first { i.checked_sub(1) } else { Some(i) }) else { return false };
                let def = &p.decls.iface(iface).methods[j];
                let ty = def.params[k].1.subst(std::slice::from_ref(p.ty(self_value)));
                return def.modes[k] == ParamMode::InoutPartial || p.decls.is_resource(&ty);
            }
            if let Some(value) = value {
                let (modes, _, _, params) = p.ty(value).fn_parts().expect("a function value has a function type");
                let i = i.expect("a function value has no receiver");
                return modes[i] == ParamMode::InoutPartial || p.decls.is_resource(&params[i]);
            }
            let Some(f) = f else { return false };
            let info = &p.fns[f];
            match i {
                None => {
                    info.self_mode == ParamMode::InoutPartial
                        || info.receiver.as_ref().is_some_and(|ty| p.decls.is_resource(ty))
                }
                Some(i) => {
                    let param = &info.params[i];
                    param.mode == ParamMode::InoutPartial || p.decls.is_resource(&param.ty)
                }
            }
        };
        if let Some(receiver) = receiver {
            if inout_self {
                let (root, path) = self.place(receiver, frame)?;
                let span = self.m.exprs[receiver].span;
                places.push(Inout {
                    index: 0,
                    root,
                    path,
                    span,
                    partial: partial(self.p, None),
                    lent: None,
                    shares: None,
                });
                values.push(Value::Unit);
            } else {
                values.push(self.held(receiver, frame)?);
            }
        }
        for (i, arg) in args.iter().enumerate() {
            if arg.inout {
                let (root, path) = self.place(arg.value, frame)?;
                let span = self.m.exprs[arg.value].span;
                let partial = partial(self.p, Some(i));
                places.push(Inout { index: values.len(), root, path, span, partial, lent: None, shares: None });
                values.push(Value::Unit);
            } else {
                values.push(self.held(arg.value, frame)?);
            }
        }
        for k in 0..places.len() {
            let take = !can_fail || places[k].partial;
            values[places[k].index] = match &places[k].root {
                Root::Local(id) if take => {
                    std::mem::replace(slot(&mut frame[id.index()], &places[k].path)?, Value::Unit)
                }
                Root::Local(_) => self.read_place(frame, &places[k].root, &places[k].path, places[k].span)?,
                // A `state` field is lent out of its object for the call, once however many
                // places it holds, so nothing reads or changes it meanwhile (REFERENCE §9.6).
                // A call that may roll it back gets a copy, as for a local.
                Root::State(..) => {
                    let key = places[k].root.key();
                    let owner =
                        match places[..k].iter().position(|place| place.lent.is_some() && place.root.key() == key) {
                            Some(owner) => owner,
                            None => {
                                places[k].lent = self.lend(&places[k].root, places[k].span)?;
                                k
                            }
                        };
                    places[k].shares = (owner != k).then_some(owner);
                    let path = places[k].path.clone();
                    let lent = &mut places[owner].lent.as_mut().expect("a `state` root is lent").value;
                    if take { std::mem::replace(slot(lent, &path)?, Value::Unit) } else { at(lent, &path)?.clone() }
                }
            };
            let place = &places[k];
            // A closure this call made reads what it captures as it is now (REFERENCE §6.7).
            if let Value::Fn(FnValue::Closure(c)) = &values[place.index]
                && c.frame == self.frame
            {
                values[place.index] = self.closure(c.expr, frame);
            }
        }
        Ok((values, places))
    }

    /// How function `f` takes its receiver and whether it can fail.
    fn shape(&self, f: FnId) -> Shape {
        let info = &self.p.fns[f];
        Shape {
            inout_self: matches!(info.self_mode, ParamMode::Inout | ParamMode::InoutPartial),
            can_fail: info.fails.is_some(),
            f: Some(f),
            method: None,
            value: None,
        }
    }

    /// Notes a resource the running call now owns.
    fn acquire(&mut self, owned: Owned) {
        self.acquired += 1;
        self.owned.push((self.acquired, owned));
    }

    /// Notes that `local`, which the running call owns, holds a new value, bound at `span`
    /// when given, and returns whether it was owned already.
    fn reacquire(&mut self, local: LocalId, span: Option<Span>) -> bool {
        let base = self.base;
        let Some((acquired, Owned::Local(_, at))) =
            self.owned[base..].iter_mut().rev().find(|(_, o)| matches!(o, Owned::Local(l, _) if *l == local))
        else {
            return false;
        };
        self.acquired += 1;
        *acquired = self.acquired;
        if let Some(span) = span {
            *at = span;
        }
        true
    }

    /// The value of `e`, which the call, literal or `match` around it holds until it takes
    /// it, when it is a resource that moves there (REFERENCE §10).
    fn held(&mut self, e: ExprId, frame: &mut Frame) -> Flow<Value> {
        let value = self.expr(e, frame)?;
        if self.p.held.get(e).is_some() {
            self.acquire(Owned::Value(value.clone(), self.m.exprs[e].span));
        }
        Ok(value)
    }

    /// Notes the resources the bindings of `pat`, which has just matched, own.
    fn own_bindings(&mut self, pat: PatId) {
        let m = self.m;
        match &m.pats[pat].kind {
            PatKind::Bind(_) if self.p.owned_binds.get(pat).is_some() => {
                let local = *self.p.pat_local.get(pat).expect("bindings are resolved");
                // A local bound again owns only its new value, which is acquired now.
                if !self.reacquire(local, Some(m.pats[pat].span)) {
                    self.acquire(Owned::Local(local, m.pats[pat].span));
                }
            }
            PatKind::Tuple(parts) => {
                for &part in parts {
                    self.own_bindings(part);
                }
            }
            PatKind::Ctor { fields: Some(fields), .. } => {
                for field in fields {
                    self.own_bindings(field.pat);
                }
            }
            _ => {}
        }
    }

    /// Takes the resource parts that `pat`, which has just matched the value of `value`, moved
    /// out of the place `value` names, so that the place no longer holds them (REFERENCE §10).
    fn take_parts(&mut self, value: ExprId, pat: PatId, frame: &mut Frame) {
        let Some(paths) = self.p.parts_out.get(pat) else { return };
        if !self.is_place(value) {
            return;
        }
        let mut base = Vec::new();
        let mut at = value;
        let root = loop {
            match (&self.m.exprs[at].kind, self.p.res(at)) {
                (ExprKind::Name(_) | ExprKind::It, Some(Res::Local(id))) => break id,
                (ExprKind::Field { base: inner, .. }, Some(Res::Field(i))) => {
                    base.push(i);
                    at = *inner;
                }
                _ => return,
            }
        };
        base.reverse();
        for path in paths.iter() {
            let full: Vec<Step> = base.iter().chain(path.iter()).map(|&i| Step::Field(i)).collect();
            if let Ok(place) = slot(&mut frame[root.index()], &full) {
                *place = Value::Unit;
            }
        }
    }

    /// Calls `f` with `values`, and once it succeeds writes the final value of each `inout`
    /// parameter back to its place, then checks each record on the places' paths, innermost
    /// first, each once. A failed call writes back only the places that keep partial changes
    /// (REFERENCE §5.4, §8.3).
    fn call_back(
        &mut self,
        callee: Callee,
        values: Vec<Value>,
        mut places: Vec<Inout>,
        frame: &mut Frame,
        site: Span,
    ) -> Flow<Value> {
        let keep: Vec<usize> = places.iter().map(|place| place.index).collect();
        let (result, finals) = self.run(callee, values, site, &keep);
        if places.is_empty() {
            return result;
        }
        if result.is_err() {
            for (k, value) in finals.into_iter().enumerate() {
                if !places[k].partial {
                    continue;
                }
                let path = places[k].path.clone();
                let owner = places[k].shares.unwrap_or(k);
                if let Ok(slot) = slot(lent_base(frame, &mut places[owner]), &path) {
                    *slot = value;
                }
            }
            // Each lent `state` field goes back as it was, but for the partial changes.
            return result;
        }
        let value = result?;
        for (k, value) in finals.into_iter().enumerate() {
            let path = places[k].path.clone();
            let owner = places[k].shares.unwrap_or(k);
            *slot(lent_base(frame, &mut places[owner]), &path)? = value;
        }
        // The lent `state` fields go back before anything reads them.
        for place in &mut places {
            place.lent = None;
        }
        let mut checked: Vec<PlaceKey> = Vec::new();
        for place in &places {
            for depth in (0..place.path.len()).rev() {
                let key = (place.root.key(), place.path[..depth].iter().map(Step::key).collect());
                if checked.contains(&key) {
                    continue;
                }
                checked.push(key);
                let value = self.read_place(frame, &place.root, &place.path[..depth], place.span)?;
                self.refine(&value, site)?;
            }
        }
        Ok(value)
    }

    /// The value of local `id`. A closure that the running call made reads what it captures
    /// again, so a call sees them as they are now (REFERENCE §6.7).
    fn local(&self, id: LocalId, frame: &Frame) -> Value {
        match &frame[id.index()] {
            Value::Fn(FnValue::Closure(c)) if c.frame == self.frame => self.closure(c.expr, frame),
            value => value.clone(),
        }
    }

    /// The closure `e`, with the values of what it captures in `frame`. A captured closure
    /// that the running call made reads what it captures again too. Each is made once, and
    /// without recursion, since a chain of them may be as long as the function.
    fn closure(&self, e: ExprId, frame: &Frame) -> Value {
        let fresh = |id: LocalId| match &frame[id.index()] {
            Value::Fn(FnValue::Closure(c)) if c.frame == self.frame => Some(c.expr),
            _ => None,
        };
        let mut made: HashMap<LocalId, Value> = HashMap::new();
        // Each closure to make, with the local that holds it, once what it captures is made.
        let mut stack = vec![(e, None, false)];
        while let Some((expr, holder, ready)) = stack.pop() {
            if holder.is_some_and(|id| made.contains_key(&id)) {
                continue;
            }
            let captures = &self.p.closures.get(expr).expect("closures are checked").captures;
            if !ready {
                stack.push((expr, holder, true));
                for &(id, _) in captures {
                    if let Some(inner) = fresh(id).filter(|_| !made.contains_key(&id)) {
                        stack.push((inner, Some(id), false));
                    }
                }
                continue;
            }
            let env = captures
                .iter()
                .map(|&(id, _)| (id, made.get(&id).cloned().unwrap_or_else(|| frame[id.index()].clone())))
                .collect();
            let value = Value::Fn(FnValue::Closure(Arc::new(ClosureValue {
                expr,
                frame: self.frame,
                locals: frame.len(),
                env,
                owner: self.owner,
            })));
            match holder {
                Some(id) => {
                    made.insert(id, value);
                }
                None => return value,
            }
        }
        unreachable!("the closure asked for is made last")
    }

    /// The closure `e` for a local, with what it captures as it is in `frame`, though not
    /// read again. [`Interp::local`] reads it again.
    fn bound(&self, e: ExprId, frame: &Frame) -> Value {
        let info = self.p.closures.get(e).expect("closures are checked");
        let env = info.captures.iter().map(|&(id, _)| (id, frame[id.index()].clone())).collect();
        Value::Fn(FnValue::Closure(Arc::new(ClosureValue {
            expr: e,
            frame: self.frame,
            locals: frame.len(),
            env,
            owner: self.owner,
        })))
    }

    /// Runs a block and returns the value of its final expression, or `Unit`.
    fn block(&mut self, block: &Block, frame: &mut Frame) -> Flow<Value> {
        let mut value = Value::Unit;
        for (i, &s) in block.stmts.iter().enumerate() {
            if i + 1 == block.stmts.len()
                && let StmtKind::Expr(e) = self.m.stmts[s].kind
            {
                value = self.expr(e, frame)?;
                continue;
            }
            self.stmt(s, frame)?;
        }
        Ok(value)
    }

    fn stmt(&mut self, s: StmtId, frame: &mut Frame) -> Flow<()> {
        let m = self.m;
        let stmt = &m.stmts[s];
        match &stmt.kind {
            StmtKind::Let { pat, init, .. } => {
                // A local reads its closure's captures again whenever it is read, so they
                // aren't read here, and a chain of closures is made in linear time.
                let value = match m.exprs[*init].kind {
                    ExprKind::Closure(_) => self.bound(*init, frame),
                    _ => self.expr(*init, frame)?,
                };
                // The checker proved that the pattern matches every value.
                self.matches(*pat, &value, frame)?;
                self.take_parts(*init, *pat, frame);
                self.own_bindings(*pat);
            }
            StmtKind::Expect { value, expect } => {
                let why = match expect {
                    Some(expect) => self.expect(*value, expect, frame)?,
                    None if self.bool(*value, frame)? => None,
                    None => Some(format!("`{}` is false", self.sources.slice(m.exprs[*value].span))),
                };
                if let Some(why) = why {
                    return Err(Unwind::Expected(why, stmt.span));
                }
            }
            StmtKind::Check { cond, fallback } => {
                if !self.bool(*cond, frame)? {
                    // The checker proved that the fallback leaves.
                    self.fallback(fallback, frame)?;
                }
            }
            StmtKind::Assign { target, op, value } => {
                // The value first, then the indices of the target, as in Rust and Python
                // (OPEN_QUESTIONS P5).
                let value = self.expr(*value, frame)?;
                let (root, path) = self.place(*target, frame)?;
                // A local given a new resource acquires it now (REFERENCE §10 rule 3).
                if let (true, Root::Local(id)) = (path.is_empty(), &root) {
                    self.reacquire(*id, None);
                }
                let mut lent = self.lend(&root, stmt.span)?;
                let base = base(frame, &root, &mut lent);
                let slot = slot(base, &path)?;
                *slot = match op.bin_op() {
                    None => value,
                    Some(op) => self.arithmetic(op, slot.clone(), value, stmt.span)?,
                };
                // Each record on the path has changed, so each is checked, innermost first
                // (OPEN_QUESTIONS P5).
                for depth in (0..path.len()).rev() {
                    self.refine(at(base, &path[..depth])?, stmt.span)?;
                }
            }
            StmtKind::Expr(e) => {
                self.expr(*e, frame)?;
            }
            StmtKind::Return(value) => {
                let value = match value {
                    Some(value) => self.expr(*value, frame)?,
                    None => Value::Unit,
                };
                return Err(Unwind::Return(value));
            }
            StmtKind::Break(_) => return Err(Unwind::Break(self.jump_target(s))),
            StmtKind::Continue(_) => return Err(Unwind::Continue(self.jump_target(s))),
            StmtKind::Assert(cond) => {
                if !self.bool(*cond, frame)? {
                    let text = self.sources.slice(m.exprs[*cond].span);
                    return Err(defect(DefectKind::AssertionFailed, format!("assertion failed: {text}"), stmt.span));
                }
            }
        }
        Ok(())
    }

    /// A defect if `value` breaks a refinement of its record. A record holds its refinements
    /// once built, so only one that was just built or changed is checked (OPEN_QUESTIONS P3).
    fn refine(&mut self, value: &Value, span: Span) -> Flow<()> {
        let Value::Adt(adt) = value else { return Ok(()) };
        let (p, sources) = (self.p, self.sources);
        let def = p.decls.adt(adt.def);
        let variant = &def.variants[adt.variant.index()];
        if variant.preds.is_empty() {
            return Ok(());
        }
        let mut frame: Frame = adt.fields.to_vec();
        frame.resize(variant.locals, Value::Unit);
        for pred in &variant.preds {
            match self.bool(pred.expr, &mut frame) {
                Ok(true) => continue,
                Ok(false) => {}
                // The predicate runs on behalf of the construction or assignment, so a defect
                // in it is traced back there, as a defect in a call is.
                Err(Unwind::Defect(mut defect)) => {
                    defect.callers.push(span);
                    return Err(Unwind::Defect(defect));
                }
                Err(other) => return Err(other),
            }
            let text = sources.slice(self.m.exprs[pred.expr].span);
            let message = match pred.field {
                Some(i) => {
                    let shown = debug_repr(&adt.fields[i.index()], &p.decls);
                    let field = &variant.fields[i.index()].name;
                    let ctor = def.ctor_name(adt.variant);
                    format!("`{ctor}.{field}` is {shown}, which breaks its refinement `{text}`")
                }
                None => format!("{} breaks `{}`'s refinement `{text}`", debug_repr(value, &p.decls), def.name),
            };
            return Err(defect(DefectKind::RefinementFailed, message, span));
        }
        Ok(())
    }

    /// The local that a place, an assignment's target or a changing method's receiver, is
    /// rooted at, and the fields and elements from there to the place. The indices are
    /// evaluated from the root out, and each is checked before the next one runs, as a read
    /// checks it (OPEN_QUESTIONS P5).
    /// A place under a `state` field is rooted at the field, which every copy of its object
    /// shares (REFERENCE §9.6).
    fn place(&mut self, target: ExprId, frame: &mut Frame) -> Flow<(Root, Vec<Step>)> {
        let span = self.m.exprs[target].span;
        let mut steps = Vec::new();
        let mut e = target;
        let root = loop {
            match (&self.m.exprs[e].kind, self.p.res(e)) {
                (ExprKind::Name(_), Some(Res::Local(id))) => break id,
                (ExprKind::Field { base, .. }, Some(Res::Field(i))) => {
                    steps.push(Ok(i));
                    e = *base;
                }
                (ExprKind::Index { base, index }, _) => {
                    steps.push(Err((*index, self.m.exprs[e].span)));
                    e = *base;
                }
                (_, res) => unreachable!("assignment targets are places, not {res:?}"),
            }
        };
        let mut root = Root::Local(root);
        let mut path = Vec::with_capacity(steps.len());
        for step in steps.into_iter().rev() {
            match step {
                Ok(i) => match self.state_root(frame, &root, &path, i, span)? {
                    Some(state) => {
                        root = state;
                        path.clear();
                    }
                    None => path.push(Step::Field(i)),
                },
                Err((index, span)) => {
                    path.push(Step::Index(self.int(index, frame)?.0, span));
                    self.read_place(frame, &root, &path, span)?;
                }
            }
        }
        Ok((root, path))
    }

    /// The root of the place at field `i` of the value at `path` under `root`, if that value
    /// is a capability object and `i` one of its `state` fields.
    fn state_root(&self, frame: &Frame, root: &Root, path: &[Step], i: FieldIdx, span: Span) -> Flow<Option<Root>> {
        let object = |value: &Value| match value {
            Value::Object(object) if self.p.decls.adt(object.def).variant().fields[i.index()].state => {
                Some(Root::State(object.state.clone(), object.def, i))
            }
            _ => None,
        };
        match root {
            Root::Local(id) => Ok(object(at(&frame[id.index()], path)?)),
            Root::State(..) => Ok(object(&self.read_place(frame, root, path, span)?)),
        }
    }

    /// A copy of the value at `path` under `root`.
    fn read_place(&self, frame: &Frame, root: &Root, path: &[Step], span: Span) -> Flow<Value> {
        match root {
            Root::Local(id) => Ok(at(&frame[id.index()], path)?.clone()),
            Root::State(state, def, i) => {
                let state_ref = state.lock();
                if state_ref.lent[i.index()] {
                    return Err(self.lent_read(*def, *i, span));
                }
                Ok(at(&state_ref.values[i.index()], path)?.clone())
            }
        }
    }

    /// Field `i` of capability object `object`.
    fn object_field(&self, object: &CapObject, i: FieldIdx, span: Span) -> Flow<Value> {
        if !self.p.decls.adt(object.def).variant().fields[i.index()].state {
            return Ok(object.fields[i.index()].clone());
        }
        self.read_place(&Vec::new(), &Root::State(object.state.clone(), object.def, i), &[], span)
    }

    /// Lends the `state` field that `root` names, if it names one, out of its object while it
    /// is changed in place. Reading the field meanwhile is a defect.
    fn lend(&self, root: &Root, span: Span) -> Flow<Option<Lent>> {
        let Root::State(state, def, i) = root else { return Ok(None) };
        let mut inner = state.lock();
        if inner.lent[i.index()] {
            return Err(self.lent_read(*def, *i, span));
        }
        inner.lent[i.index()] = true;
        let value = std::mem::replace(&mut inner.values[i.index()], Value::Unit);
        Ok(Some(Lent { state: state.clone(), field: i.index(), value }))
    }

    /// The defect of reading `state` field `i` of a `def` while a change to it is in progress,
    /// which only a call that re-enters the object can do.
    fn lent_read(&self, def: AdtId, i: FieldIdx, span: Span) -> Unwind {
        let def = self.p.decls.adt(def);
        let field = &def.variant().fields[i.index()].name;
        let message = format!(
            "this uses `state` field `{field}` of a `{}` while a change to it is in progress; calls on one capability object run one at a time (§9.6)",
            def.name
        );
        defect(DefectKind::ReentrantCall, message, span)
    }

    /// Begins a call of method `f` of a `cap record` on `object`, and returns the object's
    /// `state` as it was, which a failure restores. A call through a capability handle, or
    /// from outside the record's own `impl` blocks, while one of the object's methods runs
    /// re-enters it, which is a defect (REFERENCE §9.6; OPEN_QUESTIONS Q30).
    fn enter(&self, object: &CapObject, f: FnId, handle: bool, site: Span) -> Flow<Vec<Value>> {
        let mut state = object.state.lock();
        let def = self.p.decls.adt(object.def);
        let name = self.m.text(self.p.fns[f].name);
        if handle && state.running > 0 {
            let message = format!(
                "this calls `{name}` on a `{}` whose operation is still running, through a capability handle or from outside the record's own `impl` blocks; calls on one capability object run one at a time (§9.6)",
                def.name
            );
            return Err(defect(DefectKind::ReentrantCall, message, site));
        }
        state.running += 1;
        Ok(state.values.clone())
    }

    /// A value of record or enum `def`, built from its fields' values in declaration order. A
    /// `cap record`'s is a new object, which holds its `state` (REFERENCE §9.6).
    fn construct(&self, def: AdtId, variant: VariantIdx, mut fields: Vec<Value>) -> Value {
        let adt = self.p.decls.adt(def);
        if !adt.cap {
            return Value::Adt(Adt { def, variant, fields: fields.into() });
        }
        let mut state = vec![Value::Unit; fields.len()];
        for (i, field) in adt.variant().fields.iter().enumerate() {
            if field.state {
                state[i] = std::mem::replace(&mut fields[i], Value::Unit);
            }
        }
        Value::Object(Arc::new(CapObject { def, fields: fields.into(), state: Arc::new(CapState::new(state)) }))
    }

    /// Whether `e` is a local or a field of one.
    fn is_place(&self, e: ExprId) -> bool {
        match (&self.m.exprs[e].kind, self.p.res(e)) {
            (ExprKind::Name(_) | ExprKind::It, Some(Res::Local(_))) => true,
            (ExprKind::Field { base, .. }, Some(Res::Field(_))) => self.is_place(*base),
            _ => false,
        }
    }

    /// Takes the value of the local or field `e` names out of its place, which nothing reads
    /// again before it is assigned (REFERENCE §5.1), so what it holds isn't copied.
    fn take_out(&self, e: ExprId, frame: &mut Frame) -> Option<Value> {
        let mut path = Vec::new();
        let mut at = e;
        let root = loop {
            match (&self.m.exprs[at].kind, self.p.res(at)) {
                (ExprKind::Name(_) | ExprKind::It, Some(Res::Local(id))) => break id,
                (ExprKind::Field { base, .. }, Some(Res::Field(i))) => {
                    path.push(Step::Field(i));
                    at = *base;
                }
                _ => return None,
            }
        };
        path.reverse();
        let place = slot(&mut frame[root.index()], &path).ok()?;
        Some(std::mem::replace(place, Value::Unit))
    }

    fn jump_target(&self, s: StmtId) -> ExprId {
        *self.p.jump_target.get(s).expect("jumps are resolved")
    }

    fn bool(&mut self, e: ExprId, frame: &mut Frame) -> Flow<bool> {
        match self.expr(e, frame)? {
            Value::Bool(b) => Ok(b),
            other => unreachable!("expected a Bool, found {other:?}"),
        }
    }

    fn int(&mut self, e: ExprId, frame: &mut Frame) -> Flow<(i128, IntTy)> {
        match self.expr(e, frame)? {
            Value::Int(i, it) => Ok((i, it)),
            other => unreachable!("expected an integer, found {other:?}"),
        }
    }

    /// The type of an integer literal, which comes from its context.
    fn int_ty(&self, e: ExprId) -> IntTy {
        match self.p.ty(e) {
            Ty::Int(it) => *it,
            other => unreachable!("integer literals have an integer type, not {other:?}"),
        }
    }

    fn expr(&mut self, e: ExprId, frame: &mut Frame) -> Flow<Value> {
        let m = self.m;
        let span = m.exprs[e].span;
        self.check_stack(span, false)?;
        Ok(match &m.exprs[e].kind {
            ExprKind::Int(value) => Value::Int(*value as i128, self.int_ty(e)),
            ExprKind::Float(text) => match self.p.ty(e) {
                Ty::Float(FloatTy::F32) => Value::F32(text.parse().expect("the checker validated the literal")),
                _ => Value::F64(text.parse().expect("the checker validated the literal")),
            },
            ExprKind::Bool(b) => Value::Bool(*b),
            ExprKind::Char(c) => Value::Char(*c),
            ExprKind::Text(text) => Value::Text(Arc::from(text.as_str())),
            ExprKind::Unit => Value::Unit,
            ExprKind::Applied { callee, .. } => self.expr(*callee, frame)?,
            ExprKind::Closure(_) => self.closure(e, frame),
            ExprKind::FText(parts) => {
                let mut out = String::new();
                for part in parts {
                    match part {
                        FTextPart::Lit(text) => out.push_str(text),
                        FTextPart::Expr(x) => {
                            let value = self.expr(*x, frame)?;
                            out.push_str(&self.show(&value, m.exprs[*x].span)?);
                        }
                    }
                }
                Value::Text(out.into())
            }
            ExprKind::Name(_) => match self.p.res(e) {
                // A value that moves leaves its local, which nothing reads again before it is
                // assigned (REFERENCE §5.1), so a pool or list that moves isn't copied.
                Some(Res::Local(_)) if self.p.moves_out.get(e).is_some() => {
                    self.take_out(e, frame).expect("a moved name is a local")
                }
                Some(Res::Local(id)) => self.local(id, frame),
                Some(Res::Ctor(def, variant)) => Value::Adt(Adt { def, variant, fields: Arc::from([]) }),
                Some(Res::Fn(f)) => Value::Fn(FnValue::Named(f)),
                other => unreachable!("names evaluate to locals, not {other:?}"),
            },
            ExprKind::Call { callee, args, .. }
                if !matches!(self.p.res(*callee), Some(Res::Fn(_) | Res::Ctor(..) | Res::Method(_))) =>
            {
                let Value::Fn(f) = self.expr(*callee, frame)? else {
                    unreachable!("the checker found a function type")
                };
                let can_fail = self.p.ty(*callee).fn_parts().is_some_and(|(_, _, fails, _)| *fails != Ty::Never);
                let shape = Shape { can_fail, value: Some(*callee), ..Shape::default() };
                let mark = self.owned.len();
                let (values, places) = self.args(shape, None, args, frame)?;
                self.owned.truncate(mark);
                let callee = match &f {
                    FnValue::Named(f) => Callee::Fn(*f),
                    FnValue::Closure(c) => Callee::Closure(c),
                };
                let result = self.call_back(callee, values, places, frame, span);
                return self.attempted(e, result);
            }
            ExprKind::Call { callee, args, .. } => {
                let shape = match self.p.res(*callee) {
                    Some(Res::Fn(f)) => self.shape(f),
                    _ => Shape::default(),
                };
                let mark = self.owned.len();
                let (values, places) = self.args(shape, None, args, frame)?;
                match self.p.res(*callee) {
                    Some(Res::Fn(f)) => {
                        self.owned.truncate(mark);
                        let result = self.call_back(Callee::Fn(f), values, places, frame, span);
                        return self.attempted(e, result);
                    }
                    // `T(x)` converts its one value (STD.md).
                    Some(Res::Method(builtin)) => {
                        self.owned.truncate(mark);
                        self.builtin(builtin, values, span)?
                    }
                    // Labels follow the declaration order, so argument `i` is field `i`.
                    Some(Res::Ctor(def, variant)) => {
                        let value = self.construct(def, variant, values);
                        self.refine(&value, span)?;
                        self.owned.truncate(mark);
                        value
                    }
                    other => unreachable!("calls are resolved, not {other:?}"),
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                let res = self.p.res(e).expect("methods are resolved");
                // A method that changes its receiver, such as `push`, changes it in place.
                if let Res::Method(builtin) = res
                    && builtin.changes_receiver()
                {
                    return self.change_call(builtin, *receiver, args, frame, span);
                }
                // The receiver of a variant's construction or an associated function is a type's
                // name, and that of `I.f(x)` or `I.of(r)` an interface's, not a value. Otherwise the receiver
                // comes first.
                let named = match res {
                    Res::Ctor(..)
                    | Res::Dispatch { qualified: true, .. }
                    | Res::Method(
                        Builtin::Parse(_)
                        | Builtin::Of
                        | Builtin::PoolNew
                        | Builtin::TryFrom(_)
                        | Builtin::WrappingFrom(_)
                        | Builtin::Convert(_),
                    ) => true,
                    Res::Fn(f) => self.p.fns[f].receiver.is_none(),
                    _ => false,
                };
                let receiver = (!named).then_some(*receiver);
                let shape = match res {
                    Res::Fn(f) => self.shape(f),
                    // An interface's methods borrow `self`, and an implementation fails as its
                    // method is declared to.
                    Res::Dispatch { iface, method, qualified } => {
                        let can_fail = self.p.decls.iface(iface).methods[method].fails.is_some();
                        let self_value = receiver.unwrap_or_else(|| args[0].value);
                        let method = Some((iface, method, self_value, qualified));
                        Shape { inout_self: false, can_fail, f: None, method, value: None }
                    }
                    _ => Shape::default(),
                };
                // `with` reads a receiver that is a variable or a field of one once its
                // arguments, which may read or assign it, are evaluated. One that moves leaves
                // its local then.
                let mark = self.owned.len();
                let (values, places) = if let Some(place) = receiver.filter(|&r| res == Res::With && self.is_place(r)) {
                    let (values, places) = self.args(shape, None, args, frame)?;
                    let taken = match self.p.moves_out.get(place) {
                        Some(()) => self.take_out(place, frame).expect("a moved receiver is a place"),
                        None => self.expr(place, frame)?,
                    };
                    (std::iter::once(taken).chain(values).collect(), places)
                } else {
                    self.args(shape, receiver, args, frame)?
                };
                // The call takes what it is given, and a construction once it is built.
                if !matches!(res, Res::Ctor(..) | Res::With) {
                    self.owned.truncate(mark);
                }
                match res {
                    Res::Method(builtin) => {
                        let result = self.builtin(builtin, values, span);
                        return self.attempted(e, result);
                    }
                    Res::Fn(f) => {
                        let result = self.call_back(Callee::Fn(f), values, places, frame, span);
                        return self.attempted(e, result);
                    }
                    Res::Dispatch { iface, method, .. } => {
                        let self_value = receiver.unwrap_or_else(|| args[0].value);
                        let result = match iface {
                            _ if let Value::Cap(cap) = &values[0] => self.operation(cap, iface, method, &values[1..]),
                            IfaceId::SHOW | IfaceId::EQ | IfaceId::ORD => self.dispatch(iface, method, values, span),
                            IfaceId::ABANDON if !matches!(&values[0], Value::Adt(adt) if self.p.decls.adt(adt.def).resource_base) => {
                                self.dispatch(iface, method, values, span)
                            }
                            _ => {
                                let key = impl_key(&values[0]);
                                let f = self.p.decls.impl_method(iface, key, method);
                                let f = f.expect("the checker found an implementation");
                                // A call through a capability handle, rather than on a value of
                                // the `cap record`, may not re-enter its object (OPEN_QUESTIONS Q30).
                                self.handle_call = matches!(self.p.ty(self_value), Ty::Cap(_));
                                self.call_back(Callee::Fn(f), values, places, frame, span)
                            }
                        };
                        return self.attempted(e, result);
                    }
                    // Labels follow the declaration order, so argument `i` is field `i`.
                    Res::Ctor(def, variant) => {
                        let value = self.construct(def, variant, values);
                        self.refine(&value, span)?;
                        self.owned.truncate(mark);
                        value
                    }
                    Res::With => {
                        let mut values = values.into_iter();
                        let replaced = self.p.with_fields.get(e).expect("`with` is resolved");
                        // A capability object's copy replaces plain fields only, and shares the
                        // `state` (OPEN_QUESTIONS Q40).
                        let mut value = values.next().expect("`with` has a receiver");
                        let fields = match &mut value {
                            Value::Adt(adt) => Arc::make_mut(&mut adt.fields),
                            Value::Object(object) => Arc::make_mut(&mut Arc::make_mut(object).fields),
                            _ => unreachable!("`with` copies a record"),
                        };
                        for (i, value) in replaced.iter().zip(values) {
                            fields[i.index()] = value;
                        }
                        // The new record holds what the receiver and the arguments held, which
                        // a refinement that fails abandons with it.
                        self.owned.truncate(mark);
                        self.acquire(Owned::Value(value.clone(), span));
                        self.refine(&value, span)?;
                        self.owned.truncate(mark);
                        value
                    }
                    other => unreachable!("methods are resolved, not {other:?}"),
                }
            }
            ExprKind::Field { base, .. } => {
                if let Some(Res::Ctor(def, variant)) = self.p.res(e) {
                    return Ok(Value::Adt(Adt { def, variant, fields: Arc::from([]) }));
                }
                // A field that moves leaves its record, as a local's value does.
                if self.p.moves_out.get(e).is_some()
                    && let Some(value) = self.take_out(e, frame)
                {
                    return Ok(value);
                }
                let Some(Res::Field(i)) = self.p.res(e) else { unreachable!("fields are resolved") };
                match self.expr(*base, frame)? {
                    Value::Adt(adt) => adt.fields[i.index()].clone(),
                    Value::Object(object) => self.object_field(&object, i, span)?,
                    other => unreachable!("fields are read from records, not {other:?}"),
                }
            }
            ExprKind::Index { base, index } => return self.index(*base, *index, frame, span),
            ExprKind::List(elements) => return self.list(elements, frame),
            ExprKind::Map(entries) => return self.map(entries, frame, span),
            ExprKind::Unary { op: UnaryOp::Not, operand } => Value::Bool(!self.bool(*operand, frame)?),
            ExprKind::Unary { op: UnaryOp::Neg, operand } => {
                if let ExprKind::Int(value) = m.exprs[*operand].kind {
                    // The checker treats `-128` as one literal, so it never overflows here.
                    return Ok(Value::Int(-(value as i128), self.int_ty(e)));
                }
                let value = self.expr(*operand, frame)?;
                return self.negate(value, span);
            }
            ExprKind::Binary { op: BinOp::And, lhs, rhs } => {
                Value::Bool(self.bool(*lhs, frame)? && self.bool(*rhs, frame)?)
            }
            ExprKind::Binary { op: BinOp::Or, lhs, rhs } => {
                Value::Bool(self.bool(*lhs, frame)? || self.bool(*rhs, frame)?)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let a = self.expr(*lhs, frame)?;
                let b = self.expr(*rhs, frame)?;
                match op {
                    _ if op.is_arithmetic() => return self.arithmetic(*op, a, b, span),
                    BinOp::Eq => Value::Bool(self.equal(&a, &b, span)?),
                    BinOp::Ne => Value::Bool(!self.equal(&a, &b, span)?),
                    _ => Value::Bool(holds(*op, self.ordering(&a, &b, span)?)),
                }
            }
            ExprKind::Range { .. } => unreachable!("ranges appear only in `for` loops"),
            ExprKind::Try(inner) => return self.expr(*inner, frame),
            ExprKind::Attempt(inner) => {
                let (variant, value) = match self.expr(*inner, frame) {
                    Ok(value) => (VariantIdx::OK, value),
                    Err(Unwind::Attempted(attempt, error)) if attempt == e => (VariantIdx::ERR, error),
                    Err(other) => return Err(other),
                };
                Value::Adt(Adt { def: AdtId::RESULT, variant, fields: Arc::from([value]) })
            }
            ExprKind::Fail(value) => return Err(Unwind::Fail(self.expr(*value, frame)?)),
            ExprKind::If { cond, then_block, else_branch } => {
                let value = if self.bool(*cond, frame)? {
                    self.block(then_block, frame)?
                } else {
                    match else_branch {
                        Some(ElseBranch::Block(block)) => self.block(block, frame)?,
                        Some(ElseBranch::If(nested)) => self.expr(*nested, frame)?,
                        None => Value::Unit,
                    }
                };
                // A chain without a final `else` is a statement, so its value is `()` even
                // where a block that gives `()` ends in it (REFERENCE §6.2).
                if lacks_final_else(m, e) { Value::Unit } else { value }
            }
            ExprKind::While { cond, body, .. } => {
                while self.bool(*cond, frame)? {
                    if self.loop_body(e, body, frame)?.is_break() {
                        break;
                    }
                }
                Value::Unit
            }
            ExprKind::Loop { body, .. } => {
                while !self.loop_body(e, body, frame)?.is_break() {}
                Value::Unit
            }
            ExprKind::For { pat, iter, body, .. } => {
                if let ExprKind::Range { lo, hi, inclusive } = m.exprs[*iter].kind {
                    let (lo, it) = self.int(lo, frame)?;
                    let (hi, _) = self.int(hi, frame)?;
                    let end = if inclusive { hi + 1 } else { hi };
                    let mut i = lo;
                    while i < end {
                        self.matches(*pat, &Value::Int(i, it), frame)?;
                        if self.loop_body(e, body, frame)?.is_break() {
                            break;
                        }
                        i += 1;
                    }
                    return Ok(Value::Unit);
                }
                return self.for_collection(e, *pat, *iter, body, frame);
            }
            ExprKind::Todo(message) => {
                let message = match message {
                    Some(text) => format!("reached `todo`: {text}"),
                    None => "reached `todo`".to_string(),
                };
                return Err(defect(DefectKind::TodoReached, message, span));
            }
            ExprKind::Unreachable => return Err(defect(DefectKind::UnreachableReached, "reached `unreachable`", span)),
            ExprKind::Match { scrutinee, arms, .. } => {
                // A resource the scrutinee makes is held until an arm's bindings take it.
                let mark = self.owned.len();
                let value = self.held(*scrutinee, frame)?;
                for arm in arms {
                    if !self.matches(arm.pat, &value, frame)? {
                        continue;
                    }
                    if let Some(guard) = arm.guard
                        && !self.bool(guard, frame)?
                    {
                        continue;
                    }
                    self.owned.truncate(mark);
                    self.take_parts(*scrutinee, arm.pat, frame);
                    self.own_bindings(arm.pat);
                    // An arm whose pattern moves the scrutinee takes it out of its local once
                    // the arm is chosen, so what the pattern bound isn't copied.
                    if self.p.arms_out.get(arm.pat).is_some() && self.take_out(*scrutinee, frame).is_some() {
                        drop(value);
                    }
                    return self.block(&arm.body, frame);
                }
                // The checker leaves integer exhaustiveness to run time (OPEN_QUESTIONS P5).
                let shown = debug_repr(&value, &self.p.decls);
                return Err(defect(DefectKind::NoArmMatched, format!("no arm of this `match` matches {shown}"), span));
            }
            ExprKind::Is { value: tested, pat } => {
                let value = self.expr(*tested, frame)?;
                let matched = self.matches(*pat, &value, frame)?;
                if matched {
                    self.take_parts(*tested, *pat, frame);
                    self.own_bindings(*pat);
                }
                Value::Bool(matched)
            }
            ExprKind::Tuple(elements) => {
                let Ty::Adt(def, _) = self.p.ty(e) else { unreachable!("tuples have tuple types") };
                let def = *def;
                let mark = self.owned.len();
                let mut values = Vec::with_capacity(elements.len());
                for &element in elements {
                    values.push(self.held(element, frame)?);
                }
                self.owned.truncate(mark);
                Value::Adt(Adt { def, variant: VariantIdx::RECORD, fields: values.into() })
            }
            ExprKind::Else { value, fallback } => match self.p.it_local.get(e) {
                Some(&it) => match self.expr(*value, frame) {
                    Ok(value) => value,
                    Err(Unwind::Attempted(handler, error)) if handler == e => {
                        frame[it.index()] = error;
                        return self.fallback(fallback, frame);
                    }
                    Err(other) => return Err(other),
                },
                None => match self.expr(*value, frame)? {
                    Value::Adt(adt) if adt.variant == VariantIdx::SOME => adt.fields[0].clone(),
                    _ => return self.fallback(fallback, frame),
                },
            },
            ExprKind::It => match self.p.res(e) {
                Some(Res::Local(id)) => self.local(id, frame),
                other => unreachable!("`it` is a local, not {other:?}"),
            },
            ExprKind::Error => unreachable!("programs with errors don't run"),
            ExprKind::Debug(values) => {
                let mut parts = Vec::with_capacity(values.len());
                for value in values {
                    let shown = self.expr(*value, frame)?;
                    parts.push(match self.p.debug_fns.get(*value) {
                        Some(ty) => ty.to_string(),
                        None => debug_repr(&shown, &self.p.decls),
                    });
                }
                // `debug` output is best effort; a failed write is not a program error.
                let _ = writeln!(self.stderr, "[debug {}] {}", self.sources.location(span.lo), parts.join(", "));
                Value::Unit
            }
        })
    }

    // The collection forms are functions of their own, kept out of [`Interp::expr`], so its
    // native frame, which every level of nesting and every call takes, stays small.

    /// `xs[i]`, a copy of element `i`, or `pool[h]`, a copy of the element `h` reads, where a
    /// stale handle is a defect (REFERENCE §5.5).
    #[inline(never)]
    fn index(&mut self, base: ExprId, index: ExprId, frame: &mut Frame, span: Span) -> Flow<Value> {
        match self.expr(base, frame)? {
            Value::List(list) => {
                let (i, _) = self.int(index, frame)?;
                Ok(list.items[element_at(i, list.items.len(), span)?].clone())
            }
            Value::Pool(pool) => {
                let Value::Handle(handle) = self.expr(index, frame)? else {
                    unreachable!("a pool's index is a handle")
                };
                match pool.lookup(&handle) {
                    Ok(value) => Ok(value.clone()),
                    Err(message) => Err(defect(DefectKind::StaleHandle, message, span)),
                }
            }
            other => unreachable!("only lists and pools are indexed, not {other:?}"),
        }
    }

    /// `[a, b]`.
    #[inline(never)]
    fn list(&mut self, elements: &[ExprId], frame: &mut Frame) -> Flow<Value> {
        let mark = self.owned.len();
        let mut items = Vec::with_capacity(elements.len());
        for &element in elements {
            items.push(self.held(element, frame)?);
        }
        self.owned.truncate(mark);
        Ok(Value::List(Arc::new(ListValue { items })))
    }

    /// `["k": v]`, which sets its entries in order, so a key named twice keeps its first
    /// place and its last value.
    #[inline(never)]
    fn map(&mut self, entries: &[(ExprId, ExprId)], frame: &mut Frame, span: Span) -> Flow<Value> {
        let mark = self.owned.len();
        let mut map = MapValue::default();
        // Where in `owned` the value of each of the map's entries is held, if it is.
        let mut held_at: Vec<Option<usize>> = Vec::new();
        for &(key, value) in entries {
            let key = self.held(key, frame)?;
            let place = self.m.exprs[value].span;
            let held = self.p.held.get(value).is_some();
            let value = self.held(value, frame)?;
            let at = held.then(|| self.owned.len() - 1);
            let hash = hash_value(&key, &self.p.decls);
            match map.find(&key, hash, &mut |a, b| self.equal(a, b, span))? {
                // A key named again replaces its value, which can't be dropped, so a resource
                // it held is abandoned now, and isn't held any more (REFERENCE §10 rules 4
                // and 5; OPEN_QUESTIONS P5).
                Some(slot) => {
                    let old = map.replace(slot, value);
                    // Only a value held as a resource has anything to abandon, under the span
                    // of the expression that gave it.
                    if let Some(i) = std::mem::replace(&mut held_at[slot], at) {
                        let Owned::Value(_, owner) =
                            std::mem::replace(&mut self.owned[i].1, Owned::Value(Value::Unit, place))
                        else {
                            unreachable!("a literal holds its values")
                        };
                        if let unwind @ Unwind::Defect(_) = self.abandon(old, owner, Unwind::Return(Value::Unit)) {
                            return Err(unwind);
                        }
                    }
                }
                None => {
                    map.insert(hash, key, value);
                    held_at.push(at);
                }
            }
        }
        self.owned.truncate(mark);
        Ok(Value::Map(Arc::new(map)))
    }

    /// A call of `builtin`, which changes its receiver, a place, in place.
    #[inline(never)]
    fn change_call(
        &mut self,
        builtin: Builtin,
        receiver: ExprId,
        args: &[Arg],
        frame: &mut Frame,
        span: Span,
    ) -> Flow<Value> {
        // The receiver's indices are checked before the arguments run, as when a method that
        // doesn't change it reads it.
        let (root, path) = self.place(receiver, frame)?;
        let mark = self.owned.len();
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(self.held(arg.value, frame)?);
        }
        let mut lent = self.lend(&root, span)?;
        let base = base(frame, &root, &mut lent);
        let value = self.change(builtin, slot(base, &path)?, values, span)?;
        self.owned.truncate(mark);
        // Each record on the path has changed, as after an assignment.
        for depth in (0..path.len()).rev() {
            self.refine(at(base, &path[..depth])?, span)?;
        }
        Ok(value)
    }

    /// `for pat in xs` over a list or a map. The loop goes over the collection as it was when
    /// the loop started, so the body may change it (OPEN_QUESTIONS P5). A consuming loop,
    /// `for pat in take xs`, owns the collection, so it hands each element on rather than a
    /// copy when nothing else shares it.
    #[inline(never)]
    fn for_collection(&mut self, e: ExprId, pat: PatId, iter: ExprId, body: &Block, frame: &mut Frame) -> Flow<Value> {
        let consume = matches!(self.m.exprs[e].kind, ExprKind::For { consume: true, .. });
        if consume && self.p.decls.is_resource(self.p.ty(iter)) {
            return self.for_resources(e, pat, iter, body, frame);
        }
        match self.expr(iter, frame)? {
            Value::List(mut list) if consume && Arc::strong_count(&list) == 1 => {
                let items = std::mem::take(&mut Arc::get_mut(&mut list).expect("nothing else shares it").items);
                for item in items {
                    self.matches(pat, &item, frame)?;
                    self.own_bindings(pat);
                    drop(item);
                    if self.loop_body(e, body, frame)?.is_break() {
                        break;
                    }
                }
            }
            Value::List(list) => {
                for item in &list.items {
                    self.matches(pat, item, frame)?;
                    self.own_bindings(pat);
                    if self.loop_body(e, body, frame)?.is_break() {
                        break;
                    }
                }
            }
            Value::Map(map) => {
                for (key, value) in map.iter() {
                    self.matches(pat, &pair(key.clone(), value.clone()), frame)?;
                    self.own_bindings(pat);
                    if self.loop_body(e, body, frame)?.is_break() {
                        break;
                    }
                }
            }
            other => unreachable!("`for` goes over ranges and collections, not {other:?}"),
        }
        Ok(Value::Unit)
    }

    /// `for pat in take xs` over a collection of resources. The loop owns the elements it
    /// hasn't reached, after those its body owns, so a failure exit abandons them too
    /// (REFERENCE §10). The checker rejects a `break` out of it, which would drop them.
    #[inline(never)]
    fn for_resources(&mut self, e: ExprId, pat: PatId, iter: ExprId, body: &Block, frame: &mut Frame) -> Flow<Value> {
        let mut rest: Vec<Value> = match self.expr(iter, frame)? {
            Value::List(list) => list.items.clone(),
            Value::Map(map) => map.iter().map(|(key, value)| pair(key.clone(), value.clone())).collect(),
            other => unreachable!("a consuming loop goes over a list or a map, not {other:?}"),
        };
        rest.reverse();
        let at = self.owned.len();
        self.acquire(Owned::Rest(rest, self.m.exprs[iter].span));
        loop {
            let (_, Owned::Rest(rest, _)) = &mut self.owned[at] else {
                unreachable!("the loop's elements stay at its mark")
            };
            let Some(item) = rest.pop() else { break };
            self.matches(pat, &item, frame)?;
            self.own_bindings(pat);
            drop(item);
            if self.loop_body(e, body, frame)?.is_break() {
                break;
            }
        }
        self.owned.truncate(at);
        Ok(Value::Unit)
    }

    /// The fallback of an `else` form or a `check`.
    fn fallback(&mut self, fallback: &Fallback, frame: &mut Frame) -> Flow<Value> {
        match fallback {
            Fallback::Value(value) => self.expr(*value, frame),
            Fallback::Block(block) => self.block(block, frame),
        }
    }

    /// Hands the failure of call `e` to the `attempt`, `else` form or example that marks it,
    /// if one does.
    fn attempted(&self, e: ExprId, result: Flow<Value>) -> Flow<Value> {
        match (result, self.p.handler_of.get(e)) {
            (Err(Unwind::Fail(error)), Some(&handler)) => Err(Unwind::Attempted(handler, error)),
            (result, _) => result,
        }
    }

    /// Whether `value` matches `pat`. Binds the pattern's names as it goes, so after a failed
    /// match some of them may be set; nothing reads them then.
    fn matches(&mut self, pat: PatId, value: &Value, frame: &mut Frame) -> Flow<bool> {
        Ok(match &self.m.pats[pat].kind {
            PatKind::Wild => true,
            PatKind::Bind(_) => {
                let id = self.p.pat_local.get(pat).expect("bindings are resolved");
                frame[id.index()] = value.clone();
                true
            }
            PatKind::Lit(lit) => equal(value, &self.expr(*lit, frame)?),
            PatKind::Range { lo, hi, inclusive } => {
                let lo = self.expr(*lo, frame)?;
                let hi = self.expr(*hi, frame)?;
                let below = if *inclusive { BinOp::Le } else { BinOp::Lt };
                compare(BinOp::Ge, value, &lo) && compare(below, value, &hi)
            }
            PatKind::Ctor { fields, .. } => {
                let ctor = self.p.pat_ctor.get(pat).expect("constructor patterns are resolved");
                let Value::Adt(adt) = value else { unreachable!("constructor patterns match records and enums") };
                if adt.variant != ctor.variant {
                    return Ok(false);
                }
                for (field, i) in fields.iter().flatten().zip(ctor.fields.iter()) {
                    if !self.matches(field.pat, &adt.fields[i.index()], frame)? {
                        return Ok(false);
                    }
                }
                true
            }
            PatKind::Tuple(parts) => {
                let Value::Adt(adt) = value else { unreachable!("tuple patterns match tuples") };
                for (&part, value) in parts.iter().zip(adt.fields.iter()) {
                    if !self.matches(part, value, frame)? {
                        return Ok(false);
                    }
                }
                true
            }
        })
    }

    /// Runs one iteration of a loop body, turning jumps that target loop `e` into control flow.
    fn loop_body(&mut self, e: ExprId, body: &Block, frame: &mut Frame) -> Flow<LoopStep> {
        self.step(self.m.exprs[e].span)?;
        match self.block(body, frame) {
            Ok(_) => Ok(LoopStep::Next),
            Err(Unwind::Break(target)) if target == e => Ok(LoopStep::Break),
            Err(Unwind::Continue(target)) if target == e => Ok(LoopStep::Next),
            Err(other) => Err(other),
        }
    }

    fn arithmetic(&mut self, op: BinOp, a: Value, b: Value, span: Span) -> Flow<Value> {
        Ok(match (a, b) {
            (Value::Int(x, it), Value::Int(y, _)) => {
                let (kind, message) = match int_arithmetic(op, x, y, it) {
                    Ok(value) => return Ok(Value::Int(value, it)),
                    Err(problem) => problem,
                };
                return Err(defect(kind, message, span));
            }
            (Value::F64(x), Value::F64(y)) => Value::F64(match op {
                BinOp::Add => x + y,
                BinOp::Sub => x - y,
                BinOp::Mul => x * y,
                BinOp::Div => x / y,
                _ => unreachable!("floats have no `{}`", op.symbol()),
            }),
            (Value::F32(x), Value::F32(y)) => Value::F32(match op {
                BinOp::Add => x + y,
                BinOp::Sub => x - y,
                BinOp::Mul => x * y,
                BinOp::Div => x / y,
                _ => unreachable!("floats have no `{}`", op.symbol()),
            }),
            // A distinct type's operator works on the values it wraps, and the result is
            // checked against its refinement (REFERENCE §4.6; OPEN_QUESTIONS P5).
            (Value::Adt(a), Value::Adt(b)) => {
                let value = self.arithmetic(op, a.fields[0].clone(), b.fields[0].clone(), span)?;
                let wrapped = Value::Adt(Adt { def: a.def, variant: a.variant, fields: Arc::from([value]) });
                self.refine(&wrapped, span)?;
                wrapped
            }
            (a, b) => unreachable!("no arithmetic on {a:?} and {b:?}"),
        })
    }

    /// Unary `-`.
    fn negate(&mut self, value: Value, span: Span) -> Flow<Value> {
        Ok(match value {
            Value::Int(x, it) => {
                let negated = -x;
                if !it.contains(negated) {
                    return Err(defect(
                        DefectKind::IntegerOverflow,
                        format!("`{}` negation overflowed", it.name()),
                        span,
                    ));
                }
                Value::Int(negated, it)
            }
            Value::F64(x) => Value::F64(-x),
            Value::F32(x) => Value::F32(-x),
            Value::Adt(a) => {
                let value = self.negate(a.fields[0].clone(), span)?;
                let wrapped = Value::Adt(Adt { def: a.def, variant: a.variant, fields: Arc::from([value]) });
                self.refine(&wrapped, span)?;
                wrapped
            }
            other => unreachable!("cannot negate {other:?}"),
        })
    }

    /// Runs operation `method` of `iface` on native capability `cap`, which the runtime
    /// implements (REFERENCE §9.1). Its static type permitted the call (§9.2).
    fn operation(&mut self, cap: &Cap, iface: IfaceId, method: usize, args: &[Value]) -> Flow<Value> {
        let name = &*self.p.decls.iface(iface).methods[method].name;
        let fail = |stream: &str, err: std::io::Error| {
            // `std.io`'s `IoError`, whose one field is the message its `show` gives.
            let message = Value::Text(format!("cannot {stream}: {err}").into());
            Err(Unwind::Fail(Value::Adt(Adt {
                def: AdtId::IO_ERROR,
                variant: VariantIdx::RECORD,
                fields: Arc::from([message]),
            })))
        };
        match (cap, name, args) {
            (Cap::Stdout | Cap::Stderr, "write_line", [Value::Text(text)]) => {
                let (stream, out): (&str, &mut dyn Write) = match cap {
                    Cap::Stdout => ("write to stdout", &mut *self.stdout),
                    _ => ("write to stderr", &mut *self.stderr),
                };
                match writeln!(out, "{text}") {
                    Ok(()) => Ok(Value::Unit),
                    Err(err) => fail(stream, err),
                }
            }
            // A line without its `\n` or `\r\n`, as `Text.lines` gives it, and then `None`
            // (OPEN_QUESTIONS Q6).
            (Cap::Stdin, "read_line", []) => {
                let mut line = String::new();
                match self.stdin.read_line(&mut line) {
                    Ok(0) => Ok(option(None)),
                    Ok(_) => {
                        let line = line.strip_suffix('\n').map_or(&*line, |l| l.strip_suffix('\r').unwrap_or(l));
                        Ok(option(Some(Value::Text(line.into()))))
                    }
                    Err(err) => fail("read from stdin", err),
                }
            }
            (Cap::Dir(root), _, [Value::Adt(path), rest @ ..]) => {
                let Value::Text(text) = &path.fields[0] else { unreachable!("a `Path` holds its text") };
                let result = match (name, rest) {
                    ("read_text", []) => root.read_text(text).map(|text| Value::Text(text.into())),
                    ("write_text", [Value::Text(contents)]) => root.write_text(text, contents).map(|()| Value::Unit),
                    ("size", []) => root.size(text).map(|size| Value::Int(size.into(), IntTy::I64)),
                    ("list", []) => root.list(text).map(|paths| {
                        Value::List(Arc::new(ListValue { items: paths.iter().map(|p| path_value(p)).collect() }))
                    }),
                    ("create_dir", []) => root.create_dir(text).map(|()| Value::Unit),
                    ("remove", []) => root.remove(text).map(|()| Value::Unit),
                    _ => unreachable!("the checker resolves only the runtime's operations, not {name}"),
                };
                result.map_err(|failure| Unwind::Fail(fs_error(failure, &args[0])))
            }
            _ => unreachable!("the checker resolves only the runtime's operations, not {name}"),
        }
    }

    /// Runs a built-in method. `values` holds the receiver, then the arguments. A defect in a
    /// hand-written `eq` it runs is traced to `site`.
    fn builtin(&mut self, builtin: Builtin, values: Vec<Value>, site: Span) -> Flow<Value> {
        Ok(match (builtin, values.as_slice()) {
            (Builtin::Len, [Value::List(list)]) => Value::Int(list.items.len() as i128, IntTy::I64),
            (Builtin::Len, [Value::Map(map)]) => Value::Int(map.len() as i128, IntTy::I64),
            (Builtin::Len, [Value::Pool(pool)]) => Value::Int(pool.len as i128, IntTy::I64),
            (Builtin::Get, [Value::Pool(pool), Value::Handle(handle)]) => option(pool.lookup(handle).ok().cloned()),
            (Builtin::PoolNew, []) => Value::Pool(Arc::new(PoolValue::new(self.new_pool()))),
            // A copy of every slot, generations and all, in a pool of its own (STD.md).
            (Builtin::Duplicate, [Value::Pool(pool)]) => {
                let mut copy = PoolValue::clone(pool);
                copy.id = self.new_pool();
                Value::Pool(Arc::new(copy))
            }
            (Builtin::IsEmpty, [Value::List(list)]) => Value::Bool(list.items.is_empty()),
            (Builtin::IsEmpty, [Value::Map(map)]) => Value::Bool(map.is_empty()),
            (Builtin::Get, [Value::List(list), Value::Int(i, _)]) => {
                option(usize::try_from(*i).ok().and_then(|at| list.items.get(at)).cloned())
            }
            (Builtin::Get, [Value::Map(map), key]) => {
                option(self.find(map, key, site)?.map(|at| map.value_at(at).clone()))
            }
            (Builtin::ContainsKey, [Value::Map(map), key]) => Value::Bool(self.find(map, key, site)?.is_some()),
            (Builtin::Contains, [Value::List(list), value]) => {
                for item in &list.items {
                    if self.equal(item, value, site)? {
                        return Ok(Value::Bool(true));
                    }
                }
                Value::Bool(false)
            }
            (Builtin::Enumerate, [Value::List(list)]) => {
                let items = list.items.iter().enumerate();
                let items = items.map(|(i, item)| pair(Value::Int(i as i128, IntTy::I64), item.clone())).collect();
                Value::List(Arc::new(ListValue { items }))
            }
            (Builtin::Lines, [Value::Text(text)]) => {
                let items = lines(text).into_iter().map(|line| Value::Text(line.into())).collect();
                Value::List(Arc::new(ListValue { items }))
            }
            // A narrowed capability is the same object, with the same state (REFERENCE §9.2).
            (Builtin::Only | Builtin::Of, [cap @ (Value::Cap(_) | Value::Object(_))]) => cap.clone(),
            (Builtin::ByteLen, [Value::Text(text)]) => Value::Int(text.len() as i128, IntTy::I64),
            (Builtin::IsEmpty, [Value::Text(text)]) => Value::Bool(text.is_empty()),
            // Rust's `char::is_whitespace` is Unicode's `White_Space` (STD.md).
            (Builtin::Trim, [Value::Text(text)]) => Value::Text(text.trim_matches(char::is_whitespace).into()),
            (Builtin::SplitOnce, [Value::Text(text), Value::Text(sep)]) => {
                option(text.split_once(&**sep).map(|(before, after)| {
                    let fields = Arc::from([Value::Text(before.into()), Value::Text(after.into())]);
                    Value::Adt(Adt { def: AdtId::PAIR, variant: VariantIdx::RECORD, fields })
                }))
            }
            (Builtin::StartsWith, [Value::Text(text), Value::Text(prefix)]) => Value::Bool(text.starts_with(&**prefix)),
            (Builtin::StripPrefix, [Value::Text(text), Value::Text(prefix)]) => {
                option(text.strip_prefix(&**prefix).map(|rest| Value::Text(rest.into())))
            }
            (Builtin::Parse(it), [Value::Text(text)]) => match parse_int(text, it) {
                Ok(value) => Value::Int(value, it),
                Err(variant) => {
                    let error = Adt { def: AdtId::PARSE_ERROR, variant, fields: Arc::from([]) };
                    return Err(Unwind::Fail(Value::Adt(error)));
                }
            },
            // A conversion that keeps every value, or an integer to the nearest float, ties
            // to even, as Rust's `as` rounds it (STD.md).
            (Builtin::Convert(Num::Int(it)), [Value::Int(x, _)]) => Value::Int(*x, it),
            (Builtin::Convert(Num::Float(FloatTy::F64)), [Value::Int(x, _)]) => Value::F64(*x as f64),
            (Builtin::Convert(Num::Float(FloatTy::F64)), [Value::F32(x)]) => Value::F64(f64::from(*x)),
            (Builtin::Convert(Num::Float(FloatTy::F32)), [Value::Int(x, _)]) => Value::F32(*x as f32),
            (Builtin::Convert(Num::Float(_)), [value @ (Value::F64(_) | Value::F32(_))]) => value.clone(),
            (Builtin::TryFrom(it), [Value::Int(x, _)]) if it.contains(*x) => Value::Int(*x, it),
            (Builtin::TryFrom(_), [Value::Int(..)]) => return Err(conversion_error(CONVERSION_OUT_OF_RANGE)),
            (Builtin::WrappingFrom(it), [Value::Int(x, _)]) => Value::Int(wrap(*x, it), it),
            (Builtin::ToInt, [x, Value::Adt(rounding)]) => {
                let x = match x {
                    Value::F64(x) => *x,
                    Value::F32(x) => f64::from(*x),
                    other => unreachable!("`to_int` rounds a float, not {other:?}"),
                };
                if x.is_nan() {
                    return Err(conversion_error(CONVERSION_NOT_A_NUMBER));
                }
                // As `Rounding` declares its variants (STD.md).
                let rounded = match rounding.variant.index() {
                    0 => x.trunc(),
                    1 => x.floor(),
                    2 => x.ceil(),
                    3 => x.round_ties_even(),
                    _ => x.round(),
                };
                // `Int` holds -2^63 up to 2^63 - 1, and both bounds are exact as floats.
                let bound = 2f64.powi(63);
                if !(-bound..bound).contains(&rounded) {
                    return Err(conversion_error(CONVERSION_OUT_OF_RANGE));
                }
                Value::Int(rounded as i128, IntTy::I64)
            }
            (builtin, values) => unreachable!("{builtin:?} does not apply to {values:?}"),
        })
    }

    /// Runs a built-in method that changes its receiver, `place`, with arguments `values`.
    fn change(&mut self, builtin: Builtin, place: &mut Value, values: Vec<Value>, site: Span) -> Flow<Value> {
        let mut values = values.into_iter();
        Ok(match (builtin, place) {
            (Builtin::Push, Value::List(list)) => {
                Arc::make_mut(list).items.extend(values);
                Value::Unit
            }
            (Builtin::Pop, Value::List(list)) => option(Arc::make_mut(list).items.pop()),
            (Builtin::Set, Value::Map(map)) => {
                let (Some(key), Some(value)) = (values.next(), values.next()) else { unreachable!("`set` takes two") };
                self.set(Arc::make_mut(map), key, value, site)?.map_or_else(|| option(None), |old| option(Some(old)))
            }
            (Builtin::Insert, Value::Pool(pool)) => {
                let value = values.next().expect("`insert` takes a value");
                self.generations += 1;
                Value::Handle(Arc::make_mut(pool).insert(value, self.generations))
            }
            (Builtin::Remove, Value::Pool(pool)) => {
                let Some(Value::Handle(handle)) = values.next() else { unreachable!("`remove` takes a handle") };
                // A stale handle removes nothing, so the pool isn't copied for it.
                match pool.lookup(&handle) {
                    Ok(_) => option(Arc::make_mut(pool).remove(&handle)),
                    Err(_) => option(None),
                }
            }
            // `update` takes the element out and passes it to `change`, which owns it while it
            // runs, so a defect there abandons it and leaves the slot empty, as if removed
            // (OPEN_QUESTIONS P5).
            (Builtin::Update, Value::Pool(pool)) => {
                let (Some(Value::Handle(handle)), Some(Value::Fn(change))) = (values.next(), values.next()) else {
                    unreachable!("`update` takes a handle and a function")
                };
                let Some(element) = pool.lookup(&handle).is_ok().then(|| Arc::make_mut(pool).remove(&handle)).flatten()
                else {
                    return Ok(Value::Bool(false));
                };
                let changed = self.call_value(&change, vec![element], site)?;
                Arc::make_mut(pool).restore(&handle, changed);
                Value::Bool(true)
            }
            (Builtin::Remove, Value::Map(map)) => {
                let key = values.next().expect("`remove` takes a key");
                match self.find(map, &key, site)? {
                    Some(at) => option(Some(Arc::make_mut(map).remove(at))),
                    None => option(None),
                }
            }
            (builtin, place) => unreachable!("{builtin:?} does not change {place:?}"),
        })
    }

    /// A new pool identity.
    fn new_pool(&mut self) -> u64 {
        self.pools += 1;
        self.pools
    }

    /// Where `key` is in `map`, comparing keys with `==`.
    fn find(&mut self, map: &MapValue, key: &Value, site: Span) -> Flow<Option<usize>> {
        let hash = hash_value(key, &self.p.decls);
        map.find(key, hash, &mut |a, b| self.equal(a, b, site))
    }

    /// Maps `key` to `value` in `map`, and returns the value it replaces. A key set again
    /// keeps its place (REFERENCE §4.2).
    fn set(&mut self, map: &mut MapValue, key: Value, value: Value, site: Span) -> Flow<Option<Value>> {
        let hash = hash_value(&key, &self.p.decls);
        Ok(match map.find(&key, hash, &mut |a, b| self.equal(a, b, site))? {
            Some(at) => Some(map.replace(at, value)),
            None => {
                map.insert(hash, key, value);
                None
            }
        })
    }

    /// Runs method `method` of `iface` as the implementation for the receiver's type does.
    /// Values describe themselves, so the receiver tells which one, also in generic code
    /// (REFERENCE §4.9). `values` holds the receiver, then the arguments.
    fn dispatch(&mut self, iface: IfaceId, method: usize, values: Vec<Value>, site: Span) -> Flow<Value> {
        match (iface, values.as_slice()) {
            (IfaceId::SHOW, [value]) => Ok(Value::Text(self.show(value, site)?.into())),
            (IfaceId::EQ, [a, b]) => Ok(Value::Bool(self.equal(a, b, site)?)),
            // Only a type that implements `Ord` has `cmp`, and a float doesn't (Q22).
            (IfaceId::ORD, [a, b]) => {
                Ok(ordering_value(self.ordering(a, b, site)?.expect("values of an `Ord` type are ordered")))
            }
            // Every resource implements `Abandon`, and an aggregate abandons what it holds
            // (REFERENCE §10 rule 4).
            (IfaceId::ABANDON, [value]) if !matches!(value, Value::Adt(adt) if self.p.decls.adt(adt.def).resource_base) =>
            {
                let value = values.into_iter().next().expect("one value");
                match self.abandon(value, site, Unwind::Return(Value::Unit)) {
                    Unwind::Return(_) => Ok(Value::Unit),
                    unwind => Err(unwind),
                }
            }
            _ => {
                let key = impl_key(&values[0]);
                let f = self.p.decls.impl_method(iface, key, method).expect("the checker found an implementation");
                self.call(f, values, site)
            }
        }
    }

    /// The `Show` text of `value`. A record or enum whose type implements `Show` by hand is
    /// written by its `show`, also inside a value whose `Show` is derived (OPEN_QUESTIONS P5).
    /// A defect in it is traced to `site`.
    fn show(&mut self, value: &Value, site: Span) -> Flow<String> {
        let p = self.p;
        write_value(value, false, &p.decls, |value| {
            let Some(f) = hand_written(value, IfaceId::SHOW, &p.decls) else { return Ok(None) };
            match self.call(f, vec![value.clone()], site)? {
                Value::Text(text) => Ok(Some(text)),
                other => unreachable!("`show` returns Text, not {other:?}"),
            }
        })
    }

    /// How `a` and `b` are ordered, as `<` and `cmp` order them. A record or enum whose type
    /// implements `Ord` by hand is ordered by its `cmp`, also inside a value whose `Ord` is
    /// derived (OPEN_QUESTIONS P5). A defect in it is traced to `site`.
    fn ordering(&mut self, a: &Value, b: &Value, site: Span) -> Flow<Option<Ordering>> {
        let p = self.p;
        order_with(a, b, &mut |a, b| {
            let Some(f) = hand_written(a, IfaceId::ORD, &p.decls) else { return Ok(None) };
            match self.call(f, vec![a.clone(), b.clone()], site)? {
                Value::Adt(adt) if adt.def == AdtId::ORDERING => Ok(Some(match adt.variant.index() {
                    0 => Ordering::Less,
                    1 => Ordering::Equal,
                    _ => Ordering::Greater,
                })),
                other => unreachable!("`cmp` returns an Ordering, not {other:?}"),
            }
        })
    }

    /// `==`. A record or enum whose type implements `Eq` by hand is compared by its `eq`, also
    /// inside a value whose `Eq` is derived (OPEN_QUESTIONS P5). A defect in it is traced to
    /// `site`.
    fn equal(&mut self, a: &Value, b: &Value, site: Span) -> Flow<bool> {
        let p = self.p;
        equal_with(a, b, &mut |a, b| {
            let Some(f) = hand_written(a, IfaceId::EQ, &p.decls) else { return Ok(None) };
            match self.call(f, vec![a.clone(), b.clone()], site)? {
                Value::Bool(same) => Ok(Some(same)),
                other => unreachable!("`eq` returns Bool, not {other:?}"),
            }
        })
    }
}

/// The tuple `(a, b)`.
fn pair(a: Value, b: Value) -> Value {
    Value::Adt(Adt { def: AdtId::PAIR, variant: VariantIdx::RECORD, fields: Arc::from([a, b]) })
}

/// The lines of `text` without their `\n` or `\r\n` endings. A final line ending doesn't
/// start an empty line (STD.md), and a `\r` without a `\n` after it ends nothing
/// (OPEN_QUESTIONS P5).
fn lines(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        let Some(at) = rest.find('\n') else {
            out.push(rest);
            break;
        };
        let line = &rest[..at];
        out.push(line.strip_suffix('\r').unwrap_or(line));
        rest = &rest[at + 1..];
    }
    out
}

/// `Some(value)`, or `None`.
/// `std.fs`'s `Path` holding `text`.
fn path_value(text: &str) -> Value {
    Value::Adt(Adt { def: AdtId::PATH, variant: VariantIdx::RECORD, fields: Arc::from([Value::Text(text.into())]) })
}

/// `std.fs`'s `FsError` for an operation on `path` that failed with `failure`. Its variants
/// are `NotFound`, `PermissionDenied` and `Other`, in that order (STD.md).
fn fs_error(failure: fs::FsFailure, path: &Value) -> Value {
    let (variant, field) = match failure {
        fs::FsFailure::NotFound => (0, path.clone()),
        fs::FsFailure::PermissionDenied => (1, path.clone()),
        fs::FsFailure::Other(message) => (2, Value::Text(message.into())),
    };
    Value::Adt(Adt { def: AdtId::FS_ERROR, variant: VariantIdx::new(variant), fields: Arc::from([field]) })
}

fn option(value: Option<Value>) -> Value {
    let (variant, fields): (VariantIdx, Arc<[Value]>) = match value {
        Some(value) => (VariantIdx::SOME, Arc::from([value])),
        None => (VariantIdx::NONE, Arc::from([])),
    };
    Value::Adt(Adt { def: AdtId::OPTION, variant, fields })
}

/// The variants of `ParseError`, in declaration order (STD.md).
const PARSE_EMPTY: VariantIdx = VariantIdx::new(0);
const PARSE_INVALID: VariantIdx = VariantIdx::new(1);
const PARSE_OUT_OF_RANGE: VariantIdx = VariantIdx::new(2);

/// `parse` on integer type `it`: an optional `+` or `-`, then one or more ASCII digits
/// (STD.md). Text of that form whose value doesn't fit is out of range; any other text is
/// invalid, so the form is checked first (OPEN_QUESTIONS P5).
/// `std.num`'s `ConversionError.OutOfRange` and `NotANumber`, as STD.md declares them.
const CONVERSION_OUT_OF_RANGE: VariantIdx = VariantIdx::new(0);
const CONVERSION_NOT_A_NUMBER: VariantIdx = VariantIdx::new(1);

/// A failure with `std.num`'s `ConversionError` variant `variant`.
fn conversion_error(variant: VariantIdx) -> Unwind {
    Unwind::Fail(Value::Adt(Adt { def: AdtId::CONVERSION_ERROR, variant, fields: Arc::from([]) }))
}

/// The value of `it` with the low bits of `x`, as two's complement keeps them.
fn wrap(x: i128, it: IntTy) -> i128 {
    let span = it.max() - it.min() + 1;
    (x - it.min()).rem_euclid(span) + it.min()
}

fn parse_int(text: &str, it: IntTy) -> Result<i128, VariantIdx> {
    if text.is_empty() {
        return Err(PARSE_EMPTY);
    }
    let (negative, digits) = match text.as_bytes()[0] {
        b'-' => (true, &text[1..]),
        b'+' => (false, &text[1..]),
        _ => (false, text),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(PARSE_INVALID);
    }
    let mut value: i128 = 0;
    for b in digits.bytes() {
        let digit = i128::from(b - b'0');
        let next =
            value.checked_mul(10).and_then(|v| if negative { v.checked_sub(digit) } else { v.checked_add(digit) });
        value = next.ok_or(PARSE_OUT_OF_RANGE)?;
    }
    if it.contains(value) { Ok(value) } else { Err(PARSE_OUT_OF_RANGE) }
}

/// The type a value's `impl` is for.
fn impl_key(value: &Value) -> ImplKey {
    match value {
        Value::Int(_, it) => ImplKey::Int(*it),
        Value::F64(_) => ImplKey::Float(FloatTy::F64),
        Value::F32(_) => ImplKey::Float(FloatTy::F32),
        Value::Bool(_) => ImplKey::Bool,
        Value::Char(_) => ImplKey::Char,
        Value::Text(_) => ImplKey::Text,
        Value::Unit => ImplKey::Unit,
        Value::Adt(adt) => ImplKey::Adt(adt.def),
        Value::Object(object) => ImplKey::Adt(object.def),
        // A module may implement its interface for a standard type, as `List[Int]` (§4.9).
        Value::List(_) => ImplKey::Adt(AdtId::LIST),
        Value::Map(_) => ImplKey::Adt(AdtId::MAP),
        Value::Pool(_) => ImplKey::Adt(AdtId::POOL),
        Value::Handle(_) => ImplKey::Adt(AdtId::HANDLE),
        Value::Cap(_) | Value::Fn(_) => unreachable!("capabilities and function values implement no interface"),
    }
}

/// The function that implements the one method of `iface` for `value`'s record or enum, when
/// an `impl` declares it rather than `derives`.
fn hand_written(value: &Value, iface: IfaceId, decls: &Decls) -> Option<FnId> {
    let def = match value {
        Value::Adt(adt) => adt.def,
        Value::Object(object) => object.def,
        _ => return None,
    };
    decls.impl_method(iface, ImplKey::Adt(def), 0)
}

/// A step of a place: a record's field, or a list's element and where it is indexed.
#[derive(Clone)]
enum Step {
    Field(FieldIdx),
    Index(i128, Span),
}

impl Step {
    /// What tells two steps apart: whether it is an element, and its field or index.
    fn key(&self) -> (bool, i128) {
        match self {
            Step::Field(i) => (false, i.index() as i128),
            Step::Index(i, _) => (true, *i),
        }
    }
}

/// How a call takes its arguments: whether its receiver is `inout self`, and whether it can
/// fail, so that its `inout` arguments are copied in rather than taken out, and what it
/// calls, if it is a declared function or an interface's method.
#[derive(Clone, Copy, Default)]
struct Shape {
    inout_self: bool,
    can_fail: bool,
    f: Option<FnId>,
    /// An interface's method `j`, with the expression that gives `self` and whether that is
    /// the call's first argument, as in `Iface.method(x)`.
    method: Option<(IfaceId, usize, ExprId, bool)>,
    /// The expression that gives the function value it calls.
    value: Option<ExprId>,
}

/// An `inout` argument or receiver: the index of its value among a call's, and its place.
struct Inout {
    index: usize,
    root: Root,
    path: Vec<Step>,
    span: Span,
    /// It keeps the callee's changes whether or not the call succeeds (REFERENCE §5.4).
    partial: bool,
    /// The `state` field it is in, lent out of its object for the call, which dropping puts
    /// back.
    lent: Option<Lent>,
    /// The index of the place before it in the call that holds its lent `state` field.
    shares: Option<usize>,
}

/// Where a place is rooted: a local of the running call, or a `state` field of a `cap
/// record`'s object, which every copy of the object shares (REFERENCE §9.6).
#[derive(Clone)]
enum Root {
    Local(LocalId),
    State(Arc<CapState>, AdtId, FieldIdx),
}

/// What tells two places apart: their roots, and the keys of their steps.
type PlaceKey = ((usize, usize), Vec<(bool, i128)>);

impl Root {
    /// What tells two roots apart.
    fn key(&self) -> (usize, usize) {
        match self {
            Root::Local(id) => (0, id.index()),
            Root::State(state, _, i) => (Arc::as_ptr(state) as usize, i.index()),
        }
    }
}

/// A `state` field lent out of its object while it is changed in place. Dropping it puts
/// the value back, however the change ends.
struct Lent {
    state: Arc<CapState>,
    field: usize,
    value: Value,
}

impl Drop for Lent {
    fn drop(&mut self) {
        let mut state = self.state.lock();
        state.values[self.field] = std::mem::replace(&mut self.value, Value::Unit);
        state.lent[self.field] = false;
    }
}

/// The value a place under `root` starts from: the local's, or the lent `state` field's.
fn base<'v>(frame: &'v mut Frame, root: &Root, lent: &'v mut Option<Lent>) -> &'v mut Value {
    match (root, lent) {
        (Root::Local(id), _) => &mut frame[id.index()],
        (Root::State(..), Some(lent)) => &mut lent.value,
        (Root::State(..), None) => unreachable!("a `state` root is lent before it is changed"),
    }
}

/// The value an `inout` argument's place starts from: its local's, or its lent `state`
/// field's.
fn lent_base<'v>(frame: &'v mut Frame, place: &'v mut Inout) -> &'v mut Value {
    match (&place.root, &mut place.lent) {
        (Root::Local(id), _) => &mut frame[id.index()],
        (Root::State(..), Some(lent)) => &mut lent.value,
        (Root::State(..), None) => unreachable!("a `state` root is lent for the call"),
    }
}

/// The value at `path` inside `value`. An index outside its list is a defect.
fn at<'v>(mut value: &'v Value, path: &[Step]) -> Flow<&'v Value> {
    for step in path {
        value = match (step, value) {
            (Step::Field(i), Value::Adt(adt)) => &adt.fields[i.index()],
            (Step::Field(i), Value::Object(object)) => &object.fields[i.index()],
            (Step::Index(i, span), Value::List(list)) => &list.items[element_at(*i, list.items.len(), *span)?],
            _ => unreachable!("paths go through records and lists"),
        };
    }
    Ok(value)
}

/// The slot `path` names inside `value`. Each record and list on the way is copied first if
/// it is shared, so the write changes no other copy (REFERENCE §5.1). An index outside its
/// list is a defect.
fn slot<'v>(mut value: &'v mut Value, path: &[Step]) -> Flow<&'v mut Value> {
    for step in path {
        value = match (step, value) {
            (Step::Field(i), Value::Adt(adt)) => &mut Arc::make_mut(&mut adt.fields)[i.index()],
            (Step::Field(i), Value::Object(object)) => &mut Arc::make_mut(&mut Arc::make_mut(object).fields)[i.index()],
            (Step::Index(i, span), Value::List(list)) => {
                let at = element_at(*i, list.items.len(), *span)?;
                &mut Arc::make_mut(list).items[at]
            }
            _ => unreachable!("paths go through records and lists"),
        };
    }
    Ok(value)
}

/// Where index `i` is in a list of `len` elements, or a defect at `span` if it is outside.
fn element_at(i: i128, len: usize, span: Span) -> Flow<usize> {
    match usize::try_from(i) {
        Ok(at) if at < len => Ok(at),
        _ => Err(defect(
            DefectKind::IndexOutOfBounds,
            format!("index {i} is out of bounds for a list of length {len}"),
            span,
        )),
    }
}

enum LoopStep {
    Next,
    Break,
}

impl LoopStep {
    fn is_break(&self) -> bool {
        matches!(self, LoopStep::Break)
    }
}

/// Integer arithmetic where overflow and division by zero are defects (REFERENCE §12.1).
/// `/` truncates toward zero and `%` takes the sign of the dividend, as Rust's operators do.
fn int_arithmetic(op: BinOp, x: i128, y: i128, it: IntTy) -> Result<i128, (DefectKind, String)> {
    let result = match op {
        BinOp::Add => x.checked_add(y),
        BinOp::Sub => x.checked_sub(y),
        BinOp::Mul => x.checked_mul(y),
        BinOp::Div | BinOp::Rem if y == 0 => {
            return Err((DefectKind::DivisionByZero, format!("`{}` by zero", op.symbol())));
        }
        BinOp::Div => x.checked_div(y),
        BinOp::Rem => x.checked_rem(y),
        _ => unreachable!("`{}` is not arithmetic", op.symbol()),
    };
    match result {
        Some(value) if it.contains(value) => Ok(value),
        _ => {
            let what = match op {
                BinOp::Add => "addition",
                BinOp::Sub => "subtraction",
                BinOp::Mul => "multiplication",
                BinOp::Div => "division",
                _ => "remainder",
            };
            Err((DefectKind::IntegerOverflow, format!("`{}` {what} overflowed: {x} {} {y}", it.name(), op.symbol())))
        }
    }
}

/// Ordering of two values of the same type, as `Ord` gives it. Floats follow IEEE, so NaN is
/// unordered with everything; text compares by code point, which UTF-8 byte order preserves.
fn compare(op: BinOp, a: &Value, b: &Value) -> bool {
    holds(op, order(a, b))
}

/// Whether comparison `op` holds of two values in `ordering`, where `None` is unordered.
fn holds(op: BinOp, ordering: Option<Ordering>) -> bool {
    match op {
        BinOp::Lt => ordering == Some(Ordering::Less),
        BinOp::Le => matches!(ordering, Some(Ordering::Less | Ordering::Equal)),
        BinOp::Gt => ordering == Some(Ordering::Greater),
        BinOp::Ge => matches!(ordering, Some(Ordering::Greater | Ordering::Equal)),
        _ => unreachable!("`{}` is not an ordering", op.symbol()),
    }
}

/// [`order_with`] for values with no `Ord` written by hand.
fn order(a: &Value, b: &Value) -> Option<Ordering> {
    match order_with(a, b, &mut |_, _| Ok::<_, Infallible>(None)) {
        Ok(ordering) => ordering,
        Err(never) => match never {},
    }
}

/// Decides the order of a pair of records or enums whose `cmp` is written by hand, and `None`
/// for any other pair.
type HandWrittenOrd<'a, E> = dyn FnMut(&Value, &Value) -> Result<Option<Ordering>, E> + 'a;

/// The derived `Ord` orders a record or enum by variant in declaration order, then field by
/// field in declaration order (STD.md), where `hand_written` decides a pair of records or
/// enums it returns `Some` for. Lists and tuples are ordered element by element from the
/// left, so a prefix comes first, and maps by their entries sorted by key (OPEN_QUESTIONS
/// P5). Like [`equal`], it keeps what is still to compare in a list of its own, so no value
/// is too deep for the native stack.
fn order_with<E>(a: &Value, b: &Value, hand_written: &mut HandWrittenOrd<'_, E>) -> Result<Option<Ordering>, E> {
    /// What is left to compare, last first.
    enum Work<'v> {
        Pair(&'v Value, &'v Value),
        /// Two lists' lengths, compared once their common elements are equal.
        Lengths(usize, usize),
        /// Two maps' entries sorted by key, from entry `.2` on.
        Entries(Vec<(&'v Value, &'v Value)>, Vec<(&'v Value, &'v Value)>, usize),
    }
    let mut work = vec![Work::Pair(a, b)];
    while let Some(next) = work.pop() {
        let ordering = match next {
            Work::Pair(a, b) => match (a, b) {
                (Value::Int(x, _), Value::Int(y, _)) => x.partial_cmp(y),
                (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
                (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
                (Value::Bool(x), Value::Bool(y)) => x.partial_cmp(y),
                (Value::Char(x), Value::Char(y)) => x.partial_cmp(y),
                (Value::Text(x), Value::Text(y)) => x.partial_cmp(y),
                (Value::Unit, Value::Unit) => Some(Ordering::Equal),
                (a @ Value::Adt(x), b @ Value::Adt(y)) => match hand_written(a, b)? {
                    Some(ordering) => Some(ordering),
                    None => {
                        // Pushed in reverse, so the first field is compared first, with all it
                        // holds.
                        work.extend(x.fields.iter().zip(y.fields.iter()).rev().map(|(a, b)| Work::Pair(a, b)));
                        x.variant.index().partial_cmp(&y.variant.index())
                    }
                },
                // A `cap record` derives nothing, so it is ordered by its own `cmp`.
                (a @ Value::Object(_), b @ Value::Object(_)) => match hand_written(a, b)? {
                    Some(ordering) => Some(ordering),
                    None => unreachable!("the checker found `Ord` for {a:?}"),
                },
                (Value::List(x), Value::List(y)) => {
                    work.push(Work::Lengths(x.items.len(), y.items.len()));
                    work.extend(x.items.iter().zip(y.items.iter()).rev().map(|(a, b)| Work::Pair(a, b)));
                    Some(Ordering::Equal)
                }
                (Value::Map(x), Value::Map(y)) => {
                    work.push(Work::Entries(sorted_entries(x, hand_written)?, sorted_entries(y, hand_written)?, 0));
                    Some(Ordering::Equal)
                }
                (a, b) => unreachable!("cannot order {a:?} and {b:?}"),
            },
            Work::Lengths(x, y) => x.partial_cmp(&y),
            Work::Entries(xs, ys, i) if i < xs.len().min(ys.len()) => {
                let ((xk, xv), (yk, yv)) = (xs[i], ys[i]);
                work.push(Work::Entries(xs, ys, i + 1));
                work.push(Work::Pair(xv, yv));
                work.push(Work::Pair(xk, yk));
                Some(Ordering::Equal)
            }
            Work::Entries(xs, ys, _) => xs.len().partial_cmp(&ys.len()),
        };
        if ordering != Some(Ordering::Equal) {
            return Ok(ordering);
        }
    }
    Ok(Some(Ordering::Equal))
}

/// The prelude's `Ordering` value for `ordering` (STD.md).
fn ordering_value(ordering: Ordering) -> Value {
    let variant = match ordering {
        Ordering::Less => 0,
        Ordering::Equal => 1,
        Ordering::Greater => 2,
    };
    Value::Adt(Adt { def: AdtId::ORDERING, variant: VariantIdx::new(variant), fields: Arc::from([]) })
}

/// A map's entries sorted by key, as the keys' `Ord` orders them, written by hand or not. Its
/// keys implement `Ord` when the map does, and none is a float, so they are ordered. A `cmp`
/// written by hand need not be a total order, so this is a merge sort of its own, which keeps
/// equal keys in insertion order and never panics, as `sort_by` may for such an order.
fn sorted_entries<'v, E>(
    map: &'v MapValue,
    hand_written: &mut HandWrittenOrd<'_, E>,
) -> Result<Vec<(&'v Value, &'v Value)>, E> {
    let mut entries: Vec<(&Value, &Value)> = map.iter().collect();
    let mut width = 1;
    while width < entries.len() {
        let mut merged = Vec::with_capacity(entries.len());
        for run in entries.chunks(2 * width) {
            let (mut left, mut right) = run.split_at(width.min(run.len()));
            while let (Some(&l), Some(&r)) = (left.first(), right.first()) {
                if order_with(r.0, l.0, hand_written)? == Some(Ordering::Less) {
                    merged.push(r);
                    right = &right[1..];
                } else {
                    merged.push(l);
                    left = &left[1..];
                }
            }
            merged.extend_from_slice(left);
            merged.extend_from_slice(right);
        }
        entries = merged;
        width *= 2;
    }
    Ok(entries)
}

/// `==` as built into scalars and derived for records and enums, which are equal when their
/// variants and every field are. Floats follow IEEE, so NaN is unequal to everything.
fn equal(a: &Value, b: &Value) -> bool {
    match equal_with(a, b, &mut |_, _| Ok::<_, Infallible>(None)) {
        Ok(same) => same,
        Err(never) => match never {},
    }
}

/// Decides `==` for a pair of records or enums whose `eq` is written by hand, and `None` for
/// any other pair.
type HandWrittenEq<'a, E> = dyn FnMut(&Value, &Value) -> Result<Option<bool>, E> + 'a;

/// `==`, where `hand_written` decides a pair of records or enums it returns `Some` for. Lists
/// are equal when their elements are, in order, and maps when they map the same keys to equal
/// values, in any order (OPEN_QUESTIONS P5). It walks nested values with a list of its own
/// rather than recursion, so no value is too deep for the native stack. Only finding a key
/// among several with its hash compares keys by recursion.
fn equal_with<E>(a: &Value, b: &Value, hand_written: &mut HandWrittenEq<'_, E>) -> Result<bool, E> {
    let mut pairs = vec![(a, b)];
    while let Some(pair) = pairs.pop() {
        let same = match pair {
            (Value::Int(x, _), Value::Int(y, _)) => x == y,
            (Value::F64(x), Value::F64(y)) => x == y,
            (Value::F32(x), Value::F32(y)) => x == y,
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Char(x), Value::Char(y)) => x == y,
            (Value::Text(x), Value::Text(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Handle(x), Value::Handle(y)) => x == y,
            (a @ Value::Adt(x), b @ Value::Adt(y)) => match hand_written(a, b)? {
                Some(same) => same,
                None => {
                    // Reversed, so the first field is compared first and a later field's
                    // hand-written `eq` doesn't run once one differs (OPEN_QUESTIONS P5).
                    pairs.extend(x.fields.iter().zip(y.fields.iter()).rev());
                    x.variant == y.variant
                }
            },
            // A `cap record` derives nothing, so it is compared by its own `eq`.
            (a @ Value::Object(_), b @ Value::Object(_)) => match hand_written(a, b)? {
                Some(same) => same,
                None => unreachable!("the checker found `Eq` for {a:?}"),
            },
            (Value::List(x), Value::List(y)) => {
                pairs.extend(x.items.iter().zip(y.items.iter()).rev());
                x.items.len() == y.items.len()
            }
            (Value::Map(x), Value::Map(y)) => {
                let mut same = x.len() == y.len();
                for (hash, key, value) in x.entries.iter().flatten() {
                    if !same {
                        break;
                    }
                    // A key with the only hash of its kind in `y` is equal to that key or to
                    // none, so the two are compared with the rest, with no native stack.
                    match y.candidates(*hash) {
                        [] => same = false,
                        &[at] => {
                            pairs.push((value, y.value_at(at)));
                            pairs.push((key, y.key_at(at)));
                        }
                        _ => match y.find(key, *hash, &mut |p, q| equal_with(p, q, hand_written))? {
                            Some(at) => pairs.push((value, y.value_at(at))),
                            None => same = false,
                        },
                    }
                }
                same
            }
            (a, b) => unreachable!("cannot compare {a:?} and {b:?}"),
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// A hash of a map's key that agrees with `==`: equal keys hash alike (STD.md). A record or
/// enum with a hand-written `eq` hashes as its type alone, since its `eq` may call any two of
/// its values equal, and a map by its keys. Like [`equal`], it keeps the parts still to hash
/// in a list of its own.
fn hash_value(value: &Value, decls: &Decls) -> u64 {
    let mut hasher = DefaultHasher::new();
    let mut parts = vec![value];
    while let Some(value) = parts.pop() {
        std::mem::discriminant(value).hash(&mut hasher);
        match value {
            Value::Int(x, _) => x.hash(&mut hasher),
            Value::F64(x) => x.to_bits().hash(&mut hasher),
            Value::F32(x) => x.to_bits().hash(&mut hasher),
            Value::Bool(x) => x.hash(&mut hasher),
            Value::Char(x) => x.hash(&mut hasher),
            Value::Text(x) => x.hash(&mut hasher),
            Value::Unit | Value::Cap(_) => {}
            // A `cap record` has a hand-written `eq` if any, so it hashes as its type alone.
            Value::Object(object) => object.def.index().hash(&mut hasher),
            Value::Handle(handle) => handle.hash(&mut hasher),
            Value::Pool(_) => unreachable!("a pool implements no `Hash`"),
            Value::Fn(_) => unreachable!("a function value implements no `Hash`"),
            Value::Adt(adt) => {
                adt.def.index().hash(&mut hasher);
                if decls.impl_method(IfaceId::EQ, ImplKey::Adt(adt.def), 0).is_none() {
                    adt.variant.index().hash(&mut hasher);
                    parts.extend(adt.fields.iter().rev());
                }
            }
            Value::List(list) => {
                list.items.len().hash(&mut hasher);
                parts.extend(list.items.iter().rev());
            }
            // Equal maps have the same keys, so their keys' hashes, summed since `==` ignores
            // their order, agree with `==`. Leaving out the values keeps a map whose values
            // nest deeply from taking native stack per level.
            Value::Map(map) => {
                map.len().hash(&mut hasher);
                let keys = map.entries.iter().flatten().map(|(hash, _, _)| *hash);
                keys.fold(0u64, u64::wrapping_add).hash(&mut hasher);
            }
        }
    }
    hasher.finish()
}

/// The `Show` text of a value as derived and built in. Floats print the shortest text that
/// reads back as the same value, always with a fraction or exponent, such as `1.0`, `0.1` and
/// `1e21`. A record or enum writes the expression that builds it, as a derived `Show` does
/// (STD.md).
pub fn show(value: &Value, decls: &Decls) -> String {
    match write_value(value, false, decls, |_| Ok::<_, Infallible>(None)) {
        Ok(text) => text,
        Err(never) => match never {},
    }
}

/// The `debug` text of a value: like `show`, but text and chars are quoted and written with
/// Proviso's escapes, so the output reads as a literal. A record is written as a derived
/// `Show` writes it, whether or not it derives or implements `Show` (OPEN_QUESTIONS P5), so
/// `debug` and defect messages run no code of the program's.
fn debug_repr(value: &Value, decls: &Decls) -> String {
    match write_value(value, true, decls, |_| Ok::<_, Infallible>(None)) {
        Ok(text) => text,
        Err(never) => match never {},
    }
}

/// Writes `value` as `show` does, or as `debug` does when `quoted`. A record's fields are
/// always quoted. A record or enum that `hand_written` returns text for is written as that
/// text. Like [`equal`], it keeps the parts still to write in a list of its own, so no value
/// is too deep for the native stack.
fn write_value<E>(
    value: &Value,
    quoted: bool,
    decls: &Decls,
    mut hand_written: impl FnMut(&Value) -> Result<Option<Arc<str>>, E>,
) -> Result<String, E> {
    enum Part<'v> {
        Value(&'v Value, bool),
        Text(&'v str),
    }
    let mut out = String::new();
    let mut parts = vec![Part::Value(value, quoted)];
    while let Some(part) = parts.pop() {
        let (value, quoted) = match part {
            Part::Text(text) => {
                out.push_str(text);
                continue;
            }
            Part::Value(value, quoted) => (value, quoted),
        };
        match value {
            Value::Int(x, _) => out.push_str(&x.to_string()),
            Value::F64(x) => out.push_str(&format!("{x:?}")),
            Value::F32(x) => out.push_str(&format!("{x:?}")),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Char(c) if quoted => out.push_str(&quote(c.encode_utf8(&mut [0; 4]), '\'')),
            Value::Char(c) => out.push(*c),
            Value::Text(text) if quoted => out.push_str(&quote(text, '"')),
            Value::Text(text) => out.push_str(text),
            Value::Unit => out.push_str("()"),
            Value::Adt(adt) => {
                // A hand-written `show` decides its own text, so it isn't quoted.
                if let Some(text) = hand_written(value)? {
                    out.push_str(&text);
                    continue;
                }
                // `std.io`'s `IoError` is opaque to the modules that `debug` one, so `debug` writes it
                // as its `show` does, without its field's name (OPEN_QUESTIONS P5).
                if let (AdtId::IO_ERROR, [Value::Text(message)]) = (adt.def, &adt.fields[..]) {
                    out.push_str(message);
                    continue;
                }
                let def = decls.adt(adt.def);
                let variant = &def.variants[adt.variant.index()];
                // A tuple is written `(1, "a")`, as its literal is (OPEN_QUESTIONS P5).
                if def.tuple {
                    out.push('(');
                    parts.push(Part::Text(")"));
                    for (i, value) in adt.fields.iter().enumerate().rev() {
                        parts.push(Part::Value(value, true));
                        if i > 0 {
                            parts.push(Part::Text(", "));
                        }
                    }
                    continue;
                }
                out.push_str(&def.ctor_name(adt.variant));
                // An enum's variant without fields is written without parentheses (STD.md).
                if def.is_enum() && variant.fields.is_empty() {
                    continue;
                }
                out.push('(');
                // Pushed in reverse, so they are written in order.
                parts.push(Part::Text(")"));
                // `Some(3)`, `Err(e)` and `UserId(7)` are written in literal form, without a
                // label (STD.md, REFERENCE §4.6).
                if def.bare_variants || def.distinct {
                    parts.push(Part::Value(&adt.fields[0], true));
                    continue;
                }
                for (i, (field, value)) in variant.fields.iter().zip(adt.fields.iter()).enumerate().rev() {
                    parts.push(Part::Value(value, true));
                    parts.push(Part::Text(": "));
                    parts.push(Part::Text(&field.name));
                    if i > 0 {
                        parts.push(Part::Text(", "));
                    }
                }
            }
            // A collection is written as its literal, with its elements quoted (STD.md).
            Value::List(list) => {
                out.push('[');
                parts.push(Part::Text("]"));
                for (i, item) in list.items.iter().enumerate().rev() {
                    parts.push(Part::Value(item, true));
                    if i > 0 {
                        parts.push(Part::Text(", "));
                    }
                }
            }
            Value::Map(map) if map.is_empty() => out.push_str("[:]"),
            Value::Map(map) => {
                out.push('[');
                parts.push(Part::Text("]"));
                let entries: Vec<(&Value, &Value)> = map.iter().collect();
                for (i, (key, value)) in entries.into_iter().enumerate().rev() {
                    parts.push(Part::Value(value, true));
                    parts.push(Part::Text(": "));
                    parts.push(Part::Value(key, true));
                    if i > 0 {
                        parts.push(Part::Text(", "));
                    }
                }
            }
            // A pool is written as its elements in slot order, and a handle by its slot and
            // generation, which only `debug` writes (OPEN_QUESTIONS P5).
            Value::Pool(pool) => {
                out.push_str("Pool([");
                parts.push(Part::Text("])"));
                let elements: Vec<&Value> = pool.elements().collect();
                for (i, element) in elements.into_iter().enumerate().rev() {
                    parts.push(Part::Value(element, true));
                    if i > 0 {
                        parts.push(Part::Text(", "));
                    }
                }
            }
            Value::Handle(handle) => {
                out.push_str(&format!("Handle(slot: {}, generation: {})", handle.slot, handle.generation));
            }
            // Only a `cap record` that implements `Show` is shown, and `debug` writes its name.
            Value::Object(object) => match hand_written(value)? {
                Some(text) => out.push_str(&text),
                None => out.push_str(&decls.adt(object.def).name),
            },
            Value::Cap(cap) => out.push_str(match cap {
                Cap::Stdin => "In",
                Cap::Stdout | Cap::Stderr => "Out",
                Cap::Dir(_) => "Dir",
                Cap::Inert(iface) => &decls.iface(*iface).name,
            }),
            // `debug` writes a function value's type, which only the checker knows.
            Value::Fn(_) => out.push_str("fn"),
        }
    }
    Ok(out)
}

/// `text` written as a Proviso literal between `quote`s, with its escapes.
pub fn quote(text: &str, quote: char) -> String {
    let mut out = String::from(quote);
    for c in text.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}

/// Whether a field of the record or tuple `adt`, whose type arguments are `args`, or a part
/// of one, has moved out, which leaves `Unit` in a place whose type isn't `Unit`.
fn has_hole(decls: &Decls, adt: &Adt, args: &[Ty]) -> bool {
    let def = decls.adt(adt.def);
    if def.is_enum() || def.is_native() {
        return false;
    }
    let types = def.field_types(adt.variant, args);
    types.iter().zip(adt.fields.iter()).any(|(ty, value)| match (value, ty) {
        (Value::Unit, ty) => *ty != Ty::Unit,
        (Value::Adt(inner), Ty::Adt(_, args)) => has_hole(decls, inner, args),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use proviso_check::decls::{AdtDef, FieldDef, VariantDef};

    use super::*;

    #[test]
    fn division_truncates_toward_zero() {
        assert_eq!(int_arithmetic(BinOp::Div, -7, 2, IntTy::I64), Ok(-3));
        assert_eq!(int_arithmetic(BinOp::Rem, -7, 2, IntTy::I64), Ok(-1));
        assert_eq!(int_arithmetic(BinOp::Rem, 7, -2, IntTy::I64), Ok(1));
    }

    #[test]
    fn overflow_is_checked_per_type() {
        assert!(int_arithmetic(BinOp::Add, 127, 1, IntTy::I8).is_err());
        assert_eq!(int_arithmetic(BinOp::Add, 254, 1, IntTy::U8), Ok(255));
        assert!(int_arithmetic(BinOp::Sub, 0, 1, IntTy::U64).is_err());
        assert!(int_arithmetic(BinOp::Div, i64::MIN.into(), -1, IntTy::I64).is_err());
        assert!(int_arithmetic(BinOp::Mul, u64::MAX.into(), u64::MAX.into(), IntTy::U64).is_err());
    }

    #[test]
    fn division_by_zero_is_a_defect() {
        assert_eq!(int_arithmetic(BinOp::Rem, 1, 0, IntTy::I32).unwrap_err().0, DefectKind::DivisionByZero);
    }

    #[test]
    fn float_show_is_shortest_round_trip() {
        assert_eq!(show(&Value::F64(1.0), &Decls::default()), "1.0");
        assert_eq!(show(&Value::F64(0.1 + 0.2), &Decls::default()), "0.30000000000000004");
        assert_eq!(show(&Value::F32(0.1), &Decls::default()), "0.1");
        assert_eq!(show(&Value::F64(f64::NAN), &Decls::default()), "NaN");
    }

    #[test]
    fn debug_quotes_with_proviso_escapes() {
        assert_eq!(debug_repr(&Value::Text("a\"\\\n\t\r\0é".into()), &Decls::default()), r#""a\"\\\n\t\u{d}\u{0}é""#);
        assert_eq!(debug_repr(&Value::Char('\''), &Decls::default()), r"'\''");
        assert_eq!(debug_repr(&Value::Char('"'), &Decls::default()), "'\"'");
    }

    #[test]
    fn nan_is_unequal_to_itself() {
        let nan = Value::F64(f64::NAN);
        assert!(!equal(&nan, &nan));
        assert!(!compare(BinOp::Lt, &nan, &nan));
        assert!(!compare(BinOp::Ge, &nan, &nan));
    }

    fn field(name: &str, ty: Ty) -> FieldDef {
        FieldDef { name: name.into(), ty, state: false }
    }

    fn record(def: AdtId, fields: Vec<Value>) -> Value {
        Value::Adt(Adt { def, variant: VariantIdx::RECORD, fields: fields.into() })
    }

    #[test]
    fn nested_records_show_as_constructions_with_quoted_text() {
        let mut decls = Decls::default();
        let tag = decls.push(AdtDef::record("Tag", vec![field("label", Ty::Text), field("mark", Ty::Char)]));
        let outer = decls.push(AdtDef::record("Labelled", vec![field("tag", Ty::adt(tag)), field("n", Ty::INT)]));
        let inner = record(tag, vec![Value::Text("a\"b".into()), Value::Char('\n')]);
        let value = record(outer, vec![inner, Value::Int(-3, IntTy::I64)]);
        let expected = r#"Labelled(tag: Tag(label: "a\"b", mark: '\n'), n: -3)"#;
        assert_eq!(show(&value, &decls), expected);
        assert_eq!(debug_repr(&value, &decls), expected);
    }

    /// Dropping, comparing and writing a recursive enum use no native stack per node, so they
    /// work on a thread whose stack holds a few hundred frames. The interpreter's own thread
    /// has 1 GiB, which hides recursion until about ten million nodes.
    #[test]
    fn deep_values_need_no_native_stack() {
        let mut decls = Decls::default();
        let list = decls.push(AdtDef::enumeration("IntList"));
        let def = decls.adt_mut(list);
        def.variants.push(VariantDef::new("Nil", Vec::new()));
        def.variants.push(VariantDef::new("Cons", vec![field("head", Ty::INT), field("tail", Ty::adt(list))]));
        let build = move |n: usize, last: i128| {
            let mut value = Value::Adt(Adt { def: list, variant: VariantIdx::new(0), fields: Arc::new([]) });
            for i in 0..n {
                let head = Value::Int(if i == 0 { last } else { i as i128 }, IntTy::I64);
                let fields = Arc::new([head, value]);
                value = Value::Adt(Adt { def: list, variant: VariantIdx::new(1), fields });
            }
            value
        };
        let small = std::thread::Builder::new().stack_size(64 * 1024);
        let result = small.spawn(move || {
            let (a, b, c) = (build(100_000, 0), build(100_000, 0), build(100_000, 1));
            let text = show(&a, &decls);
            let start = text.starts_with("IntList.Cons(head: 99999, tail: IntList.Cons(head: 99998, tail: ");
            (equal(&a, &b), equal(&a, &c), text.len(), start)
        });
        // Each node writes `IntList.Cons(head: `, `, tail: ` and `)` around its head: 28
        // characters, 488,890 digits in all, and 11 for `IntList.Nil`.
        assert_eq!(result.unwrap().join().unwrap(), (true, false, 3_288_901, true));
    }

    /// Lists and maps nested through a recursive enum, as `Node(kids: [t])` and
    /// `Fork(kids: [0: t])` nest them, are also dropped, compared, ordered, hashed and written
    /// without native stack per level, and so are maps nested through their keys.
    #[test]
    fn deep_collections_need_no_native_stack() {
        let mut decls = Decls::default();
        let tree = decls.push(AdtDef::enumeration("Tree"));
        let def = decls.adt_mut(tree);
        def.variants.push(VariantDef::new("Leaf", vec![field("n", Ty::INT)]));
        def.variants.push(VariantDef::new("Node", vec![field("kids", Ty::list(Ty::adt(tree)))]));
        let leaf = move |n: i128| {
            Value::Adt(Adt { def: tree, variant: VariantIdx::new(0), fields: Arc::new([Value::Int(n, IntTy::I64)]) })
        };
        let node =
            move |kids: Value| Value::Adt(Adt { def: tree, variant: VariantIdx::new(1), fields: Arc::new([kids]) });
        // A map whose one key is the tree so far, as `Fork(kids: [t: 0])` nests it.
        let keyed = move |n: usize, last: i128| {
            let mut value = leaf(last);
            for _ in 0..n {
                let mut kids = MapValue::default();
                kids.insert(hash_value(&value, &Decls::default()), value, Value::Int(0, IntTy::I64));
                value = node(Value::Map(Arc::new(kids)));
            }
            value
        };
        let build = move |n: usize, last: i128, map: bool| {
            let mut value = leaf(last);
            for _ in 0..n {
                let kids = if map {
                    let mut kids = MapValue::default();
                    let key = Value::Int(0, IntTy::I64);
                    kids.insert(hash_value(&key, &Decls::default()), key, value);
                    Value::Map(Arc::new(kids))
                } else {
                    Value::List(Arc::new(ListValue { items: vec![value] }))
                };
                value = node(kids);
            }
            value
        };
        let small = std::thread::Builder::new().stack_size(64 * 1024);
        let result = small.spawn(move || {
            let mut out = Vec::new();
            for map in [false, true] {
                let (a, b, c) = (build(100_000, 0, map), build(100_000, 0, map), build(100_000, 1, map));
                let ordered = order(&a, &c) == Some(Ordering::Less);
                let hashed = hash_value(&a, &decls) == hash_value(&b, &decls);
                out.push((equal(&a, &b), equal(&a, &c), ordered, hashed, show(&a, &decls).len()));
            }
            let (a, b, c) = (keyed(100_000, 0), keyed(100_000, 0), keyed(100_000, 1));
            let ordered = order(&a, &c) == Some(Ordering::Less);
            let hashed = hash_value(&a, &decls) == hash_value(&b, &decls);
            out.push((equal(&a, &b), equal(&a, &c), ordered, hashed, show(&a, &decls).len()));
            out
        });
        // `Tree.Node(kids: [` and `])` are 19 characters a level, and `Tree.Leaf(n: 0)` 15.
        // A map's level writes `0: ` too.
        let expected = vec![
            (true, false, true, true, 1_900_015),
            (true, false, true, true, 2_200_015),
            (true, false, true, true, 2_200_015),
        ];
        assert_eq!(result.unwrap().join().unwrap(), expected);
    }
}
