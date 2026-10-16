//! A tree-walking interpreter over a checked module.
//!
//! It trusts the checker: every name is resolved and every expression has a type, so a
//! missing side-table entry is an interpreter bug, not a user error. Values that the
//! language treats as copies are shared behind `Arc`, so a later phase can hand them to
//! other task threads unchanged.

use std::cmp::Ordering;
use std::convert::Infallible;
use std::io::Write;
use std::sync::Arc;

use proviso_check::decls::{AdtId, Decls, FieldIdx, IfaceId, ImplKey, VariantIdx};
use proviso_check::types::{FloatTy, IntTy, Ty};
use proviso_check::{Builtin, ExampleInfo, FnId, LocalId, Program, Res};
use proviso_syntax::ast::*;
use proviso_syntax::source::{SourceFile, Span};

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
    IoError(Arc<str>),
    Cap(Cap),
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
        take_parts(&mut self.fields, &mut owned);
        while let Some(mut value) = owned.pop() {
            if let Value::Adt(adt) = &mut value {
                take_parts(&mut adt.fields, &mut owned);
            }
            // `value` now holds no other record or enum, so dropping it doesn't recurse.
        }
    }
}

/// Moves the records and enums out of `fields` into `owned`, if nothing else shares them.
fn take_parts(fields: &mut Arc<[Value]>, owned: &mut Vec<Value>) {
    let Some(fields) = Arc::get_mut(fields) else { return };
    for field in fields {
        if let Value::Adt(_) = field {
            owned.push(std::mem::replace(field, Value::Unit));
        }
    }
}

/// A capability. Copies share the underlying state, the one exception to value semantics
/// (REFERENCE §9.6).
#[derive(Clone, Debug)]
pub enum Cap {
    Stdout,
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
}

pub enum Outcome {
    Done,
    /// `main` failed with an error; this is its `show()`.
    Failed(String),
    Defect(Defect),
}

/// How an example came out (REFERENCE §14).
pub enum ExampleOutcome {
    Passed,
    /// It ran, but not as it says; this tells how.
    Failed(String),
    Defect(Defect),
}

/// Runs `main` on a thread of its own. Program output goes to `stdout`; `debug` output goes
/// to `stderr`. An `Err` is a panic in the interpreter, which is a bug.
pub fn run_main(
    file: &SourceFile,
    m: &Module,
    p: &Program,
    stdout: &mut (dyn Write + Send),
    stderr: &mut (dyn Write + Send),
) -> std::thread::Result<Outcome> {
    on_interp_thread(file, m, p, stdout, stderr, |interp| interp.main())
}

/// Runs each example in declaration order, each with [`EXAMPLE_FUEL`]. `report` gets how each
/// came out as soon as it has run, with the output streams, so a result is written next to the
/// example's `debug` output. `debug` output goes to `stderr`.
pub fn run_examples(
    file: &SourceFile,
    m: &Module,
    p: &Program,
    stdout: &mut (dyn Write + Send),
    stderr: &mut (dyn Write + Send),
    mut report: impl FnMut(&ExampleInfo, ExampleOutcome, &mut dyn Write, &mut dyn Write) + Send,
) -> std::thread::Result<()> {
    on_interp_thread(file, m, p, stdout, stderr, |interp| {
        for info in &p.examples {
            let outcome = interp.example(info);
            report(info, outcome, &mut *interp.stdout, &mut *interp.stderr);
        }
    })
}

fn on_interp_thread<'a, R: Send>(
    file: &'a SourceFile,
    m: &'a Module,
    p: &'a Program,
    stdout: &'a mut (dyn Write + Send),
    stderr: &'a mut (dyn Write + Send),
    run: impl FnOnce(&mut Interp<'a>) -> R + Send,
) -> std::thread::Result<R> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("proviso-main".to_string())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, || {
                // The stack grows down, so this is close to its top.
                let stack_limit = stack_address().saturating_sub(STACK_SIZE - STACK_RESERVE);
                let mut interp = Interp { file, m, p, stdout, stderr, depth: 0, stack_limit, fuel: None };
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
    Defect(Defect),
}

type Flow<T> = Result<T, Unwind>;

/// Whether `e` is an `if`, or a chain of `else if`s, that ends without an `else`.
fn lacks_final_else(m: &Module, mut e: ExprId) -> bool {
    loop {
        match &m.exprs[e].kind {
            ExprKind::If { else_branch: None, .. } => return true,
            ExprKind::If { else_branch: Some(ElseBranch::If(nested)), .. } => e = *nested,
            _ => return false,
        }
    }
}

fn defect(kind: DefectKind, message: impl Into<String>, span: Span) -> Unwind {
    Unwind::Defect(Defect { kind, message: message.into(), span, callers: Vec::new() })
}

struct Interp<'a> {
    file: &'a SourceFile,
    m: &'a Module,
    p: &'a Program,
    stdout: &'a mut (dyn Write + Send),
    stderr: &'a mut (dyn Write + Send),
    /// The number of calls in progress.
    depth: usize,
    /// The lowest stack address the interpreter may reach.
    stack_limit: usize,
    /// The steps an example has left, or `None` outside one.
    fuel: Option<u64>,
}

/// A function's local slots, indexed by `LocalId`.
type Frame = Vec<Value>;

impl Interp<'_> {
    fn main(&mut self) -> Outcome {
        let main = self.p.main.expect("the driver checks that `main` exists");
        let site = self.p.decl(self.m, main).name.span;
        let fields = Arc::from([Value::Cap(Cap::Stdout)]);
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
            Err(Unwind::Return(_) | Unwind::Break(_) | Unwind::Continue(_) | Unwind::Attempted(..)) => {
                unreachable!("returns, jumps and attempted failures do not escape a function")
            }
        }
    }

    /// Stops with a defect when the stack is nearly used up.
    fn check_stack(&self, span: Span) -> Flow<()> {
        if self.depth >= MAX_CALL_DEPTH || stack_address() < self.stack_limit {
            let depth = self.depth;
            return Err(defect(
                DefectKind::StackExhausted,
                format!("the call stack is exhausted after {depth} nested calls"),
                span,
            ));
        }
        Ok(())
    }

    /// Runs one example and tells how it came out.
    fn example(&mut self, info: &ExampleInfo) -> ExampleOutcome {
        let ItemKind::Example(decl) = &self.m.items[info.item].kind else { unreachable!("examples are items") };
        let mut frame: Frame = vec![Value::Unit; info.locals];
        (self.fuel, self.depth) = (Some(EXAMPLE_FUEL), 0);
        let outcome = self.expect(decl, &mut frame);
        self.fuel = None;
        match outcome {
            Ok(None) => ExampleOutcome::Passed,
            Ok(Some(message)) => ExampleOutcome::Failed(message),
            Err(Unwind::Defect(defect)) => ExampleOutcome::Defect(defect),
            Err(_) => unreachable!("an example neither returns nor fails"),
        }
    }

    /// Runs an example's call and compares the outcome with what it expects: `None` when they
    /// agree, or else what differs. Values are written as `debug` writes them.
    fn expect(&mut self, decl: &ExampleDecl, frame: &mut Frame) -> Flow<Option<String>> {
        let decls = &self.p.decls;
        let outcome = match self.expr(decl.call, frame) {
            Ok(value) => Ok(value),
            Err(Unwind::Attempted(handler, error)) if handler == decl.call => Err(error),
            Err(other) => return Err(other),
        };
        Ok(match (&decl.expect, outcome) {
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
                let text = self.file.slice(self.m.pats[*pat].span);
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
                Err(defect(DefectKind::FuelExhausted, format!("the example took more than {EXAMPLE_FUEL} steps"), span))
            }
            Some(fuel) => {
                *fuel -= 1;
                Ok(())
            }
            None => Ok(()),
        }
    }

    fn call(&mut self, f: FnId, args: Vec<Value>, site: Span) -> Flow<Value> {
        self.check_stack(site)?;
        self.step(site)?;
        let body = self.p.decl(self.m, f).body.as_ref().expect("functions that run have bodies");
        let mut frame = args;
        frame.resize(self.p.fns[f].locals, Value::Unit);
        self.depth += 1;
        let result = self.block(body, &mut frame);
        self.depth -= 1;
        match result {
            Ok(_) => Ok(Value::Unit),
            Err(Unwind::Return(value)) => Ok(value),
            Err(Unwind::Defect(mut defect)) => {
                defect.callers.push(site);
                Err(Unwind::Defect(defect))
            }
            Err(other) => Err(other),
        }
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
                let value = self.expr(*init, frame)?;
                // The checker proved that the pattern matches every value.
                self.matches(*pat, &value, frame)?;
            }
            StmtKind::Check { cond, fallback } => {
                if !self.bool(*cond, frame)? {
                    // The checker proved that the fallback leaves.
                    self.fallback(fallback, frame)?;
                }
            }
            StmtKind::Assign { target, op, value } => {
                let value = self.expr(*value, frame)?;
                let (root, path) = self.place(*target);
                let slot = slot(&mut frame[root.index()], &path);
                *slot = match op.bin_op() {
                    None => value,
                    Some(op) => self.arithmetic(op, slot.clone(), value, stmt.span)?,
                };
                // Each record on the path has changed, so each is checked, innermost first
                // (OPEN_QUESTIONS P5).
                for depth in (0..path.len()).rev() {
                    self.refine(at(&frame[root.index()], &path[..depth]), stmt.span)?;
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
                    let text = self.file.slice(m.exprs[*cond].span);
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
        let (p, file) = (self.p, self.file);
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
            let text = file.slice(self.m.exprs[pred.expr].span);
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

    /// The local an assignment target is rooted at, and the fields from there to the target.
    fn place(&self, target: ExprId) -> (LocalId, Vec<FieldIdx>) {
        let mut path = Vec::new();
        let mut e = target;
        loop {
            match (&self.m.exprs[e].kind, self.p.res(e)) {
                (ExprKind::Name(_), Some(Res::Local(id))) => {
                    path.reverse();
                    return (id, path);
                }
                (ExprKind::Field { base, .. }, Some(Res::Field(i))) => {
                    path.push(i);
                    e = *base;
                }
                (_, res) => unreachable!("assignment targets are places, not {res:?}"),
            }
        }
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
        self.check_stack(span)?;
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
                Some(Res::Local(id)) => frame[id.index()].clone(),
                Some(Res::Ctor(def, variant)) => Value::Adt(Adt { def, variant, fields: Arc::from([]) }),
                other => unreachable!("names evaluate to locals, not {other:?}"),
            },
            ExprKind::Call { callee, args, .. } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.expr(arg.value, frame)?);
                }
                match self.p.res(*callee) {
                    Some(Res::Fn(f)) => {
                        let result = self.call(f, values, span);
                        return self.attempted(e, result);
                    }
                    // Labels follow the declaration order, so argument `i` is field `i`.
                    Some(Res::Ctor(def, variant)) => {
                        let value = Value::Adt(Adt { def, variant, fields: values.into() });
                        self.refine(&value, span)?;
                        value
                    }
                    other => unreachable!("calls are resolved, not {other:?}"),
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                let res = self.p.res(e).expect("methods are resolved");
                // The receiver of a variant's construction or an associated function is a type's
                // name, and that of `I.f(x)` an interface's, not a value. Otherwise the receiver
                // comes first.
                let named = match res {
                    Res::Ctor(..) | Res::Dispatch { qualified: true, .. } | Res::Method(Builtin::Parse(_)) => true,
                    Res::Fn(f) => self.p.fns[f].receiver.is_none(),
                    _ => false,
                };
                let mut values = Vec::with_capacity(args.len() + 1);
                if !named {
                    values.push(self.expr(*receiver, frame)?);
                }
                for arg in args {
                    values.push(self.expr(arg.value, frame)?);
                }
                match res {
                    Res::Method(builtin) => {
                        let result = self.builtin(builtin, values);
                        return self.attempted(e, result);
                    }
                    Res::Fn(f) => {
                        let result = self.call(f, values, span);
                        return self.attempted(e, result);
                    }
                    Res::Dispatch { iface, method, .. } => {
                        let result = self.dispatch(iface, method, values, span);
                        return self.attempted(e, result);
                    }
                    // Labels follow the declaration order, so argument `i` is field `i`.
                    Res::Ctor(def, variant) => {
                        let value = Value::Adt(Adt { def, variant, fields: values.into() });
                        self.refine(&value, span)?;
                        value
                    }
                    Res::With => {
                        let mut values = values.into_iter();
                        let Some(Value::Adt(mut adt)) = values.next() else { unreachable!("`with` copies a record") };
                        let replaced = self.p.with_fields.get(e).expect("`with` is resolved");
                        let fields = Arc::make_mut(&mut adt.fields);
                        for (i, value) in replaced.iter().zip(values) {
                            fields[i.index()] = value;
                        }
                        let value = Value::Adt(adt);
                        self.refine(&value, span)?;
                        value
                    }
                    other => unreachable!("methods are resolved, not {other:?}"),
                }
            }
            ExprKind::Field { base, .. } => {
                if let Some(Res::Ctor(def, variant)) = self.p.res(e) {
                    return Ok(Value::Adt(Adt { def, variant, fields: Arc::from([]) }));
                }
                let Some(Res::Field(i)) = self.p.res(e) else { unreachable!("fields are resolved") };
                let Value::Adt(adt) = self.expr(*base, frame)? else { unreachable!("fields are read from records") };
                adt.fields[i.index()].clone()
            }
            ExprKind::Unary { op: UnaryOp::Not, operand } => Value::Bool(!self.bool(*operand, frame)?),
            ExprKind::Unary { op: UnaryOp::Neg, operand } => {
                if let ExprKind::Int(value) = m.exprs[*operand].kind {
                    // The checker treats `-128` as one literal, so it never overflows here.
                    return Ok(Value::Int(-(value as i128), self.int_ty(e)));
                }
                match self.expr(*operand, frame)? {
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
                    other => unreachable!("cannot negate {other:?}"),
                }
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
                    _ => Value::Bool(compare(*op, &a, &b)),
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
            ExprKind::For { iter, body, .. } => {
                let ExprKind::Range { lo, hi, inclusive } = m.exprs[*iter].kind else {
                    unreachable!("phase 1 loops over ranges")
                };
                let (lo, it) = self.int(lo, frame)?;
                let (hi, _) = self.int(hi, frame)?;
                let end = if inclusive { hi + 1 } else { hi };
                let slot = self.p.for_local.get(e).expect("loop variables are resolved").index();
                let mut i = lo;
                while i < end {
                    frame[slot] = Value::Int(i, it);
                    if self.loop_body(e, body, frame)?.is_break() {
                        break;
                    }
                    i += 1;
                }
                Value::Unit
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
                let value = self.expr(*scrutinee, frame)?;
                for arm in arms {
                    if !self.matches(arm.pat, &value, frame)? {
                        continue;
                    }
                    if let Some(guard) = arm.guard
                        && !self.bool(guard, frame)?
                    {
                        continue;
                    }
                    return self.block(&arm.body, frame);
                }
                // The checker leaves integer exhaustiveness to run time (OPEN_QUESTIONS P5).
                let shown = debug_repr(&value, &self.p.decls);
                return Err(defect(DefectKind::NoArmMatched, format!("no arm of this `match` matches {shown}"), span));
            }
            ExprKind::Is { value, pat } => {
                let value = self.expr(*value, frame)?;
                Value::Bool(self.matches(*pat, &value, frame)?)
            }
            ExprKind::Tuple(elements) => {
                let Ty::Adt(def, _) = self.p.ty(e) else { unreachable!("tuples have tuple types") };
                let def = *def;
                let mut values = Vec::with_capacity(elements.len());
                for &element in elements {
                    values.push(self.expr(element, frame)?);
                }
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
                Some(Res::Local(id)) => frame[id.index()].clone(),
                other => unreachable!("`it` is a local, not {other:?}"),
            },
            ExprKind::Error => unreachable!("programs with errors don't run"),
            ExprKind::Debug(values) => {
                let mut parts = Vec::with_capacity(values.len());
                for value in values {
                    parts.push(debug_repr(&self.expr(*value, frame)?, &self.p.decls));
                }
                let (line, col) = self.file.line_col(span.lo);
                // `debug` output is best effort; a failed write is not a program error.
                let _ = writeln!(self.stderr, "[debug {}:{line}:{col}] {}", self.file.path, parts.join(", "));
                Value::Unit
            }
        })
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
            (a, b) => unreachable!("no arithmetic on {a:?} and {b:?}"),
        })
    }

    /// Runs a built-in method. `values` holds the receiver, then the arguments.
    fn builtin(&mut self, builtin: Builtin, values: Vec<Value>) -> Flow<Value> {
        Ok(match (builtin, values.as_slice()) {
            (Builtin::WriteLine, [Value::Cap(Cap::Stdout), Value::Text(text)]) => {
                if let Err(err) = writeln!(self.stdout, "{text}") {
                    let message = format!("cannot write to stdout: {err}");
                    return Err(Unwind::Fail(Value::IoError(message.into())));
                }
                Value::Unit
            }
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
            (builtin, values) => unreachable!("{builtin:?} does not apply to {values:?}"),
        })
    }

    /// Runs method `method` of `iface` as the implementation for the receiver's type does.
    /// Values describe themselves, so the receiver tells which one, also in generic code
    /// (REFERENCE §4.9). `values` holds the receiver, then the arguments.
    fn dispatch(&mut self, iface: IfaceId, method: usize, values: Vec<Value>, site: Span) -> Flow<Value> {
        match (iface, values.as_slice()) {
            (IfaceId::SHOW, [value]) => Ok(Value::Text(self.show(value, site)?.into())),
            (IfaceId::EQ, [a, b]) => Ok(Value::Bool(self.equal(a, b, site)?)),
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

    /// `==`. A record or enum whose type implements `Eq` by hand is compared by its `eq`, also
    /// inside a value whose `Eq` is derived (OPEN_QUESTIONS P5). A defect in it is traced to
    /// `site`.
    fn equal(&mut self, a: &Value, b: &Value, site: Span) -> Flow<bool> {
        let p = self.p;
        equal_with(a, b, |a, b| {
            let Some(f) = hand_written(a, IfaceId::EQ, &p.decls) else { return Ok(None) };
            match self.call(f, vec![a.clone(), b.clone()], site)? {
                Value::Bool(same) => Ok(Some(same)),
                other => unreachable!("`eq` returns Bool, not {other:?}"),
            }
        })
    }
}

/// `Some(value)`, or `None`.
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
        Value::IoError(_) => ImplKey::IoError,
        Value::Adt(adt) => ImplKey::Adt(adt.def),
        Value::Cap(_) => unreachable!("capabilities implement no interface"),
    }
}

/// The function that implements the one method of `iface` for `value`'s record or enum, when
/// an `impl` declares it rather than `derives`.
fn hand_written(value: &Value, iface: IfaceId, decls: &Decls) -> Option<FnId> {
    let Value::Adt(adt) = value else { return None };
    decls.impl_method(iface, ImplKey::Adt(adt.def), 0)
}

fn at<'v>(mut value: &'v Value, path: &[FieldIdx]) -> &'v Value {
    for i in path {
        let Value::Adt(adt) = value else { unreachable!("field paths go through records") };
        value = &adt.fields[i.index()];
    }
    value
}

/// The slot `path` names inside `value`. Each record on the way is copied first if it is
/// shared, so the write changes no other copy (REFERENCE §5.1).
fn slot<'v>(mut value: &'v mut Value, path: &[FieldIdx]) -> &'v mut Value {
    for i in path {
        let Value::Adt(adt) = value else { unreachable!("field paths go through records") };
        value = &mut Arc::make_mut(&mut adt.fields)[i.index()];
    }
    value
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
    let ordering = order(a, b);
    match op {
        BinOp::Lt => ordering == Some(Ordering::Less),
        BinOp::Le => matches!(ordering, Some(Ordering::Less | Ordering::Equal)),
        BinOp::Gt => ordering == Some(Ordering::Greater),
        BinOp::Ge => matches!(ordering, Some(Ordering::Greater | Ordering::Equal)),
        _ => unreachable!("`{}` is not an ordering", op.symbol()),
    }
}

/// The derived `Ord` orders a record or enum by variant in declaration order, then field by
/// field in declaration order (STD.md). No `Ord` is written by hand yet, so this is every
/// ordering. Like [`equal`], it keeps the pairs still to compare in a list of its own, so no
/// value is too deep for the native stack.
fn order(a: &Value, b: &Value) -> Option<Ordering> {
    let mut pairs = vec![(a, b)];
    while let Some(pair) = pairs.pop() {
        let ordering = match pair {
            (Value::Int(x, _), Value::Int(y, _)) => x.partial_cmp(y),
            (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
            (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
            (Value::Bool(x), Value::Bool(y)) => x.partial_cmp(y),
            (Value::Char(x), Value::Char(y)) => x.partial_cmp(y),
            (Value::Text(x), Value::Text(y)) => x.partial_cmp(y),
            (Value::Unit, Value::Unit) => Some(Ordering::Equal),
            (Value::Adt(x), Value::Adt(y)) => {
                // Pushed in reverse, so the first field is compared first, with all it holds.
                pairs.extend(x.fields.iter().zip(y.fields.iter()).rev());
                x.variant.index().partial_cmp(&y.variant.index())
            }
            (a, b) => unreachable!("cannot order {a:?} and {b:?}"),
        };
        if ordering != Some(Ordering::Equal) {
            return ordering;
        }
    }
    Some(Ordering::Equal)
}

/// `==` as built into scalars and derived for records and enums, which are equal when their
/// variants and every field are. Floats follow IEEE, so NaN is unequal to everything.
fn equal(a: &Value, b: &Value) -> bool {
    match equal_with(a, b, |_, _| Ok::<_, Infallible>(None)) {
        Ok(same) => same,
        Err(never) => match never {},
    }
}

/// `==`, where `hand_written` decides a pair of records or enums it returns `Some` for. It
/// walks nested records with a list of its own rather than recursion, so no value is too deep
/// for the native stack.
fn equal_with<E>(
    a: &Value,
    b: &Value,
    mut hand_written: impl FnMut(&Value, &Value) -> Result<Option<bool>, E>,
) -> Result<bool, E> {
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
            (a @ Value::Adt(x), b @ Value::Adt(y)) => match hand_written(a, b)? {
                Some(same) => same,
                None => {
                    // Reversed, so the first field is compared first and a later field's
                    // hand-written `eq` doesn't run once one differs (OPEN_QUESTIONS P5).
                    pairs.extend(x.fields.iter().zip(y.fields.iter()).rev());
                    x.variant == y.variant
                }
            },
            (a, b) => unreachable!("cannot compare {a:?} and {b:?}"),
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
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
                // `Some(3)` and `Err(e)` are written in literal form, without a label (STD.md).
                if def.bare_variants {
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
            Value::IoError(message) => out.push_str(message),
            Value::Cap(Cap::Stdout) => out.push_str("Out"),
        }
    }
    Ok(out)
}

fn quote(text: &str, quote: char) -> String {
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
        FieldDef { name: name.into(), ty }
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
}
