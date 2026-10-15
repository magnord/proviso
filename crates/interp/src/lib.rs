//! A tree-walking interpreter over a checked module.
//!
//! It trusts the checker: every name is resolved and every expression has a type, so a
//! missing side-table entry is an interpreter bug, not a user error. Values that the
//! language treats as copies are shared behind `Arc`, so a later phase can hand them to
//! other task threads unchanged.

use std::cmp::Ordering;
use std::io::Write;
use std::sync::Arc;

use proviso_check::decls::{AdtId, Decls, FieldIdx, VariantIdx};
use proviso_check::types::{FloatTy, IntTy, Ty};
use proviso_check::{Builtin, FnId, LocalId, Program, Res};
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

/// A record value. Writes go through `Arc::make_mut`, so a shared record is copied one level
/// at the first write (value semantics, REFERENCE §5.1).
#[derive(Clone, Debug)]
pub struct Adt {
    pub def: AdtId,
    pub variant: VariantIdx,
    pub fields: Arc<[Value]>,
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

/// Runs `main` on a thread of its own. Program output goes to `stdout`; `debug` output goes
/// to `stderr`. An `Err` is a panic in the interpreter, which is a bug.
pub fn run_main(
    file: &SourceFile,
    m: &Module,
    p: &Program,
    stdout: &mut (dyn Write + Send),
    stderr: &mut (dyn Write + Send),
) -> std::thread::Result<Outcome> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("proviso-main".to_string())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, || {
                // The stack grows down, so this is close to its top.
                let stack_limit = stack_address().saturating_sub(STACK_SIZE - STACK_RESERVE);
                let mut interp = Interp { file, m, p, stdout, stderr, depth: 0, stack_limit };
                interp.main()
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
    Defect(Defect),
}

type Flow<T> = Result<T, Unwind>;

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
}

/// A function's local slots, indexed by `LocalId`.
type Frame = Vec<Value>;

impl Interp<'_> {
    fn main(&mut self) -> Outcome {
        let main = self.p.main.expect("the driver checks that `main` exists");
        let site = self.m.fn_decl(self.p.fns[main].item).expect("`main` is a function").name.span;
        let fields = Arc::from([Value::Cap(Cap::Stdout)]);
        let sys = Value::Adt(Adt { def: AdtId::SYSTEM, variant: VariantIdx::RECORD, fields });
        match self.call(main, vec![sys], site) {
            Ok(_) => Outcome::Done,
            Err(Unwind::Fail(error)) => Outcome::Failed(show(&error, &self.p.decls)),
            Err(Unwind::Defect(mut defect)) => {
                // The last caller is the synthetic call of `main` itself.
                defect.callers.pop();
                Outcome::Defect(defect)
            }
            Err(Unwind::Return(_) | Unwind::Break(_) | Unwind::Continue(_)) => {
                unreachable!("returns and jumps do not escape a function")
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

    fn call(&mut self, f: FnId, args: Vec<Value>, site: Span) -> Flow<Value> {
        self.check_stack(site)?;
        let info = &self.p.fns[f];
        let decl = self.m.fn_decl(info.item).expect("functions are declared by `fn` items");
        let mut frame = args;
        frame.resize(info.locals, Value::Unit);
        self.depth += 1;
        let result = self.block(&decl.body, &mut frame);
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
            StmtKind::Let { init, .. } => {
                let value = self.expr(*init, frame)?;
                let id = self.p.let_local.get(s).expect("`let` bindings are resolved");
                frame[id.index()] = value;
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
            if self.bool(pred.expr, &mut frame)? {
                continue;
            }
            let text = file.slice(self.m.exprs[pred.expr].span);
            let message = match pred.field {
                Some(i) => {
                    let shown = debug_repr(&adt.fields[i.index()], &p.decls);
                    let field = &variant.fields[i.index()].name;
                    format!("`{}.{field}` is {shown}, which breaks its refinement `{text}`", def.name)
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
                        FTextPart::Expr(x) => out.push_str(&show(&self.expr(*x, frame)?, &self.p.decls)),
                    }
                }
                Value::Text(out.into())
            }
            ExprKind::Name(_) => match self.p.res(e) {
                Some(Res::Local(id)) => frame[id.index()].clone(),
                other => unreachable!("names evaluate to locals, not {other:?}"),
            },
            ExprKind::Call { callee, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.expr(arg.value, frame)?);
                }
                match self.p.res(*callee) {
                    Some(Res::Fn(f)) => return self.call(f, values, span),
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
                let receiver = self.expr(*receiver, frame)?;
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.expr(arg.value, frame)?);
                }
                match self.p.res(e) {
                    Some(Res::Method(builtin)) => return self.builtin(builtin, receiver, values),
                    Some(Res::With) => {
                        let Value::Adt(mut adt) = receiver else { unreachable!("`with` copies a record") };
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
                if op.is_arithmetic() {
                    return self.arithmetic(*op, a, b, span);
                }
                Value::Bool(compare(*op, &a, &b))
            }
            ExprKind::Range { .. } => unreachable!("ranges appear only in `for` loops"),
            ExprKind::Try(inner) => return self.expr(*inner, frame),
            ExprKind::If { cond, then_block, else_branch } => {
                if self.bool(*cond, frame)? {
                    self.block(then_block, frame)?
                } else {
                    match else_branch {
                        Some(ElseBranch::Block(block)) => self.block(block, frame)?,
                        Some(ElseBranch::If(nested)) => self.expr(*nested, frame)?,
                        None => Value::Unit,
                    }
                }
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

    /// Runs one iteration of a loop body, turning jumps that target loop `e` into control flow.
    fn loop_body(&mut self, e: ExprId, body: &Block, frame: &mut Frame) -> Flow<LoopStep> {
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

    fn builtin(&mut self, builtin: Builtin, receiver: Value, args: Vec<Value>) -> Flow<Value> {
        Ok(match (builtin, &receiver) {
            (Builtin::WriteLine, Value::Cap(Cap::Stdout)) => {
                let Some(Value::Text(text)) = args.first() else { unreachable!("write_line takes Text") };
                if let Err(err) = writeln!(self.stdout, "{text}") {
                    let message = format!("cannot write to stdout: {err}");
                    return Err(Unwind::Fail(Value::IoError(message.into())));
                }
                Value::Unit
            }
            (Builtin::Show, value) => Value::Text(show(value, &self.p.decls).into()),
            (Builtin::ByteLen, Value::Text(text)) => Value::Int(text.len() as i128, IntTy::I64),
            (Builtin::IsEmpty, Value::Text(text)) => Value::Bool(text.is_empty()),
            (builtin, receiver) => unreachable!("{builtin:?} does not apply to {receiver:?}"),
        })
    }
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

/// Comparison of two values of the same type. Floats follow IEEE, so NaN is unequal to
/// everything; text compares by code point, which UTF-8 byte order preserves.
fn compare(op: BinOp, a: &Value, b: &Value) -> bool {
    match op {
        BinOp::Eq => return equal(a, b),
        BinOp::Ne => return !equal(a, b),
        _ => {}
    }
    let ordering = match (a, b) {
        (Value::Int(x, _), Value::Int(y, _)) => x.partial_cmp(y),
        (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
        (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.partial_cmp(y),
        (Value::Char(x), Value::Char(y)) => x.partial_cmp(y),
        (Value::Text(x), Value::Text(y)) => x.partial_cmp(y),
        (Value::Unit, Value::Unit) => Some(Ordering::Equal),
        (a, b) => unreachable!("cannot compare {a:?} and {b:?}"),
    };
    match op {
        BinOp::Lt => ordering == Some(Ordering::Less),
        BinOp::Le => matches!(ordering, Some(Ordering::Less | Ordering::Equal)),
        BinOp::Gt => ordering == Some(Ordering::Greater),
        BinOp::Ge => matches!(ordering, Some(Ordering::Greater | Ordering::Equal)),
        _ => unreachable!("`{}` is not a comparison", op.symbol()),
    }
}

/// `==`, built into scalars and derived for records, which are equal when every field is.
fn equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x, _), Value::Int(y, _)) => x == y,
        (Value::F64(x), Value::F64(y)) => x == y,
        (Value::F32(x), Value::F32(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Char(x), Value::Char(y)) => x == y,
        (Value::Text(x), Value::Text(y)) => x == y,
        (Value::Unit, Value::Unit) => true,
        (Value::Adt(x), Value::Adt(y)) => {
            x.variant == y.variant && x.fields.iter().zip(y.fields.iter()).all(|(x, y)| equal(x, y))
        }
        (a, b) => unreachable!("cannot compare {a:?} and {b:?}"),
    }
}

/// The `Show` text of a value. Floats print the shortest text that reads back as the same
/// value, always with a fraction or exponent, such as `1.0`, `0.1` and `1e21`. A record
/// writes the expression that builds it, as a derived `Show` does (STD.md).
pub fn show(value: &Value, decls: &Decls) -> String {
    match value {
        Value::Int(x, _) => x.to_string(),
        Value::F64(x) => format!("{x:?}"),
        Value::F32(x) => format!("{x:?}"),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => c.to_string(),
        Value::Text(text) => text.to_string(),
        Value::Unit => "()".to_string(),
        Value::Adt(adt) => {
            let def = decls.adt(adt.def);
            let variant = &def.variants[adt.variant.index()];
            let fields: Vec<String> = (variant.fields.iter().zip(adt.fields.iter()))
                .map(|(field, value)| format!("{}: {}", field.name, debug_repr(value, decls)))
                .collect();
            format!("{}({})", variant.name, fields.join(", "))
        }
        Value::IoError(message) => message.to_string(),
        Value::Cap(Cap::Stdout) => "Out".to_string(),
    }
}

/// The `debug` text of a value: like `show`, but text and chars are quoted and written with
/// Proviso's escapes, so the output reads as a literal. A record is written as `show` writes
/// it, whether or not it derives `Show` (OPEN_QUESTIONS P5).
fn debug_repr(value: &Value, decls: &Decls) -> String {
    match value {
        Value::Text(text) => quote(text, '"'),
        Value::Char(c) => quote(c.encode_utf8(&mut [0; 4]), '\''),
        other => show(other, decls),
    }
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
    use proviso_check::decls::{AdtDef, FieldDef};

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
        assert!(!compare(BinOp::Eq, &nan, &nan));
        assert!(compare(BinOp::Ne, &nan, &nan));
        assert!(!compare(BinOp::Lt, &nan, &nan));
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

    #[test]
    fn a_record_holding_nan_is_unequal_to_itself() {
        let mut decls = Decls::default();
        let def = decls.push(AdtDef::record("Reading", vec![field("value", Ty::Float(FloatTy::F64))]));
        let reading = record(def, vec![Value::F64(f64::NAN)]);
        assert!(!compare(BinOp::Eq, &reading, &reading.clone()));
        assert!(compare(BinOp::Ne, &reading, &reading.clone()));
    }
}
