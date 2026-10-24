//! The `proviso` toolchain: compile a file, report diagnostics, and run it.

pub mod golden;

use std::fmt::Write as _;
use std::io::Write;
use std::path::Path;

use proviso_check::{ExampleInfo, Options, Program, check_module};
use proviso_interp::{Defect, ExampleOutcome, Outcome, Report, run_examples, run_main};
use proviso_syntax::ast::{ItemKind, Module, TypeExprKind};
use proviso_syntax::diag::{Diagnostic, Diagnostics, Severity};
use proviso_syntax::parse_module;
use proviso_syntax::source::{SourceFile, Span};

/// How far this toolchain implements the v1 plan (OPEN_QUESTIONS P3): phase 1, and the first
/// eight slices of phase 2.
pub const IMPLEMENTED_PHASE: Phase = Phase::slice(2, 8);

/// A point in the v1 plan: a whole phase, or a slice of one. A phase delivered over several
/// pull requests numbers its slices `2.1`, `2.2` and so on, and each pull request turns its
/// own slice on. The whole phase sorts after all its slices, so `2.1 < 2.2 < 2 < 3.1`, and a
/// golden test written for the whole phase stays pending until the last slice lands.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Phase {
    pub number: u32,
    slice: u32,
}

impl Phase {
    const WHOLE: u32 = u32::MAX;

    pub const fn whole(number: u32) -> Phase {
        Phase { number, slice: Phase::WHOLE }
    }

    pub const fn slice(number: u32, slice: u32) -> Phase {
        assert!(slice > 0 && slice < Phase::WHOLE, "slices are numbered from 1");
        Phase { number, slice }
    }
}

impl From<u32> for Phase {
    fn from(number: u32) -> Phase {
        Phase::whole(number)
    }
}

impl std::str::FromStr for Phase {
    type Err = ();

    /// `2` or `2.1`. A slice is numbered from 1, so `2.0` is rejected.
    fn from_str(text: &str) -> Result<Phase, ()> {
        let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
        match text.split_once('.') {
            None if digits(text) => text.parse().map(Phase::whole).map_err(|_| ()),
            Some((number, slice)) if digits(number) && digits(slice) => {
                let number = number.parse().map_err(|_| ())?;
                match slice.parse() {
                    Ok(slice) if slice > 0 && slice < Phase::WHOLE => Ok(Phase::slice(number, slice)),
                    _ => Err(()),
                }
            }
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.slice {
            Phase::WHOLE => write!(f, "{}", self.number),
            slice => write!(f, "{}.{slice}", self.number),
        }
    }
}

/// Process exit codes. 1 comes from REFERENCE §7.4 and 70 from §7.3; 64 to 66 follow the
/// BSD `sysexits` convention that 70 already belongs to, and 101 is Rust's panic status
/// (OPEN_QUESTIONS P5).
pub mod exit {
    pub const OK: i32 = 0;
    /// `main` failed with an error, or an example failed.
    pub const FAILED: i32 = 1;
    pub const USAGE: i32 = 64;
    /// `check` found errors, so nothing ran.
    pub const CHECK_ERRORS: i32 = 65;
    pub const NO_INPUT: i32 = 66;
    /// The program hit a defect.
    pub const DEFECT: i32 = 70;
    /// A bug in the toolchain.
    pub const INTERNAL: i32 = 101;
}

/// The stack for parsing and checking, which recurse once per level of nesting, up to
/// `proviso_syntax::parser::MAX_NESTING` levels. At that limit a debug build needed 8 MiB.
const COMPILE_STACK: usize = 64 << 20;

/// The most call-site lines a defect report shows.
pub const MAX_TRACE_LINES: usize = 40;

pub struct Compiled {
    pub file: SourceFile,
    pub module: Module,
    pub program: Program,
    /// Sorted by position.
    pub diagnostics: Vec<Diagnostic>,
}

/// Parses and checks one file. `path` is used in diagnostics, and its stem names the module.
pub fn compile(path: &str, text: String, opts: Options) -> Compiled {
    let file = SourceFile::new(path, text);
    let name = Path::new(path).file_stem().and_then(|s| s.to_str()).unwrap_or("main").to_string();
    let compiled = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("proviso-compile".to_string())
            .stack_size(COMPILE_STACK)
            .spawn_scoped(scope, || {
                let mut diags = Diagnostics::default();
                let module = parse_module(&file, &name, &mut diags);
                let program = check_module(&module, opts, &mut diags);
                (module, program, diags.into_vec())
            })
            .expect("failed to start the compiler thread")
            .join()
    });
    let (module, program, mut diagnostics) = compiled.unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    diagnostics.sort_by_key(|d| (d.span.lo, d.span.hi));
    Compiled { file, module, program, diagnostics }
}

impl Compiled {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }

    /// `path:line:col`
    pub fn location(&self, span: Span) -> String {
        let (line, col) = self.file.line_col(span.lo);
        format!("{}:{line}:{col}", self.file.path)
    }

    /// A location that survives edits to other items, such as `users.parse_user+8` for the
    /// eighth line of `parse_user`, counting its first line as line 1 (REFERENCE §15.1).
    pub fn anchor(&self, span: Span) -> String {
        let m = &self.module;
        let within = |s: Span| s.lo <= span.lo && span.lo < s.hi.max(s.lo + 1);
        let from = |first: Span| self.file.line_col(span.lo).0 - self.file.line_col(first.lo).0 + 1;
        for item in m.items.iter().filter(|item| within(item.span)) {
            if let Some(name) = item.name() {
                return format!("{}.{}+{}", m.name, m.text(name.sym), from(item.span));
            }
            // A method is anchored at its type and its name, such as `shapes.Circle.area+2`,
            // and an interface's method also at the interface, as in `shapes.Circle.Show.show+2`.
            // The rest of a block is `shapes.Circle.impl+N` or `shapes.Circle.Show+N`, apart
            // from the record's own `shapes.Circle+N` (OPEN_QUESTIONS P5).
            let ItemKind::Impl(decl) = &item.kind else { continue };
            let ty = match &m.types[decl.target].kind {
                TypeExprKind::Named(name) | TypeExprKind::Applied { name, .. } => m.text(name.sym),
                TypeExprKind::SelfType => "Self",
                // The parser rejects implementations for tuples.
                TypeExprKind::Tuple(_) => "(…)",
            };
            let owner = match &decl.iface {
                Some(iface) => format!("{}.{ty}.{}", m.name, m.text(iface.sym)),
                None => format!("{}.{ty}", m.name),
            };
            return match decl.methods.iter().find(|method| within(method.span)) {
                Some(method) => format!("{owner}.{}+{}", m.text(method.decl.name.sym), from(method.span)),
                None if decl.iface.is_some() => format!("{owner}+{}", from(item.span)),
                None => format!("{owner}.impl+{}", from(item.span)),
            };
        }
        m.name.clone()
    }

    /// One line per diagnostic: `path:line:col: error[E0301]: message`.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for d in &self.diagnostics {
            let severity = match d.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            let _ = writeln!(out, "{}: {severity}[{}]: {}", self.location(d.span), d.code.id, d.message);
        }
        out
    }

    /// One JSON object per line, in the shape of REFERENCE §15.3.
    pub fn render_json(&self) -> String {
        let mut out = String::new();
        for d in &self.diagnostics {
            let severity = match d.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            let _ = writeln!(
                out,
                "{{\"code\": {}, \"kind\": {}, \"severity\": {}, \"at\": {}, \"anchor\": {}, \"message\": {}}}",
                json_string(d.code.id),
                json_string(d.code.kind),
                json_string(severity),
                json_string(&self.location(d.span)),
                json_string(&self.anchor(d.span)),
                json_string(&d.message),
            );
        }
        out
    }

    /// The defect and its call sites, then what the cleanup after it reported: a defect in
    /// an `abandon`, and the leak it caused right after it (REFERENCE §10; OPEN_QUESTIONS
    /// T10). Runs of the same call site, as in deep recursion, collapse to one line, and at
    /// most [`MAX_TRACE_LINES`] lines are shown.
    pub fn render_defect(&self, defect: &Defect) -> String {
        // A cleanup defect may carry its own cleanup to any depth, so the reports are walked
        // with a stack of their own, in order.
        let mut out = String::new();
        let mut reports: Vec<&Report> = Vec::new();
        out.push_str(&self.render_trace(defect));
        reports.extend(defect.cleanup.iter().rev());
        while let Some(report) = reports.pop() {
            match report {
                Report::Defect(defect) => {
                    out.push_str(&self.render_trace(defect));
                    reports.extend(defect.cleanup.iter().rev());
                }
                Report::Leak { ty, span } => {
                    let _ = writeln!(out, "leak[{ty}]: this `{ty}` leaked, since its `abandon` hit the defect above");
                    let _ = writeln!(out, "  at {} ({})", self.location(*span), self.anchor(*span));
                }
            }
        }
        out
    }

    /// The defect and its call sites, as [`Compiled::render_defect`] writes them.
    fn render_trace(&self, defect: &Defect) -> String {
        let mut out = format!("defect[{}]: {}\n", defect.kind.name(), defect.message);
        let _ = writeln!(out, "  at {} ({})", self.location(defect.span), self.anchor(defect.span));
        let mut runs: Vec<(Span, usize)> = Vec::new();
        for &site in &defect.callers {
            match runs.last_mut() {
                Some((last, count)) if *last == site => *count += 1,
                _ => runs.push((site, 1)),
            }
        }
        for &(site, count) in runs.iter().take(MAX_TRACE_LINES) {
            let repeated = if count > 1 { format!(", {count} times") } else { String::new() };
            let _ = writeln!(out, "  called from {} ({}){repeated}", self.location(site), self.anchor(site));
        }
        if runs.len() > MAX_TRACE_LINES {
            let _ = writeln!(out, "  … {} more call sites", runs.len() - MAX_TRACE_LINES);
        }
        out
    }
}

/// Runs a compiled program without errors and returns its exit code. The program writes to
/// `stdout`; failures and defects are reported on `stderr`.
pub fn run(compiled: &Compiled, stdout: &mut (dyn Write + Send), stderr: &mut (dyn Write + Send)) -> i32 {
    let outcome = run_main(&compiled.file, &compiled.module, &compiled.program, stdout, stderr);
    let _ = stdout.flush();
    match outcome {
        Ok(Outcome::Done) => exit::OK,
        Ok(Outcome::Failed(shown)) => {
            let _ = writeln!(stderr, "{shown}");
            exit::FAILED
        }
        Ok(Outcome::Defect(defect)) => {
            let _ = write!(stderr, "{}", compiled.render_defect(&defect));
            exit::DEFECT
        }
        Err(_) => {
            let _ = writeln!(stderr, "internal error: the interpreter panicked; this is a bug in proviso");
            exit::INTERNAL
        }
    }
}

/// Runs the examples of a compiled program without errors, as `proviso test` does, and
/// returns its exit code: 0 when every example passed, 1 when one failed, and 70 when one hit
/// a defect (OPEN_QUESTIONS P5). Each example's outcome goes to `stdout`, followed by a count;
/// defects are reported on `stderr`.
pub fn test(compiled: &Compiled, stdout: &mut (dyn Write + Send), stderr: &mut (dyn Write + Send)) -> i32 {
    let (mut passed, mut defects) = (0, 0);
    let report = |info: &ExampleInfo, outcome, stdout: &mut dyn Write, stderr: &mut dyn Write| {
        let at = compiled.location(compiled.module.items[info.item].span);
        let _ = match outcome {
            ExampleOutcome::Passed => {
                passed += 1;
                writeln!(stdout, "{at}: example passed")
            }
            ExampleOutcome::Failed(why) => writeln!(stdout, "{at}: example failed: {why}"),
            ExampleOutcome::Defect(defect) => {
                defects += 1;
                let _ = write!(stderr, "{}", compiled.render_defect(&defect));
                writeln!(stdout, "{at}: example failed: it hit a defect")
            }
        };
    };
    if run_examples(&compiled.file, &compiled.module, &compiled.program, stdout, stderr, report).is_err() {
        let _ = writeln!(stderr, "internal error: the interpreter panicked; this is a bug in proviso");
        return exit::INTERNAL;
    }
    let total = compiled.program.examples.len();
    let noun = if total == 1 { "example" } else { "examples" };
    let _ = writeln!(stdout, "{total} {noun}: {passed} passed, {} failed", total - passed);
    let _ = stdout.flush();
    match () {
        _ if defects > 0 => exit::DEFECT,
        _ if passed < total => exit::FAILED,
        _ => exit::OK,
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_strings_are_escaped() {
        assert_eq!(json_string("a\"b\\c\nd\u{1}"), r#""a\"b\\c\nd\u0001""#);
    }

    #[test]
    fn anchors_count_lines_within_the_item() {
        let text = "fn a() {\n}\n\nfn b() {\n    let x = 1\n    let y = q\n}\n".to_string();
        let compiled = compile("m.proviso", text, Options::default());
        assert_eq!(compiled.diagnostics.len(), 1, "{}", compiled.render());
        assert_eq!(compiled.anchor(compiled.diagnostics[0].span), "m.b+3");
    }

    #[test]
    fn methods_are_anchored_at_their_type_and_name() {
        let text = "record R {\n    n: Int\n}\n\nimpl R {\n    fn a(self) {\n    }\n\n    fn b(self) {\n        let y = q\n    }\n}\n";
        let compiled = compile("m.proviso", text.to_string(), Options::default());
        assert_eq!(compiled.diagnostics.len(), 1, "{}", compiled.render());
        assert_eq!(compiled.anchor(compiled.diagnostics[0].span), "m.R.b+2");
    }

    #[test]
    fn interface_methods_are_anchored_at_their_interface_too() {
        let iface = |name: &str| format!("interface {name} {{\n    fn label(self) -> Text\n}}\n\n");
        let imp = |name: &str| {
            format!("impl {name} for R {{\n    fn label(self) -> Text {{\n        return q\n    }}\n}}\n\n")
        };
        let text = format!(
            "record R {{\n    n: Int\n}}\n\n{}{}{}{}",
            iface("Front"),
            iface("Back"),
            imp("Front"),
            imp("Back")
        );
        let compiled = compile("m.proviso", text, Options::default());
        let anchors: Vec<String> = compiled.diagnostics.iter().map(|d| compiled.anchor(d.span)).collect();
        assert_eq!(anchors, ["m.R.Front.label+2", "m.R.Back.label+2"], "{}", compiled.render());
    }

    #[test]
    fn the_rest_of_an_impl_block_is_anchored_apart_from_its_type() {
        let text = "record R {\n    n: Int\n}\n\nimpl R {\n    fn a(self) {\n    }\n}\n\nimpl Show for R {\n}\n";
        let compiled = compile("m.proviso", text.to_string(), Options::default());
        let module = &compiled.module;
        let ItemKind::Impl(own) = &module.items[1].kind else { panic!("not an impl") };
        let after = own.methods[0].span.hi;
        let spans = [module.items[0].span, Span { lo: after + 1, hi: after + 2 }, module.items[2].span];
        let anchors: Vec<String> = spans.iter().map(|&s| compiled.anchor(s)).collect();
        assert_eq!(anchors, ["m.R+1", "m.R.impl+4", "m.R.Show+1"]);
    }
}
