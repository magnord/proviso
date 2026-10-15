//! The `proviso` toolchain: compile a file, report diagnostics, and run it.

pub mod golden;

use std::fmt::Write as _;
use std::io::Write;
use std::path::Path;

use proviso_check::{Options, Program, check_module};
use proviso_interp::{Defect, Outcome, run_main};
use proviso_syntax::ast::Module;
use proviso_syntax::diag::{Diagnostic, Diagnostics, Severity, codes};
use proviso_syntax::parse_module;
use proviso_syntax::source::{SourceFile, Span};

/// The last phase of the v1 plan (OPEN_QUESTIONS P3) that this toolchain implements.
pub const IMPLEMENTED_PHASE: u32 = 1;

/// Process exit codes. 1 and 70 come from REFERENCE §7.3 and §7.4; the others follow the
/// BSD `sysexits` convention that 70 already belongs to.
pub mod exit {
    pub const OK: i32 = 0;
    /// `main` failed with an error.
    pub const FAILED: i32 = 1;
    pub const USAGE: i32 = 64;
    /// `check` found errors, so nothing ran.
    pub const CHECK_ERRORS: i32 = 65;
    pub const NO_INPUT: i32 = 66;
    /// The program hit a defect.
    pub const DEFECT: i32 = 70;
    pub const INTERNAL: i32 = 101;
}

/// The interpreter's thread stack, sized for `proviso_interp::MAX_CALL_DEPTH` nested calls.
const INTERPRETER_STACK: usize = 1 << 30;

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
    let mut diags = Diagnostics::default();
    let module = parse_module(&file, &name, &mut diags);
    let program = check_module(&module, opts, &mut diags);
    let mut diagnostics = diags.into_vec();
    diagnostics.sort_by_key(|d| (d.span.lo, d.span.hi));
    Compiled { file, module, program, diagnostics }
}

impl Compiled {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }

    /// Reports a missing `main`, which only matters when the file is run.
    pub fn require_main(&mut self) {
        if self.program.main.is_none() {
            self.diagnostics.push(Diagnostic {
                code: codes::INVALID_MAIN,
                severity: Severity::Error,
                span: Span::default(),
                message: "there is no `main` to run; declare `pub fn main(sys: keep System)`".to_string(),
            });
        }
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
        for item in &m.items {
            if item.span.lo <= span.lo && span.lo < item.span.hi.max(item.span.lo + 1) {
                if let Some(name) = item.name() {
                    let (line, _) = self.file.line_col(span.lo);
                    let (first, _) = self.file.line_col(item.span.lo);
                    return format!("{}.{}+{}", m.name, m.text(name.sym), line - first + 1);
                }
            }
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

    /// The defect and its call sites. Runs of the same call site, as in deep recursion,
    /// collapse to one line, and at most [`MAX_TRACE_LINES`] lines are shown.
    pub fn render_defect(&self, defect: &Defect) -> String {
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
    let outcome = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("proviso-main".to_string())
            .stack_size(INTERPRETER_STACK)
            .spawn_scoped(scope, || {
                run_main(&compiled.file, &compiled.module, &compiled.program, &mut *stdout, &mut *stderr)
            })
            .expect("failed to start the interpreter thread")
            .join()
    });
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
}
