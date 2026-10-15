//! The golden test runner (OPEN_QUESTIONS P3). `tests/golden/README.md` specifies the format.
//!
//! Every `*.proviso` file under the root is one test. Files for a phase after the given one
//! are pending, but their headers and markers are still validated. Directives this runner
//! can't check yet (`expect-report`, `expect-log`, `run`, `schedules`, and `sig` from phase 4)
//! make an active file fail rather than pass unchecked. Setting `bless` writes the actual
//! output to the `.out` and `.err` files instead of comparing.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use proviso_check::Options;
use proviso_syntax::diag::{Severity, codes};

use crate::{compile, run};

#[derive(Default, Debug)]
pub struct Report {
    pub passed: Vec<String>,
    pub pending: Vec<String>,
    pub failed: Vec<(String, String)>,
}

pub fn run_dir(root: &Path, phase: u32, bless: bool) -> Report {
    let mut files = Vec::new();
    collect(root, &mut files);
    files.sort();
    let mut report = Report::default();
    for path in files {
        let name = path.strip_prefix(root).unwrap_or(&path).to_string_lossy().replace('\\', "/");
        match run_file(&path, &name, phase, bless) {
            Ok(Verdict::Pass) => report.passed.push(name),
            Ok(Verdict::Pending) => report.pending.push(name),
            Err(reason) => report.failed.push((name, reason)),
        }
    }
    report
}

fn collect(dir: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, files);
        } else if path.extension().is_some_and(|e| e == "proviso") {
            files.push(path);
        }
    }
}

enum Verdict {
    Pass,
    Pending,
}

/// The phase from which `// sig:` directives are checked; `sig` arrives in phase 4.
const SIG_PHASE: u32 = 4;

/// A line of a `.out` file that separates the outputs a run may legitimately produce.
const ALTERNATIVE: &str = "--- or ---";

/// The trailing comment that marks where an expected error is reported.
const MARKER: &str = "// <-";

/// Directives in the format that this runner cannot check yet.
const UNCHECKED: &[&str] = &["expect-report", "expect-log", "run", "schedules"];

struct Header {
    phase: Option<u32>,
    expect_errors: Vec<String>,
    expect_exit: i32,
    incomplete: bool,
    sig: bool,
    unchecked: Vec<String>,
}

/// The name of a directive-shaped comment, such as `phase` in `// phase: 1`.
fn directive(line: &str) -> Option<(&str, &str)> {
    let body = line.trim().strip_prefix("//")?.trim();
    let (name, value) = body.split_once(':')?;
    let shaped =
        name.starts_with(|c: char| c.is_ascii_lowercase()) && name.chars().all(|c| c.is_ascii_lowercase() || c == '-');
    shaped.then_some((name, value.trim()))
}

/// Reads the directives from the header: the comment lines that start the file. A
/// directive-shaped comment that names no directive, or one after the header, is an error.
fn parse_header(text: &str) -> Result<Header, String> {
    let mut header = Header {
        phase: None,
        expect_errors: Vec::new(),
        expect_exit: 0,
        incomplete: false,
        sig: false,
        unchecked: Vec::new(),
    };
    let mut in_header = true;
    let text = text.strip_prefix('\u{feff}').unwrap_or(text);
    for (index, line) in text.lines().enumerate() {
        in_header &= line.trim_start().starts_with("//");
        let Some((name, value)) = directive(line) else { continue };
        let known =
            matches!(name, "phase" | "expect-error" | "expect-exit" | "flags" | "sig") || UNCHECKED.contains(&name);
        if !in_header {
            if known {
                return Err(format!("line {}: the directive `{name}` must be in the header", index + 1));
            }
            continue;
        }
        match name {
            "phase" => header.phase = Some(value.parse().map_err(|_| format!("bad phase: {line}"))?),
            "expect-error" => header.expect_errors.push(value.to_string()),
            "expect-exit" => header.expect_exit = value.parse().map_err(|_| format!("bad expect-exit: {line}"))?,
            "flags" => {
                for flag in value.split_whitespace() {
                    match flag {
                        "--incomplete" => header.incomplete = true,
                        other => return Err(format!("unknown flag `{other}` in: {line}")),
                    }
                }
            }
            "sig" => header.sig = true,
            name if UNCHECKED.contains(&name) => {
                if !header.unchecked.iter().any(|d| d == name) {
                    header.unchecked.push(name.to_string());
                }
            }
            _ => return Err(format!("line {}: unknown directive `{name}`", index + 1)),
        }
    }
    Ok(header)
}

/// The `// <- <code>…` markers, as (line, code) pairs counted with multiplicity.
fn markers(text: &str) -> BTreeMap<(usize, String), usize> {
    let mut found = BTreeMap::new();
    for (index, line) in text.lines().enumerate() {
        if let Some((_, rest)) = line.split_once(MARKER) {
            for code in rest.split([' ', ',']).filter(|c| !c.is_empty()) {
                *found.entry((index + 1, code.to_string())).or_insert(0) += 1;
            }
        }
    }
    found
}

fn run_file(path: &Path, name: &str, phase: u32, bless: bool) -> Result<Verdict, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("cannot read: {e}"))?;
    let header = parse_header(&text)?;
    let marked = markers(&text);
    let Some(file_phase) = header.phase else { return Err("missing `// phase: N` header".to_string()) };
    let mut uncatalogued: Vec<&str> = header
        .expect_errors
        .iter()
        .map(String::as_str)
        .chain(marked.keys().map(|(_, code)| code.as_str()))
        .filter(|c| codes::find(c).is_none())
        .collect();
    uncatalogued.dedup();
    if !uncatalogued.is_empty() {
        return Err(format!("the codes {uncatalogued:?} are not in tests/DIAGNOSTICS.md"));
    }
    let mut want: Vec<&str> = header.expect_errors.iter().map(String::as_str).collect();
    want.sort_unstable();
    want.dedup();
    let mut marked_codes: Vec<&str> = marked.keys().map(|(_, code)| code.as_str()).collect();
    marked_codes.sort_unstable();
    marked_codes.dedup();
    if want != marked_codes {
        return Err(format!(
            "the `expect-error` codes {want:?} differ from the codes marked with `{MARKER}` {marked_codes:?}"
        ));
    }
    if file_phase > phase {
        return Ok(Verdict::Pending);
    }
    let mut unchecked = header.unchecked.clone();
    if header.sig && phase >= SIG_PHASE {
        unchecked.push("sig".to_string());
    }
    if !unchecked.is_empty() {
        return Err(format!(
            "this runner cannot check the directives {unchecked:?} yet, but the file's phase is active"
        ));
    }

    let out_path = path.with_extension("out");
    let err_path = path.with_extension("err");
    let runs = out_path.exists() || err_path.exists() || header.expect_exit != 0;
    let opts = Options { incomplete: header.incomplete, needs_main: runs && want.is_empty() };
    let compiled = compile(name, text, opts);

    if !want.is_empty() {
        if runs {
            return Err("a file that expects errors cannot also expect a run".to_string());
        }
        let mut got: BTreeMap<(usize, String), usize> = BTreeMap::new();
        for d in compiled.diagnostics.iter().filter(|d| d.severity == Severity::Error) {
            let (line, _) = compiled.file.line_col(d.span.lo);
            *got.entry((line as usize, d.code.id.to_string())).or_insert(0) += 1;
        }
        if got != marked {
            let lines = |m: &BTreeMap<(usize, String), usize>| {
                m.iter().map(|((line, code), n)| format!("{code} on line {line} x{n}")).collect::<Vec<_>>().join(", ")
            };
            return Err(format!(
                "reported errors differ from the `{MARKER}` markers\n  marked:   {}\n  reported: {}\n{}",
                lines(&marked),
                lines(&got),
                compiled.render()
            ));
        }
        return Ok(Verdict::Pass);
    }

    if compiled.has_errors() {
        return Err(format!("unexpected diagnostics:\n{}", compiled.render()));
    }
    if compiled.program.main.is_none() {
        return Ok(Verdict::Pass);
    }
    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    let code = run(&compiled, &mut stdout, &mut stderr);
    let stdout = String::from_utf8_lossy(&stdout).into_owned();
    let stderr = String::from_utf8_lossy(&stderr).into_owned();

    if code != header.expect_exit {
        return Err(format!("exit code {code}, expected {}\n--- stderr\n{stderr}", header.expect_exit));
    }
    let expected_out = fs::read_to_string(&out_path).unwrap_or_default();
    let allowed = alternatives(&expected_out);
    let mut problems = Vec::new();
    if !allowed.contains(&stdout) {
        if bless && allowed.len() == 1 {
            fs::write(&out_path, &stdout).map_err(|e| format!("cannot write {}: {e}", out_path.display()))?;
        } else {
            let hint = if bless { " (bless doesn't rewrite a file with alternatives)" } else { "" };
            problems.push(format!(
                "stdout differs from {}{hint}:\n--- expected\n{expected_out}--- actual\n{stdout}",
                file_name(&out_path)
            ));
        }
    }
    let expected_err = fs::read_to_string(&err_path).unwrap_or_default();
    if stderr != expected_err {
        if bless {
            fs::write(&err_path, &stderr).map_err(|e| format!("cannot write {}: {e}", err_path.display()))?;
        } else {
            problems.push(format!(
                "stderr differs from {}:\n--- expected\n{expected_err}--- actual\n{stderr}",
                file_name(&err_path)
            ));
        }
    }
    if problems.is_empty() { Ok(Verdict::Pass) } else { Err(problems.join("\n")) }
}

/// The outputs a `.out` file allows, separated by lines of exactly [`ALTERNATIVE`].
fn alternatives(expected: &str) -> Vec<String> {
    let mut outputs = vec![String::new()];
    for line in expected.split_inclusive('\n') {
        if line.trim_end_matches(['\r', '\n']) == ALTERNATIVE {
            outputs.push(String::new());
        } else {
            outputs.last_mut().expect("there is always a current output").push_str(line);
        }
    }
    outputs
}

fn file_name(path: &Path) -> String {
    path.file_name().map_or_else(String::new, |n| n.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn out_files_may_list_alternatives() {
        assert_eq!(alternatives("a\n--- or ---\nb\n"), ["a\n", "b\n"]);
        assert_eq!(alternatives("only\n"), ["only\n"]);
        assert_eq!(alternatives(""), [""]);
    }
}
