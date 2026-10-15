//! The golden test runner (OPEN_QUESTIONS P3). `tests/golden/README.md` specifies the format.
//!
//! Every `*.proviso` file under the root is one test. Files for a phase after
//! [`crate::IMPLEMENTED_PHASE`] are pending. Directives this runner can't check yet
//! (`expect-report`, `expect-log`, `run`, `schedules`, and `sig` before phase 4) make an active
//! file fail rather than pass unchecked. Setting `bless` writes the actual output to the
//! `.out` and `.err` files instead of comparing.

use std::fs;
use std::path::{Path, PathBuf};

use proviso_check::Options;
use proviso_syntax::diag::codes;

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

struct Header {
    phase: Option<u32>,
    expect_errors: Vec<String>,
    expect_exit: i32,
    incomplete: bool,
    sig: bool,
    /// Directives in the format that this runner cannot check yet.
    unchecked: Vec<String>,
}

fn parse_header(text: &str) -> Result<Header, String> {
    let mut header = Header {
        phase: None,
        expect_errors: Vec::new(),
        expect_exit: 0,
        incomplete: false,
        sig: false,
        unchecked: Vec::new(),
    };
    for line in text.lines() {
        let Some(comment) = line.trim().strip_prefix("//") else { continue };
        let comment = comment.trim();
        if let Some(value) = comment.strip_prefix("phase:") {
            header.phase = Some(value.trim().parse().map_err(|_| format!("bad phase header: {line}"))?);
        } else if let Some(value) = comment.strip_prefix("expect-error:") {
            header.expect_errors.push(value.trim().to_string());
        } else if let Some(value) = comment.strip_prefix("expect-exit:") {
            header.expect_exit = value.trim().parse().map_err(|_| format!("bad expect-exit header: {line}"))?;
        } else if let Some(value) = comment.strip_prefix("flags:") {
            for flag in value.split_whitespace() {
                match flag {
                    "--incomplete" => header.incomplete = true,
                    other => return Err(format!("unknown flag `{other}` in: {line}")),
                }
            }
        } else if comment.starts_with("sig:") {
            header.sig = true;
        } else if let Some(directive) =
            ["expect-report:", "expect-log:", "run:", "schedules:"].iter().find(|d| comment.starts_with(**d))
        {
            header.unchecked.push(directive.trim_end_matches(':').to_string());
        }
    }
    Ok(header)
}

fn run_file(path: &Path, name: &str, phase: u32, bless: bool) -> Result<Verdict, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("cannot read: {e}"))?;
    let header = parse_header(&text)?;
    let Some(file_phase) = header.phase else { return Err("missing `// phase: N` header".to_string()) };
    let uncatalogued: Vec<&String> = header.expect_errors.iter().filter(|c| codes::find(c).is_none()).collect();
    if !uncatalogued.is_empty() {
        return Err(format!("expect-error codes {uncatalogued:?} are not in tests/DIAGNOSTICS.md"));
    }
    if file_phase > phase {
        return Ok(Verdict::Pending);
    }
    let mut unchecked = header.unchecked.clone();
    if header.sig && phase >= SIG_PHASE {
        unchecked.push("sig".to_string());
    }
    unchecked.dedup();
    if !unchecked.is_empty() {
        return Err(format!(
            "this runner cannot check the directives {unchecked:?} yet, but the file's phase is active"
        ));
    }
    let mut compiled = compile(name, text, Options { incomplete: header.incomplete });

    if !header.expect_errors.is_empty() {
        let mut want = header.expect_errors.clone();
        want.sort();
        want.dedup();
        let mut got: Vec<String> = compiled
            .diagnostics
            .iter()
            .filter(|d| d.severity == proviso_syntax::diag::Severity::Error)
            .map(|d| d.code.id.to_string())
            .collect();
        got.sort();
        got.dedup();
        if got != want {
            return Err(format!("expected errors {want:?}, got {got:?}:\n{}", compiled.render()));
        }
        return Ok(Verdict::Pass);
    }

    let out_path = path.with_extension("out");
    let err_path = path.with_extension("err");
    if compiled.program.main.is_none() && !out_path.exists() {
        return if compiled.has_errors() {
            Err(format!("unexpected diagnostics:\n{}", compiled.render()))
        } else {
            Ok(Verdict::Pass)
        };
    }
    compiled.require_main();
    if compiled.has_errors() {
        return Err(format!("unexpected diagnostics:\n{}", compiled.render()));
    }
    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    let code = run(&compiled, &mut stdout, &mut stderr);
    let stdout = String::from_utf8_lossy(&stdout).into_owned();
    let stderr = String::from_utf8_lossy(&stderr).into_owned();

    if bless {
        fs::write(&out_path, &stdout).map_err(|e| format!("cannot write {}: {e}", out_path.display()))?;
        if !stderr.is_empty() || err_path.exists() {
            fs::write(&err_path, &stderr).map_err(|e| format!("cannot write {}: {e}", err_path.display()))?;
        }
    }
    let mut problems = Vec::new();
    if code != header.expect_exit {
        problems.push(format!("exit code {code}, expected {}", header.expect_exit));
    }
    let expected_out = fs::read_to_string(&out_path).unwrap_or_default();
    if !alternatives(&expected_out).contains(&stdout) {
        problems.push(format!(
            "stdout differs from {}:\n--- expected\n{expected_out}--- actual\n{stdout}",
            file_name(&out_path)
        ));
    }
    if err_path.exists() {
        let expected_err = fs::read_to_string(&err_path).unwrap_or_default();
        if stderr != expected_err {
            problems.push(format!(
                "stderr differs from {}:\n--- expected\n{expected_err}--- actual\n{stderr}",
                file_name(&err_path)
            ));
        }
    } else if code != header.expect_exit && !stderr.is_empty() {
        problems.push(format!("stderr:\n{stderr}"));
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

    #[test]
    fn unchecked_directives_are_collected() {
        let header =
            parse_header("// phase: 2\n// expect-report: leak Probe\n// sig: f\n// run: record-replay\n").unwrap();
        assert_eq!(header.unchecked, ["expect-report", "run"]);
        assert!(header.sig);
    }
}
