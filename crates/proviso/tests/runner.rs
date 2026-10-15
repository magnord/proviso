//! The golden test runner, run on small directories of golden files.

use std::path::PathBuf;

use proviso::golden::{Report, run_dir};

/// A fresh directory holding `files`, as (name, contents) pairs.
fn dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("runner").join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (file, text) in files {
        std::fs::write(dir.join(file), text).unwrap();
    }
    dir
}

fn failure(report: &Report) -> &str {
    assert!(report.passed.is_empty() && report.pending.is_empty(), "{report:?}");
    assert_eq!(report.failed.len(), 1, "{report:?}");
    &report.failed[0].1
}

const HELLO: &str = "// phase: 1\nuse std.io { IoError }\n\npub fn main(sys: keep System) fails IoError {\n    try sys.stdout.write_line(\"hello\")\n}\n";

#[test]
fn a_directive_the_runner_cannot_check_fails_an_active_file() {
    let dir = dir("unchecked", &[("t.proviso", "// phase: 2\n// expect-log: Dir.write_text\n")]);
    assert_eq!(run_dir(&dir, 1, false).pending, ["t.proviso"]);
    assert!(failure(&run_dir(&dir, 2, false)).contains("cannot check the directives [\"expect-log\"]"));
}

#[test]
fn sig_is_checked_from_phase_4() {
    let dir = dir("sig", &[("t.proviso", "// phase: 1\n// sig: f\nfn f() {\n}\n")]);
    assert_eq!(run_dir(&dir, 1, false).passed, ["t.proviso"]);
    assert!(failure(&run_dir(&dir, 4, false)).contains("[\"sig\"]"));
}

#[test]
fn an_uncatalogued_code_fails_even_a_pending_file() {
    let dir = dir(
        "uncatalogued",
        &[("t.proviso", "// phase: 9\n// expect-error: E9999\nfn f() {\n    g()   // <- E9999\n}\n")],
    );
    assert!(failure(&run_dir(&dir, 1, false)).contains("[\"E9999\"] are not in tests/DIAGNOSTICS.md"));
}

#[test]
fn a_misspelled_directive_fails() {
    let dir = dir("misspelled", &[("t.proviso", "// phase: 1\n// expect-eror: E0201\nfn f() {\n}\n")]);
    assert!(failure(&run_dir(&dir, 1, false)).contains("unknown directive `expect-eror`"));
}

#[test]
fn directives_are_read_only_from_the_header() {
    let dir = dir("late", &[("t.proviso", "// phase: 1\nfn f() {\n}\n// expect-exit: 70\n")]);
    assert!(failure(&run_dir(&dir, 1, false)).contains("line 4: the directive `expect-exit` must be in the header"));
}

#[test]
fn each_error_must_be_reported_on_its_marked_line() {
    let header = "// phase: 1\n// expect-error: E0201\n";
    let dir = dir(
        "markers",
        &[
            ("right.proviso", &format!("{header}fn f() {{\n    let a = x   // <- E0201\n}}\n")),
            ("wrong_line.proviso", &format!("{header}fn f() {{   // <- E0201\n    let a = x\n}}\n")),
            ("twice.proviso", &format!("{header}fn f() {{\n    let a = x + y   // <- E0201\n}}\n")),
            ("unmarked.proviso", &format!("{header}fn f() {{\n    let a = x\n}}\n")),
        ],
    );
    let report = run_dir(&dir, 1, false);
    assert_eq!(report.passed, ["right.proviso"]);
    let failed: Vec<&str> = report.failed.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(failed, ["twice.proviso", "unmarked.proviso", "wrong_line.proviso"]);
    assert!(report.failed[0].1.contains("reported: E0201 on line 4 x2"), "{}", report.failed[0].1);
    assert!(report.failed[1].1.contains("differ from the codes marked"), "{}", report.failed[1].1);
}

#[test]
fn an_expected_exit_code_needs_a_main() {
    let dir = dir("no_main", &[("t.proviso", "// phase: 1\n// expect-exit: 70\nfn f() {\n}\n")]);
    assert!(failure(&run_dir(&dir, 1, false)).contains("E0308"));
}

#[test]
fn bless_rewrites_output_only_when_the_exit_code_matches() {
    let dir = dir(
        "bless",
        &[
            ("hello.proviso", HELLO),
            ("hello.out", "stale\n"),
            ("wrong_exit.proviso", &HELLO.replace("// phase: 1\n", "// phase: 1\n// expect-exit: 70\n")),
            ("wrong_exit.out", "stale\n"),
        ],
    );
    let report = run_dir(&dir, 1, true);
    assert_eq!(report.passed, ["hello.proviso"]);
    assert!(failure(&Report { passed: vec![], ..report }).contains("exit code 0, expected 70"));
    assert_eq!(std::fs::read_to_string(dir.join("hello.out")).unwrap(), "hello\n");
    assert_eq!(std::fs::read_to_string(dir.join("wrong_exit.out")).unwrap(), "stale\n");
    assert_eq!(run_dir(&dir, 1, false).passed, ["hello.proviso"]);
}

#[test]
fn bless_keeps_alternatives() {
    let alternatives = "a\n--- or ---\nb\n";
    let dir = dir("alternatives", &[("t.proviso", HELLO), ("t.out", alternatives)]);
    assert!(failure(&run_dir(&dir, 1, true)).contains("bless doesn't rewrite a file with alternatives"));
    assert_eq!(std::fs::read_to_string(dir.join("t.out")).unwrap(), alternatives);
    std::fs::write(dir.join("t.out"), "x\n--- or ---\nhello\n").unwrap();
    assert_eq!(run_dir(&dir, 1, false).passed, ["t.proviso"]);
}

#[test]
fn stderr_must_match_the_err_file_or_be_empty() {
    let program = HELLO.replace("try sys.stdout.write_line(\"hello\")", "debug(1)");
    let dir = dir("stderr", &[("t.proviso", &program)]);
    assert!(failure(&run_dir(&dir, 1, false)).contains("stderr differs from t.err"));
    std::fs::write(dir.join("t.err"), "[debug t.proviso:5:5] 1\n").unwrap();
    assert_eq!(run_dir(&dir, 1, false).passed, ["t.proviso"]);
}

/// A program that prints a line and then hits an `assertion_failed` defect, after `headers`.
fn defect(headers: &str) -> String {
    format!(
        "// phase: 1\n// expect-exit: 70\n{headers}use std.io {{ IoError }}\n\npub fn main(sys: keep System) fails IoError {{\n    try sys.stdout.write_line(\"before\")\n    assert 1 > 2\n}}\n"
    )
}

#[test]
fn each_expected_report_must_be_printed_as_often_as_it_is_expected() {
    let dir = dir(
        "reports",
        &[
            ("printed.proviso", &defect("// expect-report: defect assertion_failed\n")),
            ("printed.out", "before\n"),
            ("missing.proviso", &defect("// expect-report: defect division_by_zero\n")),
            ("missing.out", "before\n"),
            ("twice.proviso", &defect(&"// expect-report: defect assertion_failed\n".repeat(2))),
            ("twice.out", "before\n"),
        ],
    );
    let report = run_dir(&dir, 1, true);
    assert_eq!(report.passed, ["printed.proviso"]);
    assert!(!dir.join("printed.err").exists(), "bless wrote an .err for a file with expect-report");
    let failed: Vec<&str> = report.failed.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(failed, ["missing.proviso", "twice.proviso"]);
    let (missing, twice) = (&report.failed[0].1, &report.failed[1].1);
    assert!(missing.contains("expected: defect division_by_zero x1"), "{missing}");
    assert!(missing.contains("found:    defect assertion_failed x1"), "{missing}");
    assert!(twice.contains("expected: defect assertion_failed x2"), "{twice}");
}

#[test]
fn an_unknown_report_kind_fails_even_a_pending_file() {
    let dir = dir("report_kind", &[("t.proviso", "// phase: 9\n// expect-report: crash assertion_failed\n")]);
    assert!(failure(&run_dir(&dir, 1, false)).contains("line 2: unknown report kind `crash`"));
}

#[test]
fn an_err_file_is_still_matched_exactly_when_reports_are_expected() {
    let dir = dir(
        "reports_and_err",
        &[
            ("t.proviso", &defect("// expect-report: defect assertion_failed\n")),
            ("t.out", "before\n"),
            ("t.err", "defect[assertion_failed]: assertion failed: 1 > 2\n"),
        ],
    );
    assert!(failure(&run_dir(&dir, 1, false)).contains("stderr differs from t.err"));
}
