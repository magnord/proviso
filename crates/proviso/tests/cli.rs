//! The `proviso` command line, run as a process.

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn proviso() -> Command {
    Command::new(env!("CARGO_BIN_EXE_proviso"))
}

/// Writes `text` to a fresh file under the test's temporary directory.
fn source(name: &str, text: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("cli");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path
}

fn run(args: &[&str], file: &PathBuf) -> Output {
    proviso().args(args).arg(file).output().unwrap()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

const HELLO: &str = "use std.io { IoError }\n\npub fn main(sys: keep System) fails IoError {\n    try sys.stdout.write_line(\"hello\")\n}\n";

#[test]
fn a_closed_stdout_does_not_crash_check() {
    let lines: String = (0..3000).map(|i| format!("    let x{i} = y{i}\n")).collect();
    let file = source("many_errors.proviso", &format!("fn f() {{\n{lines}}}\n"));
    let mut child =
        proviso().args(["check", "--json"]).arg(&file).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    let mut first = String::new();
    BufReader::new(child.stdout.take().unwrap()).read_line(&mut first).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(first.contains("E0201"), "{first}");
    assert_eq!(output.status.code(), Some(65), "{}", stderr(&output));
    assert!(!stderr(&output).contains("panicked"), "{}", stderr(&output));
}

#[test]
fn run_needs_a_main() {
    let file = source("no_main.proviso", "fn f() {\n}\n");
    let output = run(&["run"], &file);
    assert_eq!(output.status.code(), Some(65));
    assert!(stderr(&output).contains("error[E0308]: there is no `main` to run"), "{}", stderr(&output));
    assert_eq!(run(&["check"], &file).status.code(), Some(0));
}

#[test]
fn json_applies_only_to_check() {
    let file = source("hello.proviso", HELLO);
    let output = run(&["run", "--json"], &file);
    assert_eq!(output.status.code(), Some(64));
    assert!(stderr(&output).contains("`--json` applies only to `check`"), "{}", stderr(&output));
}

#[test]
fn unknown_options_are_usage_errors() {
    let file = source("hello.proviso", HELLO);
    for flag in ["-x", "--frobnicate"] {
        let output = run(&["check", flag], &file);
        assert_eq!(output.status.code(), Some(64), "{flag}");
        assert!(stderr(&output).contains(&format!("unknown option `{flag}`")), "{}", stderr(&output));
    }
}

#[test]
fn a_file_that_is_not_utf8_is_unreadable() {
    let file = source("latin1.proviso", "");
    std::fs::write(&file, b"fn f() {\n    let s = \"\xe9\"\n}\n").unwrap();
    let output = run(&["check"], &file);
    assert_eq!(output.status.code(), Some(66));
}

#[test]
fn deep_recursion_through_nested_expressions_is_a_defect() {
    let branches: String = (1..=10).map(|i| format!("    }} else if n == -{i} {{\n        return {i}\n")).collect();
    let text = format!(
        "fn down(n: Int) -> Int {{\n    if n == 0 {{\n        return 0\n{branches}    }} else {{\n        return down(n: n + 1)\n    }}\n}}\n\npub fn main(sys: keep System) {{\n    let n = down(n: 1)\n}}\n"
    );
    let file = source("deep.proviso", &text);
    let output = run(&["run"], &file);
    assert_eq!(output.status.code(), Some(70), "{}", stderr(&output));
    assert!(stderr(&output).starts_with("defect[stack_exhausted]"), "{}", stderr(&output));
}

/// A stdout that refuses every write.
struct Closed;

impl Write for Closed {
    fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(std::io::ErrorKind::BrokenPipe, "closed"))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[test]
fn main_that_fails_exits_with_1_and_shows_its_error() {
    let compiled = proviso::compile("hello.proviso", HELLO.to_string(), Default::default());
    let mut err = Vec::new();
    let code = proviso::run(&compiled, &mut Closed, &mut err);
    assert_eq!(code, proviso::exit::FAILED);
    assert_eq!(String::from_utf8_lossy(&err), "cannot write to stdout: closed\n");
}
