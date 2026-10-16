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

/// Golden files check only codes, so the wording that tells std's `ParseError` from a
/// module's, and an example from a function, is checked here (OPEN_QUESTIONS P5).
#[test]
fn messages_name_what_they_mean() {
    let file = source(
        "names.proviso",
        "use std.text { ParseError as PE }\n\nenum ParseError {\n    Mine\n}\n\nfn arms(t: Text) -> Int {\n    return Int.parse(t) else match it {\n        PE.Empty => 0\n        PE.Invalid => 1\n    }\n}\n\nfn wrong(e: PE) -> Int {\n    return match e {\n        ParseError.Mine => 1\n    }\n}\n\nfn gone(e: PE) -> Int {\n    return match e {\n        PE.Gone => 1\n        _ => 0\n    }\n}\n\nfn risky(n: Int) -> Int fails Text {\n    return n\n}\n\nfn id(n: Int) -> Int {\n    return n\n}\n\nexample id(try risky(1)) == 1\n",
    );
    let errors = stderr(&run(&["check"], &file));
    for expected in [
        "does not cover `std.text.ParseError.OutOfRange`",
        "expected a pattern for `std.text.ParseError`, found one for `ParseError`",
        "`std.text.ParseError` has no variant `Gone`",
        "`try` in an example, which has no function to propagate `Text` to",
    ] {
        assert!(errors.contains(expected), "missing {expected:?} in:\n{errors}");
    }
}

#[test]
fn json_applies_only_to_check() {
    let file = source("hello.proviso", HELLO);
    let output = run(&["run", "--json"], &file);
    assert_eq!(output.status.code(), Some(64));
    assert!(stderr(&output).contains("`--json` applies only to `check`"), "{}", stderr(&output));
}

#[test]
fn test_runs_examples_without_a_main() {
    let file = source(
        "examples.proviso",
        "fn double(n: Int) -> Int {\n    return n * 2\n}\n\nexample double(2) == 4\nexample double(2) == 5\n",
    );
    let output = run(&["test"], &file);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(stdout.ends_with("2 examples: 1 passed, 1 failed\n"), "{stdout}");
    assert!(stdout.contains("example failed: expected `5`, found `4`"), "{stdout}");
    assert_eq!(run(&["run"], &file).status.code(), Some(65));
    assert_eq!(run(&["test", "--json"], &file).status.code(), Some(64));
}

/// Each example's result is written as soon as it has run, so it sits next to that example's
/// `debug` output and defect report when both streams go to one place.
#[test]
fn test_reports_each_example_next_to_its_output() {
    let file = source(
        "streamed.proviso",
        "fn f(n: Int) -> Int {\n    debug(n)\n    assert n != 2\n    return n\n}\n\nexample f(1) == 1\nexample f(2) == 2\nexample f(3) == 3\n",
    );
    let merged = file.with_extension("log");
    let log = std::fs::File::create(&merged).unwrap();
    let status = proviso().arg("test").arg(&file).stdout(log.try_clone().unwrap()).stderr(log).status().unwrap();
    assert_eq!(status.code(), Some(70));
    let text = std::fs::read_to_string(&merged).unwrap();
    let kinds: Vec<&str> = text
        .lines()
        .filter_map(|line| match () {
            _ if line.starts_with("[debug") => Some("debug"),
            _ if line.starts_with("defect") => Some("defect"),
            _ if line.ends_with("example passed") => Some("passed"),
            _ if line.contains("example failed") => Some("failed"),
            _ => None,
        })
        .collect();
    assert_eq!(kinds, ["debug", "passed", "debug", "defect", "failed", "debug", "passed"], "{text}");
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

/// A chain of blocks nested past the limit is reported once, whatever the statement that
/// opens each block, though the code after each inner block is just as deep (§15.1).
#[test]
fn a_deep_chain_of_blocks_is_too_deep_once() {
    for head in ["check n > 5 else ", "if n > 5 ", "let v = o else ", "let w = risky(n) else "] {
        let mut chain = String::from("{ return 0 }");
        for _ in 0..1000 {
            chain = format!("{{ {head}{chain}\n return 1 }}");
        }
        let text = format!(
            "fn risky(n: Int) -> Int fails Text {{\n    return n\n}}\n\nfn f(n: Int, o: Option[Int]) -> Int {{\n    {head}{chain}\n    return 2\n}}\n"
        );
        let file = source("deep_blocks.proviso", &text);
        let output = run(&["check"], &file);
        let errors = stderr(&output);
        assert_eq!(output.status.code(), Some(65), "{head}: {errors}");
        assert_eq!(errors.matches("error[").count(), 1, "{head}: {errors}");
        assert!(errors.contains("error[E0902]"), "{head}: {errors}");
    }
}

/// A program whose recursion runs the interpreter's stack low while each call compares or
/// shows a value nested `depth` records deep, so that work runs right next to the limit.
fn deep_records(depth: usize, probe: &str) -> String {
    let mut text = String::from("record R0 derives(Eq, Show) {\n    x: Int\n}\n");
    for i in 1..depth {
        text += &format!("record R{i} derives(Eq, Show) {{\n    r: R{}\n}}\n", i - 1);
    }
    let last = depth - 1;
    let nested = (0..100).fold(format!("{probe} + down(v: v)"), |e, _| format!("0 + ({e})"));
    text += &format!("fn down(v: R{last}) -> Int {{\n    return {nested}\n}}\n");
    text += "pub fn main(sys: keep System) {\n    let v0 = R0(x: 1)\n";
    for i in 1..depth {
        text += &format!("    let v{i} = R{i}(r: v{})\n", i - 1);
    }
    text += &format!("    let n = down(v: v{last})\n}}\n");
    text
}

#[test]
fn equality_and_show_of_deep_records_never_overflow_the_stack() {
    let probes = [("deep_eq.proviso", "(if v == v { 1 } else { 0 })"), ("deep_show.proviso", "v.show().byte_len()")];
    for (name, probe) in probes {
        let file = source(name, &deep_records(6_000, probe));
        let output = run(&["run"], &file);
        assert_eq!(output.status.code(), Some(70), "{name}: {}", stderr(&output));
        assert!(stderr(&output).starts_with("defect[stack_exhausted]"), "{name}: {}", stderr(&output));
    }
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
