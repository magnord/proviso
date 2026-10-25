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
/// A `main` whose declaration doesn't parse is reported once, not also as missing (§15.1;
/// issue #55).
#[test]
fn a_main_that_fails_to_parse_is_not_missing() {
    for header in ["pub fn main(sys: keep System fails IoError {", "pub fn main(sys: keep System) -> {"] {
        let text = format!("use std.io {{ IoError }}\n\n{header}\n    try sys.stdout.write_line(\"x\")\n}}\n");
        let file = source("broken_main.proviso", &text);
        let output = run(&["run"], &file);
        let errors = stderr(&output);
        assert_eq!(output.status.code(), Some(65), "{header}: {errors}");
        assert_eq!(errors.matches("error[").count(), 1, "{header}: {errors}");
        assert!(errors.contains("error[E0101]"), "{header}: {errors}");
    }
}

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

/// A type argument that nothing has given yet is written `_`, never as the `Never` it once
/// stood in for, which a reader takes for the type the program asked for (issue #22). A
/// literal's is written as its default.
#[test]
fn unknown_type_arguments_show_as_underscores() {
    let file = source(
        "unknown.proviso",
        "fn checked[T: Copy](x: T) -> Result[T, Text] {\n    return Ok(x)\n}\n\nfn value_or[T: Copy](r: Result[Option[T], Text], d: T) -> T {\n    return d\n}\n\nfn f(c: Bool) -> Int {\n    let a = value_or(r: checked(if c { 1 } else { 2 }), d: 5)\n    let b = value_or(r: if c { Ok(1) } else { Err(\"x\") }, d: 0)\n    return a + b\n}\n\nfn g() {\n    let t: Text = Some(1)\n    let u: Text = Some(1.5)\n}\n\nfn both[T: Copy](x: T) -> T fails T {\n    return x\n}\n\nfn h(small: Int8) -> Int8 {\n    let y = both(x: 5) + small\n    return y\n}\n",
    );
    let errors = stderr(&run(&["check"], &file));
    assert_eq!(errors.matches("expected `Option[_]`, found `Int`").count(), 3, "{errors}");
    assert!(!errors.contains("Never"), "{errors}");
    // A literal's type has a default, so it is no unknown.
    assert!(errors.contains("expected `Text`, found `Option[Int]`"), "{errors}");
    assert!(errors.contains("expected `Text`, found `Option[Float]`"), "{errors}");
    // An unmarked call names the error type its statement settles.
    assert!(errors.contains("`both` can fail with `Int8`"), "{errors}");
}

/// A method in a handler's chain is found before the handler settles the error types in its
/// receiver, so the message names a literal's type by its default, and a type the handler
/// settles later by that type (OPEN_QUESTIONS P5, `fails Never`; issue #37).
#[test]
fn a_chain_receiver_names_its_open_error_types() {
    let file = source(
        "receiver.proviso",
        "record Plain {\n    n: Int\n}\n\nrecord Box {\n    n: Int\n}\n\nfn boxof[E: Copy](e: E) -> Box fails E {\n    return Box(n: 1)\n}\n\nimpl Box {\n    fn wrap[E: Copy](self, e: E) -> Option[E] fails E {\n        return None\n    }\n}\n\nfn stop() -> Never {\n    loop {\n    }\n}\n\nfn f() -> Int {\n    let a = attempt boxof(e: nosuch).wrap(e: 9).missing()\n    let b = attempt boxof(e: nosuch).wrap(e: 1.5).missing()\n    let c = attempt boxof(e: stop()).wrap(e: stop()).show() == Err(Plain(n: 1))\n    return 0\n}\n\nfn g() -> Int fails Text {\n    let d = try boxof(e: stop()).wrap(e: stop()).nosuch()\n    return 0\n}\n",
    );
    let errors = stderr(&run(&["check"], &file));
    assert!(errors.contains("`Option[Int]` has no method `missing`"), "{errors}");
    assert!(errors.contains("`Option[Float]` has no method `missing`"), "{errors}");
    assert!(errors.contains("`Option[Plain]` has no method `show`"), "{errors}");
    // What the handler knows already gives the type a message names.
    assert!(errors.contains("`Option[Text]` has no method `nosuch`"), "{errors}");
    assert!(!errors.contains("Never"), "{errors}");
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

/// `check --examples` runs the examples once the file checks, but not its tests, which
/// `test` runs too (REFERENCE §14). Its results go to stdout, so it can't be mixed with
/// `--json`, and `test` needs no flag to run them.
#[test]
fn check_examples_runs_examples_but_not_tests() {
    let file = source(
        "check_examples.proviso",
        "fn double(n: Int) -> Int {\n    return n * 2\n}\n\nexample double(2) == 4\n\ntest \"doubles\" {\n    expect double(3) == 7\n}\n",
    );
    let output = run(&["check", "--examples"], &file);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(stdout.ends_with(":5:1: example passed\n1 example: 1 passed, 0 failed\n"), "{stdout}");
    let output = run(&["test"], &file);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(stdout.contains(":8:5: test \"doubles\" failed: expected `7`, found `6`\n"), "{stdout}");
    assert!(stdout.ends_with("1 example and 1 test: 1 passed, 1 failed\n"), "{stdout}");
    assert_eq!(run(&["check"], &file).stdout.len(), 0);
    for args in [&["check", "--examples", "--json"][..], &["test", "--examples"], &["run", "--examples"]] {
        assert_eq!(run(args, &file).status.code(), Some(64), "{args:?}");
    }
    let broken = source("check_examples_broken.proviso", "example double(2) == 4\n");
    assert_eq!(run(&["check", "--examples"], &broken).status.code(), Some(65));
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

/// A function type's result and error type, and a closure's declared result, nest as deep
/// as its parameters do: past the limit, once, never past the stack (OPEN_QUESTIONS P5,
/// Nesting limit).
#[test]
fn deep_function_types_are_too_deep_once() {
    let forms = [("fn() -> ", ""), ("fn() fails ", ""), ("fn(", ")")];
    for (open, close) in forms {
        let ty = format!("{}fn(){}", open.repeat(40_000), close.repeat(40_000));
        let text = format!(
            "fn f(g: {ty}) {{}}

fn h() {{
    let c = || -> {ty} {{
        return 0
    }}
}}
"
        );
        let file = source("deep_fn_types.proviso", &text);
        let output = run(&["check"], &file);
        let errors = stderr(&output);
        assert_eq!(output.status.code(), Some(65), "{open}: {errors}");
        assert_eq!(errors.matches("error[").count(), 2, "{open}: {errors}");
        assert_eq!(errors.matches("error[E0902]").count(), 2, "{open}: {errors}");
    }
}

/// A closure bound to a local may call the ones bound before it. When the closures capture
/// only each other, checking what each reads and reading what each captures again at a call
/// take time in proportion to the chain, though each closure calls the two before it
/// (OPEN_QUESTIONS P5, Closures at run time).
#[test]
fn a_chain_of_closures_checks_and_runs_in_linear_time() {
    let mut text = String::from(
        "pub fn main(sys: keep System) {
    let c0 = |x: Int| x
    let c1 = |x: Int| x
",
    );
    for i in 2..6_000 {
        text += &format!(
            "    let c{i} = |x: Int| if x == 0 {{ 0 }} else {{ c{}(x) + c{}(x) }}
",
            i - 1,
            i - 2
        );
    }
    text += "    let n = c5999(0)
}
";
    let file = source("closure_chain.proviso", &text);
    for command in ["check", "run"] {
        let output = within(command, &file, 20);
        assert_eq!(output.status.code(), Some(0), "{command}: {}", stderr(&output));
    }
}

/// Runs `proviso check` on `file`, and fails the test if it takes longer than `secs`.
fn check_within(file: &PathBuf, secs: u64) -> Output {
    within("check", file, secs)
}

/// Runs `proviso <command>` on `file`, and fails the test if it takes longer than `secs`.
fn within(command: &str, file: &PathBuf, secs: u64) -> Output {
    let mut child = proviso().arg(command).arg(file).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    let start = std::time::Instant::now();
    while child.try_wait().unwrap().is_none() {
        if start.elapsed().as_secs() >= secs {
            child.kill().unwrap();
            panic!("`proviso {command}` on {} took longer than {secs} s", file.display());
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    child.wait_with_output().unwrap()
}

/// Whether a type has values is asked of each part once, though `(t, t)` doubles the tree
/// that the type stands for, so a `match` or `let` pattern on it checks as fast as the rest
/// (OPEN_QUESTIONS P5, Exhaustiveness limit). The answer still comes from the leaves: an
/// enum without variants leaves the tuples built from it without values (P5).
#[test]
fn exhaustiveness_asks_a_shared_type_part_once() {
    let lets: String = (1..=40).map(|i| format!("    let t{i} = (t{}, t{})\n", i - 1, i - 1)).collect();
    let cases = [
        ("Int", "    return match t40 {\n        _ => 1\n    }\n", 0),
        ("Int", "    let (a, b) = t40\n    return 0\n", 0),
        ("Int", "    return match Some(t40) {\n        Some(_) => 1\n        None => 0\n    }\n", 0),
        ("Void", "    return match t40 {}\n", 0),
        ("Void", "    return match Some(t40) {\n        None => 0\n    }\n", 0),
        ("Int", "    return match t40 {}\n", 65),
        ("Int", "    return match Some(t40) {\n        None => 0\n    }\n", 65),
        ("Int", "    return match (t40, v) {}\n", 0),
        ("Int", "    return match (v, t40) {}\n", 0),
        ("Int", "    return match (t40, Some(v)) {}\n", 65),
        ("Int", "    return match Some((t39, (t40, v))) {\n        None => 0\n    }\n", 0),
    ];
    for (i, (leaf, tail, code)) in cases.into_iter().enumerate() {
        let text =
            format!("enum Void {{}}\n\nfn f(x: {leaf}, v: Void) -> Int {{\n    let t0 = (x, x)\n{lets}{tail}}}\n");
        let file = source(&format!("shared_{i}.proviso"), &text);
        let output = check_within(&file, 20);
        assert_eq!(output.status.code(), Some(code), "case {i}: {}", stderr(&output));
        if code == 65 {
            assert_eq!(stderr(&output).matches("error[E0311]").count(), 1, "case {i}: {}", stderr(&output));
        }
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

/// Cleanup defects that nest, each `abandon` hitting one while it owns another resource whose
/// `abandon` does the same, are reported in full and end the run with a defect, never a crash
/// of the driver (CLAUDE.md "Stacks"; OPEN_QUESTIONS P5 "Cleanup defects").
#[test]
fn nested_cleanup_defects_never_overflow_the_stack() {
    let text = "resource record Tag {\n    id: Int\n}\n\nimpl Abandon for Tag {\n    fn abandon(take self) {\n        if self.id > 0 {\n            let t = Tag(id: self.id - 1)\n            assert false\n            t.abandon()\n        }\n    }\n}\n\nenum Stop derives(Show) {\n    Halt\n}\n\nfn work(n: Int) fails Stop {\n    let t = Tag(id: n)\n    fail Stop.Halt\n}\n\npub fn main(sys: keep System) fails Stop {\n    try work(n: 50000)\n}\n";
    let file = source("nested_cleanup.proviso", text);
    let output = run(&["run"], &file);
    assert_eq!(output.status.code(), Some(70), "{}", stderr(&output));
    assert_eq!(stderr(&output).matches("leak[Tag]").count(), 50_000);
}

/// A generic call nested in another's argument builds a type that shares its parts, as
/// `Result[T, T]` does, so its tree doubles at each call. Checking it walks each part once,
/// and a message writes its first parts with `…` for the rest (issue #18). The generic
/// records of slice 2.10 double the same way through `let`s.
#[test]
fn types_that_double_check_fast_and_show_in_short() {
    let calls = |n: usize| format!("{}1{}", "dup(x: ".repeat(n), ")".repeat(n));
    let dup = "fn dup[T: Copy](x: T) -> Result[T, T] {\n    return Ok(x)\n}\n\n";
    let pairs: String = (1..=60).map(|i| format!("    let p{i} = P(a: p{}, b: p{})\n", i - 1, i - 1)).collect();
    let pair = "record P[A, B] {\n    a: A\n    b: B\n}\n\n";
    // Two equal types built apart share no part, and an `impl` for `P[A, A]` matches them.
    let twins: String = (1..=40).map(|i| format!("    let r{i} = P(a: r{}, b: r{})\n", i - 1, i - 1)).collect();
    let twice = "interface Twice {\n    fn twice(self) -> Int\n}\n\nimpl[A: Copy] Twice for P[A, A] {\n    fn twice(self) -> Int {\n        return 2\n    }\n}\n\nfn twice_of[T: Twice](x: T) -> Int {\n    return x.twice()\n}\n\n";
    let cases = [
        (format!("{dup}fn f() -> Int {{\n    let x = {}\n    return 1\n}}\n", calls(60)), 0),
        (format!("{dup}fn f() -> Int {{\n    let x: Int = {}\n    return x\n}}\n", calls(60)), 65),
        (format!("{pair}fn f() -> Int {{\n    let p0 = 1\n{pairs}    let q = p60.a.b\n    return 1\n}}\n"), 0),
        (format!("{pair}fn f() -> Int {{\n    let p0 = 1\n{pairs}    let x: Int = p60\n    return x\n}}\n"), 65),
        (
            format!(
                "{pair}{twice}fn f() -> Int {{\n    let p0 = 1\n{pairs}    let r0 = 1\n{twins}    let q = P(a: p40, b: r40)\n    return q.twice() + twice_of(x: q)\n}}\n"
            ),
            0,
        ),
    ];
    for (i, (text, code)) in cases.into_iter().enumerate() {
        let file = source(&format!("doubling_{i}.proviso"), &text);
        let output = check_within(&file, 20);
        let errors = stderr(&output);
        assert_eq!(output.status.code(), Some(code), "case {i}: {errors}");
        if code == 65 {
            assert_eq!(errors.matches("error[E0301]").count(), 1, "case {i}: {errors}");
            assert!(errors.len() < 4_000 && errors.contains('…'), "case {i}: {} bytes", errors.len());
        }
    }
}

/// A type may nest 5,000 levels, deeper than an expression may, as `let`s that each wrap
/// the one before build it. A deeper one is too deep once, where it first is, also when a
/// generic function's result adds its own depth at each call, and nothing it reaches
/// is reported again (OPEN_QUESTIONS P5, Nesting limit; issue #17).
#[test]
fn deep_types_are_too_deep_once() {
    let lets = |n: usize, wrap: &str| -> String {
        (1..=n).map(|i| format!("    let s{i} = {}\n", wrap.replace('#', &format!("s{}", i - 1)))).collect()
    };
    let chain = "record Chain[T] {\n    next: T\n}\n\n";
    let deep = format!(
        "fn deep[T](x: take T) -> {}T{} {{\n    return todo(\"x\")\n}}\n\n",
        "Option[".repeat(50),
        "]".repeat(50)
    );
    let cases = [
        (format!("{chain}fn f() -> Int {{\n    let s0 = 1\n{}    return 1\n}}\n", lets(4_900, "Chain(next: #)")), 0, 0),
        (format!("fn f() -> Int {{\n    let s0 = 1\n{}    return 1\n}}\n", lets(6_000, "Some(#)")), 65, 5_002),
        (
            format!("{chain}fn f() -> Int {{\n    let s0 = 1\n{}    return 1\n}}\n", lets(6_000, "Chain(next: #)")),
            65,
            5_006,
        ),
        (
            format!(
                "{deep}fn f() -> Int {{\n    let s = {}1{}\n    return 1\n}}\n",
                "deep(x: ".repeat(300),
                ")".repeat(300)
            ),
            65,
            6,
        ),
    ];
    for (i, (text, code, line)) in cases.into_iter().enumerate() {
        let file = source(&format!("deep_type_{i}.proviso"), &text);
        let output = proviso().args(["check", "--incomplete"]).arg(&file).output().unwrap();
        let errors = stderr(&output);
        assert_eq!(output.status.code(), Some(code), "case {i}: {}", &errors[..errors.len().min(2_000)]);
        if code == 65 {
            assert_eq!(errors.matches("error[").count(), 1, "case {i}: {}", &errors[..errors.len().min(2_000)]);
            assert!(errors.contains(&format!(":{line}:")) && errors.contains("error[E0905]"), "case {i}: {errors}");
        }
    }
}

/// A type parameter of an `impl` block whose constraint is rejected keeps its name in the
/// block's target, so messages about the block and its `self` name it as written
/// (OPEN_QUESTIONS P5, Generic impls).
#[test]
fn rejected_impl_constraints_keep_their_parameter_names() {
    let text = "interface Count {\n    fn count(self) -> Int\n}\n\nrecord Crate[T] {\n    item: T\n}\n\n\
        impl[T] Count for Crate[T] {\n    fn count(self) -> Int {\n        return 1\n    }\n}\n\n\
        impl[T: Nope] Count for Crate[T] {\n    fn count(self) -> Int {\n        return self.nothing()\n    }\n}\n";
    let file = source("rejected_constraint.proviso", text);
    let output = proviso().arg("check").arg(&file).output().unwrap();
    let errors = stderr(&output);
    assert_eq!(output.status.code(), Some(65), "{errors}");
    assert!(errors.contains("error[E0313]: `Crate[T]` already implements `Count`"), "{errors}");
    assert!(errors.contains("error[E0303]: `Crate[T]` has no method `nothing`"), "{errors}");
    assert_eq!(errors.matches("error[").count(), 3, "{errors}");
}

/// A borrowed value whose copy needs a type parameter to be `Copy` names that parameter,
/// not one in a handle, which neither holds nor reaches its element (REFERENCE §4.8).
#[test]
fn copies_of_borrows_name_the_parameter_that_needs_copy() {
    let text = "use std.pool { Handle }\n\nrecord Two[A, B] {\n    a: A\n    b: B\n}\n\nrecord Phantom[T] {\n    n: Int\n}\n\n\
        fn f[T, U](x: Two[Handle[T], Phantom[U]], y: Two[Handle[T], U]) {\n    let a = x\n    let b = y\n}\n";
    let file = source("copy_names.proviso", text);
    let output = proviso().arg("check").arg(&file).output().unwrap();
    let errors = stderr(&output);
    assert_eq!(output.status.code(), Some(65), "{errors}");
    assert_eq!(errors.matches("which needs `U: Copy`").count(), 2, "{errors}");
    assert_eq!(errors.matches("error[").count(), 2, "{errors}");
}

/// Aliases resolve in an order of their own, without recursing once per alias, so a long
/// chain declared in either order checks, and a long cycle is reported once (E0322). An
/// alias deeper than a type may be is reported once, where it is declared, and its uses
/// aren't reported again (E0905, REFERENCE §15.1).
#[test]
fn long_alias_chains_check_once() {
    let n = 100_000;
    let chain = |order: &dyn Fn(usize) -> String, target: &dyn Fn(usize) -> String| -> String {
        let mut lines: Vec<String> = (1..=n).map(|i| format!("type {} = {}\n", order(i), target(i))).collect();
        lines.reverse();
        lines.concat()
    };
    let reversed = chain(&|i| format!("A{i}"), &|i| format!("A{}", i - 1))
        + &format!("type A0 = Int\n\nfn f(x: A{n}) -> Int {{\n    return x + 1\n}}\n");
    let cycle = chain(&|i| format!("C{i}"), &|i| format!("C{}", if i == n { 1 } else { i + 1 }));
    let deep = 10_000;
    // Signatures alone, which no expression's type reaches, or a body that returns one.
    let nested = |rev: bool, body: &str| {
        let mut lines: Vec<String> = (1..=deep).map(|i| format!("type L{i} = List[L{}]\n", i - 1)).collect();
        if rev {
            lines.reverse();
        }
        lines.concat()
            + &format!(
                "type L0 = Int\n\nrecord R {{\n    f: L{deep}\n}}\n\nfn g(x: L{deep}, y: L9000) -> L{deep} {{\n{body}}}\n\nfn h(x: L4000) -> L4000 {{\n    return x\n}}\n"
            )
    };
    let cases = [
        ("alias_reversed", reversed, 0, None),
        ("alias_cycle", cycle, 65, Some(("E0322", 1))),
        ("alias_nested", nested(false, "    return x\n"), 65, Some(("E0905", 1))),
        ("alias_nested_reversed", nested(true, "    return x\n"), 65, Some(("E0905", 1))),
        ("alias_nested_unused", nested(false, "    return R(f: x).f\n"), 65, Some(("E0905", 1))),
        ("alias_signatures", nested(true, "    loop {\n    }\n"), 65, Some(("E0905", 1))),
    ];
    for (name, text, code, errors) in cases {
        let file = source(&format!("{name}.proviso"), &text);
        let output = check_within(&file, 20);
        let shown = stderr(&output);
        assert_eq!(output.status.code(), Some(code), "{name}: {}", &shown[..shown.len().min(2_000)]);
        if let Some((error, count)) = errors {
            assert_eq!(shown.matches("error[").count(), count, "{name}: {}", &shown[..shown.len().min(2_000)]);
            assert!(shown.contains(&format!("error[{error}]")), "{name}: {}", &shown[..shown.len().min(2_000)]);
            // A deep alias is reported where it is declared, not where it is used.
            if error == "E0905" {
                assert!(shown.contains("`L5000` names a type that nests"), "{name}: {shown}");
            }
        }
    }
}

/// A `pub` alias whose type repeats a part, as `Pair[P1, P1]` does, is checked for what it
/// exposes once per part, though the tree it stands for doubles with each alias (REFERENCE §3).
#[test]
fn a_doubling_pub_alias_checks_in_linear_time() {
    let mut text = String::from("pub record Pair[A, B] {\n    first: A\n    second: B\n}\n\npub type P0 = Int\n");
    for i in 1..=60 {
        text += &format!("pub type P{i} = Pair[P{0}, P{0}]\n", i - 1);
    }
    let file = source("doubling_alias.proviso", &text);
    let output = check_within(&file, 20);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
}

/// An alias used as a value names the type to write instead, by its name alone when the type
/// has type arguments, which an expression doesn't write (REFERENCE §4.8). A message about the
/// calls an example or `expect` marks reads as a sentence.
#[test]
fn alias_and_expect_messages_read_right() {
    let file = source(
        "alias_messages.proviso",
        "record Pair[A, B] {\n    first: A\n    second: B\n}\n\ntype P = Pair[Int, Text]\ntype Opt = Option[Int]\ntype Two = (Int, Int)\ntype Nothing = Unit\n\nfn f(t: Two) {\n    let u = Nothing()\n    let p = P(first: 1, second: \"x\")\n    let o = Opt.Some(1)\n    let w = Two(1, 2)\n}\n\nrecord Box {\n    n: Int\n}\n\nimpl Box {\n    fn give(self) -> Box fails Text {\n        fail \"x\"\n    }\n\n    fn count(self) -> Int fails Int {\n        fail 1\n    }\n}\n\nexample Box(n: 1).give().count() fails _\n\ntest \"t\" {\n    expect Box(n: 1).give().count() fails _\n}\n",
    );
    let errors = stderr(&run(&["check"], &file));
    for expected in [
        "`P` is an alias of the type `Pair[Int, Text]`, and an alias names a type only; write `Pair` here",
        "`Opt` is an alias of the type `Option[Int]`, and an alias names a type only; write `Option` here",
        "`Two` is an alias of the type `(Int, Int)`, and an alias names a type only",
        "the calls this example marks fail with",
        "the calls this `expect` marks fail with",
    ] {
        assert!(errors.contains(expected), "missing {expected:?} in:\n{errors}");
    }
    for nameless in ["`Two` is an alias of the type `(Int, Int)`", "`Nothing` is an alias of the type `Unit`"] {
        assert!(errors.contains(&format!("{nameless}, and an alias names a type only\n")), "{errors}");
    }
}
