use std::io::Write;
use std::process::ExitCode;

use proviso::{IMPLEMENTED_PHASE, compile, exit, run, test};
use proviso_check::Options;
use proviso_syntax::diag::codes;

const USAGE: &str = "\
usage: proviso <command> [options]

commands:
  check [--incomplete] [--json] <file>   type-check a file
  run [--incomplete] <file>              check a file, then run its `main`
  test [--incomplete] <file>             check a file, then run its examples
  explain <code>                         describe a diagnostic code, such as E0301
  version                                print the version and implemented phase

--incomplete accepts `todo` holes. --json prints one diagnostic per line as JSON on stdout.
A program writes to stdout; its `debug` output, failures and defects go to stderr.
`test` writes each example's result and a count to stdout; defects still go to stderr.

exit codes: 0 success, 1 `main` or an example failed, 64 usage, 65 check errors,
66 unreadable file, 70 defect, 101 internal error
";

/// Writes to stdout. A reader that has gone away, as in `proviso check --json f | head`,
/// is not an error: the exit code still carries the result.
fn out(text: &str) {
    let _ = std::io::stdout().write_all(text.as_bytes());
}

fn err(text: &str) {
    let _ = std::io::stderr().write_all(text.as_bytes());
}

fn main() -> ExitCode {
    let code = real_main();
    ExitCode::from(u8::try_from(code).unwrap_or(1))
}

fn real_main() -> i32 {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = args.first() else {
        err(USAGE);
        return exit::USAGE;
    };
    match command.as_str() {
        "check" => check_or_run(Command::Check, &args[1..]),
        "run" => check_or_run(Command::Run, &args[1..]),
        "test" => check_or_run(Command::Test, &args[1..]),
        "explain" => explain(&args[1..]),
        "version" | "--version" => {
            out(&format!("proviso {} (v1 phase {IMPLEMENTED_PHASE})\n", env!("CARGO_PKG_VERSION")));
            exit::OK
        }
        "help" | "--help" | "-h" => {
            out(USAGE);
            exit::OK
        }
        other => {
            err(&format!("proviso: unknown command `{other}`\n\n{USAGE}"));
            exit::USAGE
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Command {
    Check,
    Run,
    Test,
}

fn check_or_run(command: Command, args: &[String]) -> i32 {
    let is_check = command == Command::Check;
    let mut opts = Options { needs_main: command == Command::Run, ..Options::default() };
    let mut json = false;
    let mut path = None;
    for arg in args {
        match arg.as_str() {
            "--incomplete" => opts.incomplete = true,
            "--json" if is_check => json = true,
            // `run` and `test` print their output on stdout, which JSON would mix with.
            "--json" => {
                err("proviso: `--json` applies only to `check`\n");
                return exit::USAGE;
            }
            flag if flag.starts_with('-') => {
                err(&format!("proviso: unknown option `{flag}`\n"));
                return exit::USAGE;
            }
            file if path.is_none() => path = Some(file),
            _ => {
                err("proviso: expected one file\n");
                return exit::USAGE;
            }
        }
    }
    let Some(path) = path else {
        err(USAGE);
        return exit::USAGE;
    };
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) => {
            err(&format!("proviso: cannot read {path}: {e}\n"));
            return exit::NO_INPUT;
        }
    };
    let compiled = compile(path, text, opts);
    if json {
        out(&compiled.render_json());
    } else {
        err(&compiled.render());
    }
    if compiled.has_errors() {
        return exit::CHECK_ERRORS;
    }
    match command {
        Command::Check => exit::OK,
        Command::Run => run(&compiled, &mut std::io::stdout(), &mut std::io::stderr()),
        Command::Test => test(&compiled, &mut std::io::stdout(), &mut std::io::stderr()),
    }
}

fn explain(args: &[String]) -> i32 {
    let [code] = args else {
        err("usage: proviso explain <code>\n");
        return exit::USAGE;
    };
    match codes::find(code) {
        Some(code) => {
            out(&format!("{} {}\n{}\n", code.id, code.kind, code.summary));
            exit::OK
        }
        None => {
            err(&format!("proviso: unknown diagnostic code `{code}`\n"));
            exit::USAGE
        }
    }
}
