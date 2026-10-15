use std::process::ExitCode;

use proviso::{IMPLEMENTED_PHASE, compile, exit, run};
use proviso_check::Options;
use proviso_syntax::diag::codes;

const USAGE: &str = "\
usage: proviso <command> [options]

commands:
  check [--incomplete] [--json] <file>   type-check a file
  run [--incomplete] <file>              check a file, then run its `main`
  explain <code>                         describe a diagnostic code, such as E0301
  version                                print the version and implemented phase

exit codes: 0 success, 1 `main` failed, 64 usage, 65 check errors, 66 unreadable file, 70 defect
";

fn main() -> ExitCode {
    let code = real_main();
    ExitCode::from(u8::try_from(code).unwrap_or(1))
}

fn real_main() -> i32 {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = args.first() else {
        eprint!("{USAGE}");
        return exit::USAGE;
    };
    match command.as_str() {
        "check" | "run" => check_or_run(command == "run", &args[1..]),
        "explain" => explain(&args[1..]),
        "version" | "--version" => {
            println!("proviso {} (v1 phase {IMPLEMENTED_PHASE})", env!("CARGO_PKG_VERSION"));
            exit::OK
        }
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            exit::OK
        }
        other => {
            eprint!("proviso: unknown command `{other}`\n\n{USAGE}");
            exit::USAGE
        }
    }
}

fn check_or_run(is_run: bool, args: &[String]) -> i32 {
    let mut opts = Options::default();
    let mut json = false;
    let mut path = None;
    for arg in args {
        match arg.as_str() {
            "--incomplete" => opts.incomplete = true,
            "--json" if !is_run => json = true,
            flag if flag.starts_with("--") => {
                eprintln!("proviso: unknown option `{flag}`");
                return exit::USAGE;
            }
            file if path.is_none() => path = Some(file),
            _ => {
                eprintln!("proviso: expected one file");
                return exit::USAGE;
            }
        }
    }
    let Some(path) = path else {
        eprint!("{USAGE}");
        return exit::USAGE;
    };
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("proviso: cannot read {path}: {err}");
            return exit::NO_INPUT;
        }
    };
    let mut compiled = compile(path, text, opts);
    if is_run {
        compiled.require_main();
    }
    if json {
        print!("{}", compiled.render_json());
    } else {
        eprint!("{}", compiled.render());
    }
    if compiled.has_errors() {
        return exit::CHECK_ERRORS;
    }
    if !is_run {
        return exit::OK;
    }
    run(&compiled, &mut std::io::stdout(), &mut std::io::stderr())
}

fn explain(args: &[String]) -> i32 {
    let [code] = args else {
        eprintln!("usage: proviso explain <code>");
        return exit::USAGE;
    };
    match codes::find(code) {
        Some(code) => {
            println!("{} {}\n{}", code.id, code.kind, code.summary);
            exit::OK
        }
        None => {
            eprintln!("proviso: unknown diagnostic code `{code}`");
            exit::USAGE
        }
    }
}
