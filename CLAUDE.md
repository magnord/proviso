# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

Proviso is a draft programming language designed for coding agents. The repository holds the design and a Rust implementation that is being built in phases:

- `REFERENCE.md` is the language spec. It is meant to stay small enough (about 15K tokens) for an agent to keep in context, so keep additions tight.
- `RATIONALE.md` explains why the design is the way it is.
- `OPEN_QUESTIONS.md` holds unresolved design questions (§A–§D), the experiment plan (§E), the acceptance counterexamples (§F), and spec gaps found while writing tests (§G). Its **P3** table defines the six v1 delivery phases.
- `crates/` is the v1 toolchain: a checker plus a tree-walking interpreter. Phase 1 (the pipeline, scalar types and functions) and phase 2 (data and ownership) are done. Phase 3 lands in slices, and slices 3.1 (permissions), 3.2 (reach), 3.3 (cap records), 3.4 (modules), 3.5 (the file system) and 3.6 (effect parameters) are done. A program is one file, and the standard library's modules are Proviso source in `crates/check/std/`. `System` provides native `stdin`, `stdout`, `stderr` and `fs`, a `Dir` confined to the run's root (`crates/interp/src/fs.rs`). Its `Net`, `Process`, `Clock`, `Random` and `Env` fields have no operations yet. `std.test`'s `MemDir` is a `Dir` in memory, written in Proviso. `List.map` and `List.filter` take a closure through an effect parameter, and are written in Proviso in the prelude.

Code and test comments cite these documents by section and ID, such as `REFERENCE §7.3`, `OPEN_QUESTIONS P5`, `Q25`, `T10` or `H2`. Follow that convention when a rule comes from the spec.

## Commands

Rust 1.99 or later. The workspace has no dependencies outside the standard library. `rustfmt.toml` sets `max_width = 120`.

```bash
cargo build
cargo test                                   # unit tests, CLI tests, catalog check, and every golden file
cargo test -p proviso-syntax                 # one crate (proviso-syntax, proviso-check, proviso-interp, proviso)
cargo test -p proviso --test golden          # golden files only
cargo test -p proviso --test golden -- --nocapture   # also print the pass/fail/pending summary and pending files
PROVISO_BLESS=1 cargo test                   # rewrite .out/.err goldens from actual output; review the diff
cargo run -- check [--incomplete] [--json] <file.proviso>
cargo run -- run [--incomplete] <file.proviso>
cargo run -- explain <code>                  # e.g. E0901
cargo fmt --all --check                      # CI runs this and the next two on every PR
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

All golden files run inside a single test (`crates/proviso/tests/golden.rs`), and there is no per-file filter. To work on one golden file, run `cargo run -- check` or `cargo run -- run` on it directly. Output paths are printed as given, and `.out`/`.err` files store them relative to `tests/golden`, so reproduce a golden's output from that folder, as in `cd tests/golden && ../../target/debug/proviso run records/x.proviso`.

CI (`.github/workflows/ci.yml`) runs fmt, clippy with `-D warnings`, and the tests on every pull request. Run all three before you call a branch clean. Checks take a moment to register, so a PR with no checks right after opening still has CI.

Shell commands run in zsh on macOS. There is no `timeout`, so use `perl -e 'alarm 60; exec @ARGV' -- cmd`, which exits 142 when time runs out. Quote a word that starts with `=`, such as `'====='`, and a glob in a flag, such as `--include='*.md'`.

## Architecture

The pipeline is split into one crate per stage, and each crate depends only on the ones before it:

1. **`syntax`** (`proviso-syntax`): lexer, parser, AST, source spans, interning, and the diagnostic code catalog (`diag.rs`). AST nodes live in append-only arenas addressed by typed `Id<T>`s (`arena.rs`). One `Ast` holds every module of the program, and `SourceMap` gives each file its own range of offsets, with the program's file at 0.
2. **`check`** (`proviso-check`): name resolution and type checking. It **never rewrites the tree**. What it learns goes into `SideTable`s on `Program`, keyed by AST ids. `check_program` checks the std modules, then the program's, and `enter` swaps in each module's names. A `Ty` owns its parts and names a record by `AdtId`. A function type's parts are its result, `fails` and `uses`, then its parameters from `FN_PARAMS`. The record's declaration lives in `Program::decls` (`decls.rs`), which also answers `implements`, what a type reaches and how a type is displayed.
3. **`interp`** (`proviso-interp`): tree-walking interpreter over the AST plus the checker's `Program`. It trusts the checker, so a missing side-table entry is an interpreter bug, not a user error. Values describe themselves (an integer carries its type, a record its `AdtId`), so the interpreter reads static types only for literals. Copy values are shared behind `Arc` so later phases can hand them to task threads. A `cap record` value is a handle to one `CapObject`, whose `state` sits behind a `Mutex`. Each method call snapshots that `state` and restores it on a failure or a defect.
4. **`proviso`**: the CLI (`main.rs`), the `compile`/`run` driver (`lib.rs`), and the golden test runner (`golden.rs`).

Points that span several files:

- **Phase gating.** `proviso::IMPLEMENTED_PHASE` (in `crates/proviso/src/lib.rs`) is how far the toolchain implements P3: a whole phase such as `1`, or a slice such as `2.1` when a phase lands over several PRs (tests/golden/README.md). The golden runner reports tests for later phases and slices as pending. When the checker meets a construct from a later phase, it reports `E0901 not_implemented` through `Diagnostics::not_implemented` with a `Planned` value (`Phase(n)`, `PastV1` or `Unscheduled`). Use that path for anything not built yet instead of panicking or silently accepting it.
- **Joins.** `Vars::join` in `infer.rs` is `bound_in` with a `Variance`, which a function type's parameters flip. Where values meet, capability permissions intersect and `uses` sets union, and parameter positions do the reverse. The unit tests there check that a join doesn't depend on the order of its inputs.
- **Std.** `STD` in `native.rs` declares the std modules first, in a fixed order. That order pins the `AdtId`s and `IfaceId`s the toolchain names, and `pinned()` asserts them. A std declaration without a body binds through the table in `native.rs`. A std method with a body runs like user code and needs no table entry. A diagnostic in a std file is a toolchain bug, and the golden runner fails on one.
- **Stacks.** Parsing and checking recurse once per nesting level, so `compile` runs them on a 64 MiB thread. The interpreter runs on its own 1 GiB thread, checks how much stack is left, and turns exhaustion into a defect (`MAX_CALL_DEPTH`, `STACK_RESERVE`) rather than a crash.
- **Exit codes** live in `proviso::exit`: 0 ok, 1 `main` or an example failed, 65 check errors, 70 defect (also in an example), 64/66 usage/no input, 101 toolchain bug.
- **No cascades** (REFERENCE §15.1). A diagnostic that depends on an already-rejected construct must be suppressed. Golden tests fail if an extra error is reported.

## Diagnostics

Codes are stable, so a code's meaning never changes once assigned. They are defined in two places that must agree: `tests/DIAGNOSTICS.md` and `crates/syntax/src/diag.rs`. `crates/syntax/tests/catalog.rs` fails if the two disagree. A new code goes into both when a golden test first expects it, even if the checker can't report it until a later phase. Ranges map to REFERENCE sections (E00xx lexical, E01xx syntax, E02xx names, E03xx types, E04xx refinements/contracts, E05xx ownership/resources, E06xx capabilities, E07xx errors, E08xx concurrency, E09xx implementation limits).

## Golden tests

`tests/golden/README.md` is the authoritative spec of the format. In short:

- Each `.proviso` file opens with a comment header. `// phase: N` is required, and directives are read only from the header. A misspelled or misplaced directive fails the test.
- `// expect-error: <code>` and a trailing `// <- <code>` on the offending line mark rejected programs. Lines without markers must check cleanly.
- Check each new golden with `cargo run -- check` before writing the code it tests. An error on a line without a marker is a bug in the test, such as a keyword used as a name. The runner never parses a golden for a later phase, so this is the only early check it gets.
- Programs that run are compared with `.out` (stdout) and `.err` (stderr). A missing file means no output.
- `basics/` holds the phase 1 tests, and the README lists the directories of each slice of phases 2 and 3. The `fNN_*.proviso` files at the top of `tests/golden` are the §F acceptance counterexamples. They were written strictly to REFERENCE.md before the compiler existed, so they test the spec, not the implementation. Record spec gaps in OPEN_QUESTIONS §G rather than bending a test to fit the code.
- If an active golden file uses a directive the runner doesn't support yet (`expect-log`, `schedules`, `run: record-replay`, and `sig` from phase 4), the test fails instead of passing unchecked. Implement the directive before raising `IMPLEMENTED_PHASE` to that phase.

## Tracking work

- The roadmap is OPEN_QUESTIONS P3, and a phase's PRs are the slice table in `tests/golden/README.md`. Pending golden tests are what is left.
- Design questions and spec gaps go in OPEN_QUESTIONS (§A–§D, §G, P5), never in issues, so they stay next to the spec they change.
- Other work that outlives a session goes in a GitHub issue on magnord/proviso. Examples are a review finding left unfixed, a follow-up a PR defers, a commit no one reviewed, or a tooling or skill problem. Link the PR it came from, and close the issue from the PR that fixes it.
- Ask the user before opening an issue.
- A PR that adds a provisional decision to OPEN_QUESTIONS P5 lists each one in its body, so the user can confirm or overturn it.
- A change to a skill, CLAUDE.md or another workflow file goes on its own branch and PR, never on a feature branch, even when the user asks for it in the middle of a task. Sessions started from main need it before the feature PR merges.
- When a brief sets a size target for a PR, compare the diff with it once the goldens exist. If the PR is over, say so and offer the user a split.

## Working with the user

- Commit freely on your own branch. Ask before you push or open a PR.
- Write replies, PR bodies, commit messages and docs in short declarative sentences. Use no em dashes, and no colon as a connector in the middle of a sentence.
- Give each claim its evidence, or label it as measured, inferred or a guess.
- When a tool refuses and names a step for the user, or a configured model or path is unavailable, tell the user and ask before any fallback. This holds even when the user approved the end result. Doing a refused action by hand defeats the check.
- Answer a question the user asks mid-task in visible text, even in one line, before you go back to the work. An answer only in your thinking never reaches them.
