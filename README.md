# Proviso

**A draft programming language designed for coding agents to write and maintain.**

> **Status:** mostly design. Phase 1 of the v1 implementation is in place: a checker and a tree-walking interpreter for scalar types, functions and control flow, written in Rust. This repository holds the language reference, the reasoning behind it, the open questions that are still to be settled (several of them by experiment), and that implementation.

## Why

The usual debate is which existing language suits coding agents best: C, Rust, TypeScript, Python, even assembly. Proviso starts from a different question: what would a language look like if it were designed only for agents, with no weight given to what humans find pleasant to type?

The premise is that writing code is not an agent's bottleneck. The expensive part is changing code *correctly* while seeing only a small window of it. So Proviso's central goal is:

> **Minimize the code and reasoning a correct change requires.**

It gets there with boundaries an agent can trust, not by removing abstraction.

## Core ideas

- **Signatures that tell the truth.** Every contract states how it is enforced: guaranteed by the type system, verified, checked at runtime, tested, or merely documented.
- **Capabilities instead of ambient authority.** A function can touch files, the network or the clock only through capability parameters such as `Dir[read]`. Its signature shows exactly what it can do, and tests pass in fakes.
- **Visible failure.** Every call that can fail is marked where it happens (`try`, `else fail …`). Errors (expected failures) are kept separate from defects (bugs). There are no exceptions.
- **Value semantics, with explicit exceptions.** Data has value semantics, and mutation needs exclusive access. A failed call leaves its `inout` arguments unchanged. Resources and pools can't be copied, and capability handles share state by design. Object identity uses generational handles that are never reused.
- **Refinements with no hidden checks.** Types like `Int where 0 <= age and age < 150` are proven at every construction site. Data from outside becomes trusted only through a `check` that you write, which also names the error to return. Proofs may rely only on proven, checked or explicitly trusted facts, never on tested ones.
- **Types for the bugs tests miss.** Distinct ID types, units of measure (`Float[m/s]`) and coordinate-space tags (`Vec3[world]`).
- **Structured, replayable concurrency.** No shared mutable memory. Every capability call and scheduling choice is recorded in order, so a run can be replayed exactly.
- **The compiler as a service.** `proviso sig` gives a contract-level view of a module. `proviso diff-contracts` reports how a change alters behaviour. `proviso edit` makes structured edits with stale-edit detection. `proviso trace` and `proviso replay` support debugging without editing code.

## A taste

The example below is abridged from the worked example in [REFERENCE.md §17](REFERENCE.md#17-worked-example):

```proviso
pub record User derives(Eq, Show) {
    name: Text where not name.is_empty()
    age:  Int  where 0 <= age and age < 150
}

// The signature is everything this can do: read files under `dir`, fail with LoadError.
pub fn load_users(dir: Dir[read], path: Path) -> List[User] fails LoadError {
    let text = dir.read_text(path) else fail LoadError.Io(cause: it)
    var users: List[User] = []
    for (i, line) in text.lines().enumerate() {
        users.push(try parse_user(line: line, line_no: i + 1))
    }
    return users
}

pub fn parse_user(line: Text, line_no: Int) -> User fails LoadError {
    let (name_text, age_text) = line.split_once(",")
        else fail LoadError.MissingComma(line_no: line_no)
    let name = name_text.trim()
    check not name.is_empty() else fail LoadError.EmptyName(line_no: line_no)
    let age = Int.parse(age_text.trim())
        else fail LoadError.BadAgeText(line_no: line_no, text: age_text)
    check 0 <= age and age < 150
        else fail LoadError.AgeOutOfRange(line_no: line_no, value: age)
    return User(name: name, age: age)     // the two checks prove User's refinements
}

example parse_user(line: "ada, 36", line_no: 1) == User(name: "ada", age: 36)
```

And this is what a reviewer, human or agent, would see when a change widens a function's authority:

```
$ proviso diff-contracts main..HEAD
users.load_users                                      BREAKING
  ~ authority   dir: Dir[read] → Dir[read, write]     widened: may now write files
  ~ fails       LoadError → LoadOrCacheError           callers' `try` no longer type-checks
  ~ on failure  no external writes → may leave partial writes
```

## Documents

| File | What it is |
|---|---|
| [REFERENCE.md](REFERENCE.md) | The working reference: the whole language in about 15K tokens, meant to stay small enough for an agent to keep in context |
| [RATIONALE.md](RATIONALE.md) | Why the language is designed this way: the needs, goals, alternatives considered, and costs |
| [OPEN_QUESTIONS.md](OPEN_QUESTIONS.md) | Unresolved design questions, the syntax hypotheses to test, and the experiment plan |
| [tests/golden](tests/golden/README.md) | Golden tests: the phase-1 basics and the 18 acceptance counterexamples, which stay pending until their phase is built. [tests/DIAGNOSTICS.md](tests/DIAGNOSTICS.md) is the diagnostic code catalog. |

If you are new, start with RATIONALE.md for the reasoning, then skim REFERENCE.md §1 ("At a glance") and §17 ("Worked example").

## Building and running

The toolchain needs Rust 1.99 or later, and has no dependencies outside the standard library.

```bash
cargo run -- run tests/golden/basics/hello.proviso
```

- `proviso check [--incomplete] [--json] <file>` type-checks a file.
- `proviso run [--incomplete] <file>` checks it and runs its `main`.
- `proviso explain <code>` describes a diagnostic code.

`--incomplete` accepts `todo` holes. A construct that isn't implemented yet is reported as `E0901 not_implemented`, and the message says whether it is planned for a v1 phase, deferred past v1, or not yet scheduled.

`cargo test` runs the unit tests and every golden file under `tests/golden`. A golden file states its phase and its expected errors or exit code in header comments. A file that expects errors also marks each error's line with a trailing `// <- <code>` comment. A file that runs is compared with a `.out` file of its expected stdout and an `.err` file of its expected stderr, and a missing file means no output. The format is specified in [tests/golden/README.md](tests/golden/README.md). To rewrite the expected output after an intended change, run `PROVISO_BLESS=1 cargo test`.

The workspace is split by stage:

| Crate | What it does |
|---|---|
| `syntax` | lexer, parser, syntax tree and the diagnostic code catalog |
| `check` | names and types |
| `interp` | the tree-walking interpreter |
| `proviso` | the command-line tool and the golden test runner |

## What happens next

1. **Build v1 in phases** (OPEN_QUESTIONS P3). v1 is a checker and an interpreter, and each phase ends in a program that runs. Phase 1 is done: hello world and `fib` run, and its golden tests pass. Phase 2 adds data types and ownership. The acceptance counterexamples in OPEN_QUESTIONS §F become golden tests, each assigned to the phase that must make it pass. Until the verifier lands, contracts are checked at runtime, and `sig` says so.
2. **Meet the v1 success criteria** (P4). A fresh agent writes a small program from the reference alone within two attempts, and its token cost is measured against Rust and TypeScript.
3. **Run the experiment** (OPEN_QUESTIONS §E). Agents do the same maintenance tasks across variants that differ in one feature at a time. The tooling ablation is the clean test of the thesis, and Rust and TypeScript serve as baselines for overall competitiveness. The design's own predictions are written down in advance so they can be proven wrong.

## Background

Proviso began as a conversation about which programming language suits coding agents, prompted by [Goose](https://github.com/aardappel/goose). That language was implemented almost entirely by an AI model from a human design, which shows that building a new language is no longer the hard part. Proviso's design was drafted by Claude, an AI coding agent, revised after an external critique and an independent consistency review, and is maintained in this repository. RATIONALE.md tells that story in full.

The name means a condition attached to an agreement. That fits a language built on contracts that state how they are enforced.
