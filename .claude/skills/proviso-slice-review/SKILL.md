---
name: proviso-slice-review
description: Review a Proviso toolchain PR or branch for defects before it merges, with independent lanes, a main baseline build and the bug classes earlier slices shipped. Use whenever you review, re-review or self-review a phase or slice PR in this repo ("review the PR", "do the review", "check this branch before merge"), when you write the review step of a slice brief, and when a review finding or a Codex comment arrives and needs a fix.
---

# Proviso slice review

Every phase 2 slice passed its author's own review and still shipped bugs that a later reviewer found. Most were siblings of a bug the author had just fixed, such as the same rule one level deeper or under another spelling. Reviewers primed with the author's list of bug classes look where the author already looked. This skill sets a floor for every review, so it does not depend on what the last brief remembered to say.

## 1. Set up

- Record the head SHA you review. A later commit is not covered by this review.
- Commit before you dispatch lanes. Give each lane a `git archive` of the reviewed SHA and its own `CARGO_TARGET_DIR`, so the author can keep fixing in the checkout without moving what the lanes read. Build the baseline for a fix review the same way, from the fix's parent commit.
- Build the PR in both profiles (`cargo build` and `cargo build --release`).
- Build main as the baseline without touching another checkout. Run `git archive origin/main | tar -x -C <scratch>/main-src`, then `cargo build --release --manifest-path <scratch>/main-src/Cargo.toml`. The workspace has no dependencies, so a cold build is quick.
- A lane that needs to change code works in its own `git archive` copy, never in the checkout under review, and never sets `PROVISO_BLESS`.
- Run `gh issue list --repo magnord/proviso --state open` and give each primed lane the open issues that touch its area. Unfixed findings from earlier slices live there.
- In a worktree-isolated session, put multi-step shell in a script with literal absolute paths. Say so in every lane's brief.

## 2. Lanes

Run the lanes in parallel, one subagent each. Each lane saves every finding as a small `.proviso` repro. Its header comment gives the expected behavior and the source for it, which is a REFERENCE section, an OPEN_QUESTIONS P5 bullet, a DIAGNOSTICS code or the PR's stated scope.

1. **One lane per changed crate** (syntax, check, interp). Each gets the checklist in step 3.
2. **Regression and capacity.** Run every golden from earlier phases and slices through both binaries with `check`, `check --json` and `run`, plus about 20 new stress programs. Diff stdout, stderr and exit codes, and explain every difference. Measure each capacity that CLAUDE.md or a test states, at the stated size, with the worst per-level shape, in debug and release, on main and on the PR. Reach each size by doubling, with a timeout of about a minute per run. A superlinear curve or a timeout is the finding, so don't wait out long runs at the largest size.
3. **Docs and tests.** Check DIAGNOSTICS.md against diag.rs, each new golden against REFERENCE, each new P5 bullet against actual behavior, the slice table in tests/golden/README.md, and the PR body's claims. Goldens test the spec, not the code.
4. **Unprimed, from another model family.** This reviewer gets only the diff and the spec, with no list of bug classes. The user runs it by hand in Codex, so don't run Codex yourself. Ask the user for its findings and triage them like any lane's. It finds the classes the primed lanes were never told about.

These count as findings:

- a toolchain panic (exit 101) or any other crash;
- a program that checks but behaves against the spec at run time;
- a wrong or missing diagnostic;
- a cascade (REFERENCE §15.1);
- a construct the PR scopes out that is accepted instead of reporting E0901;
- a regression from main;
- a doc, test or PR claim that disagrees with the code.

Style, naming, scoped-out features, and behavior that matches a P5 decision already on the base branch are not findings, unless P5 contradicts REFERENCE. A P5 bullet the PR adds is under review too. It is a finding when it records a limit of the implementation rather than a choice about the language.

## 3. Checklist

These are the classes earlier slices shipped. Give the list to the per-crate lanes, and add each new class a review finds.

- **Recovery at every item keyword.** Parser recovery stops at each item keyword, including the one this slice adds. An unclosed `{` is reported at the brace.
- **No cascades.** A rejected or misspelled declaration, variant, derive, pattern or type produces no errors at its uses. Suppression stops at the rejected construct. An unrelated error beside it or inside its body is still reported, and each new suppression gets a golden line that shows this.
- **Sibling spellings.** A rule holds for qualified and bare constructors, call and method-call forms, inline and let-bound values, both operand orders, one more level of nesting (a pattern inside a pattern, `Option[Option[T]]`), in records, enums and variants alike, and for a value that an `if`, `match` or block produces or that `try` wraps.
- **Sibling lists.** A new keyword, prelude name or form joins every stop set, name list and match arm that names its siblings. Grep for an existing sibling's name to find them.
- **Prelude names.** A user declaration can't take a prelude name, and a slice that adds prelude names keeps the older ones.
- **Uninhabited types.** Empty enums, `Never`, and constructors or fields of those types behave per spec, at the top level and nested.
- **Scope gate in every spelling.** A construct the slice defers reports E0901 whether it is constructed, pattern-matched, tested with `is` or copied with `with`.
- **Order dependence.** Swapping branches, operands or arguments doesn't change what the checker infers. Swap each pair of kinds that give or need type context, which are a literal, a variant, `None`, a generic function or method call, and each of those under `try`, `attempt`, `if` or `match`.
- **Partly known types.** An expected type with an unknown or `Never` part still guides inference through its known parts, at the top level and nested. Code that drops the whole type because one part is unknown is the bug.
- **Deep values.** Drop, `==`, `show` and `debug` of a long recursive value, built in a loop to a million nodes, stay iterative in both profiles.
- **Stated capacities.** CLAUDE.md "Stacks" promises a defect, never a crash. Test each capacity at its stated size with the worst shape, in both profiles.
- **Defect traces.** A defect inside code run for a construction, a predicate or a check traces back to its call site.
- **Codes keep their meaning.** A new error shape gets a new code. Widening an assigned code's summary changes its meaning, which CLAUDE.md forbids. Test a widening by asking whether someone who filters on the old code would now get cases they could not have meant. If so, it needs a new code.

## 4. Findings and fixes

- Reproduce every finding on the PR binary before you report or fix it. Drop what doesn't reproduce.
- Treat a finding as one member of a class. Before fixing it, list its siblings from the checklist and add a golden for each one. The adversarial-tdd skill's step 5 has the method.
- Sabotage each fix with its likely sibling mistake, not a revert. A golden that goes red on a revert only shows it is tied to the fix.
- A fix commit is new code. Before the PR merges, rerun every repro and sibling on it, and give it a short unprimed review. Repeat until a review comes back clean. If the chain stops before that, name the last unreviewed commit in the report and the PR body, and offer an issue for it.
- When a fix round finds another sibling in a mechanism that an open issue or two earlier rounds already flagged, stop adding cases. Ask the user whether to fix the mechanism or accept the limit, and link the issue in the PR body.
- A speed or capacity finding is fixed only when its repro, timed on the fix build, is back near main. A lane's suspected cause is a hypothesis until you profile the build yourself (`sample <pid>` on macOS).
- A finding left unfixed goes in a GitHub issue once the user agrees (CLAUDE.md, Tracking work).

## 5. Report

For each finding, give a one-line title, severity, repro path, command, expected behavior with its source, actual output and suspected code location, most severe first. State the SHA you reviewed next to the PR's head SHA. End with one line on what came out clean.
