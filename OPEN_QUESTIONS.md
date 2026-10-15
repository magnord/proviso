# Proviso — Open Questions

Companion to [REFERENCE.md](REFERENCE.md); the reasoning behind the design is in [RATIONALE.md](RATIONALE.md). The IDs here match the tags in the reference. Each entry gives:
- **Now:** what the reference currently says.
- **Options:** the realistic alternatives.
- **Resolve by:** how we decide.

The **H** items are experiment variables. They are resolved by measurement (§E), not by argument.

## A. Syntax hypotheses (experiment variables)

**H1 — Block delimiters.**
- **Now:** braces.
- **Options:** labelled ends (`end parse_user`, `end for`, `end match`).
- **Hypothesis:** labelled ends reduce failed text edits (unbalanced blocks after replacing a span) and make every block end a unique edit anchor.
- **Prediction:** ~0 effect on correctness; a small reduction in failed edits, which shrinks further once structured edits (H9) exist.

**H2 — Operator words versus symbols.**
- **Now:** `and`, `or`, `not`, with `not` binding looser than comparison, and `and`/`or` not mixable without parentheses.
- **Options:** `&&`, `||`, `!`.
- **Hypothesis:** a dropped `!` silently flips logic, and words are harder to drop.
- **Prediction:** ~0 effect.

**H3 — Argument labels.**
- **Now:** required when a function has 2 or more parameters (receiver excluded), in declaration order. Optional for one-parameter calls. Not used when calling function values.
- **Options:** always optional; always required; required only between parameters of the same type.
- **Hypothesis:** labels eliminate swapped arguments of the same type.
- **Prediction:** a measurable reduction in swap bugs on tasks with same-typed parameters, and ~0 effect elsewhere.

**H4 — Shadowing.**
- **Now:** banned within a function.
- **Options:** Rust-style rebinding (`let age = age.trim()`).
- **Hypothesis:** shadowing causes stale-name bugs during edits.
- **Prediction:** a small effect.

**H5 — Call-site mutation marker.**
- **Now:** `&x`, as in Swift.
- **Options:** `inout x`; no marker.

**H6 — Fallibility marker.**
- **Now:** a `try` prefix.
- **Options:** a postfix `?`, as in Rust.
- **Hypothesis:** a keyword is more visible when reading code through a narrow window.

**H7 — Interpolation.**
- **Now:** `f"{x}"`.
- **Options:** `"\(x)"`; no interpolation, using concatenation and `show()`.

**H8 — Statement termination.**
- **Now:** a newline, with continuation rules (§2).
- **Options:** semicolons.
- **Risk:** the continuation rules are a source of surprises.

**H9 — Structured edits** (tooling variable). Agents get `proviso edit`, versus text replacement only.

**H10 — Evidence tools** (tooling variable). `sig`, `diff-contracts`, `trace` and `query` on, versus off. This is the test of the central thesis.

**H11 — Explicit type arguments.**
- **Now:** `::[…]`, as in `max::[Int](…)` and `d.to::[cm]()`, so that `x[…]` in an expression is always indexing.
- **Options:** a different bracket for type arguments; no explicit type arguments, using annotations instead.

## B. Semantics

**Q1 — One error type per function.**
- **Now:** exactly one, with explicit conversion at call sites (`else fail X(cause: it)`).
- **Options:** unions (`fails A | B`). Unions avoid wrapper enums but complicate `match`, contract diffs and API evolution.

**Q2 — Effect variables and `fails`.**
- **Now:** a `with E` function may not declare its own `fails`.
- **Need:** a rule for combining its own error with the callback's error, without error unions (see Q1).

**Q3 — Scope of the effect system.**
- **Now:** a closure's type records only the error it can fail with. What it may capture is limited by its lifetime (default, `scoped`, `keep`), and `proviso query effects` reports captured capabilities.
- **Open:** whether to also track divergence (examples and `pred` bodies need termination), allocation, or blocking.

**Q4 — Capability retention.**
- **Now:** borrowed by default; `keep` allows retention; derived capabilities inherit their source's retention; `main` receives `keep System`.
- **Options:** full capture-set types, as in Scala's capture checking.
- **Resolve by:** writing a long-lived service (a cache, a connection pool, a server holding a `Db`) and checking whether `keep` plus capability-bearing records is enough.

**Q5 — Subtyping as the only implicit conversion.** There are three subtyping relations: permission sets (`Dir[read, write]` accepted as `Dir[read]`), refined types to their base type, and `Never` to any type. Is permission subtyping acceptable, or should narrowing need `.only::[read]()` at every call?

**Q6 — Permission vocabulary.**
- **Need:** the permissions for each standard capability (`Dir`, `Net`, `Clock`, `Random`, `Env`, `Process`, `In`, `Out`).
- **Need:** value-level narrowing: paths, hosts, ports, rate limits.
- **Open:** how a narrowed value appears in `proviso sig`.

**Q7 — Partial external writes.**
- **Now:** `sig` reports "may leave partial writes" for a function that has write authority and can fail.
- **Need:** a standard transaction model: write-then-rename for files, real transactions for databases, and something for network effects. Also the rules by which `sig` can claim "transactional".

**Q8 — Cost of `inout` atomicity.**
- **Now:** copy-in/copy-out, with copies elided.
- **Open:** how often hot loops need `inout(partial)`.
- **Resolve by:** benchmarks once a backend exists.

**Q9 — The refinement fragment.**
- **Open:** non-linear arithmetic, richer quantifiers, recursive `pred`s.
- **Open:** which solver to use, and how to keep budget units stable across solver upgrades so cached results stay valid.

**Q10 — Default enforcement level.** `ensures` defaults to `[verified]`. Will agents reach for `(tested)` too readily when verification fails? Possible policies:
- a lint;
- a review gate on weakenings reported by `diff-contracts`;
- requiring a stated reason.

**Q11 — `TextPos` validity.**
- **Now:** a position is valid only for its own text; misuse is a defect.
- **Options:** a type-level brand that ties a position to its text.

**Q12 — Laziness.**
- **Now:** collection operations are eager.
- **Problem:** lazy pipelines interact with effects (a failure surfaces only when the result is consumed) and with resources (streaming a file's lines).
- **Need:** an iterator protocol, which depends on Q13.

**Q13 — Interface features.**
- **Default methods:** currently none.
- **Associated types:** needed for an `Iterator[Item]` protocol.
- **Operator interfaces:** currently `Add`, `Sub`, `Mul`, `Div` and `Neg`; are they enough for vectors and units?

**Q14 — Dynamic dispatch (`any I`).**
- **Now:** capability types always dispatch dynamically; other interfaces need `any I`.
- **Open:** is `any I` needed in the first version, and what are its representation and cost?
- **Open:** how `proviso query dispatch` presents large target sets.

**Q15 — Concurrency model.**
- **Open:** green threads, OS threads or async I/O.
- **Open:** `select` and timeouts.
- **Open:** cancellation latency in pure loops: should the compiler insert implicit checkpoints at loop back-edges?

**Q16 — `supervise`.** Does catching defects at task boundaries bring back exceptions as control flow? Options:
- restrict it to top-level server loops;
- require a capability to use it.

**Q17 — Memory strategy.**
- **Now:** Perceus-style reference counting with reuse.
- **Options:** regions or arenas; Goose-style data stacks for hot modules.
- **Need:** performance targets, and how precise `proviso query costs` must be to be useful.

**Q18 — Pools and handles across tasks.** Can handles be sent between tasks? Who owns a pool that several tasks read?

**Q19 — Compile-time evaluation.** What may a top-level `let` contain? Is there a general `const fn` facility?

**Q20 — Code generation beyond `derives`.** Deterministic generators whose output can be inspected (`proviso query expand`) and is attributed to its generator. Who may write a generator, and how are its outputs verified?

**Q21 — Interop with C.**
- **Open:** exporting Proviso functions to C, callbacks from C, and layout guarantees for flat types.
- **Open:** replay across `extern` calls, and what to do with an extern that lies about `pure`.

**Q22 — Float equality.** `Float` has no `Eq` or `Hash`, so records with float fields cannot derive `Eq`. Options:
- a `derives(Eq(total))` variant;
- per-field comparison strategies.

**Q23 — Units.**
- **Open:** affine units such as °C and °F; conversions between integer units such as `Int[ms]`, which may need rounding.
- **Open:** functions generic over units (`fn sqrt[U](x: Float[U*U]) -> Float[U]`).
- **Open:** how units display in diagnostics.

**Q24 — Modules and packages.**
- **Open:** package namespaces and versioning.
- **Open:** orphan rules for `impl` across packages.
- **Open:** whether "`as` only to resolve collisions" is workable.

**Q25 — Holes.**
- **Now:** `check`, `run` and `test` accept `todo` with `--incomplete`, and reaching one is a defect. `build` never accepts it.
- **Open:** should CI reject `--incomplete` entirely? Should committed code ever contain holes?

**Q26 — Implicit boxing.** Recursive enums are boxed implicitly. Should the cost be visible in the type, or only through `proviso query costs`?

## C. Tooling

**T1 — Broken code.**
- **Need:** a parsing and checking strategy that stays trustworthy mid-edit.
- **Need:** a definition of when an answer must carry `"partial": true`.
- **Risk:** if queries fail on broken code, agents fall back to grep exactly when they need help most.

**T2 — Revision hashes.** Hash normalized text or the syntax tree? Do comments and doc comments count?

**T3 — Anchors for nested positions.** How do symbol-relative anchors address closures, `match` arms and loop bodies stably?

**T4 — Service protocol.** JSON-RPC, a Language Server Protocol extension, or MCP, ideally with one schema behind all three. Should streaming be used for long verification runs?

**T5 — Recording and replay.**
- **Open:** storage size and retention.
- **Open:** privacy, since recorded capability results can contain secrets. Redaction would need to be declared per capability.

**T6 — `diff-contracts` classification.**
- **Need:** precise rules for BREAKING, WEAKENED, STRENGTHENED, AUTHORITY and TRUST.
- **Need:** a way to derive "on failure" guarantees mechanically.

**T7 — Applying fixes.** Only fixes with `changes_behavior: false` may be applied automatically. Which kinds qualify (formatting, imports, adding a missing `try`?), and who decides?

**T8 — Verification determinism.** Can cached proof results be shared across machines and continuous-integration runs? What invalidates them?

## D. Process

**P1 — Spec size.**
- **Question:** can the working reference stay at about 10K tokens once the Q items are resolved?
- **Evidence:** Goose's specification is about 258 KB, roughly 60K tokens. A precise specification will be long.
- **Evidence:** after one consistency review, this reference is already about 11–12K tokens (a rough characters-per-token estimate), because each fix added precision.
- **Plan:** keep this reference short and serve the normative text through `proviso explain`.
- **Measure:** whether agents with only the reference in context make errors that the full specification would have prevented.

**P2 — Name.** *Decided:* **Proviso**, a condition attached to an agreement, which fits contracts that carry their enforcement level.
- **Rejected:** "Writ", because two languages already use the name (a statically typed game-scripting language embedded in Rust, and a Lisp embedded in Go). "Assay", because it collides with tooling for AI agents (a Rust policy engine for agents, and tryassay). "Stet" was the runner-up.
- **File extension:** the full `.proviso`. The short forms collide with verification tools: `.pvs` is used by PVS and `.pv` by ProVerif.
- **Searchability:** search for "proviso lang" or "provisolang".

**P3 — Order of implementation.** First build a checker for a core subset:
- parser;
- name resolution;
- types and exhaustiveness;
- capabilities and permissions;
- refinements over linear arithmetic;
- `sig` and `diff-contracts`.

A small interpreter for tests is enough to run §E; the C backend comes later.

**Implementation notes (non-normative, moved from the reference).**
- **Compilation.** The whole program is compiled and monomorphized into one C file, as Goose does. TinyCC runs it in-process for `proviso run`; the system C compiler produces `proviso build` output.
- **Value storage.** Values use reference counting with in-place reuse, as in Koka's Perceus, plus copy-on-write. Cycles are impossible because nothing stores a reference. An analysis elides `inout` copies (Q17).
- **Pools** use generational slots.
- **Incremental work** is keyed by hashes: item hashes for checking, obligation hashes for the verifier cache, dependency hashes for examples.
- **Costs.** `proviso query costs f` reports the copies and allocations the optimizer could not eliminate.

## E. Experiment plan

- **Core subset:** the P3 checker plus an interpreter.
- **Syntax variants:** H1–H8 are implemented as alternative surface syntaxes over one syntax tree, so only the surface changes. Each run changes one variable.
- **Tooling variants:** H9 and H10 are toggled on and off.
- **Baselines:** the same tasks in Rust and TypeScript, to measure how much advantage training-data familiarity gives.
- **Tasks:**
  - add an error case;
  - change a data representation;
  - fix a cancellation bug;
  - replace an implementation while preserving its API;
  - rename across modules;
  - add a refined field;
  - add a capability to a deep call chain.

  Each task comes with hidden tests.
- **Metrics:**
  - hidden-test correctness and regressions;
  - tokens, wall time and tool calls;
  - lines read before the first edit;
  - **failed edit applications**, the direct measure for H1 and H8;
  - contract weakenings introduced.
- **Runs:** several models, many repetitions per cell, and seeds recorded. Agent variance is high, so plan the sample sizes before running.

**Predictions** (recorded before measuring, so they can be wrong):
1. H10 (evidence tools) has the largest effect on correctness and regressions.
2. Explicit `check` facts and labels between same-typed parameters (H3) have medium effects.
3. H1, H2, H6 and H7 have effects near zero on correctness; any H1 gain shows up as fewer failed edits.
4. Early on, the Rust and TypeScript baselines beat every Proviso variant on the tasks that depend least on contracts.
