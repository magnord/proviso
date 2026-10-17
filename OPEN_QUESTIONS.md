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

**H12 — Always-qualified access.**
- **Now:** `use a.b { X, y }` imports names. `as` resolves collisions, and imported names count for the no-shadowing rule.
- **Options:** every access is qualified (`fs.Dir`, `text.split_lines(…)`), with no imported names at all, as in the Pith design. This removes import lists, collisions, `as` and import shadowing, and every call shows where it comes from. The cost is verbosity.
- **Measure:** tokens per task, failed edits, and calls that resolve to the wrong symbol.

## B. Semantics

**Q1 — One error type per function.**
- **Now:** exactly one, with explicit conversion at call sites (`else fail X(cause: it)`).
- **Options:** unions (`fails A | B`). Unions avoid wrapper enums but complicate `match`, contract diffs and API evolution.

**Q2 — Effect variables and `fails`.**
- **Now:** a `with E` function may not declare its own `fails`.
- **Need:** a rule for combining its own error with the callback's error, without error unions (see Q1).

**Q3 — Scope of the effect system.**
- **Now:** a closure's type records the error it can fail with and the capabilities it captures (`uses`). Effect variables range over both. Permissions are `observes` or `effects`.
- **Open:** whether to also track divergence (examples and `pred` bodies need termination), allocation, or blocking.

**Q4 — Capability retention.**
- **Now:** borrowed by default; `keep` allows retention; derived capabilities inherit their source's retention; `main` receives `keep System`. Reach is tracked transitively, with `uses` on capability, closure, opaque-record and `any` types.
- **Options:** full capture-set types, as in [Scala's capture checking](https://docs.scala-lang.org/scala3/reference/experimental/capture-checking/overview.html), which also track capabilities reachable through object values.
- **Resolve by:** writing a long-lived service (a cache, a connection pool, a server holding a `Db`) and checking whether `keep` plus capability-bearing records is enough.

**Q5 — Subtyping as the only implicit conversion.** There are four subtyping relations: permission sets (`Dir[read, write]` accepted as `Dir[read]`), `uses` sets (`Dir[read]` accepted as `Dir[read] uses Out`), refined types to their base type, and `Never` to any type. Is implicit narrowing acceptable, or should it need `.only::[read]()` at every call?

**Q6 — Permission vocabulary.**
- **Need:** the permissions for each standard capability (`Dir`, `Net`, `Clock`, `Random`, `Env`, `Process`, `In`, `Out`), and whether each is `observes` or `effects`. Because `observes` operations can't change `state`, consuming input from `In` is an `effects` operation under the current rules. Is that the right call?
- **Need:** value-level narrowing: paths, hosts, ports, rate limits.
- **Open:** how a narrowed value appears in `proviso sig`.
- **Found by the goldens (§G):** `Dir`'s full operation list. The reference shows no operations for `list`, `create` or `delete`, so no complete `impl Dir` can be written, and rows 4 and 11 use test-local interfaces instead. Also open: how an observes-only view narrows a capability type that has no permission list, such as `Out` (row 4 as written); whether `write_text` to a new file needs `create`; and which directory `sys.fs` is rooted at.

**Q7 — Partial external writes.**
- **Now:** `sig` reports "may leave partial writes" for a function that has write authority and can fail.
- **Need:** a standard transaction model: write-then-rename for files, real transactions for databases, and something for network effects. Also the rules by which `sig` can claim "transactional".

**Q8 — Cost of `inout` atomicity.**
- **Now:** copy-in/copy-out, with copies elided. Pool generation counters are excluded from rollback.
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
- **Now:** loop back-edges are cancellation points. **Open:** their cost in tight loops, and how many delivery points replay must record.
- **Found by the goldens (§G):** the signatures of `spawn` and `join`: what reach a spawned closure may have, and whether `join` on a task that cannot fail is marked. f18 never joins its infallible task and relies on the scope to wait for it.
- **Found by the goldens (§G):** only `proviso test` can explore schedules (`--schedules N`). `proviso run` can neither explore nor pin one, yet f18's cancellation half means something only on some schedules. The goldens use a `schedules` directive until `run` has an option.

**Q16 — `supervise`.** Does catching defects at task boundaries bring back exceptions as control flow? Options:
- restrict it to top-level server loops;
- require a capability to use it.

**Found by the goldens (§G):** `supervise`'s signature is not given: the closure lifetime it takes, the reach it admits, `Outcome`'s `E` when the work cannot fail, and what a `Defect` value exposes. P3 places `supervise` in no phase, but row 18 needs it by phase 6.

**Q17 — Memory strategy.**
- **Now:** Perceus-style reference counting with reuse.
- **Options:** regions or arenas; Goose-style data stacks for hot modules.
- **Need:** performance targets, and how precise `proviso query costs` must be to be useful.

**Q18 — Pools and handles across tasks.**
- **Now:** pools are unique, and handles carry the pool's identity and a generation.
- **Open:** can pools or handles be sent between tasks? Who owns a pool that several tasks read?

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

**Q27 — Float library functions.**
- **Now:** basic arithmetic, `sqrt` and conversions are bit-identical everywhere, and NaN bit patterns are canonical.
- **Open:** whether the standard library implements `sin`, `exp`, `pow` and the rest itself, which costs speed, so they are reproducible too. The [WebAssembly specification](https://www.w3.org/TR/wasm-core/) shows how much care NaN results alone need.

**Q28 — Where refinements must hold.**
- **Now:** after every assignment. Several fields change together through a whole-value `with`.
- **Options:** check at the end of each exclusive mutation (such as an `inout self` method); an explicit block that opens the invariant temporarily.
- **Resolve by:** writing data structures with multi-field invariants and counting the rewrites the strict rule forces.
- **Found by the goldens (§G):** whether passing `&span.lo`, or assigning `span.lo`, drops facts about `span.hi`. ref §8.3 drops the facts that "mention" the variable. Rows 3 and 16 are rejected either way, but an accepted variant, such as a callee that ensures `x <= 3`, is provable only if facts about the other parts survive.

**Q29 — Cleanup guarantees.**
- **Now:** bounded. `abandon` runs under a deadline, a defect in one `abandon` does not stop the others, and stack exhaustion and out-of-memory are process-fatal.
- **Open:** the default deadline; which operations `abandon` should be allowed to perform; whether a reserved emergency area can make post-mortems after out-of-memory reliable.

**Q30 — Serialized capability state.**
- **Now:** calls on one capability object run one at a time. Proviso-implemented operations run with cancellation masked and commit `state` only on success. Calling back into the same object through a handle is a defect.
- **Open:** whether re-entrancy can be ruled out at compile time; the throughput cost for shared fakes; deadlocks between two capability objects that call each other; long operations that delay cancellation.

**Q31 — Generics over capabilities.**
- **Now:** a type parameter may be instantiated with a type that has reach, and the result has that reach. Generic code needs `T: Copy` to copy, store or return a borrowed `T`.
- **Open:** whether generic code needs a way to name the reach of a type parameter (`T uses C`), for example in generic service containers.

**Q32 — Visible allocation.**
- **Now:** value semantics hide allocation, and `proviso query costs` reports it only after the fact.
- **Proposal:** a function may declare `noalloc`, checked transitively like an effect (as the Pith design's `alloc` effect is), and `sig` shows it. Hot paths in games need a guarantee, not just a report.
- **Open:** how `noalloc` interacts with copy-on-write and reference counting, where an ordinary copy can allocate.

**Q33 — Statement and closure-body forms.** Found by the goldens (§G).
- **Now:** an expression statement must be a call, an assignment or a control expression, and closures and `else` blocks yield their final expression (ref §2). `try f()` is used as a statement (ref §1, §10).
- **Unclear:**
  - whether a call marked with an `else` form (§7.2), such as `out.write_line(t) else ()` or `save(x) else fail E.Io(cause: it)`, counts as a call statement;
  - whether a closure body may use `return`, and what it returns from. §F row 13 writes `{ w(); return "t" }`;
  - how far an unbraced closure body extends: `|| f() else ()` could parse as `(|| f()) else ()`;
  - whether `it` is bound in `e else { … }` when `e` is a fallible call;
  - whether a path that ends in `fail` meets the rule that a non-`Unit` body ends every path with `return` (f07);
  - whether a constructor counts as a call statement. Its value is discarded as an `attempt`'s would be. The toolchain accepts `Point(x: 1, y: 2)` and `Some(1)` as statements and rejects a bare `None` (records/err_construction, option_result/err_fail_attempt).
- **Goldens:** use `try` statements, discard an error with `let _ = attempt f()`, and give a closure with statements a braced body that ends in its value.
- **Decided for phase 2:**
  - A call marked with `try` or with an `else` form counts as a call statement, so `out.write_line(t) else ()` and `save(x) else fail E.Io(cause: it)` are statements. `attempt f()` doesn't count. Its value is a `Result`, and discarding it takes `let _ = attempt f()`.
  - `return` in a closure returns from the closure, as in Rust, Swift and TypeScript. A braced closure body yields its final expression, or the value of a `return` that ends it earlier.
  - An unbraced closure body extends as far as an expression can, so `|| f() else ()` means `|| (f() else ())`.
  - `it` is the error in every `else` form on a fallible call, including `else value` and `else { … }`. It isn't bound for an `Option`. In nested `else` forms, `it` is the error of the innermost one on a fallible call, so in `f() else (o else it)` it is `f`'s error.
  - A path that ends in an expression of type `Never` meets the `return` rule. That covers `fail`, `unreachable`, `todo` and a call that returns `Never`. Phase 1 already treats `unreachable` and `todo` this way.

**Q34 — Closures bound to locals.** Found by the goldens (§G).
- **Now:** a closure's lifetime and captures are decided by the parameter it is passed to (ref §6.7).
- **Unclear:** a closure bound with `let w = || …` (§F row 13) is not passed to anything. Presumably it has the default lifetime, captures by reference, and is checked again wherever it is passed. f13 relies only on its reach being tracked.

**Q35 — Consuming a base resource.** Found by the goldens (§G).
- **Now:** a resource is consumed by a `take` parameter or a `take self` method (ref §10). The reference's `Txn.abandon` consumes `self` without visibly consuming the `Txn` itself.
- **Unclear:** what finally ends a resource that holds no resource fields. The goldens assume that a `take self` method in the type's own `impl`, `abandon` included, consumes `self` when it returns.
- **Options:** that rule; explicit destructuring (`let Txn(..) = self`); a dedicated form allowed only in the type's module.
- **Also unclear:** whether a resource moved out of an `inout` container, as `probes.pop()` does, is owned by the caller or still lent (§10 rule 6). §F row 14 needs it to be owned, so that it can be closed.
- **Decided for phase 2:** the first option.
  - A `take self` method declared in the resource type's own module consumes `self` when it returns normally, so `close`, `commit` and `abandon` need no extra statement. Before it returns, the method must consume or transfer any resource fields of `self` (§10 rule 2). If it fails, `self` is abandoned like any other resource its scope owns (§10 rule 3).
  - Outside the type's module, a `take self` method must pass `self` to something that consumes it.
  - A resource that an operation moves out of an `inout` value, as `probes.pop()` does, is owned by the caller of that operation. Rule 6 still forbids consuming the `inout` value itself. The moved resource is no longer in the container, so the container's owner can't consume it a second time, and §5.4 already makes such an `inout` partial.
- **Rejected:** destructuring adds a line to every `close` and `abandon` that only repeats what `take self` says. A dedicated form adds syntax for the same thing.

**Q36 — The standard library the reference assumes.** Found by the goldens (§G).
- **Now:** the reference names some std items in passing. The rest is meant to come from `proviso sig std` (ref §16, P4), which doesn't exist yet.
- **Need, for the goldens:**
  - the module of `Out` and `In`; the goldens assume `std.io`, where `IoError` lives;
  - `List.pop` and `List.len`;
  - the `ensures` of `List.push`. Row 17 is `refuted` only if they let the verifier build a counterexample; otherwise it is `unknown`, which needs a code of its own;
  - `Pool.insert` and `Pool.get`;
  - a way to open a file as a resource. Rows 8 and 14 use a test-local resource instead.
- **Proposal:** write the `sig` of the std items that phases 1–3 need before phase 1 ends, so goldens and the P4 trial can use them.
- **Decided for phase 2:** [STD.md](STD.md) lists the std items that phases 1 and 2 implement. Items that only phase 3 needs wait for phase 3, with `Dir`.
  - `Out`, `In` and `IoError` are in `std.io`.
  - `List.pop` and `List.len` are in STD.md. The caller owns a popped element (Q35).
  - `List.push`'s `ensures` covers only the length. Whether row 17 is `refuted` or `unknown` is left to phase 5, when the verifier exists.
  - `Pool.insert`, `Pool.get` and the rest of `std.pool` follow §5.5.
  - Phase 2 has no way to open a file. Rows 8 and 14 keep their test-local resource, and `File` arrives with `Dir` in phase 3 (Q6).

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

**T9 — Replay event log.**
- **Now:** an ordered log of capability calls (task, object, operation, arguments, result, completion order) and channel, join and cancellation choices. Replay is simulated by default and reports divergence.
- **Need:** the log format, how arguments are digested or stored, and how precisely divergence is reported.
- **Acceptance test:** two tasks write different contents to the same file through copies of a `Dir`, and both are joined in the same order. Replay must reproduce every result the program observed and report the overlapping writes (see §F).
- **Goldens:** f10 asserts the log entries and the overlap report with provisional directives (`expect-log`, `expect-report`) until this format exists.
- **Found by the goldens (§G):** simulated replay suppresses external effects, stdout included, so f10 checks replay by "no divergence", not by comparing output. "Overlapped" also needs a definition. If one write completes before the other starts, nothing overlapped in time, yet §F row 10 requires a report. f10 assumes it means calls the program doesn't order (no join, channel or scope boundary between them).

**T6 — `diff-contracts` classification.**
- **Need:** precise rules for BREAKING, WEAKENED, STRENGTHENED, AUTHORITY and TRUST.
- **Need:** a way to derive "on failure" guarantees mechanically.

**T7 — Applying fixes.** Only fixes with `changes_behavior: false` may be applied automatically. Which kinds qualify (formatting, imports, adding a missing `try`?), and who decides?

**T8 — Verification determinism.** Can cached proof results be shared across machines and continuous-integration runs? What invalidates them?

**T10 — Runtime reports.** Found by the goldens (§G).
- **Now:** a defect makes `main` exit with code 70 and write a post-mortem (ref §7.3). A resource whose `abandon` hits a defect is "reported as leaked" (§10), and replay "reports" overlapping calls (§9.8).
- **Need:** where these reports go (stderr, the post-mortem, `--json` output) and in what form. Until then, runtime goldens assert them with provisional `expect-report` kinds (tests/DIAGNOSTICS.md).
- **Decided for defects and leaks:**
  - Reports go to stderr, one per event, in the order the events happen. There is no JSON form before `serve` (T4), and `postmortem` is deferred past v1 (P3).
  - Each report is a line `<kind>[<detail>]: <message>` followed by indented `at` and `called from` lines, the format P5 gives defects. `// expect-report: <kind> <detail>` matches the first line.
  - A leak is reported as `leak[<Type>]: …`, right after the defect in `abandon` that caused it. Its `at` line is the binding that owned the resource.
  - A defect during cleanup replaces the error that started the exit. The remaining resources are still abandoned, the error isn't printed, and the run exits with code 70. If several `abandon` calls hit defects, each one is reported, and the first one propagates.
- **Still open:** how overlaps are reported, which comes with replay in phase 6 (T9).

**T11 — `sig` beyond the worked example.** Found by the goldens (§G).
- **Now:** ref §17 shows `sig` output for three items.
- **Need:** how `sig` shows an `inout` that holds a resource (§F row 14: "`sig` says so"), reach through data (a parameter whose records hold capabilities), and the `defects` line under the v1 profile. Also whether enums are listed: §17's output leaves out `pub enum LoadError`.
- **Until then:** f14's `.sig` is matched loosely, line by line (tests/golden/README.md).

## D. Process

**P1 — Spec size.**
- **Question:** can the working reference stay at about 10K tokens once the Q items are resolved?
- **Evidence:** Goose's specification is about 258 KB, roughly 60K tokens. A precise specification will be long.
- **Evidence:** after one consistency review, this reference was already about 11–12K tokens (a rough characters-per-token estimate), because each fix added precision. The soundness review (v3) added kinds, admissibility, capability reach and bounded cleanup, and grew it to about 15K once a follow-up check of v3 was folded in.
- **Plan:** keep this reference short and serve the normative text through `proviso explain`.
- **Measure:** whether agents with only the reference in context make errors that the full specification would have prevented.

**P2 — Name.** *Decided:* **Proviso**, a condition attached to an agreement, which fits contracts that carry their enforcement level.
- **Rejected:** "Writ", because two languages already use the name (a statically typed game-scripting language embedded in Rust, and a Lisp embedded in Go). "Assay", because it collides with tooling for AI agents (a Rust policy engine for agents, and tryassay). "Stet" was the runner-up.
- **File extension:** the full `.proviso`. The short forms collide with verification tools: `.pvs` is used by PVS and `.pv` by ProVerif.
- **Searchability:** search for "proviso lang" or "provisolang".

**P3 — v1 scope and delivery phases.** v1 is a checker plus a tree-walking interpreter; the C backend comes later. Semantics come before tooling, so every guarantee a tool reports survives the §F counterexamples. Each phase ends in something that runs:

| Phase | Scope | Milestone |
|---|---|---|
| 1. Pipeline | lexer, parser, names, scalar types and functions, `fails` and `try`, `assert`, `debug`, `todo`, `unreachable`, `proviso check`, an interpreter for `run` with a stub `System` that provides only `stdout`, the golden test runner | hello world and `fib` run; an `expect-error` golden passes |
| 2. Data and ownership | records, enums, aliases and `distinct` types, methods, `impl` blocks, interfaces and generic functions, `match`, collections and tuples, `Option` and `Result`, `fail`, `else` and `attempt`, `check`, refinements checked at runtime, kinds and moves, `inout` atomicity, resources and `Abandon`, pools and handles, function types and closures with the default lifetime, `keep` parameters and capability-typed fields without retention checks, the std items in [STD.md](STD.md), `example`, `test` and `proviso test` | `parse_user` from the reference's worked example (§17) runs with its examples; §F rows 6–9, 14 and 15 pass |
| 3. Authority | capabilities and permissions, `observes` and `effects`, `uses` and reach, effect variables, retention, closure lifetimes and captures, `cap record` state, `MemDir` written in Proviso | the whole §17 module runs, including its `MemDir` test; §F rows 4, 5, 11 and 13 pass |
| 4. Contracts and tools | contracts under the v1 profile, interface contract rules, `sig`, `fmt`, `diff-contracts` | `proviso sig` reproduces the reference's §17 output as a golden file; §F row 12 passes; the P4 criteria are first measured |
| 5. Verifier | the predicate fragment over linear arithmetic, admissibility, refinements under mutation | §F rows 1–3, 16 and 17 are rejected at compile time; `sig` levels move from `[checked]` to `[verified]` |
| 6. Concurrency and replay | `scope`, tasks, cancellation, channels, `supervise`, `--record` and `replay` | §F rows 10 and 18 pass; the §E cancellation task runs |

**What phase 2 gained.** The first version of this table left out features that phase 2's own rows and milestone need (§G). They moved into phase 2, each only as far as those rows need it:
- **`check` and refinements**, for `parse_user`. Under the v1 profile, phase 2 checks a refinement at runtime whenever a value of the refined type is built or changed. That includes assigning one of its fields, and passing part of it as `inout`, which is checked when the call returns. A false refinement is a `refinement_failed` defect.
- **Function types with parameter modes, and closures with the default lifetime**, for row 15. A closure that captures a value with reach, or mutates a captured `var`, waits for phase 3.
- **`keep` parameters and capability-typed fields**, for rows 8, 9 and 14. Phase 2 doesn't check retention, so phase 3 may reject a program that phase 2 accepts. No tool reports a retention guarantee before `sig` exists in phase 4.
- **Aliases, `distinct` types, methods, `impl` blocks, interfaces and generic functions**, which the implementation already planned for phase 2. Rows 8, 9, 14 and 15 declare `take self` methods and implement `Abandon`.

`supervise` moved into phase 6, with tasks, for row 18. Effect variables (§9.5) are named in phase 3, where the implementation already planned them.

**The v1 profile.** Until phase 5 there is no verifier. Clauses that would be `[verified]`, and refinements, are checked at runtime instead, and `sig` labels them `[checked]`. So v1 never claims a guarantee it doesn't enforce. The enforcement levels are what make this honest staging possible.

**Deferred past v1:**
- the C backend;
- units and tags;
- `any I`;
- `proviso edit`, `trace`, `postmortem` and `serve`;
- packages.

**Test format.** Every phase adds golden tests, as in the Pith design. The format is specified in [tests/golden/README.md](tests/golden/README.md):
- A file with `// expect-error: <code>` header lines must fail `proviso check` with exactly that set of codes. Each expected error is marked on its line with a trailing `// <- <code>` comment, and the runner checks those markers. The codes are catalogued in [tests/DIAGNOSTICS.md](tests/DIAGNOSTICS.md).
- A `.out` file holds the expected stdout of `run`, and an `.err` file holds its expected stderr. A `.sig` or `.fmt` file holds the expected output of `sig` or `fmt`. Header directives give the phase, the exit code, the expected runtime reports, and whether to record and replay.

All 18 §F rows are already written as `tests/golden/fNN_*.proviso`, each tagged with its phase from the table above. Row 14's `.sig` can only be checked from phase 4. Writing them found the gaps in §G.

**P4 — v1 success criteria.** First measured after phase 4, and again after phase 5:
- **The reference is enough.** A fresh agent session given only REFERENCE.md and the `proviso sig` output for `std` writes a correct small program within two `proviso check` attempts. The program is the §17 loader plus a summary report. This is the direct test of P1.
- **Token cost.** The program's token count, measured with one stated tokenizer, is reported next to idiomatic Rust and TypeScript versions. More than 1.5 times the Rust version is a design warning.
- **Counterexamples.** Every §F row assigned to a finished phase passes as a golden test.
- **Standard library quality.** Every public `std` function meets the quality rule in the reference (§16).

**Implementation notes (non-normative).**
- **Host language (decided).** The checker, interpreter and tools are written in Rust. Its integer and float types and UTF-8 strings match Proviso's scalar semantics one to one. Exhaustive matching suits a type checker, and the output is a single binary that starts instantly. The costs are build latency and lifetime friction, which are contained as follows:
  - The workspace is split into crates (`syntax`, `check`, `interp`, `proviso`), so an edit rebuilds only the crates that depend on it.
  - The syntax tree lives in arenas addressed by typed ids, and names are interned.
  - There are no dependencies that rely heavily on procedural macros.
  - The budget is about 2 s for an incremental `cargo check` and about 10 s from an edit to golden results. Both are measured at the end of each phase. At the end of phase 1, an incremental `cargo check` took 0.21 s and an edit took 0.61 s to reach golden results. Both times are from a debug build on the author's machine.

  The runtime library that the C backend later links against is written in C. For phase 6, each task runs on its own OS thread, and the tasks pass a single baton at delivery points. That keeps scheduling deterministic without rewriting the recursive tree-walker.
- **Compilation.** The whole program is compiled and monomorphized into one C file, as Goose does. TinyCC runs it in-process for `proviso run`; the system C compiler produces `proviso build` output.
- **Value storage.** Values use reference counting with in-place reuse, as in Koka's Perceus, plus copy-on-write. Cycles are impossible because nothing stores a reference. An analysis elides `inout` copies (Q17).
- **Pools** use generational slots.
- **Incremental work** is keyed by hashes: item hashes for checking, obligation hashes for the verifier cache, dependency hashes for examples.
- **Costs.** `proviso query costs f` reports the copies and allocations the optimizer could not eliminate.

**P5 — Provisional decisions from the implementation.** Implementing phases 1 and 2 forced choices the reference leaves open. Each is a default to confirm or overturn, not a settled rule:
- **Anchors** count the item's first line as line 1, so `users.parse_user+8` is the eighth line of `parse_user` (§15.1).
- **Exit codes** beyond the reference's 1 and 70 follow the BSD `sysexits` convention that 70 comes from: 64 for usage errors, 65 when `check` fails, and 66 for an unreadable file, including one that is not valid UTF-8. The exception is 101 for an internal error, which is a bug in the toolchain such as an interpreter panic. `--json` applies only to `check`. `run` writes the program's output to stdout, so `run --json` is a usage error (64).
- **Source files** may start with a UTF-8 byte order mark, which the toolchain ignores.
- **Escapes** in text and char literals also include `\'`, which a char literal needs (`'\''`). The reference lists only `\n \t \\ \" \u{…}` (§2).
- **Interpolated text** writes literal braces as `{{` and `}}`, and an interpolation may not span lines. `"""…"""` processes escapes and keeps its content verbatim, with no indentation stripping.
- **No shadowing (H4)** also covers the module's own functions, not only imported names.
- **Operators** stay strict where the reference is silent:
  - `Text` has no `+`; use interpolation.
  - Floats have no `%`.
  - `Bool` has no ordering.
  - Unsigned integers have no unary `-`.
  - An integer literal never becomes a float, so `let x: Float = 1` is an error.
- **Literal expressions** built only from literals and arithmetic, such as `1 + 2` or `0.1 + 0.2`, stay untyped like a single literal. So `0.1 + 0.2 == c` compares as `Float32` when `c` is a `Float32`. The literal rule in §2 mentions only single literals.
- **`Show` for floats** prints the shortest text that reads back as the same value, always with a fraction or an exponent: `1.0`, `0.1`, `1e21`, `NaN`, `inf`.
- **Value positions.** An `if` without `else` used for its value is an error, and a `try` that marks no fallible call is an error (E0703).
- **Members of `Never`.** A field access or method call on an expression of type `Never`, such as `unreachable.f()`, is an error (E0303), as in Rust and TypeScript. There is no type to look the member up in.
- **`fails Never`** is the same as no `fails` clause. `Never` has no values, so a call to such a function cannot fail, and marking it with `try` is an error (E0703). The same holds for a call whose error type is `Never` because `::[Never]` gives it or only `Never` reaches it (see Type arguments). It needs no marker, and `try`, `attempt`, `else` and an example's `fails` on it are E0703, E0706, E0707 and E0708 (issue #30). Where a `todo` hole meets the error type, as in `rethrow(e: todo)`, the code that fills it may give the type, so `attempt`, `else` and an example's `fails` are not reported there (Q25).
- **Nesting limit.** Expressions and blocks may nest at most 1,000 levels deep. Each operator in a chain such as `a + b + c` counts as a level, and so does each link of a call chain such as `a.f().g()`. The toolchain rejects deeper code with E0902 instead of overflowing its own stack.
- **Stack exhaustion** is a defect after 10,000 nested calls, or sooner if deeply nested expressions in each call run the interpreter's 1 GiB stack low. Either way the interpreter reports a `stack_exhausted` defect instead of crashing. The reference makes stack exhaustion process-fatal (§7.3), but phase 1 has no cleanup to skip, so the run ends like any other defect, with exit code 70.
- **Diagnostic codes** are grouped by area, as described in [tests/DIAGNOSTICS.md](tests/DIAGNOSTICS.md). A test keeps that catalog and the one the toolchain serves identical. A construct that isn't implemented yet reports E0901, and the message says whether it is planned for a v1 phase, deferred past v1, or not yet scheduled.
- **Defect reports** go to stderr as `defect[<kind>]: <message>`, followed by `at` and `called from` lines with locations and anchors. A run of identical call sites collapses into one line. This is a provisional answer to T10 for defects; leaks and overlaps are still open.
- **`debug`** writes to stderr as `[debug <path>:<line>:<col>] <values>`, with text and chars quoted and escaped as Proviso literals.
- **Record refinements** (phase 2). A field's `where` sees only that field. A record-level `where` sees every field. Field types and predicates may name records declared later in the file.
- **Runtime refinement checks** (phase 2). A construction, a `with` and an assignment to any part of a value check the refinements of the records they build or change. A nested assignment such as `w.span.hi = 5` checks every record on the path, innermost first. Within one record, the fields' refinements are checked in field order, then the record's, and the first that breaks is reported. The defect names the value, the type and the predicate. A defect inside a predicate, such as an overflow, is traced back to the construction or assignment that checked it.
- **Calls in refinements** (phase 2). A refinement may call any function, since the v1 profile only runs it. §8.1 allows only `pred` functions, which phase 5 brings along with the verifier, so from then on a call of a plain `fn` in a refinement is rejected.
- **`with`** labels every field it replaces, at least one, once each and in declaration order. Unlike a call (H3), it needs the label even on a one-field record, since the label is what says which fields it replaces.
- **`main` and visibility.** `main` is `pub` so that the runtime can call it (§7.4), not to export it, so its signature may mention private types, as f09's `fails Stop` does. §3 makes no such exception.
- **`debug`** writes a record the way a derived `Show` would, whether or not the record derives `Show` or implements it by hand. So `debug` and defect messages run none of the program's code.
- **Variant syntax** (phase 2). A unit variant is written without parentheses in expressions and patterns (`Shape.Empty`, `Empty`), and a variant with fields always takes them, so `Shape.Empty()` and a bare `Circle` pattern are errors. `Shape.Circle` without arguments would be a function value, which waits for closures. A derived `Show` writes a variant qualified, as `Shape.Circle(radius: 2.0)` or `Shape.Empty`.
- **Variant fields** (phase 2) follow the construction rules of records (H3). A one-field variant takes its value unlabelled; with several fields every label is given, once each and in declaration order. A field's `where` sees only that field and is checked at construction, like a record field's. An enum has no `with`, no field access and no enum-level `where`.
- **Pattern fields** (phase 2). §6.4 gives the one-field and rename forms. The rest follows construction: with several fields, the parts name fields in declaration order, each once, and all of them unless the pattern ends with `..`. A pattern may bind a name only once.
- **`match` arms** (phase 2). An arm's body is a block or a single statement, so `Circle(r) => return r` and `_ => fail e` work. A `let` or `var` alone as an arm body is an error. Arms are separated by newlines or commas. In error recovery, a block in an arm that is never closed ends before the next line with a `=>`, since only an arm has one, and a block in a variant field's `where` ends before the next variant, as in a record field.
- **Integer exhaustiveness** (phase 2). §6.3 makes it `[verified]`. Before the verifier exists, integer patterns count as `_` for the static check, and the v1 profile checks the rest at run time (§8.4): a value no arm matches is a `no_arm_matched` defect at the `match`. `Char` and `Text` have no such facts, so only `_` or a binding covers them. A guarded arm never counts toward exhaustiveness.
- **Recursive values** (phase 2) may be as deep as memory allows. Dropping, comparing, showing and `debug`ging one uses no native stack per level, so a list of ten million nodes works like a short one.
- **Empty enums** (phase 2). An enum may have no variants. It has no values, so a `match` on one needs no arms, and a parameter of its type can never be passed. The reference neither allows nor forbids it. Neither has a variant or record with a field of a type without values, nor a type that can only be built from itself, such as `enum Endless { More(next: Endless) }`, so exhaustiveness needs no arm for them, as in Rust.
- **Exhaustiveness limit** (phase 2). Checking exhaustiveness can take exponential work in the number of arms, so the check stops after 10 million steps and reports E0903, as Rust does with its pattern complexity limit. The limit allows a record of a million fields, but not, say, twenty `Bool` fields each matched both ways in arms of their own.
- **Literal patterns** (phase 2) are integer, char, text, `Bool` and `()` literals, with a leading `-` allowed on numbers. A float literal pattern is an error, since float equality is not a sound way to choose a branch. Ranges take integers and chars only.
- **`is` bindings** (phase 2) scope as §6.4 says, and in a `while` condition they also scope over the loop body. They are not in scope after `or`, under `not`, in an `else` or after the `if`. An `is` in a `match` guard binds only within the guard, not in the arm's body.
- **Type arguments** (phase 2). `Some`, `None`, `Ok` and `Err` take their type arguments from the expected type, or else from the field that has them, so `Some(3)` is an `Option[Int]`. Values that meet give each other what they know of their types. §2 says so of a literal and the other operand of a binary operator, and lists no other places where values meet. They are the operands of a comparison or of arithmetic, the branches of an `if` and the arms of a `match`, the matching elements of tuples that meet, a generic call's arguments, an `else` form's value and fallback, and an example's call and value. Their types are joined, so the result doesn't depend on their order or spelling. `if c { None } else { Some(1) }`, `if c { 1 } else { small }` and `(small, None) == (1, Some(2))` check, as their swapped forms do (issue #10). A `let` without a type fixes its value's type there, so a later use doesn't give it, and `let x = None` needs a type. Rust and Swift infer it from later uses instead. A type argument that nothing gives is an error (E0312), reported once at the value that first leaves it open, so `None == None` is one error. A diagnostic writes a type argument not known yet as `_`, as in `Option[_]`. `Never` is a subtype of every type also as a type argument, so `Some(fail e)` is an `Option[T]` for any `T`, and a type argument that only `Never` reaches is `Never`, as in `let k = Some(fail e)`. A field widens a `Never` the expected type gives, also inside a type argument, so `x == Some(Some(1))` checks for an `x: Option[Option[Never]]`. So do the branches, so `nn == (if c { None } else { Some(1) })` checks for an `nn: Option[Never]`, and the branches are an `Option[Int]`. Branches that only `Never` reaches give `Never`, so `if c { Some(fail e) } else { None }` is an `Option[Never]`.
- **`Option` and `Result` values** (phase 2). `Show` and `debug` write them in literal form, as `Some("a")` and `Err(e)`. They implement `Eq`, `Ord`, `Hash` and `Show` when their type arguments do, and `Never` counts as implementing each, since it has no values.
- **`attempt`** (phase 2) reifies only the failures of the calls it marks, which are the calls of its postfix chain (§6.1). A `try` or `fail` in an argument still exits the function, and a defect is never caught. An `attempt` that marks no fallible call is an error (E0706), as a `try` is (E0703). Calls in its chain that fail with different error types are an error (E0301) until §G's question about them is decided, as `try` requires equal types (§7.2).
- **`fail` in a `where` clause** (phase 2) is an error (E0705), as `return` is (E0108), since there is no function to fail.
- **Methods and associated functions** (phase 2). A method is called on a value and an associated function on its type, so `Span.width(s)` is an error (E0303). The qualified form `I.f(x)` exists only for interface methods (§3). A method can't be declared with a keyword's name, such as `unit`, although §2 lets keywords follow `.`; only built-in methods such as `with` have one. A method's `self` comes before its other parameters, and `I.f(x)` takes the receiver first and unlabelled. An `impl` block has no visibility of its own, so its methods are marked `pub` (E0101). An interface is a type only as a parameter's (§4.9), not a field's, binding's or result's (E0307). A call of a method declared twice isn't reported, since it may mean either declaration (§15.1). Interfaces that hold a capability, such as `Out`, wait for phase 3, so implementing one, constraining by one or calling `Out.write_line(…)` is E0901.
- **Method names** (phase 2). A type's own method may not share a name with a method of an interface it implements, by hand or by `derives` (E0212). So `x.f()` never quietly prefers one of them. Nor may an interface implemented for a prelude type declare one of its built-in methods, such as `Text`'s `byte_len`.
- **Implementations** (phase 2). Each method of an `impl I for T` repeats `I`'s declaration with `Self` read as `T`. It has the same receiver, parameter names, modes and types, return type and `fails` (E0314). The parameter names must match because callers label arguments by them (H3). An `impl` without an interface is only for a record or enum of the module (E0315).
- **Hand-written `Show` and `Eq`** (phase 2). A derived `Show` or `Eq`, and that of an `Option` or `Result`, uses the hand-written implementation of any record or enum it holds. A hand-written `show`'s text goes in unquoted. A defect in a hand-written `show` is traced to the interpolation, call or failing `main` that ran it. A derived `Eq` compares fields in declaration order and stops at the first that differs, so a later field's hand-written `eq` may not run.
- **Derived `Ord`** (phase 2) orders variants by declaration, then fields in declaration order (STD.md). `Option` and `Result` follow the order STD.md declares, so `Some(x) < None` and `Ok(x) < Err(e)`, the reverse of Rust. A hand-written `Ord` and `cmp` wait for `Ordering`. STD.md declares `Ord` without `Eq`, so `derives(Ord)` needs no `Eq`, and a type that derives `Ord` but writes its own `eq` can have `a == b` and `a < b` both true.
- **Generic calls** (phase 2). A call's type arguments come from the type the call is expected to have and from its arguments together, as for variants. A mismatch between them is reported at the argument. So `let small: Int8 = id(100)` makes the literal an `Int8`. The arguments are joined as other values that meet are (see Type arguments), so `largest(a: 1, b: small)` and `largest(a: small, b: 1)` both make `T` an `Int8`, and `first(a: Ok(small), b: Err("x"))` is a `Result[Int8, Text]`. The same holds for a generic method or associated function on any receiver, and under `try` and `attempt`. A type parameter used only in `fails` comes from where the failure goes, which is the `Result` an `attempt` is expected to be or is compared with, or the function's own `fails` under `try` (issue #20). A `Never` in the expected type gives a type argument known only in part, which the arguments widen, so `let r: Result[Int8, Never] = ok(1)` checks as `Ok(1)` does, and a type argument that only such a `Never` gives is `Never`. One that nothing gives is an error (E0312), also through another call, so `is_some(None)` needs a type. So `errs(r: ok2(6))` is E0312 for `errs[U](r: Result[Int8, U])` and `ok2[T, E](x: T) -> Result[T, E]`, and checks where an `Option[Never]` is expected. A `Never` argument gives way to the others, so `Some(fail e)` and `Some(1)` make `T` an `Int`. `f::[…](…)` gives the declared type parameters in order, and fixes them, so `pass::[Never](5)` is an error. A parameter of interface type (§4.9) is inferred, since `::[…]` can't name it. The interpreter dispatches on each value's own type instead of monomorphizing (§4.8), which behaves the same while only types without type arguments have an `impl`.
- **Type parameters** (phase 2) are PascalCase and may not take the name of a type, such as `Int`, since H4 rules out shadowing (E0203). One declared twice may have been meant as one, so a call may give either count of type arguments. `main` has none (E0308).
- **Copying a `T`** (phase 2). Moves wait for kinds, so the §4.8 rule is checked where a borrowed `T`, or a value of a type built from `T` such as `Option[T]`, is copied. A borrowed `T` is a parameter without `take` or `inout`, `self`, or a binding from a borrowed value. The value of an `if` or `match` is borrowed when the value of any of its branches may be, so `match (if c { x } else { y }) { v => v }` binds a borrowed `v`. It is copied when it is returned, bound, assigned, failed with, or stored in a construction (E0503). Passing it as an argument borrows it again and needs no constraint.
- **Tuples** (phase 2). A tuple has at least two elements, so `(a,)`, `(T)` and `(T,)` are errors (E0101) and `(a)` only groups. `()` is the unit value, and as a type it is an error, since the unit type is written `Unit`. A trailing comma may follow the last element. A tuple implements `Eq`, `Ord`, `Hash` and `Show` when its elements do, and `Ord` compares element by element from the left. `Show` and `debug` write the literal form, `(1, "a")`, with text and chars quoted. A tuple stores its elements, so building one copies them (§4.8). A tuple has no field access and no `with`. Tuples that meet are joined element by element (see Type arguments), so `(small, None) == (1, Some(2))` compares `(Int8, Option[Int])`s.
- **`let` patterns** (phase 2). A `let` or `var` takes any pattern that matches every value of its type (E0318). Integer literals and ranges, which a `match` leaves to run time, are refutable there, and so are char, text and `Bool` literals. `()` and an enum's only variant are not. A `var` makes every name its pattern binds mutable. A pattern that is one name binds it whatever its case, so `let Total = 1` is reported as misnamed (E0204), and `let None = o` is too. Inside a larger pattern a name is read as in a `match`, so `let (None, x) = p` matches the variant `None`. A `let` that takes a borrowed value apart borrows its parts, as a `match` does (§6.4), so only a part that is copied later needs `Copy`. A `let` whose pattern fails to parse still binds a lone name whatever its case, and otherwise the snake_case names it has, with an unknown type.
- **Wrong-type patterns** (phase 2). A record's pattern against an enum is E0301, as it is against another record, rather than E0303.
- **`else` forms** (phase 2). `e else f` marks the fallible calls of `e`'s postfix chain, as `try` does (§6.1), and their failure runs `f` with the error as `it`. Calls in the chain that fail with different error types are an error (E0301), as for `attempt`. With no fallible call to mark, `e` must be an `Option`, which `else` unwraps (E0707). A `Result` from `attempt` is matched instead, and a call a `try` has marked has already been handled. A call that returns an `Option` and can fail has its failure handled, and its `Option` is not unwrapped. The fallback has the unwrapped type, and a block fallback yields its final expression. The unwrapped type, the fallback's and the type the form is expected to have are joined (see Type arguments), so `let y: Int8 = conv(x: 5) else 0` makes the literal an `Int8` however the call is spelled, and so does `conv(x: 5) else small`. `else` binds loosest and groups to the right, so `o else p else 0` is `o else (p else 0)` and `o else 0 + 1` is `o else (0 + 1)`. An `else` form is a bare value when its left side is (E0102).
- **`check`** (phase 2). `check P else f` needs a `Bool` `P` and an `else` (E0101). The fallback must not finish, so it has type `Never` (E0415), as `fail`, `unreachable` and a call of a function that returns `Never` do. `return`, `break` and `continue` are statements, so a fallback writes them in a block. A block doesn't finish when one of its statements doesn't, which includes a `loop` without `break`. The code after a `check` runs only when `P` holds, so the bindings of an `is` in `P`, through `and` and nested patterns, scope over the rest of the enclosing block, as §8.4's "establishes P" and §6.4's then-block scope suggest. They don't reach the fallback or past the block, and an `is` under `or` or `not` binds nothing, as in an `if`. §8.4 and §17 show `check` without saying what its `else` may do.
- **`parse`** (phase 2) checks the form before the range, so text of the right form that doesn't fit is `OutOfRange`, also beyond 128 bits, and any other text is `Invalid`. A lone sign is `Invalid`. Each integer type and alias has it, as in `Byte.parse(t)`. STD.md declares no other `parse`, so `Bool.parse`, `Float.parse` and `Text.parse` are unknown (E0303).
- **`std.text`** (phase 2) declares only `ParseError`, as STD.md does, so importing anything else is E0205. `trim` removes Unicode `White_Space`. Diagnostics write `std.text.ParseError` when a module type has the name `ParseError`, in types, patterns and the cases a `match` misses. `Show` and `debug` write `ParseError.Empty`, as they write every enum by its own name.
- **Examples** (phase 2). `example f(…) == v` and `example f(…) fails P` mark the calls of the call's postfix chain, as `attempt` does (§7.2). `== v` needs `v` to have the call's type, and that type to implement `Eq` or be a float, which compares by IEEE `==` (§12.2; E0306). `fails P` needs a call that can fail (E0708), and `P` is a pattern for its error. Its left side is a function or method call, not a construction such as `Some(1)`, and anything else there or after the call is E0101. The call and the expected value are joined as the operands of `==` are, so either gives the other its type, as in `example id(1) == small()`. The expected value is an operand of `==`, as the call is, or an `else` form on one, so `f(x) == o else 0` compares with `o else 0` and a comparison after the value is E0103. An example is an expression with no function around it, so `return`, `fail` and `try` in it are errors (E0108, E0705, E0702). An example has no name, so it is never `pub` (E0101).
- **`proviso test`** (phase 2) runs every example in file order, even after one hits a defect. It writes `path:line:col: example passed` or `… example failed: <why>` for each as soon as the example has run, so a result sits next to the example's `debug` output. `<why>` is `expected v, found x`, `expected v, but it failed with e`, `expected a failure matching P, but it returned x`, `expected a failure matching P, but it failed with e`, or `it hit a defect`. Values are written as `debug` writes them, and `P` as the source writes it. Then it writes a count such as `2 examples: 1 passed, 1 failed`, or `1 example: …`. A defect is reported on stderr as under `proviso run`, and the example's own frame is anchored at the module, as `users`, since an example has no name. The exit code is 70 when an example hit a defect, else 1 when one failed, else 0.
- **Example fuel** (phase 2). Each example may take 1,000,000 steps, where a step is a call of a declared function or a turn of a loop, so one that takes exactly a million passes. Built-in methods, constructions and variants take no step, since each one ends. The step after that is a `fuel_exhausted` defect at the call or loop that took it. Deep recursion runs out of stack first, as under `proviso run`. §14 asks for a fuel limit without giving one.
- **Method anchors** (phase 2) are `module.Type.method+N` for a type's own method and `module.Type.Iface.method+N` for an interface's, counting from the method's first line. The rest of a block is `module.Type.impl+N` or `module.Type.Iface+N`, apart from the record's `module.Type+N`. Two `impl Type` blocks share an anchor outside their methods. T3 is still open.

## E. Experiment plan

- **Core subset:** v1 after phase 6 (P3). The success criteria in P4 come first.
- **Syntax variants:** H1–H8 are implemented as alternative surface syntaxes over one syntax tree, so only the surface changes. Each run changes one variable.
- **Tooling variants:** H9 and H10 are toggled on and off.
- **Baselines:** the same tasks in Rust and TypeScript. They measure overall competitiveness only: they cannot separate training familiarity from differences in libraries, tooling and semantics. The within-Proviso tooling ablation (H10) is the clean test of the central thesis.
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

## F. Acceptance counterexamples

These come from the soundness reviews of v2 and v3. Each one broke a guarantee as written. The first implementation must show the stated outcome for every one, and they stay in the test suite permanently. Each row becomes a golden test (P3), and P3 assigns each row to the phase that must make it pass. The tests are in [tests/golden](tests/golden/README.md).

| # | Counterexample | Required outcome |
|---|---|---|
| 1 | `passthrough(n) ensures(tested) result > 0`, then `Positive(passthrough(n))` | Rejected: a `[tested]` clause is not an assumption, so `Positive`'s refinement is unproven |
| 2 | `var span = Span(lo: 1, hi: 4); span.lo = 10` | Rejected: the assignment must prove `10 <= span.hi`, and the binding fact `span.hi == 4` refutes it |
| 3 | `&span.lo` passed to `fn f(x: inout Int)` that sets `x = 10` | Rejected when the call returns: `f`'s `ensures` don't re-establish `lo <= hi` |
| 4 | An `impl Dir` whose `read_text` writes an audit log through a stored `Out` | Rejected: an `observes` operation calls an `effects` operation |
| 5 | `fn g(f: fn() -> Text)` called with a closure that writes a file | Rejected: the closure's type `uses Dir[write]` is not accepted by `fn() -> Text` |
| 6 | `var a = Pool.new(); var b = a; a.insert(10); b.insert(20)` | Rejected: `a` moved into `b`, so `a` is used after the move |
| 7 | A call inserts through `inout Pool`, fails with an error carrying the new handle, and a later insert reuses the slot | The escaped handle is stale: `get` returns `None`, never the later object |
| 8 | `let opened = attempt open_file(…)`, giving `Result[File, FsError]` | Accepted; `opened` is a resource. Matching moves the `File`, and abandoning it closes the file only in the `Ok` case |
| 9 | An `abandon` that hits a defect while two more resources wait | Those two are still abandoned, and the defect and the leak are both reported |
| 10 | Two tasks write different contents to one file through copies of a `Dir` | `--record` logs both calls with their start and completion order. Replay reproduces every result the program observed, including a later read of the file, and reports the two writes as overlapping |
| 11 | `MemDir.write_text` updates its map through a plain `self` | Accepted: `state` fields are shared and assignable, and copies of the capability see the write |
| 12 | An interface method has `requires(checked) P`; an implementation declares `requires P` and assumes it | Rejected: an implementation takes the interface's `requires` exactly as written |
| 13 | `let w = \|\| try dir.write_text(…)`, then `g(\|\| { w(); return "t" })` where `g` takes `fn() -> Text` | Rejected: the outer closure's reach includes `w`'s, so its type `uses` the writable `Dir` |
| 14 | `fn f(fs: inout List[File]) fails E` pops a file, closes it, then fails | The caller's list is not rolled back: a resource-bearing `inout` behaves as `inout(partial)`, and `sig` says so |
| 15 | A callback lent `tx: inout Txn` calls `tx.commit()` | Rejected: a lent resource cannot be consumed |
| 16 | `&span.lo` passed to `x: inout(partial) Int` | Rejected: a part of a refined value cannot be passed as `inout(partial)` |
| 17 | `type Sorted = distinct List[Int] where self.is_sorted()`, then `s.value.push(0)` | Rejected unless `push`'s admissible `ensures` re-establish sortedness |
| 18 | A capability operation is cancelled, or hits a defect, halfway through updating its `state` | The `state` is unchanged: cancellation waits until the operation returns, and a defect discards its changes |

## G. Spec gaps found while writing goldens

Writing the §F rows as complete programs ([tests/golden](tests/golden/README.md)) showed where the reference is ambiguous or too thin to write from. The goldens don't invent semantics there: they take the most literal reading, avoid the construct, or use a test-local stand-in, and their headers say so. Each gap is filed below as a Q, T or P item. The new items (Q33–Q36, T10, T11) are not yet tagged in the reference.

| Gap | Goldens | Filed as |
|---|---|---|
| Whether a call marked with an `else` form is a valid statement; `return` and body extent in closures; whether `it` is bound in `else { … }`; whether a path ending in `fail` counts as returning | f05, f07, f08, f13 | Q33 |
| The lifetime and captures of a closure bound to a local | f13 | Q34 |
| What finally consumes a resource that holds no resource fields; whether one popped from an `inout` container is owned | f08, f09, f14, f15 | Q35 |
| The std items the rows need: `Out`'s module, `List.pop`, `List.push`'s contract, `Pool`'s operations, opening a file | f07, f08, f09, f14, f17 | Q36 |
| `Dir`'s full operation list; narrowing a capability that has no permission list (`Out`); `create` for new files; the root of `sys.fs` | f04, f10, f11 | Q6 |
| Whether `&span.lo` drops facts about `span.hi` | f03, f16 | Q28 |
| The signatures of `spawn`, `join` and `supervise`; `run` can't explore schedules | f10, f18 | Q15, Q16 |
| How defects, leaks and replay overlaps are reported; simulated replay suppresses stdout; what counts as overlapping | f09, f10 | T9, T10 |
| How `sig` shows an `inout` that holds a resource | f14 | T11 |
| Row 13 as written calls the fallible `w` unmarked, and its `try` adds a second reason for rejection. The golden makes `w` infallible so that reach is the only reason. | f13 | the row's wording |
| The error type of an `attempt` whose postfix chain has calls that fail with different types (§6.1, §7.2) | methods/err_methods | P5 |
| P3's phase 2 lacks features its own rows need: `check` (§17's `parse_user`), closures and function types with modes (row 15), and `keep` parameters and capability-typed fields (f08, f09, f14 print through a stored `Out`; retention can still wait for phase 3). P3 also places `supervise` in no phase (f18, phase 6). | f08, f09, f14, f15, f18 | P3 |

The P3 row, Q33, Q35, Q36 and T10 now have decisions for phase 2. Each one still lists the parts that stay open.
