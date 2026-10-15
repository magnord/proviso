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

**Q16 — `supervise`.** Does catching defects at task boundaries bring back exceptions as control flow? Options:
- restrict it to top-level server loops;
- require a capability to use it.

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

**Q29 — Cleanup guarantees.**
- **Now:** bounded. `abandon` runs under a deadline, a defect in one `abandon` does not stop the others, and stack exhaustion and out-of-memory are process-fatal.
- **Open:** the default deadline; which operations `abandon` should be allowed to perform; whether a reserved emergency area can make post-mortems after out-of-memory reliable.

**Q30 — Serialized capability state.**
- **Now:** calls on one capability object run one at a time. Proviso-implemented operations run with cancellation masked and commit `state` only on success. Calling back into the same object through a handle is a defect.
- **Open:** whether re-entrancy can be ruled out at compile time; the throughput cost for shared fakes; deadlocks between two capability objects that call each other; long operations that delay cancellation.

**Q31 — Generics over capabilities.**
- **Now:** a type parameter may be instantiated with a type that has reach, and the result has that reach. Generic code needs `T: Copy` to copy, store or return a borrowed `T`.
- **Open:** whether generic code needs a way to name the reach of a type parameter (`T uses C`), for example in generic service containers.

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

**T6 — `diff-contracts` classification.**
- **Need:** precise rules for BREAKING, WEAKENED, STRENGTHENED, AUTHORITY and TRUST.
- **Need:** a way to derive "on failure" guarantees mechanically.

**T7 — Applying fixes.** Only fixes with `changes_behavior: false` may be applied automatically. Which kinds qualify (formatting, imports, adding a missing `try`?), and who decides?

**T8 — Verification determinism.** Can cached proof results be shared across machines and continuous-integration runs? What invalidates them?

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

**P3 — Order of implementation.** Semantics before tooling, so that every guarantee the tools report survives the counterexamples in §F:
1. **Settle the foundations in the spec:** which facts a proof may assume (§8.4 of the reference) and the four kinds of type (§5.1). v3 does this.
2. **Build a small interpreter** that runs the §F counterexamples, including scopes and cancellation, which the cancellation task in §E needs.
3. **Build the checker over those semantics:** parser, names, types and exhaustiveness, kinds and ownership, capabilities and reach, refinements over linear arithmetic, then `sig` and `diff-contracts`.

The first milestone is a small subset whose reported guarantees survive every §F example. The C backend comes later.

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

These come from the soundness reviews of v2 and v3. Each one broke a guarantee as written. The first implementation must show the stated outcome for every one, and they stay in the test suite permanently.

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
