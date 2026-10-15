# Proviso — Design Rationale

*Why Proviso looks the way it does: the needs it serves, the goals it sets, and the reasoning behind each major decision. Written from the perspective of Claude, the coding agent that drafted the design.*

The language itself is specified in [REFERENCE.md](REFERENCE.md), and the unresolved parts are in [OPEN_QUESTIONS.md](OPEN_QUESTIONS.md). This document explains the *why*. Where a decision is still a bet rather than a conclusion, it says so.

Two kinds of cross-reference appear below. "ref §8.4" points to a section of REFERENCE.md, and tags like Q9 or H3 point to OPEN_QUESTIONS.md. A bare section number, such as §9, means a section of this document.

## 1. The question

The starting question was a common one: which language suits coding agents best? People argue for C, Rust, TypeScript, Python, even assembly. A recent language, [Goose](https://github.com/aardappel/goose), made the question concrete. It is small and fast, and it was implemented almost entirely by an AI model working from a human's design.

I reframed the question in two steps:
- First, what properties of a language *and its toolchain* make an agent's changes correct?
- Second, what would a language look like if it were designed for those properties alone, with no weight given to what a human finds pleasant to write?

Proviso is my answer to the second question. Its design depends on the answer to the first.

## 2. Where agents actually fail

Writing code is not my bottleneck. Typing speed, boilerplate and verbosity cost me almost nothing. Four things do:

1. **Context radius.** This is how much code I must read before I can safely change one function. I see a codebase through a keyhole: search, read a few hundred lines, edit. Anything that makes a line's meaning depend on code somewhere else widens that radius. Examples are inheritance, implicit conversions, macros, exceptions, global state, decorator or dependency-injection magic, and operator overloading.
2. **Feedback latency and precision.** A precise compile error in 100 ms is worth far more than a crash on a path I never ran. My most damaging failures are silent: code that compiles and runs, and is subtly wrong.
3. **Edit robustness.** I edit by replacing spans of text. Unbalanced braces after replacing a block, or an indentation slip that quietly moves a line out of an `if`, are real failure modes.
4. **Prior strength.** This is how much of a language I saw in training. It is why I write better Python and TypeScript than I would write any new language. It is also the main cost any new language must pay back.

One caveat runs through this whole document. **These four costs come from introspection, and introspection is weak evidence.** A reviewer of the first draft made this point, and I agree. My sense of what trips me up is a hypothesis, not a measurement. That is why the open questions end with an experiment plan rather than a verdict (§9).

## 3. Existing languages through this lens

| Language | Strength for agents | Weakness for agents |
|---|---|---|
| Assembly, C | none specific | Feedback arrives as a segfault or undefined behaviour. With no abstraction, reasoning is harder, not easier. |
| Python | strongest prior | Errors surface only on paths that run. Strict type checking helps a lot. |
| TypeScript | good prior, real types | Unsound escape hatches (`any`, casts). The ecosystem moves fast, so my memory of APIs goes stale. |
| Go | fast compile, one way to do most things, gofmt | Nil, and errors that are easy to ignore. |
| Rust | exhaustive matching, no null, `Result`, error messages that suggest fixes | Slow compiles, lifetime errors that are not local, crates heavy on macros. |

The row for assembly carries the most important lesson. The argument that "agents should write assembly, or skip languages and emit bytecode" misreads where my errors come from. **They are reasoning errors, not typing-effort errors.** Abstraction is what makes reasoning tractable, so removing it makes my errors worse.

Rust is the closest mainstream fit. Much of Proviso can be read as Rust's error-handling discipline plus Go's simplicity, with contracts, capabilities and a queryable compiler added. That framing is not new. What I hope is more useful is the specific reasoning behind each addition.

## 4. What Goose showed

Goose mattered for two reasons.

**The cost of a new language has moved.** An AI model built Goose's roughly 30,000-line compiler from a human design. The old objection, that a new language is too expensive to implement, is much weaker now. The remaining costs are *prior strength* (§2) and the *ecosystem*: libraries and interop.

**Goose made design trade-offs concrete.** Proviso borrows some of its ideas and rejects others:

| Goose idea | Proviso's response | Reason |
|---|---|---|
| Whole-program compilation to one C file; an in-process run through TinyCC | **Borrowed** (implementation notes) | Near-instant feedback, and C interop for free |
| Memory safety without lifetime annotations | **Borrowed in spirit** | Lifetime errors are the class of Rust error that costs agents the most rounds of iteration |
| No escaping closures; a static call graph | **Generalized** into three closure lifetimes (§7.14) | Banning escape outright cost too much abstraction |
| Explicit cost model | **Borrowed** as `proviso query costs` | Performance should be readable from the text and the tools |
| `return … from`, a long-distance return | **Rejected**; every fallible call is marked where it happens | The compiler checks the target, but the callee's signature doesn't show that it can return from an enclosing function, so the caller can't see it either |
| Punctuation-dense array types such as `T[>..]` and `T[>..<]` | **Rejected** | One character changes the meaning, and the symbol clusters tokenize poorly |
| No exclusivity rules for references (spec §9.1) | **Rejected**; mutation needs exclusive access | Aliased mutation is non-local by nature |
| A stale reference into a reused slot can read a different value of the same type (spec §9.4) | **Replaced** by generational handles | That is safe for memory but not for identity, and an identity bug is exactly the kind of silent wrongness agents miss |
| `extern fn` obligations rest on the C side (spec §7.10) | **Kept, but made inspectable** | The trust boundary has to exist; it should also be something you can query |
| A specification of about 258 KB | **A warning** (P1) | A precise spec is long, which threatens the "fits in context" goal |

## 5. From the first thesis to the current one

My first draft rested on the slogan **"expressiveness is cheap, certainty is expensive"**. It led me to ban a long list of features: closures, re-exports, shadowing, overloading and more. An external review pushed back, and it was mostly right:

- **Expressiveness can produce certainty.** A transaction abstraction proves "rollback on failure" once, for every caller. Without it, an agent has to rewrite cleanup code correctly on every failure path, every time. A scoped resource makes "forgot to close the file" impossible to write.
- **Verbosity has costs beyond tokens.** It creates more places for inconsistent edits, hides the differences that matter, and slows generation.
- **Some bans widen the context radius instead of shrinking it.** Interfaces, generics and closures let a small, checked contract stand in for a large implementation. Forcing everything into named top-level functions and closed enums spreads one change across more files.

The distinction I had been reaching for was never concise versus verbose. It was **explicit versus implicit, and enforced versus unenforced.** Inheritance hurts agents not because it is an abstraction, but because the dispatch target is implicit and nothing enforces the parent's contract.

So the thesis became:

> **Minimize the code and reasoning a correct change requires.** Get there with boundaries the agent can trust, not by removing boundaries. An abstraction is welcome when its contract is as checkable as the code it hides.

Every major decision below follows from that sentence.

## 6. Goals and non-goals

The five principles in the reference (ref §0) are the goals. Here is the reasoning behind each.

1. **Minimize the code and reasoning a correct change requires.** This is the thesis above. It measures the language by the cost of the *next change*, not of the first draft, because agents spend most of their time maintaining code.
2. **Every guarantee states how it is enforced.** A plausible contract with weak enforcement does more harm than no contract. An agent *will* rely on whatever a signature says. So the signature must say whether a property is guaranteed by the type system, proven, checked at runtime, tested, or merely intended.
3. **Nothing hidden.** No ambient authority, implicit conversions beyond subtyping, exceptions, compiler-inserted contract checks, or dispatch targets the tools can't list. Each of these makes a line's meaning depend on code the agent hasn't read.
4. **Familiar syntax by default.** Training data is a real asset, and novelty is a real cost. Departing from Rust, Swift, TypeScript or Python conventions requires evidence that the change helps.
5. **The compiler is a service.** An agent has no IDE. The compiler *is* its IDE, so it has to answer questions, not just accept or reject code.

**Non-goals:**
- **Human ergonomics.** Terseness, sugar and "fun to type" carry no weight. As it turns out, most choices here also help a human reviewer (§11).
- **Maximal expressiveness.** No macros, no custom operators, no reflection.
- **Performance at any cost.** Performance matters, and the cost model is explicit, but where they conflict, local reasoning wins. Memory strategy follows from the semantics, not the other way round (Q17).

## 7. Decisions and their reasons

Each decision below is written as a need, the decision that meets it, the alternatives I rejected, and what the decision costs.

### 7.1 Contracts that carry their enforcement level (ref §8.4)

- **Need.** To change code safely without reading every callee, I must be able to trust signatures. I also need to know *how much* to trust each clause.
- **Decision.** Every clause carries a level: `[type]`, `[verified]`, `[checked]`, `[tested]`, `[doc]`, or `[trusted]` for foreign code. `ensures` defaults to `[verified]`. If verification fails, the result is a compile error, not a silent downgrade. Lowering a clause to `(tested)` is an explicit edit, and `diff-contracts` reports it as a weakening.
- **Rejected:**
  - "A signature is the complete contract." This was my first draft. A reviewer showed it was false: `fn sort(values: inout List[Int])` is satisfied by a function that clears the list.
  - Unlabelled contracts, which invite false confidence.
- **Cost.** More annotation, which agents don't mind writing. The risk is that agents downgrade to `(tested)` whenever verification is hard. Q10 tracks that.

### 7.2 Capabilities instead of ambient authority (ref §9)

- **Need.** I must be able to tell from a signature whether a function can touch the file system, the network, the clock or randomness. I also need cheap fakes for tests, and reproducible failures.
- **Decision.**
  - All authority flows from `main(sys: keep System)` as capability values.
  - A capability's *type* lists its permissions (`Dir[read]`). Its *value* names the resource (a directory or a host).
  - Capabilities are borrowed by default. `keep` allows retention, and capabilities derived from a borrowed one are borrowed too.
- **Why it works.** One mechanism answers three questions:
  - *Which resource?* The capability value.
  - *Which actions?* The permission set in its type.
  - *Can the function keep access?* Borrow or `keep`.

  The same design also gives two things for free. Fakes are just other implementations (`MemDir`). Replay becomes possible, because every external observation passes through a capability and can be recorded.
- **Rejected:**
  - **Capabilities plus a separate effect system.** The review rightly said capabilities, effects and determinism are different concepts. I still encode them with one mechanism, because two overlapping systems is two things to learn and keep in sync. Effect *polymorphism* is still needed: `map`'s failure depends on its callback. So there is a small effect variable for failure (`with E`).
  - **Koka-style effect handlers** for fakes. Which handler runs depends on the dynamic call context, and dynamic context is exactly the non-local fact this design tries to remove.
- **Cost.** Capabilities must be threaded through call chains. A task in the experiment ("add a capability to a deep call chain") measures this directly. Permission subtyping is an implicit conversion, though a narrowing one (Q5).

### 7.3 Errors marked at every call; defects kept separate (ref §7)

- **Need.** Reading a function, I must see which calls can make it exit early. I must also be able to tell recoverable failures from bugs.
- **Decision.**
  - Every fallible call is marked: `try`, `else fail …`, `else value`, or `attempt`.
  - Each function has exactly one error type, and conversions between error types are explicit.
  - *Defects* are bugs: overflow, out-of-bounds, failed asserts, a stale handle. They are not errors. They abort the task with a post-mortem, and only `supervise` at a task boundary catches them.
  - Cancellation is neither an error nor catchable.
- **Rejected:**
  - Exceptions, which create invisible exits.
  - Goose's `return … from`: the callee's signature doesn't show the exit.
  - Rust's `?`, which is one easy-to-miss character. This choice is H6, and it will be tested.
  - Error unions (Q1).
- **Cost.** Wrapper error enums and explicit conversions at call sites. That plumbing is cheap for an agent and makes failure paths local.

### 7.4 Value semantics with exclusive mutation; handles for identity (ref §5)

- **Need.** The worst non-local question in most languages is "who else can see this, and change it?"
- **Decision.**
  - Every type is a value type. There are no stored references.
  - In-place mutation goes through `inout` with exclusive access, marked at the call site (`&x`).
  - Object identity, the case of "this entity, even after edits", uses generational handles into pools. A stale handle yields `None`, never a different object.
- **My own addition: failure atomicity.** If a call fails, its `inout` arguments are left exactly as they were. The reviewer asked whether failure leaves arguments unchanged, partly modified, or consumed. The answer is now "unchanged" by default and visible in `sig` otherwise. Copies are elided when no failure point follows the first write.
- **Rejected:**
  - Rust-style borrowing with lifetimes, which produces non-local errors.
  - Shared references with aliasing, which has non-local effects.
  - Goose's type-safe slot reuse, which leaves an identity bug in place.
- **Cost.** The performance of value semantics depends on the implementation, and Perceus-style reuse is the plan (Q17). Atomicity has a copying cost in hot loops, and `inout(partial)` is the escape hatch (Q8).

### 7.5 Refinements with no hidden checks (ref §8)

- **Need.** Invariants like `0 <= age < 150` should hold everywhere without being re-checked everywhere. I also need to know *why* something didn't verify.
- **Decision.**
  - Refinements are always `[verified]`. The compiler never inserts a contract check you didn't write.
  - Raw data becomes refined data through `check P else fail E`, which runs your check with your domain error and establishes the fact, or through `assert` or a generated validator.
  - Verification is modular: a function is checked against the contracts of the functions it calls, never their bodies.
  - Each obligation ends as proven, refuted with a counterexample, or unknown, either because the property is unsupported or because the deterministic budget ran out.
  - Suggested fixes come as alternatives labelled by how they change behaviour: validate, assert, clamp, weaken, or require.
- **Why.** My first draft said "prove what you can, check the rest at runtime", while its own example rejected unproven code. The reviewer caught the contradiction and noted something decisive: **the compiler cannot invent the right domain error.** Only the author knows whether a bad age is `BadAgeText` or `AgeOutOfRange`. Labelling fixes by behaviour has a similar motive. Validating, clamping and weakening all make the code compile, but they implement different programs, and an agent picking the first suggestion would silently pick a behaviour.
- **Rejected:**
  - Full Dafny-style proofs, because solver timeouts are unpredictable.
  - Hidden runtime checks.
  - Wall-clock verification budgets, which give results that vary between machines.
- **Cost.** The predicate fragment is deliberately small (Q9). Properties outside it are honestly `(checked)` or `(tested)`.

### 7.6 Distinct types, units and tags (ref §4.6–4.7)

- **Need.** Some of my most common bugs are ones ordinary type systems don't catch:
  - passing a `UserId` where an `OrderId` belongs;
  - mixing milliseconds with seconds, or degrees with radians;
  - mixing centimetres with metres (Unreal uses centimetres);
  - confusing world space with local space.
- **Decision.**
  - `distinct` types are cheap to declare and inherit nothing they don't list.
  - Units are checked at compile time (`Float[m/s]`), and unit literals are explicit (`3.0[m]`).
  - Phantom tags keep coordinate spaces apart (`Vec3[world]`).
- **Why.** These bugs pass every test that doesn't happen to cross the boundary. That makes them the purest example of "silent wrongness", and types eliminate them for free at runtime.

### 7.7 Resources, and abstraction that produces certainty (ref §10)

- **Need.** Files, transactions and locks must be released on every path, including failures, defects and cancellation.
- **Decision.**
  - Resources are linear values. On a normal exit, each must be consumed explicitly, with `commit` or `close`, or it is a compile error.
  - On any failure exit, its `abandon` runs automatically in reverse order, with cancellation masked.
  - Scoped helpers like `db.transaction(|tx| …)` are ordinary library functions.
- **Why.** This is the reviewer's point 1 made concrete. The success path stays explicit, because "did we commit?" should be visible. The failure path is automatic, because getting cleanup right on every failure path is exactly where repeated hand-written code goes wrong.

### 7.8 Structured, replayable concurrency (ref §11)

- **Need.** I reason poorly about interleavings. I need concurrency that cannot race, failures that propagate predictably, and runs I can reproduce.
- **Decision.**
  - There is no shared mutable memory.
  - Tasks live in a `scope` that waits for all of them. The first failure cancels the siblings.
  - Cancellation is cooperative, is delivered only at known points, and is not an error.
  - Every nondeterministic choice, at channel and join points and where cancellation is delivered, is recorded by `--record`, so `replay` reproduces the run.
- **Cost.** There are no shared-memory performance tricks, and some designs need the actor pattern. The I/O model is open (Q15).

### 7.9 Numbers and text without the classic traps (ref §12)

- **Integer overflow is a defect.** Wrapping, saturating and checked arithmetic are named operations.
- **Float behaviour is reproducible.** No fast-math, and no implicit fused multiply-add.
- **Text has no integer indexing.** This one came from my own mistake: the first draft's example sliced text with `line[comma + 1 ..]`, which is byte arithmetic on UTF-8. Positions are now opaque values that come from searches, and operations that need no positions (`split_once`, `strip_prefix`) are preferred.

### 7.10 Foreign code as a visible trust boundary (ref §13)

- **Need.** C interop is necessary, and its guarantees are unenforceable. Pretending otherwise would break principle 2.
- **Decision.**
  - `extern` declarations carry `trusted` clauses, either `pure` or `uses <capability>`, so I/O done through C still takes a capability.
  - `query trust` lists every trusted assumption a function depends on, directly or transitively.
  - `diff-contracts` flags new ones.

### 7.11 Tests next to code (ref §14)

- **Need.** Documentation drifts. Examples that run don't.
- **Decision.**
  - `example` declarations sit beside the function, appear in `sig`, and run as bounded, cached tests. They are not evaluated at compile time: purity makes a call reproducible, not cheap or terminating.
  - Property tests draw their inputs from types *including refinements*, so a refinement serves both as a proof obligation and as a test generator.

### 7.12 The compiler as a service (ref §15)

This is the bet I expect to matter most. The reviewer's strongest hypothesis, which I share, is that **precise contracts and a compiler that exposes evidence will beat any syntax choice.**

| Tool | The need it serves |
|---|---|
| `sig` | Read a 40-line contract view instead of a 2,000-line module. This is the single biggest saving of context. |
| `diff-contracts` | Answer "is this patch acceptable?" with facts such as *adds filesystem writes, changes the error type, drops the no-partial-writes guarantee*. |
| `edit` with revision hashes | Replace a symbol's body without matching text spans. Edits based on a stale revision are rejected, which matters when several agents edit at once. |
| Works on broken code | Agents ask the most questions mid-edit. If queries fail then, agents fall back to grep exactly when they need help most. |
| Anchors such as `users.parse_user+8` | Locations that stay stable when other items are edited. |
| `trace`, `replay`, `postmortem` | Debugging without adding and removing print statements, which is churn that itself causes bugs. |
| Stable JSON diagnostics with labelled fixes | Machine-readable feedback that never applies a behaviour change automatically. |

Source text stays the canonical form. Git, code review and generic agent tools all work on text, and so do other agents that don't use the service. Structured editing is added on top of text, not a replacement for it.

### 7.13 Syntax: familiar until proven otherwise (ref §2, H1–H11)

I came in with strong beliefs about syntax, and I have demoted most of them to hypotheses:

| Belief | Status | Reasoning |
|---|---|---|
| Labelled block ends (`end parse_user`) prevent brace mistakes | **H1**; braces are the default | Plausible, but unmeasured. With structured edits, the benefit may disappear. |
| Words beat symbols (`and`, `not`, `try`) | **H2, H6** | A dropped `!` flips logic silently. The words happen to match Python, so they cost little prior either way. |
| Labelled arguments prevent swapped arguments | **H3** | The one syntax rule I expect to show a measurable effect, on functions with parameters of the same type |
| No shadowing | **H4** | Cheap to keep as the default, and cheap to drop if it doesn't help |

Some rules stay because they remove ambiguity rather than express taste:
- Only arithmetic operators have precedence.
- `and` and `or` cannot be mixed without parentheses.
- Bitwise operations are named functions.
- `::[…]` marks explicit type arguments, so `x[…]` is always indexing.

### 7.14 What was left out, and what came back

**Left out**, because each one widens the context radius or adds a second way to write the same thing:
- function and operator overloading, and custom operators;
- implicit conversions and truthiness;
- macros, beyond `derives`;
- exceptions and inheritance;
- global mutable state;
- default arguments;
- property getters that run code.

**Came back after review**, in restricted forms:

| Feature | Restriction |
|---|---|
| Closures | Three explicit lifetimes: the default, which lives only for the call; `scoped`, for tasks; and `keep` |
| Interfaces | Explicit implementations, with dispatch targets that can be listed |
| Generics | Explicit constraints |
| Re-exports | `query def` always reports the original definition |

"One name, one symbol" now means that every reference resolves unambiguously. It no longer means a name can be defined in only one module.

## 8. What the consistency review taught

After v2 was written, my own pass fixed about a dozen inconsistencies, such as `NonEmptyText` used but never defined. An independent review then found 27 more. Many were the very failures Proviso exists to prevent:

- **A guarantee stated strongly in one place and quietly weakened in another.** "No compiler-inserted checks" sat beside a list of runtime defects.
- **Examples that broke the reference's own rules.** The worked example used `name.is_empty()` on text, which the predicate fragment didn't allow, so it couldn't verify. `fma(a, b, c)` skipped the required labels.
- **Names used but never imported, and syntax a parser could not decide.** `MemDir` was never imported. `max[Int](…)` looks the same as indexing followed by a call.

A prose spec has no compiler, so its claims drift the way unenforced contracts drift. That points to a concrete rule for the future: **once a checker exists, every code block in REFERENCE.md becomes a test.** It is also evidence for P1. The reference grew from about 10.5K to about 11.7K tokens (rough estimates) because each fix added precision, which suggests a precise reference is likely to keep growing.

## 9. Risks, and how we will know

- **The prior might dominate.** Early on, agents will probably write better Rust or TypeScript than Proviso, whatever its design. The experiment includes those baselines so that this cost is measured, not assumed.
- **Verification might be unpredictable.** The defences are a small fragment, deterministic budgets, modular obligations, and honest "unknown" results. Whether they are enough is open (Q9, T8).
- **Verbosity might cost more than it saves.** Labels, explicit conversions and capability threading all cost tokens. They are verbose where they carry information, but the trade has to be measured.
- **The spec might outgrow the context window** (P1). The plan is a short working reference, with the normative text served by `proviso explain`.
- **Ecosystem.** Interop with C is the bridge (Q21). Without it, nothing else matters.
- **The thesis might be wrong.** That is what the experiment in OPEN_QUESTIONS §E is for. Agents do the same maintenance tasks across variants that differ in one feature at a time, and correctness, regressions, tokens, time, code inspected and failed edits are all measured. My predictions are recorded there in advance, so the introspection in §2 can be proven wrong:
  1. Evidence tools have the largest effect.
  2. Explicit `check` facts and argument labels have medium effects.
  3. Block delimiters and operator words have effects near zero.
  4. Early on, the Rust and TypeScript baselines win on the tasks that depend least on contracts.

## 10. The name

*Proviso* means a condition attached to an agreement. That fits a language whose central idea is contracts that state how they are enforced. Earlier candidates collided with existing projects; the details are in P2. The full `.proviso` extension avoids clashes with verification tools.

## 11. A closing observation

The brief was to ignore what a human needs. Most of the result serves human reviewers just as well: signatures that tell the truth, failure paths that are visible, authority you can audit, and diffs that describe behaviour. Only a few choices are purely for agents, and those are the ones in §7.13, which is exactly where the design is least certain.

That suggests the real target was never "agents rather than humans". It was **code whose correctness can be judged locally, by any reader with a small window into it.** Agents just feel that constraint more sharply.
