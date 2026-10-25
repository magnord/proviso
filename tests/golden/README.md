# Golden tests

The golden tests of the implementation. `basics/` holds the phase-1 tests. The `fNN_*` files are one test per acceptance counterexample in [OPEN_QUESTIONS §F](../../OPEN_QUESTIONS.md#f-acceptance-counterexamples), written strictly to [REFERENCE.md](../../REFERENCE.md) before the compiler existed, so that they drive the v1 phases (P3). Writing them also showed where the reference is too thin to write a program from; those gaps are listed in OPEN_QUESTIONS §G, and each file's header says when it works around one.

## Files

- `fNN_<what>.proviso` is §F row NN, as a complete single-file program. The runner checks it as a one-module package whose module name is the file stem.
- `fNN_<what>.out` is the expected stdout of `proviso run`, and `fNN_<what>.err` the expected stderr. A missing `.out` means no output on stdout. A missing `.err` means no output on stderr, except in a file with `expect-report`, whose stderr is then checked only for the expected reports. The §F files have no `.err`. They check runtime reports with `expect-report` instead (T10), so they don't depend on a report's message or call sites.
- `fNN_<what>.sig` is the expected output of `proviso sig` for the symbol named by `// sig:`.

- `basics/` holds the phase-1 tests of the implementation, `records/` the tests of slice 2.1, `enums/` those of slice 2.2, `option_result/` those of slice 2.3, `methods/` those of slice 2.4, `parse_user/` those of slice 2.5, `collections/` those of slice 2.6, `ownership/` those of slice 2.7, `resources/` those of slice 2.8, and `closures/` those of slice 2.9. They follow the same format, except that their header has no `§F row` line, and their `.err` files fix the provisional defect output (OPEN_QUESTIONS P5). `inference/` follows the same format. It holds the tests of issues #10, #20, #22, #30 and #37 and of slice 2.9's closures, which check that inference doesn't depend on the order or spelling of operands, arguments and branches, that a literal has its settled type at run time, how unknown type arguments are reported, that a rejected value or an inferred error type causes no cascade, and that a method in a handler's chain leaves its error types to the handler.

Error codes are in [../DIAGNOSTICS.md](../DIAGNOSTICS.md). The runner rejects an `expect-error` code that isn't in the catalog.

## Header

Each file starts with:

```proviso
// §F row N: <the guarantee under test>
// phase: P
```

followed by any directives, each a full-line comment, then a comment explaining the required outcome. The header is the run of comment lines that starts the file, and directives are read only from it. A header comment shaped like a directive, a lowercase word and a colon as in `// note:`, must name a directive, so a misspelled one fails the test, and so does a directive after the header. Explanatory lines start with a capital letter or `§`.

`phase` is required. It is the P3 phase that must make the test pass. The runner skips a test whose phase is later than the implemented one and reports it as pending, after checking its header and markers. From that phase on, a failure is a regression. The runner walks `tests/golden/` recursively, so phase-specific tests can live in subdirectories.

A phase delivered over several pull requests has slices, written `// phase: 2.1`, `// phase: 2.2` and so on, numbered from 1. Each pull request raises `IMPLEMENTED_PHASE` to its own slice, which turns on the tests that slice makes pass. `// phase: 2` still means the whole phase, so the §F rows stay pending until the last slice lands and the implemented phase becomes `2`. Rows 6, 7, 8, 9, 14 and 15 are the exception. Rows 6 and 7 are slice 2.7's milestone, so they are written `// phase: 2.7`, rows 8, 9 and 14 are slice 2.8's, written `// phase: 2.8`, and row 15 is slice 2.9's, written `// phase: 2.9`. That line is the only edit made to them. A whole phase sorts after its slices: `2.1 < 2.2 < 2 < 3.1`. The slices of phase 2 are:

| Slice | Scope |
|---|---|
| 2.1 | the data model, proven by records: declarations, construction, fields, `with`, `derives(Eq, Show)`, refinements checked at runtime |
| 2.2 | enums, `match` and patterns: declarations, construction, exhaustiveness, `is` tests, `derives(Eq, Show)` on enums, record patterns |
| 2.3 | `Option` and `Result`: the prelude enums and their type arguments, construction with inferred type arguments, patterns and exhaustiveness, `Eq` and `Show`, `fail` and `attempt` |
| 2.4 | methods, interfaces and generic functions: `impl` blocks with `self` methods and associated functions, `Self` as a type, `interface` declarations and `impl I for T` for module types and prelude types such as `Int` and `Text`, hand-written `Eq` and `Show`, method resolution and `I.f(x)`, type parameters with constraints, inference and `::[…]`, interface-typed parameters, `Copy`, `derives(Ord, Hash)` |
| 2.5 | the `parse_user` milestone of P3 (REFERENCE §17): tuples, their types and patterns, irrefutable patterns in `let`, the `else` forms and `it`, `check … else`, the `Text` methods of STD.md other than `lines`, `parse` on the integer types and `std.text`'s `ParseError`, `example` declarations, and `proviso test` with its fuel limit. Later than this slice are `impl` blocks for tuple types, the `Text` functions of §12.3 that STD.md doesn't declare, the conversions of §12.1, and `proviso check --examples` |
| 2.6 | collections: `List` and `Map` from STD.md, list and map literals including the empty `[]` and `[:]`, indexing and assignment through an index, `for` over lists and maps with a pattern such as `(i, x)`, the `List` and `Map` methods of STD.md, of which `push`, `pop`, `set` and `remove` change a `var` or a part of one, `Text.lines`, and `Eq`, `Ord`, `Hash` and `Show` for both. Later than this slice are `Set`, which has no literal or constructor yet (OPEN_QUESTIONS Q37), `Array`, `in` tests and ranges outside `for` loops, consuming loops (`for x in take xs`), `inout` and `take` parameters and `&` arguments, the operations that take a closure, such as `map` and `filter`, and `replace`. STD.md declares no `swap`, no `sort`, and none of the predicates of §8.1, such as `is_sorted` |
| 2.7 | kinds, moves and pools: `unique record` declarations, kinds and moves, use after move, `take` and `inout` parameters, `inout self` and `take self` methods, `&` arguments and the exclusivity of a call's arguments (§5.3), `inout` atomicity, consuming loops (`for x in take xs`), and `std.pool`'s `Pool` and `Handle`. §F rows 6 and 7 pass. Later than this slice are `resource` and `opaque` records, `Abandon`, `inout(partial)`, `keep` parameters of a type other than `System`, interface methods with `inout self` or `take self`, `Pool.update`, which takes a closure, aliases and `distinct` types |
| 2.8 | resources: `resource record` declarations and the resource kind of what holds one (§5.1), the prelude's `Abandon` and interface methods with `take self`, §10's rules 1 to 6, abandonment in reverse order on a failure exit, defects in `abandon` with their `leak` reports, `inout` of a resource as `inout(partial)`, `inout(partial)` parameters (§5.4), `keep` parameters of any type and capability-typed fields without retention checks (OPEN_QUESTIONS P3), and plain `opaque` records. §F rows 8, 9 and 14 pass. Later than this slice are closures and function types (slice 2.9), aliases and `distinct` types, interface methods with `inout self`, a list's `replace`, which STD.md doesn't declare yet, resources as map keys, the `uses` of an `opaque` record and retention checks (phase 3), the cleanup deadline and cancellation (phase 6), and resources as type arguments of generic functions, which wait for OPEN_QUESTIONS §G |
| 2.9 | closures and function values: function types with parameter modes and `fails E` (§9.4), closures with the default lifetime and their three body forms (§6.7, OPEN_QUESTIONS Q33), captures by reference that lend what they capture (§10 rule 6), closures bound to locals (Q34), module functions as values with inferred or given type arguments, calls of function values (§3), the overlap of an `&` argument and a closure that reads the same local (§5.3), and `Pool.update`. A function value can't outlive what it captures, so it can't be stored, returned or assigned (E0509). §F row 15 passes. Later than this slice are `uses C` and `with E` on function types and effect variables, `scoped fn` and `keep fn` parameters, `keep` parameters of function types, closures that change a captured `var` or capture a value with reach (phase 3), the operations of `List` and `Map` that take a closure, such as `map` and `filter` (phase 3), aliases and `distinct` types, and, not yet scheduled, `inout(partial)` parameters of function types and an `impl` for a function type |

## Directives

| Directive | Meaning |
|---|---|
| `// expect-error: <code>` | `proviso check` must fail with `<code>`; one line per expected code. |
| `// <- <code>, …` | Trailing comment marking the line where each `<code>` is reported; for an expression that spans lines, the line where it starts. A code listed twice is reported twice on that line. |
| `// expect-exit: <n>` | The exit code of `proviso run`, or of `proviso test` under `run: test`; 0 if absent, 1 when `main` or an example fails, 70 for a defect. The file must have a `main`, unless it has `run: test`. |
| `// flags: --incomplete` | Check and run with `--incomplete`, so `todo` holes are accepted (Q25). |
| `// expect-report: <kind> <detail>` | The run must report this event; see the runtime reports in DIAGNOSTICS.md. |
| `// run: test` | Run the file's examples with `proviso test` instead of its `main`, whose stdout and stderr must match the `.out` and `.err`. The file needs no `main`. |
| `// run: record-replay` | Run with `proviso run --record`, whose stdout must match the `.out`. Then `proviso replay` the log, which must report no divergence. Simulated replay suppresses external effects, stdout included (§9.8), so a clean replay is what shows that every observed result was reproduced. |
| `// expect-log: <operation>` | The recorded log holds a call to this capability operation, with its start and completion order. Write one line per expected call. |
| `// schedules: <n>` | Run under `n` seeded schedules, as `proviso test --schedules` explores them (§11 rule 6). Every run must match. `proviso run` has no such option yet (Q15). |
| `// sig: <symbol>` | Compare `proviso sig <symbol>` with the `.sig` file. |

## Rules

- **Rejected rows.** A file with `expect-error` must fail `proviso check`. Every expected error is marked with `// <-`, and the marked codes must be the `expect-error` codes. Each error must be reported on a line marked with its code, as many times as the marker lists it, and no other error may be reported, so the lines without markers are accepted cases. A diagnostic that depends on a rejected construct is suppressed (§15.1, no cascades), and a test that reports one fails. Warnings are ignored. A file that expects errors doesn't run, so it has no `.out`, `.err`, `expect-exit`, `expect-report` or `run: test`.
- **Accepted rows.** A file without `expect-error` must pass `proviso check`. A file runs if it has `main`, an `.out` or `.err` file, `expect-exit`, `expect-report` or `run: test`, and then it must have `main` unless it has `run: test`. `proviso run`, or `proviso test` under `run: test`, must exit with the expected code and print exactly the `.out` file on stdout and the `.err` file on stderr.
- **Reports.** A report is a stderr line that starts with `<kind>[<detail>]: <message>`, as in `defect[assertion_failed]: assertion failed: n % 2 == 0`. Its kind is one of the runtime reports in DIAGNOSTICS.md, which are `defect`, `leak` and `overlap`. The runner rejects any other kind. The indented lines after it, such as its call sites, belong to it. `expect-report` lists the reports that must appear, and a report listed twice must appear at least twice. Other reports don't fail the test.
- **Alternatives.** Where the language allows several results, the `.out` lists them separated by a line `--- or ---`, and the run must match one of them (f10).
- **Environment.** Each run starts in a new, empty working directory, and `sys.fs` is taken to be rooted there (gap: Q6). Phase 1 has no `sys.fs`, so the runner doesn't set this up yet; it must before phase 3.
- **`.sig` files** are checked from phase 4, when `sig` exists. Until the canonical format covers what they test (T11), each line of the `.sig` must occur in the output in order, as a substring of a line, with runs of whitespace collapsed. After that they become exact goldens.

## Running

`cargo test` runs every file through the runner in `crates/proviso/src/golden.rs`. `PROVISO_BLESS=1 cargo test` rewrites the `.out` and `.err` files from the actual output of a run that exits with the expected code. It doesn't rewrite a `.out` that lists alternatives, it doesn't create an `.err` for a file with `expect-report`, and it never writes markers. Review the diff before committing it.

The runner checks these directives: `phase`, `expect-error`, `expect-exit`, `expect-report`, `flags` and `run: test`, and the `// <-` markers. It also checks `.out` files, including `--- or ---` alternatives, and `.err` files.

If an active file uses a directive the runner can't check yet, the file fails instead of passing unchecked. Those directives are `expect-log`, `run: record-replay`, `schedules`, and `sig` from phase 4. Each of them has to be implemented before its phase is reached.

## Rows

| Row | File | Phase | Required outcome |
|---|---|---|---|
| 1 | `f01_tested_not_assumption` | 5 | E0412 |
| 2 | `f02_field_assignment_keeps_refinement` | 5 | E0412 |
| 3 | `f03_inout_part_reverifies_refinement` | 5 | E0412 |
| 4 | `f04_observes_calls_effects` | 3 | E0601 |
| 5 | `f05_closure_reach_not_admitted` | 3 | E0602 |
| 6 | `f06_pool_used_after_move` | 2.7 | E0501 |
| 7 | `f07_escaped_handle_is_stale` | 2.7 | runs; `.out` |
| 8 | `f08_attempt_result_is_resource` | 2.8 | runs; `.out` |
| 9 | `f09_abandon_defect_spares_the_rest` | 2.8 | exit 70, defect and leak reported; `.out` |
| 10 | `f10_racing_writes_replay` | 6 | record and replay agree, overlap reported; `.out` |
| 11 | `f11_cap_state_shared_and_assignable` | 3 | runs; `.out` |
| 12 | `f12_impl_requires_as_written` | 4 | E0414 |
| 13 | `f13_reach_through_captured_closure` | 3 | E0602 |
| 14 | `f14_resource_inout_is_partial` | 2.8 (`.sig`: 4) | runs; `.out` and `.sig` |
| 15 | `f15_lent_resource_not_consumable` | 2.9 | E0502 |
| 16 | `f16_partial_inout_of_refined_part` | 5 | E0413 |
| 17 | `f17_distinct_value_push_reverifies` | 5 | E0412 |
| 18 | `f18_cap_state_never_half_updated` | 6 | runs; `.out` |

Rows 1–3 and 17 need the verifier. Before phase 5, the v1 profile checks refinements at runtime instead, so `check` accepts these files. Row 16's rule is static, so it may pass before phase 5.
