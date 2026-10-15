# Golden tests

One test per acceptance counterexample in [OPEN_QUESTIONS §F](../../OPEN_QUESTIONS.md#f-acceptance-counterexamples), written strictly to [REFERENCE.md](../../REFERENCE.md). They exist before any compiler, so they can drive the v1 phases (P3). Writing them also showed where the reference is too thin to write a program from; those gaps are listed in OPEN_QUESTIONS §G, and each file's header says when it works around one.

## Files

- `fNN_<what>.proviso` is §F row NN, as a complete single-file program. The runner checks it as a one-module package whose module name is the file stem.
- `fNN_<what>.out` is the expected stdout of `proviso run`. An optional `.err` holds the expected stderr; no §F file has one yet, because the reference doesn't fix what a defect or failure prints (T10).
- `fNN_<what>.sig` is the expected output of `proviso sig` for the symbol named by `// sig:`.

- `basics/` holds the phase-1 tests of the implementation. They follow the same format, and their `.err` files fix the provisional defect output (OPEN_QUESTIONS P5).

Error codes are in [../DIAGNOSTICS.md](../DIAGNOSTICS.md). The runner rejects an `expect-error` code that isn't in the catalog.

## Header

Each file starts with:

```proviso
// §F row N: <the guarantee under test>
// phase: P
```

followed by any directives, each a full-line comment, then a comment explaining the required outcome. `phase` is required: it is the P3 phase that must make the test pass. The runner skips a test whose phase is later than the implemented one and reports it as pending. From that phase on, a failure is a regression. The runner walks `tests/golden/` recursively, so phase-specific tests can live in subdirectories.

## Directives

| Directive | Meaning |
|---|---|
| `// expect-error: <code>` | `proviso check` must fail with `<code>`; one line per expected code. |
| `// <- <code>` | Trailing comment marking the line where `<code>` is reported; for an expression that spans lines, the line where it starts. Runners may check it; the code set is what must match. |
| `// expect-exit: <n>` | The exit code of `proviso run`; 0 if absent, 1 when `main` fails with an error, 70 for a defect. |
| `// flags: --incomplete` | Check and run with `--incomplete`, so `todo` holes are accepted (Q25). |
| `// expect-report: <kind> <detail>` | The run must report this event; see the runtime reports in DIAGNOSTICS.md. |
| `// run: record-replay` | Run with `proviso run --record`, whose stdout must match the `.out`. Then `proviso replay` the log, which must report no divergence. Simulated replay suppresses external effects, stdout included (§9.8), so a clean replay is what shows that every observed result was reproduced. |
| `// expect-log: <operation>` | The recorded log holds a call to this capability operation, with its start and completion order. Write one line per expected call. |
| `// schedules: <n>` | Run under `n` seeded schedules, as `proviso test --schedules` explores them (§11 rule 6). Every run must match. `proviso run` has no such option yet (Q15). |
| `// sig: <symbol>` | Compare `proviso sig <symbol>` with the `.sig` file. |

## Rules

- **Rejected rows.** A file with `expect-error` must fail `proviso check`, and the set of reported error codes must equal the expected set. A diagnostic that depends on a rejected construct is suppressed (§15.1, no cascades), so it doesn't count. Warnings are ignored.
- **Accepted rows.** A file without `expect-error` must pass `proviso check`. If it has `main`, `proviso run` must print the `.out` file and exit with the expected code.
- **Reports.** `expect-report` lists the reports that must appear. Other reports don't fail the test.
- **Alternatives.** Where the language allows several results, the `.out` lists them separated by a line `--- or ---`, and the run must match one of them (f10).
- **Environment.** Each run starts in a new, empty working directory, and `sys.fs` is taken to be rooted there (gap: Q6).
- **`.sig` files** are checked from phase 4, when `sig` exists. Until the canonical format covers what they test (T11), each line of the `.sig` must occur in the output in order, as a substring of a line, with runs of whitespace collapsed. After that they become exact goldens.

## Running

`cargo test` runs every file through the runner in `crates/proviso/src/golden.rs`. `PROVISO_BLESS=1 cargo test` rewrites the `.out` and `.err` files from the actual output. Review the diff before committing it.

The runner currently checks these directives: `phase`, `expect-error`, `expect-exit` and `flags`. It also checks `.out` files, including `--- or ---` alternatives, and `.err` files. The `// <-` markers are not checked yet.

If an active file uses a directive the runner can't check yet, the file fails instead of passing unchecked. Those directives are `expect-report`, `expect-log`, `run`, `schedules`, and `sig` from phase 4. Each of them has to be implemented before its phase is reached.

## Rows

| Row | File | Phase | Required outcome |
|---|---|---|---|
| 1 | `f01_tested_not_assumption` | 5 | E0412 |
| 2 | `f02_field_assignment_keeps_refinement` | 5 | E0412 |
| 3 | `f03_inout_part_reverifies_refinement` | 5 | E0412 |
| 4 | `f04_observes_calls_effects` | 3 | E0601 |
| 5 | `f05_closure_reach_not_admitted` | 3 | E0602 |
| 6 | `f06_pool_used_after_move` | 2 | E0501 |
| 7 | `f07_escaped_handle_is_stale` | 2 | runs; `.out` |
| 8 | `f08_attempt_result_is_resource` | 2 | runs; `.out` |
| 9 | `f09_abandon_defect_spares_the_rest` | 2 | exit 70, defect and leak reported; `.out` |
| 10 | `f10_racing_writes_replay` | 6 | record and replay agree, overlap reported; `.out` |
| 11 | `f11_cap_state_shared_and_assignable` | 3 | runs; `.out` |
| 12 | `f12_impl_requires_as_written` | 4 | E0414 |
| 13 | `f13_reach_through_captured_closure` | 3 | E0602 |
| 14 | `f14_resource_inout_is_partial` | 2 (`.sig`: 4) | runs; `.out` and `.sig` |
| 15 | `f15_lent_resource_not_consumable` | 2 | E0502 |
| 16 | `f16_partial_inout_of_refined_part` | 5 | E0413 |
| 17 | `f17_distinct_value_push_reverifies` | 5 | E0412 |
| 18 | `f18_cap_state_never_half_updated` | 6 | runs; `.out` |

Rows 1–3 and 17 need the verifier. Before phase 5, the v1 profile checks refinements at runtime instead, so `check` accepts these files. Row 16's rule is static, so it may pass before phase 5.
