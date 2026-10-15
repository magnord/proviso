# Proviso — Diagnostic codes

Stable codes for `proviso check` (REFERENCE §15.1, §15.3). Once assigned, a code never changes meaning, and `proviso explain <code>` serves its normative text. This catalog holds the codes the golden tests need ([golden/README.md](golden/README.md)) and grows as goldens are added.

## Ranges

| Range | Area |
|---|---|
| E00xx | lexical structure (§2) |
| E01xx | syntax (§2, §6) |
| E02xx | names, imports and argument labels (§3) |
| E03xx | types (§4) |
| E04xx | refinements, contracts and verification (§8, and interface contracts in §4.9) |
| E05xx | ownership, kinds, moves and resources (§5, §10) |
| E06xx | capabilities, permissions, reach and retention (§9) |
| E07xx | errors and failure marking (§7) |
| E08xx | concurrency (§11) |
| E09xx | implementation limits ("not implemented yet") |

The phase 1 implementation (branch `claude/repo-next-steps-4c7e5e`) already uses E0001–E0007, E0101–E0107, E0201–E0208, E0301–E0308, E0701–E0704 and E0901; their meanings live with that code until this catalog absorbs them.

## Codes

| Code | Kind | Meaning | Goldens |
|---|---|---|---|
| E0412 | `refinement_refuted` | A refinement obligation is refuted: the verifier found values, consistent with every admissible fact, that violate it (§8.3, §8.5). The diagnostic carries the counterexample. | f01, f02, f03, f17 |
| E0413 | `partial_inout_of_refined_part` | A part of a refined value is passed as `inout(partial)` (§5.4). | f16 |
| E0414 | `impl_requires_mismatch` | An implementation's `requires` clauses differ from the interface method's as written (§4.9). | f12 |
| E0501 | `use_after_move` | A unique or resource value is used after it moved (§5.1). | f06 |
| E0502 | `lent_resource_consumed` | A borrowed or `inout` resource is passed to `take` or used by a `take self` method (§10 rule 6). | f15 |
| E0601 | `effects_call_in_observes` | An operation that needs only `observes` permissions calls an `effects` operation, through its observes-only view of `self` (§9.2). | f04 |
| E0602 | `reach_not_admitted` | A value's reach is not admitted by the expected type: a closure or capability `uses` more than the parameter's `uses` or `with E` allows (§9.4). | f05, f13 |

## Runtime reports (provisional)

Goldens that run assert these with `// expect-report: <kind> <detail>`. The reference doesn't yet say how `proviso run` and `proviso replay` surface them (OPEN_QUESTIONS T9, T10), so they have names but no numeric codes.

| Report | Meaning | Goldens |
|---|---|---|
| `defect <defect kind>` | The run hit a defect of this kind (§7.3). Kinds so far: `assert_failed`, a false `assert`. | f09 |
| `leak <Type>` | A resource of this type was leaked because its `abandon` hit a defect (§10). | f09 |
| `overlap <op> <op>` | Replay found two capability calls that overlapped on aliased resources (§9.8). | f10 |

Exit codes of `proviso run` (§7.3, §7.4): 0 for success, 1 when `main` fails with an error, 70 for a defect.
