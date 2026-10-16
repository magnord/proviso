# Proviso — Diagnostic codes

These are the stable codes reported by `proviso check` (REFERENCE §15.1, §15.3). Once a code is assigned, its meaning never changes. `proviso explain <code>` prints its summary.

The toolchain serves the same catalog from `crates/syntax/src/diag.rs`. A test (`crates/syntax/tests/catalog.rs`) fails if the two disagree on any code or kind. A code is added to both when a golden test first expects it, even if the checker can't report it until a later phase. The golden runner also rejects any `expect-error` code that is not listed here.

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

## Codes

The Phase column gives the P3 phase in which the checker first reports the code. Goldens without a directory prefix live in `tests/golden/`. Those under `basics/` are phase-1 tests.

| Code | Kind | Phase | Meaning | Goldens |
|---|---|---|---|---|
| E0001 | `invalid_character` | 1 | A character that cannot appear in source outside a literal or comment, such as `;`, `!` or `?`. | basics/err_lexical |
| E0002 | `unterminated_text` | 1 | A text or char literal is missing its closing quote. | basics/err_text_literals |
| E0003 | `invalid_escape` | 1 | An escape other than `\n \t \\ \" \'` or `\u{…}`. | basics/err_lexical |
| E0004 | `invalid_number` | 1 | A malformed or too-large numeric literal, or a name glued to a number. | basics/err_lexical |
| E0005 | `invalid_char_literal` | 1 | A char literal that isn't exactly one Unicode scalar value. | basics/err_lexical |
| E0006 | `unterminated_interpolation` | 1 | An f-string `{` without a matching `}`, or a lone `}` (write `}}`). | basics/err_text_literals |
| E0007 | `empty_interpolation` | 1 | An f-string interpolation with no expression in it. | basics/err_text_literals |
| E0101 | `unexpected_token` | 1 | The parser expected something else here. | basics/err_syntax, records/err_unclosed, enums/err_unclosed |
| E0102 | `bare_value_statement` | 1 | An expression statement that is not a call, an assignment or a control expression (§2). | basics/err_bare_value, enums/err_is, option_result/err_fail_attempt |
| E0103 | `chained_comparison` | 1 | `a < b < c`: comparisons are non-associative (§6.1). | basics/err_operator_rules |
| E0104 | `mixed_and_or` | 1 | `and` and `or` mixed without parentheses (§6.1, H2). | basics/err_operator_rules |
| E0105 | `misplaced_jump` | 1 | `break` or `continue` outside a loop, or naming a label that no enclosing loop has. | basics/err_misplaced_jump |
| E0106 | `invalid_assignment_target` | 1 | An assignment to something that isn't a variable or one of its parts. | basics/err_assignment_target, records/err_fields |
| E0107 | `todo_requires_incomplete` | 1 | A `todo` hole without `--incomplete` (§15.2, Q25). | basics/err_todo |
| E0108 | `misplaced_return` | 2 | `return` outside a function body, such as in a `where` clause. | records/err_refinement_scope |
| E0201 | `unknown_name` | 1 | A name that resolves to no local, function or import, or a variant used without its enum (§4.5). | basics/err_unknown_name, enums/err_construction, enums/err_is, enums/err_match, option_result/err_types, option_result/err_fail_attempt |
| E0202 | `duplicate_item` | 1 | Two items with one name in a module, or a name imported twice (§3). | basics/err_duplicate, enums/err_declarations |
| E0203 | `shadowing` | 1 | A binding that reuses a name already in scope in the function, including functions and imports, or an import, record or enum that reuses a prelude name, such as `Text` or `Show` (§3, H4). | basics/err_shadowing, basics/err_import_alias, records/err_declarations, enums/err_declarations, enums/err_match, option_result/err_fail_attempt |
| E0204 | `wrong_case` | 1 | A type or variant that isn't PascalCase, or any other name that isn't snake_case (§2). | basics/err_case, enums/err_declarations |
| E0205 | `unknown_import` | 1 | A `use` that names a module or item that doesn't exist. | basics/err_unknown_import |
| E0206 | `missing_label` | 1 | An unlabelled argument in a call to a function with two or more parameters, or in any `with`, even on a one-field record, or an unlabelled part other than a bare name in a pattern for a variant or record with several fields (§3, §6.4, H3; OPEN_QUESTIONS P5). | basics/err_labels, records/err_fields, enums/err_construction, enums/err_match |
| E0207 | `wrong_label` | 1 | An argument label that doesn't match the parameter in its position, or a pattern that matches fields out of declaration order (OPEN_QUESTIONS P5). | basics/err_labels, enums/err_construction, enums/err_match, option_result/err_types |
| E0208 | `wrong_argument_count` | 1 | More or fewer arguments than the function has parameters, a `with` that replaces no field, or a pattern that matches more fields than there are, or fewer without `..`. A variant with fields is written with parentheses, and one without fields without them (§4.5, §6.4). | basics/err_labels, records/err_fields, enums/err_construction, enums/err_match, option_result/err_types, option_result/err_patterns |
| E0209 | `needless_alias` | 1 | An import renamed with `as` although nothing else has its name; `as` only resolves a collision (§3, Q24). | basics/err_import_alias |
| E0210 | `duplicate_name` | 2 | A name given twice in one list: a record's or variant's fields, an enum's variants, the fields a `with` replaces or a pattern matches, or a `derives` list (§4.4, §4.5). | records/err_declarations, records/err_fields, records/err_derives, enums/err_declarations, enums/err_derives, enums/err_match |
| E0211 | `private_in_public` | 2 | A `pub` or `pub(pkg)` item mentions a less visible type in its signature or, for a record or enum, its fields (§3). `main` is exempt (OPEN_QUESTIONS P5). | records/err_visibility, enums/err_visibility |
| E0301 | `type_mismatch` | 1 | A value of one type where another is expected. There are no implicit conversions (§9.2). | basics/err_type_mismatch, enums/err_construction, enums/err_match, option_result/err_types, option_result/err_patterns, option_result/err_fail_attempt |
| E0302 | `literal_out_of_range` | 1 | A literal that doesn't fit the type it meets (§2). | basics/err_literal_range, option_result/err_types, option_result/err_fail_attempt |
| E0303 | `unknown_member` | 1 | A field, method or variant that the type doesn't have. | basics/err_unknown_member, enums/err_construction, enums/err_match, option_result/err_types, option_result/err_patterns |
| E0304 | `missing_return` | 1 | A path through a non-`Unit` function that doesn't end in `return` (§2). | basics/err_missing_return |
| E0305 | `immutable_assignment` | 1 | An assignment to a `let` binding or a parameter. | basics/err_immutable |
| E0306 | `unsupported_operator` | 1 | An operator or interpolation that the operand's type doesn't support, or a literal or range pattern that the matched type doesn't support, such as a `Float` literal (§12.2). | basics/err_unsupported_operator, enums/err_construction, enums/err_match, option_result/err_types |
| E0307 | `unknown_type` | 1 | A type name that doesn't resolve, or that has the wrong number of type arguments. | basics/err_unknown_type, enums/err_declarations, enums/err_derives, option_result/err_types |
| E0308 | `invalid_main` | 1 | `main` is missing from a file that is run, or isn't declared `pub fn main(sys: keep System)` (§7.4). | basics/err_main_signature |
| E0309 | `missing_implementation` | 2 | A type doesn't implement an interface it needs, such as a field's type in a `derives` list (§4.4, §4.9). | records/err_derives, enums/err_derives, option_result/err_types |
| E0310 | `not_derivable` | 2 | A `derives` list names a prelude interface that can't be derived, such as `Copy` or `Add` (§4.4). | records/err_derives, enums/err_derives |
| E0311 | `non_exhaustive_match` | 2 | A `match` that doesn't cover every value of its type. Guarded arms don't count. Integer patterns are the exception: their exhaustiveness is `[verified]`, so before phase 5 it is checked at run time (§6.3; OPEN_QUESTIONS P5). | enums/err_match, option_result/err_patterns |
| E0312 | `cannot_infer` | 2 | A value whose type arguments neither its expected type nor its fields give, such as `let x = None` or `let r = Ok(1)`. Give the binding a type (OPEN_QUESTIONS P5). | option_result/err_types |
| E0412 | `refinement_refuted` | 5 | A refinement obligation is refuted: the verifier found values, consistent with every admissible fact, that violate it (§8.3, §8.5). The diagnostic carries the counterexample. | f01, f02, f03, f17 |
| E0413 | `partial_inout_of_refined_part` | 5 | A part of a refined value is passed as `inout(partial)` (§5.4). | f16 |
| E0414 | `impl_requires_mismatch` | 4 | An implementation's `requires` clauses differ from the interface method's as written (§4.9). | f12 |
| E0501 | `use_after_move` | 2 | A unique or resource value is used after it moved (§5.1). | f06 |
| E0502 | `lent_resource_consumed` | 2 | A borrowed or `inout` resource is passed to `take`, or used by a `take self` method (§10 rule 6). | f15 |
| E0601 | `effects_call_in_observes` | 3 | An operation that needs only `observes` permissions calls an `effects` operation through its observes-only view of `self` (§9.2). | f04 |
| E0602 | `reach_not_admitted` | 3 | A value's reach isn't admitted by the expected type: a closure or capability `uses` more than the parameter's `uses` or `with E` allows (§9.4). | f05, f13 |
| E0701 | `unmarked_fallible_call` | 1 | A call that can fail but isn't marked with `try`, `else` or `attempt` (§7.2). | basics/err_unmarked_call, option_result/err_fail_attempt |
| E0702 | `try_error_mismatch` | 1 | A `try` whose call fails with a different error type than the function declares, or in a function that declares none (§7.2). | basics/err_try_without_fails, option_result/err_fail_attempt |
| E0703 | `try_without_failure` | 1 | A `try` that marks no call that can fail. | basics/err_try_marks_nothing, option_result/err_fail_attempt |
| E0704 | `main_error_not_show` | 1 | `main`'s error type doesn't implement `Show` (§7.4). | basics/err_main_error_not_show |
| E0705 | `fail_without_fails` | 2 | A `fail` in a function that declares no `fails`, or in a `where` clause, which has no function to fail (§7.1). | option_result/err_fail_attempt |
| E0706 | `attempt_without_failure` | 2 | An `attempt` that marks no call that can fail. | option_result/err_fail_attempt |
| E0901 | `not_implemented` | 1 | A construct the language has but this implementation doesn't support yet. The message says whether it is planned for a v1 phase, deferred past v1, or not yet scheduled. | basics/err_not_implemented, records/err_not_yet, enums/err_not_yet, enums/err_construction, option_result/err_types, option_result/err_not_yet |
| E0902 | `nesting_too_deep` | 1 | Expressions and blocks nested more than 1,000 levels deep, counting each operator of a chain such as `a + b + c` (OPEN_QUESTIONS P5). | basics/err_nesting_too_deep |
| E0903 | `match_too_complex` | 2 | A `match` whose exhaustiveness takes more than 10 million steps to check, as some sets of arms take exponential work (OPEN_QUESTIONS P5). | enums/err_match_too_complex |

## Runtime reports (provisional)

Goldens that run check these reports with `// expect-report: <kind> <detail>`. OPEN_QUESTIONS T10 fixes how `proviso run` prints defects and leaks. Overlaps wait for replay (T9). Reports have names but no numeric codes.

| Report | Meaning | Goldens |
|---|---|---|
| `defect <defect kind>` | The run hit a defect of this kind (§7.3). | f09, records/refinement_construction, records/refinement_trace, enums/no_arm_matched, enums/variant_refinement |
| `leak <Type>` | A resource of this type leaked because its `abandon` hit a defect (§10). | f09 |
| `overlap <op> <op>` | Replay found two capability calls that overlapped on aliased resources (§9.8). | f10 |

The defect kinds so far are:

| Kind | Cause |
|---|---|
| `integer_overflow` | an integer result doesn't fit its type |
| `division_by_zero` | `/` or `%` by zero |
| `assertion_failed` | a false `assert` |
| `todo_reached` | a `todo` hole was reached |
| `unreachable_reached` | an `unreachable` was reached |
| `stack_exhausted` | calls nested more than 10,000 deep |

Phase 2 adds these kinds:

| Kind | Cause |
|---|---|
| `index_out_of_bounds` | `xs[i]` with `i` outside the list ([STD.md](../STD.md)) |
| `stale_handle` | `pool[h]` with a stale or wrong-pool handle (§5.5) |
| `refinement_failed` | a value broke its type's refinement, which the v1 profile checks at runtime (OPEN_QUESTIONS P3) |
| `no_arm_matched` | no arm of a `match` matched; only integer patterns can leave a gap that the checker accepts, since the v1 profile checks their exhaustiveness at runtime (OPEN_QUESTIONS P5) |

Every report is printed on stderr as `<kind>[<detail>]: <message>`, followed by its location and call sites (OPEN_QUESTIONS P5, T10). A leak comes right after the defect in `abandon` that caused it, and its location is the binding that owned the resource. Output of `debug(…)` also goes to stderr, one line per call, as `[debug <path>:<line>:<col>] <values>`.

Exit codes of `proviso run` and `proviso check`:

| Code | Meaning |
|---|---|
| 0 | success |
| 1 | `main` failed with an error (§7.4) |
| 64 | usage error |
| 65 | `check` found errors |
| 66 | unreadable file, or one that isn't UTF-8 |
| 70 | defect (§7.3) |
| 101 | internal error, which is a bug in the toolchain |

Codes 64, 65, 66 and 101 are provisional (P5).
