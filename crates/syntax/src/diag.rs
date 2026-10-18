//! Diagnostics and the catalog of stable diagnostic codes (REFERENCE §15.1).
//!
//! Codes are grouped by area: E00xx lexical, E01xx syntax, E02xx names, imports and labels,
//! E03xx types, E04xx refinements and contracts, E05xx ownership and resources, E06xx
//! capabilities, E07xx errors and failure marking, E08xx concurrency, and E09xx
//! implementation limits. A code is never reused for a different meaning.
//!
//! `tests/DIAGNOSTICS.md` documents the same catalog, and `tests/catalog.rs` keeps the two
//! in step.

use crate::source::Span;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Code {
    pub id: &'static str,
    pub kind: &'static str,
    pub summary: &'static str,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub code: Code,
    pub severity: Severity,
    pub span: Span,
    pub message: String,
}

/// When a feature that is recognized but not yet implemented is planned to arrive.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Planned {
    /// A phase of the v1 plan (OPEN_QUESTIONS P3).
    Phase(u8),
    /// Listed as deferred past v1.
    PastV1,
    /// Not yet assigned to a phase.
    Unscheduled,
}

impl Planned {
    fn describe(self) -> String {
        match self {
            Planned::Phase(n) => format!("planned for v1 phase {n}"),
            Planned::PastV1 => "deferred past v1".to_string(),
            Planned::Unscheduled => "not yet scheduled".to_string(),
        }
    }
}

#[derive(Default, Debug)]
pub struct Diagnostics {
    list: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.list.push(Diagnostic { code, severity: Severity::Error, span, message: message.into() });
    }

    /// Reports a construct the language has but this implementation does not support yet.
    /// `what` names it and agrees with "are", as in "`match` expressions".
    pub fn not_implemented(&mut self, span: Span, what: &str, planned: Planned) {
        self.error(codes::NOT_IMPLEMENTED, span, format!("{what} are not implemented yet ({})", planned.describe()));
    }

    pub fn has_errors(&self) -> bool {
        self.list.iter().any(|d| d.severity == Severity::Error)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Diagnostic> {
        self.list.iter()
    }

    pub fn into_vec(self) -> Vec<Diagnostic> {
        self.list
    }
}

macro_rules! codes {
    ($($name:ident = $id:literal, $kind:literal, $summary:literal;)*) => {
        $(pub const $name: Code = Code { id: $id, kind: $kind, summary: $summary };)*

        /// Every code, in numeric order.
        pub const ALL: &[Code] = &[$($name),*];
    };
}

pub mod codes {
    use super::Code;

    codes! {
        INVALID_CHARACTER = "E0001", "invalid_character",
            "A character that cannot appear in Proviso source outside a literal or comment.";
        UNTERMINATED_TEXT = "E0002", "unterminated_text",
            "A text or char literal is missing its closing quote.";
        INVALID_ESCAPE = "E0003", "invalid_escape",
            "An escape other than \\n \\t \\\\ \\\" \\' or \\u{...}.";
        INVALID_NUMBER = "E0004", "invalid_number",
            "A malformed or too-large numeric literal.";
        INVALID_CHAR_LITERAL = "E0005", "invalid_char_literal",
            "A char literal must hold exactly one Unicode scalar value.";
        UNTERMINATED_INTERPOLATION = "E0006", "unterminated_interpolation",
            "An f-string `{` without a matching `}`, or a lone `}` (write `}}`).";
        EMPTY_INTERPOLATION = "E0007", "empty_interpolation",
            "An f-string interpolation `{}` with no expression inside.";

        UNEXPECTED_TOKEN = "E0101", "unexpected_token",
            "The parser expected something else here.";
        BARE_VALUE_STATEMENT = "E0102", "bare_value_statement",
            "An expression statement must be a call, an assignment or a control expression (REFERENCE §2).";
        CHAINED_COMPARISON = "E0103", "chained_comparison",
            "Comparisons are non-associative: `a < b < c` must be written `a < b and b < c` (REFERENCE §6.1).";
        MIXED_AND_OR = "E0104", "mixed_and_or",
            "`and` and `or` cannot be mixed without parentheses (REFERENCE §6.1, H2).";
        MISPLACED_JUMP = "E0105", "misplaced_jump",
            "`break` or `continue` outside a loop, or naming a label no enclosing loop has.";
        INVALID_ASSIGNMENT_TARGET = "E0106", "invalid_assignment_target",
            "Only variables and their fields and elements can be assigned, or changed by a method such as `push` (REFERENCE §5.2).";
        TODO_REQUIRES_INCOMPLETE = "E0107", "todo_requires_incomplete",
            "`todo` holes are accepted only with `--incomplete` (REFERENCE §15.2, Q25).";
        MISPLACED_RETURN = "E0108", "misplaced_return",
            "`return` outside a function body, such as in a `where` clause.";

        UNKNOWN_NAME = "E0201", "unknown_name",
            "A name that does not resolve to any local, function or import, or a variant used without its enum (REFERENCE §4.5).";
        DUPLICATE_ITEM = "E0202", "duplicate_item",
            "A module may hold at most one item per name, and a name may be imported once (REFERENCE §3).";
        SHADOWING = "E0203", "shadowing",
            "A binding may not reuse a name already in scope in the same function, including imported names, an import, record, enum or interface may not reuse a prelude name, and a type parameter may not reuse a type's name (REFERENCE §3, H4).";
        WRONG_CASE = "E0204", "wrong_case",
            "Types and variants are PascalCase; everything else is snake_case (REFERENCE §2).";
        UNKNOWN_IMPORT = "E0205", "unknown_import",
            "A `use` names a module or item that does not exist.";
        MISSING_LABEL = "E0206", "missing_label",
            "Calls to functions with two or more parameters label every argument, and so does every `with` and every part of a pattern for several fields, except a bare field name (REFERENCE §3, §6.4, H3).";
        WRONG_LABEL = "E0207", "wrong_label",
            "An argument label that does not match the parameter in that position, or pattern fields out of declaration order.";
        WRONG_ARGUMENT_COUNT = "E0208", "wrong_argument_count",
            "A call passes more or fewer arguments than the function has parameters, a `with` replaces no field, or a pattern matches the wrong number of fields.";
        NEEDLESS_ALIAS = "E0209", "needless_alias",
            "`as` renames an import only to resolve a name collision (REFERENCE §3, Q24).";
        DUPLICATE_NAME = "E0210", "duplicate_name",
            "A name given twice in one list: a record's or variant's fields, an enum's variants, the fields a `with` replaces or a pattern matches, a `derives` list, a type's methods or a function's type parameters (REFERENCE §3, §4.4, §4.5).";
        PRIVATE_IN_PUBLIC = "E0211", "private_in_public",
            "A `pub` item mentions a less visible type in its signature or, for a `pub` record or enum, its fields, or a less visible interface in its constraints (REFERENCE §3).";
        AMBIGUOUS_METHOD = "E0212", "ambiguous_method",
            "A method call that the methods of two interfaces match, or a type's own method, declared or built in, named like a method of an interface it implements. Call it as `I.f(x)` (REFERENCE §3).";

        TYPE_MISMATCH = "E0301", "type_mismatch",
            "A value of one type where another is expected. Proviso has no implicit conversions (REFERENCE §9.2).";
        LITERAL_OUT_OF_RANGE = "E0302", "literal_out_of_range",
            "A literal that does not fit the type it meets (REFERENCE §2).";
        UNKNOWN_MEMBER = "E0303", "unknown_member",
            "A field, method or variant the type does not have.";
        MISSING_RETURN = "E0304", "missing_return",
            "Every path of a non-Unit function ends with an explicit `return` (REFERENCE §2).";
        IMMUTABLE_ASSIGNMENT = "E0305", "immutable_assignment",
            "Assignment to a `let` binding, a parameter or a loop variable, or a call of a method that changes it, such as `push`.";
        UNSUPPORTED_OPERATOR = "E0306", "unsupported_operator",
            "An operator, interpolation, index, or literal or range pattern that the type does not support.";
        UNKNOWN_TYPE = "E0307", "unknown_type",
            "A type or interface name that does not resolve to one, or a type with the wrong number of type arguments.";
        INVALID_MAIN = "E0308", "invalid_main",
            "A program needs `pub fn main(sys: keep System)`, optionally with `fails E` (REFERENCE §7.4).";
        MISSING_IMPLEMENTATION = "E0309", "missing_implementation",
            "A type does not implement an interface it needs, such as a field's type in a `derives` list, a type argument that a constraint of its parameter names, or a map's key type without `Eq` and `Hash` (REFERENCE §4.2, §4.4, §4.8, §4.9).";
        NOT_DERIVABLE = "E0310", "not_derivable",
            "A `derives` list names a prelude interface that can't be derived, such as `Copy` or `Add` (REFERENCE §4.4).";
        NON_EXHAUSTIVE_MATCH = "E0311", "non_exhaustive_match",
            "A `match` does not cover every value of its type; add the missing arms or `_` (REFERENCE §6.3).";
        CANNOT_INFER = "E0312", "cannot_infer",
            "A value or call whose type arguments neither its expected type nor its fields or arguments give, such as `let x = None` or `var xs = []` (OPEN_QUESTIONS P5).";
        DUPLICATE_IMPLEMENTATION = "E0313", "duplicate_implementation",
            "A type implements an interface twice, by two `impl` blocks or by an `impl` and `derives` (REFERENCE §4.9).";
        IMPL_MISMATCH = "E0314", "impl_mismatch",
            "An `impl I for T` lacks a method of `I` or declares one `I` does not, or a method's receiver, parameters and their modes, return type or `fails` differ from the interface's with `Self` read as `T` (REFERENCE §4.9).";
        ORPHAN_IMPL = "E0315", "orphan_impl",
            "An `impl` lives in neither the module of the interface nor that of the type (REFERENCE §3, §4.9).";
        NOT_IMPLEMENTABLE = "E0316", "not_implementable",
            "An `impl` of an interface that cannot be implemented by hand, such as `Copy` (REFERENCE §5.1).";
        TYPE_ARGUMENT_COUNT = "E0317", "type_argument_count",
            "A call whose `::[…]` gives a function or method more or fewer type arguments than it has type parameters (REFERENCE §4.8).";
        REFUTABLE_PATTERN = "E0318", "refutable_pattern",
            "A `let` or `for` pattern that may not match its value, such as `let Some(x) = o` or one with a literal; use `match`, `is` or an `else` form (REFERENCE §6.4, §6.6).";

        // E0412 to E0414, E0502, E0601 and E0602 are reserved for later phases: the §F
        // goldens already expect them.
        REFINEMENT_REFUTED = "E0412", "refinement_refuted",
            "A refinement obligation is refuted: values consistent with every admissible fact violate it (REFERENCE §8.3, §8.5).";
        PARTIAL_INOUT_OF_REFINED_PART = "E0413", "partial_inout_of_refined_part",
            "A part of a refined value cannot be passed as `inout(partial)` (REFERENCE §5.4).";
        IMPL_REQUIRES_MISMATCH = "E0414", "impl_requires_mismatch",
            "An implementation takes the interface method's `requires` clauses exactly as written (REFERENCE §4.9).";
        CHECK_FALLS_THROUGH = "E0415", "check_falls_through",
            "The `else` of a `check` must not finish, so it has type `Never`, as `fail` and a block that returns, breaks or continues do (REFERENCE §8.4).";
        USE_AFTER_MOVE = "E0501", "use_after_move",
            "A unique or resource value is used after it moved (REFERENCE §5.1).";
        LENT_RESOURCE_CONSUMED = "E0502", "lent_resource_consumed",
            "A borrowed or `inout` resource cannot be passed to `take` or used by a `take self` method (REFERENCE §10).";
        NOT_COPYABLE = "E0503", "not_copyable",
            "A borrowed or `inout` value of a type parameter without `Copy`, or of a type built from one, is copied: bound to a new name, assigned, stored in a value, returned or failed with (REFERENCE §4.8).";
        LENT_VALUE_MOVED = "E0504", "lent_value_moved",
            "A borrowed or `inout` value of a unique type, or a part of one, is moved: bound, assigned, returned, stored, passed to `take`, consumed by `for … in take`, or by a `take self` method or `with` (REFERENCE §5.1, §5.2).";
        OVERLAPPING_ACCESS = "E0505", "overlapping_access",
            "Two accesses to one variable overlap in a call while one of them is `inout`, such as `swap(a: &x, b: &x)`, or a value lent to a call is moved in it (REFERENCE §5.3).";
        INOUT_MARKER_MISMATCH = "E0506", "inout_marker_mismatch",
            "An argument for an `inout` parameter without `&`, or `&` on an argument whose parameter isn't `inout` (REFERENCE §5.2, H5).";
        EFFECTS_CALL_IN_OBSERVES = "E0601", "effects_call_in_observes",
            "An operation that needs only `observes` permissions calls an `effects` operation (REFERENCE §9.2).";
        REACH_NOT_ADMITTED = "E0602", "reach_not_admitted",
            "A value's reach is not admitted by the expected type's `uses` or `with E` (REFERENCE §9.4).";

        UNMARKED_FALLIBLE_CALL = "E0701", "unmarked_fallible_call",
            "A call that can fail must be marked with `try`, `else` or `attempt` (REFERENCE §7.2).";
        TRY_ERROR_MISMATCH = "E0702", "try_error_mismatch",
            "`try` propagates an error unchanged, so the error types must be equal (REFERENCE §7.2).";
        TRY_WITHOUT_FAILURE = "E0703", "try_without_failure",
            "`try` marks no call that can fail.";
        MAIN_ERROR_NOT_SHOW = "E0704", "main_error_not_show",
            "`main`'s error type must implement `Show` (REFERENCE §7.4).";
        FAIL_WITHOUT_FAILS = "E0705", "fail_without_fails",
            "`fail` in a function that declares no `fails`, or in a `where` clause (REFERENCE §7.1).";
        ATTEMPT_WITHOUT_FAILURE = "E0706", "attempt_without_failure",
            "`attempt` marks no call that can fail.";
        NOTHING_TO_UNWRAP = "E0707", "nothing_to_unwrap",
            "An `else` form whose left side is neither an `Option` nor a call that can fail (REFERENCE §6.6).";
        EXAMPLE_CANNOT_FAIL = "E0708", "example_cannot_fail",
            "An `example … fails P` whose call can't fail (REFERENCE §14).";

        NOT_IMPLEMENTED = "E0901", "not_implemented",
            "A construct the language has that this implementation does not support yet.";
        NESTING_TOO_DEEP = "E0902", "nesting_too_deep",
            "Expressions and blocks nest at most 1,000 levels deep in this implementation (OPEN_QUESTIONS P5).";
        MATCH_TOO_COMPLEX = "E0903", "match_too_complex",
            "A `match` whose exhaustiveness takes too many steps to check (OPEN_QUESTIONS P5).";
    }

    pub fn find(id: &str) -> Option<Code> {
        ALL.iter().copied().find(|code| code.id.eq_ignore_ascii_case(id))
    }
}
