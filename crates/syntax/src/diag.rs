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
            "Only variables and their parts can be assigned.";
        TODO_REQUIRES_INCOMPLETE = "E0107", "todo_requires_incomplete",
            "`todo` holes are accepted only with `--incomplete` (REFERENCE §15.2, Q25).";

        UNKNOWN_NAME = "E0201", "unknown_name",
            "A name that does not resolve to any local, function or import.";
        DUPLICATE_ITEM = "E0202", "duplicate_item",
            "A module may hold at most one item per name, and a name may be imported once (REFERENCE §3).";
        SHADOWING = "E0203", "shadowing",
            "A binding may not reuse a name already in scope in the same function, including imported names (REFERENCE §3, H4).";
        WRONG_CASE = "E0204", "wrong_case",
            "Types and variants are PascalCase; everything else is snake_case (REFERENCE §2).";
        UNKNOWN_IMPORT = "E0205", "unknown_import",
            "A `use` names a module or item that does not exist.";
        MISSING_LABEL = "E0206", "missing_label",
            "Calls to functions with two or more parameters label every argument (REFERENCE §3, H3).";
        WRONG_LABEL = "E0207", "wrong_label",
            "An argument label that does not match the parameter in that position.";
        WRONG_ARGUMENT_COUNT = "E0208", "wrong_argument_count",
            "A call passes more or fewer arguments than the function has parameters.";

        TYPE_MISMATCH = "E0301", "type_mismatch",
            "A value of one type where another is expected. Proviso has no implicit conversions (REFERENCE §9.2).";
        LITERAL_OUT_OF_RANGE = "E0302", "literal_out_of_range",
            "A literal that does not fit the type it meets (REFERENCE §2).";
        UNKNOWN_MEMBER = "E0303", "unknown_member",
            "A field or method the type does not have.";
        MISSING_RETURN = "E0304", "missing_return",
            "Every path of a non-Unit function ends with an explicit `return` (REFERENCE §2).";
        IMMUTABLE_ASSIGNMENT = "E0305", "immutable_assignment",
            "Assignment to a `let` binding or a parameter; declare it with `var`.";
        UNSUPPORTED_OPERATOR = "E0306", "unsupported_operator",
            "An operator or interpolation the operand's type does not support.";
        UNKNOWN_TYPE = "E0307", "unknown_type",
            "A type name that does not resolve.";
        INVALID_MAIN = "E0308", "invalid_main",
            "A program needs `pub fn main(sys: keep System)`, optionally with `fails E` (REFERENCE §7.4).";

        // Reserved for later phases: the §F goldens already expect these.
        REFINEMENT_REFUTED = "E0412", "refinement_refuted",
            "A refinement obligation is refuted: values consistent with every admissible fact violate it (REFERENCE §8.3, §8.5).";
        PARTIAL_INOUT_OF_REFINED_PART = "E0413", "partial_inout_of_refined_part",
            "A part of a refined value cannot be passed as `inout(partial)` (REFERENCE §5.4).";
        IMPL_REQUIRES_MISMATCH = "E0414", "impl_requires_mismatch",
            "An implementation takes the interface method's `requires` clauses exactly as written (REFERENCE §4.9).";
        USE_AFTER_MOVE = "E0501", "use_after_move",
            "A unique or resource value is used after it moved (REFERENCE §5.1).";
        LENT_RESOURCE_CONSUMED = "E0502", "lent_resource_consumed",
            "A borrowed or `inout` resource cannot be passed to `take` or used by a `take self` method (REFERENCE §10).";
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

        NOT_IMPLEMENTED = "E0901", "not_implemented",
            "A construct the language has that this implementation does not support yet.";
    }

    pub fn find(id: &str) -> Option<Code> {
        ALL.iter().copied().find(|code| code.id.eq_ignore_ascii_case(id))
    }
}
