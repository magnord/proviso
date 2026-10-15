//! Tokens produced by the lexer.

use crate::source::Span;

macro_rules! keywords {
    ($($variant:ident = $text:literal,)*) => {
        /// The reserved words of REFERENCE §2, plus the literals `true` and `false`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum Keyword {
            $($variant,)*
        }

        impl Keyword {
            pub fn from_text(text: &str) -> Option<Keyword> {
                match text {
                    $($text => Some(Keyword::$variant),)*
                    _ => None,
                }
            }

            pub fn text(self) -> &'static str {
                match self {
                    $(Keyword::$variant => $text,)*
                }
            }
        }
    };
}

keywords! {
    All = "all", And = "and", Any = "any", As = "as", Assert = "assert", Attempt = "attempt",
    Break = "break", Cap = "cap", Check = "check", Continue = "continue", Debug = "debug",
    Derives = "derives", Distinct = "distinct", Effect = "effect", Effects = "effects",
    Else = "else", Ensures = "ensures", Enum = "enum", Example = "example", Expect = "expect",
    Extern = "extern", Fail = "fail", Fails = "fails", Fn = "fn", For = "for", If = "if",
    Impl = "impl", In = "in", Inout = "inout", Interface = "interface", Invariant = "invariant",
    Is = "is", It = "it", Keep = "keep", Let = "let", Loop = "loop", Match = "match",
    Needs = "needs", Not = "not", Observes = "observes", Opaque = "opaque", Or = "or",
    Pred = "pred", Property = "property", Pub = "pub", Record = "record",
    Requires = "requires", Resource = "resource", Return = "return", Scope = "scope",
    Scoped = "scoped", SelfValue = "self", SelfType = "Self", State = "state", Tag = "tag",
    Take = "take", Test = "test", Todo = "todo", Trusted = "trusted", Try = "try",
    Type = "type", Unique = "unique", Unit = "unit", Unreachable = "unreachable", Use = "use",
    Uses = "uses", Var = "var", Where = "where", While = "while", With = "with",
    True = "true", False = "false",
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TokenKind {
    Ident,
    Keyword(Keyword),
    Int,
    Float,
    Text,
    FText,
    Char,
    DocComment,
    Newline,
    Eof,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    DotDotEq,
    Arrow,
    FatArrow,
    Eq,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    Amp,
    Pipe,
}

impl TokenKind {
    /// How a diagnostic names the token.
    pub fn describe(self) -> String {
        use TokenKind::*;
        let text = match self {
            Ident => "a name",
            Keyword(kw) => return format!("`{}`", kw.text()),
            Int => "an integer literal",
            Float => "a float literal",
            Text | FText => "a text literal",
            Char => "a char literal",
            DocComment => "a doc comment",
            Newline => "end of line",
            Eof => "end of file",
            LParen => "`(`",
            RParen => "`)`",
            LBracket => "`[`",
            RBracket => "`]`",
            LBrace => "`{`",
            RBrace => "`}`",
            Comma => "`,`",
            Colon => "`:`",
            ColonColon => "`::`",
            Dot => "`.`",
            DotDot => "`..`",
            DotDotEq => "`..=`",
            Arrow => "`->`",
            FatArrow => "`=>`",
            Eq => "`=`",
            EqEq => "`==`",
            NotEq => "`!=`",
            Lt => "`<`",
            Le => "`<=`",
            Gt => "`>`",
            Ge => "`>=`",
            Plus => "`+`",
            Minus => "`-`",
            Star => "`*`",
            Slash => "`/`",
            Percent => "`%`",
            PlusEq => "`+=`",
            MinusEq => "`-=`",
            StarEq => "`*=`",
            SlashEq => "`/=`",
            Amp => "`&`",
            Pipe => "`|`",
        };
        text.to_string()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum TokenValue {
    None,
    Int(u128),
    /// The literal's digits with underscores removed, parsed once its type is known.
    Float(String),
    Text(String),
    Char(char),
    FText(Vec<FPart>),
    Doc(String),
}

/// A piece of an interpolated text literal.
#[derive(Clone, PartialEq, Debug)]
pub enum FPart {
    Lit(String),
    /// The source of an interpolated expression, between its braces.
    Expr(Span),
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub value: TokenValue,
}
