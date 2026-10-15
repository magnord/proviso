//! Turns source text into tokens, then applies the newline rules of REFERENCE §2 (H8).

use crate::diag::{Code, Diagnostics, codes};
use crate::source::Span;
use crate::token::{FPart, Keyword, Token, TokenKind, TokenValue};

/// Lexes `src`, whose first byte is at offset `base` in its file. The result ends with
/// `Eof`, and its `Newline` tokens are only the ones that end statements.
pub fn tokenize(src: &str, base: u32, diags: &mut Diagnostics) -> Vec<Token> {
    let raw = Lexer { src, pos: 0, base, tokens: Vec::new(), diags }.run();
    apply_continuations(raw)
}

struct Lexer<'a> {
    src: &'a str,
    pos: usize,
    base: u32,
    tokens: Vec<Token>,
    diags: &'a mut Diagnostics,
}

impl Lexer<'_> {
    fn run(mut self) -> Vec<Token> {
        while let Some(c) = self.peek() {
            match c {
                ' ' | '\t' | '\r' => self.pos += 1,
                '\n' => {
                    let start = self.pos;
                    self.pos += 1;
                    self.push(TokenKind::Newline, start, TokenValue::None);
                }
                '/' if self.peek_at(1) == Some('/') => self.comment(),
                'f' if self.peek_at(1) == Some('"') => self.interpolated_text(),
                'r' if self.peek_at(1) == Some('"') => self.raw_text(),
                c if c.is_ascii_alphabetic() || c == '_' => self.ident(),
                c if c.is_ascii_digit() => self.number(),
                '"' if self.src[self.pos..].starts_with("\"\"\"") => self.multiline_text(),
                '"' => self.text(),
                '\'' => self.char_literal(),
                c => self.punct(c),
            }
        }
        let end = self.pos;
        self.push(TokenKind::Eof, end, TokenValue::None);
        self.tokens
    }

    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(self.base + start as u32, self.base + self.pos as u32)
    }

    fn push(&mut self, kind: TokenKind, start: usize, value: TokenValue) {
        let span = self.span_from(start);
        self.tokens.push(Token { kind, span, value });
    }

    fn error(&mut self, code: Code, start: usize, message: impl Into<String>) {
        let span = self.span_from(start);
        self.diags.error(code, span, message);
    }

    fn comment(&mut self) {
        let src = self.src;
        let start = self.pos;
        let end = src[start..].find('\n').map_or(src.len(), |i| start + i);
        self.pos = end;
        let text = &src[start..end];
        if text.starts_with("///") && !text.starts_with("////") {
            let body = &text[3..];
            let body = body.strip_prefix(' ').unwrap_or(body);
            self.push(TokenKind::DocComment, start, TokenValue::Doc(body.to_string()));
        }
    }

    fn ident(&mut self) {
        let src = self.src;
        let start = self.pos;
        self.pos += ident_len(&src[start..]);
        let kind = match Keyword::from_text(&src[start..self.pos]) {
            Some(kw) => TokenKind::Keyword(kw),
            None => TokenKind::Ident,
        };
        self.push(kind, start, TokenValue::None);
    }

    fn eat_digits(&mut self, radix: u32) {
        let src = self.src;
        let len = src[self.pos..].find(|c: char| !(c.is_digit(radix) || c == '_')).unwrap_or(src.len() - self.pos);
        self.pos += len;
    }

    fn number(&mut self) {
        let src = self.src;
        let start = self.pos;
        let rest = &src[start..];
        let radix = if rest.starts_with("0x") {
            16
        } else if rest.starts_with("0b") {
            2
        } else {
            10
        };
        let mut is_float = false;
        let value = if radix != 10 {
            self.pos += 2;
            let digits_start = self.pos;
            self.eat_digits(radix);
            let digits: String = src[digits_start..self.pos].chars().filter(|&c| c != '_').collect();
            u128::from_str_radix(&digits, radix).ok().map(TokenValue::Int)
        } else {
            self.eat_digits(10);
            if self.peek() == Some('.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                self.pos += 1;
                self.eat_digits(10);
            }
            if matches!(self.peek(), Some('e' | 'E')) {
                let digit_at = |n| self.peek_at(n).is_some_and(|c: char| c.is_ascii_digit());
                let skip = if digit_at(1) {
                    Some(1)
                } else if matches!(self.peek_at(1), Some('+' | '-')) && digit_at(2) {
                    Some(2)
                } else {
                    None
                };
                if let Some(skip) = skip {
                    is_float = true;
                    self.pos += skip;
                    self.eat_digits(10);
                }
            }
            let text: String = src[start..self.pos].chars().filter(|&c| c != '_').collect();
            if is_float {
                text.parse::<f64>().ok().map(|_| TokenValue::Float(text))
            } else {
                text.parse::<u128>().ok().map(TokenValue::Int)
            }
        };
        // A name glued to a number, as in `12abc` or `1.5f32`, is not a literal.
        let glued = ident_len(&src[self.pos..]);
        let kind = if is_float { TokenKind::Float } else { TokenKind::Int };
        let placeholder = if is_float { TokenValue::Float("0.0".into()) } else { TokenValue::Int(0) };
        if glued > 0 {
            self.pos += glued;
            let text = &src[start..self.pos];
            self.error(codes::INVALID_NUMBER, start, format!("`{text}` is not a valid number"));
            self.push(kind, start, placeholder);
            return;
        }
        match value {
            Some(value) => self.push(kind, start, value),
            None => {
                let text = &src[start..self.pos];
                self.error(codes::INVALID_NUMBER, start, format!("`{text}` is not a valid number, or is too large"));
                self.push(kind, start, placeholder);
            }
        }
    }

    /// Reads the escape at `self.pos` (a backslash) into `out`.
    fn escape(&mut self, out: &mut String) {
        let start = self.pos;
        self.pos += 1;
        let Some(c) = self.peek() else { return };
        self.pos += c.len_utf8();
        match c {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            'u' => match self.unicode_escape() {
                Some(c) => out.push(c),
                None => self.error(
                    codes::INVALID_ESCAPE,
                    start,
                    "a `\\u` escape is `\\u{…}` with 1 to 6 hex digits naming a Unicode scalar value",
                ),
            },
            c => self.error(
                codes::INVALID_ESCAPE,
                start,
                format!("unknown escape `\\{c}`; the escapes are \\n \\t \\\\ \\\" \\' and \\u{{…}}"),
            ),
        }
    }

    fn unicode_escape(&mut self) -> Option<char> {
        let src = self.src;
        if self.peek() != Some('{') {
            return None;
        }
        let close = src[self.pos..].find('}')?;
        let hex = &src[self.pos + 1..self.pos + close];
        if hex.is_empty() || hex.len() > 6 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
            return None;
        }
        self.pos += close + 1;
        char::from_u32(u32::from_str_radix(hex, 16).ok()?)
    }

    fn text(&mut self) {
        let start = self.pos;
        self.pos += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    self.error(codes::UNTERMINATED_TEXT, start, "this text literal is missing its closing `\"`");
                    break;
                }
                Some('"') => {
                    self.pos += 1;
                    break;
                }
                Some('\\') => self.escape(&mut out),
                Some(c) => {
                    out.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
        self.push(TokenKind::Text, start, TokenValue::Text(out));
    }

    fn multiline_text(&mut self) {
        let start = self.pos;
        self.pos += 3;
        let mut out = String::new();
        loop {
            if self.src[self.pos..].starts_with("\"\"\"") {
                self.pos += 3;
                break;
            }
            match self.peek() {
                None => {
                    self.error(codes::UNTERMINATED_TEXT, start, "this text literal is missing its closing `\"\"\"`");
                    break;
                }
                Some('\\') => self.escape(&mut out),
                Some(c) => {
                    out.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
        self.push(TokenKind::Text, start, TokenValue::Text(out));
    }

    fn raw_text(&mut self) {
        let src = self.src;
        let start = self.pos;
        self.pos += 2;
        let body_start = self.pos;
        loop {
            match self.peek() {
                None | Some('\n') => {
                    self.error(codes::UNTERMINATED_TEXT, start, "this raw text literal is missing its closing `\"`");
                    break;
                }
                Some('"') => break,
                Some(c) => self.pos += c.len_utf8(),
            }
        }
        let body = src[body_start..self.pos].to_string();
        if self.peek() == Some('"') {
            self.pos += 1;
        }
        self.push(TokenKind::Text, start, TokenValue::Text(body));
    }

    fn char_literal(&mut self) {
        let start = self.pos;
        self.pos += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    self.error(codes::UNTERMINATED_TEXT, start, "this char literal is missing its closing `'`");
                    self.push(TokenKind::Char, start, TokenValue::Char('\0'));
                    return;
                }
                Some('\'') => {
                    self.pos += 1;
                    break;
                }
                Some('\\') => self.escape(&mut out),
                Some(c) => {
                    out.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
        let mut chars = out.chars();
        let value = match (chars.next(), chars.next()) {
            (Some(c), None) => c,
            _ => {
                self.error(codes::INVALID_CHAR_LITERAL, start, "a char literal holds exactly one Unicode scalar value");
                '\0'
            }
        };
        self.push(TokenKind::Char, start, TokenValue::Char(value));
    }

    fn interpolated_text(&mut self) {
        let src = self.src;
        let start = self.pos;
        self.pos += 2;
        let mut parts = Vec::new();
        let mut lit = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    self.error(codes::UNTERMINATED_TEXT, start, "this text literal is missing its closing `\"`");
                    break;
                }
                Some('"') => {
                    self.pos += 1;
                    break;
                }
                Some('\\') => self.escape(&mut lit),
                Some('{') if self.peek_at(1) == Some('{') => {
                    lit.push('{');
                    self.pos += 2;
                }
                Some('}') if self.peek_at(1) == Some('}') => {
                    lit.push('}');
                    self.pos += 2;
                }
                Some('}') => {
                    let at = self.pos;
                    self.pos += 1;
                    self.error(
                        codes::UNTERMINATED_INTERPOLATION,
                        at,
                        "unmatched `}` in interpolated text; write `}}` for a literal brace",
                    );
                }
                Some('{') => {
                    if !lit.is_empty() {
                        parts.push(FPart::Lit(std::mem::take(&mut lit)));
                    }
                    let open = self.pos;
                    self.pos += 1;
                    match self.interpolation_end() {
                        Some(close) => {
                            if src[open + 1..close].trim().is_empty() {
                                self.pos = close + 1;
                                self.error(
                                    codes::EMPTY_INTERPOLATION,
                                    open,
                                    "this interpolation has no expression inside its braces",
                                );
                            } else {
                                let span = Span::new(self.base + open as u32 + 1, self.base + close as u32);
                                parts.push(FPart::Expr(span));
                                self.pos = close + 1;
                            }
                        }
                        None => {
                            self.pos = open + 1;
                            self.error(
                                codes::UNTERMINATED_INTERPOLATION,
                                open,
                                "this `{` has no matching `}`; write `{{` for a literal brace",
                            );
                            let line_end = src[self.pos..].find(['"', '\n']).map_or(src.len(), |i| self.pos + i);
                            self.pos = line_end;
                            if self.peek() == Some('"') {
                                self.pos += 1;
                            }
                            break;
                        }
                    }
                }
                Some(c) => {
                    lit.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
        if !lit.is_empty() {
            parts.push(FPart::Lit(lit));
        }
        self.push(TokenKind::FText, start, TokenValue::FText(parts));
    }

    /// Finds the `}` that closes the interpolation starting at `self.pos`, skipping nested
    /// brackets and text literals. Interpolations do not span lines.
    fn interpolation_end(&self) -> Option<usize> {
        let mut depth = 0usize;
        let mut in_text = false;
        let mut escaped = false;
        for (i, c) in self.src[self.pos..].char_indices() {
            if c == '\n' {
                return None;
            }
            if in_text {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    in_text = false;
                }
                continue;
            }
            match c {
                '"' => in_text = true,
                '(' | '[' | '{' => depth += 1,
                ')' | ']' => depth = depth.saturating_sub(1),
                '}' if depth == 0 => return Some(self.pos + i),
                '}' => depth -= 1,
                _ => {}
            }
        }
        None
    }

    fn punct(&mut self, c: char) {
        use TokenKind::*;
        let start = self.pos;
        let next = self.peek_at(1);
        let (kind, len) = match (c, next) {
            ('(', _) => (LParen, 1),
            (')', _) => (RParen, 1),
            ('[', _) => (LBracket, 1),
            (']', _) => (RBracket, 1),
            ('{', _) => (LBrace, 1),
            ('}', _) => (RBrace, 1),
            (',', _) => (Comma, 1),
            (':', Some(':')) => (ColonColon, 2),
            (':', _) => (Colon, 1),
            ('.', Some('.')) if self.peek_at(2) == Some('=') => (DotDotEq, 3),
            ('.', Some('.')) => (DotDot, 2),
            ('.', _) => (Dot, 1),
            ('-', Some('>')) => (Arrow, 2),
            ('-', Some('=')) => (MinusEq, 2),
            ('-', _) => (Minus, 1),
            ('=', Some('=')) => (EqEq, 2),
            ('=', Some('>')) => (FatArrow, 2),
            ('=', _) => (Eq, 1),
            ('!', Some('=')) => (NotEq, 2),
            ('<', Some('=')) => (Le, 2),
            ('<', _) => (Lt, 1),
            ('>', Some('=')) => (Ge, 2),
            ('>', _) => (Gt, 1),
            ('+', Some('=')) => (PlusEq, 2),
            ('+', _) => (Plus, 1),
            ('*', Some('=')) => (StarEq, 2),
            ('*', _) => (Star, 1),
            ('/', Some('=')) => (SlashEq, 2),
            ('/', _) => (Slash, 1),
            ('%', _) => (Percent, 1),
            ('&', Some('&')) => {
                self.pos += 2;
                self.error(codes::INVALID_CHARACTER, start, "`&&` is not an operator; write `and` (H2)");
                return;
            }
            ('&', _) => (Amp, 1),
            ('|', _) => (Pipe, 1),
            _ => {
                self.pos += c.len_utf8();
                let hint = match c {
                    '!' => "; write `not` (H2)",
                    ';' => "; a newline ends a statement, so Proviso has no semicolons (H8)",
                    '?' => "; mark a fallible call with `try` (H6)",
                    c if !c.is_ascii() && c.is_alphabetic() => "; names are ASCII",
                    _ => "",
                };
                self.error(codes::INVALID_CHARACTER, start, format!("unexpected character `{c}`{hint}"));
                return;
            }
        };
        self.pos += len;
        self.push(kind, start, TokenValue::None);
    }
}

fn ident_len(s: &str) -> usize {
    s.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(s.len())
}

/// Removes the newlines that do not end a statement (REFERENCE §2). A statement continues
/// onto the next line when the innermost unclosed bracket is `(` or `[`, when the line ends
/// with a binary operator, `=` or `,`, when the next line begins with `.`, `else`, `and`,
/// `or` or a header clause, or when the next line is a lone `{`. Doc comments inside
/// brackets are dropped, and runs of newlines collapse to one.
fn apply_continuations(raw: Vec<Token>) -> Vec<Token> {
    let mut out: Vec<Token> = Vec::with_capacity(raw.len());
    let mut brackets: Vec<TokenKind> = Vec::new();
    let mut i = 0;
    while i < raw.len() {
        let token = &raw[i];
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => brackets.push(token.kind),
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                brackets.pop();
            }
            TokenKind::DocComment if !brackets.is_empty() => {
                i += 1;
                continue;
            }
            TokenKind::Newline => {
                let mut next = i;
                while next < raw.len() && raw[next].kind == TokenKind::Newline {
                    next += 1;
                }
                let inside_parens = matches!(brackets.last(), Some(TokenKind::LParen | TokenKind::LBracket));
                let after_operator = out.last().is_some_and(|t| ends_line_open(t.kind));
                let at_start = out.last().is_none_or(|t| t.kind == TokenKind::Newline);
                if !(inside_parens || after_operator || at_start || continues_line(&raw, next)) {
                    out.push(token.clone());
                }
                i = next;
                continue;
            }
            _ => {}
        }
        out.push(token.clone());
        i += 1;
    }
    out
}

/// Tokens that leave a line open when they end it.
fn ends_line_open(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Plus | Minus
            | Star
            | Slash
            | Percent
            | DotDot
            | DotDotEq
            | EqEq
            | NotEq
            | Lt
            | Le
            | Gt
            | Ge
            | Eq
            | Comma
            | PlusEq
            | MinusEq
            | StarEq
            | SlashEq
            | Keyword(crate::token::Keyword::And | crate::token::Keyword::Or)
            | Keyword(crate::token::Keyword::In | crate::token::Keyword::Is)
    )
}

/// Whether the line starting at `raw[next]` continues the previous one.
fn continues_line(raw: &[Token], next: usize) -> bool {
    use crate::token::Keyword as K;
    let Some(token) = raw.get(next) else { return false };
    match token.kind {
        TokenKind::Dot => true,
        TokenKind::Keyword(
            K::Else
            | K::And
            | K::Or
            | K::Fails
            | K::Needs
            | K::Requires
            | K::Ensures
            | K::Invariant
            | K::Trusted
            | K::Where,
        ) => true,
        TokenKind::LBrace => raw.get(next + 1).is_none_or(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        let mut diags = Diagnostics::default();
        let tokens = tokenize(src, 0, &mut diags);
        assert!(!diags.has_errors(), "unexpected diagnostics: {:?}", diags.into_vec());
        tokens.into_iter().map(|t| t.kind).collect()
    }

    fn values(src: &str) -> Vec<TokenValue> {
        let mut diags = Diagnostics::default();
        tokenize(src, 0, &mut diags).into_iter().map(|t| t.value).collect()
    }

    #[test]
    fn newline_ends_a_statement() {
        assert_eq!(kinds("a\nb"), [Ident, Newline, Ident, Eof]);
    }

    #[test]
    fn blank_lines_collapse() {
        assert_eq!(kinds("\n\na\n\n\nb\n"), [Ident, Newline, Ident, Newline, Eof]);
    }

    #[test]
    fn open_paren_continues() {
        assert_eq!(kinds("f(a,\n  b\n)"), [Ident, LParen, Ident, Comma, Ident, RParen, Eof]);
    }

    #[test]
    fn brace_inside_paren_keeps_newlines() {
        assert_eq!(
            kinds("f({\na\nb\n})"),
            [Ident, LParen, LBrace, Newline, Ident, Newline, Ident, Newline, RBrace, RParen, Eof]
        );
    }

    #[test]
    fn trailing_operator_continues() {
        assert_eq!(kinds("a +\nb"), [Ident, Plus, Ident, Eof]);
        assert_eq!(kinds("let x =\n1"), [Keyword(crate::token::Keyword::Let), Ident, Eq, Int, Eof]);
    }

    #[test]
    fn leading_dot_and_else_continue() {
        assert_eq!(kinds("a\n.b()"), [Ident, Dot, Ident, LParen, RParen, Eof]);
        assert_eq!(kinds("}\nelse {"), [RBrace, Keyword(crate::token::Keyword::Else), LBrace, Eof]);
    }

    #[test]
    fn header_clause_and_lone_brace_continue() {
        use crate::token::Keyword as K;
        assert_eq!(
            kinds("fn f()\n    fails E\n{\n}"),
            [Keyword(K::Fn), Ident, LParen, RParen, Keyword(K::Fails), Ident, LBrace, Newline, RBrace, Eof]
        );
    }

    #[test]
    fn leading_minus_starts_a_statement() {
        assert_eq!(kinds("a\n-1"), [Ident, Newline, Minus, Int, Eof]);
    }

    #[test]
    fn doc_comments_survive_only_at_top_level() {
        assert_eq!(kinds("/// doc\nfn"), [DocComment, Newline, Keyword(crate::token::Keyword::Fn), Eof]);
        assert_eq!(kinds("{\n/// doc\n}"), [LBrace, Newline, RBrace, Eof]);
    }

    #[test]
    fn numbers() {
        assert_eq!(
            values("1_000 0xff 0b1010 1.5 2e-3")[..5],
            [
                TokenValue::Int(1000),
                TokenValue::Int(255),
                TokenValue::Int(10),
                TokenValue::Float("1.5".into()),
                TokenValue::Float("2e-3".into()),
            ]
        );
        assert_eq!(kinds("0..10"), [Int, DotDot, Int, Eof]);
        assert_eq!(kinds("0..=10"), [Int, DotDotEq, Int, Eof]);
    }

    #[test]
    fn text_escapes() {
        assert_eq!(values(r#""a\n\t\\\"\u{1F600}""#)[0], TokenValue::Text("a\n\t\\\"\u{1F600}".into()));
        assert_eq!(values(r#"r"a\n""#)[0], TokenValue::Text("a\\n".into()));
        assert_eq!(values("'x' '\\n'")[..2], [TokenValue::Char('x'), TokenValue::Char('\n')]);
    }

    #[test]
    fn interpolation_parts() {
        let TokenValue::FText(parts) = &values(r#"f"{a} and {{b}} {f(c, "}")}""#)[0] else { panic!() };
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0], FPart::Expr(Span::new(3, 4)));
        assert_eq!(parts[1], FPart::Lit(" and {b} ".into()));
        assert_eq!(parts[2], FPart::Expr(Span::new(17, 26)));
    }

    #[test]
    fn invalid_characters_are_reported() {
        let mut diags = Diagnostics::default();
        tokenize("a ; b", 0, &mut diags);
        let list = diags.into_vec();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].code, codes::INVALID_CHARACTER);
    }
}
