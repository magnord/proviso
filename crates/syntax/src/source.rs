//! Source files and byte spans within them.

/// A half-open byte range in a source file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, Debug)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(lo: u32, hi: u32) -> Span {
        Span { lo, hi }
    }

    /// The smallest span covering both.
    pub fn to(self, other: Span) -> Span {
        Span { lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }

    /// The last byte of the span, such as a block's closing brace.
    pub fn end(self) -> Span {
        Span { lo: self.hi.saturating_sub(1).max(self.lo), hi: self.hi }
    }
}

pub struct SourceFile {
    pub path: String,
    pub text: String,
    line_starts: Vec<u32>,
}

impl SourceFile {
    pub fn new(path: impl Into<String>, text: impl Into<String>) -> SourceFile {
        let text = text.into();
        assert!(text.len() < u32::MAX as usize, "source files are limited to 4 GiB");
        let mut line_starts = vec![0];
        line_starts.extend(text.bytes().enumerate().filter(|&(_, b)| b == b'\n').map(|(i, _)| i as u32 + 1));
        SourceFile { path: path.into(), text, line_starts }
    }

    /// The 1-based line and column of a byte offset. Columns count Unicode scalar values.
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let offset = offset.min(self.text.len() as u32);
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let start = self.line_starts[line] as usize;
        let col = self.text[start..offset as usize].chars().count();
        (line as u32 + 1, col as u32 + 1)
    }

    pub fn slice(&self, span: Span) -> &str {
        &self.text[span.lo as usize..span.hi as usize]
    }
}
