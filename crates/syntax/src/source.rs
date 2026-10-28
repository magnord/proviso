//! Source files, the source map that places them in one range of offsets, and byte spans
//! within them.

/// A half-open byte range in the source map. It lies within one file.
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

    /// Whether `other` lies within this span.
    pub fn contains(self, other: Span) -> bool {
        self.lo <= other.lo && other.hi <= self.hi
    }

    /// The last byte of the span, such as a block's closing brace.
    pub fn end(self) -> Span {
        Span { lo: self.hi.saturating_sub(1).max(self.lo), hi: self.hi }
    }
}

/// One file in a [`SourceMap`]. Its offsets start at `base`, so they don't overlap another
/// file's, and its methods take offsets in the map.
pub struct SourceFile {
    pub path: String,
    pub text: String,
    /// The offset of its first byte in the map.
    pub base: u32,
    line_starts: Vec<u32>,
}

impl SourceFile {
    /// A file on its own, whose offsets start at 0.
    pub fn new(path: impl Into<String>, text: impl Into<String>) -> SourceFile {
        SourceFile::at(path.into(), text.into(), 0)
    }

    fn at(path: String, text: String, base: u32) -> SourceFile {
        let mut line_starts = vec![0];
        line_starts.extend(text.bytes().enumerate().filter(|&(_, b)| b == b'\n').map(|(i, _)| i as u32 + 1));
        SourceFile { path, text, base, line_starts }
    }

    /// The offset just past its last byte, where a span at its end begins.
    pub fn end(&self) -> u32 {
        self.base + self.text.len() as u32
    }

    /// The 1-based line and column of an offset. Columns count Unicode scalar values.
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let offset = offset.saturating_sub(self.base).min(self.text.len() as u32);
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let start = self.line_starts[line] as usize;
        let col = self.text[start..offset as usize].chars().count();
        (line as u32 + 1, col as u32 + 1)
    }

    pub fn slice(&self, span: Span) -> &str {
        &self.text[(span.lo - self.base) as usize..(span.hi - self.base) as usize]
    }
}

/// The files of one program, each at its own range of offsets, so a [`Span`] needs no file
/// id and a lookup finds its file.
#[derive(Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

/// A file's index in its [`SourceMap`].
pub type FileId = usize;

impl SourceMap {
    /// Adds a file after the others. One offset is left between files, so a span at the end
    /// of one isn't the start of the next.
    pub fn add(&mut self, path: impl Into<String>, text: impl Into<String>) -> FileId {
        let text = text.into();
        let base = self.files.last().map_or(0, |last| last.end() as usize + 1);
        assert!(base + text.len() < u32::MAX as usize, "a program's sources are limited to 4 GiB");
        self.files.push(SourceFile::at(path.into(), text, base as u32));
        self.files.len() - 1
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id]
    }

    /// The file an offset lies in.
    pub fn file_at(&self, offset: u32) -> &SourceFile {
        let i = self.files.partition_point(|file| file.base <= offset);
        &self.files[i.saturating_sub(1)]
    }

    /// `path:line:col` of an offset.
    pub fn location(&self, offset: u32) -> String {
        let file = self.file_at(offset);
        let (line, col) = file.line_col(offset);
        format!("{}:{line}:{col}", file.path)
    }

    pub fn slice(&self, span: Span) -> &str {
        self.file_at(span.lo).slice(span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn files_have_disjoint_offsets() {
        let mut map = SourceMap::default();
        let a = map.add("a.proviso", "ab\ncd");
        let b = map.add("b.proviso", "x\ny");
        assert_eq!(map.file(b).base, map.file(a).end() + 1);
        let end_of_a = map.file(a).end();
        assert_eq!(map.file_at(end_of_a).path, "a.proviso");
        assert_eq!(map.location(end_of_a), "a.proviso:2:3");
        let y = map.file(b).base + 2;
        assert_eq!(map.location(y), "b.proviso:2:1");
        assert_eq!(map.slice(Span::new(y, y + 1)), "y");
    }
}
