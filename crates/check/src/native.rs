//! The standard library, embedded as Proviso source, and the native table, which binds each
//! of its declarations without a body to what the toolchain provides (OPEN_QUESTIONS P5).

use crate::Builtin;
use crate::decls::AdtId;

/// The standard library's modules, by name, in the order they are declared. That order pins
/// each of their types and interfaces at the id its constant in [`crate::decls`] names. The
/// prelude comes first, and a program's own module comes after them all.
pub const STD: [(&str, &str); 5] = [
    ("std.prelude", include_str!("../std/prelude.proviso")),
    ("std.io", include_str!("../std/io.proviso")),
    ("std.num", include_str!("../std/num.proviso")),
    ("std.text", include_str!("../std/text.proviso")),
    ("std.pool", include_str!("../std/pool.proviso")),
];

/// The module whose `pub` items every module sees without a `use` (REFERENCE §3).
pub const PRELUDE: &str = "std.prelude";

/// The standard library's modules that later phases bring, which a `use` may name already.
pub fn later_module(name: &str) -> Option<proviso_syntax::diag::Planned> {
    use proviso_syntax::diag::Planned;
    match name {
        "std.fs" | "std.test" => Some(Planned::Phase(3)),
        "std.task" => Some(Planned::Phase(6)),
        _ => None,
    }
}

/// What a declaration without a body is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Native {
    /// A record declared without braces, whose values the toolchain builds.
    Type(AdtId),
    /// A method or associated function the toolchain runs.
    Op(Builtin),
}

/// Each declaration without a body: its module, the type it is or whose `impl` block it is
/// in, and the operation's name, or `""` for the type itself.
const TABLE: &[(&str, &str, &str, Native)] = &[
    ("std.pool", "Pool", "", Native::Type(AdtId::POOL)),
    ("std.pool", "Handle", "", Native::Type(AdtId::HANDLE)),
    ("std.pool", "Pool", "new", Native::Op(Builtin::PoolNew)),
    ("std.pool", "Pool", "len", Native::Op(Builtin::Len)),
    ("std.pool", "Pool", "insert", Native::Op(Builtin::Insert)),
    ("std.pool", "Pool", "remove", Native::Op(Builtin::Remove)),
    ("std.pool", "Pool", "update", Native::Op(Builtin::Update)),
    ("std.pool", "Pool", "get", Native::Op(Builtin::Get)),
    ("std.pool", "Pool", "duplicate", Native::Op(Builtin::Duplicate)),
    ("std.prelude", "Text", "byte_len", Native::Op(Builtin::ByteLen)),
    ("std.prelude", "Text", "is_empty", Native::Op(Builtin::IsEmpty)),
    ("std.prelude", "Text", "trim", Native::Op(Builtin::Trim)),
    ("std.prelude", "Text", "split_once", Native::Op(Builtin::SplitOnce)),
    ("std.prelude", "Text", "lines", Native::Op(Builtin::Lines)),
    ("std.prelude", "Text", "starts_with", Native::Op(Builtin::StartsWith)),
    ("std.prelude", "Text", "strip_prefix", Native::Op(Builtin::StripPrefix)),
    ("std.prelude", "Float", "to_int", Native::Op(Builtin::ToInt)),
    ("std.prelude", "Float32", "to_int", Native::Op(Builtin::ToInt)),
    ("std.prelude", "List", "len", Native::Op(Builtin::Len)),
    ("std.prelude", "List", "is_empty", Native::Op(Builtin::IsEmpty)),
    ("std.prelude", "List", "push", Native::Op(Builtin::Push)),
    ("std.prelude", "List", "pop", Native::Op(Builtin::Pop)),
    ("std.prelude", "List", "get", Native::Op(Builtin::Get)),
    ("std.prelude", "List", "enumerate", Native::Op(Builtin::Enumerate)),
    ("std.prelude", "List", "contains", Native::Op(Builtin::Contains)),
    ("std.prelude", "Map", "len", Native::Op(Builtin::Len)),
    ("std.prelude", "Map", "is_empty", Native::Op(Builtin::IsEmpty)),
    ("std.prelude", "Map", "contains_key", Native::Op(Builtin::ContainsKey)),
    ("std.prelude", "Map", "set", Native::Op(Builtin::Set)),
    ("std.prelude", "Map", "remove", Native::Op(Builtin::Remove)),
    ("std.prelude", "Map", "get", Native::Op(Builtin::Get)),
];

/// What the declaration `decl` of `module`, or its operation `op`, binds to. A declaration
/// without a body that has no entry is a bug in the toolchain.
pub fn native(module: &str, decl: &str, op: &str) -> Option<Native> {
    TABLE.iter().find(|&&(m, d, o, _)| (m, d, o) == (module, decl, op)).map(|&(.., native)| native)
}
