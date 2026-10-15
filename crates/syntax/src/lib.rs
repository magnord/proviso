//! Lexing, parsing and diagnostics for Proviso source.

pub mod arena;
pub mod ast;
pub mod diag;
pub mod intern;
pub mod lexer;
pub mod parser;
pub mod source;
pub mod token;

pub use parser::parse_module;
