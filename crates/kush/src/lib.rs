//! Kush frontend and bootstrap logical kernel. Parsing is syntax-only;
//! `check` elaborates only the documented, restricted total logical subset.
pub mod ast;
pub mod bindgen;
pub mod check;
mod coverage;
mod eval;
pub use eval::Host;
pub mod executable;
mod facts;
mod float;
mod grades;
mod int;
pub mod interop;
pub use facts::Certificate;
pub mod kernel;
pub mod language_server;
mod length;
pub mod lexer;
mod lifetimes;
pub mod native;
pub mod natural;
mod ownership;
pub mod parser;
pub mod program;
pub mod project;
pub mod resolve;
#[cfg(test)]
mod row_laws_tests;
mod runtime_types;
pub mod source;
mod suspend;
mod variance;

pub use check::check;
pub use parser::parse;
pub use source::{Diagnostic, Span};
