//! Kush frontend and bootstrap logical kernel. Parsing is syntax-only;
//! `check` elaborates only the documented, restricted total logical subset.
pub mod ast;
pub mod check;
mod coverage;
mod eval;
pub use eval::Host;
pub mod executable;
mod facts;
mod float;
mod grades;
mod int;
pub use facts::Certificate;
pub mod kernel;
mod length;
pub mod lexer;
pub mod native;
pub mod natural;
mod ownership;
pub mod parser;
pub mod program;
pub mod resolve;
mod runtime_types;
pub mod source;

pub use check::check;
pub use parser::parse;
pub use source::{Diagnostic, Span};
