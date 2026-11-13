//! Kush frontend and bootstrap logical kernel. Parsing is syntax-only;
//! `check` elaborates only the documented, restricted total logical subset.
pub mod ast;
pub mod bindgen;
pub mod check;
mod coverage;
mod eval;
pub use eval::DEFAULT_EVAL_FUEL;
pub use eval::Host;
pub mod exchange;
pub mod executable;
mod facts;
mod float;
mod gpu;
mod grades;
mod int;
pub mod interop;
pub use facts::Certificate;
pub mod kernel;
#[cfg(test)]
mod lambda_corpus_tests;
pub mod language_server;
mod layout_cert;
mod length;
pub mod lexer;
mod lifetimes;
mod multishot;
pub mod native;
pub mod natural;
mod ownership;
pub mod parser;
pub mod program;
pub mod project;
mod proof_cache;
pub mod resolve;
#[cfg(test)]
mod row_laws_tests;
mod runtime_types;
pub mod source;
mod suspend;
pub mod timing;
mod variance;

pub use check::check;
pub use parser::parse;
pub use source::{Diagnostic, Span};
