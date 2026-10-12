//! Named surface syntax, module declarations, and lowering to the core.

mod ast;
mod error;
mod lexer;
mod lower;
mod parser;

pub use ast::{DefinitionDecl, Expr, ImportDecl, ModuleSyntax};
pub use error::{FrontendError, ParseError, ResolveError};
pub use parser::{parse, parse_core, parse_module};

#[cfg(test)]
mod tests;
