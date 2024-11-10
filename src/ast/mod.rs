mod ast;
pub mod parser;
mod resolver;

pub use crate::ast::parser::ParseError;
pub use ast::{expr, stmt, Accepts, LiteralValue, NodeId};
pub use resolver::{Resolver, ResolverError};

pub fn parse(source: &str) -> Result<Vec<stmt::Stmt>, Vec<ParseError>> {
    use crate::ast::parser::Parser;
    use crate::scanner::Scanner;
    let mut scanner = Scanner::new(source.as_ref());
    Parser::parse(&mut scanner)
}
