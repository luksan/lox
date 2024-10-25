mod ast;
pub mod parser;

pub use ast::{LiteralValue, expr, stmt, Accepts, NodeId};
pub use crate::ast::parser::ParseError;

pub fn parse(source: &str) -> Result<Vec<stmt::Stmt>, Vec<ParseError>> {
    use crate::scanner::Scanner;
    use crate::ast::parser::Parser;
    let mut scanner = Scanner::new(source.as_ref());
    Parser::parse(&mut scanner)
}
