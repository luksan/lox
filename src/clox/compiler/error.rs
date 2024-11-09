use miette::LabeledSpan;

use std::error::Error;
use std::fmt::{Display, Formatter};
use std::iter;

use crate::ast;
use crate::scanner::{Token, TokenType, TokenizationError};

#[derive(Debug, Clone)]
pub enum CompilerError {
    Token(TokenizationError),
    Compile(CompileError),
}

impl Error for CompilerError {}

impl Display for CompilerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let e = match self {
            CompilerError::Token(e) => e as &dyn Display,
            CompilerError::Compile(e) => e as &dyn Display,
        };
        write!(f, "{e}")
    }
}

impl miette::Diagnostic for CompilerError {
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        match self {
            CompilerError::Token(e) => e.labels(),
            CompilerError::Compile(e) => e.labels(),
        }
    }
}

impl From<ast::ParseError> for CompilerError {
    fn from(value: ast::ParseError) -> Self {
        match value {
            ast::ParseError::Token(tok) => CompilerError::Token(tok),
            ast::ParseError::Parsing { token, msg } => {
                let span = *token.span();
                CompilerError::Compile(CompileError::new(token, msg, span))
            }
            ast::ParseError::UnexpectedEndOfStream => {
                todo!("this error kind should be removed from the parser")
            }
        }
    }
}

impl From<CompileError> for CompilerError {
    fn from(value: CompileError) -> Self {
        Self::Compile(value)
    }
}

impl From<TokenizationError> for CompilerError {
    fn from(value: TokenizationError) -> Self {
        Self::Token(value)
    }
}

#[derive(Debug, Clone)]
pub struct CompileError {
    token: Token,
    msg: String,
    span: miette::SourceSpan,
}

impl CompileError {
    pub fn new(token: Token, msg: String, span: impl Into<miette::SourceSpan>) -> Self {
        Self {
            token,
            msg,
            span: span.into(),
        }
    }
}

impl Error for CompileError {}

impl Display for CompileError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let token = &self.token;
        if token.tok_type() == TokenType::Eof {
            write!(f, "[line {}] Error at end: {}", token.line(), &self.msg)
        } else {
            write!(
                f,
                "[line {}] Error at '{}': {}",
                token.line(),
                token.lexeme(),
                &self.msg
            )
        }
    }
}

impl miette::Diagnostic for CompileError {
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        Some(Box::new(iter::once(LabeledSpan::new_with_span(
            Some(self.msg.clone()),
            self.span,
        ))))
    }
}

#[cfg(test)]
mod test {
    use crate::clox::compiler::compile;
    use crate::clox::Heap;

    #[test]
    fn test_miette_err() {
        let heap = Heap::new();
        let source = "
        var a=1;
        var b=2;
        !a = 3;
        a + b = 3;

        class Foo {
         init() {
           return \"result\";
         }
        }
        fun abc(){
            var x = Foo(x);
        }

        instance.

        fun hejsan() {
          nil
        }
        ";
        let r = compile(source, &heap);
        for _e in r.unwrap_err() {
            // eprintln!("{:?}", miette::Report::new(_e).with_source_code(source))
        }
    }
}
