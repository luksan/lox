use std::result::Result as StdResult;

use std::mem;

use crate::clox::Chunk;
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxError;

pub fn compile(source: &str) -> StdResult<Chunk, LoxError> {
    let mut scanner = Scanner::new(source);
    scanner.scan_tokens()?;

    let mut compiler = Compiler::new(scanner);
    unimplemented!("Not implemented")
}

struct Compiler<'src> {
    tokens: Scanner<'src>,
    tok_pos: usize,
    previous: Token,
    current: Token,
    had_error: bool,
    panic_mode: bool,
}

impl<'src> Compiler<'src> {
    fn new(scanner: Scanner<'src>) -> Self {
        let tok0 = scanner.tokens()[0].clone();
        Self {
            tokens: scanner,
            tok_pos: 0,
            previous: tok0.clone(),
            current: tok0,
            had_error: false,
            panic_mode: false,
        }
    }

    fn advance(&mut self) {
        self.tok_pos += 1;
        self.previous = mem::replace(
            &mut self.current,
            self.tokens.tokens()[self.tok_pos].clone(),
        );
    }

    fn consume(&mut self, typ: TokenType, err_msg: &str) {
        if self.current.tok_type() == &typ {
            self.advance()
        } else {
            self.error_current(err_msg)
        }
    }

    fn error_current(&mut self, msg: &str) {
        if self.panic_mode {
            return;
        }
        self.had_error = true;
        self.panic_mode = true;
    }
    fn error_at(&mut self, tok: &Token, msg: &str) {}
}
