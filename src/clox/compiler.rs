use std::result::Result as StdResult;

use anyhow::{bail, Result};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::mem;

use crate::clox::value::Value;
use crate::clox::{Chunk, OpCode};
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxError;

pub fn compile(source: &str) -> StdResult<Chunk, LoxError> {
    let mut scanner = Scanner::new(source);
    scanner.scan_tokens()?;

    let mut compiler = Compiler::new(scanner);
    compiler.compile().map_err(|e| LoxError::CompileError(e))?;
    compiler
        .end_compiler()
        .map_err(|e| LoxError::CompileError(e))
}

struct Compiler {
    tokens: Vec<Token>,
    tok_pos: usize,
    previous: Token,
    current: Token,
    had_error: bool,
    panic_mode: bool,

    chunk: Chunk,
}

/*
PREC_NONE,
 PREC_ASSIGNMENT,  // =
 PREC_OR,          // or
 PREC_AND,         // and
 PREC_EQUALITY,    // == !=
 PREC_COMPARISON,  // < > <= >=
 PREC_TERM,        // + -
 PREC_FACTOR,      // * /
 PREC_UNARY,       // ! -
 PREC_CALL,        // . ()
 PREC_PRIMARY
*/
#[derive(Copy, Clone, Debug, PartialOrd, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
enum Precedence {
    None,
    Assignment,
    Or,
    And,
    Equality,
    Comparison,
    Term,
    Factor,
    Unary,
    Call,
    Primary,
}

impl Precedence {
    pub fn next_higher(self) -> Self {
        Precedence::try_from(self as u8 + 1).unwrap_or(self)
    }
}

struct PrattRule {
    prefix: OptParseFn,
    infix: OptParseFn,
    precedence: Precedence,
}

type ParseFn = fn(&mut Compiler);

type OptParseFn = Option<ParseFn>;

impl From<(OptParseFn, OptParseFn, Precedence)> for PrattRule {
    fn from(x: (OptParseFn, OptParseFn, Precedence)) -> Self {
        Self {
            prefix: x.0,
            infix: x.1,
            precedence: x.2,
        }
    }
}

impl Compiler {
    fn new(scanner: Scanner) -> Self {
        let tok0 = scanner.tokens()[0].clone();
        Self {
            tokens: scanner.take_tokens(),
            tok_pos: 0,
            previous: tok0.clone(),
            current: tok0,
            had_error: false,
            panic_mode: false,

            chunk: Chunk::new(),
        }
    }

    pub fn compile(&mut self) -> Result<()> {
        /*for t in &self.tokens {
            println!("{:?}", t.tok_type());
        }*/
        self.advance();
        self.expression();
        self.consume(TokenType::Eof, "Expect end of expression.");
        Ok(())
    }

    pub fn end_compiler(mut self) -> Result<Chunk> {
        self.emit_byte(OpCode::Return);
        if self.had_error {
            self.chunk.disassemble("code"); // FIXME: this should be conditional
            bail!("Compilation failed.")
        }
        Ok(self.chunk)
    }

    fn get_rule(&self, tok: TokenType) -> PrattRule {
        macro_rules! f {
            ($func:ident) => {
                Some(Self::$func as fn(&mut Compiler))
            };
        }
        macro_rules! p {
            () => {
                (None, None, Precedence::None)
            };
            (None, $infix:ident, $prec:expr) => {
                (None, f!($infix), $prec)
            };
            ($prefix:ident, None, $prec:expr) => {
                (f!($prefix), None, $prec)
            };
            ($prefix:ident, $infix:ident, $prec:expr) => {
                (f!($prefix), f!($infix), $prec)
            };
        }

        match tok {
            TokenType::LeftParen => p!(grouping, None, Precedence::None),
            TokenType::RightParen => p!(),
            TokenType::LeftBrace => p!(),
            TokenType::RightBrace => p!(),
            TokenType::Comma => p!(),
            TokenType::Dot => p!(),
            TokenType::Minus => p!(unary, binary, Precedence::Term),
            TokenType::Plus => p!(None, binary, Precedence::Term),
            TokenType::Semicolon => p!(),
            TokenType::Slash => p!(None, binary, Precedence::Factor),
            TokenType::Star => p!(None, binary, Precedence::Factor),
            TokenType::Bang => p!(unary, None, Precedence::None),
            TokenType::BangEqual => p!(None, binary, Precedence::Equality),
            TokenType::Equal => p!(),
            TokenType::EqualEqual => p!(None, binary, Precedence::Equality),
            TokenType::Greater => p!(None, binary, Precedence::Comparison),
            TokenType::GreaterEqual => p!(None, binary, Precedence::Comparison),
            TokenType::Less => p!(None, binary, Precedence::Comparison),
            TokenType::LessEqual => p!(None, binary, Precedence::Comparison),
            TokenType::Identifier => p!(),
            TokenType::String => p!(string, None, Precedence::None),
            TokenType::Number => p!(number, None, Precedence::None),
            TokenType::And => p!(),
            TokenType::Class => p!(),
            TokenType::Else => p!(),
            TokenType::False => p!(literal, None, Precedence::None),
            TokenType::Fun => p!(),
            TokenType::For => p!(),
            TokenType::Nil => p!(literal, None, Precedence::None),
            TokenType::If => p!(),
            TokenType::Or => p!(),
            TokenType::Print => p!(),
            TokenType::Return => p!(),
            TokenType::Super => p!(),
            TokenType::This => p!(),
            TokenType::True => p!(literal, None, Precedence::None),
            TokenType::Var => p!(),
            TokenType::While => p!(),
            TokenType::Eof => p!(),
        }
        .into()
    }

    fn binary(&mut self) {
        let typ = self.previous.tok_type();
        let rule = self.get_rule(typ);
        self.parse_precedence(rule.precedence.next_higher());
        macro_rules! b {
            ($b1:ident) => {
                self.emit_byte(OpCode::$b1)
            };
            ($b1:ident, $b2:ident) => {
                self.emit_bytes(OpCode::$b1, OpCode::$b2)
            };
        }

        match typ {
            TokenType::BangEqual => b!(Equal, Not),
            TokenType::EqualEqual => b!(Equal),
            TokenType::Greater => b!(Greater),
            TokenType::GreaterEqual => b!(Less, Not),
            TokenType::Less => b!(Less),
            TokenType::LessEqual => b!(Greater, Not),

            TokenType::Plus => b!(Add),
            TokenType::Minus => b!(Subtract),
            TokenType::Star => b!(Multiply),
            TokenType::Slash => b!(Divide),
            _ => unreachable!("Unexpected binary op token."),
        };
    }

    fn literal(&mut self) {
        self.emit_byte(match self.previous.tok_type() {
            TokenType::False => OpCode::False,
            TokenType::Nil => OpCode::Nil,
            TokenType::True => OpCode::True,
            _ => unreachable!("Strange literal."),
        });
    }

    fn grouping(&mut self) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    fn number(&mut self) {
        let n = self.previous.number_literal();
        self.emit_constant(n.into());
    }

    fn string(&mut self) {
        self.emit_string_constant(self.previous.string_literal().to_string());
    }

    fn unary(&mut self) {
        let typ = self.previous.tok_type();
        self.parse_precedence(Precedence::Unary);
        match typ {
            TokenType::Bang => self.emit_byte(OpCode::Not),
            TokenType::Minus => self.emit_byte(OpCode::Negate),
            _ => unimplemented!(),
        }
    }

    fn parse_precedence(&mut self, precedence: Precedence) {
        self.advance();
        let prefix_rule = match self.get_rule(self.previous.tok_type()).prefix {
            Some(p) => p,
            None => {
                self.error_current("Expect expression.");
                return;
            }
        };
        prefix_rule(self);
        while precedence <= self.get_rule(self.current.tok_type()).precedence {
            self.advance();
            let infix_rule = self.get_rule(self.previous.tok_type()).infix;
            infix_rule.unwrap()(self);
        }
    }

    fn advance(&mut self) {
        if self.tok_pos >= self.tokens.len() {
            self.tok_pos = self.tokens.len() - 1;
            //            self.error_current("Unexpected end of token stream.");
            //          return;
        }
        self.previous = mem::replace(&mut self.current, self.tokens[self.tok_pos].clone());
        self.tok_pos += 1;
    }

    fn consume(&mut self, typ: TokenType, err_msg: &str) {
        if self.current.tok_type() == typ {
            self.advance()
        } else {
            self.error_current(err_msg)
        }
    }

    fn error_current(&mut self, msg: &str) {
        if self.panic_mode {
            return;
        }
        println!("Error at {:?}: {}", self.current.tok_type(), msg);
        self.had_error = true;
        self.panic_mode = true;
    }

    fn current_chunk(&mut self) -> &mut Chunk {
        &mut self.chunk
    }

    fn emit_byte(&mut self, byte: impl Into<u8>) {
        let line = self.previous.line() as u16;
        self.current_chunk().write_u8(byte, line);
    }

    fn emit_bytes(&mut self, b1: impl Into<u8>, b2: impl Into<u8>) {
        self.emit_byte(b1);
        self.emit_byte(b2);
    }

    fn emit_constant(&mut self, c: Value) {
        let idx = self.make_constant(c);
        self.emit_bytes(OpCode::Constant, idx);
    }

    fn emit_string_constant(&mut self, c: String) {
        let s = self.chunk.const_heap.new_string(c);
        let idx = self.make_constant(s);
        self.emit_bytes(OpCode::Constant, idx);
    }

    fn make_constant(&mut self, c: Value) -> u8 {
        let i = self.chunk.add_constant(c);
        if i > u8::MAX as usize {
            self.error_current("Too many constants in one chunk.");
            0
        } else {
            i as u8
        }
    }
}
