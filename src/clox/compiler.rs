use std::fmt::Display;
use std::result::Result as StdResult;

use anyhow::{bail, Result};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::mem;

use crate::clox::mm::Heap;
use crate::clox::value::{Function, Object, Value};
use crate::clox::{Chunk, OpCode};
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxError;

pub fn compile<'a>(
    source: &'a str,
    heap: &'a mut Heap,
) -> StdResult<*const Object<Function>, LoxError> {
    let mut scanner = Scanner::new(source);
    scanner.scan_tokens()?;

    let mut compiler = Compiler::new(scanner.tokens(), heap);
    compiler.compile().map_err(|e| LoxError::CompileError(e))?;
    compiler
        .end_compiler()
        .map_err(|e| LoxError::CompileError(e))
}

const U8_MAX_LEN: usize = 256;

struct Compiler<'a> {
    tokens: &'a [Token],
    tok_pos: usize,
    previous: &'a Token,
    current: &'a Token,
    had_error: bool,
    panic_mode: bool,

    func_scope: FunctionScope<'a>,

    heap: &'a mut Heap,
}

// This is struct Compiler in the book, Ch 22.
struct FunctionScope<'compiler> {
    function: Function,
    func_type: FunctionType,
    scope_depth: usize,
    locals: Vec<Local<'compiler>>,
}

impl<'compiler> FunctionScope<'compiler> {
    fn new(func_type: FunctionType) -> Self {
        Self {
            function: Function::new(),
            func_type,
            scope_depth: 0,
            locals: vec![Local { name: "", depth: 0 }],
        }
    }

    fn add_local(&mut self, name: &'compiler Token) -> Result<()> {
        if self.locals.len() >= u8::MAX as usize + 1 {
            bail!("Too many local variables in function.");
        }
        self.locals.push(Local {
            name: name.lexeme(),
            depth: usize::MAX,
        });
        Ok(())
    }

    fn declare_local(&mut self, name: &'compiler Token) -> Result<()> {
        for local in self.locals.iter().rev() {
            if local.depth < self.scope_depth {
                break;
            }
            if local.name == name.lexeme() {
                bail!("Already a variable with this name in this scope.");
            }
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum FunctionType {
    Function,
    Script,
}

struct Local<'a> {
    name: &'a str,
    depth: usize,
}

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

type ParseFn = fn(&mut Compiler<'_>, bool);
type OptParseFn = Option<ParseFn>;

impl<'a> Compiler<'a> {
    fn new(tokens: &'a [Token], heap: &'a mut Heap) -> Self {
        let tok0 = &tokens[0];
        Self {
            tokens,
            tok_pos: 0,
            previous: tok0,
            current: tok0,
            had_error: false,
            panic_mode: false,

            func_scope: FunctionScope::new(FunctionType::Script),
            heap,
        }
    }

    pub fn compile(&mut self) -> Result<()> {
        /*for t in &self.tokens {
            println!("{:?}", t.tok_type());
        }*/
        self.advance();
        while !self.match_token(TokenType::Eof) {
            self.declaration()
        }
        Ok(())
    }

    pub fn end_compiler(mut self) -> Result<*const Object<Function>> {
        self.emit_return();
        if self.had_error {
            //  self.chunk.disassemble("code"); // FIXME: this should be conditional
            bail!("Compilation failed.")
        }
        Ok(self.heap.new_object(self.func_scope.function))
    }

    fn begin_scope(&mut self) {
        self.func_scope.scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.func_scope.scope_depth -= 1;
        while let Some(local) = self.func_scope.locals.last() {
            if local.depth > self.func_scope.scope_depth && local.depth < usize::MAX {
                self.emit_byte(OpCode::Pop);
                self.func_scope.locals.pop();
            } else {
                break;
            }
        }
    }

    fn get_rule(&self, tok: TokenType) -> PrattRule {
        macro_rules! f {
            // https://stackoverflow.com/questions/64102352
            ($func:ident) => {{
                fn f(this: &mut Compiler<'_>, can_assign: bool) {
                    this.$func(can_assign);
                }
                Some(f as ParseFn)
            }};
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

        let (prefix, infix, precedence) = match tok {
            TokenType::LeftParen => p!(grouping, call, Precedence::Call),
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
            TokenType::Identifier => p!(variable, None, Precedence::None),
            TokenType::String => p!(string, None, Precedence::None),
            TokenType::Number => p!(number, None, Precedence::None),
            TokenType::And => p!(None, and, Precedence::And),
            TokenType::Class => p!(),
            TokenType::Else => p!(),
            TokenType::False => p!(literal, None, Precedence::None),
            TokenType::Fun => p!(),
            TokenType::For => p!(),
            TokenType::Nil => p!(literal, None, Precedence::None),
            TokenType::If => p!(),
            TokenType::Or => p!(None, or, Precedence::Or),
            TokenType::Print => p!(),
            TokenType::Return => p!(),
            TokenType::Super => p!(),
            TokenType::This => p!(),
            TokenType::True => p!(literal, None, Precedence::None),
            TokenType::Var => p!(),
            TokenType::While => p!(),
            TokenType::Eof => p!(),
        };
        PrattRule {
            prefix,
            infix,
            precedence,
        }
    }

    fn binary(&mut self, _can_assign: bool) {
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

    fn call(&mut self, _can_assign: bool) {
        let arg_count = self.argument_list();
        self.emit_bytes(OpCode::Call, arg_count);
    }

    fn literal(&mut self, _can_assign: bool) {
        self.emit_byte(match self.previous.tok_type() {
            TokenType::False => OpCode::False,
            TokenType::Nil => OpCode::Nil,
            TokenType::True => OpCode::True,
            _ => unreachable!("Strange literal."),
        });
    }

    fn grouping(&mut self, _can_assign: bool) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn declaration(&mut self) {
        if self.match_token(TokenType::Fun) {
            self.fun_declaration();
        } else if self.match_token(TokenType::Var) {
            self.var_declaration();
        } else {
            self.statement();
        }
        if self.panic_mode {
            self.synchronize();
        }
    }

    fn statement(&mut self) {
        if self.match_token(TokenType::Print) {
            self.print_statement();
        } else if self.match_token(TokenType::For) {
            self.for_statement();
        } else if self.match_token(TokenType::If) {
            self.if_statement();
        } else if self.match_token(TokenType::Return) {
            self.return_statement();
        } else if self.match_token(TokenType::While) {
            self.while_statement();
        } else if self.match_token(TokenType::LeftBrace) {
            self.begin_scope();
            self.block();
            self.end_scope();
        } else {
            self.expression_statement();
        }
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    fn block(&mut self) {
        while !self.check(TokenType::RightBrace) && !self.check(TokenType::Eof) {
            self.declaration();
        }
        self.consume(TokenType::RightBrace, "Expect '}' after block.");
    }

    fn function(&mut self, func_type: FunctionType) {
        let outer_scope = std::mem::replace(&mut self.func_scope, FunctionScope::new(func_type));
        self.func_scope.function.name = self
            .heap
            .new_string(self.previous.lexeme().to_string())
            .as_loxstr()
            .unwrap();
        self.begin_scope();
        self.consume(TokenType::LeftParen, "Expect '(' after function name.");
        if !self.check(TokenType::RightParen) {
            loop {
                if self.func_scope.function.arity == 255 {
                    self.error_at_current("Can't have more than 255 parameters.");
                }
                self.func_scope.function.arity += 1;
                let constant = self.parse_variable("Expect parameter name.");
                self.define_variable(constant);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after parameters.");
        self.consume(TokenType::LeftBrace, "Expect '{' before function body.");
        self.block();
        self.emit_return();
        let new = std::mem::replace(&mut self.func_scope, outer_scope);
        let func: *const _ = self.heap.new_object(new.function);
        let val = self.make_constant(func.into());
        self.emit_bytes(OpCode::Constant, val)
    }

    fn fun_declaration(&mut self) {
        let global = self.parse_variable("Expect function name.");
        self.mark_initialized();
        self.function(FunctionType::Function);
        self.define_variable(global);
    }

    fn var_declaration(&mut self) {
        let global = self.parse_variable("Expect variable name.");
        if self.match_token(TokenType::Equal) {
            self.expression();
        } else {
            self.emit_byte(OpCode::Nil)
        }
        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        );
        self.define_variable(global);
    }

    fn expression_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after expression.");
        self.emit_byte(OpCode::Pop);
    }

    fn for_statement(&mut self) {
        self.begin_scope();
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.");
        if self.match_token(TokenType::Semicolon) {
            // no initializer
        } else if self.match_token(TokenType::Var) {
            self.var_declaration();
        } else {
            self.expression_statement()
        }

        let mut loop_start = self.current_chunk().code.len();
        let mut exit_jump = 0;
        if !self.match_token(TokenType::Semicolon) {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after loop condition.");
            exit_jump = self.emit_jump(OpCode::JumpIfFalse);
            self.emit_byte(OpCode::Pop);
        }

        if !self.match_token(TokenType::RightParen) {
            let body_jump = self.emit_jump(OpCode::Jump);
            let increment_start = self.current_chunk().code.len();
            self.expression();
            self.emit_byte(OpCode::Pop);
            self.consume(TokenType::RightParen, "Expect ')' after for clauses.");
            self.emit_loop(loop_start);
            loop_start = increment_start;
            self.patch_jump(body_jump);
        }
        self.statement();
        self.emit_loop(loop_start);
        if exit_jump > 0 {
            self.patch_jump(exit_jump);
            self.emit_byte(OpCode::Pop);
        }
        self.end_scope();
    }

    fn if_statement(&mut self) {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");
        let then_jump = self.emit_jump(OpCode::JumpIfFalse);
        self.emit_byte(OpCode::Pop);
        self.statement();
        let else_jump = self.emit_jump(OpCode::Jump);
        self.patch_jump(then_jump);
        self.emit_byte(OpCode::Pop);
        if self.match_token(TokenType::Else) {
            self.statement()
        }
        self.patch_jump(else_jump);
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_byte(OpCode::Print);
    }

    fn return_statement(&mut self) {
        if self.func_scope.func_type == FunctionType::Script {
            self.error("Can't return from top-level code.");
        }
        if self.match_token(TokenType::Semicolon) {
            self.emit_return()
        } else {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after return value.");
            self.emit_byte(OpCode::Return)
        }
    }

    fn while_statement(&mut self) {
        let loop_start = self.current_chunk().code.len();
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");
        let exit_jump = self.emit_jump(OpCode::JumpIfFalse);
        self.emit_byte(OpCode::Pop);
        self.statement();
        self.emit_loop(loop_start);
        self.patch_jump(exit_jump);
        self.emit_byte(OpCode::Pop);
    }

    fn synchronize(&mut self) {
        self.panic_mode = false;
        while self.current.tok_type() != TokenType::Eof
            && self.previous.tok_type() != TokenType::Semicolon
        {
            use TokenType::*;
            if matches!(
                self.current.tok_type(),
                Class | Fun | Var | For | If | While | Print | Return
            ) {
                break;
            }
            self.advance();
        }
    }

    fn number(&mut self, _can_assign: bool) {
        let n = self.previous.number_literal();
        self.emit_constant(n.into());
    }

    fn or(&mut self, _can_assign: bool) {
        let else_jump = self.emit_jump(OpCode::JumpIfFalse);
        let end_jump = self.emit_jump(OpCode::Jump);

        self.patch_jump(else_jump);
        self.emit_byte(OpCode::Pop);
        self.parse_precedence(Precedence::Or);
        self.patch_jump(end_jump);
    }

    fn string(&mut self, _can_assign: bool) {
        self.emit_string_constant(self.previous.string_literal().to_string());
    }

    fn named_variable(&mut self, name: &str, can_assign: bool) {
        let arg = self.resolve_local(name);
        let c;
        let (get_op, set_op) = if let Some(local) = arg {
            c = local as u8;
            (OpCode::GetLocal, OpCode::SetLocal)
        } else {
            c = self.identifier_constant(name.to_string());
            (OpCode::GetGlobal, OpCode::SetGlobal)
        };
        if can_assign && self.match_token(TokenType::Equal) {
            self.expression();
            self.emit_bytes(set_op, c);
        } else {
            self.emit_bytes(get_op, c);
        }
    }

    fn variable(&mut self, can_assign: bool) {
        self.named_variable(self.previous.lexeme(), can_assign)
    }

    fn unary(&mut self, _can_assign: bool) {
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
                self.error("Expect expression.");
                return;
            }
        };
        let can_assign = precedence <= Precedence::Assignment;
        prefix_rule(self, can_assign);
        while precedence <= self.get_rule(self.current.tok_type()).precedence {
            self.advance();
            let infix_rule = self.get_rule(self.previous.tok_type()).infix;
            infix_rule.unwrap()(self, can_assign);
        }
        if can_assign && self.match_token(TokenType::Equal) {
            self.error("Invalid assignment target.")
        }
    }

    fn identifier_constant(&mut self, name: String) -> u8 {
        let v = self.heap.new_string(name);
        self.make_constant(v)
    }

    fn resolve_local(&mut self, name: &str) -> Option<usize> {
        for (i, local) in self.func_scope.locals.iter().enumerate().rev() {
            if local.name == name {
                if local.depth == usize::MAX {
                    self.error("Can't read local variable in its own initializer.");
                }
                return Some(i);
            }
        }
        None
    }

    fn add_local(&mut self, name: &'a Token) {
        if let Err(e) = self.func_scope.add_local(name) {
            self.error(e);
        }
    }

    fn declare_variable(&mut self) {
        if self.func_scope.scope_depth == 0 {
            return;
        }
        let name = self.previous;
        if let Err(e) = self.func_scope.declare_local(name) {
            self.error(e);
        }
        self.add_local(name);
    }

    fn parse_variable(&mut self, err: &str) -> u8 {
        self.consume(TokenType::Identifier, err);
        self.declare_variable();
        if self.func_scope.scope_depth > 0 {
            return 0;
        }
        self.identifier_constant(self.previous.lexeme().to_string())
    }

    fn mark_initialized(&mut self) {
        if self.scope_depth() == 0 {
            return;
        }
        let depth = self.scope_depth();
        self.func_scope.locals.last_mut().map(|l| l.depth = depth);
    }

    fn define_variable(&mut self, global: u8) {
        if self.scope_depth() > 0 {
            self.mark_initialized();
            return;
        }
        self.emit_bytes(OpCode::DefineGlobal, global)
    }

    fn argument_list(&mut self) -> u8 {
        let mut arg_count = 0;
        if !self.check(TokenType::RightParen) {
            loop {
                self.expression();
                if arg_count == u8::MAX {
                    self.error("Can't have more than 255 arguments.");
                }
                arg_count += 1;
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after arguments.");
        arg_count
    }

    fn and(&mut self, _can_assign: bool) {
        let end_jump = self.emit_jump(OpCode::JumpIfFalse);
        self.emit_byte(OpCode::Pop);
        self.parse_precedence(Precedence::And);
        self.patch_jump(end_jump);
    }

    fn advance(&mut self) {
        if self.tok_pos >= self.tokens.len() {
            self.tok_pos = self.tokens.len() - 1;
            //            self.error_current("Unexpected end of token stream.");
            //          return;
        }
        self.previous = mem::replace(&mut self.current, &self.tokens[self.tok_pos]);
        self.tok_pos += 1;
    }

    fn consume(&mut self, typ: TokenType, err_msg: &str) {
        if self.current.tok_type() == typ {
            self.advance()
        } else {
            self.error_at_current(err_msg)
        }
    }

    fn match_token(&mut self, token: TokenType) -> bool {
        if !self.check(token) {
            return false;
        }
        self.advance();
        true
    }

    fn check(&self, token: TokenType) -> bool {
        self.current.tok_type() == token
    }

    fn error(&mut self, msg: impl Display) {
        self.error_at(self.previous, msg.to_string().as_str());
    }

    fn error_at_current(&mut self, msg: &str) {
        self.error_at(self.current, msg);
    }

    fn error_at(&mut self, token: &'a Token, msg: &str) {
        if self.panic_mode {
            return;
        }
        eprintln!(
            "[line {}] Error at '{}': {}",
            token.line(),
            token.lexeme(),
            msg
        );
        self.had_error = true;
        self.panic_mode = true;
    }

    fn current_chunk(&mut self) -> &mut Chunk {
        &mut self.func_scope.function.chunk
    }

    fn scope_depth(&self) -> usize {
        self.func_scope.scope_depth
    }

    fn emit_byte(&mut self, byte: impl Into<u8>) {
        let line = self.previous.line() as u16;
        self.current_chunk().write_u8(byte, line);
    }

    fn emit_bytes(&mut self, b1: impl Into<u8>, b2: impl Into<u8>) {
        self.emit_byte(b1);
        self.emit_byte(b2);
    }

    fn emit_loop(&mut self, loop_start: usize) {
        self.emit_byte(OpCode::Loop);
        let offset = self.current_chunk().code.len() - loop_start + 2;
        if offset > u16::MAX as usize {
            self.error("Loop body too large.");
        }
        self.emit_byte(offset.to_le_bytes()[1]);
        self.emit_byte(offset.to_le_bytes()[0]);
    }

    fn emit_jump(&mut self, instruction: OpCode) -> usize {
        self.emit_byte(instruction);
        self.emit_bytes(0xff, 0xff);
        self.current_chunk().code.len() - 2
    }

    fn emit_return(&mut self) {
        self.emit_bytes(OpCode::Nil, OpCode::Return);
    }

    fn emit_constant(&mut self, c: Value) {
        let idx = self.make_constant(c);
        self.emit_bytes(OpCode::Constant, idx);
    }

    fn patch_jump(&mut self, offset: usize) {
        let jump = self.current_chunk().code.len() - offset - 2;
        if jump > u16::MAX as usize {
            self.error("Too much code to jump over.");
        }
        let code = &mut self.current_chunk().code;
        code[offset] = ((jump >> 8) & 0xff) as u8;
        code[offset + 1] = (jump & 0xff) as u8;
    }

    fn emit_string_constant(&mut self, c: String) {
        let s = self.heap.new_string(c);
        let idx = self.make_constant(s);
        self.emit_bytes(OpCode::Constant, idx);
    }

    fn make_constant(&mut self, c: Value) -> u8 {
        let i = self.current_chunk().add_constant(c);
        if i > u8::MAX as usize {
            self.error("Too many constants in one chunk.");
            0
        } else {
            i as u8
        }
    }
}
