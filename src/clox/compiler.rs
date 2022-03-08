use std::fmt::Display;
use std::result::Result as StdResult;

use anyhow::{bail, Result};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::mem;
use std::ptr::NonNull;
use std::rc::Rc;
use tracing::trace_span;

use crate::clox::mm::{HasRoots, Heap, Obj, ObjTypes};
use crate::clox::value::{Function, Value};
use crate::clox::{get_settings, Chunk, OpCode};
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxError;

pub fn compile(source: &str, heap: &mut Heap) -> StdResult<NonNull<Obj<Function>>, LoxError> {
    let span = trace_span!("compile()");
    let _e = span.enter();
    let mut scanner = Scanner::new(source);
    scanner.scan_tokens()?;
    let mut compiler = Compiler::new(scanner.tokens(), heap);
    let root = Rc::new(&compiler as *const dyn HasRoots);
    compiler.heap.register_roots(&root);
    compiler.compile().map_err(LoxError::CompileError)?;
    compiler
        .end_compiler()
        .map(|func_ptr| NonNull::new(func_ptr as *mut _).unwrap())
        .map_err(LoxError::CompileError)
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
    current_class: Option<NonNull<ClassCompiler>>,

    heap: &'a mut Heap,
}

struct ClassCompiler {
    enclosing: Option<NonNull<Self>>,
    has_superclass: bool,
}

impl ClassCompiler {
    fn new(enclosing: Option<NonNull<Self>>) -> Self {
        Self {
            enclosing,
            has_superclass: false,
        }
    }
}

// This is struct Compiler in the book, Ch 22.
struct FunctionScope<'compiler> {
    function: Function,
    func_type: FunctionType,
    scope_depth: usize,
    locals: Vec<Local<'compiler>>,
    upvalues: Vec<Upvalue>,
    enclosing: Option<Box<FunctionScope<'compiler>>>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct Upvalue {
    index: u8,
    is_local: bool,
}

impl<'compiler> FunctionScope<'compiler> {
    fn new(func_type: FunctionType, outer: Option<Box<Self>>) -> Self {
        let name = if func_type != FunctionType::Function {
            "this"
        } else {
            ""
        };
        Self {
            function: Function::new(),
            func_type,
            scope_depth: 0,
            locals: vec![Local {
                name,
                depth: 0,
                is_captured: false,
            }],
            upvalues: vec![],
            enclosing: outer,
        }
    }

    fn add_local(&mut self, name: &'compiler str) -> Result<()> {
        if self.locals.len() > u8::MAX as usize {
            bail!("Too many local variables in function.");
        }
        self.locals.push(Local {
            name,
            depth: usize::MAX,
            is_captured: false,
        });
        Ok(())
    }

    fn add_upvalue(&mut self, index: u8, is_local: bool) -> Result<u8> {
        let new = Upvalue { index, is_local };
        if let Some(i) = self.upvalues.iter().position(|&uv| uv == new) {
            return Ok(i as u8);
        }
        if self.upvalues.len() >= U8_MAX_LEN {
            bail!("Too many closure variables in function.")
        }
        self.upvalues.push(new);
        self.function.upvalue_count = self.upvalues.len();
        Ok((self.function.upvalue_count - 1) as u8)
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

    fn resolve_local(&self, name: &str) -> Result<Option<usize>> {
        for (i, local) in self.locals.iter().enumerate().rev() {
            if local.name == name {
                if local.depth == usize::MAX {
                    bail!("Can't read local variable in its own initializer.");
                }
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    fn resolve_upvalue(&mut self, name: &str) -> Result<Option<u8>> {
        if let Some(enclosing) = self.enclosing.as_mut() {
            if let Some(local) = enclosing.resolve_local(name).unwrap() {
                enclosing.locals[local].is_captured = true;
                return Ok(Some(self.add_upvalue(local as u8, true)?));
            }
            if let Some(upvalue) = enclosing.resolve_upvalue(name)? {
                return Ok(Some(self.add_upvalue(upvalue, false)?));
            }
        }
        Ok(None)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum FunctionType {
    Function,
    Initializer,
    Method,
    Script,
}

struct Local<'a> {
    name: &'a str,
    depth: usize,
    is_captured: bool,
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

            func_scope: FunctionScope::new(FunctionType::Script, None),
            current_class: None,

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

    pub fn end_compiler(mut self) -> Result<*const Obj<Function>> {
        self.emit_return();

        if get_settings().disassemble_compiler_output {
            self.func_scope.function.disassemble();
        }

        if self.had_error {
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
            if local.depth <= self.scope_depth() {
                break;
            }
            let op_code = if local.is_captured {
                OpCode::CloseUpvalue
            } else {
                OpCode::Pop
            };
            self.emit_byte(op_code);
            self.func_scope.locals.pop();
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
            TokenType::Dot => p!(None, dot, Precedence::Call),
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
            TokenType::Super => p!(super_, None, Precedence::None),
            TokenType::This => p!(this, None, Precedence::None),
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

    fn dot(&mut self, can_assign: bool) {
        self.consume(TokenType::Identifier, "Expect property name after '.'.");
        let name = self.identifier_constant(self.previous.lexeme().to_string());
        if can_assign && self.match_token(TokenType::Equal) {
            self.expression();
            self.emit_bytes(OpCode::SetProperty, name);
        } else if self.match_token(TokenType::LeftParen) {
            let arg_cnt = self.argument_list();
            self.emit_bytes(OpCode::Invoke, name);
            self.emit_byte(arg_cnt);
        } else {
            self.emit_bytes(OpCode::GetProperty, name);
        }
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
        if self.match_token(TokenType::Class) {
            self.class_declaration();
        } else if self.match_token(TokenType::Fun) {
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
        let outer_scope =
            std::mem::replace(&mut self.func_scope, FunctionScope::new(func_type, None));
        self.func_scope.enclosing = Some(Box::new(outer_scope));
        self.func_scope.function.name = self.heap.new_string(self.previous.lexeme().to_string());
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

        if get_settings().disassemble_compiler_output {
            self.func_scope.function.disassemble();
        }

        // The compiler scope for the current function ends here
        let outer_scope = *self.func_scope.enclosing.take().unwrap();
        let new = std::mem::replace(&mut self.func_scope, outer_scope);
        let func = self.heap.new_object(new.function);
        let val = self.make_constant(func as *const _);
        self.emit_bytes(OpCode::Closure, val);
        for uv in new.upvalues {
            self.emit_bytes(uv.is_local, uv.index);
        }
    }

    fn method(&mut self) {
        self.consume(TokenType::Identifier, "Expect method name.");
        let constant = self.identifier_constant(self.previous.lexeme().to_string());
        let func_type = if self.previous.lexeme() == "init" {
            FunctionType::Initializer
        } else {
            FunctionType::Method
        };
        self.function(func_type);
        self.emit_bytes(OpCode::Method, constant);
    }

    fn class_declaration(&mut self) {
        self.consume(TokenType::Identifier, "Expect class name.");
        let class_name = self.previous;
        let name_constant = self.identifier_constant(self.previous.lexeme().to_string());
        self.declare_variable();

        self.emit_bytes(OpCode::Class, name_constant);
        self.define_variable(name_constant);

        let mut current_class = ClassCompiler::new(self.current_class.take());
        self.current_class = Some((&current_class).into());

        if self.match_token(TokenType::Less) {
            // Ch 29, superclasses
            self.consume(TokenType::Identifier, "Expect superclass name.");
            self.variable(false);
            if class_name.lexeme() == self.previous.lexeme() {
                self.error("A class can't inherit from itself.");
            }
            self.begin_scope();
            self.add_local("super");
            self.define_variable(0);

            self.named_variable(class_name.lexeme(), false);
            self.emit_byte(OpCode::Inherit);
            current_class.has_superclass = true;
        }

        self.named_variable(class_name.lexeme(), false);
        self.consume(TokenType::LeftBrace, "Expect '{' before class body.");
        while !self.check(TokenType::RightBrace) && !self.check(TokenType::Eof) {
            self.method();
        }
        self.consume(TokenType::RightBrace, "Expect '}' after class body.");
        self.emit_byte(OpCode::Pop);

        if current_class.has_superclass {
            self.end_scope();
        }
        self.current_class = current_class.enclosing.take();
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
            if self.func_scope.func_type == FunctionType::Initializer {
                self.error("Can't return a value from an initializer.")
            }
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
        let arg = self.func_scope.resolve_local(name).unwrap_or_else(|e| {
            self.error(e);
            None
        });
        let c;
        let (get_op, set_op) = if let Some(local) = arg {
            c = local as u8;
            (OpCode::GetLocal, OpCode::SetLocal)
        } else if let Some(upvalue) = self.func_scope.resolve_upvalue(name).unwrap_or_else(|e| {
            self.error(e);
            None
        }) {
            c = upvalue as u8;
            (OpCode::GetUpvalue, OpCode::SetUpvalue)
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

    fn super_(&mut self, _can_assign: bool) {
        if self.current_class.is_none() {
            self.error("Can't use 'super' outside of a class.");
        } else if unsafe { !self.current_class.unwrap().as_ref().has_superclass } {
            self.error("Can't use 'super' in a class with no superclass.")
        };
        self.consume(TokenType::Dot, "Expect '.' after 'super'.");
        self.consume(TokenType::Identifier, "Expect superclass method name.");
        let name = self.identifier_constant(self.previous.lexeme().to_string());
        self.named_variable("this", false);
        if self.match_token(TokenType::LeftParen) {
            let arg_count = self.argument_list();
            self.named_variable("super", false);
            self.emit_bytes(OpCode::SuperInvoke, name);
            self.emit_byte(arg_count);
        } else {
            self.named_variable("super", false);
            self.emit_bytes(OpCode::GetSuper, name);
        }
    }
    fn this(&mut self, _can_assign: bool) {
        if self.current_class.is_none() {
            self.error("Can't use 'this' outside of a class.");
            return;
        }
        self.variable(false)
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
        let v: *const _ = self.heap.new_string(name);
        self.make_constant(v)
    }

    fn add_local(&mut self, name: &'a str) {
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
        self.add_local(name.lexeme());
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
        if token.tok_type() == TokenType::Eof {
            eprintln!("[line {}] Error at end: {}", token.line(), msg);
        } else {
            eprintln!(
                "[line {}] Error at '{}': {}",
                token.line(),
                token.lexeme(),
                msg
            );
        }
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
        if self.func_scope.func_type == FunctionType::Initializer {
            self.emit_bytes(OpCode::GetLocal, 0);
        } else {
            self.emit_byte(OpCode::Nil);
        }
        self.emit_byte(OpCode::Return);
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
        let s: *const _ = self.heap.new_string(c);
        let idx = self.make_constant(s);
        self.emit_bytes(OpCode::Constant, idx);
    }

    fn make_constant(&mut self, c: impl Into<Value>) -> u8 {
        let i = self.current_chunk().add_constant(c);
        if i > u8::MAX as usize {
            self.error("Too many constants in one chunk.");
            0
        } else {
            i as u8
        }
    }
}

impl HasRoots for Compiler<'_> {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        let mut scope = Some(&self.func_scope);
        while let Some(s) = scope {
            scope = s.enclosing.as_deref();
            s.function.mark_roots(mark_obj);
        }
    }
}
