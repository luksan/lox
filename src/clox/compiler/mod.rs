use std::fmt::Display;
use std::iter::Peekable;
use std::mem;
use std::ptr::NonNull;

use anyhow::Result;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use tracing::trace_span;

pub use error::{CompileError, CompilerError};
use func_scope::{FunctionScope, FunctionType};

use crate::clox::mm::{HasRoots, Heap, Obj, ObjTypes};
use crate::clox::value::{Function, ValueEnum as Value};
use crate::clox::{get_settings, Chunk, OpCode};
use crate::scanner::{Scanner, TokSpan, Token, TokenIter, TokenType};

mod error;
mod func_scope;

pub fn compile(source: &str, heap: &Heap) -> Result<NonNull<Obj<Function>>, Vec<CompilerError>> {
    let span = trace_span!("compile()");
    let _e = span.enter();
    let mut scanner = Scanner::new(source);
    // The compiler has to be behind a mut ref, so it can't move in memory for the GC root ref
    let compiler = &mut Compiler::new(&mut scanner, heap);
    let _token = compiler.heap.register_gc_root(compiler as *const _);
    compiler
        .compile()
        .map(|func_ptr| NonNull::new(func_ptr as *mut _).unwrap())
}

struct Compiler<'a> {
    tokens: Peekable<&'a mut TokenIter<'a>>,
    prev_tok: Option<Token>,
    errors: Vec<CompilerError>,
    panic_mode: bool,

    func_scope: Box<FunctionScope>,
    current_class: ClassCompiler,

    heap: &'a Heap,
    precedence_spans: Vec<TokSpan>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum ClassCompiler {
    None,
    Class,
    HasSuper,
}

impl ClassCompiler {
    fn new_class(&mut self) -> Self {
        mem::replace(self, Self::Class)
    }
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

impl<'pratt> Compiler<'pratt> {
    fn new(tokens: &'pratt mut TokenIter<'pratt>, heap: &'pratt Heap) -> Self {
        Self {
            tokens: tokens.peekable(),
            prev_tok: None,
            errors: Vec::new(),
            panic_mode: false,

            func_scope: FunctionScope::new(FunctionType::Script),
            current_class: ClassCompiler::None,

            heap,
            precedence_spans: Vec::new(),
        }
    }

    fn compile(&mut self) -> Result<*const Obj<Function>, Vec<CompilerError>> {
        while !self.match_token(TokenType::Eof) {
            self.declaration()
        }

        self.emit_return();

        if get_settings().disassemble_compiler_output {
            self.func_scope.function().disassemble();
        }

        if !self.errors.is_empty() {
            return Err(mem::take(&mut self.errors));
        }
        Ok(self
            .heap
            .new_object(mem::take(&mut self.func_scope.func_obj)))
    }

    fn begin_scope(&mut self) {
        self.func_scope.begin_scope();
    }

    fn end_scope(&mut self) {
        for is_captured in self.func_scope.end_scope() {
            let op_code = if is_captured {
                OpCode::CloseUpvalue
            } else {
                OpCode::Pop
            };
            self.emit_byte(op_code);
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
        #[rustfmt::skip]
        let (prefix, infix, precedence) = match tok {
            TokenType::LeftParen    => p!(grouping, call, Precedence::Call),
            TokenType::RightParen   => p!(),
            TokenType::LeftBrace    => p!(),
            TokenType::RightBrace   => p!(),
            TokenType::Comma        => p!(),
            TokenType::Dot          => p!(None, dot, Precedence::Call),
            TokenType::Minus        => p!(unary, binary, Precedence::Term),
            TokenType::Plus         => p!(None, binary, Precedence::Term),
            TokenType::Semicolon    => p!(),
            TokenType::Slash        => p!(None, binary, Precedence::Factor),
            TokenType::Star         => p!(None, binary, Precedence::Factor),
            TokenType::Bang         => p!(unary, None, Precedence::None),
            TokenType::BangEqual    => p!(None, binary, Precedence::Equality),
            TokenType::Equal        => p!(),
            TokenType::EqualEqual   => p!(None, binary, Precedence::Equality),
            TokenType::Greater      => p!(None, binary, Precedence::Comparison),
            TokenType::GreaterEqual => p!(None, binary, Precedence::Comparison),
            TokenType::Less         => p!(None, binary, Precedence::Comparison),
            TokenType::LessEqual    => p!(None, binary, Precedence::Comparison),
            TokenType::Identifier   => p!(variable, None, Precedence::None),
            TokenType::String       => p!(string, None, Precedence::None),
            TokenType::Number       => p!(number, None, Precedence::None),
            TokenType::And          => p!(None, and, Precedence::And),
            TokenType::Class        => p!(),
            TokenType::Else         => p!(),
            TokenType::False        => p!(literal, None, Precedence::None),
            TokenType::Fun          => p!(),
            TokenType::For          => p!(),
            TokenType::Nil          => p!(literal, None, Precedence::None),
            TokenType::If           => p!(),
            TokenType::Or           => p!(None, or, Precedence::Or),
            TokenType::Print        => p!(),
            TokenType::Return       => p!(),
            TokenType::Super        => p!(super_, None, Precedence::None),
            TokenType::This         => p!(this, None, Precedence::None),
            TokenType::True         => p!(literal, None, Precedence::None),
            TokenType::Var          => p!(),
            TokenType::While        => p!(),
            TokenType::Eof          => p!(),
        };
        PrattRule {
            prefix,
            infix,
            precedence,
        }
    }

    fn binary(&mut self, _can_assign: bool) {
        let typ = self.previous().tok_type();
        let rule = self.get_rule(typ);
        let runtime_span = self.get_precedence_span();
        self.parse_precedence(rule.precedence.next_higher());
        let runtime_span = runtime_span.extend(self.prev_span());
        macro_rules! b {
            ($b1:ident) => {
                self.emit_opcode_span(OpCode::$b1, &[], runtime_span)
            };
            ($b1:ident, $b2:ident) => {{
                self.emit_opcode_span(OpCode::$b1, &[], runtime_span);
                self.emit_opcode_span(OpCode::$b2, &[], runtime_span);
            }};
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
        let err_span = *self.prev_span();
        let arg_count = self.argument_list();
        let err_span = err_span.extend(self.prev_span());
        self.emit_opcode_span(OpCode::Call, &[arg_count], err_span);
    }

    fn dot(&mut self, can_assign: bool) {
        let instance_span = self.get_precedence_span();
        self.consume(TokenType::Identifier, "Expect property name after '.'.");
        let ident = self.previous();
        let name = self.identifier_constant(ident.lexeme().to_string());
        if can_assign && self.match_token(TokenType::Equal) {
            let span = instance_span.extend(ident.span());
            self.expression();
            self.emit_opcode_span(OpCode::SetProperty, &[name.idx], span);
        } else if self.match_token(TokenType::LeftParen) {
            let arg_cnt = self.argument_list();
            let span = ident.span().extend(self.prev_span());
            self.emit_opcode_span(OpCode::Invoke, &[name.idx, arg_cnt], span);
        } else {
            let span = instance_span.extend(ident.span());
            self.emit_opcode_span(OpCode::GetProperty, &[name.idx], span);
        }
    }

    fn literal(&mut self, _can_assign: bool) {
        self.emit_byte(match self.previous().tok_type() {
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

    fn method(&mut self) {
        self.consume(TokenType::Identifier, "Expect method name.");
        let constant = self.identifier_constant(self.previous().lexeme().to_string());
        let func_type = if self.previous().lexeme() == "init" {
            FunctionType::Initializer
        } else {
            FunctionType::Method
        };
        self.function(func_type);
        self.emit_bytes(OpCode::Method, constant);
    }

    fn class_declaration(&mut self) {
        self.consume(TokenType::Identifier, "Expect class name.");
        let class_name = self.previous();
        let class_name_span = *class_name.span();
        let class_name = class_name.lexeme();
        let name_constant = self.identifier_constant(class_name.to_string());
        self.declare_variable();

        self.emit_bytes(OpCode::Class, name_constant);
        self.define_variable(Some(name_constant));

        let enclosing_class_decl = self.current_class.new_class();

        if self.match_token(TokenType::Less) {
            // Ch 29, superclasses
            self.consume(TokenType::Identifier, "Expect superclass name.");
            self.variable(false);
            if class_name == self.previous().lexeme() {
                self.error("A class can't inherit from itself.");
            }
            self.begin_scope(); // Create a scope for the "super" variable
            self.add_local("super".to_string());
            self.define_variable(None);

            self.named_variable(class_name, class_name_span, false);
            self.emit_byte(OpCode::Inherit);
            self.current_class = ClassCompiler::HasSuper;
        }

        self.named_variable(class_name, class_name_span, false);
        self.consume(TokenType::LeftBrace, "Expect '{' before class body.");
        while !self.check(TokenType::RightBrace) && !self.check(TokenType::Eof) {
            self.method();
        }
        self.consume(TokenType::RightBrace, "Expect '}' after class body.");
        self.emit_byte(OpCode::Pop);

        if self.current_class == ClassCompiler::HasSuper {
            // close the scope created above for storing "super"
            self.end_scope();
        }
        self.current_class = enclosing_class_decl;
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
            self.emit_return();
            return;
        }
        let return_token = self.previous();
        self.expression();
        if self.func_scope.func_type == FunctionType::Initializer {
            let err_span = return_token.span().extend(self.prev_span());
            self.error_at(
                return_token,
                "Can't return a value from an initializer.".to_string(),
                &err_span,
            );
        }
        self.consume(TokenType::Semicolon, "Expect ';' after return value.");
        self.emit_byte(OpCode::Return)
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
        while self.current_tok_type() != TokenType::Eof
            && self.previous().tok_type() != TokenType::Semicolon
        {
            use TokenType::*;
            if matches!(
                self.current().tok_type(),
                Class | Fun | Var | For | If | While | Print | Return
            ) {
                break;
            }
            self.advance();
        }
    }

    fn number(&mut self, _can_assign: bool) {
        let n = self.previous().number_literal();
        self.emit_constant(n.into());
    }

    fn and(&mut self, _can_assign: bool) {
        let end_jump = self.emit_jump(OpCode::JumpIfFalse);
        self.emit_byte(OpCode::Pop);
        self.parse_precedence(Precedence::And);
        self.patch_jump(end_jump);
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
        self.emit_string_constant(self.previous().string_literal().to_string());
    }

    fn variable(&mut self, can_assign: bool) {
        let tok = self.previous();
        let span = *tok.span();
        self.named_variable(tok.lexeme(), span, can_assign)
    }

    fn super_(&mut self, _can_assign: bool) {
        match self.current_class {
            ClassCompiler::None => self.error("Can't use 'super' outside of a class."),
            ClassCompiler::Class => self.error("Can't use 'super' in a class with no superclass."),
            ClassCompiler::HasSuper => {}
        };
        self.consume(TokenType::Dot, "Expect '.' after 'super'.");
        self.consume(TokenType::Identifier, "Expect superclass method name.");
        let ident = self.previous();
        let name = self.identifier_constant(ident.lexeme().to_string());
        let zerospan = TokSpan::default();
        self.named_variable("this", zerospan, false);
        if self.match_token(TokenType::LeftParen) {
            let arg_count = self.argument_list();
            let span = ident.span().extend(self.prev_span());
            self.named_variable("super", zerospan, false);
            self.emit_opcode_span(OpCode::SuperInvoke, &[name.idx, arg_count], span);
        } else {
            self.named_variable("super", zerospan, false);
            self.emit_bytes(OpCode::GetSuper, name);
        }
    }

    fn this(&mut self, _can_assign: bool) {
        if self.current_class == ClassCompiler::None {
            return self.error("Can't use 'this' outside of a class.");
        }
        self.variable(false)
    }

    fn unary(&mut self, _can_assign: bool) {
        let typ = self.previous().tok_type();
        self.parse_precedence(Precedence::Unary);
        match typ {
            TokenType::Bang => self.emit_byte(OpCode::Not),
            TokenType::Minus => self.emit_byte(OpCode::Negate),
            _ => unimplemented!(),
        }
    }

    fn parse_precedence(&mut self, precedence: Precedence) {
        self.advance();
        let Some(prefix_rule) = self.get_rule(self.previous().tok_type()).prefix else {
            return self.error("Expect expression.");
        };
        let can_assign = precedence <= Precedence::Assignment;
        self.precedence_spans.push(*self.prev_span());
        prefix_rule(self, can_assign);
        loop {
            let token_type = self.current_tok_type();
            if precedence > self.get_rule(token_type).precedence {
                break;
            }
            self.advance();
            let infix_rule = self.get_rule(self.previous().tok_type()).infix;
            infix_rule.unwrap()(self, can_assign);
        }
        let err_span = self
            .precedence_spans
            .pop()
            .unwrap()
            .extend(self.prev_span());
        if can_assign && self.match_token(TokenType::Equal) {
            self.error_at(
                self.previous(),
                "Invalid assignment target.".to_string(),
                &err_span,
            );
        }
    }

    fn get_precedence_span(&self) -> TokSpan {
        self.precedence_spans
            .last()
            .map_or_else(|| *self.prev_span(), |s| *s)
    }
}

// helper methods
impl<'helpers> Compiler<'helpers> {
    /// Make a string constant on the heap for this identifier
    fn identifier_constant(&mut self, name: String) -> ChunkConst {
        let v: *const _ = self.heap.new_string(name);
        self.make_constant(v)
    }

    fn add_local(&mut self, name: String) {
        if let Err(e) = self.func_scope.add_local(name) {
            self.error(e);
        }
    }

    /// Declare a local variable, do nothing if current scope is global
    /// Chapter 22.3
    fn declare_variable(&mut self) {
        if self.func_scope.is_global_scope() {
            return;
        }
        let name = self.previous();
        if let Err(e) = self.func_scope.declare_local(&name) {
            self.error(e);
        }
        self.add_local(name.lexeme().to_string());
    }

    /// Parse a global or local variable, return the ChunkConst if the
    /// identifier was stored in the constant table.
    fn parse_variable(&mut self, err: &str) -> Option<ChunkConst> {
        self.consume(TokenType::Identifier, err);
        self.declare_variable();
        if !self.func_scope.is_global_scope() {
            // We don't store the name of local variables.
            // Chapter 22.3
            return None;
        }
        Some(self.identifier_constant(self.previous().lexeme().to_string()))
    }

    fn mark_initialized(&mut self) {
        if self.func_scope.is_global_scope() {
            return;
        }
        self.func_scope.mark_local_initialized();
    }

    fn define_variable(&mut self, global: Option<ChunkConst>) {
        if !self.func_scope.is_global_scope() {
            self.mark_initialized();
            return;
        }
        self.emit_bytes(OpCode::DefineGlobal, global.unwrap())
    }

    fn argument_list(&mut self) -> u8 {
        let mut arg_count = 0;
        if !self.check(TokenType::RightParen) {
            loop {
                self.expression();
                if arg_count == u8::MAX {
                    self.error("Can't have more than 255 arguments.");
                } else {
                    arg_count += 1;
                }
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after arguments.");
        arg_count
    }

    fn named_variable(&mut self, name: &str, runtime_span: TokSpan, can_assign: bool) {
        let mut get_slot_and_ops = || -> Result<_> {
            Ok(if let Some(local) = self.func_scope.resolve_local(name)? {
                (local.into(), OpCode::GetLocal, OpCode::SetLocal)
            } else if let Some(upvalue) = self.func_scope.resolve_upvalue(name)? {
                (upvalue.into(), OpCode::GetUpvalue, OpCode::SetUpvalue)
            } else {
                let global_var_name = self.identifier_constant(name.to_string());
                (global_var_name.into(), OpCode::GetGlobal, OpCode::SetGlobal)
            })
        };

        let (frame_slot, get_op, set_op) = get_slot_and_ops().unwrap_or_else(|e: _| {
            self.error(e);
            (0, OpCode::BadOpCode, OpCode::BadOpCode)
        });
        let opcode = if can_assign && self.match_token(TokenType::Equal) {
            self.expression();
            set_op
        } else {
            get_op
        };
        self.emit_opcode_span(opcode, &[frame_slot], runtime_span);
    }

    fn function(&mut self, func_type: FunctionType) {
        let span = trace_span!("func", n = self.previous().lexeme());
        let _e = span.enter();
        self.func_scope.make_inner_func_scope(func_type);
        self.func_scope.function().name =
            self.heap.new_string(self.previous().lexeme().to_string());
        self.consume(TokenType::LeftParen, "Expect '(' after function name.");
        if !self.check(TokenType::RightParen) {
            loop {
                if self.func_scope.function().arity == 255 {
                    self.error_at_current("Can't have more than 255 parameters.");
                } else {
                    self.func_scope.function().arity += 1;
                }
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
            self.func_scope.function().disassemble();
        }

        // The compiler scope for the current function ends here
        let new = self.func_scope.end_inner_func_scope();
        let func_obj = self.heap.new_object(new.func_obj);
        let val = self.make_constant(func_obj);
        self.emit_bytes(OpCode::Closure, val);
        for uv in new.upvalues {
            self.emit_bytes(uv.is_local(), uv.index());
        }
    }
}

// Token iteration
impl<'tok_iter> Compiler<'tok_iter> {
    fn current(&mut self) -> &Token {
        while let Some(Err(tok)) = self.tokens.next_if(|t| t.is_err()) {
            self.errors.push(CompilerError::Token(tok));
            self.panic_mode = true;
        }
        self.tokens.peek().unwrap().as_ref().unwrap()
    }

    fn current_tok_type(&mut self) -> TokenType {
        self.current().tok_type()
    }

    fn previous(&self) -> Token {
        self.prev_tok.clone().unwrap()
    }

    fn prev_span(&self) -> &TokSpan {
        self.prev_tok.as_ref().unwrap().span()
    }

    fn advance(&mut self) {
        match self.tokens.next() {
            Some(Ok(tok)) => {
                self.prev_tok = Some(tok);
            }
            Some(Err(e)) => {
                self.errors.push(e.into());
                self.panic_mode = true;
            }
            _ => {}
        }
    }

    fn consume(&mut self, typ: TokenType, err_msg: &str) {
        if self.current_tok_type() == typ {
            self.advance()
        } else {
            let span = self.prev_span().point_end();
            let token = self.current().clone();
            self.error_at(token, err_msg, &span)
        }
    }

    /// Consumes the token and returns true if the current token in the stream matches.
    /// Returns false and leaves the token in place otherwise.
    fn match_token(&mut self, token: TokenType) -> bool {
        if !self.check(token) {
            return false;
        }
        self.advance();
        true
    }

    fn check(&mut self, token: TokenType) -> bool {
        self.current_tok_type() == token
    }

    fn error(&mut self, msg: impl Display) {
        let span = *self.prev_span();
        self.error_at(self.previous(), msg, &span);
    }

    fn error_at_current(&mut self, msg: &str) {
        let token = self.current().clone();
        let span = *token.span();
        self.error_at(token, msg, &span);
    }

    fn error_at(&mut self, token: Token, msg: impl Display, span: &TokSpan) {
        if self.panic_mode {
            return;
        }
        self.errors
            .push(CompileError::new(token, msg.to_string(), span).into());
        self.panic_mode = true;
    }
}

#[derive(Clone, Copy)]
struct ChunkConst {
    idx: u8,
}

impl From<ChunkConst> for u8 {
    fn from(value: ChunkConst) -> Self {
        value.idx
    }
}

// Bytecode output routines
impl<'bytecode> Compiler<'bytecode> {
    fn current_chunk(&mut self) -> &mut Chunk {
        &mut self.func_scope.function().chunk
    }

    fn emit_byte(&mut self, byte: impl Into<u8>) {
        let line = self.previous().line() as u16;
        let span = *self.prev_span();
        self.current_chunk().write_u8(byte, line, span);
    }

    fn emit_opcode_span(&mut self, opcode: OpCode, data: &[u8], span: TokSpan) {
        let line = self.previous().line() as u16;
        self.current_chunk().write_u8(opcode as u8, line, span);
        for byte in data {
            self.current_chunk().write_u8(*byte, line, span);
        }
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

    fn make_constant(&mut self, c: impl Into<Value>) -> ChunkConst {
        let i = self.current_chunk().add_constant(c.into());
        let idx = if i > u8::MAX as usize {
            self.error("Too many constants in one chunk.");
            0
        } else {
            i as u8
        };
        ChunkConst { idx }
    }
}

impl HasRoots for Compiler<'_> {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.func_scope.mark_roots(mark_obj);
    }
}
