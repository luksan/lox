use std::error::Error;
use std::fmt::{Display, Formatter};
use std::iter::Peekable;

use crate::jlox::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
};
use crate::scanner::TokenType::*;
use crate::scanner::{Token, TokenIter, TokenType, TokenizationError};
use crate::LoxType;

type Result<T, E = ParseError> = core::result::Result<T, E>;

#[derive(Debug)]
pub enum ParseError {
    Token(TokenizationError),
    Parsing {
        token: Token,
        msg: std::string::String,
    },
    UnexpectedEndOfStream,
}

impl ParseError {
    fn parsing(token: Token, msg: impl ToString) -> Self {
        Self::Parsing {
            token,
            msg: msg.to_string(),
        }
    }
}

impl Error for ParseError {}
impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Token(err) => write!(f, "{err}"),
            ParseError::Parsing { token, msg } => write!(f, "{token:?} {msg}"),
            ParseError::UnexpectedEndOfStream => write!(f, "Unexpected end of file."),
        }
    }
}
impl From<TokenizationError> for ParseError {
    fn from(value: TokenizationError) -> Self {
        Self::Token(value)
    }
}

pub struct Parser<'s> {
    tokens: Peekable<&'s mut TokenIter<'s>>,
    errors: Vec<ParseError>,
}

pub type ParseResult = Result<Expr>;

impl<'s> Parser<'s> {
    pub fn parse(scanner: &'s mut TokenIter<'s>) -> Result<Vec<Stmt>, Vec<ParseError>> {
        Self {
            tokens: scanner.peekable(),
            errors: Vec::new(),
        }
        .parse_self()
    }

    fn parse_self(&mut self) -> Result<Vec<Stmt>, Vec<ParseError>> {
        let mut statements = Vec::new();
        while !self.at_end() {
            match self.declaration() {
                Ok(stmt) => statements.push(stmt),
                Err(err) => self.errors.push(err),
            }
        }
        if self.errors.is_empty() {
            Ok(statements)
        } else {
            Err(core::mem::take(&mut self.errors))
        }
    }

    fn error(&mut self, token: Token, msg: &str) {
        self.errors.push(ParseError::parsing(token, msg));
    }

    fn declaration(&mut self) -> Result<Stmt> {
        let stmt = if let Some(tok) = self.match_advance(&[Class, Fun, Var]) {
            match tok.tok_type() {
                Class => self.class_declaration(),
                Fun => self.function("function"),
                Var => self.var_decl(),
                _ => unreachable!(),
            }
        } else {
            self.statement()
        };
        if stmt.is_err() {
            self.synchronize()
        }
        stmt
    }

    fn class_declaration(&mut self) -> Result<Stmt> {
        let name = self.consume(Identifier, "Expect class name.")?;
        let superclass = if let Some(_less) = self.match_advance(&[Less]) {
            // FIXME: make consume generic over type?
            let ident = self.consume(Identifier, "Expect superclass name.")?;
            Some(expr::Variable::new(ident).try_into().unwrap())
        } else {
            None
        };
        self.consume(LeftBrace, "Expect '{' before class body.")?;
        let mut methods: Vec<stmt::Function> = vec![];
        while !self.check(RightBrace) && !self.at_end() {
            let func = stmt::Function::try_from(self.function("method")?);
            let method = func.map_err(|_| ParseError::Parsing {
                token: self.peek().unwrap().clone(),
                msg: "Error: Expected function as method.".to_string(),
            })?;
            methods.push(method);
        }
        self.consume(RightBrace, "Expect '}' after class body.")?;
        Ok(stmt::Class::new(name, superclass, methods))
    }

    fn var_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Identifier, "Expect variable name.")?;
        let init = if self.match_advance(&[Equal]).is_some() {
            self.expression()?
        } else {
            expr::Literal::new(LoxType::Nil)
        };
        self.consume(Semicolon, "Expect ';' after variable declaration.")?;
        Ok(stmt::Var::new(name, init))
    }

    fn while_statement(&mut self) -> Result<Stmt> {
        self.consume(LeftParen, "Expect '(' after 'while'")?;
        let condition = self.expression()?;
        self.consume(RightParen, "Expect ')' after condition.")?;
        let body = self.statement()?;
        Ok(stmt::While::new(condition, body))
    }

    fn statement(&mut self) -> Result<Stmt> {
        if let Some(token) = self.match_advance(&[For, If, LeftBrace, Print, Return, While]) {
            match token.tok_type() {
                For => self.for_statement(),
                If => self.if_statement(),
                Print => self.print_statement(),
                Return => self.return_statement(token),
                While => self.while_statement(),
                LeftBrace => Ok(stmt::Block::new(self.block()?)),
                _ => self.expression_statement(),
            }
        } else {
            self.expression_statement()
        }
    }

    fn for_statement(&mut self) -> Result<Stmt> {
        self.consume(LeftParen, "Expect '(' after 'for'.")?;
        let initializer = if let Some(token) = self.match_advance(&[Semicolon, Var]) {
            match token.tok_type() {
                Semicolon => None,
                Var => Some(self.var_decl()?),
                _ => unreachable!(),
            }
        } else {
            Some(self.expression_statement()?)
        };

        let condition = if !self.check(Semicolon) {
            self.expression()?
        } else {
            expr::Literal::new(LoxType::Bool(true))
        };
        self.consume(Semicolon, "Expect ';' after loop condition.")?;
        let increment = if !self.check(RightParen) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(RightParen, "Expect ')' after for clauses.")?;
        let mut body = self.statement()?;

        if let Some(increment) = increment {
            body = stmt::Block::new(vec![body, stmt::Expression::new(increment)]);
        }
        body = stmt::While::new(condition, body);
        if let Some(init) = initializer {
            body = stmt::Block::new(vec![init, body])
        }

        Ok(body)
    }

    fn if_statement(&mut self) -> Result<Stmt> {
        self.consume(LeftParen, "Expect '(' after if.")?;
        let condition = self.expression()?;
        self.consume(RightParen, "Expect ')' after if condition")?;
        let then = self.statement()?;
        let els = self
            .match_advance(&[Else])
            .map(|_| self.statement())
            .transpose()?;
        Ok(stmt::If::new(condition, then, els))
    }

    fn print_statement(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        self.consume(Semicolon, "Expect ';' after value.")?;
        Ok(stmt::Print::new(expr))
    }

    fn return_statement(&mut self, return_tok: Token) -> Result<Stmt> {
        let value = if !self.check(Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(Semicolon, "Expect ';' after return value.")?;
        Ok(stmt::Return::new(return_tok, value))
    }

    fn expression_statement(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        self.consume(Semicolon, "Expect ';' after expression.")?;
        Ok(stmt::Expression::new(expr))
    }

    fn function(&mut self, kind: &str) -> Result<Stmt> {
        // TODO: return stmt::Function instead of enum variant
        let name = self.consume(Identifier, format!("Expect {} name.", kind).as_str())?;
        self.consume(LeftParen, "Expect '(' after name.")?;

        let mut parameters = vec![];
        if !self.check(RightParen) {
            loop {
                if parameters.len() >= 255 {
                    let tok = self.peek()?.clone();
                    self.error(tok, "Can't have more than 255 parameters.");
                }
                parameters.push(self.consume(Identifier, "Expect parameter name.")?);
                if self.match_advance(&[Comma]).is_none() {
                    break;
                }
            }
        }
        self.consume(RightParen, "Expect ')' after parameters.")?;
        self.consume(LeftBrace, "Expect '{' before function body.")?;
        let body = self.block()?;
        Ok(stmt::Function::new(name, parameters, body))
    }

    fn block(&mut self) -> Result<ListStmt> {
        let mut statements = ListStmt::new();
        while !self.check(RightBrace) && !self.at_end() {
            statements.push(self.declaration()?);
        }
        self.consume(RightBrace, "Expect '}' after block.")?;
        Ok(statements)
    }

    fn expression(&mut self) -> ParseResult {
        self.assignment()
    }

    fn assignment(&mut self) -> ParseResult {
        let mut expr = self.or()?;

        macro_rules! try_type {
            ($typ:ty, $val:ident, $cls:expr) => {
                #[allow(unused_assignments)]
                match TryInto::<$typ>::try_into(expr) {
                    Ok($val) => return Ok($cls),
                    Err(e) => expr = e,
                }
            };
        }

        if let Some(eq) = self.match_advance(&[Equal]) {
            let value = self.assignment()?;

            try_type!(expr::Variable, var, expr::Assign::new(var.name, value));
            try_type!(expr::Get, get, expr::Set::new(get.object, get.name, value));

            Err(ParseError::parsing(eq, "Invalid assignment target."))
        } else {
            Ok(expr)
        }
    }

    fn or(&mut self) -> ParseResult {
        let mut expr = self.and()?;
        while let Some(or) = self.match_advance(&[Or]) {
            expr = expr::Logical::new(expr, or, self.and()?);
        }
        Ok(expr)
    }

    fn and(&mut self) -> ParseResult {
        let mut expr = self.equality()?;
        while let Some(and) = self.match_advance(&[And]) {
            expr = expr::Logical::new(expr, and, self.equality()?);
        }
        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult {
        let mut expr = self.comparison()?;
        while let Some(operator) = self.match_advance(&[BangEqual, EqualEqual]) {
            expr = expr::Binary::new(expr, operator, self.comparison()?)
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult {
        let mut expr = self.term()?;
        while let Some(operator) = self.match_advance(&[Greater, GreaterEqual, Less, LessEqual]) {
            expr = expr::Binary::new(expr, operator, self.term()?)
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult {
        let mut expr = self.factor()?;
        while let Some(operator) = self.match_advance(&[Minus, Plus]) {
            expr = expr::Binary::new(expr, operator, self.factor()?)
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult {
        let mut expr = self.unary()?;
        while let Some(operator) = self.match_advance(&[Slash, Star]) {
            expr = expr::Binary::new(expr, operator, self.unary()?);
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult {
        if let Some(operator) = self.match_advance(&[Bang, Minus]) {
            Ok(expr::Unary::new(operator, self.unary()?))
        } else {
            self.call()
        }
    }

    fn finish_call(&mut self, callee: Expr) -> ParseResult {
        let mut args = Vec::new();
        if !self.check(RightParen) {
            loop {
                if args.len() >= 255 {
                    let tok = self.peek()?.clone();
                    self.error(tok, "Can't have more than 255 arguments.");
                }
                args.push(self.expression()?);
                if self.match_advance(&[Comma]).is_none() {
                    break;
                }
            }
        }
        let paren = self.consume(RightParen, "Expect ')' after arguments.")?;
        Ok(expr::Call::new(callee, paren, args))
    }

    fn call(&mut self) -> ParseResult {
        let mut expr = self.primary()?;
        while let Some(tok) = self.match_advance(&[Dot, LeftParen]) {
            match tok.tok_type() {
                Dot => {
                    let name = self.consume(Identifier, "Expect property name after '.'.")?;
                    expr = expr::Get::new(expr, name);
                }
                LeftParen => expr = self.finish_call(expr)?,
                _ => unreachable!(),
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> ParseResult {
        let token = self.tokens.next().unwrap()?;
        Ok(expr::Literal::new(match token.tok_type() {
            TokenType::False => LoxType::Bool(false),
            TokenType::True => LoxType::Bool(true),
            TokenType::Nil => LoxType::Nil,
            TokenType::Number => LoxType::Number(token.number_literal()),
            TokenType::String => LoxType::String(token.string_literal().to_owned().into()),
            TokenType::Super => {
                let _dot = self.consume(Dot, "Expect '.' after 'super'.")?;
                let method = self.consume(Identifier, "Expect superclass method name.")?;
                return Ok(expr::Super::new(token, method));
            }
            TokenType::This => return Ok(expr::This::new(token)),
            TokenType::Identifier => return Ok(expr::Variable::new(token)),

            TokenType::LeftParen => {
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, "Expected ')' after expression")?;
                return Ok(expr::Grouping::new(expr));
            }
            _bad => return Err(ParseError::parsing(token, "Expect expression.")),
        }))
    }

    fn at_end(&mut self) -> bool {
        match self.peek_type() {
            Err(_) | Ok(TokenType::Eof) => true,
            _ => false,
        }
    }

    fn advance(&mut self) -> Option<Token> {
        self.consume_token_errors();
        self.tokens.next().map(|t| t.unwrap())
    }

    fn check(&mut self, tok: TokenType) -> bool {
        match self.peek_type() {
            Ok(t) => t == tok,
            _ => false,
        }
    }

    fn consume(&mut self, tok: TokenType, error: &str) -> Result<Token> {
        match self.match_advance(&[tok]) {
            Some(t) => Ok(t),
            None => Err(ParseError::parsing(self.peek()?.clone(), error)),
        }
    }

    fn consume_token_errors(&mut self) {
        while let Some(Err(e)) = self.tokens.next_if(|t| t.is_err()) {
            self.errors.push(ParseError::Token(e));
        }
    }

    /// Look at the next token without advancing the cursor. Advances past error tokens,
    /// but will return an error if the cursor is at the end of the stream.
    fn peek(&mut self) -> Result<&Token> {
        self.consume_token_errors();
        self.tokens
            .peek()
            .map(|r| r.as_ref().unwrap())
            .ok_or(ParseError::UnexpectedEndOfStream)
    }

    fn peek_type(&mut self) -> Result<TokenType> {
        self.peek().map(|t| t.tok_type())
    }

    fn match_advance(&mut self, types: &[TokenType]) -> Option<Token> {
        let next_type = self.peek_type().ok()?;
        types
            .iter()
            .any(|t| t == &next_type)
            .then(|| self.advance().unwrap())
    }

    fn synchronize(&mut self) {
        while !self.at_end() {
            let tok = self.advance().unwrap();

            if tok.tok_type() == Semicolon {
                break;
            }

            match self.peek_type() {
                Ok(
                    TokenType::Class
                    | TokenType::Fun
                    | TokenType::Var
                    | TokenType::For
                    | TokenType::If
                    | TokenType::While
                    | TokenType::Print
                    | TokenType::Return,
                ) => break,

                _ => {}
            }
        }
    }
}
