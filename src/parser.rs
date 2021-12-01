use anyhow::{anyhow, bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
};
use crate::scanner::TokenType::*;
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxType;

use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    had_error: bool,
}

pub type ParseResult = Result<Expr>;

impl Parser {
    pub fn new(scanner: Scanner) -> Self {
        Self {
            tokens: scanner.take_tokens().into_iter().peekable(),
            had_error: false,
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();
        while !self.at_end() {
            match self.declaration() {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.had_error = true;
                    eprintln!("{}", err);
                }
            }
        }
        if !self.had_error {
            Ok(statements)
        } else {
            bail!("Aborting due to parse errors.")
        }
    }

    fn error(&mut self, token: Token, msg: &str) {
        eprintln!("{:?} {}", token, msg);
        self.had_error = true;
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
        let name = self.consume(Identifier("".into()), "Expect class name.")?;
        self.consume(LeftBrace, "Expect '{' before class body.")?;
        let mut methods: Vec<stmt::Function> = vec![];
        while !self.check(&RightBrace) && !self.at_end() {
            methods.push(
                stmt::Function::try_from(self.function("method")?)
                    .map_err(|_| anyhow!("Error: Expected function as method."))?,
            );
        }
        self.consume(RightBrace, "Expect '}' after class body.")?;
        Ok(stmt::Class::new(name, methods))
    }

    fn var_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Identifier("".into()), "Expect variable name.")?;
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

        let condition = if !self.check(&Semicolon) {
            self.expression()?
        } else {
            expr::Literal::new(LoxType::Bool(true))
        };
        self.consume(Semicolon, "Expect ';' after loop condition.")?;
        let increment = if !self.check(&RightParen) {
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
        let value = if !self.check(&Semicolon) {
            self.expression()?
        } else {
            expr::Literal::new(LoxType::Nil)
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
        let ident_match = Identifier("".into());
        let name = self.consume(
            ident_match.clone(),
            format!("Expect {} name.", kind).as_str(),
        )?;
        self.consume(LeftParen, "Expect '(' after name.")?;

        let mut parameters = vec![];
        if !self.check(&RightParen) {
            loop {
                if parameters.len() >= 255 {
                    let tok = self.peek().clone();
                    self.error(tok, "Can't have more than 255 parameters.");
                }
                parameters.push(self.consume(ident_match.clone(), "Expect parameter name.")?);
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
        while !self.check(&RightBrace) && !self.at_end() {
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

            bail!("{:?} Invalid assignment target.", eq)
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
        if !self.check(&RightParen) {
            loop {
                if args.len() >= 255 {
                    let tok = self.peek().clone();
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
                    let name =
                        self.consume(Identifier("".into()), "Expect property name after '.'.")?;
                    expr = expr::Get::new(expr, name);
                }
                LeftParen => expr = self.finish_call(expr)?,
                _ => unreachable!(),
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> ParseResult {
        let token = self.tokens.next().unwrap();
        Ok(expr::Literal::new(match token.tok_type() {
            TokenType::False => LoxType::Bool(false),
            TokenType::True => LoxType::Bool(true),
            TokenType::Nil => LoxType::Nil,
            TokenType::Number(num) => LoxType::Number(*num),
            TokenType::String(s) => LoxType::String(s.as_str().into()),
            TokenType::This => return Ok(expr::This::new(token)),
            TokenType::Identifier(_) => return Ok(expr::Variable::new(token)),

            TokenType::LeftParen => {
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, "Expected ')' after expression")?;
                return Ok(expr::Grouping::new(expr));
            }
            _bad => bail!("{:?} Expect expression.", token),
        }))
    }

    fn at_end(&mut self) -> bool {
        self.peek().tok_type() == &TokenType::Eof
    }

    fn advance(&mut self) -> Option<Token> {
        self.tokens.next()
    }

    fn check(&mut self, tok: &TokenType) -> bool {
        self.peek().tok_type() == tok
    }

    fn consume(&mut self, tok: TokenType, error: &str) -> Result<Token> {
        self.match_advance(&[tok])
            .ok_or_else(|| anyhow!("{:?} {}", self.peek(), error))
    }

    fn peek(&mut self) -> &Token {
        self.tokens.peek().unwrap()
    }

    fn match_advance(&mut self, types: &[TokenType]) -> Option<Token> {
        for t in types {
            if self.check(t) {
                return Some(self.advance().unwrap());
            }
        }
        None
    }

    fn synchronize(&mut self) {
        while !self.at_end() {
            let tok = self.advance().unwrap();

            if tok.tok_type() == &Semicolon {
                break;
            }

            match self.peek().tok_type() {
                TokenType::Class
                | TokenType::Fun
                | TokenType::Var
                | TokenType::For
                | TokenType::If
                | TokenType::While
                | TokenType::Print
                | TokenType::Return => break,

                _ => {}
            }
        }
    }
}
