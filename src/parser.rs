use anyhow::{anyhow, bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
    TypeMap,
};
use crate::scanner::TokenType::*;
use crate::scanner::{Scanner, Token, TokenType};
use crate::LoxValue;

use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
}

pub type ParseResult = Result<Expr>;

impl Parser {
    pub fn new(scanner: Scanner) -> Self {
        Self {
            tokens: scanner.take_tokens().into_iter().peekable(),
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();
        while !self.at_end() {
            match self.declaration() {
                Ok(stmt) => statements.push(stmt),
                Err(err) => eprintln!("Parse error: {}", err),
            }
        }
        Ok(statements)
    }

    fn error(&self, msg: &str) {
        eprintln!("Error:  {}", msg);
        // FIXME: log error internally, also accept token.
    }

    fn declaration(&mut self) -> Result<Stmt> {
        let stmt = if self.match_advance(&[Var]).is_some() {
            self.var_decl()
        } else {
            self.statement()
        };
        if stmt.is_err() {
            self.synchronize()
        }
        stmt
    }

    fn var_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Identifier("".into()), "Expect variable name")?;
        let init = if self.match_advance(&[Equal]).is_some() {
            self.expression()?
        } else {
            expr::Literal::new(LoxValue::Nil)
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
        if let Some(token) = self.match_advance(&[For, If, LeftBrace, Print, While]) {
            match token.tok_type() {
                For => self.for_statement(),
                If => self.if_statement(),
                Print => self.print_statement(),
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
            expr::Literal::new(LoxValue::Bool(true))
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

    fn expression_statement(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        self.consume(Semicolon, "Expect ';' after expression.")?;
        Ok(stmt::Expression::new(expr))
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
        let expr = self.or()?;
        if let Some(eq) = self.match_advance(&[Equal]) {
            let value = self.assignment()?;
            Ok(expr.map_or_else(
                |var: expr::Variable| expr::Assign::new(var.name, value),
                |expr| {
                    // FIXME: register that error was reported set error flag. Chapter 8.4.1
                    eprintln!("Invalid assignment target. Token {:?}", eq);
                    expr
                },
            ))
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
                    self.error("Can't have more than 255 arguments.");
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
        while let Some(tok) = self.match_advance(&[LeftParen]) {
            match tok.tok_type() {
                LeftParen => expr = self.finish_call(expr)?,
                _ => unreachable!(),
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> ParseResult {
        let token = self.tokens.next().unwrap();
        Ok(expr::Literal::new(match token.tok_type() {
            TokenType::False => LoxValue::Bool(false),
            TokenType::True => LoxValue::Bool(true),
            TokenType::Nil => LoxValue::Nil,
            TokenType::Number(num) => LoxValue::Number(*num),
            TokenType::String(s) => LoxValue::String(s.clone()),
            TokenType::Identifier(_) => return Ok(expr::Variable::new(token)),

            TokenType::LeftParen => {
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, "Expected ')' after expression")?;
                return Ok(expr::Grouping::new(expr));
            }
            bad => bail!("Expected primary token, got {:?}", bad),
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
            .ok_or_else(|| anyhow!("{}", error))
    }

    fn peek(&mut self) -> &Token {
        &self.tokens.peek().unwrap()
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
