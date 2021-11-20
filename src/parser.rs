use anyhow::{anyhow, bail, Result};

use crate::ast::stmt::{ListStmt, Stmt};
use crate::ast::{
    expr::{self, Expr},
    stmt, LoxValue, TypeMap,
};
use crate::scanner::TokenType::{
    Bang, BangEqual, Equal, EqualEqual, Greater, GreaterEqual, Identifier, LeftBrace, Less,
    LessEqual, Minus, Plus, Print, RightBrace, Semicolon, Slash, Star, Var,
};
use crate::scanner::{Scanner, Token, TokenType};

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

    fn statement(&mut self) -> Result<Stmt> {
        if let Some(token) = self.match_advance(&[LeftBrace, Print]) {
            match token.tok_type() {
                Print => self.print_statement(),
                LeftBrace => Ok(stmt::Block::new(self.block()?)),
                _ => self.expression_statement(),
            }
        } else {
            self.expression_statement()
        }
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
        let expr = self.equality()?;
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
            self.primary()
        }
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
