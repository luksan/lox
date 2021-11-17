use crate::ast::{Binary, Expr, Grouping, Literal, LoxValue, Unary};
use crate::scanner::TokenType::{
    Bang, BangEqual, EqualEqual, Greater, GreaterEqual, Less, LessEqual, Minus, Plus, Semicolon,
    Slash, Star,
};
use crate::scanner::{Scanner, Token, TokenType};
use std::iter::Peekable;
use std::vec::IntoIter;

use anyhow::{anyhow, bail, Result};

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
}

pub type Ast = Box<dyn Expr>;
pub type ParseResult = Result<Ast>;

impl Parser {
    pub fn new(scanner: Scanner) -> Self {
        Self {
            tokens: scanner.take_tokens().into_iter().peekable(),
        }
    }

    pub fn parse(&mut self) -> Result<Ast> {
        self.expression()
    }

    fn expression(&mut self) -> ParseResult {
        self.equality()
    }

    fn equality(&mut self) -> ParseResult {
        let mut expr = self.comparison()?;
        while let Some(operator) = self.match_advance(&[BangEqual, EqualEqual]) {
            expr = Box::new(Binary {
                left: expr,
                operator,
                right: self.comparison()?,
            })
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult {
        let mut expr = self.term()?;
        while let Some(operator) = self.match_advance(&[Greater, GreaterEqual, Less, LessEqual]) {
            expr = Binary::boxed(expr, operator, self.term()?)
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult {
        let mut expr = self.factor()?;
        while let Some(operator) = self.match_advance(&[Minus, Plus]) {
            expr = Binary::boxed(expr, operator, self.factor()?)
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult {
        let mut expr = self.unary()?;
        while let Some(operator) = self.match_advance(&[Slash, Star]) {
            expr = Binary::boxed(expr, operator, self.unary()?);
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult {
        if let Some(operator) = self.match_advance(&[Bang, Minus]) {
            Ok(Unary::boxed(operator, self.unary()?))
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> ParseResult {
        let token = self.tokens.next().unwrap();
        Ok(Literal::boxed(match token.tok_type() {
            TokenType::False => LoxValue::Bool(false),
            TokenType::True => LoxValue::Bool(true),
            TokenType::Nil => LoxValue::Nil,
            TokenType::Number(num) => LoxValue::Number(*num),
            TokenType::String(s) => LoxValue::String(s.clone()),

            TokenType::LeftParen => {
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, "Expected ')' after expression")?;
                return Ok(Grouping::boxed(expr));
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
        while let Some(tok) = self.advance() {
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
