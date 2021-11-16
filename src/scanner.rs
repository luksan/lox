use anyhow::{bail, Context, Result};
use phf::phf_map;

use std::str::{Chars, FromStr};

#[derive(Clone, Debug)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals.
    Identifier(String),
    String(String),
    Number(f64),

    // Keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    Nil,
    If,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    // comment
    Comment,

    Eof,
}

static KEYWORDS: phf::Map<&'static str, TokenType> = phf_map! {
    "and" => TokenType::And,
    "class" =>TokenType::Class,
    "else" => TokenType::Else,
    "false" => TokenType::False,
    "for" => TokenType::For,
    "fun" => TokenType::Fun,
    "if" => TokenType::If,
    "nil" => TokenType::Nil,
    "or" => TokenType::Or,
    "print" => TokenType::Print,
    "return" => TokenType::Return,
    "super" => TokenType::Super,
    "this" => TokenType::This,
    "true" => TokenType::True,
    "var" => TokenType::Var,
    "while" => TokenType::While,
};

#[derive(Clone, Debug)]
pub struct Token {
    typ: TokenType,
    lexeme: String,
    line: usize,
}

impl Token {
    pub fn new(typ: TokenType, literal: impl AsRef<str>, line: usize) -> Self {
        Self {
            typ,
            lexeme: literal.as_ref().to_owned(),
            line,
        }
    }

    pub fn lexeme(&self) -> &str {
        self.lexeme.as_str()
    }
}

struct SourceCursor<'src> {
    source: &'src str,
    start: Chars<'src>,
    current: Chars<'src>,
    curr_len: usize,
}

impl<'src> SourceCursor<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            start: source.chars(),
            current: source.chars(),
            curr_len: 0,
        }
    }

    pub fn set_start(&mut self) {
        self.start = self.current.clone();
        self.curr_len = 0;
    }

    pub fn advance(&mut self) -> Option<char> {
        self.curr_len += 1;
        self.current.next()
    }

    pub fn advance_while(&mut self, mut test: impl FnMut(&char) -> bool) {
        while let Some(c) = self.peek() {
            if !test(&c) {
                break;
            }
            self.advance();
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.current.clone().next()
    }

    pub fn peek_next(&self) -> Option<char> {
        self.current.clone().nth(1)
    }

    pub fn substring(&self, start: usize, rear: usize) -> &str {
        &self.start.as_str()[start..self.curr_len - rear]
    }
}

pub struct Scanner<'src> {
    source: &'src str,
    tokens: Vec<Token>,

    cursor: SourceCursor<'src>,
    line: usize, // current line for error reports
}

impl<'src> Scanner<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            tokens: vec![],
            cursor: SourceCursor::new(source),
            line: 0,
        }
    }

    pub fn tokens(&self) -> &[Token] {
        self.tokens.as_slice()
    }

    pub fn scan_tokens(&mut self) {
        while !self.is_at_end() {
            self.cursor.set_start();
            match self.scan_token() {
                Ok(None) => {}
                Ok(Some(tok)) => self.tokens.push(tok),
                Err(err) => eprintln!("Scanning error on line {}: {}", self.line, err),
            }
        }
        self.tokens.push(Token::new(TokenType::Eof, "", self.line));
    }

    fn scan_token(&mut self) -> Result<Option<Token>> {
        let char = self.advance().unwrap(); // scan_token() is only called while !is_at_end()
        let tok = match char {
            '(' => TokenType::LeftParen,
            ')' => TokenType::RightParen,
            '{' => TokenType::LeftBrace,
            '}' => TokenType::RightBrace,
            ',' => TokenType::Comma,
            '.' => TokenType::Dot,
            '-' => TokenType::Minus,
            '+' => TokenType::Plus,
            ';' => TokenType::Semicolon,
            '*' => TokenType::Star,
            '!' => self.ch2('=', TokenType::BangEqual, TokenType::Bang),
            '=' => self.ch2('=', TokenType::EqualEqual, TokenType::Equal),
            '<' => self.ch2('=', TokenType::LessEqual, TokenType::Equal),
            '>' => self.ch2('=', TokenType::GreaterEqual, TokenType::Greater),

            '/' if self.check('/') => {
                while let Some(ch) = self.advance() {
                    if ch == '\n' {
                        break;
                    }
                }
                self.line += 1;
                TokenType::Comment
            }
            '/' => TokenType::Slash,

            '\n' => {
                self.line += 1;
                return Ok(None);
            }
            w if w.is_ascii_whitespace() => return Ok(None),

            '"' => self.string()?,

            '0'..='9' => self.number()?,

            a if a.is_alphabetic() => self.identifier()?,

            _ => bail!("Unexpected character."),
        };

        Ok(Some(Token {
            typ: tok,
            lexeme: self.cursor.substring(0, 0).to_owned(),
            line: self.line,
        }))
    }

    fn identifier(&mut self) -> Result<TokenType> {
        self.cursor.advance_while(|c| c.is_alphanumeric());
        let ident = self.cursor.substring(0, 0);
        Ok(KEYWORDS
            .get(ident)
            .map(|i| i.clone())
            .unwrap_or_else(|| TokenType::Identifier(ident.to_owned())))
    }

    fn number(&mut self) -> Result<TokenType> {
        self.cursor.advance_while(char::is_ascii_digit);
        if self.peek() == Some('.') {
            if let Some(after_dot) = self.cursor.peek_next() {
                if after_dot.is_ascii_digit() {
                    self.advance(); // consume '.'
                    self.cursor.advance_while(char::is_ascii_digit);
                }
            }
        }
        f64::from_str(self.cursor.substring(0, 0))
            .context("NUmber parsing error")
            .map(TokenType::Number)
    }

    fn string(&mut self) -> Result<TokenType> {
        self.cursor.advance_while(|&c| {
            if c == '\n' {
                self.line += 1;
            }
            c != '"'
        });
        if self.is_at_end() {
            bail!("Unterminated string.");
        }
        self.advance(); // The closing "
        Ok(TokenType::String(self.cursor.substring(1, 1).to_owned()))
    }

    fn advance(&mut self) -> Option<char> {
        self.cursor.advance()
    }

    fn peek(&self) -> Option<char> {
        self.cursor.peek()
    }

    fn ch2(&mut self, ch: char, matches: TokenType, nope: TokenType) -> TokenType {
        if self.check(ch) {
            matches
        } else {
            nope
        }
    }

    // Consume the next character if it matches
    fn check(&mut self, ch: char) -> bool {
        if self.peek() == Some(ch) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn is_at_end(&self) -> bool {
        self.peek().is_none()
    }
}
