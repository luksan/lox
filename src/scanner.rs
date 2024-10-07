use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::iter;
use std::str::Chars;

use anyhow::{bail, Context, Result};
use miette::{Diagnostic, LabeledSpan, SourceSpan};
use phf::phf_map;

#[derive(Clone, Copy, Debug)]
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
    Identifier,
    String,
    Number,

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

    Eof,
}

impl PartialEq for TokenType {
    fn eq(&self, other: &Self) -> bool {
        use std::mem::discriminant;
        discriminant(self) == discriminant(other)
    }
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
enum Literal {
    Number(f64),
    String(String),
}

#[derive(Default, Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TokSpan {
    start: usize,
    length: usize,
}

impl TokSpan {
    pub fn offset(&self) -> usize {
        self.start
    }

    pub fn len(&self) -> usize {
        self.length
    }

    fn end(&self) -> usize {
        self.start + self.len()
    }

    pub fn point_end(&self) -> Self {
        Self {
            start: self.end(),
            length: 0,
        }
    }

    pub fn extend(&self, inclusive: &Self) -> Self {
        Self {
            start: self.start,
            length: inclusive.end() - self.start,
        }
    }
}

impl From<miette::SourceSpan> for TokSpan {
    fn from(value: SourceSpan) -> Self {
        Self {
            start: value.offset(),
            length: value.len(),
        }
    }
}
impl From<TokSpan> for miette::SourceSpan {
    fn from(value: TokSpan) -> Self {
        Self::new(value.start.into(), value.length.into())
    }
}
impl From<&TokSpan> for miette::SourceSpan {
    fn from(value: &TokSpan) -> Self {
        Self::new(value.start.into(), value.length.into())
    }
}

#[derive(Clone)]
pub struct Token {
    typ: TokenType,
    lexeme: String,
    line: usize,
    literal: Option<Literal>,
    span: TokSpan,
}

impl Token {
    fn new(
        typ: TokenType,
        lexeme: &str,
        literal: Option<Literal>,
        line: usize,
        span: TokSpan,
    ) -> Self {
        Self {
            typ,
            lexeme: lexeme.to_owned(),
            line,
            literal,
            span,
        }
    }

    pub fn lexeme(&self) -> &str {
        self.lexeme.as_str()
    }

    pub fn tok_type(&self) -> TokenType {
        self.typ
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn number_literal(&self) -> f64 {
        if let Some(Literal::Number(f)) = &self.literal {
            *f
        } else {
            panic!("Not a numeric literal.")
        }
    }

    pub fn string_literal(&self) -> &str {
        if let Some(Literal::String(s)) = &self.literal {
            s
        } else {
            panic!("Not a string literal.")
        }
    }

    pub fn span(&self) -> &TokSpan {
        &self.span
    }
}

impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return write!(f, "{}", self.lexeme());
        }
        if self.typ == TokenType::Eof {
            write!(f, "[line {}] Error at end:", self.line())
        } else {
            write!(f, "[line {}] Error at '{}':", self.line(), self.lexeme)
        }
    }
}

struct SourceCursor<'src> {
    start: &'src str,
    start_byte_pos: usize,
    current: Chars<'src>,
    curr_line: usize,
    tot_len: usize,
}

impl<'src> SourceCursor<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            start: source,
            start_byte_pos: 0,
            current: source.chars(),
            curr_line: 1, // current line for error reports
            tot_len: source.len(),
        }
    }

    /// Mark the beginning of a new token
    pub fn set_start(&mut self) {
        self.start = self.current.as_str();
        self.start_byte_pos = self.tot_len - self.start.len();
    }

    pub fn curr_len(&self) -> usize {
        (self.tot_len - self.current.as_str().len()) - self.start_byte_pos
    }

    pub fn curr_span(&self) -> TokSpan {
        TokSpan {
            start: self.start_byte_pos,
            length: self.curr_len(),
        }
    }

    pub fn advance(&mut self) -> Option<char> {
        let next = self.current.next();
        if next == Some('\n') {
            self.curr_line += 1;
        }
        next
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

    pub fn peek2(&self) -> Option<[char; 2]> {
        let mut i = self.current.clone();
        Some([i.next()?, i.next()?])
    }

    pub fn substring(&self, start: usize, rear: usize) -> &str {
        let curr_len = self.start.len() - self.current.as_str().len();
        &self.start[start..curr_len - rear]
    }
}

impl<'a> Iterator for SourceCursor<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance()
    }
}

#[derive(Debug, Clone)]
pub struct TokenizationError {
    msg: String,
    line: usize,
    span: SourceSpan,
}

impl miette::Diagnostic for TokenizationError {
    fn labels(&self) -> Option<Box<dyn Iterator<Item=LabeledSpan> + '_>> {
        Some(Box::new(iter::once(LabeledSpan::new(
            Some(self.msg.clone()),
            self.span.offset(),
            self.span.len(),
        ))))
    }
    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        Some(self) // hack to work around downcasting with with_source_code() wrapper
    }
}

impl Error for TokenizationError {}
impl Display for TokenizationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[line {}] Error: {}", self.line, self.msg)
    }
}

pub struct Scanner<'src> {
    at_eof: bool,

    cursor: SourceCursor<'src>,
    curr_literal: Option<Literal>,
}

pub type TokenIter<'s> = dyn Iterator<Item=Result<Token, TokenizationError>> + 's;

impl Iterator for Scanner<'_> {
    type Item = Result<Token, TokenizationError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.at_eof {
            return None;
        }
        Some(loop {
            if self.is_at_end() {
                self.at_eof = true;
                break Ok(Token::new(
                    TokenType::Eof,
                    "",
                    None,
                    self.cursor.curr_line,
                    self.cursor.curr_span(),
                ));
            } else {
                self.cursor.set_start();
                break match self.scan_token() {
                    Ok(None) => continue,
                    Ok(Some(tok)) => Ok(tok),
                    Err(err) => Err(TokenizationError {
                        line: self.cursor.curr_line,
                        msg: err.to_string(),
                        span: self.cursor.curr_span().into(),
                    }),
                };
            }
        })
    }
}

impl<'src> Scanner<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            at_eof: false,
            cursor: SourceCursor::new(source),
            curr_literal: None,
        }
    }

    fn scan_token(&mut self) -> Result<Option<Token>> {
        let char = self.cursor.advance().unwrap(); // scan_token() is only called while !is_at_end()
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
            '<' => self.ch2('=', TokenType::LessEqual, TokenType::Less),
            '>' => self.ch2('=', TokenType::GreaterEqual, TokenType::Greater),

            '/' if self.check('/') => {
                self.cursor.find(|c| *c == '\n');
                return Ok(None);
            }
            '/' => TokenType::Slash,

            '\n' => {
                return Ok(None);
            }
            w if w.is_ascii_whitespace() => return Ok(None),

            '"' => self.string()?,

            '0'..='9' => self.number()?,

            a if a.is_alphabetic() => self.identifier()?,

            _ => bail!("Unexpected character."),
        };

        let lexeme = self.cursor.substring(0, 0);
        Ok(Some(Token::new(
            tok,
            lexeme,
            self.curr_literal.take(),
            self.cursor.curr_line,
            self.cursor.curr_span(),
        )))
    }

    fn identifier(&mut self) -> Result<TokenType> {
        self.cursor
            .advance_while(|&c| c.is_alphanumeric() || c == '_');
        let ident = self.cursor.substring(0, 0);
        Ok(KEYWORDS
            .get(ident)
            .cloned()
            .unwrap_or(TokenType::Identifier))
    }

    fn number(&mut self) -> Result<TokenType> {
        self.cursor.advance_while(char::is_ascii_digit);
        match self.cursor.peek2() {
            Some(['.', d]) if d.is_ascii_digit() => {
                self.cursor.advance(); // consume '.'
                self.cursor.advance_while(char::is_ascii_digit);
            }
            _ => {}
        }
        self.curr_literal = Some(Literal::Number(
            self.cursor
                .substring(0, 0)
                .parse()
                .context("Number parsing error")?,
        ));
        Ok(TokenType::Number)
    }

    fn string(&mut self) -> Result<TokenType> {
        self.cursor
            .find(|c| *c == '"')
            .context("Unterminated string.")?;
        self.curr_literal = Some(Literal::String(self.cursor.substring(1, 1).to_owned()));
        Ok(TokenType::String)
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
        if self.cursor.peek() == Some(ch) {
            self.cursor.advance();
            true
        } else {
            false
        }
    }

    fn is_at_end(&self) -> bool {
        self.cursor.peek().is_none()
    }
}

#[cfg(test)]
mod test_scanner {
    use super::*;
    use miette::NamedSource;

    // #[test]
    fn test_miette_error() -> Result<(), TokenizationError> {
        let source = "hej
        flupp
        var x| = 1;
        asd
        asd";
        let scanner = Scanner::new(source);
        let err: Result<Vec<_>, _> = scanner.collect();
        let report = miette::Report::new(err.unwrap_err())
            .with_source_code(NamedSource::new("test.lox", source));
        println!("{:?}", DebugDebug(report));
        Ok(())
    }

    struct DebugDebug<T: Debug>(T);
    impl<T: Debug> Debug for DebugDebug<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            Debug::fmt(&self.0, f)
        }
    }
}
