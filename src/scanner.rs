use std::str::Chars;

enum TokenType {
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

struct Token {
    typ: TokenType,
    lexeme: String,
    literal: String,
    line: usize,
}

impl Token {
    fn new(typ: TokenType, lexeme: impl AsRef<str>, literal: impl AsRef<str>, line: usize) -> Self {
        Self {
            typ,
            lexeme: lexeme.as_ref().to_owned(),
            literal: literal.as_ref().to_owned(),
            line,
        }
    }
}
struct Scanner<'src> {
    source: &'src str,
    tokens: Vec<Token>,

    start: Chars<'src>, // Start of current token
    line: usize,        // current line for error reports
    current: Chars<'src>,
    peek: Option<char>,
}

impl<'src> Scanner<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            tokens: vec![],
            start: source.chars(),
            line: 0,
            current: source.chars(),
            peek: None,
        }
    }

    pub fn scan_tokens(&mut self) {
        while !self.is_at_end() {
            self.start = self.current.clone();
            self.scan_token();
        }
        self.tokens
            .push(Token::new(TokenType::Eof, "", "", self.line));
    }

    fn scan_token(&mut self) {}

    fn add_token(&mut self, tok: TokenType) {}
    fn advance(&mut self) -> Option<char> {
        self.peek.take().or_else(|| self.current.next())
    }

    fn peek(&mut self) -> Option<char> {
        if self.peek.is_none() {
            self.peek = self.current.next();
        }
        self.peek
    }

    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }
}
