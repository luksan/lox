#![allow(dead_code)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(
    clippy::option_map_unit_fn,
    clippy::new_without_default,
    clippy::try_err
)]

use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use anyhow::{anyhow, Context};

use jlox::interpreter::Interpreter;
pub use jlox::lox_types::LoxType;
use jlox::parser::Parser;
use jlox::resolver::Resolver;

pub mod clox;
mod jlox;
mod scanner;

fn error(line: usize, message: impl AsRef<str>) {
    report(line, "", message)
}

fn report(line: usize, pos: impl AsRef<str>, message: impl AsRef<str>) {
    eprintln!(
        "[line {}] Error {}: {}",
        line,
        pos.as_ref(),
        message.as_ref()
    );
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    CompilationError,
    RuntimeError,
}

#[derive(Debug)]
pub struct LoxError {
    kind: ErrorKind,
    source: anyhow::Error,
}

impl LoxError {
    pub fn compile(source: anyhow::Error) -> Self {
        Self {
            kind: ErrorKind::CompilationError,
            source,
        }
    }

    pub fn runtime(source: anyhow::Error) -> Self {
        Self {
            kind: ErrorKind::RuntimeError,
            source,
        }
    }

    pub fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl Error for LoxError {}

impl Display for LoxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.source)
    }
}

pub struct Lox {
    had_error: bool,
    interpreter: Interpreter,
}

impl Lox {
    fn new() -> Self {
        Self {
            had_error: false,
            interpreter: Interpreter::new(),
        }
    }

    pub fn run_file(script: impl AsRef<Path>) -> Result<(), LoxError> {
        let mut data = String::new(); // FIXME: preallocate correct len
        File::open(script)
            .and_then(|mut file| file.read_to_string(&mut data))
            .context("Failed to read lox script file.")
            .map_err(LoxError::compile)?;

        Self::new().run(data)
    }

    pub fn run_prompt() {
        let mut lox = Lox::new();
        loop {
            print!("> ");
            let _ = std::io::stdout().flush();
            let mut buffer = String::new();
            if std::io::stdin().read_line(&mut buffer).unwrap() == 0 {
                break;
            }
            if let Err(e) = lox.run(buffer) {
                eprintln!("{:?}", e);
            }
            lox.had_error = false;
        }
    }

    fn run(&mut self, source: impl AsRef<str>) -> Result<(), LoxError> {
        let mut scanner = scanner::Scanner::new(source.as_ref());
        let ast = Parser::parse(&mut scanner).map_err(|e| {
            self.had_error = true;
            LoxError::compile(e)
        })?;
        scanner.scanning_errors()?; // abort if there were scanning errors, but not before trying to parse

        let errors = Resolver::resolve(&mut self.interpreter, &ast);
        if !errors.is_empty() {
            return Err(LoxError::compile(anyhow!(
                "Aborting due to resolver errors."
            )));
        }
        self.interpreter.interpret(&ast).map_err(LoxError::runtime)
    }
}
