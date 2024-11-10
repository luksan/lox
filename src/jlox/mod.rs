use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use anyhow::Context;

use lox_types::LoxType;

use crate::ast::ResolverError;
use crate::ast::{self, ParseError};
use crate::jlox::interpreter::Interpreter;
use crate::ErrorKind;

mod environment;
mod interpreter;
mod lox_types;

#[derive(Debug)]
pub enum JloxError {
    CompilationError(Vec<ParseError>),
    ResolverErrors(Vec<ResolverError>),
    RuntimeError(anyhow::Error),
    Other(anyhow::Error),
}

impl JloxError {
    pub fn compile(source: Vec<ParseError>) -> Self {
        Self::CompilationError(source)
    }

    pub fn runtime(source: anyhow::Error) -> Self {
        Self::RuntimeError(source)
    }

    pub fn kind(&self) -> ErrorKind {
        match self {
            JloxError::CompilationError(_) => ErrorKind::CompilationError,
            JloxError::ResolverErrors(_) => ErrorKind::CompilationError,
            JloxError::RuntimeError(_) => ErrorKind::RuntimeError,
            Self::Other(_) => ErrorKind::CompilationError,
        }
    }
}

impl From<anyhow::Error> for JloxError {
    fn from(value: anyhow::Error) -> Self {
        Self::Other(value)
    }
}

impl Error for JloxError {}

impl Display for JloxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CompilationError(errors) => {
                for err in &errors[0..errors.len() - 1] {
                    writeln!(f, "{err}")?;
                }
                write!(f, "{}", errors.last().unwrap())
            }
            Self::ResolverErrors(errors) => {
                for err in &errors[0..errors.len() - 1] {
                    writeln!(f, "{err}")?;
                }
                write!(f, "{}", errors.last().unwrap())
            }
            Self::RuntimeError(err) => write!(f, "{err}"),
            Self::Other(err) => write!(f, "{err}"),
        }
    }
}

impl From<Vec<ResolverError>> for JloxError {
    fn from(value: Vec<ResolverError>) -> Self {
        Self::ResolverErrors(value)
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

    pub fn run_file(script: impl AsRef<Path>) -> Result<(), JloxError> {
        let mut data = String::new(); // FIXME: preallocate correct len
        File::open(script)
            .and_then(|mut file| file.read_to_string(&mut data))
            .context("Failed to read lox script file.")?;

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

    fn run(&mut self, source: impl AsRef<str>) -> Result<(), JloxError> {
        let ast = ast::parse(source.as_ref()).map_err(|e| {
            self.had_error = true;
            JloxError::compile(e)
        })?;

        // println!("{ast:#?}");

        self.interpreter.interpret(&ast)
    }
}
