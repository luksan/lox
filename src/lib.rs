#![allow(dead_code)]
#![allow(
    clippy::option_map_unit_fn,
    clippy::new_without_default,
    clippy::try_err
)]

pub mod clox;
mod jlox;
mod scanner;

pub use jlox::lox_types::LoxType;

use anyhow::{anyhow, Context};

use jlox::interpreter::Interpreter;
use jlox::parser::Parser;
use jlox::resolver::Resolver;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

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

#[derive(Debug, thiserror::Error)]
pub enum LoxError {
    #[error("Compilation error")]
    CompileError(anyhow::Error),
    #[error("Runtime error")]
    RuntimeError(anyhow::Error),
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
            .map_err(LoxError::CompileError)?;

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
        let scan_result = scanner.scan_tokens();
        let mut parser = Parser::new(scanner);
        let ast = parser.parse().map_err(|e| {
            self.had_error = true;
            LoxError::CompileError(e)
        })?;
        scan_result?; // abort if there were scanning errors, but not before trying to parse

        let errors = Resolver::resolve(&mut self.interpreter, &ast);
        if !errors.is_empty() {
            return Err(LoxError::CompileError(anyhow!(
                "Aborting due to resolver errors."
            )));
        }
        self.interpreter
            .interpret(&ast)
            .map_err(LoxError::RuntimeError)
    }
}
