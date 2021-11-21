#![allow(dead_code)]
mod ast;
mod environment;
mod interpreter;
mod lox_types;
mod parser;
mod scanner;

pub use lox_types::LoxValue;

use anyhow::Result;

use crate::interpreter::Interpreter;
use crate::parser::Parser;
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

    pub fn run_file(script: impl AsRef<Path>) -> Result<()> {
        let mut file = File::open(script)?;
        let mut data = String::new(); // FIXME: preallocate correct len
        file.read_to_string(&mut data)?;

        Self::new().run(data)
    }

    pub fn run_prompt() -> Result<()> {
        let mut lox = Lox::new();
        loop {
            print!("> ");
            let _ = std::io::stdout().flush();
            let mut buffer = String::new();
            if std::io::stdin().read_line(&mut buffer)? == 0 {
                break;
            }
            if let Err(e) = lox.run(buffer) {
                eprintln!("{}", e);
            }
            lox.had_error = false;
        }
        Ok(())
    }

    fn run(&mut self, source: impl AsRef<str>) -> Result<()> {
        let mut scanner = scanner::Scanner::new(source.as_ref());
        scanner.scan_tokens();
        let mut parser = Parser::new(scanner);
        let ast = parser.parse()?;
        self.interpreter.interpret(&ast)
    }
}
