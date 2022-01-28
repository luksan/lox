use std::result::Result as StdResult;

use lox::clox::Vm;
use lox::LoxError;
use std::io::Write;

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CmdOpts {
    /// Lox script file
    #[structopt(parse(from_os_str))]
    script: Option<PathBuf>,
}

#[allow(unused)]
fn main() {
    let opts = CmdOpts::from_args();

    if let Some(script) = opts.script {
        if let Err(e) = run_file(script) {
            let exit_code = match e {
                LoxError::CompileError(_) => 65,
                LoxError::RuntimeError(e) => {
                    eprintln!("{}", e);
                    70
                }
            };
            std::process::exit(exit_code);
        }
    } else {
        repl();
    }
}

fn run_file(path: impl AsRef<Path>) -> StdResult<(), LoxError> {
    let source = std::fs::read_to_string(path)
        .context("Failed to read source file.")
        .map_err(|e| LoxError::CompileError(e))?;
    let mut vm = Vm::new();
    vm.interpret(source.as_ref())
        .context("Runtime error")
        .map_err(|e| LoxError::RuntimeError(e))?;
    Ok(())
}

fn repl() -> Result<()> {
    let mut vm = Vm::new();
    let mut line = String::new();
    loop {
        print!("> ");
        std::io::stdout().flush()?;
        if std::io::stdin().read_line(&mut line)? == 0 {
            println!();
            break;
        }
        vm.interpret(&line)?;
        line.clear();
    }
    Ok(())
}
