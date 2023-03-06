use std::path::PathBuf;

use clap::Parser;

use lox::{Lox, LoxError};

#[derive(Debug, Parser)]
struct CmdOpts {
    /// Lox script file
    script: Option<PathBuf>,
}

fn main() {
    let opts = CmdOpts::parse();

    if let Some(script) = opts.script {
        if let Err(e) = Lox::run_file(script) {
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
        Lox::run_prompt();
    }
}
