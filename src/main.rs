use lox::{Lox, LoxError};
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CmdOpts {
    /// Lox script file
    #[structopt(parse(from_os_str))]
    script: Option<PathBuf>,
}

fn main() {
    let opts = CmdOpts::from_args();

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
