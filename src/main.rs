use anyhow::Result;

use lox::Lox;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CmdOpts {
    /// Lox script file
    #[structopt(parse(from_os_str))]
    script: Option<PathBuf>,
}

fn main() -> Result<()> {
    let opts = CmdOpts::from_args();

    if let Some(script) = opts.script {
        Lox::run_file(script)
    } else {
        Lox::run_prompt()
    }
}
