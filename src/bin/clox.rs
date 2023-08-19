use std::io::Write;
use std::path::{Path, PathBuf};
use std::result::Result as StdResult;

use anyhow::{bail, Context, Result};
use clap::Parser;

use lox::clox::{self, CloxSettings, Vm, VmError};
use lox::{ErrorKind, LoxError};

#[derive(Debug, Parser)]
struct CmdOpts {
    /// Lox script file
    script: Option<PathBuf>,

    /// Indicates that we are running the craftinginterpreters testsuite,
    /// so make sure that the error/debug output is compliant.
    #[structopt(long)]
    ci_testsuite: bool,

    /// Print disassembly of compiler output before it runs.
    #[structopt(long, short)]
    print_comp_asm: bool,

    /// Run the garbage collector at every allocation
    #[structopt(long)]
    gc_stress_test: bool,
}

#[allow(unused)]
fn main() {
    let opts = CmdOpts::parse();

    tracing_subscriber::fmt::init();

    let mut clox_settings = CloxSettings {
        disassemble_compiler_output: opts.print_comp_asm,
        output_ci_compliant: opts.ci_testsuite,
        gc_stress_test: opts.gc_stress_test,
        ..Default::default()
    };

    clox::set_settings(clox_settings);

    let Some(ref script) = opts.script else { repl(); return; };
    if let Err(e) = run_file(script) {
        let exit_code = match e.kind() {
            ErrorKind::CompilationError => 65,
            ErrorKind::RuntimeError => {
                eprintln!("{}", e);
                70
            }
        };
        std::process::exit(exit_code);
    }
}

fn run_file(path: impl AsRef<Path>) -> StdResult<(), LoxError> {
    let source = std::fs::read_to_string(path)
        .context("Failed to read source file.")
        .map_err(LoxError::compile)?;
    let heap = clox::Heap::new();
    let mut vm = Vm::new(&heap);
    match vm.interpret(source.as_ref()) {
        Ok(_) => Ok(()),
        Err(VmError::CompileError(e)) => Err(e),
        Err(VmError::RuntimeError(e)) => Err(LoxError::runtime(e)),
    }
}

fn repl() -> Result<()> {
    let heap = clox::Heap::new();
    let mut vm = Vm::new(&heap);
    let mut line = String::new();
    loop {
        print!("> ");
        std::io::stdout().flush()?;
        if std::io::stdin().read_line(&mut line)? == 0 {
            println!();
            break;
        }
        if let Err(e) = vm.interpret(&line) {
            println!("{:?}", e);
            bail!("Error.");
        }
        line.clear();
    }
    Ok(())
}
