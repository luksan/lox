use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;

use anyhow::{bail, Result};
use clap::Parser;
use miette::{Context, IntoDiagnostic};

use lox::clox::{self, CloxSettings, Vm};
use lox::ErrorKind;

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
fn main() -> miette::Result<()> {
    let opts = CmdOpts::parse();

    tracing_subscriber::fmt::init();

    let mut clox_settings = CloxSettings {
        disassemble_compiler_output: opts.print_comp_asm,
        output_ci_compliant: opts.ci_testsuite,
        gc_stress_test: opts.gc_stress_test,
        ..Default::default()
    };

    clox::set_settings(clox_settings);

    let Some(ref path) = opts.script else { repl(); return Ok(()); };

    let source = std::fs::read_to_string(path)
        .into_diagnostic()
        .with_context(|| format!("Failed to read source file {}", path.to_string_lossy()))?;

    let heap = clox::Heap::new();
    let mut vm = Vm::new(&heap);
    let Err(vm_err) = vm.interpret(source.as_ref()) else { return Ok(()) };

    let exit_code = match vm_err.kind() {
        ErrorKind::CompilationError => 65,
        ErrorKind::RuntimeError => 70,
    };
    if opts.ci_testsuite {
        eprintln!("{vm_err}");
    } else {
        eprintln!("{:?}", miette::Report::new(vm_err).with_source_code(source));
    }
    std::process::exit(exit_code);
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
