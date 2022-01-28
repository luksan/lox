use crate::clox::compiler::compile;
use crate::clox::value::Value;
use crate::clox::{Chunk, OpCode};
use crate::LoxError;

#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("Compilation error")]
    CompileError(#[from] LoxError),
    #[error("VM runtime error")]
    RuntimeError(#[from] anyhow::Error),
}

pub struct Vm {
    stack: Vec<Value>,
}

impl Vm {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(256),
        }
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), VmError> {
        let chunk = compile(source)?;
        self.run(&chunk)
    }

    fn run(&mut self, chunk: &Chunk) -> Result<(), VmError> {
        let mut ip = chunk.code.as_ptr();
        macro_rules! read_byte {
            () => {{
                let b = unsafe { *ip };
                unsafe {
                    ip = ip.add(1);
                }
                b
            }};
        }
        macro_rules! read_constant {
            () => {
                chunk.constants[read_byte!()]
            };
        }

        macro_rules! binary_op {
            ($op:tt) => {{
                let b = self.pop().as_f64()?;
                let a = self.pop().as_f64()?;
                self.push(a $op b);}}
        }
        loop {
            let instr = read_byte!();
            let op: OpCode = instr.into();
            match op {
                OpCode::Constant => self.stack.push(read_constant!()),
                OpCode::Add => binary_op!(+),
                OpCode::Subtract => binary_op!(-),
                OpCode::Multiply => binary_op!(*),
                OpCode::Divide => binary_op!(/),
                OpCode::Negate => {
                    let x = -self.pop().as_f64()?;
                    self.push(x);
                }
                OpCode::Return => {
                    println!("{:?}", self.pop());
                    return Ok(());
                }
                OpCode::BadOpCode => {}
            }
        }
    }

    fn push(&mut self, val: impl Into<Value>) {
        self.stack.push(val.into())
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }
}
