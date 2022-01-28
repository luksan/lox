use crate::clox::compiler::compile;
use crate::clox::value::Value;
use crate::clox::{Chunk, OpCode};
use crate::LoxError;
use anyhow::Context;

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
        println!("Created new VM.");
        println!("Value size: {}", std::mem::size_of::<Value>());
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
                let b = self.peek().as_f64().context("Operands must be numbers.")?;
                let a = self.peek().as_f64().context("Operands must be numbers.")?;
                self.pop(); self.pop();
                self.push(a $op b);}}
        }
        loop {
            let instr = read_byte!();
            let op: OpCode = instr.into();
            match op {
                OpCode::Constant => self.stack.push(read_constant!()),
                OpCode::Nil => self.push(Value::Nil),
                OpCode::True => self.push(Value::Bool(true)),
                OpCode::False => self.push(Value::Bool(false)),
                OpCode::Equal => {
                    let a = self.pop();
                    let b = self.pop();
                    self.push(a == b);
                }
                OpCode::Greater => binary_op!(>),
                OpCode::Less => binary_op!(<),
                OpCode::Add => binary_op!(+),
                OpCode::Subtract => binary_op!(-),
                OpCode::Multiply => binary_op!(*),
                OpCode::Divide => binary_op!(/),
                OpCode::Not => {
                    let neg = self.pop().is_falsey();
                    self.push(neg)
                }
                OpCode::Negate => {
                    let x = self.peek().as_f64().context("Operand must be a number.")?;
                    self.pop();
                    self.push(-x);
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

    fn peek(&self) -> Value {
        *self.stack.last().unwrap()
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }
}
