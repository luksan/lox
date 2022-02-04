use crate::clox::compiler::compile;
use crate::clox::mm::Heap;
use crate::clox::table::LoxTable;
use crate::clox::value::Value;
use crate::clox::{Chunk, OpCode};
use crate::LoxError;
use anyhow::{anyhow, bail, Context};

#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("Compilation error")]
    CompileError(#[from] LoxError),
    #[error("VM runtime error")]
    RuntimeError(#[from] anyhow::Error),
}

pub struct Vm {
    stack: Vec<Value>,
    heap: Heap,
    globals: LoxTable,
}

impl Vm {
    pub fn new() -> Self {
        println!("Created new VM.");
        println!("Value size: {}", std::mem::size_of::<Value>());
        Self {
            stack: Vec::with_capacity(256),
            heap: Heap::new(),
            globals: LoxTable::new(),
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
                let b = self.peek(0).as_f64().context("Operands must be numbers.")?;
                let a = self.peek(1).as_f64().context("Operands must be numbers.")?;
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
                OpCode::Pop => {
                    self.pop();
                }
                OpCode::GetGlobal => {
                    let name = read_constant!().as_loxstr().unwrap();
                    if let Some(v) = self.globals.get(name) {
                        self.push(v);
                    } else {
                        Err(anyhow!("Undefined variable '{}'.", name))?;
                    }
                }
                OpCode::DefineGlobal => {
                    let name = read_constant!().as_loxstr().unwrap();
                    self.globals.set(name, self.peek(0));
                    self.pop();
                }
                OpCode::Equal => {
                    let a = self.pop();
                    let b = self.pop();
                    self.push(a == b);
                }
                OpCode::Greater => binary_op!(>),
                OpCode::Less => binary_op!(<),
                OpCode::Add => {
                    if let (Ok(a), Ok(b)) = (self.peek(1).as_str(), self.peek(0).as_str()) {
                        let new = [a, b].join("");
                        let s = self.heap.new_string(new);
                        self.pop();
                        self.pop();
                        self.stack.push(s);
                    } else {
                        // FIXME: error message in Ch 19.4.1
                        binary_op!(+)
                    }
                }
                OpCode::Subtract => binary_op!(-),
                OpCode::Multiply => binary_op!(*),
                OpCode::Divide => binary_op!(/),
                OpCode::Not => {
                    let neg = self.pop().is_falsey();
                    self.push(neg)
                }
                OpCode::Negate => {
                    let x = self.peek(0).as_f64().context("Operand must be a number.")?;
                    self.pop();
                    self.push(-x);
                }
                OpCode::Print => {
                    println!("{}", self.pop());
                }
                OpCode::Return => {
                    return Ok(());
                }
                OpCode::BadOpCode => {}
            }
        }
    }

    fn push(&mut self, val: impl Into<Value>) {
        self.stack.push(val.into())
    }

    fn peek(&self, pos: usize) -> Value {
        self.stack[self.stack.len() - pos - 1]
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }
}
