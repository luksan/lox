use crate::clox::compiler::compile;
use crate::clox::mm::Heap;
use crate::clox::table::LoxTable;
use crate::clox::value::Value;
use crate::clox::{Chunk, OpCode};
use crate::LoxError;
use anyhow::anyhow;

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
        // println!("Created new VM.");
        // println!("Value size: {}", std::mem::size_of::<Value>());
        Self {
            stack: Vec::with_capacity(256),
            heap: Heap::new(),
            globals: LoxTable::new(),
        }
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), VmError> {
        let chunk = compile(source, &mut self.heap)?;
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

        macro_rules! runtime_error {
            ($fmt:literal $(,)? $( $e:expr ),*) => {{
                let idx = unsafe {ip.offset_from(chunk.code.as_ptr()) }- 1;
                let line = chunk.lines[idx as usize];
                eprintln!($fmt, $($e),*);
                Err(anyhow!("[line {}] in script", line))}
            };
        }

        macro_rules! binary_op {
            ($op:tt) => {binary_op!("Operands must be numbers.", $op)};
            ($err:literal, $op:tt) => {{ loop {
                let (a,b) = if let Ok(ab)  =self.peek(0).as_f64().and_then(|b|self.peek(1).as_f64().map(|a|(a,b))) {
                    ab
                }else { break runtime_error!($err)};
                self.pop(); self.pop();
                self.push(a $op b);
                break Ok(());
            }?;
            }
        }}
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
                OpCode::GetLocal => {
                    let slot = read_byte!();
                    self.push(self.stack[slot as usize]);
                }
                OpCode::SetLocal => {
                    let slot = read_byte!();
                    self.stack[slot as usize] = self.peek(0);
                }
                OpCode::GetGlobal => {
                    let name = read_constant!().as_loxstr().unwrap();
                    if let Some(v) = self.globals.get(name) {
                        self.push(v);
                    } else {
                        runtime_error!("Undefined variable '{}'.", name)?;
                    }
                }
                OpCode::DefineGlobal => {
                    let name = read_constant!().as_loxstr().unwrap();
                    self.globals.set(name, self.peek(0));
                    self.pop();
                }
                OpCode::SetGlobal => {
                    let name = read_constant!().as_loxstr().unwrap();
                    if self.globals.set(name, self.peek(0)) {
                        self.globals.delete(name);
                        runtime_error!("Undefined variable '{}'.", name)?;
                    }
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
                        binary_op!("Operands must be two numbers or two strings.", +)
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
                    if let Ok(x) = self.peek(0).as_f64() {
                        self.pop();
                        self.push(-x);
                    } else {
                        runtime_error!("Operand must be a number.")?;
                    }
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
