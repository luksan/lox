use crate::clox::compiler::compile;
use crate::clox::mm::Heap;
use crate::clox::table::LoxTable;
use crate::clox::value::{Function, ObjTypes, Object, Value};
use crate::clox::OpCode;
use crate::LoxError;

use anyhow::{anyhow, bail, Result};

#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("Compilation error")]
    CompileError(#[from] LoxError),
    #[error("VM runtime error")]
    RuntimeError(#[from] anyhow::Error),
}

const FRAMES_MAX: usize = 64;

pub struct Vm {
    frames: Vec<CallFrame>,
    stack: Vec<Value>,
    heap: Heap,
    globals: LoxTable,
}

pub struct CallFrame {
    function: *const Object<Function>,
    ip: *const u8,
    stack_offset: usize,
}

impl Vm {
    pub fn new() -> Self {
        // println!("Created new VM.");
        // println!("Value size: {}", std::mem::size_of::<Value>());
        Self {
            frames: Vec::with_capacity(FRAMES_MAX),
            stack: Vec::with_capacity(FRAMES_MAX * 256),
            heap: Heap::new(),
            globals: LoxTable::new(),
        }
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), VmError> {
        let function = compile(source, &mut self.heap)?;
        self.push(ObjTypes::from(function));
        let frame = self.call(unsafe { function.as_ref().unwrap() }, 0)?;
        self.frames.push(frame);
        self.run()
    }

    fn run(&mut self) -> Result<(), VmError> {
        let frame = self.frames.last_mut().unwrap();
        let chunk = &unsafe { frame.function.as_ref() }.unwrap().chunk;
        let mut ip: *const u8 = chunk.code.as_ptr();
        let mut stack_offset = frame.stack_offset;

        macro_rules! ip_incr {
            ($inc:expr) => {
                ip = ip.add($inc as usize);
            };
        }
        macro_rules! ip_decr {
            ($dec:expr) => {
                ip = ip.sub($dec as usize);
            };
        }
        macro_rules! read_byte {
            () => {{
                unsafe {
                    let b = *ip;
                    ip_incr!(1);
                    b
                }
            }};
        }
        macro_rules! read_short {
            () => {{
                let a = read_byte!() as u16;
                let b = read_byte!() as u16;
                a << 8 | b
            }};
        }
        macro_rules! read_constant {
            () => {
                chunk.constants[read_byte!()]
            };
        }

        macro_rules! runtime_error {
            // FIXME: Ch 24.5.3
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
                    self.push(self.stack[slot as usize + stack_offset]);
                }
                OpCode::SetLocal => {
                    let slot = read_byte!();
                    self.stack[slot as usize + stack_offset] = self.peek(0);
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
                OpCode::Jump => {
                    let offset = read_short!();
                    unsafe {
                        ip_incr!(offset);
                    }
                }
                OpCode::JumpIfFalse => {
                    let offset = read_short!();
                    if self.peek(0).is_falsey() {
                        unsafe {
                            ip_incr!(offset);
                        }
                    }
                }
                OpCode::Loop => {
                    let offset = read_short!();
                    unsafe {
                        ip_decr!(offset);
                    }
                }
                OpCode::Call => {
                    // Ch 24.5.1
                    let arg_count = read_byte!();
                    let callee = self.peek(arg_count as usize);
                    let new_frame = self.call_value(callee, arg_count)?;
                    self.frames.last_mut().map(|f| f.ip = ip);
                    ip = new_frame.ip;
                    stack_offset = new_frame.stack_offset;
                    self.frames.push(new_frame);
                }
                OpCode::Return => {
                    // Ch 24.5.4
                    let result = self.pop();
                    let new_stack_len = self.frames.pop().unwrap().stack_offset;
                    if self.frames.is_empty() {
                        self.pop();
                        return Ok(());
                    }
                    self.stack.truncate(new_stack_len);
                    self.push(result);
                    ip = self.frames.last().unwrap().ip;
                }
                OpCode::BadOpCode => {}
            }
        }
    }

    fn call_value(&mut self, callee: Value, arg_count: u8) -> Result<CallFrame> {
        if let Ok(fun) = callee.as_function() {
            self.call(fun, arg_count)
        } else {
            bail!("Can only call functions and classes.")
        }
    }

    fn call(&mut self, function: &Object<Function>, arg_count: u8) -> Result<CallFrame> {
        if arg_count != function.arity {
            bail!(
                "Expected {} arguments but got {}.",
                function.arity,
                arg_count
            );
        }
        if self.frames.len() >= FRAMES_MAX {
            bail!("Stack overflow.")
        }

        Ok(CallFrame {
            function,
            ip: function.chunk.code.as_ptr(),
            stack_offset: self.stack.len() - arg_count as usize - 1,
        })
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
