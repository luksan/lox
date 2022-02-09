use crate::clox::compiler::compile;
use crate::clox::mm::{Heap, Obj};
use crate::clox::table::LoxTable;
use crate::clox::value::{Closure, Function, NativeFn, NativeFnRef, ObjTypes, Upvalue, Value};
use crate::clox::{Chunk, OpCode};
use crate::LoxError;
use std::ptr;

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
    open_upvalues: *mut Obj<Upvalue>,
}

#[derive(Copy, Clone, Debug)]
pub struct CallFrame {
    closure: *const Obj<Closure>,
    ip: *const u8,
    stack_offset: usize,
}

impl CallFrame {
    fn disassemble(&self) {
        let (func, name) = unsafe { self.closure.as_ref() }
            .map(|c| (c.function(), c.function().name()))
            .unwrap();
        func.chunk.disassemble(name);
    }

    fn chunk(&self) -> &'static Chunk {
        &unsafe { self.closure.as_ref() }.unwrap().function().chunk
    }
}

impl Vm {
    pub fn new() -> Self {
        // println!("Created new VM.");
        // println!("Value size: {}", std::mem::size_of::<Value>());
        let mut new = Self {
            frames: Vec::with_capacity(FRAMES_MAX),
            stack: Vec::with_capacity(FRAMES_MAX * 256),
            heap: Heap::new(),
            globals: LoxTable::new(),
            open_upvalues: ptr::null_mut(),
        };
        new.define_native("clock", natives::clock);
        new
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), VmError> {
        let function = compile(source, &mut self.heap)?;
        self.push(ObjTypes::from(function));
        let closure = self.heap.new_object(Closure::new(function));
        self.pop();
        self.push(closure as *const _);
        let frame = self.call(closure, 0)?;
        self.run(frame)
    }

    fn run(&mut self, mut frame: CallFrame) -> Result<(), VmError> {
        macro_rules! ip_incr {
            ($inc:expr) => {
                frame.ip = frame.ip.add($inc as usize);
            };
        }
        macro_rules! ip_decr {
            ($dec:expr) => {
                frame.ip = frame.ip.sub($dec as usize);
            };
        }
        macro_rules! read_byte {
            () => {{
                unsafe {
                    let b = *frame.ip;
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
                frame.chunk().constants[read_byte!()]
            };
        }

        macro_rules! runtime_error {
            // FIXME: Ch 24.5.3 -> stack trace
            ($fmt:literal $(,)? $( $e:expr ),*) => {{
                let idx = unsafe {frame.ip.offset_from(frame.chunk().code.as_ptr()) }- 1;
                let line = frame.chunk().lines[idx as usize];
                eprintln!($fmt, $($e),*);
                Err(anyhow!("[line {}] in script", line))
            }};
            ($result:expr) => {{
                if $result.is_ok() {
                    $result
                }else {
                    runtime_error!("{}", $result.unwrap_err())
                }
            }};
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
            // frame.chunk().disassemble_instruction(unsafe { frame.ip.offset_from(frame.chunk().code.as_ptr()) } as usize);
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
                    self.push(self.stack[slot as usize + frame.stack_offset]);
                }
                OpCode::SetLocal => {
                    let slot = read_byte!();
                    self.stack[slot as usize + frame.stack_offset] = self.peek(0);
                }
                OpCode::GetGlobal => {
                    let name = read_constant!().as_object().unwrap();
                    if let Some(v) = self.globals.get(name) {
                        self.push(v);
                    } else {
                        runtime_error!("Undefined variable '{}'.", name)?;
                    }
                }
                OpCode::DefineGlobal => {
                    let name = read_constant!().as_object().unwrap();
                    self.globals.set(name, self.peek(0));
                    self.pop();
                }
                OpCode::SetGlobal => {
                    let name = read_constant!().as_object().unwrap();
                    if self.globals.set(name, self.peek(0)) {
                        self.globals.delete(name);
                        runtime_error!("Undefined variable '{}'.", name)?;
                    }
                }
                OpCode::GetUpvalue => {
                    let slot = read_byte!();
                    self.push(unsafe { frame.closure.as_ref().unwrap() }.read_upvalue(slot));
                }
                OpCode::SetUpvalue => {
                    let slot = read_byte!();
                    let value = self.peek(0);
                    unsafe { frame.closure.as_ref().unwrap() }.write_upvalue(slot, value);
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
                    if let Some(new_frame) = runtime_error!(self.call_value(callee, arg_count))? {
                        self.frames.push(std::mem::replace(&mut frame, new_frame));
                    }
                }
                OpCode::Closure => {
                    let function = read_constant!().as_object::<Function>().unwrap();
                    let closure = self.heap.new_object::<Closure>(Closure::new(function));
                    self.push(closure as *const _);
                    let stack_ptr = self.stack.as_mut_ptr();
                    for uv in closure.upvalues.iter_mut() {
                        let is_local = read_byte!() == 1;
                        let index = read_byte!() as usize;
                        *uv = if is_local {
                            self.capture_upvalue(unsafe {
                                stack_ptr.add(index + frame.stack_offset)
                            })
                        } else {
                            unsafe { frame.closure.as_ref().unwrap() }.upvalues[index]
                        }
                    }
                }
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.len() - 1);
                    self.pop();
                }
                OpCode::Return => {
                    // Ch 24.5.4
                    let result = self.pop();
                    self.close_upvalues(frame.stack_offset);
                    if let Some(outer_frame) = self.frames.pop() {
                        self.stack.truncate(frame.stack_offset);
                        self.push(result);
                        frame = outer_frame;
                    } else {
                        self.pop();
                        return Ok(());
                    }
                }
                OpCode::BadOpCode => {
                    frame.disassemble();
                    // Can't use runtime_error!() since it expects a valid IP
                    Err(anyhow!("Encountered invalid OpCode {}", op as u8))?;
                }
            }
        }
    }

    fn print_stack(&self, hdr: &str) {
        println!("Stack dump: {}", hdr);
        self.stack
            .iter()
            .rev()
            .enumerate()
            .for_each(|(i, v)| println!("[{}] {:?}", i, v));
    }

    fn capture_upvalue(&mut self, stack_ptr: *mut Value) -> &'static mut Obj<Upvalue> {
        let mut uv_ptr = self.open_upvalues;
        let mut prev_ptr = ptr::null_mut();
        while let Some(uv) = unsafe { uv_ptr.as_ref() } {
            if uv.location < stack_ptr {
                break;
            }
            if uv.location == stack_ptr {
                return unsafe { uv_ptr.as_mut().unwrap() };
            }
            prev_ptr = uv_ptr;
            uv_ptr = uv.next_open_upvalue;
        }
        let upvalue = self.heap.new_object(Upvalue::new(stack_ptr));
        upvalue.next_open_upvalue = uv_ptr;
        if prev_ptr.is_null() {
            self.open_upvalues = upvalue;
        } else {
            unsafe { (*prev_ptr).next_open_upvalue = upvalue }
        }
        upvalue
    }

    fn close_upvalues(&mut self, stack_offset: usize) {
        // Ch 25.4.4
        let last = self.stack.as_mut_ptr().wrapping_add(stack_offset);
        while let Some(uv) = unsafe { self.open_upvalues.as_mut() } {
            if uv.location < last {
                break;
            }
            unsafe { uv.close() }
            self.open_upvalues = uv.next_open_upvalue;
        }
    }

    fn call_value(&mut self, callee: Value, arg_count: u8) -> Result<Option<CallFrame>> {
        if let Some(closure) = callee.as_object() {
            self.call(closure, arg_count).map(Some)
        } else if let Some(native) = callee.as_object::<NativeFn>() {
            let arg_start = self.stack.len() - arg_count as usize;
            let result = native.call_native(&self.stack[arg_start..])?;
            self.push(result);
            return Ok(None);
        } else {
            bail!("Can only call functions and classes.")
        }
    }

    fn call(&self, closure: &Obj<Closure>, arg_count: u8) -> Result<CallFrame> {
        if arg_count != closure.function().arity {
            bail!(
                "Expected {} arguments but got {}.",
                closure.function().arity,
                arg_count
            );
        }
        if self.frames.len() >= FRAMES_MAX {
            bail!("Stack overflow.")
        }

        let frame = CallFrame {
            closure,
            ip: closure.function().chunk.code.as_ptr(),
            stack_offset: self.stack.len() - arg_count as usize - 1,
        };
        // frame.disassemble();
        Ok(frame)
    }

    fn define_native(&mut self, name: &str, function: NativeFnRef) {
        let name = self.heap.new_string(name.to_string());
        self.push(name);
        let native: *const _ = self.heap.new_object::<NativeFn>(function.into());
        self.push(native);
        self.globals.set(name.as_object().unwrap(), native.into());
        self.pop();
        self.pop();
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

mod natives {
    use super::{Result, Value};
    use once_cell::sync::OnceCell;

    pub fn clock(_args: &[Value]) -> Result<Value> {
        static START_TIME: OnceCell<std::time::Instant> = OnceCell::new();
        Ok(START_TIME
            .get_or_init(|| std::time::Instant::now())
            .elapsed()
            .as_secs_f64()
            .into())
    }
}
