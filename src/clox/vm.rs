use std::fmt::{Debug, Formatter};
use std::ptr;
use std::ptr::NonNull;

use anyhow::{anyhow, bail, Context, Result};
use tracing::{span, Level};

use crate::clox::compiler::compile;
use crate::clox::mm::{HasRoots, Heap, Obj, ObjPtr, ObjTypes};
use crate::clox::stack::{Stack, FRAMES_MAX};
use crate::clox::table::{LoxTable, Table};
use crate::clox::value::{
    BoundMethod, Class, Closure, Function, Instance, LoxObject, LoxStr, NativeFn, NativeFnRef,
    Upvalue, Value,
};
use crate::clox::{Chunk, OpCode};
use crate::LoxError;

#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("Compilation error")]
    CompileError(#[from] LoxError),
    #[error("VM runtime error")]
    RuntimeError(#[from] anyhow::Error),
}

pub struct Vm<'heap> {
    stack: Stack,
    heap: &'heap Heap,
    globals: LoxTable,
    open_upvalues: Option<ObjPtr<Upvalue>>,
    init_string: *const Obj<LoxStr>,
}

impl Debug for Vm<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "stack: {:?}", self.stack)?;
        write!(f, ", globals: {:?}", self.globals)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct CallFrame {
    closure: NonNull<Obj<Closure>>,
    ip: *const u8,
    stack_offset: *mut Value,
}

impl CallFrame {
    fn disassemble(&self) {
        let closure = unsafe { self.closure.as_ref() };
        closure
            .function()
            .chunk
            .disassemble(closure.function().name());
    }

    fn chunk(&self) -> &'static Chunk {
        &unsafe { self.closure.as_ref() }.function().chunk
    }

    fn current_line(&self) -> isize {
        let idx = unsafe { self.ip.offset_from(self.chunk().code.as_ptr()) } - 1;
        self.chunk().lines[idx as usize] as _
    }
}

struct CallStack(Vec<CallFrame>);

impl CallStack {
    fn new() -> Self {
        Self(Vec::with_capacity(FRAMES_MAX))
    }

    fn current_frame(&mut self) -> &mut CallFrame {
        self.0.last_mut().unwrap()
    }

    fn push_frame(&mut self, new_frame: CallFrame) -> Result<&mut CallFrame> {
        if self.0.len() > FRAMES_MAX {
            bail!("Stack overflow.");
        }
        self.0.push(new_frame);
        Ok(self.0.last_mut().unwrap())
    }

    fn pop_frame(&mut self) -> Option<&mut CallFrame> {
        self.0.pop().unwrap();
        self.0.last_mut()
    }
}

impl HasRoots for CallStack {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for frame in self.0.iter() {
            unsafe { frame.closure.as_ref() }.mark(mark_obj);
        }
    }
}

pub struct Runnable<'vm, 'heap: 'vm> {
    vm: &'vm mut Vm<'heap>,
    frame: CallFrame,
}

impl Runnable<'_, '_> {
    pub fn run(&mut self) -> Result<(), VmError> {
        self.vm.run(&self.frame)?;
        self.vm.push(unsafe { self.frame.closure.as_ref() });
        Ok(())
    }
}

impl Drop for Runnable<'_, '_> {
    fn drop(&mut self) {
        // remove the pointer to out call frame from the stack
        self.vm.stack.pop();
    }
}

impl<'heap> Vm<'heap> {
    pub fn new(heap: &'heap Heap) -> Self {
        // println!("Created new VM.");
        // println!("Value size: {}", std::mem::size_of::<Value>());
        let mut new = Self {
            stack: Stack::new(),
            heap,
            globals: LoxTable::new(),
            open_upvalues: None,

            init_string: ptr::null(),
        };
        let _token = new.heap.register_gc_root(&new);
        new.init_string = new.heap.new_string("init".to_string());
        new.define_native("clock", natives::clock);
        new
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), VmError> {
        let _token = self.heap.register_gc_root(self);
        self.compile(source)?.run()
    }

    pub fn compile(&mut self, source: &str) -> Result<Runnable<'_, 'heap>, VmError> {
        let _token = self.heap.register_gc_root(self);
        let function = compile(source, self.heap)?;
        self.push(ObjTypes::from(function));
        let closure = self.heap.new_object(Closure::new(function, &mut || {
            unreachable!("No upvalues in root.")
        }));
        self.pop();
        self.push(closure as *const _);
        let frame = self.call(closure, 0)?;
        Ok(Runnable { vm: self, frame })
    }

    fn run(&mut self, frame: &CallFrame) -> Result<(), VmError> {
        let trace_span = span!(Level::TRACE, "Vm::run()");
        let _enter = trace_span.enter();

        let call_stack = &mut CallStack::new();
        let _token = self.heap.register_gc_root(call_stack);

        call_stack.push_frame(frame.clone()).unwrap();
        if let Err(e) = self.run_inner(call_stack) {
            eprintln!("{e}");
            Err(anyhow!(
                "[line {}] in script",
                call_stack.current_frame().current_line()
            ))?
        } else {
            Ok(())
        }
    }

    fn run_inner(&mut self, call_stack: &mut CallStack) -> Result<()> {
        let mut frame = call_stack.current_frame();

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
        macro_rules! read_string {
            () => {
                read_constant!().as_object::<LoxStr>().unwrap()
            };
        }

        macro_rules! push_callframe {
            ($new_frame:expr) => {
                frame = call_stack.push_frame($new_frame)?;
            };
        }

        macro_rules! binary_op {
            ($op:tt) => {binary_op!(bail!("Operands must be numbers."), $op)};
            ($err:expr, $op:tt) => {
                match (self.peek(1).as_f64(), self.peek(0).as_f64()) {
                    (Some(a), Some(b)) => { self.pop(); self.pop(); self.push(a $op b); }
                    _ => { $err; }
                }
            };
        }

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
                    self.stack.get_local(frame.stack_offset, slot);
                }
                OpCode::SetLocal => {
                    let slot = read_byte!();
                    self.stack.set_local(frame.stack_offset, slot);
                }
                OpCode::GetGlobal => {
                    let name = read_constant!().as_object().unwrap();
                    let v = self
                        .globals
                        .get_value(name)
                        .with_context(|| format!("Undefined variable '{}'.", name))?;
                    self.push(v);
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
                        bail!("Undefined variable '{}'.", name);
                    }
                }
                OpCode::GetUpvalue => {
                    let slot = read_byte!();
                    self.push(unsafe { frame.closure.as_ref() }.read_upvalue(slot));
                }
                OpCode::SetUpvalue => {
                    let slot = read_byte!();
                    let value = self.peek(0);
                    unsafe { frame.closure.as_ref() }.write_upvalue(slot, value);
                }
                OpCode::GetProperty => {
                    let instance = self
                        .peek(0)
                        .as_object::<Instance>()
                        .with_context(|| format!("Only instances have properties."))?;
                    let name = read_constant!().as_object().unwrap();
                    if let Some(value) = instance.get_field(name) {
                        self.pop(); // instance
                        self.push(value);
                    } else {
                        self.bind_method(instance.get_class(), name)?;
                    }
                }
                OpCode::SetProperty => {
                    self.peek_obj::<Instance>(1)
                        .with_context(|| format!("Only instances have fields."))?
                        .set_field(read_constant!().as_object().unwrap(), self.peek(0));
                    let value = self.pop();
                    self.pop();
                    self.push(value);
                }
                OpCode::GetSuper => {
                    let name = read_string!();
                    let superclass = self.pop().as_object().unwrap();
                    self.bind_method(superclass, name)?;
                }
                OpCode::Equal => {
                    let a = self.pop();
                    let b = self.pop();
                    self.push(a == b);
                }
                OpCode::Greater => binary_op!(>),
                OpCode::Less => binary_op!(<),
                OpCode::Add => binary_op!({
                    if let (Some(a), Some(b)) = (self.peek(1).as_str(), self.peek(0).as_str()) {
                        let new = [a, b].join("");
                        let s: *const _ = self.heap.new_string(new);
                        self.pop();
                        self.pop();
                        self.push(s);
                    } else {
                        bail!("Operands must be two numbers or two strings.");
                    }}, +),

                OpCode::Subtract => binary_op!(-),
                OpCode::Multiply => binary_op!(*),
                OpCode::Divide => binary_op!(/),
                OpCode::Not => {
                    let neg = self.pop().is_falsey();
                    self.push(neg)
                }
                OpCode::Negate => {
                    if let Some(x) = self.peek(0).as_f64() {
                        self.pop();
                        self.push(-x);
                    } else {
                        bail!("Operand must be a number.");
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
                    let callee = self.peek(arg_count);
                    if let Some(new_frame) = self.call_value(callee, arg_count)? {
                        push_callframe!(new_frame);
                    }
                }
                OpCode::Invoke => {
                    // Ch 28.5
                    let method = read_string!();
                    let arg_cnt = read_byte!();
                    if let Some(new_frame) = self.invoke(method, arg_cnt)? {
                        push_callframe!(new_frame);
                    }
                }
                OpCode::SuperInvoke => {
                    let method = read_string!();
                    let arg_cnt = read_byte!();
                    let superclass = self.pop().as_object().unwrap();
                    let new_frame = self.invoke_from_class(superclass, method, arg_cnt)?;
                    push_callframe!(new_frame);
                }
                OpCode::Closure => {
                    let function = read_constant!().as_object::<Function>().unwrap();
                    let closure = Closure::new(function.into(), &mut || {
                        let is_local = read_byte!() == 1;
                        let index = read_byte!() as usize;
                        if is_local {
                            self.capture_upvalue(unsafe { frame.stack_offset.add(index) })
                        } else {
                            unsafe { frame.closure.as_ref() }.upvalues[index]
                        }
                    });
                    let closure = self.heap.new_object(closure);
                    self.push(closure as *const _);
                }
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.slot_ptr(0));
                    self.pop();
                }
                OpCode::Return => {
                    // Ch 24.5.4
                    let result = self.pop();
                    self.close_upvalues(frame.stack_offset);
                    self.stack.truncate(frame.stack_offset);
                    if let Some(outer_frame) = call_stack.pop_frame() {
                        self.push(result);
                        frame = outer_frame;
                    } else {
                        return Ok(());
                    }
                }
                OpCode::Class => {
                    let name = read_constant!().as_object().unwrap();
                    let cls = self.heap.new_object(Class::new(name));
                    self.push(cls as *const _);
                }
                OpCode::Inherit => {
                    let superclass = self
                        .peek_obj::<Class>(1)
                        .context("Superclass must be a class.")?;
                    let subclass: &Obj<Class> = self.peek_obj(0).unwrap();
                    subclass.inherit(superclass);
                    self.pop(); // subclass
                }
                OpCode::Method => {
                    self.define_method(read_string!());
                }

                OpCode::BadOpCode => {
                    frame.disassemble();
                    Err(anyhow!("Encountered invalid OpCode {}", op as u8))?;
                }
            }
        }
    }

    fn print_stack(&self, hdr: &str) {
        println!("Stack dump: {}\n{:?}", hdr, self.stack);
    }

    fn capture_upvalue(&mut self, stack_ptr: *mut Value) -> ObjPtr<Upvalue> {
        let mut uv_ptr = self.open_upvalues;
        let mut prev_ptr = None;
        // check if we already have an open upvalue for this stack slot
        while let Some(uv) = uv_ptr {
            if uv.get_val_ptr() < stack_ptr {
                break;
            }
            if uv.get_val_ptr() == stack_ptr {
                return uv;
            }
            prev_ptr = uv_ptr;
            uv_ptr = uv.get_next_open();
        }
        let upvalue = Upvalue::new(stack_ptr);
        upvalue.set_next_open(uv_ptr);
        let upvalue: ObjPtr<Upvalue> = self.heap.new_object(upvalue).into();

        if let Some(prev_ptr) = prev_ptr {
            prev_ptr.set_next_open(Some(upvalue));
        } else {
            self.open_upvalues = Some(upvalue);
        }
        upvalue
    }

    fn close_upvalues(&mut self, last: *mut Value) {
        // Ch 25.4.4
        while let Some(uv) = self.open_upvalues.as_ref() {
            if uv.get_val_ptr() < last {
                break;
            }
            Upvalue::close(uv.as_ref());
            self.open_upvalues = uv.get_next_open();
        }
    }

    fn define_method(&mut self, name: &Obj<LoxStr>) {
        let method = self.peek(0);
        self.peek(1)
            .as_object::<Class>()
            .unwrap()
            .add_method(name, method);
        self.pop();
    }

    fn call_value(&mut self, callee: Value, arg_count: u8) -> Result<Option<CallFrame>> {
        if let Some(closure) = callee.as_object() {
            self.call(closure, arg_count).map(Some)
        } else if let Some(bound) = callee.as_object::<BoundMethod>() {
            self.stack.set_slot(arg_count, bound.receiver);
            self.call(bound.get_closure(), arg_count).map(Some)
        } else if let Some(class) = callee.as_object() {
            let instance = Instance::new(class);
            let o = self.heap.new_object(instance);
            self.stack.set_slot(arg_count, o.into());
            if let Some(init) = class.get_method(unsafe { &*self.init_string }) {
                self.call(init, arg_count).map(Some)
            } else if arg_count != 0 {
                bail!("Expected 0 arguments but got {}.", arg_count)
            } else {
                Ok(None)
            }
        } else if let Some(native) = callee.as_object::<NativeFn>() {
            let result = native.call_native(self.stack.slice_top(arg_count))?;
            self.stack.remove_cnt(arg_count + 1);
            self.push(result);
            Ok(None)
        } else {
            bail!("Can only call functions and classes.")
        }
    }

    fn invoke(&mut self, name: &Obj<LoxStr>, arg_cnt: u8) -> Result<Option<CallFrame>> {
        let instance = self
            .peek_obj::<Instance>(arg_cnt)
            .context("Only instances have methods.")?;

        if let Some(field) = instance.get_field(name) {
            self.stack.set_slot(arg_cnt, field);
            self.call_value(field, arg_cnt)
        } else {
            let class: *const _ = instance.get_class();
            self.invoke_from_class(unsafe { &*class }, name, arg_cnt)
                .map(Some)
        }
    }

    fn invoke_from_class(
        &mut self,
        class: &Obj<Class>,
        name: &Obj<LoxStr>,
        arg_cnt: u8,
    ) -> Result<CallFrame> {
        if let Some(method) = class.get_method(name) {
            self.call(method, arg_cnt)
        } else {
            bail!("Undefined property '{}'.", name)
        }
    }

    fn bind_method(&mut self, class: &Obj<Class>, name: &Obj<LoxStr>) -> Result<()> {
        let method = class
            .get_method(name)
            .with_context(|| format!("Undefined property '{}'.", name))?;
        let bound = self.heap.new_object(BoundMethod::new(self.peek(0), method));
        self.pop();
        self.push(bound);
        Ok(())
    }

    fn call(&self, closure: &Obj<Closure>, arg_count: u8) -> Result<CallFrame> {
        if arg_count != closure.function().arity {
            bail!(
                "Expected {} arguments but got {}.",
                closure.function().arity,
                arg_count
            );
        }

        let frame = CallFrame {
            closure: closure.into(),
            ip: closure.function().chunk.code.as_ptr(),
            stack_offset: self.stack.slot_ptr(arg_count),
        };
        // frame.disassemble();
        Ok(frame)
    }

    fn define_native(&mut self, name: &str, function: NativeFnRef) {
        let name = self.heap.new_string(name.to_string());
        self.stack.push(name.into());
        let native = self.heap.new_object::<NativeFn>(function.into());
        self.stack.push(native.into());
        self.globals.set(name, native.into());
        self.pop();
        self.pop();
    }

    fn push(&mut self, val: impl Into<Value>) {
        self.stack.push(val.into())
    }

    fn peek(&self, pos: u8) -> Value {
        self.stack.peek(pos)
    }

    fn peek_obj<O: LoxObject + 'static>(&self, pos: u8) -> Option<&Obj<O>> {
        self.peek(pos).as_object::<O>()
    }

    fn pop(&mut self) -> Value {
        self.stack.pop()
    }
}

impl HasRoots for Vm<'_> {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for val in self.stack.iter() {
            val.mark(mark_obj);
        }
        self.globals.mark_roots(mark_obj);
        let mut uv_ptr = self.open_upvalues;
        while let Some(uv) = uv_ptr.as_ref().map(|x| x.as_ref()) {
            uv.mark(mark_obj);
            uv_ptr = uv.get_next_open();
        }
        if !self.init_string.is_null() {
            unsafe { &*self.init_string }.mark(mark_obj);
        }
    }
}

mod natives {
    use std::sync::OnceLock;

    use super::{Result, Value};

    pub fn clock(_args: &[Value]) -> Result<Value> {
        static START_TIME: OnceLock<std::time::Instant> = OnceLock::new();
        Ok(START_TIME
            .get_or_init(std::time::Instant::now)
            .elapsed()
            .as_secs_f64()
            .into())
    }
}

#[test]
fn test_interpret() {
    let heap = Heap::new();
    let mut vm = Vm::new(&heap);
    for _ in 0..100 {
        vm.interpret("var x=0;").unwrap();
    }
}

#[test]
fn test_compile_run() {
    let heap = Heap::new();
    let mut vm = Vm::new(&heap);
    let mut runner = vm.compile("var x=0;").unwrap();
    for _ in 0..1000 {
        runner.run().unwrap();
    }
}
