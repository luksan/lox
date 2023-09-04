use core::fmt;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::{iter, ptr};

use anyhow::{anyhow, bail, Context, Result};
use miette::{Diagnostic, LabeledSpan, SourceCode, SourceSpan};
use tracing::{span, Level};

use crate::clox::compiler::{compile, CompilerError};
use crate::clox::mm::{HasRoots, Heap, Obj, ObjMarker, ObjPtr, ObjTypes};
use crate::clox::stack::{Stack, FRAMES_MAX};
use crate::clox::table::{LoxTable, Table};
use crate::clox::value::{
    BoundMethod, Class, Closure, Function, Instance, LoxObject, LoxStr, NativeFn, NativeFnRef,
    Upvalue, Value,
};
use crate::clox::{Chunk, OpCode};
use crate::scanner::TokSpan;
use crate::ErrorKind;

#[derive(Debug, Diagnostic)]
pub enum VmError {
    Compile(#[related] Vec<CompilerError>),
    #[diagnostic(transparent)]
    Runtime(RuntimeError),
}

impl VmError {
    fn runtime(line: isize, err: anyhow::Error, stacktrace: StackTrace) -> Self {
        Self::Runtime(RuntimeError {
            line,
            err,
            stacktrace,
        })
    }

    pub fn kind(&self) -> ErrorKind {
        match self {
            VmError::Compile(_) => ErrorKind::CompilationError,
            VmError::Runtime(_) => ErrorKind::RuntimeError,
        }
    }
}

impl Error for VmError {}

impl Display for VmError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VmError::Compile(errors) => {
                for e in &errors[0..errors.len() - 1] {
                    writeln!(f, "{e}")?;
                }
                write!(f, "{}", errors.last().unwrap())
            }
            VmError::Runtime(err) => write!(f, "{err}"),
        }
    }
}

impl From<Vec<CompilerError>> for VmError {
    fn from(value: Vec<CompilerError>) -> Self {
        Self::Compile(value)
    }
}

type StackTrace = Vec<(String, TokSpan)>;

#[derive(Debug)]
pub struct RuntimeError {
    line: isize,
    stacktrace: Vec<(String, TokSpan)>,
    err: anyhow::Error,
}

impl RuntimeError {
    pub fn fmt_stacktrace(&self, source: &dyn SourceCode, f: &mut dyn fmt::Write) {
        for (func, span) in self.stacktrace.iter().rev() {
            let span: SourceSpan = span.into();
            let span_contents = source.read_span(&span, 1, 1).unwrap();
            let line = span_contents.line() + 1;
            let skip: usize = (line > 1) as _;
            let data = std::str::from_utf8(span_contents.data())
                .unwrap()
                .split('\n')
                .nth(skip)
                .unwrap();
            writeln!(f, "[line {line} in {func}] {data}").unwrap();
        }
    }
}
impl Error for RuntimeError {}
impl Display for RuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}\n[line {}] in script", self.err, self.line)
    }
}

impl miette::Diagnostic for RuntimeError {
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        Some(Box::new(iter::once(
            self.stacktrace
                .last()
                .map(|span| LabeledSpan::new_with_span(Some(self.err.to_string()), &span.1))
                .unwrap(),
        )))
    }
}

#[test]
fn test_vm_miette_error() {
    use crate::clox::{CloxSettings, SETTINGS};
    let heap = Heap::new();
    let mut vm = Vm::new(&heap);
    if false {
        SETTINGS
            .set(CloxSettings {
                output_ci_compliant: false,
                trace_execution: false,
                disassemble_compiler_output: false,
                gc_stress_test: false,
            })
            .unwrap();
    }
    let source = "
var x = 3;
fun bar(x) { r = 4; }
class Base {
    foo() { this.nope(2); }
    bar() { var x = this.nein; }
}
class Derived < Base {
    dfoo() { super.nope(33); }
    dbar() { var x = super.oops; }
}
var b = Base();
var d = Derived();
// d.dbar();
// b.foo();
// b.bar();
// bar(x,x);
// if( \"123\" >= 3 ){ print \"hej\"; }
// print x.prop;
// bar(1);
// y = 4;
123.foo;
// 1234.foo = 123 + 2133;
";
    let _e = vm.interpret(source).unwrap_err();
    // eprintln!("{:?}", miette::Report::new(_e).with_source_code(source))
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
    closure: ObjPtr<Closure>,
    ip: *const u8,
    stack_offset: *mut Value,
}

impl CallFrame {
    fn new(closure: ObjPtr<Closure>, stack_offset: *mut Value) -> Self {
        let ip = closure.as_ref().function().chunk.code.as_ptr();
        Self {
            closure,
            ip,
            stack_offset,
        }
    }

    fn disassemble(&self) {
        let closure = self.closure.as_ref();
        closure
            .function()
            .chunk
            .disassemble(closure.function().name());
    }

    fn func_name(&self) -> String {
        let called_value = unsafe { *self.stack_offset };
        let func_name = self.closure().function().name();
        if let Some(method) = called_value.as_object::<Instance>() {
            format!("{}::{}", method.get_class(), func_name)
        } else {
            func_name.to_string()
        }
    }

    fn chunk(&self) -> &Chunk {
        &self.closure.as_ref().function().chunk
    }

    fn closure(&self) -> &Obj<Closure> {
        self.closure.as_ref()
    }

    fn current_line(&self) -> isize {
        let idx = unsafe { self.ip.offset_from(self.chunk().code.as_ptr()) } - 1;
        self.chunk().line_at_idx(idx) as isize
    }

    fn current_span(&self) -> TokSpan {
        let idx = unsafe { self.ip.offset_from(self.chunk().code.as_ptr()) } - 1;
        self.chunk().span(idx)
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

    fn stacktrace(&self) -> StackTrace {
        self.0
            .iter()
            .map(|frame| (frame.func_name(), frame.current_span()))
            .collect()
    }
}

impl HasRoots for CallStack {
    fn mark_roots(&self, mark_obj: &mut ObjMarker) {
        for frame in self.0.iter() {
            frame.closure().mark(mark_obj);
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
        self.vm.push(self.frame.closure());
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

    pub fn interpret(&mut self, source: &str) -> miette::Result<(), VmError> {
        self.compile(source)?.run()
    }

    pub fn compile(&mut self, source: &str) -> Result<Runnable<'_, 'heap>, VmError> {
        let _token = self.heap.register_gc_root(self);
        let function = compile(source, self.heap)?;
        self.push(ObjTypes::from(function));
        drop(_token);
        let _token = self.heap.register_gc_root(self);
        let closure = self.heap.new_object(Closure::new(function, &mut || {
            unreachable!("No upvalues in root.")
        }));
        self.pop();
        self.push(closure as *const _);
        let frame = self.call(closure, 0).unwrap(); // this can't fail since the only failure mode of call() is argument count mismatch
        Ok(Runnable { vm: self, frame })
    }

    fn run(&mut self, frame: &CallFrame) -> Result<(), VmError> {
        let trace_span = span!(Level::TRACE, "Vm::run()");
        let _enter = trace_span.enter();

        let _token = self.heap.register_gc_root(self);

        let call_stack = &mut CallStack::new();
        let _token = self.heap.register_gc_root(call_stack);

        call_stack.push_frame(frame.clone()).unwrap();
        self.run_inner(call_stack).map_err(|err| {
            // for slot in self.stack.iter().rev() { println!("{:#?}", slot); }
            VmError::runtime(
                call_stack.current_frame().current_line(),
                err,
                call_stack.stacktrace(),
            )
        })
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
            () => {{
                let idx = read_byte!();
                frame.chunk().constants[idx]
            }};
        }
        macro_rules! read_string {
            () => {{
                let val = read_constant!();
                #[cfg(not(debug_assertions))]
                unsafe {
                    val.as_object_unchecked::<LoxStr>()
                }
                #[cfg(debug_assertions)]
                val.as_object::<LoxStr>().unwrap()
            }};
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
            let op = if cfg!(debug_assertions) {
                instr.into() // use FromPrimitive
            } else {
                unsafe { std::mem::transmute(instr) }
            };
            match op {
                OpCode::Constant => self.stack.push(read_constant!()),
                OpCode::Nil => self.push(Value::Nil),
                OpCode::True => self.push(Value::Bool(true)),
                OpCode::False => self.push(Value::Bool(false)),
                OpCode::Pop => {
                    self.stack.remove_cnt(1);
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
                    let name = read_string!();
                    let v = self
                        .globals
                        .get_value(name)
                        .with_context(|| format!("Undefined variable '{}'.", name))?;
                    self.push(v);
                }
                OpCode::DefineGlobal => {
                    let name = read_string!();
                    self.globals.set(name, self.peek(0));
                    self.pop();
                }
                OpCode::SetGlobal => {
                    let name = read_string!();
                    if self.globals.set(name, self.peek(0)) {
                        self.globals.delete(name);
                        bail!("Undefined variable '{}'.", name);
                    }
                }
                OpCode::GetUpvalue => {
                    let slot = read_byte!();
                    self.push(frame.closure().read_upvalue(slot));
                }
                OpCode::SetUpvalue => {
                    let slot = read_byte!();
                    let value = self.peek(0);
                    frame.closure().write_upvalue(slot, value);
                }
                OpCode::GetProperty => {
                    let instance = self
                        .peek(0)
                        .as_object::<Instance>()
                        .with_context(|| format!("Only instances have properties."))?;
                    let name = read_string!();
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
                        .set_field(read_string!(), self.peek(0));
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
                            frame.closure().upvalues[index]
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
                    let name = read_string!();
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

        let frame = CallFrame::new(closure.into(), self.stack.slot_ptr(arg_count));
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
    fn mark_roots(&self, mark_obj: &mut ObjMarker) {
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
