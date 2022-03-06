use anyhow::{bail, Result};
use std::cell::{RefCell, UnsafeCell};

use crate::clox::mm::{HasRoots, Obj, ObjTypes};
use crate::clox::table::{LoxTable, Table};
use crate::clox::Chunk;

use std::fmt::{Debug, Display, Formatter};
use std::ptr;
use std::ptr::NonNull;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    Nil,
    Number(f64),
    Obj(ObjTypes),
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{:?}", b),
            Value::Nil => write!(f, "nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Obj(o) => write!(f, "{}", o),
        }
    }
}

impl Value {
    pub fn as_f64(self) -> Result<f64> {
        match self {
            Self::Number(f) => Ok(f),
            _ => bail!("Not a number."),
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        self.as_object::<LoxStr>().map(|o| o.as_str())
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
    }

    pub fn as_object<'a, O: LoxObject + 'static>(self) -> Option<&'a Obj<O>> {
        if let Self::Obj(ptr) = self {
            ptr.cast::<O>()
        } else {
            None
        }
    }

    pub(crate) fn mark(&self, callback: &mut dyn FnMut(ObjTypes)) {
        if let Self::Obj(obj) = self {
            obj.mark(callback);
        }
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Self::Number(f)
    }
}

impl<O: Into<ObjTypes>> From<O> for Value {
    fn from(ptr: O) -> Self {
        Self::Obj(ptr.into())
    }
}

pub trait LoxObject: Debug + Display + HasRoots {}

#[derive(Debug, Clone)]
pub struct LoxStr {
    s: Box<str>,
    pub(crate) hash: u32,
}

impl LoxStr {
    pub fn as_str(&self) -> &str {
        &self.s
    }

    pub fn from_str(s: &str) -> Self {
        Self::from_string(s.to_owned())
    }

    pub fn from_string(s: String) -> Self {
        Self {
            hash: Self::hash(s.as_str()),
            s: s.into_boxed_str(),
        }
    }

    /// FNV-1a
    pub(crate) fn hash(s: &str) -> u32 {
        let mut hash = 2166136261;
        for b in s.bytes() {
            hash ^= b as u32;
            hash = hash.wrapping_mul(16777619);
        }
        hash
    }
}

impl LoxObject for LoxStr {}

impl HasRoots for LoxStr {
    fn mark_roots(&self, _mark_obj: &mut dyn FnMut(ObjTypes)) {
        // no roots
    }
}

impl PartialEq for LoxStr {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(&*self.s, &*other.s) // This assumes that LoxStr is interned
    }
}

impl PartialEq<(&str, u32)> for &LoxStr {
    fn eq(&self, other: &(&str, u32)) -> bool {
        self.hash == other.1 && &*self.s == other.0
    }
}

impl From<String> for LoxStr {
    fn from(s: String) -> Self {
        Self::from_string(s)
    }
}

impl Display for LoxStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.s)
    }
}

#[derive(Debug)]
pub struct Upvalue {
    // TODO: Pointing into the stack is op as long as it doesn't reallocate, which it shouldn't
    // since it is pre-allocated in Vm::new(). Consider using a boxed slice instead for the stack.
    pub(crate) location: *mut Value,
    pub(crate) next_open_upvalue: *const Obj<Upvalue>,
    closed: Value,
}

impl LoxObject for Upvalue {}

impl Upvalue {
    pub fn new(location: *mut Value) -> Self {
        Self {
            location,
            next_open_upvalue: ptr::null_mut(),
            closed: Value::Nil,
        }
    }

    /// SAFETY: Upvalue must not move in memory after close() is called.
    pub unsafe fn close(&mut self) {
        self.closed = *self.location;
        self.location = &mut self.closed as *mut _;
    }

    pub fn read(&self) -> Value {
        unsafe { *self.location.as_ref().unwrap() }
    }

    pub fn write(&self, value: Value) {
        unsafe {
            *self.location.as_mut().unwrap() = value;
        }
    }
}

impl HasRoots for Upvalue {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.closed.mark(mark_obj);
    }
}

impl Display for Upvalue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "upvalue")
    }
}

#[derive(Debug)]
pub struct Closure {
    pub function: NonNull<Obj<Function>>,
    pub upvalues: Box<[NonNull<Obj<Upvalue>>]>,
}

impl LoxObject for Closure {}

impl Closure {
    pub fn new(
        function: NonNull<Obj<Function>>,
        uvg: &mut dyn FnMut() -> NonNull<Obj<Upvalue>>,
    ) -> Self {
        let mut upvalues = vec![];
        upvalues.resize_with(unsafe { function.as_ref().upvalue_count }, uvg);
        Self {
            function,
            upvalues: upvalues.into_boxed_slice(),
        }
    }

    pub fn function(&self) -> &Function {
        unsafe { self.function.as_ref() }
    }

    pub fn read_upvalue(&self, slot: u8) -> Value {
        let slot = self.upvalues[slot as usize];
        unsafe { slot.as_ref().read() }
    }

    pub fn write_upvalue(&self, slot: u8, value: Value) {
        let slot = self.upvalues[slot as usize];
        unsafe {
            slot.as_ref().write(value);
        }
    }
}

impl HasRoots for Closure {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        unsafe { self.function.as_ref() }.mark(mark_obj);
        for uv in self.upvalues.iter() {
            let uv = unsafe { uv.as_ref() };
            uv.mark(mark_obj);
        }
    }
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.function())
    }
}

#[derive(Debug)]
pub struct Class {
    name: *const Obj<LoxStr>,
    methods: UnsafeCell<LoxTable>,
}

impl LoxObject for Class {}

impl Class {
    pub(crate) fn new(name: &Obj<LoxStr>) -> Self {
        Self {
            name,
            methods: LoxTable::new().into(),
        }
    }

    pub(crate) fn inherit(&self, superclass: &Obj<Class>) {
        let (sub, sup) = (self.methods.get(), superclass.methods.get());
        assert!(!ptr::eq(sub, sup));
        // This is safe as long as we don't inherit from ourselves.
        unsafe { &mut *sub }.add_all(unsafe { &*sup });
    }

    pub(crate) fn add_method(&self, name: &Obj<LoxStr>, method: Value) {
        unsafe { &mut *self.methods.get() }.set(name, method);
    }

    pub(crate) fn get_method(&self, name: &Obj<LoxStr>) -> Option<&Obj<Closure>> {
        let method = unsafe { &*self.methods.get() }.get_value(name)?;
        Some(unsafe { &*(method.as_object().unwrap() as *const _) })
    }
}

impl Display for Class {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", unsafe { &*self.name })
    }
}

impl HasRoots for Class {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        mark_obj(self.name.into());
        unsafe { &*self.methods.get() }.mark_roots(mark_obj);
    }
}

#[derive(Debug)]
pub struct Instance {
    class: NonNull<Obj<Class>>,
    fields: RefCell<LoxTable>,
}

impl LoxObject for Instance {}

impl Instance {
    pub(crate) fn new(class: &Obj<Class>) -> Self {
        Self {
            class: class.into(),
            fields: LoxTable::new().into(),
        }
    }

    pub(crate) fn get_class(&self) -> &Obj<Class> {
        unsafe { self.class.as_ref() }
    }

    pub(crate) fn get_field(&self, field: &Obj<LoxStr>) -> Option<Value> {
        self.fields.borrow().get_value(field)
    }

    pub(crate) fn set_field(&self, field: &Obj<LoxStr>, value: Value) {
        self.fields.borrow_mut().set(field, value);
    }
}

impl Display for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} instance", unsafe { self.class.as_ref() })
    }
}

impl HasRoots for Instance {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        mark_obj(self.class.into());
        self.fields.borrow().mark_roots(mark_obj);
    }
}

#[derive(Debug)]
pub struct BoundMethod {
    pub(crate) receiver: Value,
    method: NonNull<Obj<Closure>>,
}

impl LoxObject for BoundMethod {}

impl BoundMethod {
    pub(crate) fn new(receiver: Value, method: &Obj<Closure>) -> Self {
        Self {
            receiver,
            method: method.into(),
        }
    }

    pub(crate) fn get_closure(&self) -> &Obj<Closure> {
        unsafe { self.method.as_ref() }
    }
}

impl Display for BoundMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", unsafe { self.method.as_ref() })
    }
}

impl HasRoots for BoundMethod {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.receiver.mark(mark_obj);
        unsafe { self.method.as_ref() }.mark(mark_obj);
    }
}

#[derive(Debug)]
pub struct Function {
    pub(crate) arity: u8,
    pub(crate) chunk: Chunk,
    pub(crate) name: *const Obj<LoxStr>,
    pub(crate) upvalue_count: usize,
}

impl LoxObject for Function {}

impl HasRoots for Function {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for v in self.chunk.constants.iter() {
            v.mark(mark_obj);
        }
        if let Some(name) = unsafe { self.name.as_ref() } {
            name.mark(mark_obj);
        }
    }
}

impl Function {
    pub fn new() -> Self {
        Self {
            arity: 0,
            chunk: Chunk::new(),
            name: ptr::null(),
            upvalue_count: 0,
        }
    }

    pub fn name(&self) -> &str {
        unsafe { self.name.as_ref() }
            .map(|ls| ls.as_str())
            .unwrap_or("<script>")
    }

    pub fn disassemble(&self) {
        self.chunk.disassemble(self.name());
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<fn {}>",
            unsafe { self.name.as_ref() }
                .map(|s| s.as_str())
                .unwrap_or("<script>")
        )
    }
}

pub type NativeFnRef = fn(&[Value]) -> Result<Value>;

pub struct NativeFn(NativeFnRef);

impl LoxObject for NativeFn {}

impl NativeFn {
    pub fn call_native(&self, args: &[Value]) -> Result<Value> {
        self.0(args)
    }
}

impl HasRoots for NativeFn {
    fn mark_roots(&self, _mark_obj: &mut dyn FnMut(ObjTypes)) {
        // no roots
    }
}
impl Display for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn>")
    }
}

impl Debug for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "NativeFn({:?})", (&self.0) as *const _)
    }
}

impl From<NativeFnRef> for NativeFn {
    fn from(f: NativeFnRef) -> Self {
        Self(f)
    }
}
