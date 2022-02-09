use anyhow::{bail, Context, Result};

use crate::clox::mm::Obj;
use crate::clox::Chunk;

use std::any::Any;
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

    pub fn as_str(&self) -> Result<&str> {
        self.as_object::<LoxStr>()
            .map(|o| o.as_str())
            .context("Not a string.")
    }

    pub fn as_loxstr(&self) -> Option<&Obj<LoxStr>> {
        self.as_object()
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
    }

    pub fn as_object<O: Display + Debug + 'static>(&self) -> Option<&Obj<O>> {
        if let Self::Obj(ptr) = self {
            ptr.cast::<O>()
        } else {
            None
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
    pub(crate) next_open_upvalue: *mut Obj<Upvalue>,
    closed: Value,
}

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

impl Display for Upvalue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "upvalue")
    }
}

#[derive(Debug)]
pub struct Closure {
    pub function: *const Obj<Function>,
    pub upvalues: Box<[*const Obj<Upvalue>]>,
}

impl Closure {
    pub fn new(function: *const Obj<Function>) -> Self {
        Self {
            function,
            upvalues: vec![
                ptr::null();
                unsafe { function.as_ref().unwrap() }.upvalue_count as usize
            ]
            .into_boxed_slice(),
        }
    }

    pub fn function(&self) -> &'static Function {
        unsafe { self.function.as_ref().unwrap() }
    }

    pub fn read_upvalue(&self, slot: u8) -> Value {
        let slot = self.upvalues[slot as usize];
        unsafe { slot.as_ref().unwrap().read() }
    }

    pub fn write_upvalue(&self, slot: u8, value: Value) {
        let slot = self.upvalues[slot as usize];
        unsafe {
            slot.as_ref().unwrap().write(value);
        }
    }
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.function())
    }
}

#[derive(Debug)]
pub struct Function {
    pub(crate) arity: u8,
    pub(crate) chunk: Chunk,
    pub(crate) name: *const Obj<LoxStr>,
    pub(crate) upvalue_count: usize,
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

impl NativeFn {
    pub fn call_native(&self, args: &[Value]) -> Result<Value> {
        self.0(args)
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

#[derive(Clone, Copy, PartialEq)]
pub enum ObjTypes {
    Closure(NonNull<Obj<Closure>>),
    Function(NonNull<Obj<Function>>),
    NativeFn(NonNull<Obj<NativeFn>>),
    LoxStr(NonNull<Obj<LoxStr>>),
    Upvalue(NonNull<Obj<Upvalue>>),
    None,
}

macro_rules! objtypes_impl {
    ($($typ:ident),+) => { $(
        impl From<*const Obj<$typ>> for ObjTypes {
            fn from(f: *const Obj<$typ>) -> Self {
                Self::$typ(NonNull::new(f as *mut _).unwrap())
            }
        }
        )+

        macro_rules! for_all_objtypes {
            ($self:ident, $mac:ident) => {{
                match $self {
                    $( ObjTypes::$typ(p) => $mac!(p), )+
                    ObjTypes::None => unreachable!("Should have been handled above."),
                }
            }}
        }
    }
}

objtypes_impl!(Closure, Function, NativeFn, LoxStr, Upvalue);

impl ObjTypes {
    pub(crate) fn free_object(self) -> Self {
        macro_rules! free_next {
            ($ptr:expr) => {
                unsafe { Box::from_raw($ptr.as_ptr()) }.next
            };
        }
        if self == ObjTypes::None {
            return self;
        }
        for_all_objtypes!(self, free_next)
    }

    fn cast<'a, T: Display + Debug + 'static>(self) -> Option<&'a Obj<T>> {
        macro_rules! down {
            ($ptr:expr) => {
                return (unsafe { $ptr.as_ref() } as &dyn Any).downcast_ref()
            };
        }
        if self == ObjTypes::None {
            return None;
        }
        for_all_objtypes!(self, down)
    }
}

impl Debug for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($p:expr) => {
                write!(f, "{:?}->{:?}", $p, unsafe { $p.as_ref() })
            };
        }
        if self == &Self::None {
            return write!(f, "ObjTypes::None");
        }
        for_all_objtypes!(self, w)
    }
}

impl Display for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($ptr:expr) => {
                write!(f, "{}", unsafe { $ptr.as_ref() })
            };
        }
        if self == &ObjTypes::None {
            return Ok(());
        }
        for_all_objtypes!(self, w)
    }
}
