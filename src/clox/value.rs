use anyhow::{bail, Context, Result};

use crate::clox::Chunk;
use std::any::Any;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;
use std::ptr;
use std::ptr::NonNull;

use crate::clox::table::StrPtr;

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

    pub fn as_function(self) -> Result<&'static Object<Function>> {
        self.as_object().context("Not a function.")
    }

    pub fn as_str(&self) -> Result<&str> {
        self.as_object::<LoxStr>()
            .map(|o| o.as_str())
            .context("Not a string.")
    }

    pub fn as_loxstr(self) -> Option<&'static Object<LoxStr>> {
        self.as_object()
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
    }

    fn as_object<O: Display + Debug>(&self) -> Option<&'static Object<O>> {
        if let Self::Obj(ptr) = self {
            ptr.cast()
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
pub struct Function {
    arity: u8,
    pub(crate) chunk: Chunk,
    name: *const Object<LoxStr>,
}

impl Function {
    pub fn new() -> Self {
        Self {
            arity: 0,
            chunk: Chunk::new(),
            name: ptr::null(),
        }
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

pub struct Object<T: ?Sized + Display + Debug> {
    pub(crate) next: ObjTypes,
    inner: T,
}

impl<T: Display + Debug + ?Sized> Deref for Object<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Display + Debug> Debug for Object<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Object{{ inner: {:?}, next: ... }}", self.inner)
    }
}

impl<T: Display + Debug> Display for Object<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<T: Display + Debug> Object<T> {
    pub fn new<S: Into<T>>(from: S) -> &'static mut Self {
        Box::leak(Box::new(Object {
            next: ObjTypes::None,
            inner: from.into(),
        }))
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum ObjTypes {
    Function(NonNull<Object<Function>>),
    String(NonNull<Object<LoxStr>>),
    None,
}

impl ObjTypes {
    pub(crate) fn free_object(self) -> Self {
        macro_rules! free_next {
            ($ptr:expr) => {
                unsafe { Box::from_raw($ptr.as_ptr()) }.next
            };
        }
        match self {
            ObjTypes::Function(f) => free_next!(f),
            ObjTypes::String(s) => free_next!(s),
            ObjTypes::None => return self,
        }
    }

    fn cast<T: Display + Debug>(self) -> Option<&'static Object<T>> {
        macro_rules! down {
            ($ptr:expr) => {
                return (unsafe { $ptr.as_ref() } as &dyn Any).downcast_ref()
            };
        }
        match self {
            ObjTypes::Function(f) => down!(f),
            ObjTypes::String(s) => down!(s),
            ObjTypes::None => {}
        }
        None
    }
}

impl Debug for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($ptr:expr) => {
                write!(f, "{:?}->{:?}", $ptr, unsafe { $ptr.as_ref() })
            };
        }
        match self {
            ObjTypes::Function(fun) => w!(fun),
            ObjTypes::String(s) => w!(s),
            ObjTypes::None => write!(f, "None"),
        }
    }
}

impl Display for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($ptr:expr) => {
                write!(f, "{}", unsafe { $ptr.as_ref() })
            };
        }
        match self {
            ObjTypes::Function(fun) => w!(fun),
            ObjTypes::String(s) => w!(s),
            ObjTypes::None => unreachable!(),
        }
    }
}

impl From<StrPtr> for ObjTypes {
    fn from(s: StrPtr) -> Self {
        Self::String(NonNull::new(s as *mut _).unwrap())
    }
}

impl From<*const Object<Function>> for ObjTypes {
    fn from(s: *const Object<Function>) -> Self {
        Self::Function(NonNull::new(s as *mut _).unwrap())
    }
}
