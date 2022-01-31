use anyhow::{bail, Result};

use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, Index};
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

#[derive(Debug, Clone, PartialEq)]
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
    fn hash(s: &str) -> u32 {
        let mut hash = 2166136261;
        for b in s.bytes() {
            hash ^= b as u32;
            hash = hash.wrapping_mul(16777619);
        }
        hash
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

pub struct Object<T: ?Sized + Display + Debug> {
    next: ObjTypes,
    inner: T,
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

    fn next(&self) -> ObjTypes {
        self.next
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum ObjTypes {
    String(NonNull<Object<LoxStr>>),
    None,
}

impl ObjTypes {
    fn free_object(self) -> Self {
        match self {
            ObjTypes::String(s) => unsafe { Box::from_raw(s.as_ptr()) },
            ObjTypes::None => return self,
        }
        .next()
    }
}

impl Debug for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ObjTypes::String(s) => write!(f, "{:?}->{:?}", s, unsafe { s.as_ref() }),
            ObjTypes::None => write!(f, "None"),
        }
    }
}

impl Display for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ObjTypes::String(s) => write!(f, "{}", unsafe { s.as_ref() }),
            ObjTypes::None => unreachable!(),
        }
    }
}

pub struct Heap {
    objs: ObjTypes,
}

impl Heap {
    pub fn new() -> Self {
        Self {
            objs: ObjTypes::None,
        }
    }

    pub fn new_string(&mut self, s: String) -> Value {
        let o = Object::<LoxStr>::new(s);
        o.next = std::mem::replace(&mut self.objs, ObjTypes::String(NonNull::from(&*o)));
        Value::Obj(self.objs)
    }

    pub fn free_objects(&mut self) {
        while !matches!(self.objs, ObjTypes::None) {
            self.objs = self.objs.free_object();
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        self.free_objects();
    }
}

impl Value {
    pub fn as_f64(self) -> Result<f64> {
        match self {
            Self::Number(f) => Ok(f),
            _ => bail!("Not a number."),
        }
    }

    pub fn as_string(&self) -> Result<&str> {
        if let Self::Obj(o) = self {
            if let ObjTypes::String(s) = o {
                return Ok(unsafe { s.as_ref() }.inner.as_str());
            }
        }
        bail!("Not a string.");
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
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

pub struct ValueArray {
    values: Vec<Value>,
}

impl ValueArray {
    pub fn new() -> Self {
        Self { values: vec![] }
    }
    pub fn write(&mut self, val: Value) -> usize {
        self.values.push(val);
        self.values.len() - 1
    }
}

impl Index<u8> for ValueArray {
    type Output = Value;

    fn index(&self, index: u8) -> &Self::Output {
        &self.values[index as usize]
    }
}

impl Deref for ValueArray {
    type Target = [Value];

    fn deref(&self) -> &Self::Target {
        self.values.as_slice()
    }
}
