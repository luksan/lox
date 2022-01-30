use anyhow::{bail, Result};

use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, Index};
use std::ptr;
use std::ptr::NonNull;

#[derive(Copy, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    Nil,
    Number(f64),
    Obj(NonNull<Object>),
}

impl Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "Bool({:?})", b),
            Value::Nil => write!(f, "Nil"),
            Value::Number(n) => write!(f, "Number({:?})", n),
            Self::Obj(o) => write!(f, "Object({:?})", self.as_obj()),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{:?}", b),
            Value::Nil => write!(f, "nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Obj(o) => write!(f, "{}", unsafe { o.as_ref() }),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoxStr {
    s: Box<str>,
    hash: u32,
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
            hash: 0,
            s: s.into_boxed_str(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Object {
    inner: ObjTypes,
    next: *const Object,
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.inner {
            ObjTypes::String(s) => write!(f, "{}", s.as_str()),
            ObjTypes::None => unreachable!("Bad object."),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ObjTypes {
    String(LoxStr),
    None,
}

pub struct Heap {
    objs: *const Object,
}

impl Heap {
    pub fn new() -> Self {
        Self { objs: ptr::null() }
    }

    fn new_object(&mut self) -> *mut Object {
        let o = Box::new(Object {
            inner: ObjTypes::None,
            next: self.objs,
        });
        self.objs = Box::into_raw(o);
        self.objs as *mut _
    }

    pub fn new_string(&mut self, s: String) -> Value {
        let o: &mut Object = unsafe { self.new_object().as_mut().unwrap() };
        o.inner = ObjTypes::String(LoxStr::from_string(s));
        Value::Obj(NonNull::from(o))
    }

    pub fn free_objects(&mut self) {
        while !self.objs.is_null() {
            let o: Box<Object> = unsafe { Box::from_raw(self.objs as *mut _) };
            self.objs = o.next;
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
            if let ObjTypes::String(s) = unsafe { &o.as_ref().inner } {
                return Ok(s.as_str());
            }
        }
        bail!("Not a string.");
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
    }

    fn as_obj(&self) -> &Object {
        if let Self::Obj(o) = self {
            unsafe { o.as_ref() }
        } else {
            panic!("Not an object.")
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
