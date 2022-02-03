use anyhow::{bail, Result};

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

    pub fn as_str(&self) -> Result<&str> {
        if let Self::Obj(o) = self {
            if let Some(s) = o.cast::<LoxStr>() {
                return Ok(s.inner.as_str());
            }
        }
        bail!("Not a string.");
    }

    pub fn as_loxstr(self) -> Option<&'static Object<LoxStr>> {
        if let Self::Obj(o) = self {
            if let Some(s) = o.cast::<LoxStr>() {
                return Some(s);
            }
        }
        None
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

impl From<ObjTypes> for Value {
    fn from(o: ObjTypes) -> Self {
        Self::Obj(o)
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
    String(NonNull<Object<LoxStr>>),
    None,
}

impl ObjTypes {
    pub(crate) fn free_object(self) -> Self {
        match self {
            ObjTypes::String(s) => unsafe { Box::from_raw(s.as_ptr()) }.next,
            ObjTypes::None => return self,
        }
    }

    fn cast<T: Display + Debug>(self) -> Option<&'static Object<T>> {
        match self {
            ObjTypes::String(s) => {
                return (unsafe { s.as_ref() } as &dyn Any).downcast_ref();
            }
            ObjTypes::None => {}
        }
        None
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

impl From<StrPtr> for ObjTypes {
    fn from(s: StrPtr) -> Self {
        Self::String(NonNull::new(s as *mut _).unwrap())
    }
}
