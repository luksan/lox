use crate::clox::table::LoxTable;
use crate::clox::value::{LoxStr, ObjTypes, Value};

use std::cell::{Cell, UnsafeCell};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, DerefMut, Index};

pub struct Heap {
    objs: Cell<ObjTypes>,
    strings: UnsafeCell<LoxTable>,
}

impl Heap {
    pub fn new() -> Self {
        Self {
            objs: ObjTypes::None.into(),
            strings: LoxTable::new().into(),
        }
    }

    pub fn new_object<O: Display + Debug + 'static>(&self, inner: O) -> &'static mut Obj<O>
    where
        *const Obj<O>: Into<ObjTypes>,
    {
        let o = Obj::new(inner);
        o.next = self.objs.replace((o as *const Obj<O>).into());
        o
    }

    pub fn new_string(&self, s: String) -> Value {
        // Safety: This is safe since Heap isn't Sync,
        // and self.strings is only accessed in this method, which
        // isn't recursive.
        let str_int = unsafe { &mut *self.strings.get() };
        if let Some(s) = str_int.find_key(s.as_str()) {
            return Value::Obj(s.into());
        }
        let o = self.new_object(LoxStr::from_string(s));
        str_int.set(o, Value::Nil);
        Value::Obj(self.objs.get())
    }

    pub fn free_objects(&mut self) {
        while !matches!(self.objs.get(), ObjTypes::None) {
            self.objs.replace(self.objs.get().free_object());
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        self.free_objects();
    }
}

#[cfg(test)]
mod heap_test {
    use super::Heap;

    #[test]
    fn string_interning() {
        let heap = Heap::new();
        let s1 = heap.new_string("asd".to_string());
        let s2 = heap.new_string("asd".to_string());
        assert_eq!(s1, s2);
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

pub struct Obj<T: ?Sized + Display + Debug> {
    pub(crate) next: ObjTypes,
    inner: T,
}

impl<T: Display + Debug> Obj<T> {
    fn new<S: Into<T>>(from: S) -> &'static mut Self {
        Box::leak(Box::new(Obj {
            next: ObjTypes::None,
            inner: from.into(),
        }))
    }
}

impl<T: Display + Debug + ?Sized> Deref for Obj<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Display + Debug + ?Sized> DerefMut for Obj<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: Display + Debug> Debug for Obj<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Object{{ inner: {:?}, next: ... }}", self.inner)
    }
}

impl<T: Display + Debug> Display for Obj<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
