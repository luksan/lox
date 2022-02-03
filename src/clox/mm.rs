use crate::clox::table::LoxTable;
use crate::clox::value::{LoxStr, ObjTypes, Object, Value};
use std::ops::{Deref, Index};
use std::ptr::NonNull;

pub struct Heap {
    objs: ObjTypes,
    strings: LoxTable,
}

impl Heap {
    pub fn new() -> Self {
        Self {
            objs: ObjTypes::None,
            strings: LoxTable::new(),
        }
    }

    pub fn new_string(&mut self, s: String) -> Value {
        if let Some(s) = self.strings.find_key(s.as_str()) {
            return Value::Obj(s.into());
        }
        let o = Object::<LoxStr>::new(s);
        o.next = std::mem::replace(&mut self.objs, ObjTypes::String(NonNull::from(&*o)));
        self.strings.set(o, Value::Nil);
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

#[cfg(test)]
mod heap_test {
    use super::Heap;

    #[test]
    fn string_interning() {
        let mut heap = Heap::new();
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
