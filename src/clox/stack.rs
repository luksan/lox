use crate::clox::value::Value;
use std::fmt::{Debug, Formatter};

pub const FRAMES_MAX: usize = 64;

pub struct Stack {
    inner: Box<[Value; FRAMES_MAX * 256]>,
    top: *mut Value,
}

impl Stack {
    pub(crate) fn new() -> Self {
        let mut inner = Box::new([Value::Nil; FRAMES_MAX * 256]);
        let top = inner.as_mut_ptr();
        Self { inner, top }
    }

    pub(crate) fn push(&mut self, value: Value) {
        unsafe {
            self.top.write(value);
            self.top = self.top.add(1);
        }
    }

    pub(crate) fn peek(&self, from_top: u8) -> Value {
        unsafe { *self.top.sub(from_top as usize + 1) }
    }

    pub(crate) fn pop(&mut self) -> Value {
        unsafe {
            self.top = self.top.sub(1);
            *self.top
        }
    }

    pub(crate) fn remove_cnt(&mut self, cnt: u8) {
        self.top = unsafe { self.top.sub(cnt as usize) };
    }

    pub(crate) fn set_slot(&mut self, from_top: u8, value: Value) {
        unsafe {
            *self.top.sub(from_top as usize + 1) = value;
        }
    }

    /// Pushes the local at base + slot to the top of the stack.
    pub(crate) fn get_local(&mut self, base: *const Value, slot: u8) {
        let val = unsafe { *base.add(slot as usize) };
        self.push(val);
    }

    /// Writes the top value on the stack to the local variable at base + slot.
    pub(crate) fn set_local(&mut self, base: *mut Value, slot: u8) {
        unsafe { *base.add(slot as usize) = self.peek(0) };
    }

    pub(crate) fn slice_top(&self, from_top: u8) -> &[Value] {
        unsafe {
            std::slice::from_raw_parts(self.top.sub(from_top as usize + 1), from_top as usize + 1)
        }
    }

    pub(crate) fn slot_ptr(&self, from_top: u8) -> *mut Value {
        unsafe { self.top.sub(from_top as usize + 1) }
    }

    /// Number of active stack entries.
    fn len(&self) -> usize {
        unsafe { self.top.offset_from(self.inner.as_ptr()) as usize }
    }

    pub(crate) fn truncate(&mut self, to_slot: *mut Value) {
        self.top = to_slot;
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &Value> {
        self.inner[0..self.len()].iter()
    }
}

impl Debug for Stack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.inner[0..self.len()])
    }
}
