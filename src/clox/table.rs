use crate::clox::value::{LoxStr, Object, Value};
use std::cell::Cell;
use std::ptr;

pub type StrPtr = *const Object<LoxStr>;

pub trait Table {
    fn get(&self, key: StrPtr) -> Option<Value>;
    fn set(&mut self, key: StrPtr, value: Value) -> bool;
    fn delete(&mut self, key: StrPtr);
    fn add_all(&mut self, other: &dyn Table);
}

pub struct LoxTable {
    count: usize,
    entries: Vec<Entry>,
}

struct Entry {
    key: Cell<StrPtr>,
    value: Cell<Value>,
}

impl Entry {
    fn key(&self) -> Option<&LoxStr> {
        unsafe { self.key.get().as_ref() }.map(|o| &**o)
    }

    fn value(&self) -> Option<Value> {
        if !self.key.get().is_null() {
            Some(self.value.get())
        } else {
            None
        }
    }

    fn set(&self, key: StrPtr, val: Value) {
        self.key.set(key);
        self.value.set(val);
    }
}

impl Default for Entry {
    fn default() -> Self {
        Self {
            key: Cell::new(ptr::null()),
            value: Value::Nil.into(),
        }
    }
}

impl LoxTable {
    pub fn new() -> Self {
        Self {
            count: 0,
            entries: vec![],
        }
    }

    pub fn get(&self, key: &LoxStr) -> Option<Value> {
        if self.count == 0 {
            return None;
        }
        self.find_entry(key).value()
    }

    /// Inserts the value in the table, returns false if a value already was present.
    pub fn set(&mut self, key: StrPtr, value: Value) -> bool {
        if self.count + 1 > self.entries.len() / 4 * 3 {
            self.adjust_capacity(8.max(self.entries.len() * 2));
        }
        if key.is_null() {
            panic!("Table set() called with NULL key.");
        }
        let key_ref = unsafe { &**key.as_ref().unwrap() };
        let entry = self.find_entry(key_ref);
        let is_new = entry.value().is_none();
        entry.set(key, value);
        if is_new {
            self.count += 1;
        }
        is_new
    }

    pub fn delete(&mut self, key: &LoxStr) {}

    pub fn add_all(&mut self, other: &Self) {
        for e in other.entries.iter().filter(|e| e.value().is_some()) {
            self.set(e.key.get(), e.value.get());
        }
    }

    fn find_entry(&self, key: &LoxStr) -> &Entry {
        let capacity = self.capacity() as u32;
        let mut index = key.hash % capacity;
        loop {
            let e = &self.entries[index as usize];
            if let Some(e_key) = unsafe { e.key() } {
                if e_key != key {
                    // FIXME: this should assume string interning and do a ptr cmp
                    index = (index + 1) % capacity;
                    continue;
                }
            }
            break;
        }
        &self.entries[index as usize]
    }

    fn adjust_capacity(&mut self, cap: usize) {
        let mut old = std::mem::replace(&mut self.entries, Vec::new());
        self.entries.resize_with(cap, || Default::default());
        for e in old.drain(..).filter(|e| e.value().is_some()) {
            self.set(e.key.get(), e.value.get());
        }
    }

    fn capacity(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod test {
    use crate::clox::table::LoxTable;
    use crate::clox::value::{Heap, Value};

    #[test]
    fn basic_test() {
        let mut table = LoxTable::new();
        let mut heap = Heap::new();
        let s1 = heap.new_string("asd".to_string()).as_loxstr().unwrap();
        assert!(table.get(s1).is_none());
        assert!(table.set(s1, Value::Nil));
        assert_eq!(table.get(s1), Some(Value::Nil));
        assert!(!table.set(s1, Value::Bool(true)));
        assert_eq!(table.get(s1), Some(Value::Bool(true)));

        let s2 = heap.new_string("asd".to_string()).as_loxstr().unwrap();
        assert_ne!(table.get(s2), None); // FIXME: this should return None if a ptr cmp is done
    }
}
