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

    fn delete(&self) {
        self.key.set(ptr::null());
        self.value.set(Value::Bool(true));
    }

    fn is_tombstone(&self) -> bool {
        self.key.get().is_null() && self.value.get() == Value::Bool(true)
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
        let tombstone = entry.is_tombstone();
        entry.set(key, value);
        if is_new && !tombstone {
            self.count += 1;
        }
        is_new
    }

    pub fn delete(&mut self, key: &LoxStr) -> bool {
        if self.count == 0 {
            return false;
        }
        let entry = self.find_entry(key);
        if entry.value().is_some() {
            entry.delete();
            true
        } else {
            false
        }
    }

    pub fn add_all(&mut self, other: &Self) {
        for e in other.entries.iter().filter(|e| e.value().is_some()) {
            self.set(e.key.get(), e.value.get());
        }
    }

    pub fn entries(&self) -> impl Iterator<Item = (StrPtr, Value)> + '_ {
        self.entries
            .iter()
            .filter(|e| e.value().is_some())
            .map(|e| (e.key.get(), e.value.get()))
    }

    fn find_entry(&self, key: &LoxStr) -> &Entry {
        let capacity = self.capacity() as u32;
        let mut index = key.hash % capacity;
        let mut tombstone = u32::MAX;
        loop {
            let e = &self.entries[index as usize];
            if let Some(e_key) = e.key() {
                if e_key == key {
                    // FIXME: this should assume string interning and do a ptr cmp
                    return &self.entries[index as usize];
                }
            } else {
                if !e.is_tombstone() {
                    return &self.entries[if tombstone < u32::MAX {
                        tombstone
                    } else {
                        index
                    } as usize];
                } else if tombstone == u32::MAX {
                    tombstone = index;
                }
            }
            index = (index + 1) % capacity;
        }
    }

    fn adjust_capacity(&mut self, cap: usize) {
        let mut old = std::mem::replace(&mut self.entries, Vec::new());
        self.entries.resize_with(cap, || Default::default());
        self.count = 0;
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

    #[test]
    fn test_deletion() {
        let mut table = LoxTable::new();
        let mut heap = Heap::new();
        macro_rules! str {
            ($s:expr) => {
                heap.new_string($s.to_string()).as_loxstr().unwrap()
            };
        }
        macro_rules! get {
            ($k:expr) => {
                assert_eq!(table.get($k), None)
            };
            ($k:expr, $v:expr) => {
                assert_eq!(table.get($k), Some($v))
            };
        }
        let s1 = str!("asd");
        assert!(table.set(s1, Value::Nil));
        get!(s1, Value::Nil);
        table.delete(s1);
        get!(s1);
        assert!(table.set(s1, Value::Bool(true)));
        get!(s1, Value::Bool(true));

        let mut entries = vec![(s1, Value::Bool(true))];
        for n in 0..100 {
            let s = str!(n);
            let v = Value::Number(n as f64);
            assert!(table.set(s, v));
            entries.push((s, v));
        }
        assert_eq!(table.count, 101);
        for (k, v) in &entries {
            get!(k, *v);
        }
        for k in &entries {
            assert!(table.delete(k.0));
            assert!(!table.delete(k.0));
        }
        assert_eq!(table.count, 101);
        for (k, v) in &entries {
            assert!(table.set(*k, *v));
            assert!(table.delete(*k));
        }

        for n in 100..130 {
            let s = str!(n);
            let v = Value::Number(n as f64);
            assert!(table.set(s, v));
            entries.push((s, v));
        }
        assert_eq!(table.count, 109);
        table.adjust_capacity(109);
        assert_eq!(table.count, 30);
    }
}
