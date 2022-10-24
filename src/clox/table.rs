use crate::clox::mm::{HasRoots, Obj, ObjTypes};
use crate::clox::value::{LoxStr, Value};

use std::cell::Cell;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::ptr;

pub type StrPtr = *const Obj<LoxStr>;

pub trait Table {
    fn get_value(&self, key: &Obj<LoxStr>) -> Option<Value>;
    /// Inserts a value in the table, returns false if the key already
    /// was in the table.
    fn set(&mut self, key: &Obj<LoxStr>, value: Value) -> bool;

    /// Remove the entry from the table, returns true if the entry was present.
    fn delete(&mut self, key: &Obj<LoxStr>) -> bool;
    fn add_all(&mut self, other: &Self);
}

impl Table for HashMap<StrPtr, Value> {
    fn get_value(&self, key: &Obj<LoxStr>) -> Option<Value> {
        self.get(&(key as StrPtr)).copied()
    }

    fn set(&mut self, key: &Obj<LoxStr>, value: Value) -> bool {
        self.insert(key as StrPtr, value).is_none()
    }

    fn delete(&mut self, key: &Obj<LoxStr>) -> bool {
        self.remove(&(key as StrPtr)).is_some()
    }

    fn add_all(&mut self, other: &Self) {
        <Self as Extend<_>>::extend(self, other);
    }
}

// pub type LoxTable = HashMap<StrPtr, Value>;
pub type LoxTable = LoxMap;

pub struct LoxMap {
    count: usize,
    entries: Vec<Entry>,
}

impl Debug for LoxMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.iter() {
            write!(f, "{}: {}", k, v)?;
        }
        Ok(())
    }
}

struct Entry {
    key: Cell<StrPtr>,
    value: Cell<Value>,
}

#[test]
fn sizeof_entry() {
    // println!("sizeof entry {}", std::mem::size_of::<Entry>());
    assert_eq!(std::mem::size_of::<Entry>(), 16);
}

impl Entry {
    fn key(&self) -> Option<&Obj<LoxStr>> {
        unsafe { self.key.get().as_ref() }
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

impl Table for LoxMap {
    fn get_value(&self, key: &Obj<LoxStr>) -> Option<Value> {
        if self.count == 0 {
            return None;
        }
        self.find_entry(key).value()
    }

    fn set(&mut self, key: &Obj<LoxStr>, value: Value) -> bool {
        if self.count + 1 > self.entries.len() / 4 * 3 {
            self.adjust_capacity(8.max(self.entries.len() * 2));
        }
        let entry = self.find_entry(key);
        let is_new = entry.key().is_none();
        let tombstone = entry.is_tombstone();
        entry.set(key, value);
        if is_new && !tombstone {
            self.count += 1;
        }
        is_new
    }

    fn delete(&mut self, key: &Obj<LoxStr>) -> bool {
        if self.count == 0 {
            return false;
        }
        let entry = self.find_entry(key);
        if entry.key().is_some() {
            entry.delete();
            true
        } else {
            false
        }
    }

    fn add_all(&mut self, other: &Self) {
        for (k, v) in other.iter() {
            self.set(k, v);
        }
    }
}

impl LoxMap {
    pub fn new() -> Self {
        Self {
            count: 0,
            entries: vec![],
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Obj<LoxStr>, Value)> + '_ {
        self.entries
            .iter()
            .filter_map(|e| e.key().map(|key| (key, e.value.get())))
    }

    fn find_entry(&self, key: &LoxStr) -> &Entry {
        let mask = self.capacity() - 1;
        let mut index = key.hash as usize & mask;
        let mut tombstone = None;
        loop {
            // SAFETY: the index is always in bounds since capacity is a power of 2
            let entry = unsafe { self.entries.get_unchecked(index) };
            index = (index + 1) & mask;

            match entry.key() {
                Some(entry_key) if &**entry_key == key => return entry,
                Some(_) => {}
                None => {
                    if !entry.is_tombstone() {
                        return tombstone.unwrap_or(entry);
                    } else if tombstone.is_none() {
                        tombstone = Some(entry)
                    }
                }
            }
        }
        // unreachable!("The table is never at 100% capacity, or completely full of tombstones.")
    }

    fn adjust_capacity(&mut self, cap: usize) {
        assert!(cap.is_power_of_two());
        let mut old = std::mem::replace(&mut self.entries, Vec::new());
        self.entries.resize_with(cap, Default::default);
        self.count = 0;
        for e in old.drain(..) {
            if let Some(key) = e.key() {
                self.set(key, e.value.get());
            }
        }
    }

    fn capacity(&self) -> usize {
        self.entries.len()
    }
}

impl HasRoots for LoxMap {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for (k, v) in self.iter() {
            k.mark(mark_obj);
            v.mark(mark_obj);
        }
    }
}

pub(crate) struct StringInterner(LoxMap);

impl StringInterner {
    pub(crate) fn new() -> Self {
        Self(LoxMap::new())
    }

    pub(crate) fn remove_white(&self) {
        for e in self.0.entries.iter() {
            if let Some(k) = e.key() {
                if !k.is_marked() {
                    e.delete();
                }
            }
        }
    }

    pub fn find_key(&self, k: &str) -> Option<StrPtr> {
        if self.0.count == 0 {
            return None;
        }
        let cap = self.capacity() as u32;
        let hash = LoxStr::hash(k);
        let mut index = hash & (cap - 1);
        loop {
            let entry = &self.entries[index as usize];
            if entry.value().is_none() && !entry.is_tombstone() {
                return None;
            }
            if let Some(key) = entry.key() {
                if &**key == (k, hash) {
                    return Some(entry.key.get());
                }
            }

            index = (index + 1) & (cap - 1);
        }
    }
}

impl Deref for StringInterner {
    type Target = LoxMap;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for StringInterner {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod test {
    // use tracing_test::traced_test;

    use crate::clox::mm::Heap;
    use crate::clox::table::{LoxMap, StringInterner, Table};
    use crate::clox::value::Value;
    use std::rc::Rc;

    #[test]
    fn basic_test() {
        let mut table = LoxMap::new();
        let heap = Heap::new();
        let s1 = heap.new_string("asd".to_string());
        assert!(table.get_value(s1).is_none());
        assert!(table.set(s1, Value::Nil));
        assert_eq!(table.get_value(s1), Some(Value::Nil));
        assert!(!table.set(s1, Value::Bool(true)));
        assert_eq!(table.get_value(s1), Some(Value::Bool(true)));

        let heap2 = Heap::new(); // put a string on another heap
        let s2 = heap2.new_string("asd".to_string());
        assert_eq!(table.get_value(s2), None); // This is None because of string interning
    }

    // #[traced_test]
    #[test]
    fn test_deletion() {
        let mut table = LoxMap::new();
        let mut heap = Heap::new();

        let roots = Rc::new(&table as *const _);
        heap.register_roots(&roots);

        macro_rules! str {
            ($s:expr) => {{
                heap.new_string($s.to_string())
            }};
        }
        macro_rules! get {
            ($k:expr) => {
                assert_eq!(table.get_value($k), None)
            };
            ($k:expr, $v:expr) => {
                assert_eq!(table.get_value($k), Some($v))
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
            assert!(table.set(s, v), "{n}", n = n);
            entries.push((s, v));
        }
        assert_eq!(table.count, 109);
        table.adjust_capacity(2);
        assert_eq!(table.count, 30);
    }

    #[test]
    fn find_key() {
        let mut table = StringInterner::new();
        let heap = Heap::new();
        let s1 = heap.new_string("asd".to_string());
        table.set(s1, Value::Bool(false));
        assert_eq!(table.find_key("asd"), Some(s1 as *const _));
        assert_eq!(table.find_key(s1.as_str()), Some(s1 as *const _));
        assert_eq!(table.find_key("asd2"), None);
    }
}
