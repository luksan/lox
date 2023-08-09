use std::cell::{Cell, UnsafeCell};
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use crate::clox::mm::{HasRoots, Obj, ObjTypes};
use crate::clox::value::{LoxObject, LoxStr, Value};

pub type StrPtr = *const Obj<LoxStr>;

pub trait Table {
    fn get_value(&self, key: &Obj<LoxStr>) -> Option<Value>;
    /// Inserts a value in the table, returns false if the key already
    /// was in the table.
    fn set(&self, key: &Obj<LoxStr>, value: Value) -> bool;

    /// Remove the entry from the table, returns true if the entry was present.
    fn delete(&self, key: &Obj<LoxStr>) -> bool;
    fn add_all(&self, other: &Self);
}

/*
use std::collections::HashMap;
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
*/

// pub type LoxTable = HashMap<StrPtr, Value>;
pub type LoxTable = LoxMap;

pub struct LoxMap {
    pop_count: Cell<usize>,
    entries: UnsafeCell<Box<[Entry]>>,
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
    key: Cell<Option<NonNull<Obj<LoxStr>>>>,
    value: Cell<Value>,
}

#[test]
fn sizeof_entry() {
    // println!("sizeof entry {}", std::mem::size_of::<Entry>());
    assert_eq!(std::mem::size_of::<Entry>(), 16);
}

impl Entry {
    fn key(&self) -> Option<&Obj<LoxStr>> {
        self.key.get().map(|ptr| unsafe { ptr.as_ref() })
    }

    fn key_matches(&self, other: &Obj<LoxStr>) -> Option<bool> {
        self.key.get().map(|str_ptr| *other == str_ptr.as_ptr())
    }

    fn value(&self) -> Option<Value> {
        if self.key.get().is_some() {
            Some(self.value.get())
        } else {
            None
        }
    }

    fn delete(&self) {
        self.key.set(None);
        self.value.set(Value::Bool(true));
    }

    fn is_tombstone(&self) -> bool {
        self.key.get().is_none() && self.value.get() == Value::Bool(true)
    }

    fn set(&self, key: &Obj<LoxStr>, val: Value) {
        self.key.set(Some(key.into()));
        self.value.set(val);
    }
}

impl Default for Entry {
    fn default() -> Self {
        Self {
            key: Cell::new(None),
            value: Value::Nil.into(),
        }
    }
}

impl Table for LoxMap {
    fn get_value(&self, key: &Obj<LoxStr>) -> Option<Value> {
        if self.count() == 0 {
            return None;
        }
        self.find_entry(key).value()
    }

    fn set(&self, key: &Obj<LoxStr>, value: Value) -> bool {
        let curr_cap = self.capacity();
        if self.count() + 1 > curr_cap / 4 * 3 {
            self.adjust_capacity(8.max(curr_cap * 2));
        }
        let entry = self.find_entry(key);
        let is_new = entry.key().is_none();
        let tombstone = entry.is_tombstone();
        entry.set(key, value);
        if is_new && !tombstone {
            self.pop_count.set(self.pop_count.get() + 1);
        }
        is_new
    }

    fn delete(&self, key: &Obj<LoxStr>) -> bool {
        if self.count() == 0 {
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

    fn add_all(&self, other: &Self) {
        for (k, v) in other.iter() {
            self.set(k, v);
        }
    }
}

impl LoxMap {
    pub fn new() -> Self {
        Self {
            pop_count: 0.into(),
            entries: UnsafeCell::new(Box::new([])),
        }
    }

    fn entries_ref(&self) -> &[Entry] {
        unsafe { &**self.entries.get() }
    }

    /// Returns the sum of live entries and tombstones
    fn count(&self) -> usize {
        self.pop_count.get()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Obj<LoxStr>, Value)> + '_ {
        self.entries_ref()
            .iter()
            .filter_map(|e| e.key().map(|key| (key, e.value.get())))
    }

    fn find_entry(&self, key: &Obj<LoxStr>) -> &Entry {
        let mask = self.capacity() - 1;
        let entries = self.entries_ref();
        let mut index = key.hash as usize & mask;
        let mut first_tombstone = None;
        loop {
            // SAFETY: the index is always in bounds since capacity is a power of 2
            let entry = unsafe { entries.get_unchecked(index) };

            match entry.key_matches(key) {
                Some(true) => return entry,
                Some(false) => {}
                None if !entry.is_tombstone() => return first_tombstone.unwrap_or(entry),
                None => {
                    first_tombstone.get_or_insert(entry);
                }
            }
            index = (index + 1) & mask;
        }
        // unreachable!("The table is never at 100% capacity, or completely full of tombstones.")
    }

    fn adjust_capacity(&self, cap: usize) {
        // TODO: mark this function as unsafe
        assert!(cap.is_power_of_two());
        let mut new = Vec::with_capacity(cap);
        new.resize_with(cap, Entry::default);
        // SAFETY: this is fine as long as we don't hold any references to the entries slice across a adjust_capacity call
        let old = std::mem::replace(unsafe { &mut *self.entries.get() }, new.into_boxed_slice());
        self.pop_count.set(0);
        for e in old.iter() {
            if let Some(key) = e.key() {
                self.set(key, e.value.get());
            }
        }
    }

    fn capacity(&self) -> usize {
        self.entries_ref().len()
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

#[derive(Debug)]
pub struct TypedMap<T: LoxObject>(LoxMap, PhantomData<Obj<T>>);

impl<T: LoxObject + 'static> TypedMap<T> {
    pub fn new() -> Self {
        Self(LoxMap::new(), PhantomData)
    }

    pub fn get(&self, key: &Obj<LoxStr>) -> Option<&Obj<T>> {
        self.0
            .get_value(key)
            // SAFETY: this unwrap is ok since all values in the map are of the correct type
            .map(|val| unsafe { val.as_object().unwrap_unchecked() })
    }

    pub fn set(&self, key: &Obj<LoxStr>, val: *const Obj<T>) -> bool {
        self.0.set(key, val.into())
    }

    pub fn set_value(&self, key: &Obj<LoxStr>, val: Value) -> bool {
        self.set(
            key,
            val.as_object()
                .expect("Attempted to insert incorrect value in TypedMap."),
        )
    }

    pub fn add_all(&self, other: &Self) {
        self.0.add_all(&other.0);
    }

    pub fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.0.mark_roots(mark_obj)
    }
}

pub(crate) struct StringInterner(LoxMap);

impl StringInterner {
    pub(crate) fn new() -> Self {
        Self(LoxMap::new())
    }

    pub(crate) fn remove_white(&self) {
        for e in self.0.entries_ref().iter() {
            if let Some(k) = e.key() {
                if !k.is_marked() {
                    e.delete();
                }
            }
        }
    }

    pub fn find_key(&self, k: &str) -> Option<StrPtr> {
        if self.0.count() == 0 {
            return None;
        }
        let cap = self.capacity() as u32;
        let hash = LoxStr::hash(k);
        let entries = self.0.entries_ref();
        let mut index = hash & (cap - 1);
        loop {
            let entry = &entries[index as usize];
            if entry.value().is_none() && !entry.is_tombstone() {
                return None;
            }
            if let Some(key) = entry.key() {
                if &**key == (k, hash) {
                    return Some(key as _);
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

    #[test]
    fn basic_test() {
        let table = LoxMap::new();
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
        let table = LoxMap::new();
        let heap = Heap::new();

        let _token = heap.register_gc_root(&table);

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
        assert_eq!(table.count(), 101);
        for (k, v) in &entries {
            get!(k, *v);
        }
        for k in &entries {
            assert!(table.delete(k.0));
            assert!(!table.delete(k.0));
        }
        assert_eq!(table.count(), 101);
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
        assert_eq!(table.count(), 109);
        table.adjust_capacity(2);
        assert_eq!(table.count(), 30);
    }

    #[test]
    fn find_key() {
        let table = StringInterner::new();
        let heap = Heap::new();
        let s1 = heap.new_string("asd".to_string());
        table.set(s1, Value::Bool(false));
        assert_eq!(table.find_key("asd"), Some(s1 as *const _));
        assert_eq!(table.find_key(s1.as_str()), Some(s1 as *const _));
        assert_eq!(table.find_key("asd2"), None);
    }
}
