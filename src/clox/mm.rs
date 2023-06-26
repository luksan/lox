use crate::clox::get_settings;
use crate::clox::table::{StrPtr, StringInterner, Table};
use crate::clox::value::{LoxObject, Value, ValueEnum};

use tracing::{trace, trace_span};

use std::any::Any;
use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::HashMap;
use std::ffi::c_void;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index};
use std::ptr::NonNull;
use std::rc::{Rc, Weak};

pub struct ObjPtr<O: LoxObject>(NonNull<Obj<O>>);

impl<O: LoxObject> From<&Obj<O>> for ObjPtr<O> {
    fn from(value: &Obj<O>) -> Self {
        Self(NonNull::from(value))
    }
}

impl<O: LoxObject> Clone for ObjPtr<O> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<O: LoxObject> Copy for ObjPtr<O> {}

impl<O: LoxObject> ObjPtr<O> {
    pub fn as_ref(&self) -> &Obj<O> {
        unsafe { self.0.as_ref() }
    }
}

impl<O: LoxObject> Deref for ObjPtr<O> {
    type Target = O;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<O: LoxObject> Debug for ObjPtr<O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", unsafe { self.0.as_ref() })
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ObjTypes(NonNull<ObjKind>);

impl<T: LoxObject> From<&Obj<T>> for ObjTypes {
    fn from(o: &Obj<T>) -> Self {
        Self((&o.kind).into())
    }
}

impl<T: LoxObject> From<&mut Obj<T>> for ObjTypes {
    fn from(o: &mut Obj<T>) -> Self {
        // The first field of the Obj struct is the type enum,
        // so this cast is ok.
        Self(NonNull::from(o).cast())
    }
}

impl<T: LoxObject> From<*const Obj<T>> for ObjTypes {
    fn from(o: *const Obj<T>) -> Self {
        unsafe { Self(NonNull::new_unchecked(o as *mut ObjKind)) }
    }
}

impl<T: LoxObject> From<NonNull<Obj<T>>> for ObjTypes {
    fn from(o: NonNull<Obj<T>>) -> Self {
        Self(o.cast())
    }
}

macro_rules! objtypes_impl {
    ($($typ:ident),+) => {
        $(use crate::clox::value::$typ;)+

        macro_rules! for_all_objtypes {
            ($self:ident, $mac:ident) => {{
                #[allow(unused_unsafe)]
                match unsafe {*$self.0.as_ref()} {
                    $( ObjKind::$typ => {
                        let obj_ref = unsafe {$self.0.cast::<Obj<$typ>>().as_ref()};
                        $mac!(obj_ref)
                    }, )+
                }
            }}
        }

        macro_rules! for_all_objtypes_nonnull {
            ($self:ident, $mac:ident) => {{
                #[allow(unused_unsafe)]
                match unsafe {*$self.0.as_ref()} {
                    $( ObjKind::$typ => {
                        let mut obj_ptr = unsafe {$self.0.cast::<Obj<$typ>>()};
                        $mac!(obj_ptr)
                    }, )+
                }
            }}
        }

        #[derive(Copy, Clone, Debug, PartialEq)]
        #[repr(u8)]
        enum ObjKind {
            $($typ,)+
        }

        impl ObjKind {
            fn new<T: LoxObject + 'static>() -> Self {
                use std::any::TypeId;
                let id = TypeId::of::<T>();
                $(
                if TypeId::of::<$typ>() == id { return Self::$typ}
                )+
                unreachable!("Missing objtype for x")
            }
        }

    }
}

objtypes_impl!(
    BoundMethod, // Ch 28.2
    Class,
    Closure,
    Function,
    Instance,
    NativeFn,
    LoxStr,
    Upvalue
);

impl ObjTypes {
    pub(crate) fn as_ptr(self) -> *const c_void {
        self.0.as_ptr() as *const _
    }

    pub(crate) unsafe fn free_object(self) -> Option<Self> {
        macro_rules! free_next {
            ($ptr:expr) => {{
                unsafe { $ptr.as_mut().free() }
            }};
        }
        for_all_objtypes_nonnull!(self, free_next)
    }

    pub(crate) fn cast<'a, T: LoxObject + 'static>(self) -> Option<&'a Obj<T>> {
        macro_rules! down {
            ($ptr:expr) => {
                return ($ptr as &dyn Any).downcast_ref()
            };
        }
        for_all_objtypes!(self, down)
    }

    pub(crate) fn mark(&self, callback: &mut dyn FnMut(Self)) {
        macro_rules! set_mark {
            ($ptr:expr) => {
                $ptr.mark(callback)
            };
        }
        for_all_objtypes!(self, set_mark)
    }

    fn blacken(&self, callback: &mut dyn FnMut(Self)) {
        macro_rules! blacken {
            ($ptr:expr) => {
                $ptr.mark_roots(callback)
            };
        }
        for_all_objtypes!(self, blacken)
    }

    fn is_marked(&self) -> bool {
        macro_rules! sweep {
            ($ptr:expr) => {{
                $ptr.is_marked.get()
            }};
        }
        for_all_objtypes!(self, sweep)
    }

    fn clear_mark(&self) {
        macro_rules! sweep {
            ($ptr:expr) => {{
                $ptr.is_marked.set(false);
            }};
        }
        for_all_objtypes!(self, sweep)
    }

    fn next(&self) -> Option<Self> {
        macro_rules! sweep {
            ($ptr:expr) => {{
                $ptr.next.get()
            }};
        }
        for_all_objtypes!(self, sweep)
    }

    fn set_next(self, next: Option<Self>) {
        macro_rules! sweep {
            ($ptr:expr) => {{
                $ptr.next.set(next);
            }};
        }
        for_all_objtypes!(self, sweep)
    }
}

impl Debug for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($p:expr) => {
                write!(f, "{:?}->{:?}", $p, $p as *const _)
            };
        }
        for_all_objtypes!(self, w)
    }
}

impl Display for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($ptr:expr) => {
                write!(f, "{}", $ptr)
            };
        }
        for_all_objtypes!(self, w)
    }
}

pub trait HasRoots {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes));
}

impl HasRoots for HashMap<StrPtr, Value> {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for (k, v) in self.iter() {
            unsafe { &**k }.mark(mark_obj);
            v.mark(mark_obj);
        }
    }
}

pub struct Heap {
    objs: Cell<Option<ObjTypes>>,
    strings: UnsafeCell<StringInterner>,
    has_roots: RefCell<Vec<Weak<*const dyn HasRoots>>>,
    obj_count: Cell<usize>,
    next_gc: Cell<usize>,
}

pub struct GcToken<'heap, 'a>(Rc<*const (dyn HasRoots + 'a)>, PhantomData<&'heap Heap>);

impl Heap {
    pub fn new() -> Self {
        Self {
            objs: None.into(),
            strings: StringInterner::new().into(),
            has_roots: vec![].into(),
            obj_count: 0.into(),
            next_gc: 100.into(),
        }
    }

    /// SAFETY: The returned token must be kept alive as long as the GC root is using
    /// the heap, and it must be dropped before the heap is dropped.
    #[must_use]
    pub(crate) fn register_gc_root<'heap, 'a>(
        &'heap self,
        root: *const (dyn HasRoots + 'a),
    ) -> GcToken<'heap, 'a> {
        let token = Rc::new(root);
        trace!("Registered GC root {:?}", root);
        let weak = Rc::downgrade(&token);
        self.has_roots
            .borrow_mut()
            // This transmute extends the lifetime 'a to 'heap
            .push(unsafe { std::mem::transmute(weak) });
        GcToken(token, PhantomData::default())
    }

    pub(crate) fn new_object<O: LoxObject + 'static>(&self, inner: O) -> &Obj<O>
    where
        *const Obj<O>: Into<ObjTypes>,
        ObjTypes: From<*const Obj<O>>,
    {
        if self.obj_count > self.next_gc || get_settings().gc_stress_test {
            self.collect_garbage();
            self.next_gc.set(self.obj_count.get() * 2);
        }
        self.obj_count.set(self.obj_count.get() + 1);

        let new_obj = Obj::new(inner);
        let prev_head = self.objs.get();
        new_obj.next.set(prev_head);
        trace!("new {:?}", new_obj);

        let obj_type: ObjTypes = new_obj.into();
        self.objs.set(Some(obj_type));

        new_obj
    }

    pub(crate) fn new_string(&self, s: String) -> &Obj<LoxStr> {
        // Safety: This is safe since Heap isn't Sync,
        // and self.strings is only accessed in this method, which
        // isn't recursive.
        let str_int = unsafe { &mut *self.strings.get() };
        if let Some(str_ptr) = str_int.find_key(s.as_str()) {
            trace!("new_string() '{}' already interned.", s);
            return unsafe { &*str_ptr };
        }
        trace!("new_string() interning '{}'", s);
        let o = self.new_object(LoxStr::from_string(s));
        str_int.set(o, Value::Nil);
        o
    }

    fn collect_garbage(&self) {
        let span = trace_span!("GC");
        let _span_enter = span.enter();
        let mut gray_list = vec![];
        for root in self.has_roots.borrow().iter() {
            let r = root.upgrade().map(|ptr| unsafe { &**ptr });
            if r.is_none() {
                continue;
            };
            let r = r.unwrap();
            r.mark_roots(&mut |gray| {
                gray_list.push(gray);
            });
        }
        while let Some(obj) = gray_list.pop() {
            obj.blacken(&mut |gray| {
                gray_list.push(gray);
            });
        }

        // Clear interned strings about to be dropped
        unsafe { &*self.strings.get() }.remove_white();

        // sweep
        let mut next = self.objs.get();
        let mut prev = None;
        while let Some(obj) = next {
            if obj.is_marked() {
                obj.clear_mark();
                next = obj.next();
                prev = Some(obj);
            } else {
                next = unsafe { obj.free_object() };
                self.obj_count.set(self.obj_count.get() - 1);
                if let Some(prev) = prev {
                    prev.set_next(next);
                } else {
                    self.objs.set(next);
                }
            }
        }
    }

    unsafe fn free_objects(&mut self) {
        while let Some(next) = self.objs.get() {
            self.objs.set(unsafe { next.free_object() });
        }
        self.obj_count.set(0);
    }

    pub(crate) fn print_heap(&self) {
        println!("Heap objects");
        let mut next_obj = self.objs.get();
        while let Some(obj) = next_obj {
            println!("  {:?}", obj);
            next_obj = obj.next();
        }
    }
}

impl Debug for Heap {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Heap {{...}}")
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        unsafe { self.free_objects() }
    }
}

#[cfg(test)]
mod heap_test {
    use super::Heap;
    use crate::clox::value::Function;

    #[test]
    fn miri_heap_test() {
        let heap = Heap::new();
        let _x1 = heap.new_object(Function::new());
    }

    #[test]
    fn string_interning() {
        let heap = Heap::new();
        let s1 = heap.new_string("asd".to_string());
        let s2 = heap.new_string("asd".to_string());
        assert_eq!(s1.as_value(), s2.as_value());
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

#[repr(C)]
pub struct Obj<T: ?Sized + LoxObject> {
    kind: ObjKind,
    next: Cell<Option<ObjTypes>>,
    is_marked: Cell<bool>,
    inner: T,
}

impl<T: LoxObject + 'static> Obj<T>
where
    *const Obj<T>: Into<ObjTypes>,
    ObjTypes: From<*const Self>,
{
    fn new<'a, S: Into<T>>(from: S) -> &'a mut Self {
        Box::leak(Box::new(Obj {
            kind: ObjKind::new::<T>(),
            next: None.into(),
            inner: from.into(),
            is_marked: false.into(),
        }))
    }

    unsafe fn free(&mut self) -> Option<ObjTypes> {
        trace!("Freeing {:?} @ {:?}", self, self as *const _);
        unsafe { Box::from_raw(self as *mut Self) }.next.get()
    }

    pub(crate) fn mark(&self, callback: &mut dyn FnMut(ObjTypes)) {
        if self.is_marked.get() {
            return;
        }
        trace!("Marked {:?}", self);
        self.is_marked.set(true);
        callback(ObjTypes::from(self))
    }

    pub(crate) fn is_marked(&self) -> bool {
        self.is_marked.get()
    }

    pub fn as_value(&self) -> Value {
        let x: ValueEnum = ObjTypes::from(self).into();
        x.into()
    }
}

impl<T: LoxObject + ?Sized> Deref for Obj<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: LoxObject + ?Sized> DerefMut for Obj<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: LoxObject> Debug for Obj<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Obj<{}>{{{:?}}}", value_type_str::<T>(), self.inner)
    }
}

impl<T: LoxObject> Display for Obj<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

fn value_type_str<T>() -> &'static str {
    std::any::type_name::<T>().rsplit_once("::").unwrap().1
}
