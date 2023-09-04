use crate::clox::get_settings;
use crate::clox::table::{StrPtr, StringInterner, Table};
use crate::clox::value::{LoxObject, Value, ValueEnum};

use tracing::{trace, trace_span};

use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::ffi::c_void;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index};
use std::ptr::NonNull;

#[repr(transparent)]
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

    pub fn as_ptr(&self) -> *const Obj<O> {
        self.0.as_ptr()
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
        Self::from(o as *const _)
    }
}

impl<T: LoxObject> From<ObjPtr<T>> for ObjTypes {
    fn from(o: ObjPtr<T>) -> Self {
        o.0.into()
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
                        let obj_ptr = ObjPtr(unsafe {$self.0.cast::<Obj<$typ>>()});
                        $mac!($typ, obj_ptr)
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

        #[derive(Debug)]
        pub enum ObjType<'a> {
            $($typ(&'a Obj<$typ>),)+
        }
       $(
        impl<'a> From<&'a Obj<$typ>> for ObjType<'a> {
            fn from(objref: &'a Obj<$typ>) -> Self {
                Self::$typ(objref)
            }
        }
       )+
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
            ($typ:tt, $ptr:expr) => {{
                unsafe { Obj::free($ptr) }
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

    pub(crate) fn mark(&self, callback: &mut ObjMarker) {
        macro_rules! set_mark {
            ($ptr:expr) => {
                $ptr.mark(callback)
            };
        }
        for_all_objtypes!(self, set_mark)
    }

    pub fn match_type(&self) -> ObjType {
        macro_rules! get_type {
            ($ref:expr) => {
                return $ref.into()
            };
        }
        for_all_objtypes!(self, get_type)
    }

    fn blacken(&self, callback: &mut ObjMarker) {
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

#[repr(transparent)]
pub struct ObjMarker<'a>(&'a mut dyn FnMut(ObjTypes));

pub trait HasRoots {
    fn mark_roots(&self, mark_obj: &mut ObjMarker);
}

impl HasRoots for HashMap<StrPtr, Value> {
    fn mark_roots(&self, mark_obj: &mut ObjMarker) {
        for (k, v) in self.iter() {
            unsafe { &**k }.mark(mark_obj);
            v.mark(mark_obj);
        }
    }
}

pub struct Heap {
    objs: Cell<Option<ObjTypes>>,
    strings: UnsafeCell<StringInterner>,
    has_roots: Box<[WeakRoot; 2]>,
    obj_count: Cell<usize>,
    next_gc: Cell<usize>,
}

pub struct GcToken<'heap, 'root>(&'heap WeakRoot, PhantomData<&'root dyn HasRoots>);

impl Drop for GcToken<'_, '_> {
    fn drop(&mut self) {
        self.0.dropped();
    }
}

#[derive(Debug, Default)]
struct WeakRoot(Cell<Option<NonNull<dyn HasRoots>>>);

impl WeakRoot {
    fn register<'root>(&self, root: *const (dyn HasRoots + 'root)) -> Option<GcToken<'_, 'root>> {
        if self.0.get().is_some() {
            // Slot is already taken
            return None;
        }
        self.0.set(NonNull::new(root as *mut _));
        Some(GcToken(self, PhantomData))
    }

    fn upgrade(&self) -> Option<&dyn HasRoots> {
        self.0.get().map(|ptr| unsafe { ptr.as_ref() })
    }

    fn dropped(&self) {
        self.0.set(Default::default())
    }
}

impl Heap {
    pub fn new() -> Self {
        Self {
            objs: None.into(),
            strings: StringInterner::new().into(),
            has_roots: Box::default(),
            obj_count: 0.into(),
            next_gc: 100.into(),
        }
    }

    /// SAFETY: The returned token must be kept alive as long as the GC root is using
    /// the heap, and it must be dropped before the heap is dropped.
    #[must_use]
    pub(crate) fn register_gc_root<'heap, 'root>(
        &'heap self,
        root: *const (dyn HasRoots + 'root),
    ) -> GcToken<'heap, 'root> {
        trace!("Registering GC root {:?}", root);
        self.has_roots
            .iter()
            .find_map(|slot| slot.register(root))
            .expect("No empty GC root slot found.")
    }

    pub(crate) fn new_object<O: LoxObject + 'static>(&self, inner: O) -> &Obj<O>
    where
        *const Obj<O>: Into<ObjTypes>,
        ObjTypes: From<*const Obj<O>>,
    {
        trace!("new_object({:?})", &inner);
        if self.obj_count > self.next_gc || get_settings().gc_stress_test {
            self.collect_garbage(&inner);
            self.next_gc.set(self.obj_count.get() * 2);
        }
        self.obj_count.set(self.obj_count.get() + 1);

        let new_obj = Obj::new(inner, self.objs.get());
        trace!("new {:?}", new_obj);

        let obj_type: ObjTypes = unsafe { NonNull::new_unchecked(new_obj) }.into();
        self.objs.set(Some(obj_type));

        unsafe { &*new_obj }
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
        let str_int = unsafe { &mut *self.strings.get() };
        str_int.set(o, Value::Nil);
        o
    }

    fn collect_garbage(&self, new_obj: &dyn HasRoots) {
        let span = trace_span!("GC");
        let _span_enter = span.enter();
        let mut gray_list = Vec::with_capacity(self.obj_count.get());
        let mut mark_closure = |obj| gray_list.push(obj);
        let mut obj_marker = ObjMarker(&mut mark_closure);
        for root in self.has_roots.iter() {
            let Some(r) = root.upgrade() else { continue };
            r.mark_roots(&mut obj_marker);
        }

        // Trace the not-yet-allocated object as well
        new_obj.mark_roots(&mut obj_marker);

        while let Some(obj) = gray_list.pop() {
            let mut mark_closure = |obj| gray_list.push(obj);
            let mut obj_marker = ObjMarker(&mut mark_closure);
            obj.blacken(&mut obj_marker);
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
    use crate::clox::Vm;

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

    #[test]
    fn gc_trace() -> anyhow::Result<()> {
        let heap = Heap::new();
        let mut vm = Vm::new(&heap);
        let source = "
class A {
   func() {}
}
for (var i = 0; i < 100; i = i + 1) {
   var a = A();
}
        ";
        let mut runner = vm.compile(source)?;
        for _ in 0..1000 {
            runner.run().unwrap();
        }
        Ok(())
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
    fn new<S: Into<T>>(from: S, next: Option<ObjTypes>) -> *mut Self {
        Box::leak(Box::new(Obj {
            kind: ObjKind::new::<T>(),
            next: next.into(),
            inner: from.into(),
            is_marked: false.into(),
        }))
    }

    unsafe fn free(s: ObjPtr<T>) -> Option<ObjTypes> {
        trace!("Freeing {:?} @ {:?}", s, s.0.as_ptr());
        unsafe { Box::from_raw(s.0.as_ptr()) }.next.get()
    }

    pub(crate) fn mark(&self, callback: &mut ObjMarker) {
        if self.is_marked.get() {
            return;
        }
        trace!("Marked {:?}", self);
        self.is_marked.set(true);
        (callback.0)(ObjTypes::from(self))
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
