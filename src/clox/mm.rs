use crate::clox::get_settings;
use crate::clox::table::LoxTable;
use crate::clox::value::{Closure, Function, LoxStr, NativeFn, Upvalue, Value};

use tracing::{instrument, trace};

use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, DerefMut, Index};
use std::ptr::NonNull;

#[derive(Clone, Copy, PartialEq)]
pub enum ObjTypes {
    Closure(NonNull<Obj<Closure>>),
    Function(NonNull<Obj<Function>>),
    NativeFn(NonNull<Obj<NativeFn>>),
    LoxStr(NonNull<Obj<LoxStr>>),
    Upvalue(NonNull<Obj<Upvalue>>),
    None,
}

macro_rules! objtypes_impl {
    ($($typ:ident),+) => { $(
        impl From<*const Obj<$typ>> for ObjTypes {
            fn from(f: *const Obj<$typ>) -> Self {
                Self::$typ(NonNull::new(f as *mut _).unwrap())
            }
        }

        impl From<NonNull<Obj<$typ>>> for ObjTypes {
            fn from(f: NonNull<Obj<$typ>>) -> Self {
                Self::$typ(f)
            }
        }
        )+

        macro_rules! for_all_objtypes {
            ($self:ident, $mac:ident) => {{
                #[allow(non_snake_case)]
                match $self {
                    $( ObjTypes::$typ($typ) => $mac!($typ), )+
                    ObjTypes::None => unreachable!("Should have been handled above."),
                }
            }}
        }
    }
}

objtypes_impl!(Closure, Function, NativeFn, LoxStr, Upvalue);

impl ObjTypes {
    pub(crate) fn free_object(self) -> Self {
        macro_rules! free_next {
            ($ptr:expr) => {{
                trace!("Freeing Obj<{}> @ {:?}", stringify!($ptr), $ptr);
                unsafe { Box::from_raw($ptr.as_ptr()) }.next
            }};
        }
        if self == ObjTypes::None {
            return self;
        }
        for_all_objtypes!(self, free_next)
    }

    pub(crate) fn cast<'a, T: Display + Debug + 'static>(self) -> Option<&'a Obj<T>> {
        macro_rules! down {
            ($ptr:expr) => {
                return (unsafe { $ptr.as_ref() } as &dyn Any).downcast_ref()
            };
        }
        if self == ObjTypes::None {
            return None;
        }
        for_all_objtypes!(self, down)
    }
}

impl Debug for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($p:expr) => {
                write!(f, "{:?}->{:?}", $p, unsafe { $p.as_ref() })
            };
        }
        if self == &Self::None {
            return write!(f, "ObjTypes::None");
        }
        for_all_objtypes!(self, w)
    }
}

impl Display for ObjTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        macro_rules! w {
            ($ptr:expr) => {
                write!(f, "{}", unsafe { $ptr.as_ref() })
            };
        }
        if self == &ObjTypes::None {
            return Ok(());
        }
        for_all_objtypes!(self, w)
    }
}

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

    pub fn new_object<O: Display + Debug + 'static>(&self, inner: O) -> &'static Obj<O>
    where
        *const Obj<O>: Into<ObjTypes>,
    {
        if get_settings().gc_stress_test {
            self.collect_garbage();
        }
        trace!("new Obj<{}>", value_type_str::<O>());
        let o = Obj::new(inner);
        o.next = self.objs.replace((o as *const Obj<O>).into());
        o
    }

    pub fn new_string(&self, s: String) -> Value {
        // Safety: This is safe since Heap isn't Sync,
        // and self.strings is only accessed in this method, which
        // isn't recursive.
        let str_int = unsafe { &mut *self.strings.get() };
        if let Some(str_ptr) = str_int.find_key(s.as_str()) {
            trace!("new_string() '{}' already interned.", s);
            return Value::Obj(str_ptr.into());
        }
        trace!("new_string() interning '{}'", s);
        let o = self.new_object(LoxStr::from_string(s));
        str_int.set(o, Value::Nil);
        Value::Obj(self.objs.get())
    }

    #[instrument]
    fn collect_garbage(&self) {
        trace!("gc start");

        trace!("gc end");
    }

    pub fn free_objects(&mut self) {
        while !matches!(self.objs.get(), ObjTypes::None) {
            self.objs.replace(self.objs.get().free_object());
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
        write!(f, "Obj<{}>{{{:?}}}", value_type_str::<T>(), self.inner)
    }
}

impl<T: Display + Debug> Display for Obj<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

fn value_type_str<T>() -> &'static str {
    std::any::type_name::<T>().rsplitn(2, "::").next().unwrap()
}
