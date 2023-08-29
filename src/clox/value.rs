// this is needed for sptr
#![allow(unstable_name_collisions)]
use sptr::Strict;

use std::cell::Cell;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomPinned;
use std::ptr;
use std::ptr::NonNull;

use anyhow::Result;

use crate::clox::mm::{HasRoots, Obj, ObjPtr, ObjTypes};
use crate::clox::table::{LoxTable, Table, TypedMap};
use crate::clox::Chunk;

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct ValuePacked(*const u64);

impl ValuePacked {
    const NAN_EXPONENT: u64 = 0b111_1111_1111 << 52;
    const NOT_FLOAT: u64 = Self::NAN_EXPONENT | (3 << 50); // Quiet NaN and "Indefinite" bits, Ch 30.3.1
    const PTR_MASK: u64 = 0xffff_ffff_ffff; // max 48 bit pointers

    const NIL: u64 = 1;
    const FALSE: u64 = 2;
    const TRUE: u64 = 3;

    #[allow(non_snake_case)]
    pub const fn Bool(val: bool) -> Self {
        Self(sptr::invalid(
            ((if val { Self::TRUE } else { Self::FALSE }) | Self::NOT_FLOAT) as usize,
        ))
    }
    #[allow(non_snake_case)]
    pub fn Number(n: f64) -> Self {
        n.into()
    }

    #[allow(non_upper_case_globals)]
    pub const False: Self = Self((Self::FALSE | Self::NOT_FLOAT) as *const _);
    #[allow(non_upper_case_globals)]
    pub const Nil: Self = Self((Self::NIL | Self::NOT_FLOAT) as *const _);

    fn is_float(self) -> bool {
        self.0 as u64 & Self::NOT_FLOAT != Self::NOT_FLOAT
    }

    fn as_objtypes(self) -> Option<ObjTypes> {
        if !self.is_float() && f64::from_bits(self.0 as u64).is_sign_negative() {
            let ptr = self.0.map_addr(|int| int & Self::PTR_MASK as usize) as *const Obj<Function>;
            Some(ObjTypes::from(ptr))
        } else {
            None
        }
    }
    pub fn as_f64(self) -> Option<f64> {
        if self.is_float() {
            Some(f64::from_bits(self.0 as u64))
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        self.as_object::<LoxStr>().map(|o| o.as_str())
    }

    pub fn as_object<'a, O: LoxObject + 'static>(self) -> Option<&'a Obj<O>> {
        if !self.is_float() && f64::from_bits(self.0 as u64).is_sign_negative() {
            let ptr = self.0.map_addr(|int| int & Self::PTR_MASK as usize) as *const Obj<O>;
            ObjTypes::from(ptr).cast()
        } else {
            None
        }
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::False
    }

    pub(crate) fn mark(&self, callback: &mut dyn FnMut(ObjTypes)) {
        self.as_objtypes().map(|o| o.mark(callback));
    }
}

impl PartialEq for ValuePacked {
    fn eq(&self, other: &Self) -> bool {
        if self.0 != other.0 {
            return false;
        }
        self.as_f64().map_or(true, |f| !f.is_nan())
    }
}

impl From<bool> for ValuePacked {
    fn from(v: bool) -> Self {
        Self::Bool(v)
    }
}

impl From<f64> for ValuePacked {
    fn from(float: f64) -> Self {
        let x = Self(sptr::invalid(float.to_bits() as usize));
        // assert!(x.is_float());
        x
    }
}

impl<O: Into<ObjTypes>> From<O> for ValuePacked {
    fn from(ptr: O) -> Self {
        let ptr = ptr.into();
        let neg_zero = (-0.0f64).to_bits();
        Self(
            ptr.as_ptr()
                .map_addr(|int| int | (neg_zero | Self::NOT_FLOAT) as usize)
                as *const _,
        )
    }
}

impl From<ValueEnum> for ValuePacked {
    fn from(v: ValueEnum) -> Self {
        Self(sptr::invalid(match v {
            ValueEnum::Bool(b) if b => Self::NOT_FLOAT | Self::TRUE,
            ValueEnum::Bool(_) => Self::NOT_FLOAT | Self::FALSE,
            ValueEnum::Nil => Self::NOT_FLOAT | Self::NIL,
            ValueEnum::Number(f) => f.to_bits(),
            ValueEnum::Obj(o) => return Self::from(o),
        } as usize))
    }
}

impl From<ValuePacked> for ValueEnum {
    fn from(v: ValuePacked) -> Self {
        if v.is_float() {
            return Self::Number(f64::from_bits(v.0 as u64));
        }
        if f64::from_bits(v.0 as u64).is_sign_negative() {
            return Self::Obj(v.as_objtypes().unwrap());
        }
        let bits = v.0 as u64 & 3;
        match bits {
            ValuePacked::NIL => Self::Nil,
            ValuePacked::TRUE => Self::Bool(true),
            ValuePacked::FALSE => Self::Bool(false),
            _ => unreachable!("BUG in ValuePacked NaN boxing."),
        }
    }
}

impl Display for ValuePacked {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", ValueEnum::from(*self))
    }
}

impl Debug for ValuePacked {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", ValueEnum::from(*self))
    }
}

#[test]
fn test_nanpack() {
    assert!(ValuePacked(sptr::invalid(1.0f64.to_bits() as usize)).is_float());
    assert!(ValuePacked(sptr::invalid((1.0f64 / 0.0).to_bits() as usize)).is_float());
    let nan_bits = (1.0f64 / 0.0).to_bits();
    assert_eq!(
        nan_bits & ValuePacked::NAN_EXPONENT,
        ValuePacked::NAN_EXPONENT
    );
    assert_ne!(nan_bits & ValuePacked::NOT_FLOAT, ValuePacked::NOT_FLOAT);
    assert!(ValuePacked::Nil.is_falsey());
    assert!(ValuePacked::Bool(false).is_falsey());
    assert!(ValuePacked::False.is_falsey());
    assert!(!ValuePacked::Bool(true).is_falsey());
}

#[test]
fn test_miri_value_packed() {
    let heap = crate::clox::Heap::new();
    let mut func = Function::new();
    func.name = heap.new_string("func_name".to_string());
    let obj_ref: &_ = heap.new_object(func);
    let val: ValuePacked = obj_ref.into();
    let obj2 = val.as_object::<Function>().unwrap();
    let val: ValueEnum = obj2.into();
    let val: ValuePacked = val.into();
    let obj3 = val.as_object::<Function>().unwrap();
    assert_eq!(obj3.name(), "func_name");
}

pub type Value = ValuePacked;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ValueEnum {
    Bool(bool),
    Nil,
    Number(f64),
    Obj(ObjTypes),
}

impl Display for ValueEnum {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{:?}", b),
            Self::Nil => write!(f, "nil"),
            Self::Number(n) => write!(f, "{}", n),
            Self::Obj(o) => write!(f, "{}", o),
        }
    }
}

impl ValueEnum {
    pub fn as_f64(self) -> Option<f64> {
        match self {
            Self::Number(f) => Some(f),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        self.as_object::<LoxStr>().map(|o| o.as_str())
    }

    pub fn is_falsey(self) -> bool {
        self == Self::Nil || self == Self::Bool(false)
    }

    pub fn as_object<'a, O: LoxObject + 'static>(self) -> Option<&'a Obj<O>> {
        if let Self::Obj(ptr) = self {
            ptr.cast::<O>()
        } else {
            None
        }
    }

    pub(crate) fn mark(&self, callback: &mut dyn FnMut(ObjTypes)) {
        if let Self::Obj(obj) = self {
            obj.mark(callback);
        }
    }
}

impl From<bool> for ValueEnum {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<f64> for ValueEnum {
    fn from(f: f64) -> Self {
        Self::Number(f)
    }
}

impl<O: Into<ObjTypes>> From<O> for ValueEnum {
    fn from(ptr: O) -> Self {
        Self::Obj(ptr.into())
    }
}

pub trait LoxObject: Debug + Display + HasRoots {}

#[derive(Debug, Clone)]
pub struct LoxStr {
    s: Box<str>,
    pub(crate) hash: u32,
}

impl LoxStr {
    pub fn as_str(&self) -> &str {
        &self.s
    }

    pub fn from_str(s: &str) -> Self {
        Self::from_string(s.to_owned())
    }

    pub fn from_string(s: String) -> Self {
        Self {
            hash: Self::hash(s.as_str()),
            s: s.into_boxed_str(),
        }
    }

    /// FNV-1a
    pub(crate) fn hash(s: &str) -> u32 {
        let mut hash = 2166136261;
        for b in s.bytes() {
            hash ^= b as u32;
            hash = hash.wrapping_mul(16777619);
        }
        hash
    }
}

#[test]
fn test_fnv1a() {
    let vectors: &[(&str, u32)] = &[
        ("1234", 0xfdc422fd),
        ("Clox fnv1a impl.", 0x14117b55),
        ("Test 3!\"#", 0xc8ee58ac),
    ];
    for (s, hash) in vectors {
        let lox_str = LoxStr::from_str(s);
        assert_eq!(lox_str.hash, *hash);
    }
}

impl LoxObject for LoxStr {}

impl HasRoots for LoxStr {
    fn mark_roots(&self, _mark_obj: &mut dyn FnMut(ObjTypes)) {
        // no roots
    }
}

impl PartialEq for LoxStr {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(&*self.s, &*other.s) // This assumes that LoxStr is interned
    }
}

impl PartialEq<*const Obj<LoxStr>> for Obj<LoxStr> {
    fn eq(&self, other: &*const Obj<LoxStr>) -> bool {
        ptr::eq(self, *other) // Assume string interning
    }
}

impl PartialEq<(&str, u32)> for &LoxStr {
    fn eq(&self, other: &(&str, u32)) -> bool {
        self.hash == other.1 && &*self.s == other.0
    }
}

impl From<String> for LoxStr {
    fn from(s: String) -> Self {
        Self::from_string(s)
    }
}

impl Display for LoxStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.s)
    }
}

#[derive(Debug)]
pub struct Upvalue {
    location: Cell<*mut Value>,
    next_open_upvalue: Cell<Option<ObjPtr<Upvalue>>>,
    closed: Cell<Value>,
    _pinned: PhantomPinned,
}

impl LoxObject for Upvalue {}

impl Upvalue {
    pub fn new(location: *mut Value) -> Self {
        Self {
            location: location.into(),
            next_open_upvalue: None.into(),
            closed: Value::Nil.into(),
            _pinned: PhantomPinned,
        }
    }

    pub fn get_val_ptr(&self) -> *const Value {
        self.location.get()
    }

    pub fn get_next_open(&self) -> Option<ObjPtr<Upvalue>> {
        self.next_open_upvalue.get()
    }

    pub fn set_next_open(&self, next: Option<ObjPtr<Upvalue>>) {
        self.next_open_upvalue.set(next);
    }

    pub fn close(this: &Obj<Self>) {
        this.closed.set(this.read());
        this.location.set(this.closed.as_ptr());
    }

    pub fn read(&self) -> Value {
        unsafe { *self.location.get() }
    }

    pub fn write(&self, value: Value) {
        unsafe {
            self.location.get().write(value);
        }
    }
}

impl HasRoots for Upvalue {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.closed.get().mark(mark_obj);
    }
}

impl Display for Upvalue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "upvalue")
    }
}

#[derive(Debug)]
pub struct Closure {
    pub function: NonNull<Obj<Function>>,
    pub upvalues: Box<[ObjPtr<Upvalue>]>,
}

impl LoxObject for Closure {}

impl Closure {
    pub fn new(function: NonNull<Obj<Function>>, uvg: &mut dyn FnMut() -> ObjPtr<Upvalue>) -> Self {
        let mut upvalues = vec![];
        upvalues.resize_with(unsafe { function.as_ref().upvalue_count }, uvg);
        Self {
            function,
            upvalues: upvalues.into_boxed_slice(),
        }
    }

    pub fn function(&self) -> &Function {
        unsafe { self.function.as_ref() }
    }

    pub fn read_upvalue(&self, slot: u8) -> Value {
        let slot = self.upvalues[slot as usize];
        slot.as_ref().read()
    }

    pub fn write_upvalue(&self, slot: u8, value: Value) {
        let slot = self.upvalues[slot as usize];
        slot.as_ref().write(value);
    }
}

impl HasRoots for Closure {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        unsafe { self.function.as_ref() }.mark(mark_obj);
        for uv in self.upvalues.iter() {
            let uv = uv.as_ref();
            uv.mark(mark_obj);
        }
    }
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.function())
    }
}

#[derive(Debug)]
pub struct Class {
    name: *const Obj<LoxStr>,
    methods: TypedMap<Closure>,
}

impl LoxObject for Class {}

impl Class {
    pub(crate) fn new(name: &Obj<LoxStr>) -> Self {
        Self {
            name,
            methods: TypedMap::new(),
        }
    }

    pub(crate) fn inherit(&self, superclass: &Obj<Class>) {
        self.methods.add_all(&superclass.methods);
    }

    pub(crate) fn add_method(&self, name: &Obj<LoxStr>, method: Value) {
        self.methods.set_value(name, method);
    }

    pub(crate) fn get_method(&self, name: &Obj<LoxStr>) -> Option<&Obj<Closure>> {
        self.methods.get(name)
    }
}

impl Display for Class {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", unsafe { &*self.name })
    }
}

impl HasRoots for Class {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        mark_obj(self.name.into());
        self.methods.mark_roots(mark_obj);
    }
}

#[derive(Debug)]
pub struct Instance {
    class: NonNull<Obj<Class>>,
    fields: LoxTable,
}

impl LoxObject for Instance {}

impl Instance {
    pub(crate) fn new(class: &Obj<Class>) -> Self {
        Self {
            class: class.into(),
            fields: LoxTable::new(),
        }
    }

    pub(crate) fn get_class(&self) -> &Obj<Class> {
        unsafe { self.class.as_ref() }
    }

    pub(crate) fn get_field(&self, field: &Obj<LoxStr>) -> Option<Value> {
        self.fields.get_value(field)
    }

    pub(crate) fn set_field(&self, field: &Obj<LoxStr>, value: Value) {
        self.fields.set(field, value);
    }
}

impl Display for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} instance", unsafe { self.class.as_ref() })
    }
}

impl HasRoots for Instance {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        mark_obj(self.class.into());
        self.fields.mark_roots(mark_obj);
    }
}

#[derive(Debug)]
pub struct BoundMethod {
    pub(crate) receiver: Value,
    method: NonNull<Obj<Closure>>,
}

impl LoxObject for BoundMethod {}

impl BoundMethod {
    pub(crate) fn new(receiver: Value, method: &Obj<Closure>) -> Self {
        Self {
            receiver,
            method: method.into(),
        }
    }

    pub(crate) fn get_closure(&self) -> &Obj<Closure> {
        unsafe { self.method.as_ref() }
    }
}

impl Display for BoundMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", unsafe { self.method.as_ref() })
    }
}

impl HasRoots for BoundMethod {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        self.receiver.mark(mark_obj);
        unsafe { self.method.as_ref() }.mark(mark_obj);
    }
}

#[derive(Debug)]
pub struct Function {
    pub(crate) arity: u8,
    pub(crate) chunk: Chunk,
    pub(crate) name: *const Obj<LoxStr>,
    pub(crate) upvalue_count: usize,
}

impl LoxObject for Function {}

impl HasRoots for Function {
    fn mark_roots(&self, mark_obj: &mut dyn FnMut(ObjTypes)) {
        for v in self.chunk.constants.iter() {
            v.mark(mark_obj);
        }
        if let Some(name) = unsafe { self.name.as_ref() } {
            name.mark(mark_obj);
        }
    }
}

impl Function {
    pub fn new() -> Self {
        Self {
            arity: 0,
            chunk: Chunk::new(),
            name: ptr::null(),
            upvalue_count: 0,
        }
    }

    pub fn name(&self) -> &str {
        unsafe { self.name.as_ref() }
            .map(|ls| ls.as_str())
            .unwrap_or("<script>")
    }

    pub fn disassemble(&self) {
        self.chunk.disassemble(self.name());
    }
}

impl Default for Function {
    fn default() -> Self {
        Function::new()
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<fn {}>",
            unsafe { self.name.as_ref() }
                .map(|s| s.as_str())
                .unwrap_or("<script>")
        )
    }
}

pub type NativeFnRef = fn(&[Value]) -> Result<Value>;

pub struct NativeFn(NativeFnRef);

impl LoxObject for NativeFn {}

impl NativeFn {
    pub fn call_native(&self, args: &[Value]) -> Result<Value> {
        self.0(args)
    }
}

impl HasRoots for NativeFn {
    fn mark_roots(&self, _mark_obj: &mut dyn FnMut(ObjTypes)) {
        // no roots
    }
}
impl Display for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn>")
    }
}

impl Debug for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "NativeFn({:?})", (&self.0) as *const _)
    }
}

impl From<NativeFnRef> for NativeFn {
    fn from(f: NativeFnRef) -> Self {
        Self(f)
    }
}
