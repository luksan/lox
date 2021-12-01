use anyhow::{bail, Context, Result};

use crate::ast::stmt;

use crate::environment::{Env, Environment};
use crate::interpreter::ExprVisitResult;
use crate::scanner::Token;
use crate::Interpreter;

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Not;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
pub enum LoxType {
    Bool(bool),
    Class(Class),
    Function(Function),
    Instance(Instance),
    NativeFn(NativeFn),
    Nil,
    Number(f64),
    String(Rc<str>),
}

impl LoxType {
    pub fn as_f64(&self) -> anyhow::Result<f64> {
        match self {
            Self::Number(num) => Ok(*num),
            typ => bail!("{:?} is not a number", typ),
        }
    }

    pub fn as_callable(&mut self) -> anyhow::Result<&mut dyn Callable> {
        match self {
            Self::Class(cls) => Ok(cls),
            Self::Function(fun) => Ok(fun),
            Self::NativeFn(fun) => Ok(fun),
            _ => bail!("{:?} is not callable.", self),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Nil => false,
            Self::Bool(b) => *b,
            _ => true,
        }
    }
}

impl Display for LoxType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            Self::Class(class) => write!(f, "{}", class.name),
            Self::Instance(obj) => write!(f, "{} instance", obj.class.name),
            Self::Function(fun) => write!(f, "<fn {}>", fun.declaration.name.lexeme()),
            Self::NativeFn(_) => write!(f, "<native fn>"),
            Self::Nil => write!(f, "nil"),
            Self::Number(num) => {
                if num.trunc() == *num {
                    // check if decimal part is zero
                    write!(f, "{:.0}", num)
                } else {
                    write!(f, "{}", num)
                }
            }
            Self::String(s) => write!(f, "{}", s),
        }
    }
}

impl Not for LoxType {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Bool(!self.is_truthy())
    }
}

impl From<bool> for LoxType {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<Class> for LoxType {
    fn from(c: Class) -> Self {
        Self::Class(c)
    }
}

impl From<Function> for LoxType {
    fn from(fun: Function) -> Self {
        Self::Function(fun)
    }
}

impl From<Instance> for LoxType {
    fn from(obj: Instance) -> Self {
        Self::Instance(obj)
    }
}

impl From<NativeFn> for LoxType {
    fn from(func: NativeFn) -> Self {
        Self::NativeFn(func)
    }
}

impl From<f64> for LoxType {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}

pub trait Callable {
    fn arity(&self) -> usize;
    fn call(&mut self, interpreter: &mut Interpreter, arguments: &[LoxType]) -> ExprVisitResult;
}

#[derive(Clone, Debug)]
pub struct Class {
    name: Rc<str>,
    superclass: Option<Box<Class>>,
    pub methods: Rc<HashMap<String, Function>>,
}

impl Class {
    pub fn new(name: &str, superclass: Option<Class>, methods: HashMap<String, Function>) -> Self {
        let superclass = superclass.map(|cls| Box::new(cls));
        Self {
            name: Rc::from(name),
            superclass,
            methods: Rc::from(methods),
        }
    }

    pub fn find_method(&self, name: &str) -> Option<Function> {
        self.methods.get(name).cloned().or_else(|| {
            self.superclass
                .as_ref()
                .and_then(|sup| sup.find_method(name))
        })
    }
}

impl PartialEq for Class {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.name, &other.name)
    }
}

impl Callable for Class {
    fn arity(&self) -> usize {
        self.find_method("init").map_or(0, |init| init.arity())
    }

    fn call(&mut self, interpreter: &mut Interpreter, arguments: &[LoxType]) -> ExprVisitResult {
        let instance = Instance::new(self.clone());
        if let Some(init) = self.find_method("init") {
            init.bind(&instance).call(interpreter, arguments)?;
        }
        Ok(instance.into())
    }
}

#[derive(Clone, Debug)]
pub struct Instance {
    class: Class,
    fields: Rc<RefCell<HashMap<String, LoxType>>>,
}

impl Instance {
    pub fn new(class: Class) -> Self {
        Self {
            class,
            fields: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn get(&self, name: &Token) -> Result<LoxType> {
        self.fields
            .borrow()
            .get(name.lexeme())
            .cloned()
            .or_else(|| {
                self.class
                    .find_method(name.lexeme())
                    .map(|fun| fun.bind(self).into())
            })
            .with_context(|| {
                format!(
                    "Undefined property '{}'.\n[line {}]",
                    name.lexeme(),
                    name.line()
                )
            })
    }

    pub fn set(&mut self, name: &Token, value: LoxType) {
        self.fields
            .borrow_mut()
            .insert(name.lexeme().to_string(), value);
    }
}

impl PartialEq for Instance {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.fields, &other.fields)
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    declaration: Rc<stmt::Function>,
    pub closure: Env,
    pub is_init: bool,
}

impl Function {
    pub fn new(declaration: &stmt::Function, closure: Env) -> Self {
        Self {
            declaration: Rc::from(declaration.clone()),
            closure,
            is_init: false,
        }
    }

    pub fn bind(&self, instance: &Instance) -> Function {
        let mut bound = self.clone();
        bound.closure = Environment::new(Some(bound.closure));
        bound
            .closure
            .define("this", LoxType::Instance(instance.clone()));
        bound
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.declaration, &other.declaration) && self.closure == other.closure
    }
}

impl Callable for Function {
    fn arity(&self) -> usize {
        self.declaration.params.len()
    }

    fn call(&mut self, interpreter: &mut Interpreter, arguments: &[LoxType]) -> ExprVisitResult {
        let env = self.closure.create_local();
        for (arg, name) in arguments.iter().zip(self.declaration.params.iter()) {
            env.define(name.lexeme(), arg.clone());
        }
        let val = match interpreter.execute_block(&self.declaration.body, env) {
            Ok(_) => LoxType::Nil,
            Err(e) => e.fun_ret()?,
        };
        if self.is_init {
            Ok(self.closure.get_at("this", 0).unwrap())
        } else {
            Ok(val)
        }
    }
}

#[derive(Clone)]
pub struct NativeFn {
    arity: usize,
    fun: fn(&mut Interpreter, &[LoxType]) -> Result<LoxType>,
}

impl NativeFn {
    pub fn new(arity: usize, fun: fn(&mut Interpreter, &[LoxType]) -> Result<LoxType>) -> Self {
        Self { arity, fun }
    }
}

impl Debug for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn {:?}:{}", &self.fun as *const _, self.arity)
    }
}

impl PartialEq for NativeFn {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(&self.fun, &other.fun)
    }
}

impl Callable for NativeFn {
    fn arity(&self) -> usize {
        self.arity
    }

    fn call(&mut self, interpreter: &mut Interpreter, arguments: &[LoxType]) -> ExprVisitResult {
        (self.fun)(interpreter, arguments)
    }
}
