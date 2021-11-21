use anyhow::bail;

use crate::ast::stmt;

use crate::interpreter::ExprVisitResult;
use crate::Interpreter;
use std::fmt::{Display, Formatter};
use std::ops::Not;

#[derive(Clone, Debug, PartialEq)]
pub enum LoxType {
    Bool(bool),
    Function(Function),
    Nil,
    Number(f64),
    String(String),
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
            Self::Function(fun) => Ok(fun),
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
            Self::Function(fun) => write!(f, "<fn {}>", fun.declaration.name.lexeme()),
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

impl From<f64> for LoxType {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}

pub trait Callable {
    fn arity(&self) -> usize;
    fn call(&mut self, interpreter: &mut Interpreter, arguments: &Vec<LoxType>) -> ExprVisitResult;
}

#[derive(Clone, Debug)]
pub struct Function {
    declaration: stmt::Function,
}

impl Function {
    pub fn new(declaration: &stmt::Function) -> LoxType {
        LoxType::Function(Self {
            declaration: declaration.clone(),
        })
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }
}

impl Callable for Function {
    fn arity(&self) -> usize {
        self.declaration.params.len()
    }

    fn call(&mut self, interpreter: &mut Interpreter, arguments: &Vec<LoxType>) -> ExprVisitResult {
        let env = interpreter.env.create_local();
        for (arg, name) in arguments.iter().zip(self.declaration.params.iter()) {
            env.define(name.lexeme(), arg.clone());
        }

        interpreter.execute_block(&self.declaration.body, env);
        Ok(LoxType::Nil)
    }
}
