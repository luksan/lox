use anyhow::bail;

use std::fmt::{Display, Formatter};
use std::ops::Not;

#[derive(Clone, Debug, PartialEq)]
pub enum LoxValue {
    Bool(bool),
    Nil,
    Number(f64),
    String(String),
}

impl LoxValue {
    pub fn as_f64(&self) -> anyhow::Result<f64> {
        match self {
            Self::Number(num) => Ok(*num),
            typ => bail!("{:?} is not a number", typ),
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

impl Display for LoxValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            LoxValue::Nil => write!(f, "nil"),
            LoxValue::Number(num) => {
                if num.trunc() == *num {
                    // check if decimal part is zero
                    write!(f, "{:.0}", num)
                } else {
                    write!(f, "{}", num)
                }
            }
            LoxValue::String(s) => write!(f, "{}", s),
        }
    }
}

impl Not for LoxValue {
    type Output = LoxValue;

    fn not(self) -> Self::Output {
        LoxValue::Bool(!self.is_truthy())
    }
}

impl From<bool> for LoxValue {
    fn from(b: bool) -> Self {
        LoxValue::Bool(b)
    }
}

impl From<f64> for LoxValue {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}
