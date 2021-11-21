use anyhow::bail;

use std::fmt::{Display, Formatter};
use std::ops::Not;

#[derive(Clone, Debug, PartialEq)]
pub enum LoxType {
    Bool(bool),
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
