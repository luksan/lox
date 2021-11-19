use anyhow::{bail, Result};

use crate::ast::{
    expr::{self, Expr},
    LoxValue, Visitor,
};
use crate::scanner::TokenType;

pub struct Interpreter {}

impl Interpreter {
    pub fn new() -> Self {
        Self {}
    }

    pub fn interpret(&mut self, expression: &Expr) {
        match expression.accept(self) {
            Ok(val) => println!("{}", val),
            Err(err) => eprintln!("{:?}", err),
        }
    }

    fn evaluate(expr: &Expr) -> Result<LoxValue> {
        let mut v = Self::new();
        expr.accept(&mut v)
    }
}

impl Visitor<expr::Binary, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Binary) -> Result<LoxValue> {
        let left = Self::evaluate(&node.left)?;
        let right = Self::evaluate(&node.right)?;

        macro_rules! floats {
            ($op:tt) => {
                (left.as_f64()? $op right.as_f64()?).into()
            }
        }
        Ok(match node.operator.tok_type() {
            TokenType::Greater => floats!(>),
            TokenType::GreaterEqual => floats!(>=),
            TokenType::Less => floats!(<),
            TokenType::LessEqual => floats!(<=),

            TokenType::BangEqual => (left != right).into(),
            TokenType::EqualEqual => (left == right).into(),

            TokenType::Minus => floats!(-),
            TokenType::Slash => floats!(/),
            TokenType::Star => floats!(*),
            TokenType::Plus => match (&left, &right) {
                (LoxValue::Number(_), LoxValue::Number(_)) => floats!(+),
                (LoxValue::String(l), LoxValue::String(r)) => {
                    LoxValue::String([l.as_str(), r.as_str()].join(""))
                }
                _ => bail!("Unsupported operand types for addition."),
            },

            _ => unreachable!(),
        })
    }
}
impl Visitor<expr::Grouping, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Grouping) -> Result<LoxValue> {
        node.expression.accept(self)
    }
}
impl Visitor<expr::Literal, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Literal) -> Result<LoxValue> {
        Ok(node.value.clone())
    }
}
impl Visitor<expr::Unary, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Unary) -> Result<LoxValue> {
        let right = node.right.accept(self)?;

        match node.operator.tok_type() {
            TokenType::Minus => right.as_f64().map(|f| (-f).into()),
            TokenType::Bang => Ok((!right.is_truthy()).into()),
            _ => unreachable!(),
        }
    }
}
