use anyhow::{anyhow, bail, Result};

use crate::ast::{
    expr::{self, Expr},
    LoxValue, Visitor,
};
use crate::scanner::TokenType;

pub struct Interpreter {
    value: Result<Option<LoxValue>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self { value: Ok(None) }
    }

    pub fn interpret(&mut self, expression: &Expr) {
        expression.accept(self);
        if let Some(val) = self.take() {
            println!("{}", val);
        } else {
            eprintln!("{:?}", self.value)
        }
        self.value = Ok(None);
    }

    fn evaluate(expr: &Expr) -> Result<LoxValue> {
        let mut v = Self::new();
        expr.accept(&mut v);
        v.value
            .and_then(|o| o.ok_or_else(|| anyhow!("Expression evaluated to None.")))
    }

    fn map(&mut self, func: impl FnOnce(LoxValue) -> Result<LoxValue>) {
        if let Some(value) = self.take() {
            self.value = func(value).map(|val| Some(val));
        }
    }

    fn take(&mut self) -> Option<LoxValue> {
        self.value.as_mut().map_or(None, |o| o.take())
    }

    fn bin_expr(&mut self, bin: &expr::Binary) -> Result<LoxValue> {
        let left = Self::evaluate(&bin.left)?;
        let right = Self::evaluate(&bin.right)?;

        macro_rules! floats {
            ($op:tt) => {
                (left.as_f64()? $op right.as_f64()?).into()
            }
        }
        Ok(match bin.operator.tok_type() {
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

impl Visitor<expr::Binary, ()> for Interpreter {
    fn visit(&mut self, node: &expr::Binary) -> () {
        self.value = self.bin_expr(node).map(Some);
    }
}
impl Visitor<expr::Grouping, ()> for Interpreter {
    fn visit(&mut self, node: &expr::Grouping) -> () {
        node.expression.accept(self);
    }
}
impl Visitor<expr::Literal, ()> for Interpreter {
    fn visit(&mut self, node: &expr::Literal) -> () {
        self.value = Ok(Some(node.value.clone()));
    }
}
impl Visitor<expr::Unary, ()> for Interpreter {
    fn visit(&mut self, node: &expr::Unary) -> () {
        node.right.accept(self);

        match node.operator.tok_type() {
            TokenType::Minus => self.map(|l| l.as_f64().map(|f| (-f).into())),
            TokenType::Bang => self.map(|l| Ok((!l.is_truthy()).into())),
            _ => unreachable!(),
        };
    }
}
