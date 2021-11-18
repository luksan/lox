use anyhow::{anyhow, bail, Result};

use crate::ast::{AstVisitor, Binary, Expr, Grouping, Literal, LoxValue, Unary};
use crate::parser::Ast;
use crate::scanner::TokenType;

pub struct Interpreter {
    value: Result<Option<LoxValue>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self { value: Ok(None) }
    }

    pub fn interpret(&mut self, expression: &dyn Expr) {
        expression.accept(self);
        if let Some(val) = self.take() {
            println!("{}", val);
        } else {
            eprintln!("{:?}", self.value)
        }
        self.value = Ok(None);
    }

    fn evaluate(ast: &Ast) -> Result<LoxValue> {
        let mut v = Self::new();
        ast.accept(&mut v);
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

    fn bin_expr(&mut self, bin: &Binary) -> Result<LoxValue> {
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

impl AstVisitor for Interpreter {
    fn binary_expr(&mut self, bin: &Binary) {
        self.value = self.bin_expr(bin).map(Some);
    }

    fn grouping_expr(&mut self, grp: &Grouping) {
        grp.expression.accept(self);
    }

    fn literal_expr(&mut self, lit: &Literal) {
        self.value = Ok(Some(lit.value.clone()));
    }

    fn unary_expr(&mut self, unary: &Unary) {
        unary.right.accept(self);

        match unary.operator.tok_type() {
            TokenType::Minus => self.map(|l| l.as_f64().map(|f| (-f).into())),
            TokenType::Bang => self.map(|l| Ok(!l.is_truthy())),
            _ => unreachable!(),
        };
    }
}
