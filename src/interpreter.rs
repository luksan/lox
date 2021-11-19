use anyhow::{bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, Stmt},
    LoxValue, Visitor,
};
use crate::scanner::TokenType;

pub struct Interpreter {}

impl Interpreter {
    pub fn new() -> Self {
        Self {}
    }

    pub fn interpret(&mut self, statements: &Vec<Stmt>) -> Result<()> {
        for stmt in statements {
            self.execute(stmt)?;
        }
        Ok(())
    }

    fn execute(&mut self, statement: &Stmt) -> Result<()> {
        statement.accept(self)
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<LoxValue> {
        expr.accept(self)
    }
}

impl Visitor<expr::Binary, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Binary) -> Result<LoxValue> {
        let left = self.evaluate(&node.left)?;
        let right = self.evaluate(&node.right)?;

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

impl Visitor<stmt::Expression, Result<()>> for Interpreter {
    fn visit(&mut self, node: &stmt::Expression) -> Result<()> {
        self.evaluate(&node.expression)?;
        Ok(())
    }
}

impl Visitor<stmt::Print, Result<()>> for Interpreter {
    fn visit(&mut self, node: &stmt::Print) -> Result<()> {
        let val = self.evaluate(&node.expression)?;
        println!("{}", val);
        Ok(())
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
