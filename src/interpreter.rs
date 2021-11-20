use anyhow::{bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
    LoxValue, Visitor,
};
use crate::environment::Environment;
use crate::scanner::TokenType;

pub struct Interpreter {
    env: Box<Environment>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Environment::new(),
        }
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

    fn execute_block(&mut self, statements: &ListStmt) -> Result<()> {
        for statement in statements {
            self.execute(statement)?;
        }
        Ok(())
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

impl Visitor<stmt::Block, Result<()>> for Interpreter {
    fn visit(&mut self, node: &stmt::Block) -> Result<()> {
        self.env.create_inner();
        self.execute_block(&node.statements)?;
        self.env.end_scope();
        Ok(())
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

impl Visitor<stmt::Var, Result<()>> for Interpreter {
    fn visit(&mut self, node: &stmt::Var) -> Result<()> {
        let value = self.evaluate(&node.initializer)?;
        self.env.define(node.name.lexeme(), value);
        Ok(())
    }
}

impl Visitor<expr::Assign, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Assign) -> Result<LoxValue> {
        let value = self.evaluate(&node.value)?;
        self.env.assign(&node.name, value.clone())?;
        Ok(value)
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

impl Visitor<expr::Variable, Result<LoxValue>> for Interpreter {
    fn visit(&mut self, node: &expr::Variable) -> Result<LoxValue> {
        self.env.get(&node.name)
    }
}
