use anyhow::{bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
    Visitor,
};
use crate::environment::Environment;
use crate::scanner::TokenType;
use crate::LoxValue;

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

/* stmt Visitors */
type StmtVisitResult = Result<()>;

impl Visitor<stmt::Block, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Block) -> StmtVisitResult {
        self.env.create_inner();
        self.execute_block(&node.statements)?;
        self.env.end_scope();
        Ok(())
    }
}

impl Visitor<stmt::Expression, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Expression) -> StmtVisitResult {
        self.evaluate(&node.expression)?;
        Ok(())
    }
}

impl Visitor<stmt::Function, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Function) -> StmtVisitResult {
        todo!()
    }
}

impl Visitor<stmt::If, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::If) -> StmtVisitResult {
        if self.evaluate(&node.condition)?.is_truthy() {
            self.execute(&node.thenBranch)
        } else if let Some(els) = &node.elseBranch {
            self.execute(els)
        } else {
            Ok(())
        }
    }
}

impl Visitor<stmt::Print, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Print) -> StmtVisitResult {
        let val = self.evaluate(&node.expression)?;
        println!("{}", val);
        Ok(())
    }
}

impl Visitor<stmt::Var, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Var) -> StmtVisitResult {
        let value = self.evaluate(&node.initializer)?;
        self.env.define(node.name.lexeme(), value);
        Ok(())
    }
}

impl Visitor<stmt::While, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::While) -> StmtVisitResult {
        while self.evaluate(&node.condition)?.is_truthy() {
            self.execute(&node.body)?;
        }
        Ok(())
    }
}

/* expr Visitors */
type ExprVisitResult = Result<LoxValue>;

impl Visitor<expr::Assign, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Assign) -> ExprVisitResult {
        let value = self.evaluate(&node.value)?;
        self.env.assign(&node.name, value.clone())?;
        Ok(value)
    }
}

impl Visitor<expr::Binary, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Binary) -> ExprVisitResult {
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

impl Visitor<expr::Grouping, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Grouping) -> ExprVisitResult {
        node.expression.accept(self)
    }
}
impl Visitor<expr::Literal, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Literal) -> ExprVisitResult {
        Ok(node.value.clone())
    }
}

impl Visitor<expr::Logical, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Logical) -> ExprVisitResult {
        let left = self.evaluate(&node.left)?;
        match node.operator.tok_type() {
            TokenType::Or => {
                if left.is_truthy() {
                    return Ok(left);
                }
            }
            TokenType::And => {
                if !left.is_truthy() {
                    return Ok(left);
                }
            }
            _ => unreachable!(),
        }
        self.evaluate(&node.right)
    }
}

impl Visitor<expr::Unary, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Unary) -> ExprVisitResult {
        let right = node.right.accept(self)?;

        match node.operator.tok_type() {
            TokenType::Minus => right.as_f64().map(|f| (-f).into()),
            TokenType::Bang => Ok((!right.is_truthy()).into()),
            _ => unreachable!(),
        }
    }
}

impl Visitor<expr::Variable, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Variable) -> ExprVisitResult {
        self.env.get(&node.name)
    }
}

impl Visitor<expr::Call, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Call) -> ExprVisitResult {
        let callee = self.evaluate(&node.callee)?;

        let args: Vec<_> = node
            .arguments
            .iter()
            .map(|expr| self.evaluate(expr))
            .collect();

        unimplemented!()
    }
}
