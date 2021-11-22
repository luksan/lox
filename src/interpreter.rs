use anyhow::{bail, Result};

use crate::ast::{
    expr::{self, Expr},
    stmt::{self, ListStmt, Stmt},
    Visitor,
};
use crate::environment::{Env, Environment};
use crate::lox_types::NativeFn;
use crate::scanner::TokenType;
use crate::{lox_types, LoxType};

pub struct Interpreter {
    pub env: Env,
    globals: Env,
    start_time: std::time::Instant,
}

impl Interpreter {
    pub fn new() -> Self {
        let env = Environment::new();
        let globals = env.clone();

        globals.define("clock", NativeFn::new(0, Self::clock));

        Self {
            env,
            globals,
            start_time: std::time::Instant::now(),
        }
    }

    pub fn interpret(&mut self, statements: &Vec<Stmt>) -> Result<()> {
        for stmt in statements {
            self.execute(stmt)?;
        }
        Ok(())
    }

    fn clock(&mut self, _args: &Vec<LoxType>) -> Result<LoxType> {
        Ok(self.start_time.elapsed().as_secs_f64().into())
    }

    fn execute(&mut self, statement: &Stmt) -> StmtVisitResult {
        statement.accept(self)
    }

    fn evaluate(&mut self, expr: &Expr) -> ExprVisitResult {
        expr.accept(self)
    }

    pub fn execute_block(&mut self, statements: &ListStmt, mut env: Env) -> StmtVisitResult {
        std::mem::swap(&mut env, &mut self.env);
        let mut result = Ok(());
        for statement in statements {
            result = self.execute(statement);
            if result.is_err() {
                break;
            }
        }
        std::mem::swap(&mut env, &mut self.env);

        result
    }
}

/* stmt Visitors */
pub type StmtVisitResult = Result<()>;

impl Visitor<stmt::Block, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Block) -> StmtVisitResult {
        let env = self.env.create_local();
        self.execute_block(&node.statements, env)?;
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
        let function = lox_types::Function::new(node, self.env.clone());
        self.env.define(node.name.lexeme(), function);
        Ok(())
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

impl Visitor<stmt::Return, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Return) -> StmtVisitResult {
        let value = self.evaluate(&node.value)?;
        // Abort the tree-walk and return the value as an error to the
        // place where the callable was called.
        Err(anyhow::Error::msg(value))
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
pub type ExprVisitResult = Result<LoxType>;

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
                (LoxType::Number(_), LoxType::Number(_)) => floats!(+),
                (LoxType::String(l), LoxType::String(r)) => {
                    LoxType::String([l.as_str(), r.as_str()].join(""))
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
        let mut callee = self.evaluate(&node.callee)?;
        let function = callee.as_callable()?;
        if node.arguments.len() != function.arity() {
            bail!(
                "{:?}: Expected {} arguments but got {}.",
                node.paren,
                function.arity(),
                node.arguments.len()
            );
        }

        let args = node
            .arguments
            .iter()
            .map(|expr| self.evaluate(expr))
            .collect::<Result<Vec<_>, _>>()?;

        function.call(self, &args)
    }
}
