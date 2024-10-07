#![allow(clippy::ptr_arg)]

use anyhow::{anyhow, bail, Context, Result};

use std::collections::HashMap;
use std::ops::ControlFlow;
use std::ops::ControlFlow::Continue;

use crate::jlox::ast::{
    expr,
    stmt::{self, ListStmt, Stmt},
    Accepts, NodeId, Visitor,
};
use crate::jlox::environment::Env;
use crate::jlox::lox_types::{self, LoxType, NativeFn};
use crate::scanner::{Token, TokenType};

pub struct Interpreter {
    pub env: Env,
    globals: Env,
    locals: HashMap<NodeId, usize>,
    start_time: std::time::Instant,
}

impl Interpreter {
    pub fn new() -> Self {
        let env = Env::new();
        let globals = env.clone();

        globals.define("clock", NativeFn::new(0, Self::clock).into());

        Self {
            env,
            globals,
            locals: HashMap::new(),
            start_time: std::time::Instant::now(),
        }
    }

    pub fn interpret(&mut self, statements: &[Stmt]) -> Result<()> {
        for stmt in statements {
            if let ControlFlow::Break(result) = self.execute(stmt) {
                result?;
            }
        }
        Ok(())
    }

    fn clock(&mut self, _args: &[LoxType]) -> Result<LoxType> {
        Ok(self.start_time.elapsed().as_secs_f64().into())
    }

    fn execute(&mut self, statement: &Stmt) -> StmtVisitResult {
        statement.accept(self)
    }

    pub fn resolve(&mut self, expr: NodeId, scope_idx: usize) {
        self.locals.insert(expr, scope_idx);
    }

    fn lookup_variable(&mut self, name: &Token, expr: NodeId) -> ExprVisitResult {
        if let Some(depth) = self.locals.get(&expr) {
            self.env.get_at(name.lexeme(), *depth)
                .with_context(|| format!("{:?} JLox bug. Failed to lookup variable {:?} at depth {depth}.", name, name.lexeme()))
        } else {
            self.globals.get(name)
        }
    }

    fn evaluate(&mut self, expr: &dyn Accepts<Self, ExprVisitResult>) -> ExprVisitResult {
        expr.accept(self)
    }

    fn evaluate_for_stmt(
        &mut self,
        expr: &dyn Accepts<Self, ExprVisitResult>,
    ) -> ControlFlow<ExprVisitResult, LoxType> {
        let result = self.evaluate(expr);
        if let Ok(val) = result {
            Continue(val)
        } else {
            ControlFlow::Break(result)
        }
    }

    pub fn execute_block(&mut self, statements: &ListStmt, mut env: Env) -> StmtVisitResult {
        std::mem::swap(&mut env, &mut self.env);
        let ret = statements.iter().try_for_each(|stmt| stmt.accept(self));
        std::mem::swap(&mut env, &mut self.env);
        ret
    }

    fn get_superclass(
        &mut self,
        class: &stmt::Class,
    ) -> ControlFlow<ExprVisitResult, Option<lox_types::Class>> {
        if let Some(sup) = &class.superclass {
            if let LoxType::Class(cls) = self.evaluate_for_stmt(sup)? {
                Continue(Some(cls))
            } else {
                ControlFlow::Break(Err(anyhow!(
                    "Superclass must be a class.\n[line {}]",
                    sup.name.line()
                )))
            }
        } else {
            Continue(None)
        }
    }
}

/* stmt Visitors */
type StmtVisitResult = ControlFlow<ExprVisitResult>;

impl Visitor<stmt::Block, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Block) -> StmtVisitResult {
        let env = self.env.create_local();
        self.execute_block(&node.statements, env)
    }
}

impl Visitor<stmt::Class, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Class) -> StmtVisitResult {
        let superclass: Option<lox_types::Class> = self.get_superclass(node)?;
        self.env.define(node.name.lexeme(), LoxType::Nil);

        let method_env = if let Some(superclass) = superclass.as_ref() {
            let env = self.env.create_local();
            env.define("super", superclass.clone().into());
            env
        } else {
            self.env.clone()
        };

        let mut methods = HashMap::new();
        for method in &node.methods {
            let mut fun = lox_types::Function::new(method, method_env.clone());
            if method.name.lexeme() == "init" {
                fun.is_init = true;
            }
            methods.insert(method.name.lexeme().to_string(), fun);
        }

        let class = lox_types::Class::new(node.name.lexeme(), superclass, methods);
        self.env
            .assign(&node.name, class.into())
            .expect("This doesn't fail, since the variable name was defined above.");
        Continue(())
    }
}

impl Visitor<stmt::Expression, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Expression) -> StmtVisitResult {
        self.evaluate_for_stmt(&node.expression)?;
        Continue(())
    }
}

impl Visitor<stmt::Function, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Function) -> StmtVisitResult {
        let function = lox_types::Function::new(node, self.env.clone());
        self.env.define(node.name.lexeme(), function.into());
        Continue(())
    }
}

impl Visitor<stmt::If, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::If) -> StmtVisitResult {
        if self.evaluate_for_stmt(&node.condition)?.is_truthy() {
            self.execute(&node.thenBranch)
        } else if let Some(els) = &node.elseBranch {
            self.execute(els)
        } else {
            Continue(())
        }
    }
}

impl Visitor<stmt::Print, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Print) -> StmtVisitResult {
        let val = self.evaluate_for_stmt(&node.expression)?;
        println!("{}", val);
        Continue(())
    }
}

impl Visitor<stmt::Return, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Return) -> StmtVisitResult {
        ControlFlow::Break(Ok(match &node.value {
            Some(v) => self.evaluate_for_stmt(v)?,
            None => LoxType::Nil,
        }))
    }
}

impl Visitor<stmt::Var, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::Var) -> StmtVisitResult {
        let value = self.evaluate_for_stmt(&node.initializer)?;
        self.env.define(node.name.lexeme(), value);
        Continue(())
    }
}

impl Visitor<stmt::While, StmtVisitResult> for Interpreter {
    fn visit(&mut self, node: &stmt::While) -> StmtVisitResult {
        while self.evaluate_for_stmt(&node.condition)?.is_truthy() {
            self.execute(&node.body)?;
        }
        Continue(())
    }
}

/* expr Visitors */
pub type ExprVisitResult = Result<LoxType>;

impl Visitor<expr::Assign, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Assign) -> ExprVisitResult {
        let value = self.evaluate(&node.value)?;
        if let Some(&depth) = self.locals.get(&node.id) {
            self.env.assign_at(depth, &node.name, value.clone())?;
        } else {
            self.globals.assign(&node.name, value.clone())?;
        }
        Ok(value)
    }
}

impl Visitor<expr::Binary, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Binary) -> ExprVisitResult {
        let left = self.evaluate(&node.left)?;
        let right = self.evaluate(&node.right)?;

        macro_rules! floats {
            ($op:tt) => {{
                let ctx = || format!("Operands must be numbers.\n[line {}]", node.operator.line());
                let left = left.as_f64().with_context(ctx)?;
                let right = right.as_f64().with_context(ctx)?;
                (left $op right).into()
            }}
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
                    LoxType::String([l.as_ref(), r.as_ref()].join("").into())
                }
                _ => bail!(
                    "Operands must be two numbers or two strings.\n[line {}]",
                    node.operator.line()
                ),
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

impl Visitor<expr::Set, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Set) -> ExprVisitResult {
        if let LoxType::Instance(mut obj) = self.evaluate(&node.object)? {
            let value = self.evaluate(&node.value)?;
            obj.set(&node.name, value.clone());
            Ok(value)
        } else {
            bail!("Only instances have fields.\n[line {}]", node.name.line())
        }
    }
}

impl Visitor<expr::Super, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Super) -> ExprVisitResult {
        let distance = self
            .locals
            .get(&node.id)
            .expect("Resolver error! 'super' node missing in locals.");
        let superclass = self.env.get_at("super", *distance).unwrap();
        let object = self
            .env
            .get_at("this", *distance - 1)
            .expect("Resolver error! 'this' not at dist -1.");

        if let LoxType::Class(sup) = superclass {
            let method = sup.find_method(node.method.lexeme()).with_context(|| {
                format!(
                    "Undefined property '{}'.\n[line {}]",
                    node.method.lexeme(),
                    node.method.line()
                )
            })?;
            if let LoxType::Instance(ref object) = object {
                Ok(method.bind(object).into())
            } else {
                bail!("Object is not an instance.")
            }
        } else {
            bail!("Superclass is not a class.")
        }
    }
}

impl Visitor<expr::This, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::This) -> ExprVisitResult {
        self.lookup_variable(&node.keyword, node.id)
    }
}

impl Visitor<expr::Unary, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Unary) -> ExprVisitResult {
        let right = node.right.accept(self)?;

        match node.operator.tok_type() {
            TokenType::Minus => right.as_f64().map(|f| (-f).into()).with_context(|| {
                format!("Operand must be a number.\n[line {}]", node.operator.line())
            }),
            TokenType::Bang => Ok((!right.is_truthy()).into()),
            _ => unreachable!(),
        }
    }
}

impl Visitor<expr::Variable, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Variable) -> ExprVisitResult {
        self.lookup_variable(&node.name, node.id)
    }
}

impl Visitor<expr::Call, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Call) -> ExprVisitResult {
        let mut callee = self.evaluate(&node.callee)?;
        let function = callee.as_callable().with_context(|| {
            format!(
                "Can only call functions and classes.\n[line {}]",
                node.paren.line()
            )
        })?;
        if node.arguments.len() != function.arity() {
            bail!(
                "Expected {} arguments but got {}.\n[line {}]",
                function.arity(),
                node.arguments.len(),
                node.paren.line(),
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

impl Visitor<expr::Get, ExprVisitResult> for Interpreter {
    fn visit(&mut self, node: &expr::Get) -> ExprVisitResult {
        if let LoxType::Instance(object) = self.evaluate(&node.object)? {
            Ok(object.get(&node.name)?)
        } else {
            bail!(
                "Only instances have properties.\n[line {}]",
                node.name.line()
            )
        }
    }
}
