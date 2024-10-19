use anyhow::{anyhow, bail, Context, Result};

use std::collections::HashMap;
use std::ops::ControlFlow;
use std::ops::ControlFlow::Continue;

use crate::ast::{expr, stmt::{self, Stmt}, Accepts, NodeId};
use crate::ast::expr::{Assign, Binary, Call, Get, Grouping, Literal, Logical, Set, Super, This, Unary, Variable};
use crate::ast::stmt::{Block, Class, Expression, Function, If, Print, Return, Var, While};
use crate::jlox::environment::{Env, RootedEnv};
use crate::jlox::JloxError;
use crate::jlox::lox_types::{self, LoxType, NativeFn};
use crate::jlox::resolver::Resolver;
use crate::scanner::{Token, TokenType};

pub struct Interpreter {
    pub env: RootedEnv,
    globals: RootedEnv,
    locals: HashMap<NodeId, (usize, usize)>, // (scope depth, env slot)
    start_time: std::time::Instant,
}

impl Interpreter {
    pub fn new() -> Self {
        let env = RootedEnv::new(Env::new_root_env());
        let globals = RootedEnv::new(env.clone());

        globals.define("clock", NativeFn::new(0, Self::clock).into());

        Self {
            env,
            globals,
            locals: HashMap::new(),
            start_time: std::time::Instant::now(),
        }
    }

    pub fn interpret(&mut self, statements: &[Stmt]) -> Result<(), JloxError> {
        let resolved = Resolver::resolve(statements)?;
        self.locals.extend(resolved);
        for stmt in statements {
            if let ControlFlow::Break(result) = self.execute(stmt) {
                result.map_err(JloxError::RuntimeError)?;
            }
        }
        Ok(())
    }

    fn clock(&mut self, _args: &[LoxType]) -> Result<LoxType> {
        Ok(self.start_time.elapsed().as_secs_f64().into())
    }

    fn execute(&mut self, statement: &Stmt) -> ControlFlow<Result<LoxType>> {
        statement.accept(self)
    }

    fn lookup_variable(&mut self, name: &Token, expr: NodeId) -> ExprVisitResult {
        if let Some((depth, _)) = self.locals.get(&expr) {
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

    pub fn execute_block(&mut self, statements: &[Stmt], env: Env) -> ControlFlow<Result<LoxType>> {
        let old_env = std::mem::replace(&mut self.env, RootedEnv::new(env));
        self.env.run_gc(); // GC must run before the block is executed, since ret might contain references to un-traced Envs.
        let ret = statements.iter().try_for_each(|stmt| stmt.accept(self));
        self.env = old_env;
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

pub type ExprVisitResult = Result<LoxType>;

impl stmt::StmtTypesVisitor for Interpreter {
    type Ret = ControlFlow<Result<LoxType>>;

    fn visit_block(&mut self, node: &Block) -> Self::Ret {
        let env = self.env.create_local();
        self.execute_block(&node.statements, env)
    }

    fn visit_class(&mut self, node: &Class) -> Self::Ret {
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

    fn visit_expression(&mut self, node: &Expression) -> Self::Ret {
        self.evaluate_for_stmt(&node.expression)?;
        Continue(())
    }

    fn visit_function(&mut self, node: &Function) -> Self::Ret {
        let function = lox_types::Function::new(node, self.env.clone());
        self.env.define(node.name.lexeme(), function.into());
        Continue(())
    }

    fn visit_if(&mut self, node: &If) -> Self::Ret {
        if self.evaluate_for_stmt(&node.condition)?.is_truthy() {
            self.execute(&node.thenBranch)
        } else if let Some(els) = &node.elseBranch {
            self.execute(els)
        } else {
            Continue(())
        }
    }

    fn visit_print(&mut self, node: &Print) -> Self::Ret {
        let val = self.evaluate_for_stmt(&node.expression)?;
        println!("{}", val);
        Continue(())
    }

    fn visit_return(&mut self, node: &Return) -> Self::Ret {
        ControlFlow::Break(Ok(match &node.value {
            Some(v) => self.evaluate_for_stmt(v)?,
            None => LoxType::Nil,
        }))
    }

    fn visit_var(&mut self, node: &Var) -> Self::Ret {
        let value = self.evaluate_for_stmt(&node.initializer)?;
        self.env.define(node.name.lexeme(), value);
        Continue(())
    }

    fn visit_while(&mut self, node: &While) -> Self::Ret {
        while self.evaluate_for_stmt(&node.condition)?.is_truthy() {
            self.execute(&node.body)?;
        }
        Continue(())
    }
}

impl expr::ExprTypesVisitor for Interpreter {
    type Ret = Result<LoxType>;

    fn visit_assign(&mut self, node: &Assign) -> Self::Ret {
        let value = self.evaluate(&node.value)?;
        if let Some((depth, _)) = self.locals.get(&node.id) {
            self.env.assign_at(*depth, &node.name, value.clone())?;
        } else {
            self.globals.assign(&node.name, value.clone())?;
        }
        Ok(value)
    }

    fn visit_binary(&mut self, node: &Binary) -> Self::Ret {
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

    fn visit_call(&mut self, node: &Call) -> Self::Ret {
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

    fn visit_get(&mut self, node: &Get) -> Self::Ret {
        if let LoxType::Instance(object) = self.evaluate(&node.object)? {
            Ok(object.get(&node.name)?)
        } else {
            bail!(
                "Only instances have properties.\n[line {}]",
                node.name.line()
            )
        }
    }

    fn visit_grouping(&mut self, node: &Grouping) -> Self::Ret {
        node.expression.accept(self)
    }

    fn visit_literal(&mut self, node: &Literal) -> Self::Ret {
        Ok(LoxType::from_literal(&node.value))
    }

    fn visit_logical(&mut self, node: &Logical) -> Self::Ret {
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

    fn visit_set(&mut self, node: &Set) -> Self::Ret {
        if let LoxType::Instance(mut obj) = self.evaluate(&node.object)? {
            let value = self.evaluate(&node.value)?;
            obj.set(&node.name, value.clone());
            Ok(value)
        } else {
            bail!("Only instances have fields.\n[line {}]", node.name.line())
        }
    }

    fn visit_super(&mut self, node: &Super) -> Self::Ret {
        let (distance, _slot) = self
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

    fn visit_this(&mut self, node: &This) -> Self::Ret {
        self.lookup_variable(&node.keyword, node.id)
    }

    fn visit_unary(&mut self, node: &Unary) -> Self::Ret {
        let right = node.right.accept(self)?;

        match node.operator.tok_type() {
            TokenType::Minus => right.as_f64().map(|f| (-f).into()).with_context(|| {
                format!("Operand must be a number.\n[line {}]", node.operator.line())
            }),
            TokenType::Bang => Ok((!right.is_truthy()).into()),
            _ => unreachable!(),
        }
    }

    fn visit_variable(&mut self, node: &Variable) -> Self::Ret {
        self.lookup_variable(&node.name, node.id)
    }
}
