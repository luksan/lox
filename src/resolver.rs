use anyhow::anyhow;
use std::collections::HashMap;

use crate::ast::expr::{Binary, Call, Expr, Get, Grouping, Literal, Logical, Unary, Variable};
use crate::ast::stmt::{Expression, If, Print, Return, While};
use crate::ast::{
    expr,
    stmt::{self, ListStmt, Stmt},
    NodeId, Visitor,
};

use crate::scanner::Token;
use crate::Interpreter;

pub struct Resolver {
    interpreter: Interpreter,
    curr_func_type: FunctionType,
    scopes: Vec<HashMap<String, bool>>,
    errors: Vec<anyhow::Error>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum FunctionType {
    Function,
    Method,
    None,
}

impl Resolver {
    pub fn resolve(
        interpreter: Interpreter,
        statements: &ListStmt,
    ) -> (Interpreter, Vec<anyhow::Error>) {
        let mut me = Self {
            interpreter,
            curr_func_type: FunctionType::None,
            scopes: vec![],
            errors: vec![],
        };

        me.resolve_stmt_list(statements);

        (me.interpreter, me.errors)
    }

    fn error(&mut self, token: &Token, desc: &str) {
        let err = anyhow!("{:?} {}", token, desc);
        eprintln!("{}", err);
        self.errors.push(err);
    }

    fn peek(&mut self) -> Option<&mut HashMap<String, bool>> {
        self.scopes.last_mut()
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, name: &Token) {
        if let Some(scope) = self.scopes.last_mut() {
            if let Some(_exists) = scope.insert(name.lexeme().to_string(), false) {
                // Variable already declared
                self.error(name, "Already a variable with this name in this scope.");
            }
        }
    }

    fn define(&mut self, name: &Token) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(name.lexeme().to_string(), true));
    }

    fn resolve_stmt_list(&mut self, statements: &ListStmt) -> Ret {
        for s in statements {
            self.resolve_stmt(s);
        }
    }
    fn resolve_stmt(&mut self, statement: &Stmt) -> Ret {
        statement.accept(self)
    }
    fn resolve_function(&mut self, fun: &stmt::Function, typ: FunctionType) {
        let prev_func = self.curr_func_type;
        self.curr_func_type = typ;

        self.begin_scope();
        for param in &fun.params {
            self.declare(param);
            self.define(param);
        }
        self.resolve_stmt_list(&fun.body);
        self.end_scope();

        self.curr_func_type = prev_func;
    }

    fn resolve_expr(&mut self, expr: &Expr) -> Ret {
        expr.accept(self)
    }

    fn resolve_local(&mut self, expr: NodeId, name: &Token) {
        for (idx, scope) in self.scopes.iter().rev().enumerate() {
            if scope.contains_key(name.lexeme()) {
                self.interpreter.resolve(expr, idx);
                return;
            }
        }
    }
}

pub enum ExprRef<'a> {
    Assign(&'a expr::Assign),
    Variable(&'a expr::Variable),
}

impl<'a> From<&'a expr::Assign> for ExprRef<'a> {
    fn from(val: &'a expr::Assign) -> Self {
        Self::Assign(val)
    }
}

impl<'a> From<&'a expr::Variable> for ExprRef<'a> {
    fn from(val: &'a Variable) -> Self {
        Self::Variable(val)
    }
}

type Ret = ();

impl Visitor<stmt::Block, Ret> for Resolver {
    fn visit(&mut self, node: &stmt::Block) -> Ret {
        self.begin_scope();
        self.resolve_stmt_list(&node.statements);
        self.end_scope();
    }
}

impl Visitor<stmt::Class, Ret> for Resolver {
    fn visit(&mut self, node: &stmt::Class) -> Ret {
        self.declare(&node.name);
        self.define(&node.name);

        for method in &node.methods {
            let decl = FunctionType::Method;
            self.resolve_function(method, decl);
        }
    }
}

impl Visitor<stmt::Expression, Ret> for Resolver {
    fn visit(&mut self, node: &Expression) -> Ret {
        self.resolve_expr(&node.expression);
    }
}

impl Visitor<stmt::Function, Ret> for Resolver {
    fn visit(&mut self, node: &stmt::Function) -> Ret {
        self.declare(&node.name);
        self.define(&node.name);

        self.resolve_function(node, FunctionType::Function);
    }
}

impl Visitor<stmt::If, Ret> for Resolver {
    fn visit(&mut self, node: &If) -> Ret {
        self.resolve_expr(&node.condition);
        self.resolve_stmt(&node.thenBranch);
        node.elseBranch.as_ref().map(|stmt| self.resolve_stmt(stmt));
    }
}

impl Visitor<stmt::Print, Ret> for Resolver {
    fn visit(&mut self, node: &Print) -> Ret {
        self.resolve_expr(&node.expression);
    }
}

impl Visitor<stmt::Return, Ret> for Resolver {
    fn visit(&mut self, node: &Return) -> Ret {
        if self.curr_func_type == FunctionType::None {
            self.error(&node.keyword, "Can't return from top-level code.");
        }
        self.resolve_expr(&node.value);
    }
}

impl Visitor<stmt::Var, Ret> for Resolver {
    fn visit(&mut self, node: &stmt::Var) -> Ret {
        self.declare(&node.name);
        self.resolve_expr(&node.initializer);
        self.define(&node.name);
    }
}

impl Visitor<stmt::While, Ret> for Resolver {
    fn visit(&mut self, node: &While) -> Ret {
        self.resolve_expr(&node.condition);
        self.resolve_stmt(&node.body);
    }
}

impl Visitor<expr::Assign, Ret> for Resolver {
    fn visit(&mut self, node: &expr::Assign) -> Ret {
        self.resolve_expr(&node.value);
        self.resolve_local(node.id, &node.name)
    }
}

impl Visitor<expr::Binary, Ret> for Resolver {
    fn visit(&mut self, node: &Binary) -> Ret {
        self.resolve_expr(&node.left);
        self.resolve_expr(&node.right);
    }
}

impl Visitor<expr::Call, Ret> for Resolver {
    fn visit(&mut self, node: &Call) -> Ret {
        self.resolve_expr(&node.callee);
        for arg in &node.arguments {
            self.resolve_expr(arg);
        }
    }
}

impl Visitor<expr::Get, Ret> for Resolver {
    fn visit(&mut self, node: &Get) -> Ret {
        self.resolve_expr(&node.object);
    }
}

impl Visitor<expr::Grouping, Ret> for Resolver {
    fn visit(&mut self, node: &Grouping) -> Ret {
        self.resolve_expr(&node.expression);
    }
}

impl Visitor<expr::Literal, Ret> for Resolver {
    fn visit(&mut self, _node: &Literal) -> Ret {}
}

impl Visitor<expr::Logical, Ret> for Resolver {
    fn visit(&mut self, node: &Logical) -> Ret {
        self.resolve_expr(&node.left);
        self.resolve_expr(&node.right);
    }
}

impl Visitor<expr::Set, Ret> for Resolver {
    fn visit(&mut self, node: &expr::Set) -> Ret {
        self.resolve_expr(&node.value);
        self.resolve_expr(&node.object);
    }
}

impl Visitor<expr::Unary, Ret> for Resolver {
    fn visit(&mut self, node: &Unary) -> Ret {
        self.resolve_expr(&node.right)
    }
}

impl Visitor<expr::Variable, Ret> for Resolver {
    fn visit(&mut self, node: &expr::Variable) -> Ret {
        if self
            .peek()
            .map(|scope| scope.get(node.name.lexeme()) == Some(&false))
            == Some(true)
        {
            self.error(
                &node.name,
                "Can't read local variable in its own initializer.",
            );
        }
        self.resolve_local(node.id, &node.name)
    }
}
