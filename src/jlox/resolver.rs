#![allow(clippy::ptr_arg)]

use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};

use crate::jlox::ast::expr::{Assign, Binary, Call, Get, Grouping, Literal, Logical, Set, Super, This, Unary, Variable};
use crate::jlox::ast::stmt::{Block, Class, Expression, Function, If, Print, Return, Var, While};
use crate::jlox::ast::{expr, stmt::{self, ListStmt, Stmt}, Accepts, NodeId};
use crate::jlox::Interpreter;
use crate::scanner::Token;

#[derive(Debug)]
pub struct ResolverError {
    token: Token,
    msg: String,
}
impl Error for ResolverError {}
impl Display for ResolverError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} {}", self.token, self.msg)
    }
}

pub struct Resolver<'i> {
    interpreter: &'i mut Interpreter,
    curr_func_type: FunctionType,
    curr_class: ClassType,
    scopes: Vec<HashMap<String, bool>>,
    errors: Vec<ResolverError>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum FunctionType {
    Initializer,
    Function,
    Method,
    None,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ClassType {
    Class,
    Subclass,
    None,
}

impl<'i> Resolver<'i> {
    pub fn resolve(
        interpreter: &'i mut Interpreter,
        statements: &ListStmt,
    ) -> Result<(), Vec<ResolverError>> {
        let mut me = Self {
            interpreter,
            curr_func_type: FunctionType::None,
            curr_class: ClassType::None,
            scopes: vec![],
            errors: vec![],
        };

        me.resolve_stmt_list(statements);

        if me.errors.is_empty() {
            Ok(())
        } else {
            Err(me.errors)
        }
    }

    fn error(&mut self, token: &Token, desc: &str) {
        self.errors.push(ResolverError {
            token: token.clone(),
            msg: desc.to_string(),
        });
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

    fn resolve_stmt_list(&mut self, statements: &ListStmt) {
        for s in statements {
            self.resolve_stmt(s);
        }
    }
    fn resolve_stmt(&mut self, statement: &Stmt) {
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

    fn resolve_expr(&mut self, expr: &dyn Accepts<Self, ()>) {
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

impl stmt::StmtTypesVisitor for Resolver<'_> {
    type Ret = ();

    fn visit_block(&mut self, node: &Block) -> Self::Ret {
        self.begin_scope();
        self.resolve_stmt_list(&node.statements);
        self.end_scope();
    }

    fn visit_class(&mut self, node: &Class) -> Self::Ret {
        let enclosing_class = self.curr_class;
        self.curr_class = ClassType::Class;

        self.declare(&node.name);
        self.define(&node.name);

        if let Some(sup) = &node.superclass {
            if sup.name.lexeme() == node.name.lexeme() {
                self.error(&sup.name, "A class can't inherit from itself.")
            }
            self.curr_class = ClassType::Subclass;
            self.resolve_expr(sup);
            self.begin_scope(); // "super" env
            self.scopes
                .last_mut()
                .unwrap()
                .insert("super".to_string(), true);
        }
        self.begin_scope();
        self.scopes
            .last_mut()
            .unwrap()
            .insert("this".to_string(), true);

        for method in &node.methods {
            let decl = if method.name.lexeme() == "init" {
                FunctionType::Initializer
            } else {
                FunctionType::Method
            };
            self.resolve_function(method, decl);
        }
        self.end_scope();
        if node.superclass.is_some() {
            self.end_scope();
        }
        self.curr_class = enclosing_class;
    }

    fn visit_expression(&mut self, node: &Expression) -> Self::Ret {
        self.resolve_expr(&node.expression);
    }

    fn visit_function(&mut self, node: &Function) -> Self::Ret {
        self.declare(&node.name);
        self.define(&node.name);

        self.resolve_function(node, FunctionType::Function);
    }

    fn visit_if(&mut self, node: &If) -> Self::Ret {
        self.resolve_expr(&node.condition);
        self.resolve_stmt(&node.thenBranch);
        if let Some(stmt) = &node.elseBranch {
            self.resolve_stmt(stmt);
        }
    }

    fn visit_print(&mut self, node: &Print) -> Self::Ret {
        self.resolve_expr(&node.expression);
    }

    fn visit_return(&mut self, node: &Return) -> Self::Ret {
        if self.curr_func_type == FunctionType::None {
            self.error(&node.keyword, "Can't return from top-level code.");
        }
        if self.curr_func_type == FunctionType::Initializer && node.value.is_some() {
            self.error(&node.keyword, "Can't return a value from an initializer.")
        }
        if let Some(expr) = &node.value {
            self.resolve_expr(expr);
        }
    }

    fn visit_var(&mut self, node: &Var) -> Self::Ret {
        self.declare(&node.name);
        self.resolve_expr(&node.initializer);
        self.define(&node.name);
    }

    fn visit_while(&mut self, node: &While) -> Self::Ret {
        self.resolve_expr(&node.condition);
        self.resolve_stmt(&node.body);
    }
}

impl expr::ExprTypesVisitor for Resolver<'_> {
    type Ret = ();

    fn visit_assign(&mut self, node: &Assign) -> Self::Ret {
        self.resolve_expr(&node.value);
        self.resolve_local(node.id, &node.name)
    }

    fn visit_binary(&mut self, node: &Binary) -> Self::Ret {
        self.resolve_expr(&node.left);
        self.resolve_expr(&node.right);
    }

    fn visit_call(&mut self, node: &Call) -> Self::Ret {
        self.resolve_expr(&node.callee);
        for arg in &node.arguments {
            self.resolve_expr(arg);
        }
    }

    fn visit_get(&mut self, node: &Get) -> Self::Ret {
        self.resolve_expr(&node.object);
    }

    fn visit_grouping(&mut self, node: &Grouping) -> Self::Ret {
        self.resolve_expr(&node.expression);
    }

    fn visit_literal(&mut self, _node: &Literal) -> Self::Ret {}

    fn visit_logical(&mut self, node: &Logical) -> Self::Ret {
        self.resolve_expr(&node.left);
        self.resolve_expr(&node.right);
    }

    fn visit_set(&mut self, node: &Set) -> Self::Ret {
        self.resolve_expr(&node.value);
        self.resolve_expr(&node.object);
    }

    fn visit_super(&mut self, node: &Super) -> Self::Ret {
        match &self.curr_class {
            ClassType::Class => self.error(
                &node.keyword,
                "Can't use 'super' in a class with no superclass.",
            ),
            ClassType::Subclass => self.resolve_local(node.id, &node.keyword),
            ClassType::None => self.error(&node.keyword, "Can't use 'super' outside of a class."),
        }
    }

    fn visit_this(&mut self, node: &This) -> Self::Ret {
        if self.curr_class == ClassType::None {
            self.error(&node.keyword, "Can't use 'this' outside of a class.");
            return;
        }
        self.resolve_local(node.id, &node.keyword)
    }

    fn visit_unary(&mut self, node: &Unary) -> Self::Ret {
        self.resolve_expr(&node.right)
    }

    fn visit_variable(&mut self, node: &Variable) -> Self::Ret {
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
