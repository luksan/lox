use crate::scanner::{Token, TokenType};

use std::fmt::Write;

#[derive(Debug)]
pub enum LoxValue {
    Number(f64),
    String(String),
}

pub trait Expr {
    fn visit(&self, visitor: &mut dyn AstVisitor);
}

impl Visitee for &dyn Expr {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        self.visit(visitor);
    }
}

pub trait AstVisitor {
    fn binary_expr(&mut self, bin: &Binary<'_>) {}
    fn grouping_expr(&mut self, grp: &Grouping<'_>) {}
    fn literal_expr(&mut self, lit: Literal) {}
    fn unary_expr(&mut self, unary: Unary<'_>) {}
}

pub trait Visitee {
    fn accept(&self, visitor: &mut dyn AstVisitor);
}

struct Binary<'ast> {
    left: &'ast dyn Expr,
    operator: &'ast Token,
    right: &'ast dyn Expr,
}

struct Grouping<'ast> {
    expression: &'ast dyn Expr,
}

#[derive(Debug)]
struct Literal {
    value: LoxValue,
}

struct Unary<'ast> {
    operator: Token,
    right: &'ast dyn Expr,
}

macro_rules! ast_type {
    ($typename:ident, ($member:ident, :, )) => {};
}

struct AstPrinter {
    tree_str: String,
}

impl AstPrinter {
    fn head(&mut self, name: &str) {
        self.tree_str.push('(');
        self.tree_str.push_str(name);
    }

    fn mid(&mut self, visitable: impl Visitee) {
        self.tree_str.push(' ');
        visitable.accept(self)
    }

    fn tail(&mut self, visitable: impl Visitee) {
        self.mid(visitable);
        self.tree_str.push(')');
    }
}

impl AstVisitor for AstPrinter {
    fn binary_expr(&mut self, bin: &Binary<'_>) {
        self.head(bin.operator.lexeme());
        self.mid(bin.left);
        self.tail(bin.right);
    }

    fn grouping_expr(&mut self, grp: &Grouping<'_>) {
        self.head("group");
        self.tail(grp.expression);
    }

    fn literal_expr(&mut self, lit: Literal) {
        let _ = write!(self.tree_str, "{:?}", lit);
    }

    fn unary_expr(&mut self, unary: Unary<'_>) {
        self.head(unary.operator.lexeme());
        self.tail(unary.right);
    }
}
