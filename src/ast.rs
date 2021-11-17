use crate::scanner::Token;

use crate::parser::Ast;
use std::fmt::Write;

#[derive(Debug)]
pub enum LoxValue {
    Bool(bool),
    Nil,
    Number(f64),
    String(String),
}

pub trait Expr {
    fn accept(&self, visitor: &mut dyn AstVisitor);
}

impl Expr for Box<dyn Expr> {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        (**self).accept(visitor)
    }
}

impl<E> Expr for &Box<E>
where
    E: Expr,
{
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        E::accept(self, visitor)
    }
}

#[allow(unused_variables)]
pub trait AstVisitor {
    fn binary_expr(&mut self, bin: &Binary) {}
    fn grouping_expr(&mut self, grp: &Grouping) {}
    fn literal_expr(&mut self, lit: &Literal) {}
    fn unary_expr(&mut self, unary: &Unary) {}
}

pub type SubExpr = Box<dyn Expr>;

pub struct Binary {
    pub left: SubExpr,
    pub operator: Token,
    pub right: SubExpr,
}

impl Binary {
    pub fn boxed(left: SubExpr, operator: Token, right: SubExpr) -> Box<Self> {
        Box::new(Self {
            left,
            operator,
            right,
        })
    }
}

impl Expr for Binary {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.binary_expr(self)
    }
}

pub struct Grouping {
    pub expression: SubExpr,
}

impl Grouping {
    pub fn boxed(expression: SubExpr) -> Box<Self> {
        Box::new(Self { expression })
    }
}

impl Expr for Grouping {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.grouping_expr(self);
    }
}

#[derive(Debug)]
pub struct Literal {
    pub value: LoxValue,
}

impl Literal {
    pub fn boxed(value: LoxValue) -> Box<Self> {
        Box::new(Self { value })
    }
}

impl Expr for Literal {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.literal_expr(self);
    }
}

pub struct Unary {
    pub operator: Token,
    pub right: SubExpr,
}

impl Unary {
    pub fn boxed(operator: Token, right: SubExpr) -> Box<Self> {
        Box::new(Self { operator, right })
    }
}

impl Expr for Unary {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.unary_expr(self);
    }
}

pub struct AstPrinter {
    tree_str: String,
}

impl AstPrinter {
    pub fn print(ast: &Ast) -> String {
        let mut s = Self {
            tree_str: String::new(),
        };
        ast.accept(&mut s);
        s.tree_str
    }

    fn head(&mut self, name: &str) {
        self.tree_str.push('(');
        self.tree_str.push_str(name);
    }

    fn mid(&mut self, visitable: &dyn Expr) {
        self.tree_str.push(' ');
        visitable.accept(self)
    }

    fn tail(&mut self, visitable: &dyn Expr) {
        self.mid(visitable);
        self.tree_str.push(')');
    }
}

impl AstVisitor for AstPrinter {
    fn binary_expr(&mut self, bin: &Binary) {
        self.head(bin.operator.lexeme());
        self.mid(&bin.left);
        self.tail(&bin.right);
    }

    fn grouping_expr(&mut self, grp: &Grouping) {
        self.head("group");
        self.tail(&grp.expression);
    }

    fn literal_expr(&mut self, lit: &Literal) {
        let _ = write!(self.tree_str, "{:?}", lit);
    }

    fn unary_expr(&mut self, unary: &Unary) {
        self.head(unary.operator.lexeme());
        self.tail(&unary.right);
    }
}
