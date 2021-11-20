use anyhow::{bail, Result};

use crate::scanner::Token;

use std::fmt::{Display, Formatter, Write};
use std::ops::Not;

#[derive(Clone, Debug, PartialEq)]
pub enum LoxValue {
    Bool(bool),
    Nil,
    Number(f64),
    String(String),
}

impl LoxValue {
    pub fn as_f64(&self) -> Result<f64> {
        match self {
            Self::Number(num) => Ok(*num),
            typ => bail!("{:?} is not a number", typ),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Nil => false,
            Self::Bool(b) => *b,
            _ => true,
        }
    }
}

impl Display for LoxValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            LoxValue::Nil => write!(f, "nil"),
            LoxValue::Number(num) => {
                if num.trunc() == *num {
                    // check if decimal part is zero
                    write!(f, "{:.0}", num)
                } else {
                    write!(f, "{}", num)
                }
            }
            LoxValue::String(s) => write!(f, "{}", s),
        }
    }
}

impl Not for LoxValue {
    type Output = LoxValue;

    fn not(self) -> Self::Output {
        LoxValue::Bool(!self.is_truthy())
    }
}

impl From<bool> for LoxValue {
    fn from(b: bool) -> Self {
        LoxValue::Bool(b)
    }
}

impl From<f64> for LoxValue {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}

pub trait Visitor<NodeType, R> {
    fn visit(&mut self, node: &NodeType) -> R;
}

pub trait TypeMap<Inner> {
    fn map(self, f: impl FnOnce(Inner) -> Self) -> Self;
    fn map_or_else(self, f: impl FnOnce(Inner) -> Self, dflt: impl FnOnce(Self) -> Self) -> Self
    where
        Self: Sized;
}

impl<T, Inner> TypeMap<Inner> for T
where
    T: Sized,
    Inner: TryFrom<T>,
    <Inner as TryFrom<T>>::Error: Into<T>,
{
    fn map(self, f: impl FnOnce(Inner) -> T) -> T {
        match self.try_into() {
            Ok(inner) => f(inner),
            Err(slf) => slf.into(),
        }
    }

    fn map_or_else(self, f: impl FnOnce(Inner) -> Self, dflt: impl FnOnce(Self) -> Self) -> Self {
        match self.try_into() {
            Ok(inner) => f(inner),
            Err(slf) => dflt(slf.into()),
        }
    }
}

macro_rules! ast_nodes {
    { [$enum_name:ident] $($node_type:ident : $($member_type:ident $member_name:ident),* ; )+ } => {
        #[derive(Clone, Debug)]
        pub enum $enum_name {
            $( $node_type ( $node_type ) ),+
        }

        impl $enum_name {
            pub fn accept<V, R>(&self, visitor: &mut V) -> R where
                $( V: Visitor<$node_type, R> ),+ {
                use $enum_name::*;
                    match self {
                        $($node_type(typ) => visitor.visit(typ) ),+
                    }
            }
        }

        $(
        #[derive(Clone, Debug)]
        pub struct $node_type {
            $( pub $member_name: $member_type),*
        }

        impl $node_type {
            pub fn new( $($member_name: $member_type),* ) -> Box<$enum_name> {
                Box::new( $enum_name::$node_type($node_type { $($member_name),*}))
            }
        }

        impl TryFrom<$enum_name> for $node_type {
            type Error = $enum_name;
            fn try_from(value: $enum_name) -> Result<Self, Self::Error> {
                match value {
                    $enum_name::$node_type(me) => Ok(me),
                    _ => Err(value),
                }
            }
        }

        impl TryFrom<Box<$enum_name>> for $node_type {
            type Error = Box<$enum_name>;
            fn try_from(value: Box<$enum_name>) -> Result<Self, Self::Error> {
                match *value {
                    $enum_name::$node_type(me) => Ok(me),
                    _ => Err(value),
                }
            }
        }
        )+
    };
}

pub mod expr {
    use super::*;

    ast_nodes! { [ ExprTypes ]
        Assign   : Token name, Expr value;
        Binary   : Expr left, Token operator, Expr right;
        Grouping : Expr expression;
        Literal  : Object value;
        Unary    : Token operator, Expr right;
        Variable : Token name;
    }

    pub type Expr = Box<ExprTypes>;
    pub type Object = LoxValue;
}

pub mod stmt {
    use super::*;

    ast_nodes! { [ StmtTypes ]
        Block      : ListStmt statements;
        Expression : Expr expression;
        Print      : Expr expression;
        Var        : Token name, Expr initializer;
    }

    pub type Stmt = Box<StmtTypes>;
    pub type ListStmt = Vec<Stmt>;
}

pub struct AstPrinter {
    tree_str: String,
}

use expr::Expr;

impl AstPrinter {
    pub fn print(ast: &Expr) -> String {
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

    fn mid(&mut self, visitable: &Expr) {
        self.tree_str.push(' ');
        visitable.accept(self)
    }

    fn tail(&mut self, visitable: &Expr) {
        self.mid(visitable);
        self.tree_str.push(')');
    }
}

impl Visitor<expr::Assign, ()> for AstPrinter {
    fn visit(&mut self, node: &expr::Assign) -> () {
        self.head(node.name.lexeme());
        self.tail(&node.value)
    }
}
impl Visitor<expr::Binary, ()> for AstPrinter {
    fn visit(&mut self, bin: &expr::Binary) -> () {
        self.head(bin.operator.lexeme());
        self.mid(&bin.left);
        self.tail(&bin.right);
    }
}
impl Visitor<expr::Grouping, ()> for AstPrinter {
    fn visit(&mut self, grp: &expr::Grouping) -> () {
        self.head("group");
        self.tail(&grp.expression);
    }
}

impl Visitor<expr::Literal, ()> for AstPrinter {
    fn visit(&mut self, lit: &expr::Literal) -> () {
        let _ = write!(self.tree_str, "{:?}", lit);
    }
}
impl Visitor<expr::Unary, ()> for AstPrinter {
    fn visit(&mut self, unary: &expr::Unary) -> () {
        self.head(unary.operator.lexeme());
        self.tail(&unary.right);
    }
}

impl Visitor<expr::Variable, ()> for AstPrinter {
    fn visit(&mut self, _node: &expr::Variable) -> () {
        self.head("var TODO)");
    }
}
