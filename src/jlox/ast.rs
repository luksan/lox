#![allow(non_snake_case)]

use std::fmt::{Debug, Formatter};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::jlox::LoxType;
use crate::scanner::Token;

pub trait Visitor<NodeType, R> {
    fn visit(&mut self, node: &NodeType) -> R;
}

pub trait Accepts<V, R> {
    fn accept(&self, visitor: &mut V) -> R;
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(u64);

impl Debug for NodeId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl NodeId {
    fn new() -> Self {
        static ID_COUNTER: AtomicU64 = AtomicU64::new(0);
        Self(ID_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

macro_rules! ast_nodes {
    { [$enum_name:ident] $($node_type:ident : $($member_type:ident $member_name:ident),* ; )+ } => {
        #[derive(Clone)]
        pub enum $enum_name {
            $( $node_type ( $node_type ) ),+
        }

        impl Debug for $enum_name {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(Self::$node_type(typ) => typ.fmt(f) ),+
                }
            }
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

        impl<V, R> Accepts<V, R> for Box<$enum_name> where
                $( V: Visitor<$node_type, R> ),+ {
            fn accept(&self, visitor: &mut V) -> R {
                use $enum_name::*;
                    match **self {
                        $($node_type(ref typ) => visitor.visit(typ) ),+
                    }
            }
        }

        $(
        impl<V, R> Accepts<V, R> for $node_type where
            V: Visitor<$node_type, R>  {
            fn accept(&self, visitor: &mut V) -> R {
                visitor.visit(self)
            }
        }

        #[derive(Clone, Debug)]
        pub struct $node_type {
            pub id: NodeId,
            $( pub $member_name: $member_type),*
        }

        impl $node_type {
            #[allow(clippy::new_ret_no_self)]
            pub fn new( $($member_name: $member_type),* ) -> Box<$enum_name> {
                Box::new( $enum_name::$node_type($node_type {
                    id: NodeId::new(),
                    $($member_name),*}))
            }

            /// Create a new AST node without wrapping it in the enum
            pub fn new_bare( $($member_name: $member_type),* ) -> Self {
                $node_type {
                    id: NodeId::new(),
                    $($member_name),*
                }
            }
        }

        impl From<$node_type> for Box<$enum_name> {
            fn from(val: $node_type) -> Self {
                Box::new($enum_name::$node_type(val))
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
        Call     : Expr callee, Token paren, ListExpr arguments;
        Get      : Expr object, Token name;
        Grouping : Expr expression;
        Literal  : Object value;
        Logical  : Expr left, Token operator, Expr right;
        Set      : Expr object, Token name, Expr value;
        Super    : Token keyword, Token method;
        This     : Token keyword;
        Unary    : Token operator, Expr right;
        Variable : Token name;
    }

    pub type Expr = Box<ExprTypes>;
    pub type ListExpr = Vec<Expr>;
    type Object = LoxType;
}

pub mod stmt {
    use super::*;
    use expr::Expr;

    ast_nodes! { [ StmtTypes ]
        Block      : ListStmt statements;
        Class      : Token name, OptionVar superclass, ListFunc methods;
        Expression : Expr expression;
        Function   : Token name, ListToken params, ListStmt body;
        If         : Expr condition, Stmt thenBranch, OptionStmt elseBranch;
        Print      : Expr expression;
        Return     : Token keyword, OptionExpr value;
        Var        : Token name, Expr initializer;
        While      : Expr condition, Stmt body;
    }

    pub type Stmt = Box<StmtTypes>;
    pub type ListStmt = Vec<Stmt>;
    type OptionExpr = Option<Expr>;
    type OptionStmt = Option<Stmt>;
    type ListToken = Vec<Token>;
    type ListFunc = Vec<Function>;
    type OptionVar = Option<expr::Variable>;
}
