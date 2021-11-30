#![allow(non_snake_case)]

use anyhow::Result;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::scanner::Token;
use crate::LoxType;

pub trait Visitor<NodeType, R> {
    fn visit(&mut self, node: &NodeType) -> R;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(u64);

impl NodeId {
    fn new() -> Self {
        static ID_COUNTER: AtomicU64 = AtomicU64::new(0);
        Self(ID_COUNTER.fetch_add(1, Ordering::SeqCst))
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
            pub id: NodeId,
            $( pub $member_name: $member_type),*
        }

        impl $node_type {
            pub fn new( $($member_name: $member_type),* ) -> Box<$enum_name> {
                Box::new( $enum_name::$node_type($node_type {
                    id: NodeId::new(),
                    $($member_name),*}))
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
        Call     : Expr callee, Token paren, ListExpr arguments;
        Get      : Expr object, Token name;
        Grouping : Expr expression;
        Literal  : Object value;
        Logical  : Expr left, Token operator, Expr right;
        Set      : Expr object, Token name, Expr value;
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
        Class      : Token name, ListStmt methods;
        Expression : Expr expression;
        Function   : Token name, ListToken params, ListStmt body;
        If         : Expr condition, Stmt thenBranch, OptionStmt elseBranch;
        Print      : Expr expression;
        Return     : Token keyword, Expr value;
        Var        : Token name, Expr initializer;
        While      : Expr condition, Stmt body;
    }

    pub type Stmt = Box<StmtTypes>;
    pub type ListStmt = Vec<Stmt>;
    type OptionStmt = Option<Stmt>;
    type ListToken = Vec<Token>;
}
