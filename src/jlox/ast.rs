#![allow(non_snake_case)]

use std::fmt::{Debug, Formatter};
use std::sync::atomic::{AtomicU64, Ordering};

use paste::paste;

use crate::jlox::LoxType;
use crate::scanner::Token;

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

        paste!{
        pub trait [< $enum_name Visitor >] {
            type Ret;
           $( fn [<visit_ $node_type:snake>] (&mut self, node: & $node_type) -> Self::Ret; )+
        }

        impl $enum_name {
            pub fn accept_visitor<V: [<$enum_name Visitor>]>(&self, visitor: &mut V) -> V::Ret {
                match self {
                    $(Self::$node_type(typ) => visitor.[<visit_ $node_type:snake>] (typ) ),+
                }
            }
        }
        impl<V:[<$enum_name Visitor>]> Accepts<V, V::Ret> for Box<$enum_name> {
            fn accept(&self, visitor: &mut V) -> V::Ret {
                match **self {
                    $(
                    $enum_name::$node_type(ref node) => visitor.[<visit_ $node_type:snake>](node)
                    ),+
                }
            }
        }

        $(
        impl <V: [<$enum_name Visitor>]> Accepts<V, V::Ret> for $node_type 
        {
            fn accept(&self, visitor: &mut V) -> V::Ret {
                visitor.[<visit_ $node_type:snake>](self)
            }
        }
        )+
        }

        $(
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
