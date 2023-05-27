//! Monomorphic IR that is very close to Viper and can be directly converted
//! into it.

#![allow(clippy::write_with_newline)]

pub mod ast;
pub mod cfg;
pub mod domain;
pub mod program;

pub use self::{
    ast::{
        expression::{
            self, BinaryOp, BinaryOpKind, Conditional as ConditionalExpression, Constant,
            ConstantValue, ContainerOp, ContainerOpKind, DomainFuncApp, Expression, Field,
            FieldAccessPredicate, FuncApp, InhaleExhale, LabelledOld, LetExpr, Local, MagicWand,
            PermBinaryOp, PermBinaryOpKind, PredicateAccessPredicate, Quantifier, QuantifierKind,
            Trigger, UnaryOp, UnaryOpKind, Unfolding,
        },
        field::FieldDecl,
        function::{FunctionDecl, FunctionKind},
        position::Position,
        predicate::{PredicateDecl, PredicateKind},
        statement::{
            ApplyMagicWand, Assert, Assign, Assume, Comment, Conditional as ConditionalStatement,
            Exhale, Fold, Inhale, Label as LabelStatement, LogEvent, MaterializePredicate,
            MethodCall, Statement, Unfold,
        },
        ty::{self, Type},
        variable::VariableDecl,
    },
    cfg::{BasicBlock, Label, MethodDecl, MethodKind, ProcedureDecl, Successor},
    domain::{DomainAxiomDecl, DomainDecl, DomainFunctionDecl, DomainRewriteRuleDecl},
    program::Program,
};
