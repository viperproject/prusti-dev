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
            self, BinaryOpKind, ConstantValue, ContainerOpKind, Expression, Trigger, UnaryOpKind,
        },
        field::FieldDecl,
        function::{FunctionDecl, FunctionKind},
        position::Position,
        predicate::{PredicateDecl, PredicateKind},
        statement::Statement,
        ty::{self, Type},
        variable::VariableDecl,
    },
    cfg::{BasicBlock, Label, MethodDecl, MethodKind, ProcedureDecl, Successor},
    domain::{DomainAxiomDecl, DomainDecl, DomainFunctionDecl},
    program::Program,
};
