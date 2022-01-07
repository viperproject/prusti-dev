//! Monomorphic IR that is very close to Viper and can be directly converted
//! into it.

pub mod ast;
pub mod cfg;
pub(crate) mod derived_operations;
pub mod program;

pub use self::{
    ast::{expression::Expression, position::Position, ty::Type, variable::VariableDecl},
    program::Program,
};
