#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(trait_type=std::cmp::PartialEq,ignore=[position, lifetimes, lifetime]),
    Eq,
    Hash(trait_type=core::hash::Hash,ignore=[position, lifetimes, lifetime]),
    Ord(trait_type=std::cmp::Ord,ignore=[position, lifetimes, lifetime]),
)]
#![derive_for_all_structs(new, new_with_pos)]

pub mod expression;
pub mod field;
pub mod function;
pub mod position;
pub mod predicate;
pub mod rvalue;
pub mod statement;
pub mod ty;
pub mod type_decl;
pub mod variable;

pub use self::{
    expression::Expression, function::FunctionDecl, statement::Statement, type_decl::TypeDecl,
};
