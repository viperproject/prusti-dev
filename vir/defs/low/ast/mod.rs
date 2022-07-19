#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(ignore=[position]),
    Eq,
    Hash(ignore=[position])
)]
#![derive_for_all_structs(new, new_with_pos)]

pub mod expression;
pub mod field;
pub mod function;
pub mod position;
pub mod predicate;
pub mod statement;
pub mod ty;
pub mod variable;

pub use self::{expression::Expression, function::FunctionDecl, statement::Statement};
