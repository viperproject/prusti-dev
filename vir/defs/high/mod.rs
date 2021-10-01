#![derive_for_all(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]

pub mod expression;
pub mod function;
pub mod position;
pub mod typ;
pub mod variable;

pub use self::expression::Expression;
