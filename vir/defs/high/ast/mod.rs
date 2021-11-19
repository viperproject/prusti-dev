#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    Serialize,
    Deserialize,
    PartialEq(ignore=[position]),
    Eq,
    Hash(ignore=[position])
)]
#![derive_for_all_structs(new, new_with_pos)]

pub mod expression;
pub mod field;
pub mod function;
pub mod position;
pub mod ty;
pub mod type_decl;
pub mod variable;
