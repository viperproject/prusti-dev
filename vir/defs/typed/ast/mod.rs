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

copy_module!(crate::high::ast::expression);
copy_module!(crate::high::ast::field);
copy_module!(crate::high::ast::function);
copy_module!(crate::high::ast::position);
copy_module!(crate::high::ast::predicate);
copy_module!(crate::high::ast::statement);
pub mod ty;
pub mod type_decl;
copy_module!(crate::high::ast::variable);
copy_module!(crate::high::ast::rvalue);
