#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(trait_type=std::cmp::PartialEq,ignore=[position]),
    Eq,
    Hash(trait_type=core::hash::Hash,ignore=[position])
)]
#![derive_for_all_structs(new, new_with_pos)]

copy_module!(crate::typed::ast::expression);
copy_module!(crate::typed::ast::field);
copy_module!(crate::typed::ast::function);
copy_module!(crate::typed::ast::position);
copy_module!(crate::typed::ast::predicate);
pub mod statement;
copy_module!(crate::typed::ast::ty);
copy_module!(crate::typed::ast::type_decl);
copy_module!(crate::typed::ast::variable);
pub mod rvalue;

pub use self::{
    expression::Expression, function::FunctionDecl, statement::Statement, type_decl::TypeDecl,
};
