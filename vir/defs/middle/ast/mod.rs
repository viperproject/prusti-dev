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

copy_module!(crate::high::ast::expression);
copy_module!(crate::high::ast::field);
copy_module!(crate::high::ast::function);
copy_module!(crate::high::ast::position);
copy_module!(crate::high::ast::predicate);
pub mod statement;
copy_module!(crate::high::ast::ty);
copy_module!(crate::high::ast::type_decl);
copy_module!(crate::high::ast::variable);
copy_module!(crate::high::ast::rvalue);

pub use self::{
    expression::Expression, function::FunctionDecl, statement::Statement, type_decl::TypeDecl,
};
