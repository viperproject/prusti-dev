copy_module!(crate::high::operations_internal::const_generics::ty);
mod type_decl;
copy_module!(crate::high::operations_internal::const_generics::common);

pub trait WithConstArguments {
    fn get_const_arguments(&self) -> Vec<super::super::ast::expression::Expression>;
}
