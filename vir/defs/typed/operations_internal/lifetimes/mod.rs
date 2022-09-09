mod ty;
mod type_decl;
copy_module!(crate::high::operations_internal::lifetimes::common);

pub trait WithLifetimes {
    fn get_lifetimes(&self) -> Vec<super::super::ast::ty::LifetimeConst>;
}
