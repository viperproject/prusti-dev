copy_module!(crate::high::operations_internal::identifier::common);
copy_module!(crate::high::operations_internal::identifier::expression);
copy_module!(crate::high::operations_internal::identifier::function);
copy_module!(crate::high::operations_internal::identifier::predicate);
copy_module!(crate::high::operations_internal::identifier::rvalue);
mod ty;

pub use function::compute_function_identifier;
