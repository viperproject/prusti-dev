use super::{
    super::super::{ast, ast::function::FunctionDecl},
    common::append_type_arguments,
};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for FunctionDecl {
    fn get_identifier(&self) -> String {
        compute_function_identifier(&self.name, &self.type_arguments)
    }
}

pub fn compute_function_identifier(name: &str, type_arguments: &[ast::ty::Type]) -> String {
    let mut identifier = name.to_string();
    append_type_arguments(&mut identifier, type_arguments);
    identifier
}
