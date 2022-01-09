use super::{super::super::ast::function::FunctionDecl, common::append_type_arguments};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for FunctionDecl {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        append_type_arguments(&mut identifier, &self.type_arguments);
        identifier
    }
}
