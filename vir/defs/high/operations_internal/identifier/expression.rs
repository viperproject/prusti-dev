use super::{super::super::ast::expression::FuncApp, common::append_type_arguments};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for FuncApp {
    fn get_identifier(&self) -> String {
        let mut identifier = self.function_name.clone();
        append_type_arguments(&mut identifier, &self.type_arguments);
        identifier
    }
}
