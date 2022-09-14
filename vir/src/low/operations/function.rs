use super::super::ast::{function::FunctionDecl, variable::VariableDecl};

impl FunctionDecl {
    pub fn result_variable(&self) -> VariableDecl {
        VariableDecl::result_variable(self.return_type.clone())
    }
}
