use crate::low::ast::expression::*;

impl From<VariableDecl> for Expression {
    fn from(variable: VariableDecl) -> Self {
        Self::local_no_pos(variable)
    }
}
