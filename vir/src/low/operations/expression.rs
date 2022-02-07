use super::ty::Typed;
use crate::low::ast::expression::{visitors::ExpressionFolder, *};

impl From<VariableDecl> for Expression {
    fn from(variable: VariableDecl) -> Self {
        Self::local_no_pos(variable)
    }
}

impl Expression {
    pub fn function_call<S: Into<String>>(
        name: S,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{}", i),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::func_app_no_pos(name.into(), arguments, parameters, return_type)
    }
    pub fn domain_function_call(
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{}", i),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::domain_func_app_no_pos(
            domain_name.to_string(),
            function_name.to_string(),
            arguments,
            parameters,
            return_type,
        )
    }
    #[must_use]
    pub fn set_default_position(self, new_position: Position) -> Self {
        struct DefaultPositionReplacer {
            new_position: Position,
        }
        impl ExpressionFolder for DefaultPositionReplacer {
            fn fold_position(&mut self, position: Position) -> Position {
                if position.is_default() {
                    self.new_position
                } else {
                    position
                }
            }
        }
        DefaultPositionReplacer { new_position }.fold_expression(self)
    }
}
