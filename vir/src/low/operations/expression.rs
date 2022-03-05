use super::ty::Typed;
use crate::low::ast::expression::{
    visitors::{default_fold_expression, ExpressionFolder},
    *,
};

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
    pub fn is_place(&self) -> bool {
        match self {
            Expression::Local(_) => true,
            Expression::Field(Field { base, .. })
            | Expression::LabelledOld(LabelledOld { base, .. }) => base.is_place(),
            _ => false,
        }
    }
    #[must_use]
    pub fn replace_place(self, target: &Expression, replacement: &Expression) -> Self {
        debug_assert!(target.is_place());
        assert_eq!(
            target.get_type(),
            replacement.get_type(),
            "{} → {}",
            target,
            replacement
        );
        struct PlaceReplacer<'a> {
            target: &'a Expression,
            replacement: &'a Expression,
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_place() && &expression == self.target {
                    self.replacement.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
        }
        let mut replacer = PlaceReplacer {
            target,
            replacement,
        };
        replacer.fold_expression(self)
    }
    #[must_use]
    pub fn replace_discriminant(self, new_discriminant: &Expression) -> Self {
        struct DiscriminantReplacer<'a> {
            new_discriminant: &'a Expression,
        }
        impl<'a> ExpressionFolder for DiscriminantReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_discriminant() {
                    self.new_discriminant.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
        }
        let mut replacer = DiscriminantReplacer { new_discriminant };
        replacer.fold_expression(self)
    }
}
