use super::super::ast::{
    expression::{Expression, Local},
    field::FieldDecl,
    ty::{self, Type},
    variable::VariableDecl,
};
use crate::common::expression::{BinaryOperationHelpers, ExpressionIterator};

pub type DiscriminantValue = i128;

impl Expression {
    pub fn is_discriminant(&self) -> bool {
        if let Expression::Local(Local { variable, .. }) = self {
            variable.name == crate::common::builtin_constants::DISCRIMINANT_VARIABLE_NAME
        } else {
            false
        }
    }

    pub fn generate_discriminant_bounds(
        &self,
        bounds: &[(DiscriminantValue, DiscriminantValue)],
    ) -> Self {
        bounds
            .iter()
            .map(|&(from, to)| {
                if from == to {
                    Self::equals(self.clone(), from.into())
                } else {
                    Self::and(
                        Self::less_equals(from.into(), self.clone()),
                        Self::less_equals(self.clone(), to.into()),
                    )
                }
            })
            .disjoin()
    }
}

impl FieldDecl {
    pub fn is_discriminant(&self) -> bool {
        self.name == crate::common::builtin_constants::DISCRIMINANT_FIELD_NAME
    }
}

impl VariableDecl {
    pub fn result_variable(ty: Type) -> Self {
        VariableDecl::new(crate::common::builtin_constants::RESULT_VARIABLE_NAME, ty)
    }

    pub fn discriminant_variable() -> Self {
        VariableDecl::new(
            crate::common::builtin_constants::DISCRIMINANT_VARIABLE_NAME,
            Type::Int,
        )
    }

    pub fn is_result_variable(&self) -> bool {
        self.name == crate::common::builtin_constants::RESULT_VARIABLE_NAME
    }

    pub fn is_self_variable(&self) -> bool {
        self.name == crate::common::builtin_constants::SELF_VARIABLE_NAME
    }
}
