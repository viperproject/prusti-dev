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
            variable.name == "discriminant$"
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
        self.name == "discriminant"
    }
}
