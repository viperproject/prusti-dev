use super::super::ast::{
    expression::{Expression, Local},
    field::FieldDecl,
    ty::{self, Type},
    variable::VariableDecl,
};

impl Expression {
    pub fn is_discriminant(&self) -> bool {
        if let Expression::Local(Local { variable, .. }) = self {
            variable.name == "discriminant$"
        } else {
            false
        }
    }
}

impl FieldDecl {
    pub fn is_discriminant(&self) -> bool {
        self.name == "discriminant"
    }
}
