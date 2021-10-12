use super::super::ast::{
    expression::{Expression, Local},
    field::FieldDecl,
    ty::{self, Type},
    variable::VariableDecl,
};

impl Expression {
    pub fn discriminant() -> Self {
        let variable = VariableDecl::new("discriminant$", Type::MInt);
        Expression::local_no_pos(variable)
    }
    pub fn is_discriminant(&self) -> bool {
        if let Expression::Local(Local { variable, .. }) = self {
            variable.name == "discriminant$"
        } else {
            false
        }
    }
}

impl FieldDecl {
    pub fn discriminant() -> Self {
        FieldDecl::new("discriminant", Type::MInt)
    }
    pub fn is_discriminant(&self) -> bool {
        self.name == "discriminant"
    }
}
