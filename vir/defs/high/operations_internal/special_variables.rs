use super::super::ast::{
    expression::{Expression, Field, Local},
    field::FieldDecl,
    ty::{self, Type},
    type_decl::Enum,
    variable::VariableDecl,
};

impl VariableDecl {
    pub fn self_variable(ty: Type) -> Self {
        VariableDecl::new(crate::common::builtin_constants::SELF_VARIABLE_NAME, ty)
    }

    pub fn is_self_variable(&self) -> bool {
        self.name == crate::common::builtin_constants::SELF_VARIABLE_NAME
    }

    pub fn result_variable(ty: Type) -> Self {
        VariableDecl::new(crate::common::builtin_constants::RESULT_VARIABLE_NAME, ty)
    }

    pub fn discriminant_variable() -> Self {
        VariableDecl::new(
            crate::common::builtin_constants::DISCRIMINANT_VARIABLE_NAME,
            Type::MInt,
        )
    }
}

impl Expression {
    pub fn self_variable(ty: Type) -> Self {
        let variable = VariableDecl::self_variable(ty);
        Expression::local_no_pos(variable)
    }

    pub fn is_self_variable(&self) -> bool {
        if let Expression::Local(Local { variable, .. }) = self {
            variable.is_self_variable()
        } else {
            false
        }
    }

    pub fn discriminant() -> Self {
        let variable = VariableDecl::discriminant_variable();
        Expression::local_no_pos(variable)
    }

    pub fn is_discriminant(&self) -> bool {
        if let Expression::Local(Local { variable, .. }) = self {
            variable.name == crate::common::builtin_constants::DISCRIMINANT_VARIABLE_NAME
        } else {
            false
        }
    }

    pub fn is_discriminant_field(&self) -> bool {
        if let Expression::Field(Field { field, .. }) = self {
            field.is_discriminant()
        } else {
            false
        }
    }
}

const DISCRIMINANT_INDEX: usize = 100000;

impl FieldDecl {
    pub fn discriminant(ty: Type) -> Self {
        FieldDecl::new(
            crate::common::builtin_constants::DISCRIMINANT_FIELD_NAME,
            DISCRIMINANT_INDEX,
            ty,
        )
    }
    pub fn is_discriminant(&self) -> bool {
        self.name == crate::common::builtin_constants::DISCRIMINANT_FIELD_NAME
            && self.index == DISCRIMINANT_INDEX
    }
    pub fn reference_address(reference_type: ty::Reference) -> Self {
        let ty = Type::pointer(*reference_type.target_type);
        FieldDecl::new(
            crate::common::builtin_constants::ADDRESS_FIELD_NAME,
            0usize,
            ty,
        )
    }
    pub fn is_address(&self) -> bool {
        self.name == crate::common::builtin_constants::ADDRESS_FIELD_NAME && self.index == 0usize
    }
}

impl Enum {
    pub fn discriminant_field(&self) -> FieldDecl {
        FieldDecl::discriminant(self.discriminant_type.clone())
    }
}
