use super::super::{super::ast::rvalue::*, ty::Typed};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for Rvalue {
    fn get_identifier(&self) -> String {
        match self {
            Self::AddressOf(value) => value.get_identifier(),
            Self::BinaryOp(value) => value.get_identifier(),
            Self::UnaryOp(value) => value.get_identifier(),
            Self::Aggregate(value) => value.get_identifier(),
            Self::Discriminant(value) => value.get_identifier(),
            Self::Ref(value) => value.get_identifier(),
        }
    }
}

impl WithIdentifier for Ref {
    fn get_identifier(&self) -> String {
        format!("ref_${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for AddressOf {
    fn get_identifier(&self) -> String {
        format!("address_of${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for UnaryOp {
    fn get_identifier(&self) -> String {
        format!("UnaryOp${}${}", self.kind, self.argument.get_identifier())
    }
}

impl WithIdentifier for BinaryOp {
    fn get_identifier(&self) -> String {
        format!(
            "BinaryOp${}${}${}",
            self.kind,
            self.left.get_identifier(),
            self.right.get_identifier()
        )
    }
}

impl WithIdentifier for Discriminant {
    fn get_identifier(&self) -> String {
        format!("discriminant${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for Aggregate {
    fn get_identifier(&self) -> String {
        format!("aggregate${}", self.ty.get_identifier())
    }
}

impl WithIdentifier for Operand {
    fn get_identifier(&self) -> String {
        format!(
            "{}${}",
            self.kind,
            self.expression.get_type().get_identifier()
        )
    }
}
