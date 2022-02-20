use super::super::{super::ast::rvalue::*, ty::Typed};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for Rvalue {
    fn get_identifier(&self) -> String {
        match self {
            Self::UnaryOp(value) => value.get_identifier(),
            Self::BinaryOp(value) => value.get_identifier(),
        }
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

impl WithIdentifier for Operand {
    fn get_identifier(&self) -> String {
        format!(
            "{}${}",
            self.kind,
            self.expression.get_type().get_identifier()
        )
    }
}
