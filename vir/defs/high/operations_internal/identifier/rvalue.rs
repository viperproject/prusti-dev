use super::{
    super::{super::ast::rvalue::*, ty::Typed},
    common::append_type_arguments,
};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for Rvalue {
    fn get_identifier(&self) -> String {
        match self {
            Self::Repeat(value) => value.get_identifier(),
            Self::AddressOf(value) => value.get_identifier(),
            Self::Len(value) => value.get_identifier(),
            Self::Cast(value) => value.get_identifier(),
            Self::BinaryOp(value) => value.get_identifier(),
            Self::CheckedBinaryOp(value) => value.get_identifier(),
            Self::UnaryOp(value) => value.get_identifier(),
            Self::Aggregate(value) => value.get_identifier(),
            Self::Discriminant(value) => value.get_identifier(),
            Self::Ref(value) => value.get_identifier(),
            Self::Reborrow(value) => value.get_identifier(),
        }
    }
}

impl WithIdentifier for Repeat {
    fn get_identifier(&self) -> String {
        format!("Repeat${}", self.argument.get_identifier())
    }
}

impl WithIdentifier for Reborrow {
    fn get_identifier(&self) -> String {
        format!("Reborrow${}", self.deref_place.get_type().get_identifier())
    }
}

impl WithIdentifier for Ref {
    fn get_identifier(&self) -> String {
        format!("Ref${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for AddressOf {
    fn get_identifier(&self) -> String {
        format!("AddressOf${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for Len {
    fn get_identifier(&self) -> String {
        format!("Len${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for Cast {
    fn get_identifier(&self) -> String {
        format!(
            "Cast${}${}",
            self.operand.get_identifier(),
            self.ty.get_identifier()
        )
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

impl WithIdentifier for CheckedBinaryOp {
    fn get_identifier(&self) -> String {
        format!(
            "CheckedBinaryOp${}${}${}",
            self.kind,
            self.left.get_identifier(),
            self.right.get_identifier()
        )
    }
}

impl WithIdentifier for Discriminant {
    fn get_identifier(&self) -> String {
        format!("Discriminant${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for Aggregate {
    fn get_identifier(&self) -> String {
        let mut identifier = format!("Aggregate${}", self.ty.get_identifier());
        identifier.push('$');
        for operand in &self.operands {
            identifier.push_str(&operand.get_identifier());
            identifier.push('$');
        }
        identifier
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
