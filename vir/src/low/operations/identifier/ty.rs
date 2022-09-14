use super::super::super::ast::ty;
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for ty::Type {
    fn get_identifier(&self) -> String {
        match self {
            ty::Type::Int => "Int".to_string(),
            ty::Type::Bool => "Bool".to_string(),
            ty::Type::Perm => "Perm".to_string(),
            ty::Type::Ref => "Ref".to_string(),
            ty::Type::Float(ty) => ty.get_identifier(),
            ty::Type::BitVector(ty) => ty.get_identifier(),
            ty::Type::Seq(ty) => ty.get_identifier(),
            ty::Type::Set(ty) => ty.get_identifier(),
            ty::Type::MultiSet(ty) => ty.get_identifier(),
            ty::Type::Map(ty) => ty.get_identifier(),
            ty::Type::Domain(ty) => ty.get_identifier(),
        }
    }
}

impl WithIdentifier for ty::Float {
    fn get_identifier(&self) -> String {
        match self {
            ty::Float::F32 => "F32".to_string(),
            ty::Float::F64 => "F64".to_string(),
        }
    }
}

impl WithIdentifier for ty::BitVector {
    fn get_identifier(&self) -> String {
        match self {
            ty::BitVector::Signed(ty) => format!("S${}", ty.get_identifier()),
            ty::BitVector::Unsigned(ty) => format!("U${}", ty.get_identifier()),
        }
    }
}

impl WithIdentifier for ty::BitVectorSize {
    fn get_identifier(&self) -> String {
        match self {
            ty::BitVectorSize::BV8 => "BV8".to_string(),
            ty::BitVectorSize::BV16 => "BV16".to_string(),
            ty::BitVectorSize::BV32 => "BV32".to_string(),
            ty::BitVectorSize::BV64 => "BV64".to_string(),
            ty::BitVectorSize::BV128 => "BV128".to_string(),
        }
    }
}

impl WithIdentifier for ty::Seq {
    fn get_identifier(&self) -> String {
        format!("Seq${}", self.element_type.get_identifier())
    }
}

impl WithIdentifier for ty::Set {
    fn get_identifier(&self) -> String {
        format!("Set${}", self.element_type.get_identifier())
    }
}

impl WithIdentifier for ty::MultiSet {
    fn get_identifier(&self) -> String {
        format!("MultiSet${}", self.element_type.get_identifier())
    }
}

impl WithIdentifier for ty::Map {
    fn get_identifier(&self) -> String {
        format!(
            "Map${}${}",
            self.key_type.get_identifier(),
            self.val_type.get_identifier()
        )
    }
}

impl WithIdentifier for ty::Domain {
    fn get_identifier(&self) -> String {
        format!("D${}", self.name)
    }
}
