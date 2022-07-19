use super::{super::super::ast::ty, common::append_type_arguments};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for ty::Type {
    fn get_identifier(&self) -> String {
        match self {
            ty::Type::MBool => "MBool".to_string(),
            ty::Type::MInt => "MInt".to_string(),
            ty::Type::MFloat32 => "MFloat32".to_string(),
            ty::Type::MFloat64 => "MFloat64".to_string(),
            ty::Type::MPerm => "MPerm".to_string(),
            ty::Type::Bool => "Bool".to_string(),
            ty::Type::Int(ty) => ty.get_identifier(),
            ty::Type::Sequence(ty) => ty.get_identifier(),
            ty::Type::Map(ty) => ty.get_identifier(),
            ty::Type::Float(ty) => ty.get_identifier(),
            ty::Type::TypeVar(ty) => ty.get_identifier(),
            ty::Type::Tuple(ty) => ty.get_identifier(),
            ty::Type::Struct(ty) => ty.get_identifier(),
            ty::Type::Enum(ty) => ty.get_identifier(),
            ty::Type::Union(ty) => ty.get_identifier(),
            ty::Type::Array(ty) => ty.get_identifier(),
            ty::Type::Slice(ty) => ty.get_identifier(),
            ty::Type::Reference(ty) => ty.get_identifier(),
            ty::Type::Pointer(ty) => ty.get_identifier(),
            ty::Type::FnPointer => "FnPointer".to_string(),
            ty::Type::Never => "Never".to_string(),
            ty::Type::Str => "Str".to_string(),
            ty::Type::Closure(ty) => ty.get_identifier(),
            ty::Type::FunctionDef(ty) => ty.get_identifier(),
            ty::Type::Projection(ty) => ty.get_identifier(),
            ty::Type::Unsupported(ty) => ty.get_identifier(),
            ty::Type::Trusted(ty) => ty.get_identifier(),
            ty::Type::Lifetime => "Lifetime".to_string(),
        }
    }
}

impl WithIdentifier for ty::Int {
    fn get_identifier(&self) -> String {
        self.to_string()
    }
}

impl WithIdentifier for ty::Sequence {
    fn get_identifier(&self) -> String {
        format!("Seq${}", self.element_type.get_identifier())
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

impl WithIdentifier for ty::Float {
    fn get_identifier(&self) -> String {
        self.to_string()
    }
}

impl WithIdentifier for ty::TypeVar {
    fn get_identifier(&self) -> String {
        match self {
            ty::TypeVar::LifetimeConst(type_var) => type_var.get_identifier(),
            ty::TypeVar::GenericType(type_var) => type_var.get_identifier(),
        }
    }
}

impl WithIdentifier for ty::LifetimeConst {
    fn get_identifier(&self) -> String {
        "lifetime".to_string()
    }
}

impl WithIdentifier for ty::GenericType {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

impl WithIdentifier for ty::Tuple {
    fn get_identifier(&self) -> String {
        let mut identifier = "Tuple".to_string();
        append_type_arguments(&mut identifier, &self.arguments);
        identifier
    }
}

impl WithIdentifier for ty::Struct {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        append_type_arguments(&mut identifier, &self.arguments);
        assert!(!identifier.contains('<'), "identifier: {}", identifier);
        identifier
    }
}

impl WithIdentifier for ty::Enum {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        identifier.push('$');
        if let Some(variant) = &self.variant {
            identifier.push_str(&variant.index);
        } else {
            identifier.push('_');
        }
        append_type_arguments(&mut identifier, &self.arguments);
        identifier
    }
}

impl WithIdentifier for ty::Union {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        identifier.push('$');
        if let Some(variant) = &self.variant {
            identifier.push_str(&variant.index);
        } else {
            identifier.push('_');
        }
        append_type_arguments(&mut identifier, &self.arguments);
        identifier
    }
}

impl WithIdentifier for ty::Array {
    fn get_identifier(&self) -> String {
        format!("array${}", self.element_type.get_identifier())
    }
}

impl WithIdentifier for ty::Slice {
    fn get_identifier(&self) -> String {
        format!("slice${}", self.element_type.get_identifier())
    }
}

impl WithIdentifier for ty::Reference {
    fn get_identifier(&self) -> String {
        format!(
            "ref${}${}",
            self.uniqueness,
            self.target_type.get_identifier(),
        )
    }
}

impl WithIdentifier for ty::Pointer {
    fn get_identifier(&self) -> String {
        format!("ptr${}", self.target_type.get_identifier())
    }
}

impl WithIdentifier for ty::Closure {
    fn get_identifier(&self) -> String {
        format!("closure${}", self.name)
    }
}

impl WithIdentifier for ty::FunctionDef {
    fn get_identifier(&self) -> String {
        format!("function_def${}", self.name)
    }
}

impl WithIdentifier for ty::Projection {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        append_type_arguments(&mut identifier, &self.arguments);
        identifier
    }
}

impl WithIdentifier for ty::Unsupported {
    fn get_identifier(&self) -> String {
        format!("unsupported${}", self.name)
    }
}

impl WithIdentifier for ty::Trusted {
    fn get_identifier(&self) -> String {
        let mut identifier = self.name.clone();
        append_type_arguments(&mut identifier, &self.arguments);
        assert!(!identifier.contains('<'), "identifier: {}", identifier);
        identifier
    }
}
