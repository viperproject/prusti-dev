use super::super::super::ast::type_decl::*;
use crate::common::position::Positioned;

impl Positioned for TypeDecl {
    fn position(&self) -> Position {
        match self {
            Self::Bool => Default::default(),
            Self::Int(_) => Default::default(),
            Self::Float(_) => Default::default(),
            Self::TypeVar(_) => Default::default(),
            Self::Struct(decl) => decl.position(),
            Self::Sequence(_) => Default::default(),
            Self::Map(_) => Default::default(),
            Self::Enum(_) => Default::default(),
            Self::Array(_) => Default::default(),
            Self::Reference(_) => Default::default(),
            Self::Pointer(_) => Default::default(),
            Self::Closure(_) => Default::default(),
            Self::Unsupported(_) => Default::default(),
            Self::Trusted(_) => Default::default(),
        }
    }
}

impl Positioned for Struct {
    fn position(&self) -> Position {
        self.position
    }
}
