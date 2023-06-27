use super::super::ast::{
    field::FieldDecl,
    ty::{LifetimeConst, Type},
    type_decl::{Enum, Struct, Trusted, TypeDecl},
    variable::VariableDecl,
};

impl Struct {
    pub fn is_manually_managed_type(&self) -> bool {
        self.structural_invariant.is_some()
    }
}

impl Enum {
    pub fn variant(&self, variant_name: &str) -> Option<&Struct> {
        self.variants
            .iter()
            .find(|variant| variant.name == variant_name)
    }
    pub fn into_variant(self, variant_name: &str) -> Option<Struct> {
        self.variants
            .into_iter()
            .find(|variant| variant.name == variant_name)
    }
}

impl TypeDecl {
    pub fn get_lifetime_parameters(&self) -> &[LifetimeConst] {
        match self {
            Self::Bool => &[],
            Self::Int(_decl) => &[],
            Self::Float(_decl) => &[],
            Self::TypeVar(_decl) => &[],
            Self::Struct(decl) => &decl.lifetimes,
            Self::Sequence(decl) => &decl.lifetimes,
            Self::Map(decl) => &decl.lifetimes,
            Self::Enum(decl) => &decl.lifetimes,
            // Self::Union(decl) => &decl.lifetimes,
            Self::Array(decl) => &decl.lifetimes,
            // // Self::Slice(_decl) => &decl.lifetimes,
            Self::Reference(decl) => &decl.lifetimes,
            // Since pointer targets may be invalid, we ignore their lifetimes.
            Self::Pointer(_decl) => &[],
            // // Self::FnPointer => &[],
            // // Self::Str => &[],
            // Self::Closure(decl) => &decl.lifetimes,
            // // Self::Projection(_decl) => &[],
            // Self::Unsupported(_decl) => &[],
            Self::Trusted(decl) => &decl.lifetimes,
            _ => unimplemented!("{}", self),
        }
    }
    pub fn get_const_parameters(&self) -> &[VariableDecl] {
        match self {
            Self::Bool => &[],
            Self::Int(_decl) => &[],
            Self::Float(_decl) => &[],
            Self::TypeVar(_decl) => &[],
            Self::Struct(decl) => &decl.const_parameters,
            Self::Sequence(decl) => &decl.const_parameters,
            Self::Map(decl) => &decl.const_parameters,
            Self::Enum(decl) => &decl.const_parameters,
            // Self::Union(decl) => &decl.const_parameters,
            Self::Array(decl) => &decl.const_parameters,
            // // Self::Slice(_decl) => &decl.const_parameters,
            Self::Reference(decl) => &decl.const_parameters,
            Self::Pointer(decl) => &decl.const_parameters,
            // // Self::FnPointer => &[],
            // // Self::Str => &[],
            // Self::Closure(decl) => &decl.const_parameters,
            // // Self::Projection(_decl) => &[],
            // Self::Unsupported(_decl) => &[],
            Self::Trusted(decl) => &decl.const_parameters,
            _ => unimplemented!("{}", self),
        }
    }
}
