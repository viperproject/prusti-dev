use super::super::ast::{
    field::FieldDecl,
    ty::Type,
    type_decl::{Enum, Struct, Trusted, Tuple, TypeDecl, Union},
};

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

impl Union {
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
