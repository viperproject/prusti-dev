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

impl Tuple {
    pub fn iter_fields(&self) -> impl Iterator<Item = std::borrow::Cow<'_, FieldDecl>> {
        self.arguments
            .iter()
            .enumerate()
            .map(|(index, argument_type)| {
                std::borrow::Cow::Owned(FieldDecl::new(
                    format!("tuple_{}", index),
                    index,
                    argument_type.clone(),
                ))
            })
    }
}

impl Struct {
    pub fn iter_fields(&self) -> impl Iterator<Item = std::borrow::Cow<'_, FieldDecl>> {
        self.fields.iter().map(std::borrow::Cow::Borrowed)
    }
}
