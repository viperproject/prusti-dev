use super::super::ast::{
    field::FieldDecl,
    type_decl::{Struct, Tuple},
};

impl Tuple {
    pub fn iter_fields(&self) -> impl Iterator<Item = std::borrow::Cow<'_, FieldDecl>> {
        self.arguments
            .iter()
            .enumerate()
            .map(|(index, argument_type)| {
                std::borrow::Cow::Owned(FieldDecl::new(
                    format!("tuple${}", index),
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
