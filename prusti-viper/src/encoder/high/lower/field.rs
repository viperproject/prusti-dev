use super::{super::types::interface::HighTypeEncoderInterfacePrivate, IntoPolymorphic};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

impl IntoPolymorphic<vir_poly::Field> for vir_high::FieldDecl {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Field {
        vir_poly::Field::new(self.name.clone(), self.ty.lower(encoder))
    }
}
