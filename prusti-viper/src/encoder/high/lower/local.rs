use super::{super::types::interface::HighTypeEncoderInterfacePrivate, IntoPolymorphic};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

impl IntoPolymorphic<vir_poly::LocalVar> for vir_high::VariableDecl {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::LocalVar {
        vir_poly::LocalVar {
            name: self.name.clone(),
            typ: self.ty.lower(encoder),
        }
    }
}

impl IntoPolymorphic<Vec<vir_poly::LocalVar>> for Vec<vir_high::VariableDecl> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Vec<vir_poly::LocalVar> {
        self.iter()
            .map(|variable| variable.lower(encoder))
            .collect()
    }
}
