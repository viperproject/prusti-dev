use super::{super::types::interface::HighTypeEncoderInterfacePrivate, IntoPolymorphic};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

impl IntoPolymorphic<vir_poly::Position> for vir_high::Position {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Position {
        vir_poly::Position::new(self.line, self.column, self.id)
    }
}
