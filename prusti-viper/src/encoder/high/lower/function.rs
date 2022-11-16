use super::{super::types::interface::HighTypeEncoderInterfacePrivate, IntoPolymorphic};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

impl IntoPolymorphic<vir_poly::Function> for vir_high::FunctionDecl {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Function {
        vir_poly::Function {
            name: self.name.clone(),
            type_arguments: self.type_arguments.lower(encoder),
            formal_args: self
                .parameters
                .iter()
                .map(|parameter| parameter.lower(encoder))
                .collect(),
            return_type: self.return_type.lower(encoder),
            // FIXME: We should add predicates for all arguments here.
            pres: self.pres.iter().map(|post| post.lower(encoder)).collect(),
            posts: self.posts.iter().map(|post| post.lower(encoder)).collect(),
            // FIXME: We should add fold-unfold information here.
            body: self.body.as_ref().map(|body| body.lower(encoder)),
        }
    }
}
