use super::{super::ensurer::ExpandedPermissionKind, Visitor};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    high::to_typed::types::HighToTypedTypeEncoderInterface,
    mir::errors::ErrorInterface,
};
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::{
    common::position::Positioned,
    typed::{self as vir_typed, operations::ty::Typed},
};

impl<'p, 'v, 'tcx> super::super::ensurer::Context for Visitor<'p, 'v, 'tcx> {
    fn expand_place(
        &mut self,
        place: &vir_typed::Expression,
        guiding_place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_typed::Expression)>> {
        let ty = place.get_type();
        let type_decl = self.encoder.encode_type_def_typed(ty)?;
        fn expand_fields<'a>(
            place: &vir_typed::Expression,
            fields: impl Iterator<Item = std::borrow::Cow<'a, vir_typed::FieldDecl>>,
        ) -> Vec<(ExpandedPermissionKind, vir_typed::Expression)> {
            let places = fields
                .map(|field| {
                    let position = place.position();
                    (
                        ExpandedPermissionKind::Same,
                        vir_typed::Expression::field(place.clone(), field.into_owned(), position),
                    )
                })
                .collect::<Vec<_>>();
            if places.is_empty() {
                // We have a ZST; unfolding it just gives a zero sized memory
                // block at the same place.
                vec![(ExpandedPermissionKind::MemoryBlock, place.clone())]
            } else {
                places
            }
        }
        let expansion = match type_decl {
            vir_typed::TypeDecl::Bool
            | vir_typed::TypeDecl::Int(_)
            | vir_typed::TypeDecl::Float(_)
            | vir_typed::TypeDecl::Pointer(_) => {
                // Primitive type. Convert.
                vec![(ExpandedPermissionKind::MemoryBlock, place.clone())]
            }
            vir_typed::TypeDecl::Trusted(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Struct(decl) => expand_fields(place, decl.iter_fields()),
            vir_typed::TypeDecl::Union(_) => {
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                vec![(ExpandedPermissionKind::Same, variant_place)]
            }
            vir_typed::TypeDecl::Enum(decl) => {
                let discriminant_field = decl.discriminant_field();
                let position = place.position();
                let discriminant_place =
                    vir_typed::Expression::field(place.clone(), discriminant_field, position);
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                vec![
                    (ExpandedPermissionKind::Same, discriminant_place),
                    (ExpandedPermissionKind::Same, variant_place),
                ]
            }
            vir_typed::TypeDecl::Array(decl) => {
                // TODO: Instead of a concrete index use a wildcard that would match any index.
                let index = place.get_index(guiding_place);
                let index_place = vir_typed::Expression::builtin_func_app(
                    vir_typed::BuiltinFunc::Index,
                    vec![decl.element_type.clone()],
                    vec![place.clone(), index.clone()],
                    decl.element_type,
                    place.position(),
                );
                vec![(ExpandedPermissionKind::Same, index_place)]
            }
            vir_typed::TypeDecl::Reference(decl) => {
                let deref_place =
                    vir_typed::Expression::deref(place.clone(), decl.target_type, place.position());
                vec![(ExpandedPermissionKind::Same, deref_place)]
            }
            vir_typed::TypeDecl::Sequence(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Map(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Never => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
        };
        Ok(expansion)
    }
    fn get_span(&mut self, position: vir_typed::Position) -> Option<MultiSpan> {
        self.encoder
            .error_manager()
            .position_manager()
            .get_span(self.proc_def_id, position.into())
            .cloned()
    }
    fn change_error_context(
        &mut self,
        position: vir_typed::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_typed::Position {
        self.encoder
            .change_error_context(self.proc_def_id, position, error_ctxt)
    }
}
