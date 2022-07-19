use super::{super::ensurer::ExpandedPermissionKind, Visitor};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::{errors::ErrorInterface, types::MirTypeEncoderInterface},
};
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::{
    common::position::Positioned,
    high::{self as vir_high, operations::ty::Typed},
};

impl<'p, 'v, 'tcx> super::super::ensurer::Context for Visitor<'p, 'v, 'tcx> {
    fn expand_place(
        &mut self,
        place: &vir_high::Expression,
        guiding_place: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_high::Expression)>> {
        let ty = place.get_type();
        let type_decl = self.encoder.encode_type_def(ty)?;
        fn expand_fields<'a>(
            place: &vir_high::Expression,
            fields: impl Iterator<Item = std::borrow::Cow<'a, vir_high::FieldDecl>>,
        ) -> Vec<(ExpandedPermissionKind, vir_high::Expression)> {
            let places = fields
                .map(|field| {
                    let position = place.position();
                    (
                        ExpandedPermissionKind::Same,
                        vir_high::Expression::field(place.clone(), field.into_owned(), position),
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
            vir_high::TypeDecl::Bool
            | vir_high::TypeDecl::Int(_)
            | vir_high::TypeDecl::Float(_)
            | vir_high::TypeDecl::Pointer(_) => {
                // Primitive type. Convert.
                vec![(ExpandedPermissionKind::MemoryBlock, place.clone())]
            }
            vir_high::TypeDecl::Trusted(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Tuple(tuple_decl) => expand_fields(place, tuple_decl.iter_fields()),
            vir_high::TypeDecl::Struct(decl) => expand_fields(place, decl.iter_fields()),
            vir_high::TypeDecl::Union(_) => {
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                vec![(ExpandedPermissionKind::Same, variant_place)]
            }
            vir_high::TypeDecl::Enum(decl) => {
                let discriminant_field = decl.discriminant_field();
                let position = place.position();
                let discriminant_place =
                    vir_high::Expression::field(place.clone(), discriminant_field, position);
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                vec![
                    (ExpandedPermissionKind::Same, discriminant_place),
                    (ExpandedPermissionKind::Same, variant_place),
                ]
            }
            vir_high::TypeDecl::Array(decl) => {
                // TODO: Instead of a concrete index use a wildcard that would match any index.
                let index = place.get_index(guiding_place);
                let index_place = vir_high::Expression::builtin_func_app(
                    vir_high::BuiltinFunc::Index,
                    vec![decl.element_type.clone()],
                    vec![place.clone(), index.clone()],
                    decl.element_type,
                    place.position(),
                );
                vec![(ExpandedPermissionKind::Same, index_place)]
            }
            vir_high::TypeDecl::Reference(decl) => {
                let deref_place =
                    vir_high::Expression::deref(place.clone(), decl.target_type, place.position());
                vec![(ExpandedPermissionKind::Same, deref_place)]
            }
            vir_high::TypeDecl::Sequence(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Map(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Never => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
        };
        Ok(expansion)
    }
    fn get_span(&mut self, position: vir_high::Position) -> Option<MultiSpan> {
        self.encoder
            .error_manager()
            .position_manager()
            .get_span(position.into())
            .cloned()
    }
    fn change_error_context(
        &mut self,
        position: vir_high::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_high::Position {
        self.encoder.change_error_context(position, error_ctxt)
    }
}
