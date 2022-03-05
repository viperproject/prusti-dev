use super::{super::ensurer::ExpandedPermissionKind, Visitor};
use crate::encoder::{errors::SpannedEncodingResult, mir::types::MirTypeEncoderInterface};
use vir_crate::high::{self as vir_high, operations::ty::Typed};

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
                    (
                        ExpandedPermissionKind::Same,
                        vir_high::Expression::field_no_pos(place.clone(), field.into_owned()),
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
            | vir_high::TypeDecl::Float(_) => {
                // Primitive type. Convert.
                vec![(ExpandedPermissionKind::MemoryBlock, place.clone())]
            }
            vir_high::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Tuple(tuple_decl) => expand_fields(place, tuple_decl.iter_fields()),
            vir_high::TypeDecl::Struct(struct_decl) => {
                expand_fields(place, struct_decl.iter_fields())
            }
            vir_high::TypeDecl::Enum(decl) => {
                let discriminant_field = decl.discriminant_field();
                let discriminant_place =
                    vir_high::Expression::field_no_pos(place.clone(), discriminant_field);
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                vec![
                    (ExpandedPermissionKind::Same, discriminant_place),
                    (ExpandedPermissionKind::Same, variant_place),
                ]
            }
            vir_high::TypeDecl::Array(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Reference(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Never => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
        };
        Ok(expansion)
    }
}
