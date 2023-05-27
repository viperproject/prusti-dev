use super::{super::ensurer::ExpandedPermissionKind, Visitor};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    high::to_typed::types::HighToTypedTypeEncoderInterface,
    mir::errors::ErrorInterface,
};
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::{
    common::{builtin_constants::ADDRESS_FIELD_NAME, position::Positioned},
    typed::{self as vir_typed, operations::ty::Typed},
};

impl<'p, 'v, 'tcx> super::super::ensurer::Context for Visitor<'p, 'v, 'tcx> {
    fn expand_place(
        &mut self,
        place: &vir_typed::Expression,
        guiding_place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_typed::Expression)>> {
        let ty = place.get_type();
        // FIXME: For expansion we should use not the TypeDef const generic and
        // lifetime variables, but concrete values from `ty`. However, for this
        // it seams we need to use Rust compiler's `SubstsRef` design, which
        // means one more refactoring…
        let type_decl = self.encoder.encode_type_def_typed(ty)?;
        fn expand_fields<'a>(
            place: &vir_typed::Expression,
            fields: impl Iterator<Item = &'a vir_typed::FieldDecl>,
        ) -> Vec<(ExpandedPermissionKind, vir_typed::Expression)> {
            let places = fields
                .map(|field| {
                    let position = place.position();
                    (
                        ExpandedPermissionKind::Same,
                        vir_typed::Expression::field(place.clone(), field.clone(), position),
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
            | vir_typed::TypeDecl::Float(_) => {
                // Primitive type.
                unreachable!();
            }
            vir_typed::TypeDecl::Pointer(_) => {
                let target_type = ty.clone().unwrap_pointer().target_type;
                let deref_place =
                    vir_typed::Expression::deref(place.clone(), *target_type, place.position());
                vec![(ExpandedPermissionKind::Same, deref_place)]
            }
            vir_typed::TypeDecl::Trusted(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Struct(decl) => {
                // if decl.is_manually_managed_type() {
                //     let place_span = self.get_span(guiding_place.position()).unwrap();
                //     let error = SpannedEncodingError::incorrect(
                //         "types with structural invariants are required to be managed manually",
                //         place_span,
                //     );
                //     return Err(error);
                // }
                expand_fields(place, decl.fields.iter())
            }
            vir_typed::TypeDecl::Enum(decl) => {
                let position = place.position();
                let variant_name = place.get_variant_name(guiding_place);
                let variant_place = place.clone().into_variant(variant_name.clone());
                let mut expansion = vec![(ExpandedPermissionKind::Same, variant_place)];
                if decl.safety.is_enum() {
                    let discriminant_field = decl.discriminant_field();
                    let discriminant_place =
                        vir_typed::Expression::field(place.clone(), discriminant_field, position);
                    expansion.push((ExpandedPermissionKind::Same, discriminant_place));
                }
                expansion
            }
            vir_typed::TypeDecl::Array(_decl) => {
                // TODO: Instead of a concrete index use a wildcard that would match any index.
                let index = place.get_index(guiding_place);
                let element_type = match ty {
                    vir_typed::Type::Array(vir_typed::ty::Array {
                        box element_type, ..
                    }) => element_type,
                    vir_typed::Type::Slice(vir_typed::ty::Slice {
                        box element_type, ..
                    }) => element_type,
                    _ => {
                        unreachable!()
                    }
                };
                let index_place = vir_typed::Expression::builtin_func_app(
                    vir_typed::BuiltinFunc::Index,
                    vec![element_type.clone()],
                    vec![place.clone(), index.clone()],
                    element_type.clone(),
                    place.position(),
                );
                vec![(ExpandedPermissionKind::Same, index_place)]
            }
            vir_typed::TypeDecl::Reference(_decl) => {
                let target_type = ty.clone().unwrap_reference().target_type;
                let deref_place =
                    vir_typed::Expression::deref(place.clone(), *target_type, place.position());
                let address_place = vir_typed::Expression::field(
                    place.clone(),
                    vir_typed::FieldDecl::new(
                        ADDRESS_FIELD_NAME,
                        0usize,
                        vir_typed::Type::Int(vir_typed::ty::Int::Usize),
                    ),
                    place.position(),
                );
                vec![
                    (ExpandedPermissionKind::Same, deref_place),
                    (ExpandedPermissionKind::Same, address_place),
                ]
            }
            vir_typed::TypeDecl::Sequence(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Map(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
            vir_typed::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
        };
        Ok(expansion)
    }
    fn get_span(&mut self, position: vir_typed::Position) -> Option<MultiSpan> {
        self.encoder
            .error_manager()
            .position_manager()
            .get_span(position.into())
            .cloned()
    }
    fn change_error_context(
        &mut self,
        position: vir_typed::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_typed::Position {
        self.encoder.change_error_context(position, error_ctxt)
    }
}
