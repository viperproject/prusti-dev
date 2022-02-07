use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer, places::PlacesInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use vir_crate::{common::identifier::WithIdentifier, low as vir_low, middle as vir_mid};

pub(super) struct ComputeAddressEncoder;

impl TypeDeclWalker for ComputeAddressEncoder {
    type Parameters = ();

    fn need_walk_type(
        &mut self,
        ty: &vir_mid::Type,
        _: &(),
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<bool> {
        Ok(!lowerer.compute_address_state.encoded_types.contains(ty))
    }

    fn before(
        &mut self,
        ty: &vir_mid::Type,
        _: &(),
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        lowerer
            .compute_address_state
            .encoded_types
            .insert(ty.clone());
        Ok(())
    }

    fn walk_field(
        &mut self,
        ty: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        _: &(),
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let compute_address = ty!(Address);
        let body = expr! {
            forall(
                place: Place, address: Address ::
                raw_code {
                    let field_place = lowerer.encode_field_place(
                        ty,
                        field,
                        place.clone().into(),
                        Default::default()
                    )?;
                    let field_address = lowerer.encode_field_address(
                        ty,
                        field,
                        expr! { ComputeAddress::compute_address(place, address) },
                        Default::default(),
                    )?;
                }
                [ { (ComputeAddress::compute_address([field_place.clone()], address)) } ]
                (ComputeAddress::compute_address([field_place], address)) == [field_address]
            )
        };
        let axiom = vir_low::DomainAxiomDecl {
            name: format!(
                "{}${}$compute_address_axiom",
                ty.get_identifier(),
                field.name
            ),
            body,
        };
        lowerer.compute_address_state.axioms.push(axiom);
        self.walk_type(&field.ty, (), lowerer)
    }
}
