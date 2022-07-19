use super::{super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, PlacesInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

pub(super) struct PlaceEncoder {}

impl PlaceExpressionDomainEncoder for PlaceEncoder {
    fn domain_name(&mut self, _lowerer: &mut Lowerer) -> &str {
        "Place"
    }

    fn encode_local(
        &mut self,
        local: &vir_mid::expression::Local,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let function_name = format!("{}$place", local.variable.name);
        let return_type = lowerer.place_type()?;
        let place_root = lowerer.create_unique_domain_func_app(
            "Place",
            function_name,
            vec![],
            return_type,
            local.position,
        )?;
        lowerer.encode_compute_address_for_place_root(&place_root)?;
        Ok(place_root)
    }

    fn encode_deref(
        &mut self,
        deref: &vir_mid::expression::Deref,
        lowerer: &mut Lowerer,
        arg: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        lowerer.encode_deref_place(arg, deref.position)
    }

    fn encode_array_index_axioms(
        &mut self,
        ty: &vir_mid::Type,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        lowerer.encode_place_array_index_axioms(ty)
    }
}
