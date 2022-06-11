use super::{super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, AddressesInterface};
use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

pub(super) struct PlaceAddressEncoder {}

impl PlaceExpressionDomainEncoder for PlaceAddressEncoder {
    fn domain_name(&mut self, _lowerer: &mut Lowerer) -> &str {
        "Address"
    }

    fn encode_local(
        &mut self,
        local: &vir_mid::expression::Local,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        lowerer.root_address(local)
    }

    fn encode_deref(
        &mut self,
        _deref: &vir_mid::expression::Deref,
        _lowerer: &mut Lowerer,
        _arg: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unreachable!("The address cannot be dereferenced; use the value instead.")
    }

    fn encode_array_index_axioms(
        &mut self,
        _base_type: &vir_mid::Type,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}
