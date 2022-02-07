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
}
