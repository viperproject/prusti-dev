use super::{super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, AddressesInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
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
