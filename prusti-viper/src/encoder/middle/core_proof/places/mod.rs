use super::lowerer::Lowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, compute_address::ComputeAddressInterface,
        lowerer::DomainsLowererInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

mod encoder;
mod interface;

pub(super) use self::interface::PlacesInterface;
