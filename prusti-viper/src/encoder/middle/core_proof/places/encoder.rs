use super::{super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, PlacesInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use vir_crate::{
    common::builtin_constants::{PLACE_DOMAIN_NAME, PLACE_OPTION_DOMAIN_NAME},
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(super) struct PlaceEncoder {}

impl PlaceExpressionDomainEncoder for PlaceEncoder {
    fn domain_name(&mut self, _lowerer: &mut Lowerer) -> &str {
        PLACE_OPTION_DOMAIN_NAME
    }

    fn encode_local(
        &mut self,
        local: &vir_mid::expression::Local,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let function_name = format!("{}$place", local.variable.name);
        let return_type = lowerer.place_type()?;
        let place_root = lowerer.create_unique_domain_func_app(
            PLACE_DOMAIN_NAME,
            function_name,
            vec![],
            return_type,
            local.position,
        )?;
        lowerer.encode_compute_address_for_place_root(&place_root)?;
        let place_option_root = lowerer.place_option_some_constructor(place_root.clone())?;
        Ok(place_option_root)
    }

    fn encode_deref(
        &mut self,
        deref: &vir_mid::expression::Deref,
        lowerer: &mut Lowerer,
        arg: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if deref.base.get_type().is_reference() {
            lowerer.encode_deref_place(arg, deref.position)
        } else {
            assert!(deref.base.get_type().is_pointer());
            lowerer.place_option_none_constructor(deref.position)
            // lowerer.encode_aliased_place_root(deref.position)
        }
    }

    fn encode_array_index_axioms(
        &mut self,
        ty: &vir_mid::Type,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        lowerer.encode_place_array_index_axioms(ty)
    }

    fn encode_labelled_old(
        &mut self,
        expression: &vir_mid::expression::LabelledOld,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_expression(&expression.base, lowerer)
    }
}
