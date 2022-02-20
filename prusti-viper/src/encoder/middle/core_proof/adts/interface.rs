use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use vir_crate::low::{self as vir_low};

use super::types::{
    constructor_call, constructor_name, destructor_call, destructor_name, BASE_VARIANT,
    CONSTANT_FIELD, CONSTANT_VARIANT,
};

pub(in super::super) trait AdtsInterface {
    fn adt_constructor_constant_call(
        &mut self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn adt_destructor_constant_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String>;
    fn adt_constructor_base_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String>;
    fn adt_destructor_base_call(
        &mut self,
        domain_name: &str,
        field_name: &str,
        field_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn adt_constructor_variant_name(
        &mut self,
        domain_name: &str,
        variant: &str,
    ) -> SpannedEncodingResult<String>;
    fn adt_destructor_variant_name(
        &mut self,
        domain_name: &str,
        variant: &str,
        field_name: &str,
    ) -> SpannedEncodingResult<String>;
}

impl<'p, 'v: 'p, 'tcx: 'v> AdtsInterface for Lowerer<'p, 'v, 'tcx> {
    fn adt_constructor_constant_call(
        &mut self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(constructor_call(domain_name, CONSTANT_VARIANT, arguments))
    }
    fn adt_destructor_constant_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String> {
        Ok(destructor_name(
            domain_name,
            CONSTANT_VARIANT,
            CONSTANT_FIELD,
        ))
    }
    fn adt_constructor_base_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String> {
        Ok(constructor_name(domain_name, BASE_VARIANT))
    }
    fn adt_destructor_base_call(
        &mut self,
        domain_name: &str,
        field_name: &str,
        field_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(destructor_call(
            domain_name,
            BASE_VARIANT,
            field_name,
            field_type,
            argument,
        ))
    }
    fn adt_constructor_variant_name(
        &mut self,
        domain_name: &str,
        variant: &str,
    ) -> SpannedEncodingResult<String> {
        Ok(constructor_name(domain_name, variant))
    }
    fn adt_destructor_variant_name(
        &mut self,
        domain_name: &str,
        variant: &str,
        field_name: &str,
    ) -> SpannedEncodingResult<String> {
        Ok(destructor_name(domain_name, variant, field_name))
    }
}
