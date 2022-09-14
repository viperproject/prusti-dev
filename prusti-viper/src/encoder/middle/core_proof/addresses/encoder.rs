use super::{super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, AddressesInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::Lowerer, pointers::PointersInterface, references::ReferencesInterface,
        snapshots::IntoProcedureSnapshot,
    },
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(super) struct PlaceAddressEncoder {
    old_label: Option<String>,
}

impl PlaceAddressEncoder {
    pub(super) fn new() -> Self {
        Self { old_label: None }
    }
}

impl PlaceExpressionDomainEncoder for PlaceAddressEncoder {
    fn domain_name(&mut self, lowerer: &mut Lowerer) -> &str {
        lowerer.address_domain()
    }

    fn encode_local(
        &mut self,
        local: &vir_mid::expression::Local,
        lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        lowerer.root_address(local, &self.old_label)
    }

    fn encode_deref(
        &mut self,
        deref: &vir_mid::expression::Deref,
        lowerer: &mut Lowerer,
        _arg: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Code duplication with AddressesInterface::extract_root_address
        // FIXME: Code duplication with AssertionEncoder.
        let base_snapshot = deref.base.to_procedure_snapshot(lowerer)?;
        let ty = deref.base.get_type();
        let result = if ty.is_reference() {
            lowerer.reference_address(ty, base_snapshot, deref.position)?
        } else {
            lowerer.pointer_address(ty, base_snapshot, deref.position)?
        };
        Ok(result)
    }

    fn encode_array_index_axioms(
        &mut self,
        _base_type: &vir_mid::Type,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }

    fn encode_labelled_old(
        &mut self,
        _expression: &vir_mid::expression::LabelledOld,
        _lowerer: &mut Lowerer,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }
}
