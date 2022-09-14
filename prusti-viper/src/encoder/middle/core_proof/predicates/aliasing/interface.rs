use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{addresses::AddressesInterface, lowerer::Lowerer},
};
use rustc_hash::FxHashSet;
use vir_crate::{low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct PredicatesAliasingState {
    non_aliased_places: Vec<vir_mid::Expression>,
    non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
}

pub(in super::super::super) trait PredicatesAliasingInterface {
    fn set_non_aliased_places(
        &mut self,
        places: Vec<vir_mid::Expression>,
    ) -> SpannedEncodingResult<()>;
    fn mark_place_as_used_in_memory_block(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<()>;
    fn take_non_aliased_memory_block_addresses(
        &mut self,
    ) -> SpannedEncodingResult<FxHashSet<vir_low::Expression>>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesAliasingInterface for Lowerer<'p, 'v, 'tcx> {
    fn set_non_aliased_places(
        &mut self,
        places: Vec<vir_mid::Expression>,
    ) -> SpannedEncodingResult<()> {
        assert!(
            self.predicates_encoding_state
                .aliasing
                .non_aliased_places
                .is_empty(),
            "Predicates aliasing state is already initialized."
        );
        self.predicates_encoding_state.aliasing.non_aliased_places = places;
        Ok(())
    }

    fn mark_place_as_used_in_memory_block(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<()> {
        for non_aliased_place in &self.predicates_encoding_state.aliasing.non_aliased_places {
            if place.has_prefix(non_aliased_place) {
                let address = self.encode_expression_as_place_address(place)?;
                self.predicates_encoding_state
                    .aliasing
                    .non_aliased_memory_block_addresses
                    .insert(address);
                return Ok(());
            }
        }
        Ok(())
    }

    fn take_non_aliased_memory_block_addresses(
        &mut self,
    ) -> SpannedEncodingResult<FxHashSet<vir_low::Expression>> {
        self.predicates_encoding_state
            .aliasing
            .non_aliased_places
            .clear();
        Ok(std::mem::take(
            &mut self
                .predicates_encoding_state
                .aliasing
                .non_aliased_memory_block_addresses,
        ))
    }
}
