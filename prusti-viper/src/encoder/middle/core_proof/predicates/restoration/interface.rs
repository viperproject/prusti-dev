use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{Lowerer, PredicatesLowererInterface},
};
use rustc_hash::FxHashSet;
use vir_crate::{common::identifier::WithIdentifier, low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct RestorationState {
    encoded_restore_raw_borrowed_transition_predicate: FxHashSet<String>,
}

pub(in super::super::super) trait RestorationInterface {
    fn encode_restore_raw_borrowed_transition_predicate(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn restore_raw_borrowed(
        &mut self,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        address: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> RestorationInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_restore_raw_borrowed_transition_predicate(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .predicates_encoding_state
            .restoration
            .encoded_restore_raw_borrowed_transition_predicate
            .contains(&ty_identifier)
        {
            self.predicates_encoding_state
                .restoration
                .encoded_restore_raw_borrowed_transition_predicate
                .insert(ty_identifier);

            use vir_low::macros::*;
            let predicate = vir_low::PredicateDecl::new(
                predicate_name! { RestoreRawBorrowed<ty> },
                vir_low::PredicateKind::WithoutSnapshotWhole,
                vars!(place: Place, address: Address),
                None,
            );
            self.declare_predicate(predicate)?;
        }
        Ok(())
    }
    fn restore_raw_borrowed(
        &mut self,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        address: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_restore_raw_borrowed_transition_predicate(ty)?;
        use vir_low::macros::*;
        let predicate = expr! {
            acc(RestoreRawBorrowed<ty>(
                [place],
                [address]
            ))
        };
        Ok(predicate)
    }
}
