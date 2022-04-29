use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, types::TypesInterface},
};
use rustc_hash::FxHashSet;

use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

use super::encoder::PredicateEncoder;

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    unfolded_owned_non_aliased_predicates: FxHashSet<vir_mid::Type>,
}

pub(in super::super::super) trait PredicatesOwnedInterface {
    /// Marks that `OwnedNonAliased<ty>` was unfolded in the program and we need
    /// to provide its body.
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>>;
    fn acc_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
        place: impl Into<vir_low::Expression>,
        root_address: impl Into<vir_low::Expression>,
        snapshot: impl Into<vir_low::Expression>,
        lifetimes: Vec<impl Into<vir_low::Expression>>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesOwnedInterface for Lowerer<'p, 'v, 'tcx> {
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .owned
            .unfolded_owned_non_aliased_predicates
            .contains(ty)
        {
            self.ensure_type_definition(ty)?;
            self.predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates
                .insert(ty.clone());
        }
        Ok(())
    }

    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>> {
        let unfolded_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates,
        );
        let mut predicate_encoder = PredicateEncoder::new(self, &unfolded_predicates);
        for ty in &unfolded_predicates {
            predicate_encoder.encode_owned_non_aliased(ty)?;
        }
        Ok(predicate_encoder.into_predicates())
    }

    fn acc_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
        place: impl Into<vir_low::Expression>,
        root_address: impl Into<vir_low::Expression>,
        snapshot: impl Into<vir_low::Expression>,
        lifetimes: Vec<impl Into<vir_low::Expression>>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let mut arguments = vec![place.into(), root_address.into(), snapshot.into()];
        arguments.extend(lifetimes.into_iter().map(|lifetime| lifetime.into()));
        Ok(vir_low::Expression::predicate_access_predicate_no_pos(
            predicate_name! { OwnedNonAliased<ty> },
            arguments,
            vir_low::Expression::full_permission(),
        ))
    }
}
