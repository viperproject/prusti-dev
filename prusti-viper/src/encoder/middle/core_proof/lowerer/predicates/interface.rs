use crate::encoder::{
    errors::SpannedEncodingResult,
    high::pure_functions::HighPureFunctionEncoderInterface,
    middle::core_proof::{into_low::IntoLow, lowerer::Lowerer},
};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    low::{self as vir_low, operations::ty::Typed},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super) struct PredicatesLowererState {
    predicates: BTreeMap<String, vir_low::PredicateDecl>,
}

impl PredicatesLowererState {
    pub fn destruct(self) -> Vec<vir_low::PredicateDecl> {
        self.predicates.into_values().collect()
    }
}

pub(in super::super::super) trait PredicatesLowererInterface {
    fn declare_predicate(&mut self, predicate: vir_low::PredicateDecl)
        -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn declare_predicate(
        &mut self,
        predicate: vir_low::PredicateDecl,
    ) -> SpannedEncodingResult<()> {
        assert!(
            !self
                .predicates_state
                .predicates
                .contains_key(&predicate.name),
            "predicate already declared: {}",
            predicate.name
        );
        self.predicates_state
            .predicates
            .insert(predicate.name.clone(), predicate);
        Ok(())
    }
}
