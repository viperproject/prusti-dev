use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low as vir_low, middle as vir_mid,
    middle::operations::lifetimes::WithLifetimes,
};

pub(in super::super) trait LabelsInterface {
    fn save_custom_label(&mut self, label: String) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> LabelsInterface for Lowerer<'p, 'v, 'tcx> {
    fn save_custom_label(&mut self, label: String) -> SpannedEncodingResult<()> {
        let label = vir_low::Label::new(label);
        assert!(self.labels_state.labels.insert(label));
        Ok(())
    }
}
