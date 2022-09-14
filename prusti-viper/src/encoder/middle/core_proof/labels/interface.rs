use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use vir_crate::low as vir_low;

pub(in super::super) trait LabelsInterface {
    fn fresh_label(&mut self, prefix: &str) -> SpannedEncodingResult<String>;
    fn save_custom_label(&mut self, label: String) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> LabelsInterface for Lowerer<'p, 'v, 'tcx> {
    fn fresh_label(&mut self, prefix: &str) -> SpannedEncodingResult<String> {
        let label = format!("{}{}", prefix, self.labels_state.counter);
        self.save_custom_label(label.clone())?;
        self.labels_state.counter += 1;
        Ok(label)
    }

    fn save_custom_label(&mut self, label: String) -> SpannedEncodingResult<()> {
        let label = vir_low::Label::new(label);
        assert!(self.labels_state.labels.insert(label));
        Ok(())
    }
}
