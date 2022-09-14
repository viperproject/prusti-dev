use std::collections::BTreeSet;
use vir_crate::low as vir_low;

#[derive(Default)]
pub(in super::super) struct LabelsState {
    pub(super) counter: u64,
    pub(super) labels: BTreeSet<vir_low::Label>,
}

impl LabelsState {
    pub(crate) fn destruct(self) -> Vec<vir_low::Label> {
        self.labels.into_iter().collect()
    }
}
