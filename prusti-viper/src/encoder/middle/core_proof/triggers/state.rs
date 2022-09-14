use std::collections::BTreeSet;

#[derive(Default)]
pub(in super::super) struct TriggersState {
    pub(super) encoded_triggering_functions: BTreeSet<String>,
}
