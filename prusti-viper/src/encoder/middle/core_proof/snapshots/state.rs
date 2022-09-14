use super::{adts::SnapshotDomainsInfo, into_snapshot::SelfFramingAssertionEncoderState};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid},
};

#[derive(Default)]
pub(in super::super) struct SnapshotsState {
    /// FIXME: The visibility should be `pub(super)`.
    pub(in super::super) snapshot_domains_info: SnapshotDomainsInfo,
    /// Used for decoding domain names into original types.
    pub(super) domain_types: BTreeMap<String, vir_mid::Type>,
    /// The list of types for which `to_bytes` was encoded.
    pub(super) encoded_to_bytes: FxHashSet<vir_mid::Type>,
    /// The list of types for which sequence_repeat_constructor was encoded.
    pub(super) encoded_sequence_repeat_constructor: FxHashSet<vir_mid::Type>,
    pub(super) ssa_state: vir_low::ssa::SSAState<vir_mid::BasicBlockId>,
    // pub(super) all_variables: AllVariablesMap,
    // pub(super) variables: BTreeMap<vir_mid::BasicBlockId, VariableVersionMap>,
    // pub(super) variables_at_label: BTreeMap<String, VariableVersionMap>,
    // pub(super) current_variables: Option<VariableVersionMap>,
    /// Mapping from low types to their domain names.
    pub(super) type_domains: FxHashMap<vir_low::Type, String>,
    pub(super) self_framing_assertion_encoder_state: SelfFramingAssertionEncoderState,
}
impl SnapshotsState {
    pub(in super::super) fn destruct(self) -> SnapshotDomainsInfo {
        self.snapshot_domains_info
    }
}
