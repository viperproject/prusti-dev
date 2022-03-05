use super::variables::{AllVariablesMap, VariableVersionMap};

use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::middle::{self as vir_mid};

#[derive(Default)]
pub(in super::super) struct SnapshotsState {
    /// Used for decoding domain names into original types.
    pub(super) domain_types: BTreeMap<String, vir_mid::Type>,
    /// The list of types for which `to_bytes` was encoded.
    pub(super) encoded_to_bytes: FxHashSet<vir_mid::Type>,
    pub(super) all_variables: AllVariablesMap,
    pub(super) variables: BTreeMap<vir_mid::BasicBlockId, VariableVersionMap>,
    pub(super) current_variables: Option<VariableVersionMap>,
}
