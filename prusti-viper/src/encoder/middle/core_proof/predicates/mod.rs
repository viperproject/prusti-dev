mod memory_block;
mod owned;
mod restoration;
mod state;
mod aliasing;

use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::low as vir_low;

pub(super) use self::{
    aliasing::PredicatesAliasingInterface,
    memory_block::PredicatesMemoryBlockInterface,
    owned::{
        OwnedNonAliasedSnapCallBuilder, OwnedNonAliasedUseBuilder, OwnedPredicateInfo,
        PredicatesOwnedInterface, SnapshotFunctionInfo,
    },
    restoration::RestorationInterface,
    state::PredicatesState,
};

/// Addidional information about the predicates used by purification
/// optimizations.
#[derive(Clone, Debug)]
pub(super) struct PredicateInfo {
    pub(super) owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
    pub(super) non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
}
