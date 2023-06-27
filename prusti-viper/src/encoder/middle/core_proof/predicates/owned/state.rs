use super::OwnedPredicateInfo;
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    // pub(super) unfolded_owned_predicates: FxHashSet<vir_mid::Type>,
    // pub(super) used_unique_ref_predicates: FxHashSet<vir_mid::Type>,
    // pub(super) used_frac_ref_predicates: FxHashSet<vir_mid::Type>,
    // pub(super) used_owned_range_snapshot_functions: FxHashSet<vir_mid::Type>,
    // pub(super) used_unique_ref_range_snapshot_functions: FxHashSet<vir_mid::Type>,
    // pub(super) used_frac_ref_range_snapshot_functions: FxHashSet<vir_mid::Type>,
    pub(super) encoded_owned_predicates: FxHashSet<String>,
    pub(super) encoded_unique_ref_predicates: FxHashSet<String>,
    pub(super) encoded_frac_ref_predicates: FxHashSet<String>,

    pub(super) encoded_owned_predicate_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_unique_ref_predicate_current_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_unique_ref_predicate_final_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_frac_ref_predicate_snapshot_functions: FxHashSet<String>,

    pub(super) encoded_owned_predicate_range_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_unique_ref_predicate_current_range_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_unique_ref_predicate_final_range_snapshot_functions: FxHashSet<String>,
    pub(super) encoded_frac_ref_predicate_range_snapshot_functions: FxHashSet<String>,

    pub(super) predicates: Vec<vir_low::PredicateDecl>,
    /// A map from predicate names to snapshot function names and snapshot types.
    pub(super) predicate_info: BTreeMap<String, OwnedPredicateInfo>,
}
