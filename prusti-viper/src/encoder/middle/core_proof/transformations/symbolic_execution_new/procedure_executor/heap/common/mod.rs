mod named_predicate_instances;
mod predicate_instances;
mod predicate_instance;
mod snapshot;
mod utils;

pub(super) use self::{
    named_predicate_instances::NamedPredicateInstances,
    predicate_instance::NoSnapshot,
    predicate_instances::{
        AliasedFractionalBool,
        //  AliasedFractionalBoundedPerm,
        AliasedWholeBool,
        FindSnapshotResult,
        //    AliasedWholeNat,
        PredicateInstances,
    },
};
