//! Encoder of owned predicates.

mod builders;
mod encoder;
mod state;
mod interface;

pub(super) use self::state::PredicatesOwnedState;
pub(in super::super) use self::{
    builders::{
        FracRefUseBuilder, OwnedNonAliasedSnapCallBuilder, OwnedNonAliasedUseBuilder,
        UniqueRefUseBuilder,
    },
    interface::{OwnedPredicateInfo, PredicatesOwnedInterface, SnapshotFunctionInfo},
};
