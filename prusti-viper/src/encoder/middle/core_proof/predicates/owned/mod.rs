//! Encoder of owned predicates.

mod builders;
mod encoder;
mod interface;

pub(super) use self::interface::PredicatesOwnedState;
pub(in super::super) use self::{
    builders::{
        FracRefUseBuilder, OwnedAliasedSnapCallBuilder, OwnedNonAliasedSnapCallBuilder,
        OwnedNonAliasedUseBuilder, UniqueRefUseBuilder,
    },
    interface::PredicatesOwnedInterface,
};
