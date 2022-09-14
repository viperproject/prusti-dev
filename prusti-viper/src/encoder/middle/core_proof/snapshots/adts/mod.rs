//! Interface for calling constructors of snapshot ADTs that model Rust types.
//! For constructing values, you probably want to use methods defined in
//! `prusti-viper/src/encoder/middle/core_proof/snapshots/values/mod.rs`.
//!
//! This is a higher-level wrapper around
//! `prusti-viper/src/encoder/middle/core_proof/adts/interface.rs`.

mod interface;
mod state;

pub(in super::super) use self::{
    interface::SnapshotAdtsInterface,
    state::{SnapshotDomainInfo, SnapshotDomainsInfo},
};
