#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(trait_type=std::cmp::PartialEq,ignore=[position]),
    Eq,
    Hash(trait_type=core::hash::Hash,ignore=[position])
)]

pub mod procedure;

pub use procedure::{BasicBlock, BasicBlockId, ProcedureDecl, Successor};
