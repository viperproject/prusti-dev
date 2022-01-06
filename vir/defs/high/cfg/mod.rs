#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    Serialize,
    Deserialize,
    PartialEq(ignore=[position]),
    Eq,
    Hash(ignore=[position])
)]

pub mod procedure;

pub use procedure::{BasicBlock, BasicBlockId, ProcedureDecl, Successor};
