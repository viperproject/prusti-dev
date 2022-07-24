#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq,
    Eq,
    Hash
)]
#![derive_for_all_structs(new, new_with_pos)]

pub mod method;
pub mod procedure;

pub use self::{
    method::{MethodDecl, MethodKind},
    procedure::{BasicBlock, Label, ProcedureDecl, Successor},
};
