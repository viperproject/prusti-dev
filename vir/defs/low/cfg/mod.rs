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
#![derive_for_all_structs(new, new_with_pos)]

pub mod method;

pub use self::method::{BasicBlock, Label, ProcedureDecl};
