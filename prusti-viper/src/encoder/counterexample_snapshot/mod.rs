mod interface;
mod mapping;
mod discriminants_interface;

pub(crate) use self::interface::{MirProcedureMappingInterface, MirProcedureMapping};
pub(crate) use self::discriminants_interface::{DiscriminantsStateInterface, DiscriminantsState};
pub(crate) use self::mapping::{VarMapping, VarMappingInterface};
pub mod counterexample_snapshot2;
pub mod counterexample_translation_snapshot;