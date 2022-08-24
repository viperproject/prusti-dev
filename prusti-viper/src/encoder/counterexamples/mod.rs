mod interface;
mod mapping;
mod discriminants_interface;

pub(crate) use self::interface::{MirProcedureMappingInterface, MirProcedureMapping};
pub(crate) use self::discriminants_interface::{DiscriminantsStateInterface, DiscriminantsState};
pub(crate) use self::mapping::{VarMapping, VarMappingInterface};

pub mod counterexample_refactored;
pub mod counterexample_translation_refactored;
pub mod counterexample_translation;
pub mod counterexample;