mod discriminants_interface;
mod interface;
mod mapping;

pub(crate) use self::{
    discriminants_interface::{DiscriminantsState, DiscriminantsStateInterface},
    interface::{MirProcedureMapping, MirProcedureMappingInterface},
    mapping::{VarMapping, VarMappingInterface},
};

pub mod counterexample;
pub mod counterexample_refactored;
pub mod counterexample_translation;
pub mod counterexample_translation_refactored;
