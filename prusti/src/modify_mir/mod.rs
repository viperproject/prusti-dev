use prusti_interface::{
    specs::typed::DefSpecificationMap,
};

// store the specs between multiple calls to mir_drops_elaborated.
// TODO: Can we store env too somehow?
pub static mut SPECS: Option<DefSpecificationMap> = None;

mod mir_info_collector;
pub mod mir_modify;
pub mod mir_helper;
