use prusti_interface::specs::typed::DefSpecificationMap;

pub static mut SPECS: Option<DefSpecificationMap> = None;

mod mir_info_collector;
pub mod mir_modify;
pub mod mir_helper;
