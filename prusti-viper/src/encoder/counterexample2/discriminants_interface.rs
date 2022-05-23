use vir_crate::low::{self as vir_low};
use rustc_hash::{FxHashMap};
use log::{info};
use prusti_interface::data::ProcedureDefId;
use std::cell::RefCell;

#[derive(Default)]
pub(crate) struct DiscriminantsState {
    discriminants_info: RefCell<FxHashMap<(ProcedureDefId, String), Vec<String>>>,
}

pub(crate) trait  DiscriminantsStateInterface {
    fn add_discriminant_info(&self, enum_id: String, discr_id: String, proc_def_id: ProcedureDefId); 
    fn discriminants_info(&self) -> FxHashMap<(ProcedureDefId, String), Vec<String>>;
}

impl<'v, 'tcx: 'v> DiscriminantsStateInterface for super::super::Encoder<'v, 'tcx> {
    fn add_discriminant_info(
        &self,
        enum_id: String,
        discr_id: String,
        proc_def_id: ProcedureDefId,
    ) {
        self.discriminantsState.discriminants_info
            .borrow_mut()
            .entry((proc_def_id, enum_id))
            .or_default()
            .push(discr_id);
    }
    fn discriminants_info(&self) -> FxHashMap<(ProcedureDefId, String), Vec<String>> {
        self.discriminantsState.discriminants_info.borrow().clone()
    }
}