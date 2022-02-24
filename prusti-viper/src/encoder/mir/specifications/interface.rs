use crate::encoder::mir::specifications::specs::Specifications;
use log::trace;
use prusti_interface::specs::{typed, typed::DefSpecificationMap};
use rustc_hir::def_id::{DefId, LocalDefId};
use std::cell::RefCell;

pub(crate) struct SpecificationsState {
    specs: RefCell<Specifications>,
}

impl SpecificationsState {
    pub fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            specs: RefCell::new(Specifications::new(user_typed_specs)),
        }
    }
}

pub(crate) trait SpecificationsInterface {
    fn is_pure(&self, def_id: DefId) -> bool;

    fn is_trusted(&self, def_id: DefId) -> bool;

    fn get_predicate_body(&self, def_id: DefId) -> Option<LocalDefId>;

    fn has_extern_spec(&self, def_id: DefId) -> bool;

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification>;

    /// Get the specifications attached to the `def_id` function.
    fn get_procedure_specs(&self, def_id: DefId) -> Option<typed::ProcedureSpecification>;

    /// Get a local wrapper `DefId` for functions that have external specs.
    /// Return the original `DefId` for everything else.
    fn get_wrapper_def_id(&self, def_id: DefId) -> DefId;
}

impl<'v, 'tcx: 'v> SpecificationsInterface for super::super::super::Encoder<'v, 'tcx> {
    fn is_pure(&self, def_id: DefId) -> bool {
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), def_id)
            .and_then(|spec| spec.pure.extract_refinements().inherit_refined())
            .unwrap_or(false);
        trace!("is_pure {:?} = {}", def_id, result);
        result
    }

    fn is_trusted(&self, def_id: DefId) -> bool {
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), def_id)
            .and_then(|spec| {
                spec.trusted
                    .extract_refinements()
                    .with_selective_replacement()
                    .copied()
            })
            .unwrap_or(false);
        trace!("is_trusted {:?} = {}", def_id, result);
        result
    }

    fn get_predicate_body(&self, def_id: DefId) -> Option<LocalDefId> {
        let mut specs = self.specifications_state.specs.borrow_mut();
        let result = specs
            .get_and_refine_proc_spec(self.env(), def_id)
            .and_then(|spec| {
                spec.predicate_body
                    .extract_refinements()
                    .with_selective_replacement()
            });
        trace!("get_predicate_body {:?} = {:?}", def_id, result);
        result.cloned()
    }

    fn has_extern_spec(&self, def_id: DefId) -> bool {
        // FIXME: eventually, procedure specs (the entries in def_spec) should
        // have an `is_extern_spec` field. For now, due to the way we handle
        // MIR, extern specs create a wrapper function with a different DefId,
        // so since we already have this remapping, it is enough to check if
        // there is a wrapper present for the given external DefId.
        let result = self
            .specifications_state
            .specs
            .borrow()
            .get_extern_spec_map()
            .contains_key(&def_id);
        trace!("has_extern_spec {:?} = {}", def_id, result);
        result
    }

    fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification> {
        self.specifications_state
            .specs
            .borrow()
            .get_loop_spec(def_id)
            .cloned()
    }

    fn get_procedure_specs(&self, def_id: DefId) -> Option<typed::ProcedureSpecification> {
        let mut specs = self.specifications_state.specs.borrow_mut();
        let spec = specs.get_and_refine_proc_spec(self.env(), def_id)?;
        Some(spec.clone())
    }

    fn get_wrapper_def_id(&self, def_id: DefId) -> DefId {
        self.specifications_state
            .specs
            .borrow()
            .get_extern_spec_map()
            .get(&def_id)
            .map(|local_id| local_id.to_def_id())
            .unwrap_or(def_id)
    }
}
