use crate::encoder::mir::specifications::specs::Specifications;
use log::trace;
use prusti_interface::{
    specs::{typed, typed::DefSpecificationMap},
    utils::has_spec_only_attr,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{ty, ty::subst::SubstsRef};
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

#[derive(Copy, Clone, Debug)]
pub struct SpecQuery<'tcx> {
    pub def_id: DefId,
    pub substs: SubstsRef<'tcx>,
}

impl<'tcx> SpecQuery<'tcx> {
    pub(crate) fn new(def_id: DefId, substs: SubstsRef<'tcx>) -> Self {
        Self { def_id, substs }
    }

    pub(crate) fn without_substs(def_id: DefId) -> Self {
        Self::new(def_id, ty::List::empty())
    }
}

pub(crate) trait SpecificationsInterface<'tcx> {
    fn is_pure(&self, query: SpecQuery<'tcx>) -> bool;

    fn is_trusted(&self, query: SpecQuery<'tcx>) -> bool;

    fn get_predicate_body(&self, query: SpecQuery<'tcx>) -> Option<LocalDefId>;

    fn has_extern_spec(&self, def_id: DefId) -> bool;

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    fn get_loop_specs(&self, query: SpecQuery<'tcx>) -> Option<typed::LoopSpecification>;

    /// Get the specifications attached to a function.
    fn get_procedure_specs(&self, query: SpecQuery<'tcx>) -> Option<typed::ProcedureSpecification>;

    /// Get a local wrapper `DefId` for functions that have external specs.
    /// Return the original `DefId` for everything else.
    fn get_wrapper_def_id(&self, def_id: DefId) -> DefId;

    /// Is the closure specified with the `def_id` is spec only?
    fn is_spec_closure(&self, def_id: DefId) -> bool;
}

impl<'v, 'tcx: 'v> SpecificationsInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn is_pure(&self, query: SpecQuery<'tcx>) -> bool {
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), query)
            .and_then(|spec| spec.pure.extract_inherit())
            .unwrap_or(false);
        trace!("is_pure {:?} = {}", query, result);
        result
    }

    fn is_trusted(&self, query: SpecQuery<'tcx>) -> bool {
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), query)
            .and_then(|spec| spec.trusted.extract_with_selective_replacement().copied())
            .unwrap_or(false);
        trace!("is_trusted {:?} = {}", query, result);
        result
    }

    fn get_predicate_body(&self, query: SpecQuery<'tcx>) -> Option<LocalDefId> {
        let mut specs = self.specifications_state.specs.borrow_mut();
        let result = specs
            .get_and_refine_proc_spec(self.env(), query)
            .and_then(|spec| spec.predicate_body.extract_with_selective_replacement());
        trace!("get_predicate_body {:?} = {:?}", query, result);
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

    fn get_loop_specs(&self, query: SpecQuery<'tcx>) -> Option<typed::LoopSpecification> {
        self.specifications_state
            .specs
            .borrow()
            .get_loop_spec(self.env(), query)
            .cloned()
    }

    fn get_procedure_specs(&self, query: SpecQuery<'tcx>) -> Option<typed::ProcedureSpecification> {
        let mut specs = self.specifications_state.specs.borrow_mut();
        let spec = specs.get_and_refine_proc_spec(self.env(), query)?;
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

    /// Is the closure specified with the `def_id` is spec only?
    fn is_spec_closure(&self, def_id: DefId) -> bool {
        has_spec_only_attr(self.env().tcx().get_attrs(def_id))
    }
}
