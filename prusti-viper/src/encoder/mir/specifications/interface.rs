use crate::encoder::mir::specifications::specs::Specifications;
use log::trace;
use prusti_interface::{
    specs::{typed, typed::DefSpecificationMap},
    utils::has_spec_only_attr,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_span::Span;
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

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification>;

    /// Get the specifications attached to the `def_id` function.
    fn get_procedure_specs(&self, def_id: DefId) -> Option<typed::ProcedureSpecification>;

    /// Is the closure specified with the `def_id` spec only?
    fn is_spec_closure(&self, def_id: DefId) -> bool;

    /// Get the span of the declared specification, if any, or else the span of
    /// the method declaration.
    fn get_spec_span(&self, def_id: DefId) -> Span;
}

impl<'v, 'tcx: 'v> SpecificationsInterface for super::super::super::Encoder<'v, 'tcx> {
    fn is_pure(&self, def_id: DefId) -> bool {
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), def_id)
            // In case of error -> It is emitted in get_and_refine_proc_spec
            .map(|spec| spec.kind.is_pure().unwrap_or(false))
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
            .and_then(|spec| spec.trusted.extract_with_selective_replacement().copied())
            .unwrap_or(false);
        trace!("is_trusted {:?} = {}", def_id, result);
        result
    }

    fn get_predicate_body(&self, def_id: DefId) -> Option<LocalDefId> {
        let mut specs = self.specifications_state.specs.borrow_mut();
        let result = specs
            .get_and_refine_proc_spec(self.env(), def_id)
            // In case of error -> It is emitted in get_and_refine_proc_spec
            .map(|spec| spec.kind.get_predicate_body().unwrap_or(None))
            .unwrap_or(None);
        trace!("get_predicate_body {:?} = {:?}", def_id, result);
        result.cloned()
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

    fn is_spec_closure(&self, def_id: DefId) -> bool {
        has_spec_only_attr(self.env().tcx().get_attrs(def_id))
    }

    fn get_spec_span(&self, def_id: DefId) -> Span {
        self.specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), def_id)
            .and_then(|spec| spec.span)
            .unwrap_or_else(|| self.env().get_def_span(def_id))
    }
}
