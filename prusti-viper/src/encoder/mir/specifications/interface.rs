use crate::encoder::mir::specifications::specs::Specifications;
use log::trace;
use prusti_interface::{
    specs::{
        typed,
        typed::{DefSpecificationMap, ProcedureSpecification},
    },
    utils::has_spec_only_attr,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::subst::SubstsRef;
use std::{cell::RefCell, hash::Hash};

pub(crate) struct SpecificationsState<'tcx> {
    specs: RefCell<Specifications<'tcx>>,
}

impl<'tcx> SpecificationsState<'tcx> {
    pub fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            specs: RefCell::new(Specifications::new(user_typed_specs)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct SpecQuery<'tcx> {
    pub called_def_id: DefId,
    pub caller_def_id: Option<DefId>,
    pub call_substs: SubstsRef<'tcx>,
    pub cause: SpecQueryCause,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecQueryCause {
    Unknown,
    FunctionDefEncoding,
    FunctionCallEncoding,
    PureOrTrustedCheck,
}

impl<'tcx> SpecQuery<'tcx> {
    pub(crate) fn new(
        called_def_id: DefId,
        caller_def_id: Option<DefId>,
        call_substs: SubstsRef<'tcx>,
        reason: SpecQueryCause,
    ) -> Self {
        Self {
            called_def_id,
            caller_def_id,
            call_substs,
            cause: reason,
        }
    }

    pub(crate) fn adapt_to_call(&self, called_def_id: DefId, call_substs: SubstsRef<'tcx>) -> Self {
        let mut copy = *self;
        copy.called_def_id = called_def_id;
        copy.call_substs = call_substs;
        copy
    }
}

pub(crate) trait SpecificationsInterface<'tcx> {
    fn is_pure(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool;

    fn is_trusted(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool;

    fn get_predicate_body(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> Option<LocalDefId>;

    fn has_extern_spec(&self, def_id: DefId) -> bool;

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    fn get_loop_specs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Option<typed::LoopSpecification>;

    /// Get the specifications attached to a function.
    fn get_procedure_specs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Option<typed::ProcedureSpecification>;

    /// Get the specifications attached to a function for a function call.
    fn get_procedure_specs_for_call(
        &self,
        called_def_id: DefId,
        caller_def_id: DefId,
        call_substs: SubstsRef<'tcx>,
    ) -> Option<typed::ProcedureSpecification>;

    /// Get a local wrapper `DefId` for functions that have external specs.
    /// Return the original `DefId` for everything else.
    fn get_wrapper_def_id(&self, def_id: DefId) -> DefId;

    /// Is the closure specified with the `def_id` is spec only?
    fn is_spec_closure(&self, def_id: DefId) -> bool;
}

impl<'v, 'tcx: 'v> SpecificationsInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn is_pure(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool {
        let substs = substs.unwrap_or_else(|| self.env().identity_substs(def_id));
        let query = SpecQuery::new(def_id, None, substs, SpecQueryCause::PureOrTrustedCheck);
        let result = self
            .specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), query)
            // In case of error -> It is emitted in get_and_refine_proc_spec
            .map(|spec| spec.kind.is_pure().unwrap_or(false))
            .unwrap_or(false);
        trace!("is_pure {:?} = {}", query, result);
        result
    }

    fn is_trusted(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool {
        let substs = substs.unwrap_or_else(|| self.env().identity_substs(def_id));
        let query = SpecQuery::new(def_id, None, substs, SpecQueryCause::PureOrTrustedCheck);
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

    fn get_predicate_body(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> Option<LocalDefId> {
        let query = SpecQuery::new(def_id, None, substs, SpecQueryCause::FunctionDefEncoding);
        let mut specs = self.specifications_state.specs.borrow_mut();
        let result = specs
            .get_and_refine_proc_spec(self.env(), query)
            // In case of error -> It is emitted in get_and_refine_proc_spec
            .map(|spec| spec.kind.get_predicate_body().unwrap_or(None))
            .unwrap_or(None);
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

    fn get_loop_specs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Option<typed::LoopSpecification> {
        let query = SpecQuery::new(def_id, None, substs, SpecQueryCause::Unknown);
        self.specifications_state
            .specs
            .borrow()
            .get_loop_spec(self.env(), query)
            .cloned()
    }

    fn get_procedure_specs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Option<typed::ProcedureSpecification> {
        let query = SpecQuery::new(def_id, None, substs, SpecQueryCause::FunctionDefEncoding);
        let mut specs = self.specifications_state.specs.borrow_mut();
        let spec = specs.get_and_refine_proc_spec(self.env(), query)?;
        Some(spec.clone())
    }

    fn get_procedure_specs_for_call(
        &self,
        called_def_id: DefId,
        caller_def_id: DefId,
        call_substs: SubstsRef<'tcx>,
    ) -> Option<ProcedureSpecification> {
        let query = SpecQuery::new(
            called_def_id,
            Some(caller_def_id),
            call_substs,
            SpecQueryCause::FunctionCallEncoding,
        );
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
