use crate::encoder::mir::specifications::specs::Specifications;
use log::trace;
use prusti_interface::{
    specs::{
        typed,
        typed::{DefSpecificationMap, ProcedureSpecification, ProcedureSpecificationKind},
    },
    utils::has_spec_only_attr,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::subst::SubstsRef;
use rustc_span::Span;
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
pub(super) struct FunctionCallEncodingQuery<'tcx> {
    pub called_def_id: DefId,
    pub caller_def_id: DefId,
    pub call_substs: SubstsRef<'tcx>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum SpecQuery<'tcx> {
    FunctionDefEncoding(DefId, SubstsRef<'tcx>),
    FunctionCallEncoding(FunctionCallEncodingQuery<'tcx>),
    /// For determining the [ProcedureSpecificationKind] of a procedure, e.g.
    /// for a check whether the function is pure or impure
    GetProcKind(DefId, SubstsRef<'tcx>),
    FetchSpan(DefId),
}

impl<'tcx> SpecQuery<'tcx> {
    pub fn referred_def_id(&self) -> DefId {
        match self {
            SpecQuery::FunctionDefEncoding(def_id, _)
            | SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
                called_def_id: def_id,
                ..
            })
            | SpecQuery::GetProcKind(def_id, _)
            | SpecQuery::FetchSpan(def_id) => *def_id,
        }
    }

    pub fn adapt_to(&self, new_def_id: DefId, new_substs: SubstsRef<'tcx>) -> Self {
        use SpecQuery::*;
        match self {
            FunctionDefEncoding(_, _) => FunctionDefEncoding(new_def_id, new_substs),
            FunctionCallEncoding(FunctionCallEncodingQuery { caller_def_id, .. }) => {
                FunctionCallEncoding(FunctionCallEncodingQuery {
                    called_def_id: new_def_id,
                    caller_def_id: *caller_def_id,
                    call_substs: new_substs,
                })
            }
            GetProcKind(_, _) => GetProcKind(new_def_id, new_substs),
            FetchSpan(_) => FetchSpan(new_def_id),
        }
    }
}

pub(crate) trait SpecificationsInterface<'tcx> {
    // TODO abstract-predicates: Maybe this should be deleted (and ProcedureSpecificationKind::is_pure)
    fn is_pure(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool;

    fn get_proc_kind(
        &self,
        def_id: DefId,
        substs: Option<SubstsRef<'tcx>>,
    ) -> ProcedureSpecificationKind;

    fn is_trusted(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool;

    fn get_predicate_body(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> Option<LocalDefId>;

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification>;

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

    /// Is the closure specified with the `def_id` spec only?
    fn is_spec_closure(&self, def_id: DefId) -> bool;

    /// Get the span of the declared specification, if any, or else the span of
    /// the method declaration.
    fn get_spec_span(&self, def_id: DefId) -> Span;
}

impl<'v, 'tcx: 'v> SpecificationsInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn is_pure(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool {
        let kind = self.get_proc_kind(def_id, substs);
        let mut pure = matches!(
            kind,
            ProcedureSpecificationKind::Pure | ProcedureSpecificationKind::Predicate(_)
        );

        let func_name = self.env().get_unique_item_name(def_id);
        if func_name.starts_with("prusti_contracts::prusti_contracts::Map")
            || func_name.starts_with("prusti_contracts::prusti_contracts::Seq")
        {
            pure = true;
        }

        trace!("is_pure {:?} = {}", def_id, pure);
        pure
    }

    fn get_proc_kind(
        &self,
        def_id: DefId,
        substs: Option<SubstsRef<'tcx>>,
    ) -> ProcedureSpecificationKind {
        let substs = substs.unwrap_or_else(|| self.env().identity_substs(def_id));
        let query = SpecQuery::GetProcKind(def_id, substs);
        self.specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), query)
            .map(|spec| spec.kind)
            .and_then(|kind| kind.extract_with_selective_replacement().copied())
            .unwrap_or(ProcedureSpecificationKind::Impure)
    }

    fn is_trusted(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool {
        let substs = substs.unwrap_or_else(|| self.env().identity_substs(def_id));
        let query = SpecQuery::GetProcKind(def_id, substs);
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
        let query = SpecQuery::FunctionDefEncoding(def_id, substs);
        let mut specs = self.specifications_state.specs.borrow_mut();
        let result = specs
            .get_and_refine_proc_spec(self.env(), query)
            // In case of error -> It is emitted in get_and_refine_proc_spec
            .map(|spec| spec.kind.get_predicate_body().unwrap_or(None))
            .unwrap_or(None);
        trace!("get_predicate_body {:?} = {:?}", query, result);
        result.cloned()
    }

    fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification> {
        self.specifications_state
            .specs
            .borrow()
            .get_loop_spec(&def_id)
            .cloned()
    }

    fn get_procedure_specs(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Option<typed::ProcedureSpecification> {
        let query = SpecQuery::FunctionDefEncoding(def_id, substs);
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
        let query = SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
            called_def_id,
            caller_def_id,
            call_substs,
        });
        let mut specs = self.specifications_state.specs.borrow_mut();
        let spec = specs.get_and_refine_proc_spec(self.env(), query)?;
        Some(spec.clone())
    }

    fn is_spec_closure(&self, def_id: DefId) -> bool {
        has_spec_only_attr(self.env().tcx().get_attrs(def_id))
    }

    fn get_spec_span(&self, def_id: DefId) -> Span {
        let query = SpecQuery::FetchSpan(def_id);
        self.specifications_state
            .specs
            .borrow_mut()
            .get_and_refine_proc_spec(self.env(), query)
            .and_then(|spec| spec.span)
            .unwrap_or_else(|| self.env().get_def_span(def_id))
    }
}
