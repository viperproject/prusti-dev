use crate::encoder::mir::specifications::{constraints::ConstraintResolver, interface::SpecQuery};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{DefSpecificationMap, LoopSpecification, ProcedureSpecification, Refinable},
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;

/// Provides access to specifications, handling refinement if needed
pub(super) struct Specifications<'tcx> {
    user_typed_specs: DefSpecificationMap,

    /// A refinement can be different based on the query.
    /// The query can resolve to different [ProcedureSpecification]s due to ghost constraints.
    /// Since Prusti does currently not support refinements of ghost constraints, we
    /// store different refined versions for different queries.
    refined_specs: FxHashMap<SpecQuery<'tcx>, ProcedureSpecification>,
}

impl<'tcx> Specifications<'tcx> {
    pub(super) fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            user_typed_specs,
            refined_specs: FxHashMap::default(),
        }
    }

    pub(super) fn get_user_typed_specs(&self) -> &DefSpecificationMap {
        &self.user_typed_specs
    }

    pub(super) fn get_extern_spec_map(&self) -> &HashMap<DefId, LocalDefId> {
        &self.get_user_typed_specs().extern_specs
    }

    pub(super) fn get_loop_spec<'a, 'env: 'a>(
        &'a self,
        _env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a LoopSpecification> {
        trace!("Get loop specs of {:?}", query);
        self.user_typed_specs
            .get_loop_spec(&query.called_def_id)
            .map(|spec| &spec.base_spec)
    }

    pub(super) fn get_and_refine_proc_spec<'a, 'env: 'a>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        trace!("Get procedure specs of {:?}", query);

        // Refinement (if needed)
        if !self.is_refined(query) {
            if let Some((trait_def_id, trait_substs)) =
                env.find_trait_method_substs(query.called_def_id, query.call_substs)
            {
                let trait_query = query.adapt_to_call(trait_def_id, trait_substs);
                let refined = self.perform_proc_spec_refinement(env, query, trait_query);
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {:?}",
                    query
                );
                return refined;
            }
        }

        self.get_proc_spec(env, query)
    }

    fn perform_proc_spec_refinement<'a, 'env: 'a>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        impl_query: SpecQuery<'tcx>,
        trait_query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        debug!(
            "Refining specs of {:?} with specs of {:?}",
            impl_query, trait_query
        );

        let impl_spec = self
            .get_proc_spec(env, impl_query)
            .cloned()
            .unwrap_or_else(ProcedureSpecification::empty);

        let trait_spec = self.get_proc_spec(env, trait_query);

        let refined = if let Some(trait_spec_set) = trait_spec {
            impl_spec.refine(trait_spec_set)
        } else {
            impl_spec
        };

        self.refined_specs.insert(impl_query, refined);
        self.get_proc_spec(env, impl_query)
    }

    fn get_proc_spec<'a, 'env: 'a>(
        &'a self,
        env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        self.refined_specs.get(&query).or_else(|| {
            self.user_typed_specs
                .get_proc_spec(&query.called_def_id)
                .and_then(|spec| spec.resolve_emit_err(env, &query))
        })
    }

    fn is_refined(&self, query: SpecQuery) -> bool {
        self.refined_specs.contains_key(&query)
    }
}
