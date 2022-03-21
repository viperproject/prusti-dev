use crate::encoder::mir::specifications::{interface::SpecQuery, obligations::ObligationResolver};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{DefSpecificationMap, LoopSpecification, ProcedureSpecification, Refinable},
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;

/// Provides access to specifications, handling refinement if needed
pub(super) struct Specifications {
    user_typed_specs: DefSpecificationMap,
    refined_specs: FxHashMap<DefId, ProcedureSpecification>,
}

impl Specifications {
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

    pub(super) fn get_loop_spec(&self, def_id: DefId) -> Option<&LoopSpecification> {
        trace!("Get loop specs of {:?}", def_id);
        let spec = self.get_user_typed_specs().get(&def_id)?;
        spec.as_loop()
    }

    pub(super) fn get_and_refine_proc_spec<'a, 'env: 'a, 'tcx>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        trace!("Get procedure specs of {:?}", query);

        // Refinement (if needed)
        if !self.is_refined(query) {
            if let Some(trait_def_id) = env.find_trait_method(query.def_id) {
                let refined = self.perform_proc_spec_refinement(env, query, trait_def_id);
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

    fn perform_proc_spec_refinement<'a, 'env: 'a, 'tcx: 'a>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        of_query: SpecQuery<'tcx>,
        with_trait_def_id: DefId,
    ) -> Option<&'a ProcedureSpecification> {
        debug!(
            "Refining specs of {:?} with specs of {:?}",
            of_query, with_trait_def_id
        );

        let impl_spec = self
            .get_proc_spec(env, of_query)
            .cloned()
            .unwrap_or_else(ProcedureSpecification::empty);

        let trait_spec = self.get_proc_spec(env, SpecQuery::without_substs(with_trait_def_id));

        let refined = if let Some(trait_spec_set) = trait_spec {
            impl_spec.refine(trait_spec_set)
        } else {
            impl_spec
        };

        self.refined_specs.insert(of_query.def_id, refined);
        self.get_proc_spec(env, of_query)
    }

    fn get_proc_spec<'a, 'env: 'a, 'tcx>(
        &'a self,
        env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        self.refined_specs.get(&query.def_id).or_else(|| {
            self.user_typed_specs
                .get(&query.def_id)
                .and_then(|spec_set| spec_set.as_procedure())
                .map(|spec_with_obligation| ObligationResolver {
                    env,
                    query,
                    with_obligation: spec_with_obligation,
                })
                .map(|resolver| resolver.resolve())
        })
    }

    fn is_refined(&self, query: SpecQuery) -> bool {
        self.refined_specs.contains_key(&query.def_id)
    }
}
