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

    pub(super) fn get_loop_spec(&self, def_id: DefId) -> Option<&LoopSpecification> {
        trace!("Get loop specs of {:?}", def_id);
        let spec = self.user_typed_specs.get(&def_id)?;
        spec.as_loop()
    }

    pub(super) fn get_and_refine_proc_spec<'tcx>(
        &mut self,
        env: &Environment<'tcx>,
        def_id: DefId,
    ) -> Option<&ProcedureSpecification> {
        trace!("Get procedure specs of {:?}", def_id);

        // Refinement (if needed)
        if !self.is_refined(def_id) {
            if let Some(trait_def_id) = env.find_trait_method(def_id) {
                let refined = self.perform_proc_spec_refinement(def_id, trait_def_id);
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {:?}",
                    def_id
                );
                return refined;
            }
        }

        self.get_proc_spec(def_id)
    }

    fn perform_proc_spec_refinement(
        &mut self,
        of_def_id: DefId,
        with_trait_def_id: DefId,
    ) -> Option<&ProcedureSpecification> {
        debug!(
            "Refining specs of {:?} with specs of {:?}",
            of_def_id, with_trait_def_id
        );

        let impl_spec = self
            .get_proc_spec(of_def_id)
            .cloned()
            .unwrap_or_else(ProcedureSpecification::empty);

        let trait_spec = self.get_proc_spec(with_trait_def_id);

        let refined = if let Some(trait_spec_set) = trait_spec {
            impl_spec.refine(trait_spec_set)
        } else {
            impl_spec
        };

        self.refined_specs.insert(of_def_id, refined);
        self.get_proc_spec(of_def_id)
    }

    fn get_proc_spec(&self, def_id: DefId) -> Option<&ProcedureSpecification> {
        self.refined_specs.get(&def_id).or_else(|| {
            self.user_typed_specs
                .get(&def_id)
                .and_then(|spec_set| spec_set.as_procedure())
        })
    }

    fn is_refined(&self, def_id: DefId) -> bool {
        self.refined_specs.contains_key(&def_id)
    }
}
